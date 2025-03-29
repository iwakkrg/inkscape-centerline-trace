#!/usr/bin/env python3
#
# Inkscape extension to vectorize bitmaps by tracing along the center of lines
# (C) 2016 juewei@fabmail.org
# Distribute under GPL-2.0 or ask.
#
# code snippets visited to learn the extension 'effect' interface:
# - convert2dashes.py
# - http://github.com/jnweiger/inkscape-silhouette
# - http://github.com/jnweiger/inkscape-gears-dev
# - http://sourceforge.net/projects/inkcut/
# - http://code.google.com/p/inkscape2tikz/
# - http://code.google.com/p/eggbotcode/
#
# vectorize strokes in a graymap png file
# as a path along the centerline of the strokes.
#
# This is done with autotrace -centerline, as
# the builtin potrace in inkscape cannot do centerline --
# it would always draw a path around the contour of the
# stroke, resulting in double lines.
#
# We want a stroke represented by a single path (optionally with line-width) ,
# rather than its outline contour.
#
# Algorithm:
#
# The input image is converted to a graymap and histogram normalized with PIL.ImageOps.equalize. or autocontrast
#
# autotrace needs a bi-level bitmap. In order to find the
# best threshold value, we run autotrace at multiple thresholds
# and evaluate the result.
#
# We count the number of line segments produced and
# measure the total path length drawn.
#
# The svg that has the longest path but the least number of
# segments is returned.
#
# Requires:
# apt-get install autotrace python-pil
#
# 2016-05-10 jw, V0.1 -- initial draught
# 2016-05-11 jw, V0.2 -- first usable inkscape-extension
# 2016-05-15 jw, V0.3 -- equal spatial illumination applied. autocontrast instead of equalize. denoise.
# 2016-05-16 jw, V0.4 -- added replace option. Made filters optional.
# 2016-11-05 jw, V0.5 -- support embedded jpeg (and possibly other file types)
#			 https://github.com/fablabnbg/inkscape-centerline-trace/issues/8
# 2016-11-06 jw, V0.6 -- support transparent PNG images by applying white background
#			 https://github.com/fablabnbg/inkscape-centerline-trace/issues/3
# 2016-11-07 jw, V0.7 -- transparency: use black background when the '[x] trace white line' is enabled.
# 2017-03-05 jw,      -- instructions for mac added: http://macappstore.org/autotrace/
# 2017-07-12 jw,      -- instructions for windows added: https://inkscape.org/en/gallery/item/10567/centerline_NIH0Rhk.pdf
# 2018-06-20 jw,      -- usual suspects for paths to find autotrace on osx.
# 2018-08-10 jw, V0.7b --  require python-lxml for deb.
# 2018-08-31 jw, V0.8 -- MacOS instructions updated and MacOS path added for autotrace 0.40.0 from
#                        https://github.com/jnweiger/autotrace/releases
# 2018-09-01 jw, V0.8a -- Windows Path added
# 2018-09-03 jw, V0.8b -- New option: cliprect, hairline, at_filter_iterations, at_error_threshold added.
#                         Fixed stroke_width of scaled images.
# 2018-09-04 jw, V0.8c -- Fixed https://github.com/fablabnbg/inkscape-centerline-trace/issues/28
#                         Hints for https://github.com/fablabnbg/inkscape-centerline-trace/issues/27 added.
# 2019-03-24 jw, V0.8d -- Pad one pixel border to images, so that lines touching edges are recognized by autotrace.
# 2025-03-29 iwak, V0.9 -- Updated to work with inkscape 1.0+.


__version__ = '0.9'    # Keep in sync with centerline-trace.inx ca. line 3 and 24
__author__ = 'Juergen Weigert <juergen@fabmail.org>'

import sys, os, re, math, tempfile, subprocess, base64, time
import argparse

try:
    from PIL import Image
    from PIL import ImageOps
    from PIL import ImageStat
    from PIL import ImageFilter
except Exception:
    print("Error: Cannot import PIL. Try\n  apt-get install python-pil", file=sys.stderr)
    sys.exit(1)

debug = False
# debug = True

autotrace_exe = 'autotrace'

# search path, so that inkscape libraries are found when we are standalone.
sys_platform = sys.platform.lower()
if sys_platform.startswith('win'):  # windows
    sys.path.append(r'C:\Program Files\Inkscape\share\extensions')
    os.environ['PATH'] += os.pathsep + r'C:\Program Files\Inkscape\share\extensions'
    os.environ['PATH'] += os.pathsep + r'C:\Program Files (x86)\AutoTrace'
    os.environ['PATH'] += os.pathsep + r'C:\Program Files\AutoTrace'
elif sys_platform.startswith('darwin'):  # mac
    sys.path.append('/Applications/Inkscape.app/Contents/Resources/extensions')
    os.environ['PATH'] += ':/Applications/Inkscape.app/Contents/Resources/extensions'
    os.environ['PATH'] += ':' + os.environ.get('HOME', '') + '/.config/inkscape/extensions'
    os.environ['PATH'] += ':/Applications/autotrace.app/Contents/MacOS'
    os.environ['PATH'] += ':/usr/local/bin:/usr/local/lib'
else:  # linux
    # if sys_platform.startswith('linux'):
    sys.path.append('/usr/share/inkscape/extensions')

# inkscape libraries
import inkex, simplestyle
import cubicsuperpath

# Updated per deprecation: use inkex.localization.localize
try:
    inkex.localization.localize()
except Exception:
    pass

def inkbool(val):
    """
    Convert a string to a boolean. Accepts True/False, yes/no, 1/0.
    """
    if isinstance(val, bool):
        return val
    val_lower = val.lower()
    if val_lower in ("true", "yes", "1"):
        return True
    elif val_lower in ("false", "no", "0"):
        return False
    else:
        raise argparse.ArgumentTypeError("Boolean value expected.")

def uutounit(self, nn, uu):
    try:
        return self.svg.uutounit(nn, uu)   # inkscape 0.91
    except Exception:
        return inkex.uutounit(nn, uu)      # inkscape 0.48

class TraceCenterline(inkex.Effect):
    """
    Inkscape Extension make long continuous paths from smaller parts
    """
    def __init__(self):
        # Call the base class constructor.
        super().__init__()

        self.dumpname = os.path.join(tempfile.gettempdir(), "trace-centerline.dump")
        self.autotrace_opts = []         # extra options for autotrace tuning.
        self.megapixel_limit = 2.0        # max image size (limit needed, as we have no progress indicator)
        self.invert_image = False         # True: trace bright lines.
        self.replace_image = False        # True: remove image object when adding path object.
        self.candidates = 15              # [1..255] Number of autotrace candidate runs.
        self.filter_median = 0            # 0 to disable median filter.
        self.filter_equal_light = 0.0     # [0.0 .. 1.9] Use 1.0 with photos. Use 0.0 with perfect scans.
        self.hairline = False             # Fixed linewidth.
        self.hairline_width = 0.1         # Width of hairline [mm]

        # Test if autotrace is installed and in path
        command = autotrace_exe + ' --version'
        p = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return_code = p.wait()
        out, err = p.communicate()
        found = out.find(b'AutoTrace')
        if found == -1:
            print(err.decode(), file=sys.stderr)
            if err.find(b'cannot open shared object file') != -1:
                print("NOTE: This build of autotrace is incompatible with your system, try a different build.\n", file=sys.stderr)
            print("You need to install autotrace for this extension to work. Try https://github.com/jnweiger/autotrace/releases or search for autotrace version 0.40.0 or later.", file=sys.stderr)
            sys.exit(1)

        try:
            self.tty = open("/dev/tty", 'w')
        except Exception:
            try:
                self.tty = open(os.devnull, 'w')  # '/dev/null' for POSIX, 'nul' for Windows.
            except Exception:
                self.tty = open("CON:", 'w')  # windows. Does this work???
        if debug:
            print("TraceCenterline: __init__", file=self.tty)

        self.arg_parser.add_argument('-V', '--version',
                                     action='store_const', const=True, dest='version', default=False,
                                     help='Just print version number ("'+__version__+'") and exit.')  # Keep in sync with centerline-trace.inx ca. line 3 and 24
        self.arg_parser.add_argument('-i', '--invert', action='store', type=inkbool, default=False,
                                     help='Trace bright lines. (Default: dark lines)')
        self.arg_parser.add_argument('-C', '--cliprect', action='store', type=inkbool, default=False,
                                     help='Clip to selected rectangle. (Default: Trace entire bitmap)')
        self.arg_parser.add_argument('-r', '--remove', action='store', type=inkbool, default=False,
                                     help='Replace image with vector graphics. (Default: Place on top)')
        self.arg_parser.add_argument('-H', '--hairline', action='store', type=inkbool, default=False,
                                     help='Fixed linewidth. (Default: Automatic)')
        self.arg_parser.add_argument('-W', '--hairline-width', action='store',
                                     type=float, default=0.1, help="Width of a hairline [mm] (Default: 0.1)")
        self.arg_parser.add_argument('--at-error-threshold', action='store',
                                     type=float, default=2.0,
                                     help="Autotrace: Subdivide fitted curves that are offset by a number of pixels exceeding the specified real number (default: 2.0)")
        self.arg_parser.add_argument('--at-filter-iterations', action='store',
                                     type=int, default=4,
                                     help="Autotrace: Smooth the curve the specified number of times prior to fitting (default: 4)")
        self.arg_parser.add_argument('-m', '--megapixels', action='store',
                                     type=float, default=2.0, help="Limit image size in megapixels. (Lower is faster)")
        self.arg_parser.add_argument('-e', '--equal-light', action='store',
                                     type=float, default=0.0,
                                     help="Equalize illumination. Use 1.0 with flash photography, use 0.0 to disable.")
        self.arg_parser.add_argument('-c', '--candidates', action='store',
                                     type=int, default=15, help="[1..255] Autotrace candidate runs. (Lower is much faster)")
        self.arg_parser.add_argument('-d', '--despecle', action='store',
                                     type=int, default=0, help="[0..9] Apply median filter for noise reduction. (Default 0, off)")
        self.arg_parser.add_argument('-D', '--debug-show', action='store_const', const=True, default=False, dest='debug',
                                     help='debugging: shows processed pictures.')

    def __del__(self):
        try:
            if hasattr(self, 'tty') and self.tty and not self.tty.closed:
                self.tty.close()
        except Exception:
            pass

    def version(self):
        return __version__

    def author(self):
        return __author__

    def svg_centerline_trace(self, image_file, cliprect=None):
        """
        svg_centerline_trace prepares the image by
        a) limiting_size (aka runtime),
        b) removing noise,
        c) linear histogram expansion,
        d) equalized spatial illumnination (my own algorithm)

        Then we run several iterations of autotrace and find the optimal black white threshold by evaluating
        all outputs. The output with the longest total path and the least path elements wins.

        A cliprect dict with the keys x, y, w, h can be specified. All 4 are expected in the
        range 0..1 and are mapped to the image width and height.
        """
        num_attempts = self.candidates  # 15 is great. min 1, max 255, beware it gets much slower with more attempts.
        autotrace_cmd = [autotrace_exe,
                         '--filter-iterations', str(self.options.at_filter_iterations),
                         '--error-threshold', str(self.options.at_error_threshold),
                         '--centerline',
                         '--input-format=pbm',
                         '--output-format=svg']
        autotrace_cmd += self.autotrace_opts

        stroke_style_add = 'stroke-width:%.2f; fill:none; stroke-linecap:round;'

        if debug:
            print("svg_centerline_trace start " + image_file, file=self.tty)
            print('+ ' + ' '.join(autotrace_cmd), file=self.tty)
        im = Image.open(image_file)
        orig_im_size = (im.size[0], im.size[1])
        box = [0, 0, 0, 0]
        if cliprect is not None:
            box[0] = cliprect['x'] * im.size[0]
            box[1] = cliprect['y'] * im.size[1]
            # sorted(min, val, max)[1] does clamping without chaining min(max()) in an ugly way.
            box[2] = sorted((0, int(0.5 + box[0] + cliprect['w'] * im.size[0]), im.size[0]))[1]
            box[3] = sorted((0, int(0.5 + box[1] + cliprect['h'] * im.size[1]), im.size[1]))[1]
            box[0] = sorted((0, int(0.5 + box[0]), im.size[0]))[1]
            box[1] = sorted((0, int(0.5 + box[1]), im.size[1]))[1]
            im = im.crop(box)
            if box[0] == box[2] or box[1] == box[3]:
                print("ERROR: Cliprect and Image do not overlap.", orig_im_size, box, cliprect, file=sys.stderr)
                return ('<svg/>', 1, orig_im_size)

        if 'A' in im.mode:
            # this image has alpha. Paste it onto white or black.
            im = im.convert("RGBA")
            if self.invert_image:
                bg = Image.new('RGBA', im.size, (0, 0, 0, 255))  # black background
            else:
                bg = Image.new('RGBA', im.size, (255, 255, 255, 255))  # white background
            im = Image.alpha_composite(bg, im)

        im = im.convert(mode='L', dither=None)
        if debug:
            print("seen: " + str([im.format, im.size, im.mode]), file=self.tty)
        scale_limit = math.sqrt(im.size[0] * im.size[1] * 0.000001 / self.megapixel_limit)
        if scale_limit > 1.0:
            print("Megapixel limit (" + str(self.megapixel_limit) + ") exceeded. Scaling down by factor : " + str(scale_limit), file=sys.stderr)
            im = im.resize((int(im.size[0] / scale_limit), int(im.size[1] / scale_limit)), resample=Image.BILINEAR)

        if self.invert_image:
            im = ImageOps.invert(im)

        ### Add a one pixel padding around the image. Otherwise autotrace fails when a line touches the edge of the image.
        im = ImageOps.expand(im, border=1, fill=255)

        if self.filter_median > 0:
            if self.filter_median % 2 == 0:
                self.filter_median = self.filter_median + 1    # need odd values.
            im = im.filter(ImageFilter.MedianFilter(size=self.filter_median))  # feeble denoise attempt. FIXME: try ROF instead.
        im = ImageOps.autocontrast(im, cutoff=0)  # linear expand histogram (an alternative to equalize)
        ## cutoff=2 destroys some images, see https://github.com/fablabnbg/inkscape-centerline-trace/issues/28

        if self.filter_equal_light > 0.0:
            scale_thumb = math.sqrt(im.size[0] * im.size[1] * 0.0001)   # exactly 0.01 MP (e.g. 100x100)
            im_neg_thumb = ImageOps.invert(im.resize((int(im.size[0] / scale_thumb), int(im.size[1] / scale_thumb)), resample=Image.BILINEAR))
            im_neg_thumb = im_neg_thumb.filter(ImageFilter.GaussianBlur(radius=30))
            im_neg_blur = im_neg_thumb.resize(im.size, resample=Image.BILINEAR)
            if self.options.debug:
                im_neg_blur.show()

            if debug:
                print("ImageOps.equalize(im) done", file=self.tty)
            im = Image.blend(im, im_neg_blur, self.filter_equal_light * 0.5)
            im = ImageOps.autocontrast(im, cutoff=0)  # linear expand histogram (an alternative to equalize)
            if self.options.debug:
                im.show()

        def svg_pathstats(path_d):
            """ calculate statistics from an svg path:
                length (measuring bezier splines as straight lines through the handles).
                points (all, including duplicates)
                segments (number of not-connected!) path segments.
            """
            path_d = path_d.lower()
            p_points = 0
            p_length = 0
            p_segments = 0
            for p in path_d.split('m'):
                pp = re.sub('[cl,]', ' ', p)
                pp, closed = re.subn('z\s*$', '', pp)
                xy = pp.split()
                if len(xy) < 2:
                    continue
                x0 = float(xy[0])
                y0 = float(xy[1])
                p_points += 1
                x = xy[2::2]
                y = xy[3::2]
                if len(x):
                    p_segments += 1
                    if closed:
                        x.extend([x0])
                        y.extend([y0])
                for i in range(len(x)):
                    p_points += 1
                    dx = float(x[i]) - x0
                    dy = float(y[i]) - y0
                    p_length += math.sqrt(dx * dx + dy * dy)
                    x0, y0 = float(x[i]), float(y[i])
            return {'points': p_points, 'segments': p_segments, 'length': p_length}

        candidate = {}
        if self.options.debug:
            im.show()

        for i in range(num_attempts):
            threshold = int(256. * (1 + i) / (num_attempts + 1))
            # make lookup table that maps to black/white using threshold.
            lut = [255 for n in range(threshold)] + [0 for n in range(threshold, 256)]
            if debug:
                print("attempt " + str(i), file=self.tty)
            bw = im.point(lut, mode='1')
            if debug:
                print("bw from lut done: threshold=%d" % threshold, file=self.tty)
            if self.options.debug:
                bw.show(command="/usr/bin/display -title=bw:threshold=%d" % threshold)
            cand = {'threshold': threshold, 'img_width': bw.size[0], 'img_height': bw.size[1], 'mean': ImageStat.Stat(im).mean[0]}
            fp = tempfile.NamedTemporaryFile(prefix="centerlinetrace", suffix='.pbm', delete=False)
            fp.write(("P4\n%d %d\n" % (bw.size[0], bw.size[1])).encode())
            fp.write(bw.tobytes())
            fp.close()
            if debug:
                print("pbm from bw done", file=self.tty)
            p = subprocess.Popen(autotrace_cmd + [fp.name], stdout=subprocess.PIPE)
            cand['svg'] = p.communicate()[0].decode()
            if debug:
                print("autotrace done", file=self.tty)
            if not len(cand['svg']):
                print("autotrace_cmd: " + ' '.join(autotrace_cmd + [fp.name]), file=sys.stderr)
                print("ERROR: returned nothing, leaving tmp bmp file around for you to debug", file=sys.stderr)
                cand['svg'] = '<svg/>'
            else:
                os.unlink(fp.name)
            try:
                xml = inkex.etree.fromstring(cand['svg'])
            except Exception:
                print("autotrace_cmd: " + ' '.join(autotrace_cmd + [fp.name]), file=sys.stderr)
                print("ERROR: no proper xml returned: '" + cand['svg'] + "'", file=sys.stderr)
                xml = inkex.etree.fromstring('<svg/>')
            p_len, p_seg, p_pts = 0, 0, 0
            for p in xml.findall('path'):
                pstat = svg_pathstats(p.attrib['d'])
                p_len += pstat['length']
                p_seg += pstat['segments']
                p_pts += pstat['points']
            cand['length'] = p_len
            cand['segments'] = p_seg
            cand['points'] = p_pts

            if cand['mean'] > 127:
                cand['mean'] = 255 - cand['mean']  # should not happen
            blackpixels = cand['img_width'] * cand['img_height'] * cand['mean'] / 255.
            cand['strokewidth'] = blackpixels / max(cand['length'], 1.0)
            candidate[i] = cand

        def calc_weight(cand, idx):
            offset = (num_attempts / 2. - idx) * (num_attempts / 2. - idx) * (cand['img_width'] + cand['img_height'])
            w = cand['length'] * 5 - offset * .005 - cand['points'] * .2 - cand['segments'] * 20
            return w

        best_weight_idx = 0
        for n in candidate.keys():
            if calc_weight(candidate[n], n) > calc_weight(candidate[best_weight_idx], best_weight_idx):
                best_weight_idx = n

        if debug:
            print("best: %d/%d" % (best_weight_idx, num_attempts), file=self.tty)
        ## if standalone:
        # svg = re.sub('stroke:', (stroke_style_add % candidate[best_weight_idx]['strokewidth']) + ' stroke:', candidate[best_weight_idx]['svg'])
        # return svg

        ## inkscape-extension:
        return (candidate[best_weight_idx]['svg'], candidate[best_weight_idx]['strokewidth'], orig_im_size)

    def calc_unit_factor(self, units='mm'):
        """ return the scale factor for all dimension conversions.
            - The document units are always irrelevant as
              everything in inkscape is expected to be in 90dpi pixel units
        """
        # Updated to use self.svg.uutounit per new API.
        dialog_units = self.svg.uutounit(1.0, units)
        self.unit_factor = 1.0 / dialog_units
        return self.unit_factor

    def effect(self):
        global debug

        if self.options.version:
            print(__version__)
            sys.exit(0)
        if self.options.invert is not None:
            self.invert_image = self.options.invert
        if self.options.remove is not None:
            self.replace_image = self.options.remove
        if self.options.megapixels is not None:
            self.megapixel_limit = self.options.megapixels
        if self.options.candidates is not None:
            self.candidates = self.options.candidates
        if self.options.despecle is not None:
            self.filter_median = self.options.despecle
        if self.options.equal_light is not None:
            self.filter_equal_light = self.options.equal_light
        if self.options.hairline is not None:
            self.hairline = self.options.hairline
        if self.options.hairline_width is not None:
            self.hairline_width = self.options.hairline_width

        self.calc_unit_factor()

        cliprect = None
        # Updated: use self.svg.selected instead of self.selected.
        if self.options.cliprect:
            for id, node in self.svg.selected.items():
                if node.tag == inkex.addNS('path', 'svg'):
                    print("Error: id=" + str(id) + " is a path.\nNeed a rectangle object for clipping.", file=sys.stderr)
                if node.tag == inkex.addNS('rect', 'svg'):
                    if debug:
                        print("cliprect: id=" + str(id), "node=" + str(node.tag), file=self.tty)
                    cliprect = {
                        'x': float(node.get('x', 0)),
                        'y': float(node.get('y', 0)),
                        'w': float(node.get('width', 0)),
                        'h': float(node.get('height', 0)),
                        'node': node
                    }
                    if debug:
                        print("cliprect: id=" + str(id), "cliprect=" + str(cliprect), file=self.tty)

        if not len(self.svg.selected.items()):
            inkex.errormsg(_("Please select an image."))
            return

        if cliprect is not None and len(self.svg.selected.items()) < 2:
            inkex.errormsg(_("Please select an image. Only a cliprect was selected."))
            return

        for id, node in self.svg.selected.items():
            if debug:
                print("id=" + str(id), "tag=" + str(node.tag), file=self.tty)
            if self.options.cliprect and node.tag == inkex.addNS('rect', 'svg'):
                continue
            if node.tag != inkex.addNS('image', 'svg'):
                inkex.errormsg(_("Object " + id + " is NOT an image. seen:" + str(node.tag) + " expected:" + inkex.addNS('image', 'svg') + "\n Try - Object->Ungroup"))
                return

            # images can also just have a transform attribute, and no x or y,
            # FIXME: should find the image transformation!
            # could be replaced by a (slower) call to command line, or by computeBBox from simpletransform
            svg_x_off = float(node.get('x', 0))
            svg_y_off = float(node.get('y', 0))
            svg_img_w = float(node.get('width',  0.001))
            svg_img_h = float(node.get('height', 0.001))
            if cliprect is not None:
                # normalize cliprect into range 0..1
                cliprect['x'] = cliprect['x'] - svg_x_off
                cliprect['y'] = cliprect['y'] - svg_y_off
                cliprect['x'] = cliprect['x'] / svg_img_w
                cliprect['y'] = cliprect['y'] / svg_img_h
                cliprect['w'] = cliprect['w'] / svg_img_w
                cliprect['h'] = cliprect['h'] / svg_img_h

            # handle two cases. Embedded and linked images
            # <image .. xlink:href="data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAT8AA ..." preserveAspectRatio="none" height="432" width="425" transform="matrix(1,0,-0.52013328,0.85408511,0,0)"/>
            # <image .. xlink:href="xlink:href="data:image/jpeg;base64,/9j/4AAQSkZJRgAB..."
            # <image  .. xlink:href="file:///home/jw/schaf.png"

            href = str(node.get(inkex.addNS('href', 'xlink')))

            # ######################
            #
            # dump the entire svg to file, so that we can examine what an image is.
            # f=open(self.dumpname, 'w')
            # f.write(href)
            # f.close()
            # if debug: print >>self.tty, "Dump written to "+self.dumpname
            #
            # ######################

            if href[:7] == 'file://':
                filename = href[7:]
                if debug:
                    print("linked image: =" + filename, file=self.tty)
            elif href[0] == '/' or href[0] == '.':
                filename = href
                if debug:
                    print("linked image path: =" + filename, file=self.tty)
            elif href[:11] == 'data:image/':
                l = href[11:].index(';')
                img_type = href[11:11+l]   # 'png' or 'jpeg'
                if debug:
                    print("embedded image: " + href[:11+l], file=self.tty)
                img = base64.decodebytes(href[11+l+8:].encode('utf-8'))
                f = tempfile.NamedTemporaryFile(mode="wb", prefix='centerlinetrace', suffix="." + img_type, delete=False)
                f.write(img)
                filename = f.name
                f.close()
            else:
                inkex.errormsg(_("Neither file:// nor data:image/; prefix. Cannot parse PNG/JPEG image href " + href[:200] + "..."))
                sys.exit(1)
            if debug:
                print("filename=" + filename, file=self.tty)
            path_svg, stroke_width, im_size = self.svg_centerline_trace(filename, cliprect)
            xml = inkex.etree.fromstring(path_svg)
            try:
                path_d = xml.find('path').attrib['d']
            except Exception:
                inkex.errormsg(_("Couldn't trace the path. Please make sure that the checkbox for tracing bright lines is set correctly and that your drawing has enough contrast."))
                sys.exit(1)

            sx = svg_img_w / im_size[0]
            sy = svg_img_h / im_size[1]
            if debug:
                print("svg_im_width ", svg_img_w, "sx=", sx, file=self.tty)
                print("svg_im_height ", svg_img_h, "sy=", sy, file=self.tty)
                print("im_x ", svg_x_off, file=self.tty)
                print("im_y ", svg_y_off, file=self.tty)
                print("pixel_size= ", im_size, file=self.tty)
            if cliprect is not None:
                svg_x_off = max(svg_x_off, float(cliprect['node'].get('x', 0)))
                svg_y_off = max(svg_y_off, float(cliprect['node'].get('y', 0)))
            matrix = "translate(%g,%g) scale(%g,%g)" % (svg_x_off, svg_y_off, sx, sy)
            if href[:5] == 'data:':
                os.unlink(filename)  # remove temporary file
            if self.hairline:
                stroke_width = self.hairline_width * 96. / 25.4   # mm2px FIXME: 96dpi is just a default guess.
            else:
                stroke_width = stroke_width * 0.5 * (abs(sx) + abs(sy))
            style = {'stroke': '#000000', 'fill': 'none', 'stroke-linecap': 'round', 'stroke-width': stroke_width}
            if self.invert_image:
                style['stroke'] = '#777777'
            # simplestyle.formatStyle() is deprecated; use the new inkex.Style
            path_attr = {'style': str(inkex.Style(style)), 'd': path_d, 'transform': matrix}
            # Updated: use self.svg.get_current_layer() per new API.
            inkex.etree.SubElement(self.svg.get_current_layer(), inkex.addNS('path', 'svg'), path_attr)
            if self.replace_image:
                node.getparent().remove(node)
                if cliprect is not None:        # and its cliprect ...
                    cliprect['node'].getparent().remove(cliprect['node'])

if __name__ == '__main__':
    e = TraceCenterline()
    e.run()     # formerly e.affect(); now updated to run() per new API.
    sys.exit(0)  # helps to keep the selection
