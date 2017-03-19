# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Library enables user to instantiate new modules from KiCAD library

from pcbparser import PcbParser


class BoardTools(object):
    @staticmethod
    def get_board_extents(board_edge):
        # extract list of x vals and y vals from board edge
        x_vals = [coord[0] for coord in board_edge]
        y_vals = [coord[1] for coord in board_edge]

        # find bounding rectangle for the board
        max_x = max(x_vals)
        min_x = min(x_vals)
        max_y = max(y_vals)
        min_y = min(y_vals)

        return max_x, min_x, max_y, min_y

    @staticmethod
    def get_board_center(board_edge):
        # get extents of the board
        max_x, min_x, max_y, min_y = BoardTools.get_board_extents(board_edge)

        # compute center of board
        cx = (max_x + min_x) / 2.0
        cy = (max_y + min_y) / 2.0

        return cx, cy

    @staticmethod
    def get_board_dims(board_edge):
        # get extents of the board
        max_x, min_x, max_y, min_y = BoardTools.get_board_extents(board_edge)

        width = max_x - min_x
        height = max_y - min_y

        return width, height

    @staticmethod
    def get_board_ul(board_edge):
        # get width and height of board
        width, height = BoardTools.get_board_dims(board_edge)

        # title block center (assuming A4 paper)
        # TODO: handle paper sizes other than A4
        disp_center_x = 297 / 2.0
        disp_center_y = 210 / 2.0

        # try to center components on board
        xmid = 0.5 * width
        x0 = disp_center_x - xmid
        ymid = 0.5 * height
        y0 = disp_center_y - ymid

        return (x0, y0)

    @staticmethod
    def get_keepouts(board_edge, min_kw=1e-3, min_kh=1e-3):
        # TODO: handle general board edges

        # get width and height of board
        width, height = BoardTools.get_board_dims(board_edge)

        keepouts = []
        for p0, p1 in zip(board_edge[:-1], board_edge[1:]):
            x0, y0 = p0
            x1, y1 = p1

            if x1 > x0:
                # quadrants I and IV
                kw = x1 - x0
                kh = max(y0, y1)
                kx = x0
                ky = 0
            elif x0 > x1:
                # quadrants II and III
                kw = x0 - x1
                kh = height - min(y0, y1)
                kx = x1
                ky = min(y0, y1)
            else:
                continue

            if kw > min_kw and kh > min_kw:
                keepouts.append([kw, kh, kx, ky])

        return keepouts

    @staticmethod
    def add_nets(pcb_dict, net_class_list, infile, outfile):
        # Create a dictionary mapping each unique net to an ID number
        net_dict = BoardTools.build_net_dict(pcb_dict)

        # Parse the exisiting PCB file
        tree = PcbParser.read_pcb_file(infile)

        # add nets to PCB file
        PcbParser.add_net_count(tree, net_dict)
        PcbParser.add_net_decls(tree, net_dict)
        PcbParser.add_nets_to_modules(tree, pcb_dict, net_dict)

        # add net classes to PCB file
        PcbParser.populate_net_classes(tree, net_class_list)

        # Write updated PCB information
        PcbParser.write_pcb_file(tree, outfile)

    @staticmethod
    def build_net_dict(pcb_dict):
        # build set of unique nets
        net_set = set()
        for mod_dict in pcb_dict.values():
            for net in mod_dict.values():
                net_set.add(net)

        # make a dictionary mapping each net to an id
        net_id = 1
        net_dict = {}
        for net in net_set:
            net_dict[net] = net_id
            net_id = net_id + 1

        return net_dict
