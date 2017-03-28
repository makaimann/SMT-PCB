# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Library enables user to parse kicad_pcb file
# Should be compatible with python2 and python3

import re

class LispPrinter(object):
    @staticmethod
    def formatFlat(s):
        s = ' '.join(s)
        return '(' + s + ')'

    @staticmethod
    def format(s, level=0):
        # set the indent level for readability
        indent = ' ' * level
        
        if isinstance(s, basestring):
            return indent + s + '\n'
        elif all(isinstance(x, basestring) for x in s):
            return indent + LispPrinter.formatFlat(s) + '\n'
        else:
            out = indent + '(' + s[0] + '\n'
            for e in s[1:]:
                out = out + LispPrinter.format(e, level + 1)
            out = out + indent + ')\n'
            return out
    
class PcbParser(object):

    @staticmethod
    def read_pcb_file(infile):
        # parse Lisp-like syntax
        # modified from: http://norvig.com/lispy2.html

        # read the *.kicad_pcb file token by token
        with open(infile, 'r') as f:
            inport = InPort(f)

            # Read the first token to start parsing
            token1 = inport.next_token()
            if token1 is None:
                tree = None
            else:
                tree = PcbParser.parse_recursive(inport, token1)

        return tree

    @staticmethod
    def parse_recursive(inport, token):
        # If the current token is a left parenthesis,
        # start building a new sub-list
        if token == '(':
            lis = []
            while True:
                token = inport.next_token()
                if token == ')':
                    return lis
                else:
                    lis.append(PcbParser.parse_recursive(inport, token))
        # Otherwise the token must be an atom,
        # unless there is a syntax error
        elif token == ')':
            raise Exception('Unexpected )')
        elif token is None:
            raise Exception('Unexpected EOF')
        else:
            return token

    @staticmethod
    def write_pcb_file(tree, outfile):
        formatted = LispPrinter.format(tree)
        open(outfile, 'w').write(formatted)

    @staticmethod
    def get_cmd_index(tree, cmd):
        return [x[0] for x in tree].index(cmd)

    @staticmethod
    def get_cmd(tree, cmd):
        return next(x for x in tree if x[0] == cmd)

    @staticmethod
    def add_net_count(tree, net_dict):
        general_cmd = PcbParser.get_cmd(tree, 'general')
        net_cmd = PcbParser.get_cmd(general_cmd, 'nets')
        net_cmd[1] = str(1 + len(net_dict))

    @staticmethod
    def add_net_decls(tree, net_dict):
        # build net declarations
        net_decls = []
        for net_name, net_id in net_dict.items():
            net_decls.append(['net', str(net_id), net_name])

        # add them to the PCB file at the right position
        net_cmd_index = PcbParser.get_cmd_index(tree, 'net')
        tree[(net_cmd_index + 1):(net_cmd_index + 1)] = net_decls

    @staticmethod
    def populate_default_net_class(tree, net_set):
        net_class_cmd = PcbParser.get_cmd(tree, 'net_class')
        for net_name in net_set:
            net_class_cmd.append(['add_net', net_name])

    @staticmethod
    def populate_net_classes(tree, net_class_list):
        # insert the net declarations into the kicad_pcb file
        idx = PcbParser.get_cmd_index(tree, 'net_class')
        tree[(idx + 1):(idx + 1)] = net_class_list

    @staticmethod
    def add_nets_to_modules(tree, pcb_dict, net_dict):
        for val in tree:
            if val[0] == 'module':
                PcbParser.add_nets_to_module(val, pcb_dict, net_dict)

    @staticmethod
    def add_nets_to_module(mod, pcb_dict, net_dict):
        for val in mod:
            if val[0:2] == ['fp_text', 'reference']:
                refdes = val[2]
                if refdes not in pcb_dict:
                    return
            elif val[0] == 'pad':
                pad_name = val[1]
                if pad_name in pcb_dict[refdes]:
                    net_name = pcb_dict[refdes][pad_name]
                    net_id = net_dict[net_name]
                    val.append(['net', str(net_id), net_name])

    @staticmethod
    def get_mod_list(tree):
        mod_list = []
        for entry in tree:
            if entry[0] == 'module':
                mod = {}
                mod['name'] = entry[1]
                for val in entry[2:]:
                    if val[0] == 'layer':
                        mod['layer'] = val[1]
                    elif val[0] == 'at':
                        mod['x'] = float(val[1])
                        mod['y'] = float(val[2])
                        if len(val) == 3:
                            mod['rot'] = 0
                        else:
                            mod['rot'] = int(val[3])
                    elif val[0] == 'fp_text' and val[1] == 'reference':
                        mod['refdes'] = val[2]
                mod_list = mod_list + [mod]
        return mod_list

class InPort(object):
    # class used to parse Lisp-like syntax
    # modified from: http://norvig.com/lispy2.html

    # Tokenizer splits on parentheses but respects double-quoted strings
    # TODO: handle multi-line quotes
    tokenizer = r'''\s*([()]|"[^"]*"|[^\s(")]*)(.*)'''

    def __init__(self, file):
        self.file = file
        self.line = ''

    def next_token(self):
        while True:
            if self.line == '':
                self.line = self.file.readline()
            if self.line == '':
                return None
            token, self.line = re.match(InPort.tokenizer, self.line).groups()
            if token != '':
                return token
