# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Library enables user to parse kicad_pcb file
# Should be compatible with python2 and python3

import time
import re


class PcbParser(object):
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
            return indent + PcbParser.formatFlat(s) + '\n'
        else:
            out = indent + '(' + s[0] + '\n'
            for e in s[1:]:
                out = out + PcbParser.format(e, level + 1)
            out = out + indent + ')\n'
            return out

    @staticmethod
    def read_pcb_file(infile):
        # parse Lisp-like syntax
        # modified from: http://norvig.com/lispy2.html

        print 'Parsing PCB file.'
        start = time.time()

        # read the *.kicad_pcb file token by token
        with open(infile, 'r') as f:
            inport = InPort(f)

            def read_ahead(token):
                # If the current token is a left parenthesis,
                # start building a new sub-list
                if token == '(':
                    lis = []
                    while True:
                        token = inport.next_token()
                        if token == ')':
                            return lis
                        else:
                            lis.append(read_ahead(token))
                # Otherwise the token must be an atom,
                # unless there is a syntax error
                elif token == ')':
                    raise Exception('Unexpected )')
                elif token is None:
                    raise Exception('Unexpected EOF')
                else:
                    return token

            # Read the first token to start parsing
            token1 = inport.next_token()
            if token1 is None:
                tree = None
            else:
                tree = read_ahead(token1)

        end = time.time()
        print 'Parsing took', end - start, 'seconds'

        return tree

    @staticmethod
    def write_pcb_file(tree, outfile):
        formatted = PcbParser.format(tree)
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

# class used to parse Lisp-like syntax
# modified from: http://norvig.com/lispy2.html


class InPort(object):
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
