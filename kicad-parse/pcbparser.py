# Steven Herbst
# sherbst@stanford.edu

# Library enables user to parse kicad_pcb file

import re

class TreeNode(object):
    def __init__(self):
        self.parent = None
        self.prev = None
        self.next = None
        self.firstChild = None
        self.lastChild = None
        self.value = None

    @property
    def isLeaf(self):
        return self.firstChild is None

    def append(self, node):
        node.parent = self
        if self.firstChild is None:
            self.firstChild = node
            self.lastChild = node
        else:
            self.lastChild.next = node
            node.prev = self.lastChild
            self.lastChild = node

    def prepend(self, node):
        node.parent = self
        if self.firstChild is None:
            self.firstChild = node
            self.lastChild = node
        else:
            self.firstChild.prev = node
            node.next = self.firstChild
            self.firstChildChild = node

    def children(self):
        child = self.firstChild
        while child:
            yield child 
            child = child.next

    def nextSiblings(self):
        sib = self.next
        while sib:
            yield sib
            sib = sib.next

    def prevSiblings(self):
        sib = self.prev
        while sib:
            yield sib
            sib = sib.prev
    
    def __str__(self):
        return TreeNode.str_helper(self, level=0)

    @staticmethod
    def str_helper(node, level):
        # set the indent level for readability
        indent = ' ' * level
        
        if node.isLeaf:
            return indent + node.value + '\n'
        else:
            out = indent + '(\n'
            for e in node.children():
                out = out + TreeNode.str_helper(e, level + 1)
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
    
            # Create new tree
            if token1 is None:
                return None
            if token1 is not None:
                return PcbParser.parse_recursive(inport, token1, None)

    @staticmethod
    def parse_recursive(inport, token, parent):
        # If the current token is a left parenthesis,
        # start building a new sub-list
        if token == '(':
            node = TreeNode()
            if parent is not None:
                parent.add(node)
            while True:
                token = inport.next_token()
                if token == ')':
                    return node
                else:
                    PcbParser.parse_recursive(inport, token, node)
        # Otherwise the token must be an atom,
        # unless there is a syntax error
        elif token == ')':
            raise Exception('Unexpected )')
        elif token is None:
            raise Exception('Unexpected EOF')
        else:
            node = TreeNode()
            node.value = token
            node.isLeaf = True
            parent.add(node)

    @staticmethod
    def get_cmd_index(tree, cmd):
        return [x[0] for x in tree].index(cmd)

    @staticmethod
    def get_cmd(tree, cmd):
        return next(x for x in tree if x[0] == cmd)

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
