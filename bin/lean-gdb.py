import gdb
import gdb.printing

class LeanNamePrinter:
    """Print a lean::name object."""

    def __init__(self, val):
        self.val = val

    def to_string(self):
        def rec(imp):
            s = ("'%s'" % imp['m_str'].string()) if imp['m_is_string'] else str(imp['m_k'])
            if imp['m_prefix']:
                return "%s.%s" % (rec(imp['m_prefix'].dereference()), s)
            else:
                return s

        if not self.val['m_ptr']:
            return ""
        else:
            return rec(self.val['m_ptr'].dereference())

class LeanListPrinter:
    """Print a lean::list object."""

    def __init__(self, val):
        self.val = val

    def children(self):
        l = self.val
        i = 0
        while l['m_ptr']:
            cell = l['m_ptr'].dereference()
            yield ('[%s]' % i, cell['m_head'])
            l = cell['m_tail']
            i += 1

    def to_string(self):
        return str(self.val.type)

    def display_hint(self):
        return 'array'

class LeanBufferPrinter:
    """Print a lean::buffer object."""

    def __init__(self, val):
        self.val = val

    def children(self):
        p = self.val['m_buffer']
        for i in range(int(self.val['m_pos'])):
            yield ('[%s]' % i, p.dereference())
            p += 1

    def to_string(self):
        return str(self.val.type)

    def display_hint(self):
        return 'array'

class LeanExprPrinter:
    """Print a lean::expr object."""

    expr_kinds = [
        'lean::expr_var',
        'lean::expr_sort',
        'lean::expr_const',
        'lean::expr_mlocal',
        'lean::expr_mlocal',
        'lean::expr_app',
        'lean::expr_binding',
        'lean::expr_binding',
        'lean::expr_let',
        'lean::expr_macro',
    ]

    def __init__(self, val):
        kind = val['m_ptr']['m_kind']
        subtype = gdb.lookup_type(LeanExprPrinter.expr_kinds[kind])
        self.val = val['m_ptr'].cast(subtype.pointer()).dereference()

    def to_string(self):
        return str(self.val.type)

    def children(self):
        def deep_fields(v):
            for f in v.type.fields():
                if f.is_base_class:
                    for g in deep_fields(v[f]):
                        yield g
                elif f.name == 'm_kind':
                    yield (f.name, v[f].cast(gdb.lookup_type('lean::expr_kind')))
                else:
                    yield (f.name, v[f])

        return deep_fields(self.val)

def build_pretty_printer():
    pp = gdb.printing.RegexpCollectionPrettyPrinter("lean")
    pp.add_printer('name', '^lean::name$', LeanNamePrinter)
    pp.add_printer('expr', '^lean::expr$', LeanExprPrinter)
    pp.add_printer('list', '^lean::list', LeanListPrinter)
    pp.add_printer('buffer', '^lean::buffer', LeanBufferPrinter)
    return pp

gdb.printing.register_pretty_printer(
    gdb.current_objfile(),
    build_pretty_printer(),
    replace=True)
