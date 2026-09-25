from __future__ import annotations

import itertools
from . import certificate


def scan(values, order, predicate, stop=False):
    for node in order:
        value = values[node]
        if value is None:
            continue
        if predicate(node, value):
            return node, value
        if stop:
            return None
    return None


def resolve(values, order, predicate, stop, allowed):
    result = scan(values, order, predicate, stop)
    return result if result is not None and allowed(result[0]) else None


def exact_checks():
    cases = prefixes = scoped = 0
    for n in range(5):
        order = tuple(range(n))
        for vals in itertools.product((None, False, True), repeat=n):
            for mask in range(2**n):
                allowed = lambda k: bool(mask & (1 << k))
                predicate = lambda k, v: v
                boundary = max((k+1 for k in order if allowed(k)), default=0)
                for stop in (False, True):
                    baseline = resolve(vals, order, predicate, stop, allowed)
                    prefix = resolve(vals, order[:boundary], predicate, stop, allowed)
                    assert baseline == prefix
                    prefixes += 1
                    filtered = tuple(k for k in order if allowed(k))
                    got = resolve(vals, filtered, predicate, stop, lambda k: True)
                    direct = None
                    for k in filtered:
                        if vals[k] is True:
                            direct = k, True
                            break
                        if vals[k] is False and stop:
                            break
                    assert got == direct
                    scoped += 1
                    cases += 1
    assert cases == 2 * sum(6**n for n in range(5)) == 3110
    return {'finite_cases': cases, 'prefix_equalities': prefixes,
            'scope_before_filter_equalities': scoped}


def native_bridge():
    from . import core, frag_gua as gua
    from .footprint import footprint, footprint_profile
    sigma = gua.make_sigma()
    cases = reader_cases = 0
    scopes = [core.Scope(same=('phrase',)), core.Scope(same=('word',)), core.Scope(delta={'word':1})]
    for n in range(1,5):
        words = [int(k >= max(1,n//2)) for k in range(n)]
        reference = gua.struct_from_segments(['ɛ']*n, words, [0]*(max(words)+1))
        nodes = reference.nodes('seg')
        orders = {1: nodes, -1: nodes[::-1]}
        for ai, anchor in enumerate(nodes):
            for direction, scope, filter_name, mode, policy, coord in itertools.product(
                    (-1,1), scopes, (None,'nuclear'), ('skip','stop'),
                    ('dynamic','dynamic_in_scope','search'), ((),(('word',0),))):
                slot = core.Slot('s','Rel','subject',relation='succ',kind='search' if policy=='search' else 'step',
                    scope=scope,direction=direction,filter=filter_name,filter_mode=mode,
                    policy='dynamic' if policy=='search' else policy,coord=coord)
                d = core.Decl('support','Or',(core.Slot('t','Or','subject'),slot),
                    core.Present('t'),core.Feat('nuclear','s',True))
                assert d.well_typed(sigma)[0], d.well_typed(sigma)
                ordered = orders[direction]
                after = ordered[ordered.index(anchor)+1:]
                inside = lambda node: scope.admits(reference,anchor,node)
                coordinates = lambda node: all(reference.dom[node].get(k)==v for k,v in coord)
                selected_order = after if policy=='dynamic' else tuple(k for k in after if inside(k))
                if policy=='search': selected_order=tuple(k for k in selected_order if coordinates(k))
                accept = lambda node: (inside(node) if policy=='dynamic' else True) and coordinates(node)
                seen = {}
                for vals in itertools.product(('ɛ','t','a',core.ABSENT),repeat=n):
                    state=gua.struct_from_segments(vals,words,[0]*(max(words)+1))
                    live={node:(state.real[node] if state.real[node]!=core.ABSENT else None) for node in nodes}
                    pred=lambda node,v: filter_name is None or v in ('ɛ','a')
                    expected=resolve(live,selected_order,pred,mode=='stop' and policy!='search',accept)
                    ctx=core.Ctx(sigma,reference,state,d,anchor)
                    actual=ctx.resolve('s')
                    pair=None if actual is None else (actual,state.real[actual])
                    assert pair==expected,(vals,ai,direction,scope,filter_name,mode,policy,coord,pair,expected)
                    assert footprint_profile(state,d)=='direct_step_fixed_frame_support'
                    support=footprint(sigma,state,d,anchor)
                    key=tuple((node,state.real[node]) for node in sorted(support,key=repr))
                    readers=core.read(sigma,reference,state,d,anchor).triple()
                    assert seen.setdefault(key,readers)==readers
                    cases+=1;reader_cases+=1
    assert cases == sum(n*4**n for n in range(1,5))*144 == 180288
    return {'resolver_and_selected_value_cases':cases,'fixed_frame_reader_cases':reader_cases,
            'tokens':['ɛ','t','a',core.ABSENT], 'maximum_length':4,
            'controls':'Both directions, stop/skip, dynamic/in-scope/search, unrestricted/same-word/next-word scopes, fixed coordinates, absent anchors and neighbors.'}


def main():
    record={'generic':exact_checks(),'native':native_bridge(),
        'scope':'Fixed structural frame and current anchor-based scans. Full support handles extension predicates; productive structural composition is a separate theorem.'}
    certificate.write('footprint_support.json',record)
    print(record)


if __name__=='__main__':
    main()
