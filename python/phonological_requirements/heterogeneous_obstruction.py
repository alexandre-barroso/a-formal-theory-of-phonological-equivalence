from __future__ import annotations

from fractions import Fraction as F
from itertools import product
from random import Random
from . import certificate
from .continuous import objective_x


def energy(xs, weights=(1, 1, -4, 1, 1, 1)):
    previous = F(1)
    total = F(0)
    for x, weight in zip(xs, weights):
        total += 5 * max(previous - x, 0)**2 + weight * x
        previous = x
    return total


def support_remainder(xs, drops):
    zs = [u-v for u, v in zip([F(1), *xs], xs)]
    terms = [max(z, 0)**2 - 2*v*z + v*v for z, v in zip(zs, drops)]
    assert all(t >= 0 for t in terms)
    return 5 * sum(terms)


def main():
    witness = list(map(F, ['4/5', '7/10', '1', '7/10', '1/2', '2/5']))
    monotone = list(map(F, ['9/10', '9/10', '9/10', '3/5', '2/5', '3/10']))
    original_drops = list(map(F, ['1/5', '1/10', '0', '3/10', '1/5', '1/10']))
    monotone_drops = list(map(F, ['1/10', '0', '0', '3/10', '1/5', '1/10']))
    assert energy(witness) == F(1, 20)
    assert energy(monotone) == F(1, 4)
    rng = Random(20260919)
    cases = [tuple(witness), tuple(monotone)]
    cases.extend(product([F(k, 4) for k in range(5)], repeat=6))
    cases.extend(tuple(F(rng.randrange(101), 100) for _ in range(6)) for _ in range(2000))
    monotone_cases = 0
    for xs in cases:
        val = energy(xs)
        assert val == objective_x(F(5), [F(1), F(1), F(-4), F(1), F(1), F(1)], 2, [F(1), *xs])
        assert val - F(1, 20) == support_remainder(xs, original_drops) + 1-xs[2]
        assert val >= F(1, 20)
        assert val - F(1, 4) == support_remainder(xs, monotone_drops) + xs[1]-xs[2]
        if all(u >= v for u, v in zip([F(1), *xs], xs)):
            assert val >= F(1, 4)
            monotone_cases += 1
    assert len(cases) == 17627 and monotone_cases >= 211
    mutants = {
        'alter_negative_weight': energy(witness, (1, 1, -3, 1, 1, 1)) != F(1, 20),
        'symmetric_drop': 5*sum((u-v)**2 for u, v in zip([F(1), *witness], witness)) + sum(w*x for w, x in zip((1,1,-4,1,1,1), witness)) != F(1,20),
        'erase_monotonicity_premise': energy(witness) < F(1, 4),
    }
    assert all(mutants.values())
    result = {'native_original_comparisons': len(cases), 'monotone_checks': monotone_cases,
              'seed': 20260919, 'original_witness': list(map(str, witness)),
              'original_minimum': '1/20', 'monotone_witness': list(map(str, monotone)),
              'monotone_minimum': '1/4', 'detected_mutations': mutants,
              'scope': 'Exact continuous six-site witness; universal lower bounds are independently proved in Lean and Wolfram. No assertion that every negative site causes failure.'}
    certificate.write('heterogeneous_obstruction.json', result)
    print(result)


if __name__ == '__main__':
    main()
