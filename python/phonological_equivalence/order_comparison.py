from fractions import Fraction
from itertools import product


def order(profiles, ranking):
    return {(x, y) for x, y in product(profiles, repeat=2)
            if tuple(profiles[x][i] for i in ranking) < tuple(profiles[y][i] for i in ranking)}


def winners(domain, edges):
    return {x for x in domain if not any((y, x) in edges for y in domain)}


def normalized(masses):
    total = sum(masses.values())
    if not masses or total <= 0 or any(v < 0 for v in masses.values()):
        raise ValueError('A finite law requires a nonempty support and positive total mass')
    return {x: Fraction(v, total) for x, v in masses.items()}
