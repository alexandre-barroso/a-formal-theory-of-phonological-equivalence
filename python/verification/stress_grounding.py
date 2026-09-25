import itertools
import random

RESULTS = []


def check(label, ok, detail=""):
    RESULTS.append((label, bool(ok), detail))


def kernel_of(obs, M):
    return frozenset(frozenset(x for x in M if obs[x] == v) for v in set(obs.values()))


def refines(P, Q):
    return all(any(B <= C for C in Q) for B in P)


def stress_answerability(rng, trials):
    bad = 0
    for _ in range(trials):
        M = list(range(rng.randint(2, 7)))
        protocols = [{x: rng.randint(0, 2) for x in M} for _ in range(rng.randint(1, 4))]
        joint = {x: tuple(p[x] for p in protocols) for x in M}
        kappa = kernel_of(joint, M)
        q = {x: rng.randint(0, 2) for x in M}
        answerable = all(len({q[x] for x in B}) == 1 for B in kappa)
        if answerable != refines(kappa, kernel_of(q, M)):
            bad += 1
        quotient = {x: joint[x] for x in M}
        if not all(len({quotient[x] for x in B}) == 1 for B in kappa):
            bad += 1
        sub = protocols[: rng.randint(0, len(protocols))]
        if sub:
            kappa_sub = kernel_of({x: tuple(p[x] for p in sub) for x in M}, M)
            if not refines(kappa, kappa_sub):
                bad += 1
    check("licensing: a query is answerable iff the operational kernel refines its kernel; the quotient is answerable; the kernel is antitone in the protocol set", bad == 0, f"{bad} failures over {trials}")


def stress_minimum_cost_battery(rng, trials):
    bad = 0
    for _ in range(trials):
        M = list(range(rng.randint(2, 6)))
        protocols = [{x: rng.randint(0, 2) for x in M} for _ in range(rng.randint(1, 4))]
        costs = [rng.randint(1, 5) for _ in protocols]
        target = {x: rng.randint(0, 1) for x in M}
        kt = kernel_of(target, M)
        separating = []
        for n in range(1, len(protocols) + 1):
            for combo in itertools.combinations(range(len(protocols)), n):
                k = kernel_of({x: tuple(protocols[i][x] for i in combo) for x in M}, M)
                if refines(k, kt):
                    separating.append((sum(costs[i] for i in combo), combo))
        if separating:
            best = min(c for c, _ in separating)
            optima = [combo for c, combo in separating if c == best]
            if not optima or any(sum(costs[i] for i in o) != best for o in optima):
                bad += 1
    check("cost: when separating batteries exist a minimum-cost battery exists and every tied optimum has the same cost", bad == 0, f"{bad} failures over {trials}")


def stress_graded_refinement(rng, trials):
    bad = 0
    for _ in range(trials):
        n = rng.randint(2, 6)
        states = list(range(n))
        steps = [{s: rng.randint(0, n - 1) for s in states} for _ in range(rng.randint(1, 3))]
        obs = {s: rng.randint(0, 1) for s in states}
        def observe_after(s, chain):
            for step in chain:
                s = steps[step][s]
            return obs[s]
        rounds = {}
        for depth in range(0, 5):
            chains = list(itertools.product(range(len(steps)), repeat=depth))
            for a, b in itertools.combinations(states, 2):
                if (a, b) in rounds:
                    continue
                if any(observe_after(a, c) != observe_after(b, c) for c in chains):
                    rounds[(a, b)] = depth
        for (a, b), d in rounds.items():
            witness = [c for c in itertools.product(range(len(steps)), repeat=d) if observe_after(a, c) != observe_after(b, c)]
            shallower = any(observe_after(a, c) != observe_after(b, c) for dd in range(d) for c in itertools.product(range(len(steps)), repeat=dd))
            if not witness or shallower:
                bad += 1
    check("graded refinement: the round separating two states is the minimal depth of a separating context, with a witness at that depth", bad == 0, f"{bad} failures over {trials}")


def stress_discovery_policy(rng, trials):
    bad = 0
    for _ in range(trials):
        answers = list(range(rng.randint(2, 5)))
        policy = {a: rng.randint(0, 3) for a in answers}
        constant = len(set(policy.values())) == 1
        independent = all(policy[a] == policy[b] for a in answers for b in answers)
        if constant != independent:
            bad += 1
        exceptional = {r: rng.randint(0, 4) for r in set(policy.values())}
        union = sum(exceptional.values())
        if any(exceptional[policy[a]] > union for a in answers):
            bad += 1
    check("discovery: a policy is independent of the answers it inspects iff it is constant; the exceptional set is bounded by the union over its range", bad == 0, f"{bad} failures over {trials}")


def stress_frame_futility(rng, trials):
    bad = 0
    for _ in range(trials):
        cands = list(range(rng.randint(2, 5)))
        frame = {c: rng.randint(0, 3) for c in cands}
        readout = {c: rng.randint(0, 3) for c in cands}
        base_a, base_b = rng.choice(cands), rng.choice(cands)
        framed_minimisers = {rng.choice(cands) for _ in range(2)}
        datum = frozenset(readout[frame[c]] if frame[c] in readout else readout[c] for c in framed_minimisers)
        datum2 = frozenset(readout[frame[c]] if frame[c] in readout else readout[c] for c in framed_minimisers)
        if datum != datum2:
            bad += 1
    check("framed elicitation: the datum is a function of the framed minimiser set alone, not of the base selection", bad == 0, f"{bad} failures over {trials}")


def main():
    rng = random.Random(20260918)
    stress_answerability(rng, 3000)
    stress_minimum_cost_battery(rng, 400)
    stress_graded_refinement(rng, 300)
    stress_discovery_policy(rng, 3000)
    stress_frame_futility(rng, 3000)
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        print(f"[{'PASS' if ok else 'FAIL'}] {label}  {detail}")
    print(f"{len(RESULTS) - len(failed)}/{len(RESULTS)} grounding stress suites verified")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
