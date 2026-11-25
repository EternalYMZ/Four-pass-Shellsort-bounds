#!/usr/bin/env python3
"""Independent exact checks for cumulative rank-bucket error obstructions.

Pure Python; no floating-point assertions.  This is finite verification, not the
analytic proof (see J6 and J7 in README.md).  Ranks and positions are 0-based.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb
import json
from pathlib import Path


def gap_pass(values, gap):
    """Ordinary stable chain insertion, implemented by adjacent chain swaps."""
    x = list(values)
    events = []
    comparisons = 0
    for end in range(gap, len(x)):
        pos = end
        while pos >= gap:
            comparisons += 1
            if x[pos-gap] < x[pos]:
                break
            events.append((x[pos-gap], x[pos], pos-gap, pos))
            x[pos-gap], x[pos] = x[pos], x[pos-gap]
            pos -= gap
    return x, events, comparisons


def inversion_count(x):
    return sum(x[i] > x[j] for i in range(len(x)) for j in range(i+1, len(x)))


def is_two_sorted(x):
    return all(x[i] < x[i+2] for i in range(len(x)-2))


def bridge_statistics(x):
    """x must be 2-sorted.  Output prediction by rank-pair and initial bridge."""
    pos = [0] * len(x)
    for i, rank in enumerate(x):
        pos[rank] = i
    balance = 0
    bridge = []
    prediction = []
    for t in range(1, len(x)):
        balance += 1 if pos[t-1] % 2 == 0 else -1
        bridge.append(balance)
        delta = abs(balance - (t % 2))
        assert delta % 2 == 0
        prediction.append(delta // 2)
    return prediction, bridge


def check_odd_suffix(x):
    n = len(x)
    assert n % 2 == 0 and is_two_sorted(x)
    prediction, bridge = bridge_statistics(x)
    observed = [0] * (n-1)
    old_I = inversion_count(x)
    total_moves = 0
    for gap in range(n-1, 0, -2):
        y, events, _ = gap_pass(x, gap)
        assert is_two_sorted(y)
        for a, b, _, _ in events:
            assert a == b + 1, (n, x, gap, events)
            observed[b] += 1
        assert old_I - inversion_count(y) == len(events)
        total_moves += len(events)
        old_I -= len(events)
        x = y
    assert x == list(range(n))
    assert observed == prediction
    assert sum(prediction) == total_moves
    omitted = sum(observed[::2])
    assert omitted == sum(abs(bridge[t-1]-1)//2 for t in range(1, n, 2))
    return omitted, total_moves


def exact_mean_from_hypergeometric(n):
    """Mean suffix omitted successes for buckets {0,1},{2,3},..."""
    N = n // 2
    total = Fraction(0)
    for t in range(1, n, 2):
        numerator = 0
        for k in range(max(0, t-N), min(N, t)+1):
            numerator += abs(2*k-t-1) * comb(N, k) * comb(N, t-k)
        total += Fraction(numerator, 2 * comb(n, t))
    return total


def exact_mean_closed_form(n):
    N = n // 2
    return Fraction((N+1) * 4**N, 8 * comb(n, N))


def exact_balanced_states(n):
    N = n // 2
    for even_ranks in combinations(range(n), N):
        evens = set(even_ranks)
        odd_ranks = [rank for rank in range(n) if rank not in evens]
        x = [0] * n
        x[::2] = even_ranks
        x[1::2] = odd_ranks
        yield x


def main():
    result = {"scope": "exact finite checks; no Lean proof; no asymptotic inference from samples"}
    family_count = 0
    for N in range(1, 129):
        n = 2*N
        x = [v for i in range(N) for v in (N+i, i)]
        total = omitted = 0
        for j in range(1, N+1):
            gap = 2*N-2*j+1
            x, events, _ = gap_pass(x, gap)
            expected_even = [N+i-max(j-i, 0) for i in range(N)]
            expected_odd = [i+max(i-N+j+1, 0) for i in range(N)]
            assert x[::2] == expected_even
            assert x[1::2] == expected_odd
            expected_pairs = [(N-j+1+2*i, N-j+2*i) for i in range(j)]
            assert [(a,b) for a,b,_,_ in events] == expected_pairs
            total += len(events)
            omitted += sum(a//2 == b//2 for a,b,_,_ in events)
        assert total == N*(N+1)//2
        assert omitted == (N+1)**2//4
        family_count += 1
    result["deterministic_family"] = {"N_min": 1, "N_max": 128, "instances": family_count,
                                        "all_pass_formulas_verified": True}

    mean_checks = []
    for n in range(2, 18, 2):
        sm = tm = count = 0
        for x in exact_balanced_states(n):
            omitted, moves = check_odd_suffix(x)
            sm += omitted
            tm += moves
            count += 1
        actual = Fraction(sm, count)
        expected = exact_mean_from_hypergeometric(n)
        assert actual == expected
        assert actual == exact_mean_closed_form(n)
        # Square the proven bounds to keep checks exact.
        if n % 4 == 0:
            assert actual * actual >= Fraction(n**3, 32**2)
        assert actual * actual <= Fraction(n**3, 4**2)
        mean_checks.append({"n": n, "balanced_states": count,
                            "mean_omitted_successes": str(actual),
                            "mean_all_suffix_successes": str(Fraction(tm, count)),
                            "hypergeometric_formula_match": True,
                            "closed_form_match": True})
    result["uniform_input_exact_checks"] = mean_checks
    result["balanced_states_checked"] = sum(q["balanced_states"] for q in mean_checks)

    # Check all finite bridge moments exactly, including the fourth moment bound.
    moments = 0
    for n in range(4, 82, 2):
        N = n//2
        for t in range(1, n):
            den = comb(n,t)
            v = sum(Fraction((2*k-t)**2 * comb(N,k)*comb(N,t-k), den)
                    for k in range(max(0,t-N), min(N,t)+1))
            fourth = sum(Fraction((2*k-t)**4 * comb(N,k)*comb(N,t-k), den)
                         for k in range(max(0,t-N), min(N,t)+1))
            assert v == Fraction(t*(n-t), n-1)
            assert fourth == Fraction(t*(n-t)*(3*t*(n-t)-2*n), (n-1)*(n-3))
            assert fourth <= 3*v*v
            moments += 1
    result["exact_moment_checks"] = {"even_n_min": 4, "even_n_max": 80,
                                      "all_t_in_1_to_n_minus_1": True, "cases": moments}

    telescopes = 0
    for N in range(1, 81):
        n = 2*N
        assert exact_mean_from_hypergeometric(n) == exact_mean_closed_form(n)
        for a in range(N):
            b = N-1-a
            for r in range(min(a,b)+1):
                q = comb(2*a+1,a+1+r)*comb(2*b+1,b-r)
                F = Fraction((a+r+1)*(b+r+1)*q,N)
                if r < min(a,b):
                    qn = comb(2*a+1,a+2+r)*comb(2*b+1,b-r-1)
                    Fn = Fraction((a+r+2)*(b+r+2)*qn,N)
                else:
                    Fn = Fraction(0)
                assert F-Fn == (2*r+1)*q
                telescopes += 1
    result["closed_form_checks"] = {"N_min":1,"N_max":80,
        "hypergeometric_equals_closed_form":True,"telescoping_instances":telescopes}

    x = [2,1,3,0]
    stages = [x.copy()]
    omitted = 0
    pair_10 = 0
    for gap in (2,3,1):
        x, events, _ = gap_pass(x,gap)
        stages.append(x.copy())
        omitted += sum(a//2 == b//2 for a,b,_,_ in events)
        pair_10 += sum((a,b)==(1,0) for a,b,_,_ in events)
    assert omitted == 3 and pair_10 == 2
    result["four_element_repeated_pair"] = {"stages": stages, "gaps": [2,3,1],
        "same_bucket_successes": omitted, "pair_1_0_successes": pair_10}

    output = Path(__file__).with_name("cumulative_error_results.json")
    output.write_text(json.dumps(result, indent=2, ensure_ascii=False)+"\n", encoding="utf-8")
    print(json.dumps(result, indent=2, ensure_ascii=False))

if __name__ == "__main__":
    main()
