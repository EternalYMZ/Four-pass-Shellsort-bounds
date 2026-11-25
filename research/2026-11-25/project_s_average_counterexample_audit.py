"""Independent finite audit of the uniform-input adjacent-rank counterexample.

Enumerate every balanced rank-parity word after the initial gap-2 pass.
They have equal probability under a uniform random input permutation.
Use adjacent chain exchanges to implement ordinary insertion sort.
This script is corroboration, not the analytic proof for arbitrary n.
"""

import argparse
from fractions import Fraction
from itertools import combinations
from math import comb


def verify(max_n_half: int) -> None:
    total_states = 0
    for n_half in range(1, max_n_half + 1):
        n = 2 * n_half
        ranks = set(range(n))
        loss_sum = 0
        states = 0
        for even_tuple in combinations(range(n), n_half):
            even = set(even_tuple)
            x = [0] * n
            x[::2] = even_tuple
            x[1::2] = sorted(ranks - even)
            partial_sum = 0
            prefix = []
            for rank in range(n):
                partial_sum += 1 if rank in even else -1
                prefix.append(partial_sum)
            expected = [
                abs(prefix[t - 1] - (t % 2)) // 2
                for t in range(1, n)
            ]
            pair_counts = [0] * (n - 1)
            for gap in range(n - 1, 0, -2):
                for start in range(gap):
                    for initial_pos in range(start + gap, n, gap):
                        pos = initial_pos
                        while pos >= gap and x[pos - gap] > x[pos]:
                            high, low = x[pos - gap], x[pos]
                            assert high == low + 1, (
                                n_half, even_tuple, gap, pos, high, low
                            )
                            pair_counts[low] += 1
                            x[pos - gap], x[pos] = x[pos], x[pos - gap]
                            pos -= gap
            assert x == list(range(n))
            assert pair_counts == expected, (
                n_half, even_tuple, pair_counts, expected
            )
            loss = sum(pair_counts[::2])
            assert 2 * loss == sum(
                abs(prefix[t - 1] - 1) for t in range(1, n, 2)
            )
            loss_sum += loss
            states += 1
        mean = Fraction(loss_sum, states)
        closed = Fraction(
            (n_half + 1) * 4**n_half,
            8 * comb(2 * n_half, n_half),
        )
        assert mean == closed, (n_half, mean, closed)
        print(
            f"N={n_half}: {states} equally likely states; "
            f"mean omitted successful comparisons={mean}"
        )
        total_states += states
    print(f"PASS: all per-pair trajectory identities, {total_states} states.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n-half", type=int, default=8)
    args = parser.parse_args()
    verify(args.max_n_half)
