# Project S · P03 · Four-pass Shellsort bounds

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

The source placement lemmas track long and short original chains through each residue class. For e = gcd(h,g), d = gcd(g,k), gcd(h,g,k) = 1 and r = n mod h, the conservative complete-block count d(floor(r/g) + floor((h-r)/g)) is at least d(floor(h/g)-1). A separate arithmetic theorem computes the sum of floor((W+i)/g) over 0 ≤ i < d exactly. The probabilistic transfer from block counts to an unrestricted four-pass lower bound remains open.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.

## Proof guide

[Read the proof idea in Chinese](brief.md). ExactFiberPacking gives the finite residue-fiber packing calculation.
