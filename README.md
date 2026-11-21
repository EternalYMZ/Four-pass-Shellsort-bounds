# Project S · P03 · Four-pass Shellsort bounds

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

Exact fiber packing and source placement track long and short chains through each residue class. For e = gcd(h,g), d = gcd(g,k), gcd(h,g,k) = 1 and r = n mod h, the maximum common complete-block count for one multiplicity table used on every fiber is d(floor(r/g) + floor((h-r)/g)), at least d(floor(h/g)-1). The exact per-fiber and common-table statements are in [ExactFiberPacking.lean](Shellsort/ExactFiberPacking.lean). The probabilistic transfer to an unrestricted four-pass lower bound remains open.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.

## Proof guide

[Read the proof guide](brief.md). ExactFiberPacking gives the finite residue-fiber packing calculation.
