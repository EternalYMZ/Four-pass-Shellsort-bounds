# Project S · P03 · Four-pass Shellsort bounds

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

With e = gcd(h,g), d = gcd(g,k), gcd(h,g,k) = 1 and r = n mod h, the new arithmetic lemmas identify runs of slots from long and short original chains. They bound the uniform block count d(floor(r/g) + floor((h-r)/g)) from below by d(floor(h/g)-1). The older cyclic support and variance theorems have explicit source hypotheses. The general four-pass lower bound of order n^(25/18) remains open in this formalization.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.
