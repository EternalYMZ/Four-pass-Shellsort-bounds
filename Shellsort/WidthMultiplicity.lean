import Mathlib.Tactic

open scoped BigOperators

namespace ProjectS.FourPass.WidthMultiplicity

/-- Optimum over common original source types of a given physical width,
after summing over the rounding offsets in one fiber. -/
def value (d g W : ℕ) : ℕ := d*(W/g) + (W%g+d-g)

private theorem floor_increment {g i : ℕ} (W : ℕ) (hi : i < g) :
    (W+i)/g = W/g + (if g ≤ W%g+i then 1 else 0) := by
  have hg : 0 < g := by omega
  have hw := Nat.mod_add_div W g
  have hu := Nat.mod_lt W hg
  have hlower : W/g ≤ (W+i)/g := Nat.div_le_div_right (by omega)
  have hupper : (W+i)/g < W/g+2 := by
    by_contra! hh
    have h := (Nat.le_div_iff_mul_le hg).1 hh
    rw [Nat.add_mul, Nat.two_mul, Nat.mul_comm (W/g)] at h
    omega
  by_cases hc : g ≤ W%g+i
  · simp only [ite_eq_left hc]
    have h := (Nat.le_div_iff_mul_le hg).2 (show (W/g+1)*g ≤ W+i by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (W/g)]
      omega)
    omega
  · simp only [ite_eq_right hc, Nat.add_zero]
    by_contra! hne
    have h := (Nat.le_div_iff_mul_le hg).1 (show W/g+1 ≤ (W+i)/g by omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (W/g)] at h
    omega

/-- Closed sum of the floor counts after the physical offset has been
permuted through 0,...,d-1. -/
theorem floor_sum {g : ℕ} (hg : 0 < g) (W d : ℕ) (hd : d ≤ g) :
    ∑ i ∈ Finset.range d, (W+i)/g = value d g W := by
  induction d with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, value, Nat.zero_mul,
      Nat.zero_add, Nat.add_zero]
    have hm := Nat.mod_lt W hg
    omega
  | succ d ih =>
    rw [Finset.sum_range_succ, ih (by omega), floor_increment W (by omega)]
    unfold value
    rw [Nat.succ_mul]
    split_ifs <;> omega

end ProjectS.FourPass.WidthMultiplicity
