import Std

namespace Shellsort.FourPassCyclicSupport

/-- A forward arc from `a` of length `L` meets the projection of `0,...,B`. -/
def hits (J B L a : Nat) : Prop :=
  ∃ x ≤ B, ∃ j < L, x % J = (a + j) % J

/-- Exact criterion for every possible cut to have a positive-mass terminal arc
when the source has full support on `0,...,B`. -/
theorem every_arc_hits_iff (J B L : Nat) (hL : 0 < L) :
    (∀ a < J, hits J B L a) ↔ J ≤ B + L := by
  constructor
  · intro allHit
    by_cases bound : J ≤ B + L
    · exact bound
    · obtain ⟨x, hx, j, hj, heq⟩ := allHit (B + 1) (by omega)
      rw [Nat.mod_eq_of_lt (by omega : x < J),
          Nat.mod_eq_of_lt (by omega : B + 1 + j < J)] at heq
      omega
  · intro bound a ha
    by_cases small : a ≤ B
    · exact ⟨a, small, 0, hL, by simp⟩
    · refine ⟨0, Nat.zero_le _, J - a, by omega, ?_⟩
      rw [show a + (J - a) = J by omega]
      simp

/-- Grouping successive integer outcomes into bins leaves no holes in the support. -/
theorem rounded_image (M d α y : Nat) (hα : α < d) :
    (∃ x ≤ M, (x + α) / d = y) ↔ y ≤ (M + α) / d := by
  have hd : 0 < d := by omega
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Nat.div_le_div_right (by omega)
  · intro hy
    cases y with
    | zero => exact ⟨0, Nat.zero_le _, by simpa using Nat.div_eq_of_lt hα⟩
    | succ k =>
      have upper := (Nat.le_div_iff_mul_le hd).mp hy
      have lower : d ≤ (k + 1) * d := by
        rw [Nat.succ_mul]
        omega
      refine ⟨(k + 1) * d - α, by omega, ?_⟩
      rw [show (k + 1) * d - α + α = (k + 1) * d by omega, Nat.mul_div_cancel _ hd]

/-- The exact cyclic arc-support test for a rounded binomial with positive probabilities
on all original outcomes 0,...,M. This states the integer part of the test. -/
theorem rounded_every_arc_iff (M d α J L : Nat) (hα : α < d) (hL : 0 < L) :
    (∀ a < J, ∃ x ≤ M, ∃ j < L, (x + α) / d % J = (a + j) % J) ↔
      J ≤ (M + α) / d + L := by
  rw [← every_arc_hits_iff _ _ _ hL]
  constructor
  · intro allHit a ha
    obtain ⟨x, hx, j, hj, heq⟩ := allHit a ha
    exact ⟨(x + α) / d, (rounded_image M d α _ hα).mp ⟨x, hx, rfl⟩, j, hj, heq⟩
  · intro allHit a ha
    obtain ⟨y, hy, j, hj, heq⟩ := allHit a ha
    obtain ⟨x, hx, hxy⟩ := (rounded_image M d α y hα).mpr hy
    exact ⟨x, hx, j, hj, hxy ▸ heq⟩

end Shellsort.FourPassCyclicSupport
