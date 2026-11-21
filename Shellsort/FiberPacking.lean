import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic

namespace ProjectS.FourPass.FiberPacking

/-- First progression index whose physical slot lies at least at the cut. -/
def first (D b cut : ℕ) : ℕ := (cut + (D-1-b)) / D

theorem first_bounds {D b : ℕ} (hb : b < D) (cut : ℕ) :
    cut ≤ b + D * first D b cut ∧ b + D * first D b cut < cut + D := by
  unfold first
  have h := Nat.mod_add_div (cut + (D-1-b)) D
  have h' := Nat.mod_lt (cut + (D-1-b)) (by omega : 0 < D)
  omega

/-- Every chosen run of J consecutive source indices lies in the same physical
type interval [cut,cut+width), for any offset of the physical progression. -/
theorem run_in_band {D b J : ℕ} (hb : b < D) (cut width a j : ℕ)
    (ha : a < width / (D*J)) (hj : j < J) :
    let u := first D b cut + (a*J+j)
    cut ≤ b + D*u ∧ b + D*u < cut + width := by
  dsimp only
  obtain ⟨hlo,hhi⟩ := first_bounds hb cut
  have h1 : a*J+j+1 ≤ (a+1)*J := by rw [Nat.add_mul]; simp; omega
  have h2 := Nat.mul_le_mul_right J (show a+1 ≤ width/(D*J) by omega)
  have h3 := Nat.mul_le_mul_left D (h1.trans h2)
  have h4 := Nat.mul_div_le width (D*J)
  have h5 : D*(width/(D*J)*J) = (D*J)*(width/(D*J)) := by ring
  rw [h5] at h3
  rw [Nat.mul_add] at h3 ⊢
  omega

/-- Rephasing a run of J consecutive indices preserves full residue coverage. -/
theorem phase_hits {J : ℕ} (hJ : 0 < J) (base t : ℕ) (ht : t < J) :
    ∃ j < J, (base+j) % J = t := by
  let _ : NeZero J := ⟨Nat.ne_of_gt hJ⟩
  let v : Fin J := ⟨t, ht⟩
  let u : Fin J := ⟨base%J, Nat.mod_lt _ hJ⟩
  let j := v - u
  refine ⟨j.val, j.isLt, ?_⟩
  have he : u+j=v := by dsimp [j]; abel
  have hv := congrArg Fin.val he
  change (base%J+j.val)%J=t at hv
  simpa [Nat.add_mod, Nat.mod_eq_of_lt j.isLt] using hv

/-- The two capacities lose at most one full block in total per rounding
type. This bound uses the original long and short sources separately. -/
theorem split_floor_bounds {g : ℕ} (hg : 0 < g) (x y : ℕ) :
    x/g+y/g ≤ (x+y)/g ∧ (x+y)/g ≤ x/g+y/g+1 := by
  have hx := Nat.mod_add_div x g
  have hy := Nat.mod_add_div y g
  have hz := Nat.mod_add_div (x+y) g
  have hmx := Nat.mod_lt x hg
  have hmy := Nat.mod_lt y hg
  constructor
  · apply (Nat.le_div_iff_mul_le hg).2
    rw [Nat.add_mul, Nat.mul_comm (x/g), Nat.mul_comm (y/g)]
    omega
  · by_contra! hn
    have mul := Nat.mul_le_mul_left g (show x/g+y/g+2 ≤ (x+y)/g by omega)
    rw [Nat.mul_add,Nat.mul_add,Nat.mul_two] at mul
    omega

def commonBlocks (d h g r : ℕ) : ℕ := d*(r/g + (h-r)/g)

theorem common_blocks_bounds {d h g r : ℕ} (hg : 0 < g) (hr : r ≤ h) :
    d*(h/g-1) ≤ commonBlocks d h g r ∧ commonBlocks d h g r ≤ d*(h/g) := by
  obtain ⟨h1,h2⟩ := split_floor_bounds hg r (h-r)
  have he : r+(h-r)=h := by omega
  rw [he] at h1 h2
  have hsub : h/g-1 ≤ r/g+(h-r)/g := Nat.sub_le_of_le_add (by simpa [Nat.add_comm] using h2)
  exact ⟨Nat.mul_le_mul_left d hsub, Nat.mul_le_mul_left d h1⟩

theorem two_gap_ratio {d h g r : ℕ} (hg : 0 < g) (hr : r ≤ h) (hQ : h/g=2) :
    d ≤ commonBlocks d h g r := by simpa [hQ] using (common_blocks_bounds (d:=d) hg hr).1

private theorem physical_type {x h nu : ℕ} (hh : 0 < h)
    (lo : nu*h ≤ x) (hi : x < (nu+1)*h) :
    x/h = nu ∧ nu*h + x%h = x := by
  have hlo := (Nat.le_div_iff_mul_le hh).2 lo
  have hhi : ¬nu+1 ≤ x/h := fun hx => (Nat.not_le_of_lt hi) ((Nat.le_div_iff_mul_le hh).1 hx)
  have eq : x/h=nu := by omega
  refine ⟨eq, ?_⟩
  have hm := Nat.mod_add_div x h
  rw [eq, Nat.mul_comm h nu, Nat.add_comm] at hm
  exact hm

/-- A retained original long-chain source has the stated quotient and residue. -/
theorem long_run_type {D b J h r : ℕ} (hb : b < D) (hh : 0 < h) (hr : r ≤ h)
    (nu a j : ℕ) (ha : a < r/(D*J)) (hj : j < J) :
    let x := b+D*(first D b (nu*h)+(a*J+j))
    x/h=nu ∧ x%h < r := by
  dsimp only
  obtain ⟨lo,hi⟩ := run_in_band hb (nu*h) r a j ha hj
  have upper := hi.trans_le (Nat.add_le_add_left hr (nu*h))
  rw [← Nat.succ_mul] at upper
  obtain ⟨eq,hm⟩ := physical_type hh lo upper
  exact ⟨eq, by omega⟩

/-- A retained original short-chain source has the stated quotient and residue. -/
theorem short_run_type {D b J h r : ℕ} (hb : b < D) (hh : 0 < h) (hr : r ≤ h)
    (nu a j : ℕ) (ha : a < (h-r)/(D*J)) (hj : j < J) :
    let x := b+D*(first D b (nu*h+r)+(a*J+j))
    x/h=nu ∧ r ≤ x%h := by
  dsimp only
  obtain ⟨lo,hi⟩ := run_in_band hb (nu*h+r) (h-r) a j ha hj
  have bounds : nu*h+r+(h-r)=(nu+1)*h := by rw [Nat.succ_mul]; omega
  rw [bounds] at hi
  obtain ⟨eq,hm⟩ := physical_type hh ((Nat.le_add_right _ _).trans lo) hi
  exact ⟨eq, by omega⟩

end ProjectS.FourPass.FiberPacking
