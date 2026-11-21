import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Finite single-site contribution of independent endpoint sources to the
    squared modulus of the conditional phase. Each entry gives the probability
    of surviving to the site and the conditional probability of ending there. -/
namespace Shellsort.EndpointInnovationBudget

abbrev SiteSource := ℝ × ℝ

def loss (γ : ℝ) (i : SiteSource) : ℝ :=
  γ * i.1 * i.2 * (1-i.2)

/-- Sum over both survival outcomes of each independent source, weighting
    the squared modulus by its value on that joint history. -/
def expectedModulusSq (γ : ℝ) : List SiteSource → ℝ → ℝ
  | [], x => x
  | i :: rest, x =>
      (1-i.1) * expectedModulusSq γ rest x +
      i.1 * expectedModulusSq γ rest (x * (1-γ*i.2*(1-i.2)))

theorem expectedModulusSq_product (γ : ℝ) (sources : List SiteSource) (x : ℝ) :
    expectedModulusSq γ sources x = x * (sources.map (fun i => 1-loss γ i)).prod := by
  induction sources generalizing x with
  | nil => simp [expectedModulusSq]
  | cons i rest ih =>
      simp only [expectedModulusSq, ih, List.map_cons, List.prod_cons, loss]
      ring

private theorem survival_product_bounds (xs : List ℝ)
    (hx : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1) :
    1-xs.sum ≤ (xs.map (fun a => 1-a)).prod ∧
    (xs.map (fun a => 1-a)).prod ≤ 1-xs.sum+xs.sum^2/2 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx' := hx x List.mem_cons_self
      have hrest : ∀ y ∈ xs, 0 ≤ y ∧ y ≤ 1 :=
        fun y hy => hx y (List.mem_cons_of_mem _ hy)
      obtain ⟨lo,hi⟩ := ih hrest
      have neg0 : 0 ≤ 1-x := sub_nonneg.mpr hx'.2
      have s0 := List.sum_nonneg (fun y hy => (hrest y hy).1)
      have l := mul_le_mul_of_nonneg_left lo neg0
      have u := mul_le_mul_of_nonneg_left hi neg0
      simp only [List.map_cons,List.sum_cons,List.prod_cons]
      constructor
      · nlinarith [mul_nonneg hx'.1 s0]
      · nlinarith [mul_nonneg hx'.1 (sq_nonneg xs.sum),sq_nonneg x]

/-- If the sum of the mean per-source losses is at most one, the mean
    phase-innovation variance lies between half that sum and the full sum. -/
theorem innovation_variance_bounds (γ : ℝ) (sources : List SiteSource)
    (hh : ∀ i ∈ sources, 0 ≤ loss γ i ∧ loss γ i ≤ 1)
    (hs : (sources.map (loss γ)).sum ≤ 1) :
    (sources.map (loss γ)).sum / 2 ≤ 1-expectedModulusSq γ sources 1 ∧
    1-expectedModulusSq γ sources 1 ≤ (sources.map (loss γ)).sum := by
  let xs := sources.map (loss γ)
  have hx : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1 := by
    intro x h
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    exact hh i hi
  have s0 : 0 ≤ xs.sum := List.sum_nonneg (fun x h => (hx x h).1)
  have s1 : xs.sum ≤ 1 := hs
  have hu := mul_nonneg s0 (sub_nonneg.mpr s1)
  obtain ⟨a,b⟩ := survival_product_bounds xs hx
  rw [expectedModulusSq_product, one_mul]
  change xs.sum / 2 ≤ 1 - _ ∧ 1 - _ ≤ xs.sum
  have heq : (xs.map (fun a => 1-a)).prod =
      (sources.map (fun i => 1-loss γ i)).prod := by simp [xs,Function.comp_def]
  rw [← heq]
  constructor <;> nlinarith

end Shellsort.EndpointInnovationBudget
