import Shellsort.ModularCut

noncomputable section
namespace Shellsort

/-- After an odd-gap sort, each low key in parity class `r` occurring at or
beyond the first `g` positions has a distinct low predecessor of the opposite
parity. The unmatched positions are bounded by the number of slots of parity
`r` below `g`. Positions and key ranks are numbered starting at zero. -/
theorem oddGap_parity_count_le {n g : ℕ} (p : RankPlacement n)
    (hg : g % 2 = 1) (t r : ℕ) (hr : r < 2) :
    chainLowerCount (thresholdSet (gapSort p g) t) 2 r ≤
      chainLowerCount (thresholdSet (gapSort p g) t) 2 (1 - r) + (g + 1 - r) / 2 := by
  classical
  let B := thresholdSet (gapSort p g) t
  let E := B.filter (fun i => i.val % 2 = r)
  let O := B.filter (fun i => i.val % 2 = 1 - r)
  have head : (E.filter (fun i => i.val < g)).card ≤ (g + 1 - r) / 2 := by
    rw [← Finset.card_range ((g + 1 - r) / 2)]
    apply Finset.card_le_card_of_injOn (fun i : Fin n => i.val / 2)
    · intro i hi
      obtain ⟨hiE, hlt⟩ := Finset.mem_filter.mp hi
      have hpar := (Finset.mem_filter.mp hiE).2
      apply Finset.mem_range.mpr
      change i.val / 2 < (g + 1 - r) / 2
      omega
    · intro i hi j hj hij
      have hiE := (Finset.mem_filter.mp hi).1
      have hjE := (Finset.mem_filter.mp hj).1
      have hpi := (Finset.mem_filter.mp hiE).2
      have hpj := (Finset.mem_filter.mp hjE).2
      apply Fin.ext
      change i.val / 2 = j.val / 2 at hij
      omega
  let pred (i : Fin n) : Fin n := ⟨i.val - g, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  have tail : (E.filter (fun i => ¬ i.val < g)).card ≤ O.card := by
    apply Finset.card_le_card_of_injOn pred
    · intro i hi
      obtain ⟨hiE, hlt⟩ := Finset.mem_filter.mp hi
      obtain ⟨hiB, hpar⟩ := Finset.mem_filter.mp hiE
      have hpg : (pred i).val + g = i.val := Nat.sub_add_cancel (by omega)
      apply Finset.mem_filter.mpr
      constructor
      · apply gapSort_threshold_prefix p t g i (pred i) hiB
        · calc
            (pred i).val % g = ((pred i).val + g) % g := by simp
            _ = i.val % g := by rw [hpg]
        · change i.val - g < i.val
          omega
      · omega
    · intro i hi j hj hij
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      have heq := congrArg Fin.val hij
      change i.val - g = j.val - g at heq
      apply Fin.ext
      omega
  have split := Finset.card_filter_add_card_filter_not (s := E) (fun i => i.val < g)
  change E.card ≤ O.card + _
  omega

/-- Any subsequent list of even gaps leaves the two threshold counts unchanged. -/
theorem oddGap_evenWord_parity_count_le {n g : ℕ} (p : RankPlacement n)
    (hg : g % 2 = 1) (gaps : List ℕ) (he : ∀ h ∈ gaps, 2 ∣ h)
    (t r : ℕ) (hr : r < 2) :
    chainLowerCount (thresholdSet (sortWord (gapSort p g) gaps) t) 2 r ≤
      chainLowerCount (thresholdSet (sortWord (gapSort p g) gaps) t) 2 (1 - r) +
        (g + 1 - r) / 2 := by
  simp only [sortWord_threshold_divisor_count _ gaps he]
  exact oddGap_parity_count_le p hg t r hr

/-- Number of low keys on even slots minus their number on odd slots. -/
def thresholdParityBias {n : ℕ} (p : RankPlacement n) (t : ℕ) : ℤ :=
  (chainLowerCount (thresholdSet p t) 2 0 : ℤ) - chainLowerCount (thresholdSet p t) 2 1

/-- Error of the signed low-key parity count relative to the completely
sorted array, after an odd pass and any subsequent list of even passes. -/
theorem oddGap_evenWord_parity_error {n g : ℕ} (p : RankPlacement n)
    (hg : g % 2 = 1) (gaps : List ℕ) (he : ∀ h ∈ gaps, 2 ∣ h) (t : ℕ) :
    |thresholdParityBias (sortWord (gapSort p g) gaps) t -
      thresholdParityBias (Equiv.refl (Fin n)) t| ≤ (((g + 1) / 2 : ℕ) : ℤ) := by
  have h0 := oddGap_evenWord_parity_count_le p hg gaps he t 0 (by decide)
  have h1 := oddGap_evenWord_parity_count_le p hg gaps he t 1 (by decide)
  have e0 := oddGap_parity_count_le (g := 1) p (by decide) t 0 (by decide)
  have e1 := oddGap_parity_count_le (g := 1) p (by decide) t 1 (by decide)
  simp only [gapSort_one] at e0 e1
  simp at h0 h1 e0 e1
  unfold thresholdParityBias
  rw [abs_le]
  constructor <;> omega

end Shellsort
