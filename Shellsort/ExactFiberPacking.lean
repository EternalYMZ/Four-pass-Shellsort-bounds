import Shellsort.FiberPacking
import Shellsort.WidthMultiplicity

namespace ProjectS.FourPass.ExactFiberPacking
open FiberPacking WidthMultiplicity
open scoped BigOperators

/-- An actual allocation chooses distinct compressed indices z. Its physical
slot is f+d*z; all G possible residue labels must be realized in each block. -/
def Allocates (d f A W G q : ℕ) : Prop :=
  ∃ z : Fin q × Fin G → ℕ, Function.Injective z ∧
    ∀ p, A ≤ f+d*z p ∧ f+d*z p < A+W ∧ z p % G = p.2.val

private theorem cut_iff {d f : ℕ} (hf : f<d) (A z : ℕ) :
    A ≤ f+d*z ↔ first d f A ≤ z := by
  obtain ⟨lo,hi⟩ := first_bounds hf A
  constructor
  · intro hx
    by_contra! hn
    have inc := Nat.mul_le_mul_left d (show z+1 ≤ first d f A by omega)
    rw [Nat.mul_add,Nat.mul_one] at inc
    omega
  · intro hz
    have inc := Nat.mul_le_mul_left d hz
    omega

private theorem band_width {d f : ℕ} (hf : f<d) (A W : ℕ) :
    first d f (A+W) = first d f A + (W+(A+(d-1-f))%d)/d := by
  let x := A+(d-1-f)
  have hx := Nat.mod_add_div x d
  have hF : A+W+(d-1-f) = (W+x%d) + d*(x/d) := by dsimp [x] at *; omega
  unfold first
  rw [hF,Nat.add_mul_div_left _ _ (by omega)]
  dsimp [x]
  omega

private theorem range_iff {d f : ℕ} (hf : f<d) (A W z : ℕ) :
    (A ≤ f+d*z ∧ f+d*z < A+W) ↔
      first d f A ≤ z ∧ z < first d f A + (W+(A+(d-1-f))%d)/d := by
  have c₁ := cut_iff hf A z
  have c₂ := cut_iff hf (A+W) z
  rw [band_width hf A W] at c₂
  omega

def capacity (d f A W G : ℕ) := (W+(A+(d-1-f))%d)/(d*G)

/-- Exact maximum, allowing arbitrary assignments rather than just consecutive runs. -/
theorem allocation_iff {d f G : ℕ} (hf : f<d) (hg : 0<G) (A W q : ℕ) :
    Allocates d f A W G q ↔ q ≤ capacity d f A W G := by
  let L := first d f A
  let T := (W+(A+(d-1-f))%d)/d
  have hc : capacity d f A W G = T/G := by simp [capacity,T,Nat.div_div_eq_div_mul]
  rw [hc, Nat.le_div_iff_mul_le hg]
  constructor
  · rintro ⟨z,hinj,hz⟩
    have valid (p) : L ≤ z p ∧ z p < L+T :=
      (range_iff hf A W _).mp ⟨(hz p).1,(hz p).2.1⟩
    let pick (p) : Fin T := ⟨z p-L, by have := valid p; omega⟩
    have one : Function.Injective pick := by
      intro p s hp
      have vv : z p-L=z s-L := congrArg Fin.val hp
      have := valid p
      have := valid s
      exact hinj (by omega)
    simpa using Fintype.card_le_of_injective pick one
  · intro enough
    let _ : NeZero G := ⟨by omega⟩
    let start : Fin G := ⟨L%G,Nat.mod_lt _ hg⟩
    let ix (p : Fin q × Fin G) : Fin (q*G) := finProdFinEquiv (p.1,p.2-start)
    let z (p) := L+(ix p).val
    refine ⟨z, ?_, ?_⟩
    · intro p s hp
      have he : (ix p).val=(ix s).val := Nat.add_left_cancel hp
      have eq := finProdFinEquiv.injective (Fin.ext he)
      change (p.1,p.2-start)=(s.1,s.2-start) at eq
      have eq₁ : p.1=s.1 := (Prod.mk.inj eq).1
      have eq₂ : p.2-start=s.2-start := (Prod.mk.inj eq).2
      exact Prod.ext eq₁ (by simpa using congrArg (fun v : Fin G => v+start) eq₂)
    · intro p
      have hi := (ix p).isLt
      have inside := (range_iff hf A W (z p)).mpr (by change L≤L+_ ∧ L+_ < L+T; omega)
      refine ⟨inside.1,inside.2,?_⟩
      have phase : start+(p.2-start)=p.2 := by abel
      have hh := congrArg Fin.val phase
      change (L%G+(p.2-start).val)%G=p.2.val at hh
      change (L+((p.2-start).val+G*p.1.val))%G=p.2.val
      rw [←Nat.add_assoc,Nat.add_mul_mod_self_left]
      simpa [Nat.add_mod,Nat.mod_eq_of_lt (p.2-start).isLt] using hh

private noncomputable def offsets {d h : ℕ} (hd : 0<d) (hh : Nat.Coprime d h) (c : ℕ) :
    Fin d ≃ Fin d := by
  let F (i : Fin d) : Fin d := ⟨(i.val*h+c)%d,Nat.mod_lt _ hd⟩
  have inj : Function.Injective F := by
    intro i j he
    have hm : i.val*h+c ≡ j.val*h+c [MOD d] := congrArg Fin.val he
    have hs := Nat.ModEq.cancel_right_of_coprime hh (hm.add_right_cancel' c)
    exact Fin.ext (by simpa [Nat.ModEq,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using hs)
  exact Equiv.ofBijective F ((Finite.injective_iff_bijective).mp inj)

theorem width_total {d f h G : ℕ} (hf : f<d) (hg : 0<G) (hh : Nat.Coprime d h) (a W : ℕ) :
    (∑ i : Fin d, capacity d f (i.val*h+a) W G) = value d (d*G) W := by
  let c := a+(d-1-f)
  let σ := offsets (d:=d) (h:=h) (by omega) hh c
  calc
    _ = ∑ i : Fin d, (fun j : Fin d => (W+j.val)/(d*G)) (σ i) := by
      apply Finset.sum_congr rfl; intro i _
      change (W+((i.val*h+a)+(d-1-f))%d)/(d*G)=(W+(i.val*h+c)%d)/(d*G)
      rw [Nat.add_assoc]
    _ = ∑ j : Fin d, (W+j.val)/(d*G) := σ.sum_comp (fun j : Fin d => (W+j.val)/(d*G))
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun i => (W+i)/(d*G))]
      exact floor_sum (Nat.mul_pos (by omega) hg) _ _ (by nlinarith)

/-- Feasible means a common number for all phase labels within each original
type. The numbers may vary with the quotient and with the long/short label. -/
def Feasible (d f h r G total : ℕ) : Prop :=
  ∃ a b : Fin d → ℕ, total=(∑ i,a i)+(∑ i,b i) ∧ ∀ i : Fin d,
    Allocates d f (i.val*h) r G (a i) ∧ Allocates d f (i.val*h+r) (h-r) G (b i)

theorem exact_two_types {d f h r G : ℕ} (hf : f<d) (hg : 0<G)
    (hh : Nat.Coprime d h) (_hr : r≤h) :
    IsGreatest {q | Feasible d f h r G q} (value d (d*G) r + value d (d*G) (h-r)) := by
  let a (i : Fin d) := capacity d f (i.val*h) r G
  let b (i : Fin d) := capacity d f (i.val*h+r) (h-r) G
  have sa : ∑ i,a i = value d (d*G) r := by simpa [a] using width_total hf hg hh 0 r
  have sb : ∑ i,b i = value d (d*G) (h-r) := width_total hf hg hh r (h-r)
  constructor
  · exact ⟨a,b,by rw [sa,sb],fun i => ⟨(allocation_iff hf hg _ _ _).mpr le_rfl,
                                          (allocation_iff hf hg _ _ _).mpr le_rfl⟩⟩
  · rintro q ⟨u,v,he,ok⟩
    rw [he,←sa,←sb]
    exact Nat.add_le_add (Finset.sum_le_sum (fun i _ => (allocation_iff hf hg _ _ _).mp (ok i).1))
      (Finset.sum_le_sum (fun i _ => (allocation_iff hf hg _ _ _).mp (ok i).2))

/-- Distinct selected compressed slots name distinct sources on a physical fiber. -/
theorem source_injective {d h : ℕ} (hh : Nat.Coprime d h) (f : ℕ) :
    Function.Injective (fun z : Fin h => (f+d*z.val)%h) := by
  intro z w he
  have hm : f+d*z.val ≡ f+d*w.val [MOD h] := he
  have hc := Nat.ModEq.cancel_left_of_coprime hh.symm (hm.add_left_cancel' f)
  exact Fin.ext (by simpa [Nat.ModEq,Nat.mod_eq_of_lt z.isLt,Nat.mod_eq_of_lt w.isLt] using hc)

theorem type_bands {h r : ℕ} (hh : 0<h) (hr : r≤h) (ν x : ℕ) :
    (ν*h≤x ∧ x<ν*h+r ↔ x/h=ν ∧ x%h<r) ∧
    (ν*h+r≤x ∧ x<(ν+1)*h ↔ x/h=ν ∧ r≤x%h) := by
  have rem := Nat.mod_lt x hh
  have qr := Nat.mod_add_div x h
  have lower := Nat.le_div_iff_mul_le (x:=ν) (y:=x) hh
  have upper := Nat.div_lt_iff_lt_mul (y:=ν+1) (x:=x) hh
  rw [Nat.add_mul,one_mul] at upper ⊢
  have digit (he : x/h=ν) : x%h+ν*h=x := by simpa [he,Nat.mul_comm] using qr
  constructor <;> constructor
  · rintro ⟨ha,hb⟩
    have he : x/h=ν := by omega
    have := digit he
    exact ⟨he,by omega⟩
  · rintro ⟨he,hr'⟩
    have := digit he
    omega
  · rintro ⟨ha,hb⟩
    have he : x/h=ν := by omega
    have := digit he
    exact ⟨he,by omega⟩
  · rintro ⟨he,hr'⟩
    have := digit he
    omega

/-- Mixed-radix digits identify the physical class and, after the anchor
permutation, its chain anchor. -/
def classAnchor {e J : ℕ} (π : Equiv.Perm (Fin J)) : Fin (J*e) ≃ Fin e × Fin J :=
  ((finProdFinEquiv.symm).trans (Equiv.prodComm _ _)).trans ((Equiv.refl _).prodCongr π)

theorem classAnchor_digits {e J : ℕ} (he : 0<e) (hJ : 0<J)
    (π : Equiv.Perm (Fin J)) (z : ℕ) :
    classAnchor π ⟨z%(J*e),Nat.mod_lt _ (Nat.mul_pos hJ he)⟩ =
    (⟨z%e,Nat.mod_lt _ he⟩,π ⟨z/e%J,Nat.mod_lt _ hJ⟩) := by
  apply Prod.ext
  · apply Fin.ext
    exact Nat.mod_mul_left_mod z J e
  · apply congrArg π
    apply Fin.ext
    exact Nat.mod_mul_left_div_self z e J

/-- The inverse of multiplication by H gives the actual phase anchor. -/
noncomputable def anchorPerm {H J : ℕ} (hJ : 0<J) (hh : Nat.Coprime H J) :
    Equiv.Perm (Fin J) := (offsets hJ hh.symm 0).symm

theorem anchor_spec {H J : ℕ} (hJ : 0<J) (hh : Nat.Coprime H J) (u : Fin J) :
    ((anchorPerm hJ hh u).val*H)%J = u.val := by
  have eq := congrArg Fin.val ((offsets hJ hh.symm 0).apply_symm_apply u)
  change (((anchorPerm hJ hh u).val*H+0)%J) = u.val at eq
  exact eq

/-- Physical slots in the d quotient bands neither duplicate a source
between bands nor give that source a conflicting long/short type. -/
theorem source_unique_across_types {d f h r z w : ℕ} (hh : Nat.Coprime d h)
    (hz : f+d*z<d*h) (hw : f+d*w<d*h)
    (same : (f+d*z)%h=(f+d*w)%h) :
    z=w ∧ (f+d*z)/h=(f+d*w)/h ∧
    ((f+d*z)%h<r ↔ (f+d*w)%h<r) := by
  have bounded (t : ℕ) (ht : f+d*t<d*h) : t<h := by
    by_contra! hn
    have bound := Nat.mul_le_mul_left d hn
    omega
  have he := (source_injective hh f) (a₁ := ⟨z,bounded z hz⟩) (a₂ := ⟨w,bounded w hw⟩) same
  have eq : z=w := congrArg Fin.val he
  simp [eq]

/-- The number of blocks a *single fixed type* can supply simultaneously
in all physical fibers. A worst fiber hits the exact no-rounding phase. -/
theorem all_fibers_iff {d G : ℕ} (hd : 0<d) (hg : 0<G) (A W q : ℕ) :
    (∀ f : Fin d, Allocates d f.val A W G q) ↔ q ≤ W/(d*G) := by
  let b := A+(d-1)
  let f : Fin d := ⟨b%d, Nat.mod_lt _ hd⟩
  have hf := f.isLt
  have eq : A+(d-1-f.val)=d*(b/d) := by
    have := Nat.mod_add_div b d
    change b%d < d at hf
    change A+(d-1-b%d)=d*(b/d)
    dsimp [b] at *
    omega
  constructor
  · intro works
    have bound := (allocation_iff f.isLt hg A W q).mp (works f)
    simpa [capacity,eq] using bound
  · intro bound u
    apply (allocation_iff u.isLt hg A W q).mpr
    exact bound.trans (Nat.div_le_div_right (Nat.le_add_right _ _))

def FeasibleAll (d h r G total : ℕ) : Prop :=
  ∃ a b : Fin d → ℕ, total=(∑ i,a i)+(∑ i,b i) ∧ ∀ i : Fin d, ∀ f : Fin d,
    Allocates d f.val (i.val*h) r G (a i) ∧ Allocates d f.val (i.val*h+r) (h-r) G (b i)

/-- A single type multiplicity table is required to work on *every* fiber. -/
theorem exact_common_table {d h r G : ℕ} (hd : 0<d) (hg : 0<G) :
    IsGreatest {q | FeasibleAll d h r G q} (d*(r/(d*G)+(h-r)/(d*G))) := by
  let a := r/(d*G)
  let b := (h-r)/(d*G)
  have sum : (∑ _ : Fin d,a)+(∑ _ : Fin d,b) = d*(a+b) := by simp [Nat.mul_add]
  constructor
  · refine ⟨fun _ => a,fun _ => b,sum.symm,fun i f => ⟨?_,?_⟩⟩
    · exact (all_fibers_iff hd hg _ r a).mpr le_rfl f
    · exact (all_fibers_iff hd hg _ (h-r) b).mpr le_rfl f
  · rintro q ⟨u,v,he,ok⟩
    change q≤d*(a+b)
    rw [he,←sum]
    apply Nat.add_le_add <;> apply Finset.sum_le_sum <;> intro i _
    · exact (all_fibers_iff hd hg _ r _).mp (fun f => (ok i f).1)
    · exact (all_fibers_iff hd hg _ (h-r) _).mp (fun f => (ok i f).2)

end ProjectS.FourPass.ExactFiberPacking

#print axioms ProjectS.FourPass.ExactFiberPacking.exact_two_types
#print axioms ProjectS.FourPass.ExactFiberPacking.exact_common_table
#print axioms ProjectS.FourPass.ExactFiberPacking.source_injective
#print axioms ProjectS.FourPass.ExactFiberPacking.type_bands
#print axioms ProjectS.FourPass.ExactFiberPacking.classAnchor_digits
#print axioms ProjectS.FourPass.ExactFiberPacking.anchor_spec
#print axioms ProjectS.FourPass.ExactFiberPacking.source_unique_across_types
