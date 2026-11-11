/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressPathPoincare

set_option backward.isDefEq.respectTransparency false

/-!
Finite-product variance tensorization and an open-path Poincare bound on
uniform boxes of even side ell. Internal edge indicators exclude wraparound;
the coefficient is ell^2/(4*ell^d), without an extra dimension factor. A
pointwise unit Bloch field gives the per-box near-purity estimate, including
an actual original-spinor specialization. These product coordinates describe
a geometric average, not independent pilot boxes. Transport of internal edges
to the original periodic grid and its Bell-mean promise remains separate.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.BoxTensor
noncomputable section
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Complete original `expect_swap` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem expect_swap (p : FinDist X) (q : FinDist Y) (f : X → Y → ℝ) :
    p.expect (fun x => q.expect (f x))=q.expect (fun y => p.expect (fun x => f x y)) := by
  unfold FinDist.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Fintype Y] in
/-- Complete original `mean_sq_le_second` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem mean_sq_le_second (p : FinDist X) (f : X → ℝ) :
    (p.expect f)^2 ≤ p.expect (fun x => (f x)^2) := by
  have h := finite_expect_nonneg p (fun x => (f x-p.expect f)^2) (fun x => sq_nonneg _)
  change 0 ≤ p.variance f at h
  rw [finite_variance_identity] at h
  linarith

/-- Complete original `variance_conditional_mean` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem variance_conditional_mean (p : FinDist X) (q : FinDist Y) (f : X → Y → ℝ) :
    p.variance (fun x => q.expect (f x)) ≤ q.expect (fun y => p.variance (fun x => f x y)) := by
  have hc (x : X) :
      q.expect (fun y => f x y-p.expect (fun z => f z y))=
        q.expect (f x)-p.expect (fun z => q.expect (f z)) := by
    rw [finite_expect_sub,← expect_swap]
  unfold FinDist.variance
  calc
    _ = p.expect (fun x => (q.expect (fun y => f x y-p.expect (fun z => f z y)))^2) := by
      simp_rw [hc]
    _ ≤ p.expect (fun x => q.expect (fun y => (f x y-p.expect (fun z => f z y))^2)) :=
      finite_expect_mono _ _ _ (fun x => mean_sq_le_second q _)
    _ = _ := expect_swap p q _

/-- Complete original `total_variance_split` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem total_variance_split (p : FinDist X) (q : FinDist Y) (f : X → Y → ℝ) :
    p.expect (fun x => q.variance (f x))+p.variance (fun x => q.expect (f x))=
      p.expect (fun x => q.expect (fun y => (f x y)^2))-
        (p.expect (fun x => q.expect (f x)))^2 := by
  simp_rw [finite_variance_identity]
  rw [finite_expect_sub]
  ring

/-- Complete original `product_variance_bound` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem product_variance_bound (p : FinDist X) (q : FinDist Y) (f : X → Y → ℝ) :
    p.expect (fun x => q.expect (fun y => (f x y)^2))-
      (p.expect (fun x => q.expect (f x)))^2 ≤
    p.expect (fun x => q.variance (f x))+q.expect (fun y => p.variance (fun x => f x y)) := by
  rw [← total_variance_split]
  exact add_le_add le_rfl (variance_conditional_mean p q f)

#print axioms expect_swap
#print axioms mean_sq_le_second
#print axioms variance_conditional_mean
#print axioms total_variance_split
#print axioms product_variance_bound
variable [DecidableEq X]

omit [Fintype Y] in
/-- Complete original `cohort_expect_cons` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem cohort_expect_cons {n : ℕ} (p : FinDist X) (F : (Fin (n+1) → X) → ℝ) :
    (cohortLaw p (n+1)).expect F=
      p.expect (fun a => (cohortLaw p n).expect (fun ω => F (Fin.cons a ω))) :=
  product_expect_cons p F

omit [Fintype Y] in
/-- Complete original `cohort_expect_zero` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem cohort_expect_zero (p : FinDist X) (F : (Fin 0 → X) → ℝ) :
    (cohortLaw p 0).expect F=F (fun i => Fin.elim0 i) := by
  have he (ω : Fin 0 → X) : ω=(fun i => Fin.elim0 i) := Subsingleton.elim _ _
  unfold FinDist.expect cohortLaw
  simp only [FinDist.probOf,Fin.prod_univ_zero]
  simp_rw [he]
  simp

omit [Fintype X] [Fintype Y] [DecidableEq X] in
/-- Complete original `update_cons_zero` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem update_cons_zero {n : ℕ} (a v : X) (ω : Fin n → X) :
    Function.update (Fin.cons a ω : Fin (n+1) → X) 0 v=(Fin.cons v ω : Fin (n+1) → X) := by
  funext i
  cases i using Fin.cases <;> simp

omit [Fintype X] [Fintype Y] [DecidableEq X] in
/-- Complete original `update_cons_succ` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem update_cons_succ {n : ℕ} (a v : X) (ω : Fin n → X) (j : Fin n) :
    Function.update (Fin.cons a ω : Fin (n+1) → X) j.succ v=
      (Fin.cons a (Function.update ω j v) : Fin (n+1) → X) := by
  funext i
  cases i using Fin.cases with
  | zero =>
    exact Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j)) v (Fin.cons a ω : Fin (n+1) → X)
  | succ i => simp [Function.update_apply]

omit [Fintype Y] in
/-- Complete original `head_variance_expect` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem head_variance_expect {n : ℕ} (p : FinDist X) (f : (Fin (n+1) → X) → ℝ) :
    (cohortLaw p (n+1)).expect (fun ω => p.variance (fun v => f (Function.update ω 0 v)))=
      (cohortLaw p n).expect (fun ω => p.variance (fun v => f (Fin.cons v ω))) := by
  rw [cohort_expect_cons]
  simp_rw [update_cons_zero]
  exact finite_expect_const _ _

omit [Fintype Y] in
/-- Complete original `tail_variance_expect` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem tail_variance_expect {n : ℕ} (p : FinDist X) (f : (Fin (n+1) → X) → ℝ) (j : Fin n) :
    (cohortLaw p (n+1)).expect (fun ω => p.variance (fun v => f (Function.update ω j.succ v)))=
      p.expect (fun a => (cohortLaw p n).expect
        (fun ω => p.variance (fun v => f (Fin.cons a (Function.update ω j v))))) := by
  rw [cohort_expect_cons]
  simp_rw [update_cons_succ]

omit [Fintype Y] in
/-- Complete original `cohort_variance_tensor` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem cohort_variance_tensor (p : FinDist X) : ∀ n : ℕ,∀ f : (Fin n → X) → ℝ,
    (cohortLaw p n).variance f ≤
      ∑ j : Fin n,(cohortLaw p n).expect (fun ω => p.variance (fun v => f (Function.update ω j v))) := by
  intro n
  induction n with
  | zero =>
    intro f
    rw [finite_variance_identity,cohort_expect_zero,cohort_expect_zero]
    simp
  | succ n ih =>
    intro f
    rw [Fin.sum_univ_succ,head_variance_expect]
    calc
      _ ≤ p.expect (fun a => (cohortLaw p n).variance (fun ω => f (Fin.cons a ω)))+
          (cohortLaw p n).expect (fun ω => p.variance (fun v => f (Fin.cons v ω))) := by
        rw [finite_variance_identity]
        simp_rw [cohort_expect_cons]
        exact product_variance_bound p (cohortLaw p n) (fun a ω => f (Fin.cons a ω))
      _ ≤ p.expect (fun a => ∑ j : Fin n,(cohortLaw p n).expect
          (fun ω => p.variance (fun v => f (Fin.cons a (Function.update ω j v)))))+
          (cohortLaw p n).expect (fun ω => p.variance (fun v => f (Fin.cons v ω))) :=
        add_le_add (finite_expect_mono _ _ _ (fun a => ih (fun ω => f (Fin.cons a ω)))) le_rfl
      _ = _ := by
        rw [finite_expect_sum]
        simp_rw [← tail_variance_expect]
        ring

omit [Fintype Y] in
/-- Complete original `cohort_resample_expect` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem cohort_resample_expect (p : FinDist X) : ∀ n : ℕ,∀ j : Fin n,
    ∀ f : (Fin n → X) → ℝ,
    (cohortLaw p n).expect (fun ω => p.expect (fun v => f (Function.update ω j v)))=
      (cohortLaw p n).expect f := by
  intro n
  induction n with
  | zero => intro j; exact Fin.elim0 j
  | succ n ih =>
    intro j f
    cases j using Fin.cases with
    | zero =>
      rw [cohort_expect_cons,cohort_expect_cons]
      simp_rw [update_cons_zero]
      have he : p.expect (fun _ : X => (cohortLaw p n).expect
          (fun ω => p.expect (fun v => f (Fin.cons v ω))))=
          (cohortLaw p n).expect (fun ω => p.expect (fun v => f (Fin.cons v ω))) :=
        finite_expect_const _ _
      rw [he]
      exact (expect_swap p (cohortLaw p n) (fun v ω => f (Fin.cons v ω))).symm
    | succ j =>
      rw [cohort_expect_cons,cohort_expect_cons]
      simp_rw [update_cons_succ]
      congr 1
      funext a
      exact ih j (fun ω => f (Fin.cons a ω))

#print axioms cohort_resample_expect
#print axioms cohort_expect_cons
#print axioms cohort_expect_zero
#print axioms update_cons_zero
#print axioms update_cons_succ
#print axioms head_variance_expect
#print axioms tail_variance_expect
#print axioms cohort_variance_tensor
end

noncomputable section
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- Construction for uniform Box in the partial address box poincare model. -/
def uniformBox (ell n : ℕ) [NeZero ell] : FinDist (Fin n → Fin ell) :=
  cohortLaw (Matched.uniformLaw (Fin ell)) n

/-- Complete original `uniform_box_weight` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem uniform_box_weight (ell n : ℕ) [NeZero ell] (ω : Fin n → Fin ell) :
    (uniformBox ell n).prob ω=1/(ell : ℝ)^n := by
  simp only [uniformBox,cohortLaw,FinDist.probOf,Matched.uniformLaw,Fintype.card_fin,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,one_div_pow]

/-- Complete original `uniform_box_expect` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem uniform_box_expect (ell n : ℕ) [NeZero ell] (f : (Fin n → Fin ell) → ℝ) :
    (uniformBox ell n).expect f=(∑ ω,f ω)/(ell : ℝ)^n := by
  unfold FinDist.expect
  simp_rw [uniform_box_weight,one_div_mul_eq_div]
  rw [Finset.sum_div]

/-- Complete original `uniform_site_expect` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem uniform_site_expect (ell : ℕ) [NeZero ell] (f : Fin ell → ℝ) :
    (Matched.uniformLaw (Fin ell)).expect f=(∑ a,f a)/(ell : ℝ) := by
  unfold FinDist.expect
  simp only [Matched.uniformLaw,Fintype.card_fin,one_div_mul_eq_div,Finset.sum_div]

/-- Complete original `uniform_site_variance` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem uniform_site_variance (ell : ℕ) [NeZero ell] (f : Fin ell → ℝ) :
    (Matched.uniformLaw (Fin ell)).variance f=
      (∑ a,(f a-(∑ b,f b)/(ell : ℝ))^2)/(ell : ℝ) := by
  unfold FinDist.variance
  rw [uniform_site_expect,uniform_site_expect]

/-- Construction for at Nat in the partial address box poincare model. -/
def atNat {ell : ℕ} (f : Fin ell → ℝ) (i : ℕ) : ℝ :=
  if h : i<ell then f ⟨i,h⟩ else 0

/-- Complete original `at_nat_val` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem at_nat_val {ell : ℕ} (f : Fin ell → ℝ) (i : Fin ell) : atNat f i.val=f i := by
  simp only [atNat,dite_eq_left i.isLt]

/-- Construction for fiber Energy in the partial address box poincare model. -/
def fiberEnergy {ell : ℕ} (f : Fin ell → ℝ) : ℝ :=
  BoxPoincare.pathEnergy (atNat f) 0 (ell-1)

/-- Complete original `uniform_path_poincare` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem uniform_path_poincare (m : ℕ) [NeZero m] [NeZero (2*m)] (f : Fin (2*m) → ℝ) :
    (Matched.uniformLaw (Fin (2*m))).variance f ≤ ((2*m : ℕ) : ℝ)/4*fiberEnergy f := by
  have h := BoxPoincare.even_path_poincare (atNat f) m (Nat.pos_of_ne_zero (NeZero.ne m))
  rw [uniform_site_variance]
  simpa only [BoxPoincare.pathMean,at_nat_val,fiberEnergy] using h

/-- Complete original `box_fiber_poincare` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem box_fiber_poincare (m n : ℕ) [NeZero m] [NeZero (2*m)] (f : (Fin n → Fin (2*m)) → ℝ) :
    (uniformBox (2*m) n).variance f ≤ ((2*m : ℕ) : ℝ)/4*
      ∑ j : Fin n,(uniformBox (2*m) n).expect
        (fun ω => fiberEnergy (fun v => f (Function.update ω j v))) := by
  calc
    _ ≤ ∑ j : Fin n,(uniformBox (2*m) n).expect
        (fun ω => (Matched.uniformLaw (Fin (2*m))).variance (fun v => f (Function.update ω j v))) :=
      cohort_variance_tensor (Matched.uniformLaw (Fin (2*m))) n f
    _ ≤ ∑ j : Fin n,(uniformBox (2*m) n).expect
        (fun ω => ((2*m : ℕ) : ℝ)/4*fiberEnergy (fun v => f (Function.update ω j v))) := by
      apply Finset.sum_le_sum
      intro j _
      exact finite_expect_mono _ _ _ (fun ω => uniform_path_poincare m _)
    _ = _ := by
      simp_rw [finite_expect_mul]
      rw [Finset.mul_sum]

#print axioms uniform_box_weight
#print axioms uniform_box_expect
#print axioms uniform_site_expect
#print axioms uniform_site_variance
#print axioms at_nat_val
#print axioms uniform_path_poincare
#print axioms box_fiber_poincare
/-- Complete original `fiber_energy_eq` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem fiber_energy_eq {ell : ℕ} (f : Fin ell → ℝ) :
    fiberEnergy f=∑ a : Fin ell,if h : a.val+1<ell then
      (f ⟨a.val+1,h⟩-f a)^2 else 0 := by
  cases ell with
  | zero => simp [fiberEnergy,BoxPoincare.pathEnergy]
  | succ k =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_last,Nat.lt_irrefl,dite_eq_right (by decide : ¬False),add_zero]
    have hf (i : Fin k) :
        (if h : (i.castSucc : Fin (k+1)).val+1<k+1 then
          (f ⟨(i.castSucc : Fin (k+1)).val+1,h⟩-f i.castSucc)^2 else 0)=
        (atNat f (i.val+1)-atNat f i.val)^2 := by
      have hi : i.val+1<k+1 := by omega
      have hi0 : i.val<k+1 := by omega
      simp only [Fin.val_castSucc,dite_eq_left hi,atNat,dite_eq_left hi0]
      rfl
    simp_rw [hf]
    unfold fiberEnergy BoxPoincare.pathEnergy
    simp only [Nat.add_sub_cancel,Nat.Ico_zero_eq_range]
    exact (Fin.sum_univ_eq_sum_range (fun i => (atNat f (i+1)-atNat f i)^2) k).symm

/-- Construction for edge At in the partial address box poincare model. -/
def edgeAt {ell n : ℕ} (f : (Fin n → Fin ell) → ℝ) (j : Fin n) (ω : Fin n → Fin ell) : ℝ :=
  if h : (ω j).val+1<ell then
    (f (Function.update ω j ⟨(ω j).val+1,h⟩)-f ω)^2 else 0

/-- Complete original `fiber_to_edge_sum` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem fiber_to_edge_sum {ell n : ℕ} (f : (Fin n → Fin ell) → ℝ) (j : Fin n) (ω : Fin n → Fin ell) :
    fiberEnergy (fun v => f (Function.update ω j v))=
      ∑ v : Fin ell,edgeAt f j (Function.update ω j v) := by
  rw [fiber_energy_eq]
  apply Finset.sum_congr rfl
  intro v _
  simp only [edgeAt,Function.update_self,Function.update_idem]

/-- Complete original `fiber_expect_eq` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem fiber_expect_eq (ell n : ℕ) [NeZero ell] (f : (Fin n → Fin ell) → ℝ) (j : Fin n) :
    (uniformBox ell n).expect (fun ω => fiberEnergy (fun v => f (Function.update ω j v)))=
      (ell : ℝ)*(uniformBox ell n).expect (edgeAt f j) := by
  have hp : (ell : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne ell
  have hs (ω : Fin n → Fin ell) : (∑ v : Fin ell,edgeAt f j (Function.update ω j v))=
      (ell : ℝ)*(Matched.uniformLaw (Fin ell)).expect (fun v => edgeAt f j (Function.update ω j v)) := by
    rw [uniform_site_expect]
    field_simp
  simp_rw [fiber_to_edge_sum,hs]
  rw [finite_expect_mul]
  congr 1
  exact cohort_resample_expect (Matched.uniformLaw (Fin ell)) n j (edgeAt f j)

/-- Construction for grid Energy in the partial address box poincare model. -/
def gridEnergy {ell n : ℕ} (f : (Fin n → Fin ell) → ℝ) : ℝ := ∑ ω,∑ j,edgeAt f j ω

/-- Complete original `box_poincare` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem box_poincare (m n : ℕ) [NeZero m] [NeZero (2*m)] (f : (Fin n → Fin (2*m)) → ℝ) :
    (uniformBox (2*m) n).variance f ≤
      (((2*m : ℕ) : ℝ)^2/(4*((2*m : ℕ) : ℝ)^n))*gridEnergy f := by
  have h := box_fiber_poincare m n f
  simp_rw [fiber_expect_eq] at h
  rw [← Finset.mul_sum,← finite_expect_sum,uniform_box_expect] at h
  calc
    _ ≤ _ := h
    _ = _ := by unfold gridEnergy; field_simp

#print axioms fiber_energy_eq
#print axioms fiber_to_edge_sum
#print axioms fiber_expect_eq
#print axioms box_poincare
/-- Complete original `unit_variance_sum` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem unit_variance_sum (ell n : ℕ) [NeZero ell]
    (v : Fin 3 → (Fin n → Fin ell) → ℝ) (hu : ∀ a,∑ h : Fin 3,(v h a)^2=1) :
    (∑ h : Fin 3,(uniformBox ell n).variance (v h))=
      1-AxisRisk.length (fun h => (uniformBox ell n).expect (v h))^2 := by
  simp_rw [finite_variance_identity]
  rw [Finset.sum_sub_distrib,← finite_expect_sum]
  simp_rw [hu]
  rw [finite_expect_const,AxisRisk.length_sq]
  simp only [AxisRisk.dot,pow_two]

/-- Complete original `box_defect_bound` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem box_defect_bound (m n : ℕ) [NeZero m] [NeZero (2*m)]
    (v : Fin 3 → (Fin n → Fin (2*m)) → ℝ) (hu : ∀ a,∑ h : Fin 3,(v h a)^2=1) :
    (1-AxisRisk.length (fun h => (uniformBox (2*m) n).expect (v h)))/2 ≤
      (((2*m : ℕ) : ℝ)^2/(8*((2*m : ℕ) : ℝ)^n))*∑ h : Fin 3,gridEnergy (v h) := by
  let R := AxisRisk.length (fun h => (uniformBox (2*m) n).expect (v h))
  have hid := unit_variance_sum (2*m) n v hu
  have hvnonneg : 0 ≤ ∑ h : Fin 3,(uniformBox (2*m) n).variance (v h) := by
    apply Finset.sum_nonneg
    intro h _
    exact finite_expect_nonneg _ _ (fun a => sq_nonneg _)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR1 : R ≤ 1 := by change _=1-R^2 at hid; nlinarith
  have hdef : (1-R)/2 ≤ (∑ h : Fin 3,(uniformBox (2*m) n).variance (v h))/2 := by
    change _=1-R^2 at hid
    nlinarith [mul_nonneg hR0 (sub_nonneg.mpr hR1)]
  have hvar : (∑ h : Fin 3,(uniformBox (2*m) n).variance (v h)) ≤
      (((2*m : ℕ) : ℝ)^2/(4*((2*m : ℕ) : ℝ)^n))*∑ h : Fin 3,gridEnergy (v h) := by
    calc
      _ ≤ ∑ h : Fin 3,(((2*m : ℕ) : ℝ)^2/(4*((2*m : ℕ) : ℝ)^n))*gridEnergy (v h) :=
        Finset.sum_le_sum fun h _ => box_poincare m n (v h)
      _ = _ := by rw [Finset.mul_sum]
  calc
    _ ≤ _ := hdef
    _ ≤ _ := div_le_div_of_nonneg_right hvar (by norm_num : (0 : ℝ) ≤ 2)
    _ = _ := by field_simp; ring

variable {B : Type}

/-- Complete original `native_box_mean` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem native_box_mean {d r m : ℕ} [NeZero m] [NeZero (2*m)]
    (e : (Fin d → Fin (2^r)) ≃ B × (Fin d → Fin (2*m)))
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (box : B) :
    PilotVector.boxVector (NativePilot.actualFields e a b c k) box=
      (fun h => (uniformBox (2*m) d).expect (fun localPoint =>
        pauliField a b c k h (e.symm (box,localPoint)))) := by
  funext h
  rw [uniform_box_expect]
  change (∑ localPoint : Fin d → Fin (2*m),pauliField a b c k h (e.symm (box,localPoint)))/
    (Fintype.card (Fin d → Fin (2*m)) : ℝ)=_
  have hc : Fintype.card (Fin d → Fin (2*m))=(2*m)^d := by simp
  rw [hc,Nat.cast_pow]

/-- Complete original `native_box_defect_bound` guarantee for `PartialAddressBoxPoincare`; all source hypotheses and output obligations are retained. -/
theorem native_box_defect_bound {d r m : ℕ} [NeZero m] [NeZero (2*m)]
    (e : (Fin d → Fin (2^r)) ≃ B × (Fin d → Fin (2*m)))
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (box : B) :
    (1-AxisRisk.length (PilotVector.boxVector (NativePilot.actualFields e a b c k) box))/2 ≤
      (((2*m : ℕ) : ℝ)^2/(8*((2*m : ℕ) : ℝ)^d))*
        ∑ h : Fin 3,gridEnergy (fun localPoint => pauliField a b c k h (e.symm (box,localPoint))) := by
  rw [native_box_mean]
  apply box_defect_bound
  intro localPoint
  exact pauli_field_unit a b c k hz (e.symm (box,localPoint))

#print axioms unit_variance_sum
#print axioms box_defect_bound
#print axioms native_box_mean
#print axioms native_box_defect_bound
end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.BoxTensor
