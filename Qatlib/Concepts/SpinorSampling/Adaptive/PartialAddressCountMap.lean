/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressPlan

set_option backward.isDefEq.respectTransparency false

/-!
Sparse count-map postprocessing of the same actual partial-address records.
The rational program only reads recorded edge/spin/basis/outcome fields.
Its deterministic identity with the U statistic transfers the existing
literal-count confidence theorem. Pilot learning and grid/loss composition
remain outside this module. Sparse support avoids enumerating absent edges;
no implementation-level running-time bound for these finite sums is claimed.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress
open Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.UniformMatching
open scoped BigOperators
set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.CountMap
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Construction for count Feature in the partial address count map model. -/
def countFeature (edge : E) (spin : Bool) (r : GlobalRecord E) : ℝ :=
  if r.1=edge ∧ r.2.1=spin then 1 else 0

/-- Construction for sign Feature in the partial address count map model. -/
def signFeature (edge : E) (spin : Bool) (basis : Fin 3) (r : GlobalRecord E) : ℝ :=
  if r.1=edge ∧ r.2.1=spin then
    if r.2.2.1=basis then bitSign r.2.2.2 else 0 else 0

/-- Construction for directed in the partial address count map model. -/
def directed (edge : E) (r s : GlobalRecord E) : ℝ :=
  countFeature edge false r*countFeature edge true s-
    9*∑ basis : Fin 3,signFeature edge false basis r*signFeature edge true basis s

/-- Complete original `basis_delta` guarantee for `PartialAddressCountMap`; all source hypotheses and output obligations are retained. -/
theorem basis_delta (a b : Fin 3) (x y : ℝ) :
    (∑ h : Fin 3,(if a=h then x else 0)*(if b=h then y else 0))=
      if a=b then x*y else 0 := by
  rw [Finset.sum_eq_single a]
  · by_cases hab : a=b
    · simp [hab]
    · simp [hab,Ne.symm hab]
  · intro h _ hne
    simp [Ne.symm hne]
  · simp

omit [Fintype E] in
/-- Complete original `directed_formula` guarantee for `PartialAddressCountMap`; all source hypotheses and output obligations are retained. -/
theorem directed_formula (e : E) (r s : GlobalRecord E) :
    directed e r s=
      if (r.1=e ∧ r.2.1=false) ∧ (s.1=e ∧ s.2.1=true) then
        1-9*(if r.2.2.1=s.2.2.1 then bitSign r.2.2.2*bitSign s.2.2.2 else 0) else 0 := by
  by_cases hr : r.1=e ∧ r.2.1=false
  · by_cases hs : s.1=e ∧ s.2.1=true
    · simp [directed,countFeature,signFeature,hr,hs]
    · simp [directed,countFeature,signFeature,hr,hs]
  · simp [directed,countFeature,signFeature,hr]

/-- Complete original `directed_sum` guarantee for `PartialAddressCountMap`; all source hypotheses and output obligations are retained. -/
theorem directed_sum (r s : GlobalRecord E) :
    (∑ e : E,directed e r s)=
      if r.1=s.1 ∧ r.2.1=false ∧ s.2.1=true then
        1-9*(if r.2.2.1=s.2.2.1 then bitSign r.2.2.2*bitSign s.2.2.2 else 0) else 0 := by
  rw [Finset.sum_eq_single r.1]
  · simp only [directed_formula]
    by_cases he : r.1=s.1
    · simp [he]
    · simp [he,Ne.symm he]
  · intro e _ he
    simp [directed_formula,Ne.symm he]
  · simp

/-- Complete original `global_kernel_rank` guarantee for `PartialAddressCountMap`; all source hypotheses and output obligations are retained. -/
theorem global_kernel_rank (r s : GlobalRecord E) :
    globalKernel r s=(Fintype.card E : ℝ)/2*((∑ e : E,directed e r s)+(∑ e : E,directed e s r)) := by
  rw [directed_sum,directed_sum]
  cases hr : r.2.1 <;> cases hs : s.2.1
  all_goals
    by_cases he : r.1=s.1
    · simp [globalKernel,kernel,hr,hs,he]
      all_goals try (simp only [eq_comm,mul_comm])
      all_goals ring
    · simp [globalKernel,he,Ne.symm he]
/-- Construction for count Total in the partial address count map model. -/
def countTotal {n : ℕ} (e : E) (spin : Bool) (ω : Fin n → GlobalRecord E) : ℝ :=
  ∑ i,countFeature e spin (ω i)
/-- Construction for sign Total in the partial address count map model. -/
def signTotal {n : ℕ} (e : E) (spin : Bool) (h : Fin 3) (ω : Fin n → GlobalRecord E) : ℝ :=
  ∑ i,signFeature e spin h (ω i)
/-- Construction for numerator in the partial address count map model. -/
def numerator {n : ℕ} (ω : Fin n → GlobalRecord E) : ℝ :=
  ∑ e : E,(countTotal e false ω*countTotal e true ω-
    9*∑ h : Fin 3,signTotal e false h ω*signTotal e true h ω)

omit [Fintype E] in
/-- Complete original `directed_double_sum` guarantee for `PartialAddressCountMap`; all source hypotheses and output obligations are retained. -/
theorem directed_double_sum {n : ℕ} (e : E) (ω : Fin n → GlobalRecord E) :
    (∑ i : Fin n,∑ j : Fin n,directed e (ω i) (ω j))=
      countTotal e false ω*countTotal e true ω-
        9*∑ h : Fin 3,signTotal e false h ω*signTotal e true h ω := by
  simp only [directed,countTotal,signTotal,Finset.sum_sub_distrib,
    Finset.mul_sum,Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
  · calc
      _ = ∑ i : Fin n,∑ h : Fin 3,∑ j : Fin n,
          9*(signFeature e false h (ω i)*signFeature e true h (ω j)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro h _
        rw [Finset.sum_comm]

/-- Complete original `directed_edge_sums` guarantee for `PartialAddressCountMap`; all source hypotheses and output obligations are retained. -/
theorem directed_edge_sums {n : ℕ} (ω : Fin n → GlobalRecord E) :
    (∑ i : Fin n,∑ j : Fin n,∑ e : E,directed e (ω i) (ω j))=numerator ω := by
  calc
    _ = ∑ i : Fin n,∑ e : E,∑ j : Fin n,directed e (ω i) (ω j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ e : E,∑ i : Fin n,∑ j : Fin n,directed e (ω i) (ω j) := by
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [directed_double_sum]; rfl

/-- Complete original `global_double_sum` guarantee for `PartialAddressCountMap`; all source hypotheses and output obligations are retained. -/
theorem global_double_sum {n : ℕ} (ω : Fin n → GlobalRecord E) :
    (∑ i : Fin n,∑ j : Fin n,globalKernel (ω i) (ω j))=
      (Fintype.card E : ℝ)*numerator ω := by
  have hf := directed_edge_sums ω
  have hb : (∑ i : Fin n,∑ j : Fin n,∑ e : E,directed e (ω j) (ω i))=numerator ω := by
    rw [Finset.sum_comm]
    exact hf
  simp_rw [global_kernel_rank]
  simp only [← Finset.mul_sum,Finset.sum_add_distrib]
  rw [hf,hb]
  ring

/-- Complete original `ordered_ustatistic_count_formula` guarantee for `PartialAddressCountMap`; all source hypotheses and output obligations are retained. -/
theorem ordered_ustatistic_count_formula {n : ℕ} (ω : Fin n → GlobalRecord E) :
    orderedUStatistic globalKernel ω=
      (Fintype.card E : ℝ)*numerator ω/(n*(n-1) : ℕ) := by
  have h (i j : Fin n) :
      (if i ≠ j then globalKernel (ω i) (ω j) else 0)=globalKernel (ω i) (ω j) := by
    by_cases hij : i=j
    · subst j
      simp [globalKernel,kernel]
    · simp [hij]
  simp only [orderedUStatistic,h,global_double_sum]

/-- Construction for count N in the partial address count map model. -/
def countN {n : ℕ} (e : E) (spin : Bool) (ω : Fin n → GlobalRecord E) : ℕ :=
  ∑ i,if (ω i).1=e ∧ (ω i).2.1=spin then 1 else 0

/-- Construction for sign Z in the partial address count map model. -/
def signZ {n : ℕ} (e : E) (spin : Bool) (h : Fin 3) (ω : Fin n → GlobalRecord E) : ℤ :=
  ∑ i,if (ω i).1=e ∧ (ω i).2.1=spin then
    if (ω i).2.2.1=h then if (ω i).2.2.2 then -1 else 1 else 0 else 0

omit [Fintype E] in
/-- Complete original `countN_cast` guarantee for `PartialAddressCountMap`; all source hypotheses and output obligations are retained. -/
theorem countN_cast {n : ℕ} (e : E) (spin : Bool) (ω : Fin n → GlobalRecord E) :
    (countN e spin ω : ℝ)=countTotal e spin ω := by
  simp [countN,countTotal,countFeature]

omit [Fintype E] in
/-- Complete original `signZ_cast` guarantee for `PartialAddressCountMap`; all source hypotheses and output obligations are retained. -/
theorem signZ_cast {n : ℕ} (e : E) (spin : Bool) (h : Fin 3) (ω : Fin n → GlobalRecord E) :
    (signZ e spin h ω : ℝ)=signTotal e spin h ω := by
  simp [signZ,signTotal,signFeature,bitSign]

/-- Construction for count Value Q in the partial address count map model. -/
def countValueQ {n : ℕ} (ω : Fin n → GlobalRecord E) : ℚ :=
  (Fintype.card E : ℚ)*(∑ e : E,((countN e false ω : ℚ)*(countN e true ω : ℚ)-
    9*∑ h : Fin 3,(signZ e false h ω : ℚ)*(signZ e true h ω : ℚ)))/(n*(n-1) : ℕ)

/-- Complete original `count_value_eq_ustatistic` guarantee for `PartialAddressCountMap`; all source hypotheses and output obligations are retained. -/
theorem count_value_eq_ustatistic {n : ℕ} (ω : Fin n → GlobalRecord E) :
    (countValueQ ω : ℝ)=orderedUStatistic globalKernel ω := by
  rw [ordered_ustatistic_count_formula]
  simp only [countValueQ,Rat.cast_div,Rat.cast_mul,Rat.cast_sum,Rat.cast_sub,
    Rat.cast_natCast,Rat.cast_intCast,Rat.cast_ofNat,countN_cast,signZ_cast,numerator]

/-- Construction for observed Edges in the partial address count map model. -/
def observedEdges {n : ℕ} (ω : Fin n → GlobalRecord E) : Finset E :=
  Finset.univ.image fun i => (ω i).1

/-- Construction for sparse Count Value Q in the partial address count map model. -/
def sparseCountValueQ {n : ℕ} (ω : Fin n → GlobalRecord E) : ℚ :=
  (Fintype.card E : ℚ)*(∑ e ∈ observedEdges ω,
    ((countN e false ω : ℚ)*(countN e true ω : ℚ)-
    9*∑ h : Fin 3,(signZ e false h ω : ℚ)*(signZ e true h ω : ℚ)))/(n*(n-1) : ℕ)

/-- Complete original `sparse_value_eq_dense` guarantee for `PartialAddressCountMap`; all source hypotheses and output obligations are retained. -/
theorem sparse_value_eq_dense {n : ℕ} (ω : Fin n → GlobalRecord E) :
    sparseCountValueQ ω=countValueQ ω := by
  have hsum : (∑ e ∈ observedEdges ω,
      ((countN e false ω : ℚ)*(countN e true ω : ℚ)-
      9*∑ h : Fin 3,(signZ e false h ω : ℚ)*(signZ e true h ω : ℚ)))=
      ∑ e : E,((countN e false ω : ℚ)*(countN e true ω : ℚ)-
      9*∑ h : Fin 3,(signZ e false h ω : ℚ)*(signZ e true h ω : ℚ)) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    have hno (i : Fin n) : (ω i).1 ≠ e := by
      intro hi
      apply he
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,hi⟩
    have hc (spin : Bool) : countN e spin ω=0 := by simp [countN,hno]
    have hs (spin : Bool) (h : Fin 3) : signZ e spin h ω=0 := by simp [signZ,hno]
    simp [hc,hs]
  simp only [sparseCountValueQ,countValueQ,hsum]

/-- Complete original `sparse_value_eq_ustatistic` guarantee for `PartialAddressCountMap`; all source hypotheses and output obligations are retained. -/
theorem sparse_value_eq_ustatistic {n : ℕ} (ω : Fin n → GlobalRecord E) :
    (sparseCountValueQ ω : ℝ)=orderedUStatistic globalKernel ω := by
  rw [sparse_value_eq_dense,count_value_eq_ustatistic]

/-- Complete original `checked_sparse_value_confidence` guarantee for `PartialAddressCountMap`; all source hypotheses and output obligations are retained. -/
theorem checked_sparse_value_confidence [Nonempty E] (u v : E → Bool → ℂ)
    (hu : ∀ e,RetainedSpin.qubitMass (u e)=1) (hv : ∀ e,RetainedSpin.qubitMass (v e)=1)
    (q ε δ : ℚ) (n : ℕ) (hc : checkedXYZCountQ (2*Fintype.card E) q ε δ=some n)
    (hq : average (fun e => sectorMass (u e) (v e) true) ≤ (q : ℝ)) :
    (law u v hu hv).probEvent (fun ω : Fin n → GlobalRecord E =>
      (ε : ℝ)< |(sparseCountValueQ ω : ℝ)-
        average (fun e => RetainedSpin.bellProbability (u e) (v e))|) ≤ (δ : ℝ) := by
  simp only [sparse_value_eq_ustatistic]
  exact checked_xyz_count_confidence u v hu hv q ε δ n hc hq

#print axioms basis_delta
#print axioms directed_formula
#print axioms directed_sum
#print axioms global_kernel_rank
#print axioms directed_double_sum
#print axioms directed_edge_sums
#print axioms global_double_sum
#print axioms ordered_ustatistic_count_formula
#print axioms countN_cast
#print axioms signZ_cast
#print axioms count_value_eq_ustatistic
#print axioms sparse_value_eq_dense
#print axioms sparse_value_eq_ustatistic
#print axioms checked_sparse_value_confidence
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.CountMap
