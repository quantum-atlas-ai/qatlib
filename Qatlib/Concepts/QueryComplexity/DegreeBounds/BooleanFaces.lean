/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds.BooleanPolynomial

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DegreeBounds
open MvPolynomial
open scoped BigOperators

noncomputable def faceEmbedding {I : Type} [DecidableEq I] (s : Finset I)
    (x : s → Bool) : I → Bool := fun i => if hi : i ∈ s then x ⟨i,hi⟩ else false

noncomputable def cubeSign {J : Type} [Fintype J] (x : J → Bool) : ℝ :=
  ∏ i, if x i then -1 else 1

/-- A monomial supported on the chosen face evaluates as the corresponding product over the face
coordinates. -/
private theorem face_monomial_product {I : Type} [Fintype I] [DecidableEq I]
    (s : Finset I) (d : I →₀ ℕ) (x : s → Bool) (hd : d.support ⊆ s) :
    (∏ i : I, (booleanPoint (faceEmbedding s x) i : ℝ)^d i)=
      ∏ i : s, (booleanPoint x i : ℝ)^d i := by
  classical
  have hp : (∏ i ∈ s, (booleanPoint (faceEmbedding s x) i : ℝ)^d i)=
      ∏ i : I, (booleanPoint (faceEmbedding s x) i : ℝ)^d i := by
    apply Finset.prod_subset (Finset.subset_univ s)
    intro i _ hi
    have hdi : d i=0 := Finsupp.notMem_support_iff.mp (fun hm => hi (hd hm))
    simp [hdi]
  rw [← hp,← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro i _
  simp [booleanPoint,faceEmbedding,i.property]

/-- A monomial with support outside the chosen face vanishes on that face. -/
private theorem face_monomial_product_zero {I : Type} [Fintype I] [DecidableEq I]
    (s : Finset I) (d : I →₀ ℕ) (x : s → Bool) (hd : ¬ d.support ⊆ s) :
    (∏ i : I, (booleanPoint (faceEmbedding s x) i : ℝ)^d i)=0 := by
  classical
  obtain ⟨i,hi,his⟩ := Finset.not_subset.mp hd
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [booleanPoint,faceEmbedding,his,Finsupp.mem_support_iff.mp hi]

/-- The alternating sum of a monomial on a Boolean face is the parity sign when its support
equals the face, and zero otherwise. -/
theorem face_monomial_alternating_sum {I : Type} [Fintype I] [DecidableEq I]
    (s : Finset I) (d : I →₀ ℕ) :
    (∑ x : s → Bool, cubeSign x *
      ∏ i : I, (booleanPoint (faceEmbedding s x) i : ℝ)^d i)=
      if d.support=s then (-1 : ℝ)^s.card else 0 := by
  classical
  by_cases hd : d.support ⊆ s
  · have hprod : (∑ x : s → Bool, cubeSign x *
        ∏ i : I, (booleanPoint (faceEmbedding s x) i : ℝ)^d i)=
        ∏ i : s, ∑ b : Bool, (if b then (-1 : ℝ) else 1)*(if b then (1 : ℝ) else 0)^d i := by
      simp_rw [face_monomial_product s d _ hd,cubeSign,← Finset.prod_mul_distrib]
      simpa only [booleanPoint] using!
        (Finset.prod_univ_sum (fun _ : s => (Finset.univ : Finset Bool))
          (fun i b => (if b then (-1 : ℝ) else 1)*(if b then (1 : ℝ) else 0)^d i)).symm
    rw [hprod]
    by_cases he : d.support=s
    · rw [ite_eq_left he]
      have hfactor : ∀ i : s, (∑ b : Bool,
          (if b then (-1 : ℝ) else 1)*(if b then (1 : ℝ) else 0)^d i)= -1 := by
        intro i
        have hi : d i ≠ 0 := Finsupp.mem_support_iff.mp (he.symm ▸ i.property)
        simp [hi]
      simp only [hfactor,Finset.prod_const,Finset.card_univ,Fintype.card_coe]
    · rw [ite_eq_right he]
      have hss : d.support ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hd,he⟩
      obtain ⟨i,hi,his⟩ := Finset.exists_mem_notMem_of_card_lt_card (Finset.card_lt_card hss)
      let j : s := ⟨i,hi⟩
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      have hdi : d j=0 := Finsupp.notMem_support_iff.mp his
      simp [hdi]
  · have he : d.support ≠ s := fun he => hd (he ▸ Finset.Subset.refl _)
    simp [face_monomial_product_zero s d _ hd,he]

/-- The alternating sum of a multilinear polynomial on the face of a supported monomial extracts
its coefficient multiplied by the face parity sign. -/
theorem face_alternating_sum_coefficient {I : Type} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℝ) (hp : ∀ i, p.degreeOf i ≤ 1) (e : I →₀ ℕ) (he : e ∈ p.support) :
    (∑ x : e.support → Bool, cubeSign x * eval (booleanPoint (faceEmbedding e.support x)) p)=
      p.coeff e * (-1 : ℝ)^e.support.card := by
  classical
  simp only [eval_eq',Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm (d : I →₀ ℕ) :
      (∑ x : e.support → Bool, cubeSign x *
        (p.coeff d * ∏ i : I, (booleanPoint (faceEmbedding e.support x) i : ℝ)^d i))=
      p.coeff d * (if d.support=e.support then (-1 : ℝ)^e.support.card else 0) := by
    rw [← face_monomial_alternating_sum e.support d,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [hterm]
  rw [Finset.sum_eq_single e]
  · simp
  · intro d hd hde
    have hs : d.support ≠ e.support := by
      intro hs
      apply hde
      ext i
      have hdi := degreeOf_le_iff.mp (hp i) d hd
      have hei := degreeOf_le_iff.mp (hp i) e he
      by_cases hi : i ∈ e.support
      · have hdn : d i ≠ 0 := Finsupp.mem_support_iff.mp (hs.symm ▸ hi)
        have hen : e i ≠ 0 := Finsupp.mem_support_iff.mp hi
        omega
      · have hz : e i=0 := Finsupp.notMem_support_iff.mp hi
        have hdz : d i=0 := Finsupp.notMem_support_iff.mp (hs.symm ▸ hi)
        omega
    simp [hs]
  · exact fun h => (h he).elim

/-- A Boolean function of positive exact degree has a face of that dimension with nonzero
alternating sum. -/
theorem exactDegree_alternating_face {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) (hd : 0 < Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f) :
    ∃ s : Finset I, s.card=Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f ∧
      (∑ x : s → Bool, cubeSign x * (if f (faceEmbedding s x) then (1 : ℝ) else 0)) ≠ 0 := by
  classical
  let p := map (Int.castRingHom ℝ) (integerBooleanRepresentative f)
  have hp : ∀ i, p.degreeOf i ≤ 1 := integerBooleanRepresentative_real_degreeOf f
  have hdeg : p.totalDegree=Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f :=
    integerBooleanRepresentative_real_degree_eq f
  have hn : p.support.Nonempty := by
    by_contra hn
    have he : p.support=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hh : p.totalDegree=0 := by simp [totalDegree,he]
    omega
  obtain ⟨e,he,htop⟩ := Finset.exists_mem_eq_sup p.support hn (fun d => d.sum (fun _ k => k))
  have hcard : e.sum (fun _ k => k)=e.support.card := by
    change (∑ i ∈ e.support, e i)=e.support.card
    calc
      _ = ∑ i ∈ e.support, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have h1 := degreeOf_le_iff.mp (hp i) e he
        have h0 := Finsupp.mem_support_iff.mp hi
        omega
      _ = e.support.card := by simp
  refine ⟨e.support,?_,?_⟩
  · change p.totalDegree=_ at htop
    omega
  · have hs := face_alternating_sum_coefficient p hp e he
    have heval (x : e.support → Bool) :
        eval (booleanPoint (faceEmbedding e.support x)) p=
          if f (faceEmbedding e.support x) then 1 else 0 :=
      integerBooleanRepresentative_map_eval f _
    simp only [heval] at hs
    rw [hs]
    exact mul_ne_zero (mem_support_iff.mp he) (pow_ne_zero _ (by norm_num))

end Qatlib.Concepts.QueryComplexity.DegreeBounds
