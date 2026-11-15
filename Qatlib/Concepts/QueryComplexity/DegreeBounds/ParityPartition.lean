/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeBounds.BooleanFaces
public import Qatlib.Concepts.QueryComplexity.DegreeBounds.HuangNorm

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DegreeBounds
open scoped BigOperators Matrix.Norms.L2Operator

/-- The absolute value of the Boolean cube parity sign is one. -/
theorem cubeSign_abs {J : Type} [Fintype J] (x : J → Bool) : |cubeSign x|=1 := by
  classical
  unfold cubeSign
  rw [Finset.abs_prod]
  apply Finset.prod_eq_one
  intro i _
  cases x i <;> norm_num

/-- The Boolean cube parity sign is either one or minus one. -/
private theorem cubeSign_values {J : Type} [Fintype J] (x : J → Bool) :
    cubeSign x=1 ∨ cubeSign x= -1 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← sq_abs,cubeSign_abs]

/-- The parity signs sum to zero on a nonempty Boolean cube. -/
theorem cubeSign_sum_zero {J : Type} [Fintype J] [DecidableEq J] [Nonempty J] :
    (∑ x : J → Bool, cubeSign x)=0 := by
  classical
  have h : (∑ x : J → Bool, cubeSign x)=∏ i : J, ∑ b : Bool, if b then (-1 : ℝ) else 1 := by
    simpa only [cubeSign] using! (Finset.prod_univ_sum (fun _ : J => (Finset.univ : Finset Bool))
      (fun _ b => if b then (-1 : ℝ) else 1)).symm
  rw [h]
  obtain ⟨i⟩ := (inferInstance : Nonempty J)
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- The parity signs of vertices differing in exactly one coordinate are negatives of each
other. -/
theorem cubeSign_edge_neg {J : Type} [Fintype J] [DecidableEq J] (x y : J → Bool)
    (hc : (Finset.univ.filter (fun i => x i ≠ y i)).card=1) : cubeSign y= -cubeSign x := by
  classical
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hc
  have hdiff : x i ≠ y i := by
    have hm : i ∈ Finset.univ.filter (fun i => x i ≠ y i) := by rw [hi]; simp
    simpa using! hm
  have hsame : ∀ j ∈ (Finset.univ : Finset J).erase i, x j=y j := by
    intro j hj
    by_contra he
    have hm : j ∈ Finset.univ.filter (fun i => x i ≠ y i) := by simp [he]
    rw [hi] at hm
    exact (Finset.mem_erase.mp hj).1 (Finset.mem_singleton.mp hm)
  have hp : (∏ j ∈ (Finset.univ : Finset J).erase i, if x j then (-1 : ℝ) else 1)=
      ∏ j ∈ (Finset.univ : Finset J).erase i, if y j then (-1 : ℝ) else 1 :=
    Finset.prod_congr rfl (fun j hj => by rw [hsame j hj])
  have hx := Finset.prod_erase_mul (Finset.univ : Finset J)
    (fun j => if x j then (-1 : ℝ) else 1) (Finset.mem_univ i)
  have hy := Finset.prod_erase_mul (Finset.univ : Finset J)
    (fun j => if y j then (-1 : ℝ) else 1) (Finset.mem_univ i)
  rw [hp] at hx
  unfold cubeSign
  cases hxi : x i <;> cases hyi : y i <;>
    simp only [hxi,hyi,Bool.false_eq_true,ite_true,ite_false] at hx hy hdiff
  all_goals first | exact (hdiff rfl).elim | linarith

/-- Nonzero correlation with full parity implies that squared spectral sensitivity is at least
the cube dimension. -/
theorem sensitivity_nonzero_parity_norm (m : ℕ) (g : (Fin (m+1) → Bool) → Bool)
    (hcorr : (∑ x : Fin (m+1) → Bool, cubeSign x * (if g x then (1 : ℝ) else 0)) ≠ 0) :
    (m+1 : ℝ) ≤ spectralSensitivity g ^ 2 := by
  classical
  let a : (Fin (m+1) → Bool) → ℝ := fun x => (if g x then -1 else 1)*cubeSign x
  have hav (x : Fin (m+1) → Bool) : a x=1 ∨ a x= -1 := by
    rcases cubeSign_values x with hx | hx <;> cases hg : g x <;> simp [a,hg,hx]
  have hsum0 := cubeSign_sum_zero (J := Fin (m+1))
  have haf (x : Fin (m+1) → Bool) :
      a x=cubeSign x-2*(cubeSign x*(if g x then (1 : ℝ) else 0)) := by
    cases hg : g x
    · simp [a,hg]
    · simp [a,hg]
      ring
  have ha : (∑ x : Fin (m+1) → Bool, a x) ≠ 0 := by
    intro hz
    apply hcorr
    simp_rw [haf] at hz
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,hsum0] at hz
    linarith
  let s0 : Finset (Fin (m+1) → Bool) := Finset.univ.filter (fun x => a x=1)
  let s1 : Finset (Fin (m+1) → Bool) := Finset.univ \ s0
  have h0 : ∀ x ∈ s0, a x=1 := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have h1 : ∀ x ∈ s1, a x= -1 := by
    intro x hx
    have hn : a x ≠ 1 := by
      intro he
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ x,he⟩)
    exact (hav x).resolve_left hn
  have hsum : (∑ x : Fin (m+1) → Bool, a x)=(s0.card : ℝ)-(s1.card : ℝ) := by
    have hs0 : (∑ x ∈ s0, a x)=(s0.card : ℝ) := by
      simp only [Finset.sum_congr rfl (fun x hx => h0 x hx),Finset.sum_const,
        nsmul_eq_mul,mul_one]
    have hs1 : (∑ x ∈ s1, a x)= -(s1.card : ℝ) := by
      simp only [Finset.sum_congr rfl (fun x hx => h1 x hx),Finset.sum_const,
        nsmul_eq_mul,mul_neg,mul_one]
    have hs := Finset.sum_sdiff (f := a) (show s0 ⊆ Finset.univ from Finset.filter_subset _ _)
    change (∑ x ∈ s1, a x)+(∑ x ∈ s0, a x)=(∑ x : Fin (m+1) → Bool, a x) at hs
    linarith
  have hneq : s0.card ≠ s1.card := by
    intro he
    apply ha
    rw [hsum,he,sub_self]
  have hcard : s0.card+s1.card=2^(m+1) := by
    have he := Finset.card_sdiff_of_subset (show s0 ⊆ Finset.univ from Finset.filter_subset _ _)
    have hle := Finset.card_le_card (show s0 ⊆ Finset.univ from Finset.filter_subset _ _)
    have ht : (Finset.univ : Finset (Fin (m+1) → Bool)).card=2^(m+1) := by simp
    change s1.card=_ at he
    rw [ht] at he hle
    omega
  have hor : 2^m+1 ≤ s0.card ∨ 2^m+1 ≤ s1.card := by
    rw [pow_succ] at hcard
    omega
  have hedge (x y : Fin (m+1) → Bool) (he : a x=a y)
      (hadj : y ∈ Sensitivity.Q.adjacent x) : g x ≠ g y := by
    intro hf
    have hflip := cubeSign_edge_neg x y ((huang_adjacent_iff x y).mp hadj)
    have hn : (if g x then (-1 : ℝ) else 1) ≠ 0 := by cases g x <;> norm_num
    have hsign : cubeSign x=cubeSign y := mul_left_cancel₀ hn (by simpa only [a,← hf] using! he)
    have hz : cubeSign x=0 := by linarith
    have habs := cubeSign_abs x
    rw [hz,abs_zero] at habs
    norm_num at habs
  rcases hor with hor | hor
  · apply sensitivity_large_induced_cube_norm m g (↑s0) (by simpa using! hor)
    intro x hx y hy hadj
    exact hedge x y ((h0 x hx).trans (h0 y hy).symm) hadj
  · apply sensitivity_large_induced_cube_norm m g (↑s1) (by simpa using! hor)
    intro x hx y hy hadj
    exact hedge x y ((h1 x hx).trans (h1 y hy).symm) hadj

end Qatlib.Concepts.QueryComplexity.DegreeBounds
