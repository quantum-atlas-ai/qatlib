/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryModelComparisonDefs
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section


namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix
open scoped Classical BigOperators ENNReal

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

theorem groverAngle_sin {N M : ℕ} (hM : 0 < M) (hN : M ≤ N) :
    Real.sin (groverAngle N M hM hN) = Real.sqrt ((M : ℝ) / (N : ℝ)) := by
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hMN : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hdiv : (M : ℝ) / (N : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hsqrt := Real.sqrt_le_sqrt (x := (M : ℝ) / (N : ℝ)) (y := 1) hdiv
  have hsq : Real.sqrt ((M : ℝ) / (N : ℝ)) ≤ 1 := by simpa using hsqrt
  have hneg : (-1 : ℝ) ≤ Real.sqrt ((M : ℝ) / (N : ℝ)) := by
    have h0 : (0 : ℝ) ≤ Real.sqrt ((M : ℝ) / (N : ℝ)) := Real.sqrt_nonneg _
    linarith
  have hsin : Real.sin (Real.arcsin (Real.sqrt ((M : ℝ) / (N : ℝ))))
      = Real.sqrt ((M : ℝ) / (N : ℝ)) :=
    Real.sin_arcsin hneg hsq
  unfold groverAngle
  exact hsin

theorem groverAngle_pos {N M : ℕ} (hM : 0 < M) (hN : M ≤ N) :
    0 < groverAngle N M hM hN := by
  rw [groverAngle]
  rw [Real.arcsin_pos]
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hN0 : 0 < N := by omega
    exact_mod_cast hN0
  positivity

theorem groverAngle_le_pi_div_two {N M : ℕ} (hM : 0 < M) (hN : M ≤ N) :
    groverAngle N M hM hN ≤ Real.pi / 2 := by
  rw [groverAngle]
  exact Real.arcsin_le_pi_div_two _

theorem groverRotation_mul (θ φ : ℝ) :
    groverRotation θ * groverRotation φ = groverRotation (θ + φ) := by
  ext i j
  simp only [groverRotation, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [Real.cos_add, Real.sin_add] <;> ring

theorem groverRotation_zero : groverRotation 0 = 1 := by
  ext i j
  simp only [groverRotation, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem groverRotation_pow (θ : ℝ) (k : ℕ) :
    groverRotation θ ^ k = groverRotation (k * θ) := by
  induction k with
  | zero => simp [groverRotation_zero]
  | succ k ih =>
    rw [pow_succ, ih, groverRotation_mul]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_comm, mul_comm]

theorem groverIterations_least {N M : ℕ} (hM : 0 < M) (hN : M ≤ N) :
    (∀ k : ℕ, k < groverIterations N M hM hN →
        (2 * k + 1) * groverAngle N M hM hN < Real.pi / 2) ∧
      (2 * groverIterations N M hM hN + 1) * groverAngle N M hM hN ≥ Real.pi / 2 := by
  have hθ : 0 < groverAngle N M hM hN := groverAngle_pos hM hN
  have hθ4 : (0 : ℝ) < 4 * groverAngle N M hM hN := by positivity
  constructor
  · intro k hk
    have hk' : (k : ℝ) < Real.pi / (4 * groverAngle N M hM hN) - 1 / 2 :=
      (Nat.lt_ceil).1 hk
    have hk0 : (k : ℝ) + 1 / 2 < Real.pi / (4 * groverAngle N M hM hN) := by linarith
    have hk1 : ((k : ℝ) + 1 / 2) * (4 * groverAngle N M hM hN) < Real.pi :=
      (lt_div_iff₀ hθ4).1 hk0
    have hk2 : (2 * (k : ℝ) + 1) * groverAngle N M hM hN < Real.pi / 2 := by nlinarith
    linarith
  · have hle : Real.pi / (4 * groverAngle N M hM hN) - 1 / 2
        ≤ (groverIterations N M hM hN : ℝ) :=
      Nat.le_ceil _
    have hle0 : Real.pi / (4 * groverAngle N M hM hN)
        ≤ (groverIterations N M hM hN : ℝ) + 1 / 2 := by linarith
    have hle1 : Real.pi
        ≤ ((groverIterations N M hM hN : ℝ) + 1 / 2) * (4 * groverAngle N M hM hN) :=
      (div_le_iff₀ hθ4).1 hle0
    have hfinal : Real.pi / 2
        ≤ (2 * (groverIterations N M hM hN : ℝ) + 1) * groverAngle N M hM hN := by
      nlinarith
    linarith

theorem ceil_sub_half_bounds {x : ℝ} (hx : 0 ≤ x) :
    Nat.floor x ≤ Nat.ceil (x - 1 / 2) ∧ Nat.ceil (x - 1 / 2) ≤ Nat.ceil x := by
  have hfloor : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx
  have hceil1 : x - 1 / 2 ≤ (Nat.ceil (x - 1 / 2) : ℝ) := Nat.le_ceil _
  have hceil3 : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil _
  constructor
  · refine Nat.lt_succ_iff.mp ?_
    rw [Nat.floor_lt hx]
    have hsucc : ((Nat.ceil (x - 1 / 2)).succ : ℝ) = (Nat.ceil (x - 1 / 2) : ℝ) + 1 :=
      Nat.cast_succ _
    rw [hsucc]
    linarith
  · refine (Nat.ceil_le).2 ?_
    linarith

theorem groverIterations_floor_bounds {N M : ℕ} (hM : 0 < M) (hN : M ≤ N) :
    Nat.floor (Real.pi / (4 * groverAngle N M hM hN)) ≤ groverIterations N M hM hN ∧
      groverIterations N M hM hN
        ≤ Nat.ceil (Real.pi / (4 * groverAngle N M hM hN)) := by
  have hθ : 0 < groverAngle N M hM hN := groverAngle_pos hM hN
  have hx : Real.pi / (4 * groverAngle N M hM hN) - 1 / 2
      = Real.pi / (4 * groverAngle N M hM hN) - 1 / 2 := rfl
  have hxpos : 0 ≤ Real.pi / (4 * groverAngle N M hM hN) := by positivity
  have hbounds := ceil_sub_half_bounds (x := Real.pi / (4 * groverAngle N M hM hN)) hxpos
  constructor
  · rw [groverIterations]
    exact hbounds.1
  · rw [groverIterations]
    exact hbounds.2

structure ClassicalMachineClass (I : Type) where
  trees : List (BoolQueryTree I Bool)
  nonempty : trees ≠ []

def ClassicalMachineClass.depthSet (M : ClassicalMachineClass I) (f : (I → Bool) → Bool) :
    Finset ℕ :=
  (M.trees.filter (fun t => decide (∀ g, (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g t).1 = f g))).map
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries |>.toFinset

noncomputable def ClassicalMachineClass.minDepth (M : ClassicalMachineClass I)
    (f : (I → Bool) → Bool) (h : ∃ n, n ∈ M.depthSet f) : ℕ :=
  finsetMinNat (M.depthSet f) h

structure RandomizedMachineClass (I : Type) where
  programs : List (ClassicalProgram I Bool)
  nonempty : programs ≠ []

def RandomizedMachineClass.budgetSet (M : RandomizedMachineClass I)
    (P : ClassicalProgram I Bool → Prop) : Finset ℕ :=
  (M.programs.filter (fun prog => decide (P prog))).map ClassicalProgram.worstQueries |>.toFinset

noncomputable def RandomizedMachineClass.minBudget (M : RandomizedMachineClass I)
    (P : ClassicalProgram I Bool → Prop) (h : ∃ n, n ∈ M.budgetSet P) : ℕ :=
  finsetMinNat (M.budgetSet P) h

def ClassicalProgram.ComputesWithSuccess (prog : ClassicalProgram I Bool)
    (f : (I → Bool) → Bool) (threshold : ℝ≥0∞) : Prop :=
  ∀ g : I → Bool,
    threshold ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb prog.law g (fun b => b = f g)

def ClassicalProgram.ComputesZeroError (prog : ClassicalProgram I Bool)
    (f : (I → Bool) → Bool) : Prop :=
  ∀ g : I → Bool,
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb prog.law g (fun b => b = f g) = 1

def ClassicalProgram.ComputesZeroErrorInconclusive (prog : ClassicalProgram I Bool)
    (f : (I → Bool) → Bool) (threshold : ℝ≥0∞) : Prop :=
  ∀ g : I → Bool,
    1 - threshold ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb prog.law g (fun b => b = f g)

theorem tree_depth_ge_exactDegree {I : Type} [Fintype I] [DecidableEq I]
    (t : BoolQueryTree I Bool) (f : (I → Bool) → Bool)
    (h : ∀ g, (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g t).1 = f g) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries t := by
  refine le_trans ?_ (treeAcceptPolynomial_totalDegree_le t)
  unfold Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree
  apply csInf_le'
  refine ⟨treeAcceptPolynomial t, ?_, rfl⟩
  intro g
  have h1 := treeAcceptPolynomial_eval t g
  unfold oraclePoint at h1
  unfold Qatlib.Concepts.QueryComplexity.DegreeMethod.boolEval
  rw [h1, h g]

theorem minExactQueries_degree_bound {M : MachineClass I W} {f : (I → Bool) → Bool}
    {h : ∃ n, n ∈ M.exactCountSet f} :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f ≤ 2 * M.minExactQueries f h := by
  obtain ⟨Q, hQ, hQf, hcnt⟩ := M.minExactQueries_attained (f := f) (h := h)
  have hbound : Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f
      ≤ 2 * Qatlib.Foundations.QueryWordCore.Circuit.QueryCount Q.circuit := by
    exact Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegreeQueryLowerBound I W Q.circuit Q.initial
      Q.accept f (fun g => hQf g)
  rw [hcnt] at hbound
  exact hbound

theorem minDepth_ge_exactDegree {I : Type} [Fintype I] [DecidableEq I]
    (M : ClassicalMachineClass I) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ M.depthSet f) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree f ≤ M.minDepth f h := by
  have hmem : M.minDepth f h ∈ M.depthSet f := finsetMinNat_mem (s := M.depthSet f) (h := h)
  unfold ClassicalMachineClass.depthSet at hmem
  rw [List.mem_toFinset, List.mem_map] at hmem
  obtain ⟨t, ht, hcnt⟩ := hmem
  obtain ⟨htm, hdec⟩ := List.mem_filter.mp ht
  have hcomp : ∀ g, (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g t).1 = f g :=
      of_decide_eq_true hdec
  have hdeg := tree_depth_ge_exactDegree t f hcomp
  exact hdeg.trans_eq hcnt

end Qatlib.Concepts.QueryComplexity.DegreeMethod
