/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GraphSpectralConstructionDefs
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Sum

@[expose] public section
open Qatlib.Foundations.PureStateMath Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuantumGibbs.FormAlgebra

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra.GraphNormalizedChainConstruction

open Qatlib
open Matrix
open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open Qatlib.Concepts.GraphStationary.StationaryLaw
open Qatlib.Concepts.GraphLaplacian.LaplacianPsd
open Qatlib.Concepts.DirichletForm.EnergyIdentity
open Qatlib.Concepts.GraphCutTrial.CutEnergyBound
open scoped BigOperators Matrix
open scoped symmDiff

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Each term of a finite sum of nonnegative real values is at most the total sum. -/
lemma sum_ge_single {f : V → ℝ} (hf : ∀ z, 0 ≤ f z) (y : V) : f y ≤ ∑ z, f z := by
  have h := Finset.single_le_sum (s := (Finset.univ : Finset V)) (f := f)
    (fun i _ => hf i) (Finset.mem_univ y)
  exact h

/-- A vertex degree equals the sum of its adjacency indicators. -/
lemma degree_eq_sum_adj (x : V) : degree G x = ∑ z, (if G.Adj x z then (1 : ℝ) else 0) := by
  have h : neighborCount G x = ∑ z, (if G.Adj x z then (1 : ℝ) else 0) := by
    unfold neighborCount adjWeight
    rfl
  rw [← neighborCount_eq_degree G x, h]

/-- An adjacent vertex contributes at least one to the sum of adjacency indicators. -/
lemma adj_sum_ge_one {x y : V} (h : G.Adj x y) :
    (1 : ℝ) ≤ ∑ z, (if G.Adj x z then (1 : ℝ) else 0) := by
  have hsingle := Finset.single_le_sum (s := (Finset.univ : Finset V))
    (f := fun z => if G.Adj x z then (1 : ℝ) else 0)
    (fun i _ => by by_cases hz : G.Adj x i <;> simp [hz]) (Finset.mem_univ y)
  simpa [h] using! hsingle

/-- Both endpoints of an edge have positive degree. -/
lemma degree_pos_of_adj {x y : V} (h : G.Adj x y) : 0 < degree G x ∧ 0 < degree G y := by
  have hx : (1 : ℝ) ≤ degree G x := by
    rw [degree_eq_sum_adj G x]
    exact adj_sum_ge_one G h
  have hy : (1 : ℝ) ≤ degree G y := by
    rw [degree_eq_sum_adj G y]
    exact adj_sum_ge_one G (G.adj_symm h)
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hy⟩

/-- The square of `sqrtDegree` equals the vertex degree. -/
lemma sqrtDegree_sq (x : V) : sqrtDegree G x ^ 2 = degree G x :=
  Real.sq_sqrt (degree_nonneg G x)

/-- The square root of the degree is positive exactly when the degree is positive. -/
lemma sqrtDegree_pos_iff (x : V) : 0 < sqrtDegree G x ↔ 0 < degree G x := by
  rw [sqrtDegree, Real.sqrt_pos]

/-- A constant factor can be pulled out of an adjacency-restricted sum. -/
lemma sum_mul_ite (c : ℝ) (g : V → ℝ) (x : V) :
    (∑ y, (if G.Adj x y then c * g y else 0)) = c * (∑ y, (if G.Adj x y then g y else 0)) := by
  have h : (∑ y, (if G.Adj x y then c * g y else 0))
      = ∑ y ∈ (Finset.univ : Finset V), c * (if G.Adj x y then g y else 0) := by
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> ring
  rw [h, Finset.mul_sum]

/-- Expresses the normalized Laplacian as the nonisolated diagonal indicator minus the
inverse-square-root degree weighted adjacency matrix. -/
lemma normalizedLaplacian_eq (x y : V) :
    normalizedLaplacian G x y
      = (if x = y then (if degree G x = 0 then 0 else 1) else 0)
        - (if G.Adj x y then (sqrtDegree G x)⁻¹ * (sqrtDegree G y)⁻¹ else 0) := by
  by_cases hxy : x = y
  · subst hxy
    simp [normalizedLaplacian]
  · simp only [normalizedLaplacian, hxy, ite_false, normalizedAdj]
    ring

/-- The normalized Laplacian is symmetric. -/
lemma normalizedLaplacian_isSymm : (normalizedLaplacian G).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro x y
  by_cases hxy : x = y
  · subst hxy
    simp [normalizedLaplacian]
  · by_cases hadj : G.Adj x y
    · have hadj' : G.Adj y x := G.adj_symm hadj
      have hxy' : ¬ y = x := fun h => hxy h.symm
      rw [normalizedLaplacian_eq, normalizedLaplacian_eq]
      simp only [hxy, hxy', ite_false, hadj, hadj', ite_true]
      have hinv : (sqrtDegree G y)⁻¹ * (sqrtDegree G x)⁻¹
          = (sqrtDegree G x)⁻¹ * (sqrtDegree G y)⁻¹ := mul_comm _ _
      rw [hinv]
    · have hadj' : ¬ G.Adj y x := fun h => hadj (G.adj_symm h)
      have hxy' : ¬ y = x := fun h => hxy h.symm
      rw [normalizedLaplacian_eq, normalizedLaplacian_eq]
      simp only [hxy, hxy', ite_false, hadj, hadj', sub_zero]

/-- The squared norm of a degree-scaled function equals its degree-weighted sum of squares. -/
lemma degreeScaled_sq_sum (u : V → ℝ) :
    (∑ x, (degreeScaled G u x)^2) = ∑ x, degree G x * u x ^ 2 := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : degree G x = 0
  · rw [hx]
    have hzero : degreeScaled G u x = 0 := by
      unfold degreeScaled sqrtDegree
      rw [hx]
      simp
    rw [hzero]
    simp
  · rw [degreeScaled, mul_pow, sqrtDegree_sq]

/-- The normalized Laplacian form on a degree-scaled function equals its degree-weighted squared
norm minus its adjacency quadratic form. -/
theorem normalizedLaplacian_form_eq (u : V → ℝ) :
    (∑ x, ∑ y, degreeScaled G u x * normalizedLaplacian G x y * degreeScaled G u y)
      = (∑ x, degree G x * u x ^ 2)
        - (∑ x, ∑ y, (if G.Adj x y then u x * u y else 0)) := by
    have hstep : ∀ x y,
        degreeScaled G u x * normalizedLaplacian G x y * degreeScaled G u y
          = (if x = y then (if degree G x = 0 then 0 else 1) else 0)
              * degreeScaled G u x * degreeScaled G u y
            - (if G.Adj x y then u x * u y else 0) := by
      intro x y
      rw [normalizedLaplacian_eq]
      by_cases hxy : x = y
      · subst hxy
        have hnoadj : ¬ G.Adj x x := G.loopless.irrefl x
        simp only [hnoadj, ite_false]
        ring
      · by_cases hadj : G.Adj x y
        · have hpos := degree_pos_of_adj G hadj
          have hdx : 0 < sqrtDegree G x := (sqrtDegree_pos_iff G x).2 hpos.1
          have hdy : 0 < sqrtDegree G y := (sqrtDegree_pos_iff G y).2 hpos.2
          have hA : sqrtDegree G x ≠ 0 := hdx.ne'
          have hB : sqrtDegree G y ≠ 0 := hdy.ne'
          have hprod : degreeScaled G u x * -((sqrtDegree G x)⁻¹ * (sqrtDegree G y)⁻¹)
                * degreeScaled G u y = -(u x * u y) := by
            unfold degreeScaled
            have h1 : (sqrtDegree G x)⁻¹ * sqrtDegree G x = 1 := inv_mul_cancel₀ hA
            have h2 : (sqrtDegree G y)⁻¹ * sqrtDegree G y = 1 := inv_mul_cancel₀ hB
            calc
              (sqrtDegree G x * u x) * -((sqrtDegree G x)⁻¹ * (sqrtDegree G y)⁻¹)
                  * (sqrtDegree G y * u y)
                  = -(u x * ((sqrtDegree G x)⁻¹ * sqrtDegree G x)
                      * ((sqrtDegree G y)⁻¹ * sqrtDegree G y) * u y) := by ring
              _ = -(u x * u y) := by rw [h1, h2, mul_one, mul_one]
          simp only [hxy, ite_false, hadj, ite_true, zero_sub]
          rw [hprod]
          ring
        · simp only [hxy, ite_false, hadj, ite_false, sub_zero]
          ring
    calc
      (∑ x, ∑ y, degreeScaled G u x * normalizedLaplacian G x y * degreeScaled G u y)
          = ∑ x, ∑ y, ((if x = y then (if degree G x = 0 then 0 else 1) else 0)
                * degreeScaled G u x * degreeScaled G u y
              - (if G.Adj x y then u x * u y else 0)) := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            exact hstep x y
      _ = ∑ x, ((∑ y, (if x = y then (if degree G x = 0 then 0 else 1) else 0)
                * degreeScaled G u x * degreeScaled G u y)
              - (∑ y, (if G.Adj x y then u x * u y else 0))) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_sub_distrib]
      _ = (∑ x, ∑ y, (if x = y then (if degree G x = 0 then 0 else 1) else 0)
                * degreeScaled G u x * degreeScaled G u y)
            - (∑ x, ∑ y, (if G.Adj x y then u x * u y else 0)) := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ x, (if degree G x = 0 then 0 else 1) * degreeScaled G u x * degreeScaled G u x)
            - (∑ x, ∑ y, (if G.Adj x y then u x * u y else 0)) := by
        have hP : (∑ x, ∑ y, (if x = y then (if degree G x = 0 then 0 else 1) else 0)
              * degreeScaled G u x * degreeScaled G u y)
            = ∑ x, (if degree G x = 0 then 0 else 1) * degreeScaled G u x * degreeScaled G u x := by
          apply Finset.sum_congr rfl
          intro x _
          have hsum : (∑ y, (if x = y then (if degree G x = 0 then 0 else 1) else 0)
                * degreeScaled G u x * degreeScaled G u y)
              = (if degree G x = 0 then 0 else 1) * degreeScaled G u x * degreeScaled G u x := by
            have hreorder : (∑ y, (if x = y then (if degree G x = 0 then 0 else 1) else 0)
                  * degreeScaled G u x * degreeScaled G u y)
                = ∑ y ∈ (Finset.univ : Finset V),
                    (if y = x then ((if degree G x = 0 then 0 else 1)
                      * degreeScaled G u x * degreeScaled G u y) else 0) := by
              apply Finset.sum_congr rfl
              intro y _
              by_cases h : x = y
              · subst h; simp
              · have h' : ¬ y = x := fun h2 => h h2.symm
                simp [h, h']
            rw [hreorder]
            have hsingle := Finset.sum_ite_eq' (Finset.univ : Finset V) x
              (fun y => (if degree G x = 0 then 0 else 1)
                * degreeScaled G u x * degreeScaled G u y)
            simp only [Finset.mem_univ, ite_eq_left] at hsingle
            exact hsingle
          rw [hsum]
        rw [hP]
      _ = (∑ x, degree G x * u x ^ 2)
            - (∑ x, ∑ y, (if G.Adj x y then u x * u y else 0)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : degree G x = 0
        · rw [hx]
          have hzero : degreeScaled G u x = 0 := by
            unfold degreeScaled sqrtDegree
            rw [hx]
            simp
          rw [hzero]
          simp
        · have hs : (sqrtDegree G x * u x) * (sqrtDegree G x * u x)
              = degree G x * u x ^ 2 := by
            calc
              (sqrtDegree G x * u x) * (sqrtDegree G x * u x)
                  = (sqrtDegree G x) ^ 2 * u x ^ 2 := by ring
              _ = degree G x * u x ^ 2 := by rw [sqrtDegree_sq]
          unfold degreeScaled
          rw [ite_eq_right hx]
          calc
            1 * (sqrtDegree G x * u x) * (sqrtDegree G x * u x)
                = (sqrtDegree G x * u x) * (sqrtDegree G x * u x) := by ring
            _ = degree G x * u x ^ 2 := hs

/-- The normalized Laplacian form on a degree-scaled function is half the sum of squared
differences over ordered adjacent pairs. -/
theorem normalizedLaplacian_quadratic_form (u : V → ℝ) :
    (∑ x, ∑ y, degreeScaled G u x * normalizedLaplacian G x y * degreeScaled G u y)
      = (1 / 2 : ℝ) * (∑ x, ∑ y, (if G.Adj x y then (u x - u y)^2 else 0)) := by
  have hleft := normalizedLaplacian_form_eq G u
  have hright : (1 / 2 : ℝ) * (∑ x, ∑ y, (if G.Adj x y then (u x - u y)^2 else 0))
      = (∑ x, degree G x * u x ^ 2)
        - (∑ x, ∑ y, (if G.Adj x y then u x * u y else 0)) := by
    have hsq : ∀ x y, (if G.Adj x y then (u x - u y)^2 else 0)
        = (if G.Adj x y then u x ^ 2 else 0)
          + (if G.Adj x y then u y ^ 2 else 0)
          - (if G.Adj x y then 2 * (u x * u y) else 0) := by
      intro x y
      by_cases h : G.Adj x y
      · simp only [h, ite_true]
        ring
      · simp only [h, ite_false]
        ring
    have hinner : ∀ x, (∑ y, (if G.Adj x y then (u x - u y)^2 else 0))
        = (∑ y, (if G.Adj x y then u x ^ 2 else 0))
          + (∑ y, (if G.Adj x y then u y ^ 2 else 0))
          - (∑ y, (if G.Adj x y then 2 * (u x * u y) else 0)) := by
      intro x
      calc
        (∑ y, (if G.Adj x y then (u x - u y)^2 else 0))
            = ∑ y, ((if G.Adj x y then u x ^ 2 else 0)
                + (if G.Adj x y then u y ^ 2 else 0)
                - (if G.Adj x y then 2 * (u x * u y) else 0)) := by
                  apply Finset.sum_congr rfl
                  intro y _
                  exact hsq x y
        _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hfirst : (∑ x, ∑ y, (if G.Adj x y then u x ^ 2 else 0))
        = ∑ x, degree G x * u x ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      have hinner : (∑ y, (if G.Adj x y then u x ^ 2 else 0))
          = u x ^ 2 * (∑ y, (if G.Adj x y then (1 : ℝ) else 0)) := by
        calc
          (∑ y, (if G.Adj x y then u x ^ 2 else 0))
              = ∑ y, (if G.Adj x y then u x ^ 2 * 1 else 0) := by
                apply Finset.sum_congr rfl
                intro y _
                split_ifs <;> ring
          _ = u x ^ 2 * (∑ y, (if G.Adj x y then (1 : ℝ) else 0)) :=
            sum_mul_ite G _ _ _
      rw [hinner, degree_eq_sum_adj G x]
      ring
    have hsecond : (∑ x, ∑ y, (if G.Adj x y then u y ^ 2 else 0))
        = ∑ x, degree G x * u x ^ 2 := by
      have hswap : (∑ x, ∑ y, (if G.Adj x y then u y ^ 2 else 0))
          = ∑ y, ∑ x, (if G.Adj y x then u y ^ 2 else 0) := by
        calc
          (∑ x, ∑ y, (if G.Adj x y then u y ^ 2 else 0))
              = ∑ y, ∑ x, (if G.Adj x y then u y ^ 2 else 0) := Finset.sum_comm
          _ = ∑ y, ∑ x, (if G.Adj y x then u y ^ 2 else 0) := by
            apply Finset.sum_congr rfl
            intro y _
            apply Finset.sum_congr rfl
            intro x _
            by_cases h : G.Adj x y
            · simp [h, G.adj_symm h]
            · have h' : ¬ G.Adj y x := fun h2 => h (G.adj_symm h2)
              simp [h, h']
      rw [hswap]
      apply Finset.sum_congr rfl
      intro y _
      have hinner : (∑ x, (if G.Adj y x then u y ^ 2 else 0))
          = u y ^ 2 * (∑ x, (if G.Adj y x then (1 : ℝ) else 0)) := by
        calc
          (∑ x, (if G.Adj y x then u y ^ 2 else 0))
              = ∑ x, (if G.Adj y x then u y ^ 2 * 1 else 0) := by
                apply Finset.sum_congr rfl
                intro x _
                split_ifs <;> ring
          _ = u y ^ 2 * (∑ x, (if G.Adj y x then (1 : ℝ) else 0)) :=
            sum_mul_ite G _ _ _
      rw [hinner, degree_eq_sum_adj G y]
      ring
    have hthird : (∑ x, ∑ y, (if G.Adj x y then 2 * (u x * u y) else 0))
        = 2 * (∑ x, ∑ y, (if G.Adj x y then u x * u y else 0)) := by
      calc
        (∑ x, ∑ y, (if G.Adj x y then 2 * (u x * u y) else 0))
            = ∑ x, (2 * (∑ y, (if G.Adj x y then u x * u y else 0))) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [sum_mul_ite]
        _ = 2 * (∑ x, ∑ y, (if G.Adj x y then u x * u y else 0)) := by
              rw [← Finset.mul_sum]
    calc
      (1 / 2 : ℝ) * (∑ x, ∑ y, (if G.Adj x y then (u x - u y)^2 else 0))
          = (1 / 2 : ℝ) * ∑ x, ((∑ y, (if G.Adj x y then u x ^ 2 else 0))
              + (∑ y, (if G.Adj x y then u y ^ 2 else 0))
              - (∑ y, (if G.Adj x y then 2 * (u x * u y) else 0))) := by
            have hmain : (∑ x, ∑ y, (if G.Adj x y then (u x - u y)^2 else 0))
                = ∑ x, ((∑ y, (if G.Adj x y then u x ^ 2 else 0))
                    + (∑ y, (if G.Adj x y then u y ^ 2 else 0))
                    - (∑ y, (if G.Adj x y then 2 * (u x * u y) else 0))) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [hinner x]
            rw [hmain]
      _ = (1 / 2 : ℝ) * ((∑ x, ∑ y, (if G.Adj x y then u x ^ 2 else 0))
              + (∑ x, ∑ y, (if G.Adj x y then u y ^ 2 else 0))
              - (∑ x, ∑ y, (if G.Adj x y then 2 * (u x * u y) else 0))) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = (∑ x, degree G x * u x ^ 2)
              - (∑ x, ∑ y, (if G.Adj x y then u x * u y else 0)) := by
            rw [hfirst, hsecond, hthird]
            ring
  rw [hleft, hright]

/-- The weighted Laplacian applied to a function is its stationary weight times its difference
from its kernel average. -/
lemma weightedLaplacian_mulVec (f : V → ℝ) (x : V) :
    (weightedLaplacian G *ᵥ f) x = stationary G x * (f x - ∑ y, kernel G x y * f y) := by
  rw [Matrix.mulVec]
  unfold weightedLaplacian
  simp only [dotProduct]
  calc
    (∑ y, (stationary G x * ((if x = y then (1 : ℝ) else 0) - kernel G x y)) * f y)
        = stationary G x * (∑ y, ((if x = y then (1 : ℝ) else 0) - kernel G x y) * f y) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = stationary G x * (f x - ∑ y, kernel G x y * f y) := by
          congr 1
          have hsplit : (∑ y, ((if x = y then (1 : ℝ) else 0) - kernel G x y) * f y)
              = (∑ y, (if x = y then (1 : ℝ) else 0) * f y)
                - ∑ y, kernel G x y * f y := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro y _
            ring
          rw [hsplit]
          have hsingle : (∑ y, (if x = y then (1 : ℝ) else 0) * f y) = f x := by
            have hreorder : (∑ y, (if x = y then (1 : ℝ) else 0) * f y)
                = ∑ y ∈ (Finset.univ : Finset V), (if y = x then f y else 0) := by
              apply Finset.sum_congr rfl
              intro y _
              by_cases h : x = y
              · subst h; simp
              · have h' : ¬ y = x := fun h2 => h h2.symm
                simp [h, h']
            rw [hreorder]
            have h2 := Finset.sum_ite_eq' (Finset.univ : Finset V) x (fun y => f y)
            simp only [Finset.mem_univ, ite_eq_left] at h2
            exact h2
          rw [hsingle]

/-- The graph energy equals the quadratic form of the weighted Laplacian. -/
theorem energy_eq_weightedLaplacian (f : V → ℝ) :
    energy G f = ∑ x, f x * (weightedLaplacian G *ᵥ f) x := by
  unfold energy
  apply Finset.sum_congr rfl
  intro x _
  rw [weightedLaplacian_mulVec G f x]
  ring

/-- Every function has zero energy when the graph volume is zero. -/
theorem energy_eq_zero_of_volume_zero (hv : volume G = 0) (f : V → ℝ) : energy G f = 0 := by
  rw [energy_eq_weightedLaplacian G f]
  rw [weightedLaplacian_of_volume_zero G hv]
  simp

/-- For nonzero graph volume, energy is the ordered edge squared-difference sum divided by four
times the volume. -/
theorem energy_eq_quarter_edgeForm (hv : volume G ≠ 0) (f : V → ℝ) :
    energy G f
      = (1 / (4 * volume G)) * (∑ x, ∑ y, (if G.Adj x y then (f x - f y)^2 else 0)) := by
  have hquad : (∑ x, f x * (((1 / (2 * volume G)) • G.lapMatrix ℝ) *ᵥ f) x)
      = (1 / (2 * volume G)) * (∑ x, ∑ y, f x * G.lapMatrix ℝ x y * f y) := by
    calc
      (∑ x, f x * (((1 / (2 * volume G)) • G.lapMatrix ℝ) *ᵥ f) x)
          = ∑ x, (1 / (2 * volume G)) * (∑ y, f x * G.lapMatrix ℝ x y * f y) := by
            apply Finset.sum_congr rfl
            intro x _
            simp only [Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, dotProduct]
            have h1 : (∑ y, ((1 / (2 * volume G)) * G.lapMatrix ℝ x y) * f y)
                = (1 / (2 * volume G)) * (∑ y, G.lapMatrix ℝ x y * f y) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y _
              ring
            have h2 : (∑ y, f x * G.lapMatrix ℝ x y * f y)
                = f x * (∑ y, G.lapMatrix ℝ x y * f y) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y _
              ring
            rw [h1, h2]
            ring
      _ = (1 / (2 * volume G)) * (∑ x, ∑ y, f x * G.lapMatrix ℝ x y * f y) := by
            rw [Finset.mul_sum]
  have hquad' : (∑ x, ∑ y, f x * G.lapMatrix ℝ x y * f y)
      = toLinearMap₂' ℝ (G.lapMatrix ℝ) f f := by
    simp only [Matrix.toLinearMap₂'_apply']
    apply Finset.sum_congr rfl
    intro x _
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  calc
    energy G f
        = ∑ x, f x * (((1 / (2 * volume G)) • G.lapMatrix ℝ) *ᵥ f) x := by
          rw [energy_eq_weightedLaplacian G f, weightedLaplacian_eq_smul G hv]
    _ = (1 / (2 * volume G)) * (∑ x, ∑ y, f x * G.lapMatrix ℝ x y * f y) := hquad
    _ = (1 / (2 * volume G)) * toLinearMap₂' ℝ (G.lapMatrix ℝ) f f := by rw [hquad']
    _ = (1 / (2 * volume G))
        * ((∑ x, ∑ y, (if G.Adj x y then (f x - f y)^2 else 0)) / 2) := by
          rw [G.lapMatrix_toLinearMap₂' (R := ℝ) f]
    _ = (1 / (4 * volume G)) * (∑ x, ∑ y, (if G.Adj x y then (f x - f y)^2 else 0)) := by
          ring

/-- For nonzero graph volume, zero stationary mean is equivalent to `degreeMeanZero`. -/
theorem mean_zero_iff_degree_mean_zero (hv : volume G ≠ 0) (f : V → ℝ) :
    mean G f = 0 ↔ degreeMeanZero G f := by
  have hmean : mean G f = (1 / volume G) * (∑ x, degree G x * f x) := by
    unfold mean
    simp only [stationary, hv, ite_false]
    calc
      (∑ x, (degree G x / volume G) * f x)
          = ∑ x, (1 / volume G) * (degree G x * f x) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = (1 / volume G) * (∑ x, degree G x * f x) := by rw [Finset.mul_sum]
  rw [hmean]
  constructor
  · intro h
    have hne : (1 / volume G : ℝ) ≠ 0 := by
      exact div_ne_zero (by norm_num) hv
    exact (mul_eq_zero.mp h).resolve_left hne
  · intro h
    rw [h, mul_zero]

/-- For nonzero graph volume, variance is the degree-weighted squared deviation divided by the
volume. -/
theorem variance_eq_degree_weighted (hv : volume G ≠ 0) (f : V → ℝ) :
    variance G f = (1 / volume G) * (∑ x, degree G x * (f x - mean G f)^2) := by
  unfold variance
  simp only [stationary, hv, ite_false]
  calc
    (∑ x, (degree G x / volume G) * (f x - mean G f)^2)
        = ∑ x, (1 / volume G) * (degree G x * (f x - mean G f)^2) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = (1 / volume G) * (∑ x, degree G x * (f x - mean G f)^2) := by
          rw [Finset.mul_sum]

/-- For positive variance and nonzero graph volume, the energy-to-variance ratio is half the
normalized Rayleigh quotient of the centered function. -/
theorem energy_eq_half_normalizedRayleigh (hv : volume G ≠ 0) (f : V → ℝ)
    (hvariance : 0 < variance G f) :
    energy G f / variance G f
      = (1 / 2) * normalizedRayleigh G (fun x => f x - mean G f) := by
  have hvar := variance_eq_degree_weighted G hv f
  have henergy := energy_eq_quarter_edgeForm G hv f
  have hnorm : (∑ x, degree G x * (f x - mean G f)^2) ≠ 0 := by
    intro hz
    have : variance G f = 0 := by
      rw [hvar, hz]
      simp
    linarith
  have hquot : (∑ x, ∑ y, (if G.Adj x y then ((f x - mean G f) - (f y - mean G f))^2 else 0))
      = ∑ x, ∑ y, (if G.Adj x y then (f x - f y)^2 else 0) := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : G.Adj x y
    · simp only [h, ite_true]
      ring
    · simp only [h, ite_false]
  rw [normalizedRayleigh]
  rw [normalizedLaplacian_quadratic_form G (fun x => f x - mean G f)]
  rw [degreeScaled_sq_sum G (fun x => f x - mean G f)]
  rw [hquot, henergy, hvar]
  field_simp
  ring

/-- A lower bound on the edge quadratic form of mean-zero functions yields a lazy chain gap for
a graph of positive regular degree. -/
theorem lazyChainGap_of_edgeForm {d δ : ℝ} (hd : IsDegreeRegular G d) (hdpos : 0 < d)
    (hvol : volume G ≠ 0) (hδ : δ ≤ 1)
    (hbound : ∀ f : V → ℝ, mean G f = 0 →
        4 * δ * d * (∑ x, (f x)^2)
          ≤ (∑ x, ∑ y, (if G.Adj x y then (f x - f y)^2 else 0))) :
    LazyChainGap G δ := by
  intro f hmean hδ'
  have hvolpos : 0 < volume G := lt_of_le_of_ne (volume_nonneg G) (Ne.symm hvol)
  have hsq : ∀ x, (f x - mean G f)^2 = (f x)^2 := by
    intro x
    rw [hmean, sub_zero]
  have hsum : (∑ x, degree G x * (f x - mean G f)^2) = d * (∑ x, (f x)^2) := by
    calc
      (∑ x, degree G x * (f x - mean G f)^2) = ∑ x, d * (f x)^2 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hd x, hsq x]
      _ = d * (∑ x, (f x)^2) := by rw [Finset.mul_sum]
  have hvar := variance_eq_degree_weighted G hvol f
  have henergy := energy_eq_quarter_edgeForm G hvol f
  have hbound' := hbound f hmean
  have hvar' : variance G f = (d * (∑ x, (f x)^2)) / volume G := by
    rw [hvar, hsum]
    field_simp
  have henergy' : energy G f
      = (∑ x, ∑ y, (if G.Adj x y then (f x - f y)^2 else 0)) / (4 * volume G) := by
    rw [henergy]
    field_simp
  rw [hvar', henergy']
  have hA : δ * d * (∑ x, (f x)^2)
      ≤ (∑ x, ∑ y, (if G.Adj x y then (f x - f y)^2 else 0)) / 4 := by
    nlinarith [hbound']
  have hL : δ * ((d * (∑ x, (f x)^2)) / volume G)
      = (δ * d * (∑ x, (f x)^2)) / volume G := by ring
  have hR : (∑ x, ∑ y, (if G.Adj x y then (f x - f y)^2 else 0)) / (4 * volume G)
      = ((∑ x, ∑ y, (if G.Adj x y then (f x - f y)^2 else 0)) / 4) / volume G := by
    field_simp
  rw [hL, hR]
  rw [div_le_iff₀ hvolpos]
  have hmul : ((∑ x, ∑ y, (if G.Adj x y then (f x - f y)^2 else 0)) / 4) / volume G
      * volume G = (∑ x, ∑ y, (if G.Adj x y then (f x - f y)^2 else 0)) / 4 := by
    field_simp
  rw [hmul]
  exact hA

abbrev JohnsonGround (N r : ℕ) : Type := Fin r ⊕ Fin (N - r)

def johnsonMarked (N r : ℕ) : Finset (JohnsonGround N r) :=
  (Finset.univ : Finset (Fin r)).image Sum.inl

def johnsonUnmarked (N r : ℕ) : Finset (JohnsonGround N r) :=
  (Finset.univ : Finset (Fin (N - r))).image Sum.inr

abbrev JohnsonVertex (N r k : ℕ) : Type := {S : Finset (JohnsonGround N r) // S.card = k}

instance (N r k : ℕ) : Finite (JohnsonVertex N r k) := by
  unfold JohnsonVertex
  infer_instance

instance (N r k : ℕ) : Fintype (JohnsonVertex N r k) := Fintype.ofFinite _

def johnsonGraph (N r k : ℕ) : SimpleGraph (JohnsonVertex N r k) where
  Adj S S' := (S.1 ∆ S'.1).card = 2
  symm := ⟨fun S S' h => by
    have hcomm : (S'.1 ∆ S.1).card = (S.1 ∆ S'.1).card := by
      congr 1
      ext x
      simp [Finset.mem_symmDiff, or_comm, and_comm]
    rw [hcomm]
    exact h⟩
  loopless := ⟨fun S h => by
    have hempty : S.1 ∆ S.1 = ∅ := by
      ext x
      simp
    rw [hempty] at h
    simp at h⟩

instance (N r k : ℕ) : DecidableRel (johnsonGraph N r k).Adj := fun _ _ => by
  unfold johnsonGraph SimpleGraph.Adj
  infer_instance

def johnsonLayerOf {N r : ℕ} (S : Finset (JohnsonGround N r)) : ℕ :=
  (S ∩ johnsonMarked N r).card

def johnsonLayer {N r k : ℕ} (S : JohnsonVertex N r k) : ℕ := johnsonLayerOf S.1

def johnsonStepLayer {N r k : ℕ} (S : JohnsonVertex N r k) (a b : JohnsonGround N r) : ℕ :=
  johnsonLayerOf (insert b (S.1.erase a))

def johnsonBirthRate (k r i : ℕ) : ℕ := (k - i) * (r - i)

def johnsonDeathRate (k N r i : ℕ) : ℕ := i * ((N - r) - (k - i))

def johnsonSameRate (k N r i : ℕ) : ℕ := i * (r - i) + (k - i) * ((N - r) - (k - i))

/-- The Johnson marked set has cardinality `r`. -/
lemma johnson_marked_card (N r : ℕ) : (johnsonMarked N r).card = r := by
  simp [johnsonMarked, Finset.card_image_of_injective _ Sum.inl_injective]

/-- The Johnson marked and unmarked sets are disjoint. -/
lemma johnson_marked_disjoint_unmarked (N r : ℕ) :
    Disjoint (johnsonMarked N r) (johnsonUnmarked N r) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  obtain ⟨x, hx, hax⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, hay⟩ := Finset.mem_image.mp hb
  exact Sum.inl_ne_inr (a := x) (b := y) (hax.trans hay.symm)

/-- Every Johnson ground element is either marked or unmarked. -/
lemma johnson_marked_or_unmarked (N r : ℕ) (x : JohnsonGround N r) :
    x ∈ johnsonMarked N r ∨ x ∈ johnsonUnmarked N r := by
  match x with
  | Sum.inl a => exact Or.inl (by simp [johnsonMarked])
  | Sum.inr b => exact Or.inr (by simp [johnsonUnmarked])

/-- An unmarked Johnson ground element is not marked. -/
lemma johnson_unmarked_not_marked (N r : ℕ) (x : JohnsonGround N r) (hx : x ∈ johnsonUnmarked N r) :
    x ∉ johnsonMarked N r := by
  intro hm
  exact Finset.disjoint_left.mp (johnson_marked_disjoint_unmarked N r) hm hx

/-- A Johnson ground element that is not marked is unmarked. -/
lemma johnson_not_marked_unmarked (N r : ℕ) (x : JohnsonGround N r) (hx : x ∉ johnsonMarked N r) :
    x ∈ johnsonUnmarked N r := by
  rcases johnson_marked_or_unmarked N r x with hm | hu
  · exact absurd hm hx
  · exact hu

/-- The Johnson unmarked set is the complement of the marked set. -/
lemma johnson_unmarked_eq_sdiff (N r : ℕ) :
    johnsonUnmarked N r = (Finset.univ : Finset (JohnsonGround N r)) \ johnsonMarked N r := by
  apply Finset.ext
  intro x
  cases x with
  | inl a => simp [johnsonMarked, johnsonUnmarked]
  | inr b => simp [johnsonMarked, johnsonUnmarked]

/-- The Johnson unmarked set has cardinality the natural difference of `N` and `r`. -/
lemma johnson_unmarked_card (N r : ℕ) : (johnsonUnmarked N r).card = N - r := by
  rw [johnson_unmarked_eq_sdiff]
  have hsub : johnsonMarked N r ⊆ (Finset.univ : Finset (JohnsonGround N r)) :=
    Finset.subset_univ _
  rw [Finset.card_sdiff_of_subset hsub, johnson_marked_card]
  rw [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  omega

/-- A Johnson vertex's layer is at most its cardinality `k`. -/
lemma johnson_layer_le {N r k : ℕ} (S : JohnsonVertex N r k) : johnsonLayer S ≤ k := by
  have hsub : S.1 ∩ johnsonMarked N r ⊆ S.1 := Finset.inter_subset_left
  calc johnsonLayer S = (S.1 ∩ johnsonMarked N r).card := rfl
    _ ≤ S.1.card := Finset.card_le_card hsub
    _ = k := S.2

/-- The number of unmarked elements in a Johnson vertex is its cardinality minus its layer. -/
lemma johnson_unmarked_in_vertex {N r k : ℕ} (S : JohnsonVertex N r k) :
    (S.1 \ johnsonMarked N r).card = k - johnsonLayer S := by
  have h1 : (S.1 \ johnsonMarked N r).card = S.1.card - (johnsonMarked N r ∩ S.1).card :=
    Finset.card_sdiff
  have h2 : johnsonMarked N r ∩ S.1 = S.1 ∩ johnsonMarked N r := Finset.inter_comm _ _
  rw [h1, h2]
  simp [johnsonLayer, johnsonLayerOf, S.2]

/-- The number of marked elements outside a Johnson vertex is `r` minus its layer. -/
lemma johnson_marked_compl {N r k : ℕ} (S : JohnsonVertex N r k) :
    (johnsonMarked N r \ S.1).card = r - johnsonLayer S := by
  have h1 : (johnsonMarked N r \ S.1).card = (johnsonMarked N r).card
      - (S.1 ∩ johnsonMarked N r).card := Finset.card_sdiff
  rw [h1, johnson_marked_card]
  simp [johnsonLayer, johnsonLayerOf]

/-- Counts the unmarked elements outside a Johnson vertex by subtracting its unmarked membership
count from the total unmarked count. -/
lemma johnson_unmarked_compl {N r k : ℕ} (S : JohnsonVertex N r k) :
    (johnsonUnmarked N r \ S.1).card = (N - r) - (k - johnsonLayer S) := by
  have h1 : (johnsonUnmarked N r \ S.1).card = (johnsonUnmarked N r).card
      - (S.1 ∩ johnsonUnmarked N r).card := Finset.card_sdiff
  have h2 : S.1 ∩ johnsonUnmarked N r = S.1 \ johnsonMarked N r := by
    ext x
    constructor
    · intro hx
      have hxc := Finset.mem_inter.mp hx
      exact Finset.mem_sdiff.mpr ⟨hxc.1, johnson_unmarked_not_marked N r x hxc.2⟩
    · intro hx
      have hxc := Finset.mem_sdiff.mp hx
      exact Finset.mem_inter.mpr ⟨hxc.1, johnson_not_marked_unmarked N r x hxc.2⟩
  rw [h1, johnson_unmarked_card, h2, johnson_unmarked_in_vertex]

/-- Replacing an element changes the Johnson layer by adding the new element's marked indicator
and subtracting the removed element's indicator. -/
lemma johnson_stepLayer {N r k : ℕ} (S : JohnsonVertex N r k) (a b : JohnsonGround N r)
    (ha : a ∈ S.1) (hb : b ∉ S.1) :
    johnsonStepLayer S a b = johnsonLayer S + (if b ∈ johnsonMarked N r then 1 else 0)
      - (if a ∈ johnsonMarked N r then 1 else 0) := by
  have hinter : (S.1.erase a) ∩ johnsonMarked N r = (S.1 ∩ johnsonMarked N r).erase a := by
    ext x
    simp [Finset.mem_inter, Finset.mem_erase]
  have hcard : ((S.1.erase a) ∩ johnsonMarked N r).card = (S.1 ∩ johnsonMarked N r).card
      - (if a ∈ johnsonMarked N r then 1 else 0) := by
    rw [hinter]
    by_cases ha' : a ∈ johnsonMarked N r
    · rw [Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨ha, ha'⟩)]
      rw [ite_eq_left ha']
    · have hnot : a ∉ S.1 ∩ johnsonMarked N r := by
        rw [Finset.mem_inter]
        simp [ha']
      rw [Finset.card_erase_eq_ite, ite_eq_right hnot, ite_eq_right ha']
      omega
  have hge : a ∈ johnsonMarked N r → 1 ≤ (S.1 ∩ johnsonMarked N r).card := by
    intro ha'
    exact Finset.card_pos.mpr ⟨a, Finset.mem_inter.mpr ⟨ha, ha'⟩⟩
  have hins : (insert b (S.1.erase a)) ∩ johnsonMarked N r
      = if b ∈ johnsonMarked N r then
          insert b ((S.1.erase a) ∩ johnsonMarked N r) else (S.1.erase a) ∩ johnsonMarked N r := by
    by_cases hb' : b ∈ johnsonMarked N r
    · ext x
      simp [hb', Finset.mem_inter, Finset.mem_insert]
    · ext x
      simp [hb', Finset.mem_inter]
  have hnotb : b ∉ (S.1.erase a) ∩ johnsonMarked N r := by
    rw [Finset.mem_inter]
    intro hcon
    exact hb (Finset.mem_erase.mp hcon.1).2
  have hcard2 : ((insert b (S.1.erase a)) ∩ johnsonMarked N r).card
      = (S.1 ∩ johnsonMarked N r).card + (if b ∈ johnsonMarked N r then 1 else 0)
        - (if a ∈ johnsonMarked N r then 1 else 0) := by
    by_cases hb' : b ∈ johnsonMarked N r
    · rw [hins, ite_eq_left hb']
      rw [Finset.card_insert_of_notMem hnotb, hcard]
      by_cases ha' : a ∈ johnsonMarked N r
      · rw [ite_eq_left hb', ite_eq_left ha']
        have hge' := hge ha'
        omega
      · rw [ite_eq_left hb', ite_eq_right ha']
        omega
    · rw [hins, ite_eq_right hb', hcard]
      by_cases ha' : a ∈ johnsonMarked N r
      · rw [ite_eq_right hb', ite_eq_left ha']
        have hge' := hge ha'
        omega
      · rw [ite_eq_right hb', ite_eq_right ha']
        omega
  simp only [johnsonStepLayer, johnsonLayerOf]
  rw [hcard2]
  rfl

/-- The sums over a predicate and its negation add to the original finite sum. -/
lemma sum_split_pred {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] (f : α → ℝ) :
    (∑ x ∈ s.filter p, f x) + ∑ x ∈ s.filter (fun x => ¬ p x), f x = ∑ x ∈ s, f x := by
  have hunion : s.filter p ∪ s.filter (fun x => ¬ p x) = s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hx : p x <;> simp [hx]
  have hdisj : Disjoint (s.filter p) (s.filter (fun x => ¬ p x)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact absurd (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  rw [← Finset.sum_union hdisj, hunion]

/-- Filtering a finite set for nonmembership in another set has the cardinality of their set
difference. -/
lemma card_filter_neg {α : Type*} [DecidableEq α] (s t : Finset α) :
    (s.filter (fun a => a ∉ t)).card = (s \ t).card := by
  congr 1
  ext x
  simp [Finset.mem_sdiff]

/-- Filtering a finite set for membership in another set has the cardinality of their
intersection. -/
lemma card_filter_pos {α : Type*} [DecidableEq α] (s t : Finset α) :
    (s.filter (fun a => a ∈ t)).card = (s ∩ t).card := by
  rw [Finset.filter_mem_eq_inter]

/-- A constant-valued double finite sum is the product of the two cardinalities and the
constant. -/
lemma sum_const_two {α β : Type*} (s : Finset α) (t : Finset β) (c : ℝ)
    (F : α → β → ℝ) (h : ∀ a ∈ s, ∀ b ∈ t, F a b = c) :
    (∑ a ∈ s, ∑ b ∈ t, F a b) = s.card * t.card * c := by
  calc (∑ a ∈ s, ∑ b ∈ t, F a b) = ∑ a ∈ s, ∑ b ∈ t, c := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        exact h a ha b hb
    _ = ∑ a ∈ s, t.card * c := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
    _ = s.card * (t.card * c) := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
    _ = s.card * t.card * c := by ring

/-- The sum over Johnson replacement steps splits into birth, death, and same-layer
contributions with their respective rates. -/
theorem johnson_layerTransport {N r k : ℕ} (S : JohnsonVertex N r k) (g : ℕ → ℝ) :
    (∑ a ∈ S.1, ∑ b ∈ (Finset.univ : Finset (JohnsonGround N r)) \ S.1,
        g (johnsonStepLayer S a b))
      = (johnsonBirthRate k r (johnsonLayer S) : ℝ) * g (johnsonLayer S + 1)
        + (johnsonDeathRate k N r (johnsonLayer S) : ℝ) * g (johnsonLayer S - 1)
        + (johnsonSameRate k N r (johnsonLayer S) : ℝ) * g (johnsonLayer S) := by
  classical
  set M := johnsonMarked N r with hMdef
  set T := (Finset.univ : Finset (JohnsonGround N r)) \ S.1 with hTdef
  have hcardA : (S.1.filter (fun a => a ∈ M)).card = johnsonLayer S := by
    rw [card_filter_pos]
    simp [hMdef, johnsonLayer, johnsonLayerOf]
  have hcardB : (S.1.filter (fun a => a ∉ M)).card = k - johnsonLayer S := by
    rw [card_filter_neg, johnson_unmarked_in_vertex]
  have hcardC : (T.filter (fun b => b ∈ M)).card = r - johnsonLayer S := by
    rw [card_filter_pos]
    have hset : T ∩ M = johnsonMarked N r \ S.1 := by
      ext x
      simp only [hTdef, hMdef, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_inter]
      constructor
      · intro hx
        exact ⟨hx.2, hx.1⟩
      · intro hx
        exact ⟨hx.2, hx.1⟩
    rw [hset, johnson_marked_compl]
  have hcardD : (T.filter (fun b => b ∉ M)).card = (N - r) - (k - johnsonLayer S) := by
    rw [card_filter_neg]
    have hset : T \ M = johnsonUnmarked N r \ S.1 := by
      ext x
      simp only [hTdef, hMdef, Finset.mem_sdiff, Finset.mem_univ, true_and]
      constructor
      · intro hx
        exact ⟨johnson_not_marked_unmarked N r x hx.2, hx.1⟩
      · intro hx
        exact ⟨hx.2, johnson_unmarked_not_marked N r x hx.1⟩
    rw [hset, johnson_unmarked_compl]
  have hstep : ∀ a b : JohnsonGround N r, a ∈ S.1 → b ∉ S.1 →
      johnsonStepLayer S a b = johnsonLayer S + (if b ∈ M then 1 else 0)
        - (if a ∈ M then 1 else 0) := by
    intro a b ha hb
    rw [johnson_stepLayer S a b ha hb]
  have hmm : ∀ a ∈ S.1, a ∈ M → ∀ b ∈ T, b ∈ M →
      johnsonStepLayer S a b = johnsonLayer S := by
    intro a ha ham b hb hbm
    rw [hstep a b ha (Finset.mem_sdiff.mp hb).2]
    simp [ham, hbm]
  have hmu : ∀ a ∈ S.1, a ∈ M → ∀ b ∈ T, b ∉ M →
      johnsonStepLayer S a b = johnsonLayer S - 1 := by
    intro a ha ham b hb hbm
    rw [hstep a b ha (Finset.mem_sdiff.mp hb).2]
    simp [ham, hbm]
  have hum : ∀ a ∈ S.1, a ∉ M → ∀ b ∈ T, b ∈ M →
      johnsonStepLayer S a b = johnsonLayer S + 1 := by
    intro a ha ham b hb hbm
    rw [hstep a b ha (Finset.mem_sdiff.mp hb).2]
    simp [ham, hbm]
  have huu : ∀ a ∈ S.1, a ∉ M → ∀ b ∈ T, b ∉ M →
      johnsonStepLayer S a b = johnsonLayer S := by
    intro a ha ham b hb hbm
    rw [hstep a b ha (Finset.mem_sdiff.mp hb).2]
    simp [ham, hbm]
  have hsplit : (∑ a ∈ S.1, ∑ b ∈ T, g (johnsonStepLayer S a b))
      = (∑ a ∈ S.1.filter (fun a => a ∈ M), ∑ b ∈ T.filter (fun b => b ∈ M),
          g (johnsonStepLayer S a b)
        + ∑ a ∈ S.1.filter (fun a => a ∈ M), ∑ b ∈ T.filter (fun b => b ∉ M),
          g (johnsonStepLayer S a b))
        + (∑ a ∈ S.1.filter (fun a => a ∉ M), ∑ b ∈ T.filter (fun b => b ∈ M),
          g (johnsonStepLayer S a b)
        + ∑ a ∈ S.1.filter (fun a => a ∉ M), ∑ b ∈ T.filter (fun b => b ∉ M),
          g (johnsonStepLayer S a b)) := by
    have houter : (∑ a ∈ S.1, ∑ b ∈ T, g (johnsonStepLayer S a b))
        = ∑ a ∈ S.1.filter (fun a => a ∈ M), ∑ b ∈ T, g (johnsonStepLayer S a b)
          + ∑ a ∈ S.1.filter (fun a => a ∉ M), ∑ b ∈ T, g (johnsonStepLayer S a b) := by
      rw [← sum_split_pred S.1 (fun a => a ∈ M) (fun a => ∑ b ∈ T, g (johnsonStepLayer S a b))]
    have hinner : ∀ (u : Finset (JohnsonGround N r)),
        (∑ a ∈ u, ∑ b ∈ T, g (johnsonStepLayer S a b))
          = ∑ a ∈ u, (∑ b ∈ T.filter (fun b => b ∈ M), g (johnsonStepLayer S a b)
              + ∑ b ∈ T.filter (fun b => b ∉ M), g (johnsonStepLayer S a b)) := by
      intro u
      apply Finset.sum_congr rfl
      intro a _
      have h := sum_split_pred T (fun b => b ∈ M) (fun b => g (johnsonStepLayer S a b))
      linarith
    rw [houter, hinner (S.1.filter (fun a => a ∈ M)),
      hinner (S.1.filter (fun a => a ∉ M))]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsplit]
  rw [sum_const_two _ _ _ _ (fun a ha b hb => by
    rw [hmm a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
      b (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2])]
  rw [sum_const_two _ _ _ _ (fun a ha b hb => by
    rw [hmu a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
      b (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2])]
  rw [sum_const_two _ _ _ _ (fun a ha b hb => by
    rw [hum a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
      b (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2])]
  rw [sum_const_two _ _ _ _ (fun a ha b hb => by
    rw [huu a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
      b (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2])]
  rw [hcardA, hcardC, hcardB, hcardD]
  simp only [johnsonBirthRate, johnsonDeathRate, johnsonSameRate, Nat.cast_mul, Nat.cast_add]
  ring

section NormalizedChainBridge

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Nonzero graph volume implies the vertex type is nonempty. -/
theorem volume_ne_zero_nonempty (hv : volume G ≠ 0) : Nonempty V := by
  classical
  by_contra h
  let : IsEmpty V := ⟨fun x => h ⟨x⟩⟩
  have huniv : Finset.univ = (∅ : Finset V) := Finset.univ_eq_empty
  unfold volume at hv
  rw [huniv] at hv
  simp at hv

/-- The lazy kernel is half the identity plus half the normalized kernel. -/
theorem kernel_eq_half_add_normalizedKernel (x y : V) :
    kernel G x y = (if x = y then (1 / 2 : ℝ) else 0) + (1 / 2) * normalizedKernel G x y := by
  by_cases hdx : degree G x = 0
  · have hker : kernel G x y = (if x = y then (1 : ℝ) else 0) := by
      simp [kernel, hdx]
    have hnorm : normalizedKernel G x y = (if x = y then (1 : ℝ) else 0) := by
      simp [normalizedKernel, hdx]
    rw [hker, hnorm]
    by_cases hxy : x = y
    · simp [hxy]; norm_num
    · simp [hxy]
  · have hdne : degree G x ≠ 0 := hdx
    have hker : kernel G x y = (if x = y then (1 / 2 : ℝ) else 0)
        + (if G.Adj x y then 1 / (2 * degree G x) else 0) := by
      simp [kernel, hdx]
    have hnorm : normalizedKernel G x y = (if G.Adj x y then (degree G x)⁻¹ else 0) := by
      simp [normalizedKernel, hdx]
    have h1 : (1 / (2 * degree G x) : ℝ) = (1 / 2 : ℝ) * (degree G x)⁻¹ := by
      field_simp [hdne]
    rw [hker, hnorm]
    by_cases hadj : G.Adj x y
    · by_cases hxy : x = y
      · simp [hxy]
      · simp [hadj, hxy, h1]
    · by_cases hxy : x = y
      · simp [hxy]
      · simp [hadj, hxy]

/-- Every row of the normalized kernel sums to one. -/
theorem normalizedKernel_row_sum (x : V) : ∑ y, normalizedKernel G x y = 1 := by
  by_cases hx : degree G x = 0
  · have hnorm : ∀ y, normalizedKernel G x y = (if x = y then (1 : ℝ) else 0) := by
      intro y
      simp [normalizedKernel, hx]
    simp_rw [hnorm]
    exact Qatlib.Concepts.GraphStationary.StationaryLaw.sum_diag x (1 : ℝ)
  · have hpos : 0 < degree G x := lt_of_le_of_ne (degree_nonneg G x) (Ne.symm hx)
    have hnorm : ∀ y, normalizedKernel G x y = (if G.Adj x y then (degree G x)⁻¹ else 0) := by
      intro y
      simp [normalizedKernel, hx]
    simp_rw [hnorm]
    calc (∑ y, (if G.Adj x y then (degree G x)⁻¹ else 0))
        = (degree G x)⁻¹ * ∑ y, (if G.Adj x y then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          by_cases h : G.Adj x y <;> simp [h]
      _ = (degree G x)⁻¹ * degree G x := by rw [degree_eq_sum_adj]
      _ = 1 := by field_simp [hpos.ne']

/-- The normalized kernel has nonnegative entries. -/
theorem normalizedKernel_nonneg (x y : V) : 0 ≤ normalizedKernel G x y := by
  by_cases hx : degree G x = 0
  · simp [normalizedKernel, hx]
    split_ifs <;> norm_num
  · have hpos : 0 < degree G x := lt_of_le_of_ne (degree_nonneg G x) (Ne.symm hx)
    simp [normalizedKernel, hx]
    split_ifs with h
    · positivity
    · norm_num

/-- For nonzero graph volume, the normalized kernel satisfies detailed balance with the
stationary weights. -/
theorem normalizedKernel_detailed_balance (hv : volume G ≠ 0) (x y : V) :
    stationary G x * normalizedKernel G x y = stationary G y * normalizedKernel G y x := by
  have hvpos : 0 < volume G := lt_of_le_of_ne (volume_nonneg G) (Ne.symm hv)
  simp only [stationary, hv, ite_false]
  by_cases hx : degree G x = 0
  · have hnx : ¬ G.Adj x y := not_adj_of_degree_eq_zero G hx y
    have hny : ¬ G.Adj y x := fun h => hnx (G.adj_symm h)
    by_cases hxy : x = y
    · subst hxy
      simp [normalizedKernel, hx]
    · by_cases hy : degree G y = 0
      · simp [normalizedKernel, hx, hy, hxy, Ne.symm hxy]
      · simp [normalizedKernel, hx, hy, hxy, hny]
  · by_cases hy : degree G y = 0
    · have hny : ¬ G.Adj y x := not_adj_of_degree_eq_zero G hy x
      have hnx : ¬ G.Adj x y := fun h => hny (G.adj_symm h)
      by_cases hxy : x = y
      · subst hxy
        simp [hy] at hx
      · simp [normalizedKernel, hx, hy, Ne.symm hxy, hnx]
    · have hxpos : 0 < degree G x := lt_of_le_of_ne (degree_nonneg G x) (Ne.symm hx)
      have hypos : 0 < degree G y := lt_of_le_of_ne (degree_nonneg G y) (Ne.symm hy)
      by_cases hxy : x = y
      · subst hxy
        simp [normalizedKernel, hx]
      · by_cases hadj : G.Adj x y
        · have hadj' : G.Adj y x := G.adj_symm hadj
          simp [normalizedKernel, hx, hy, hadj, hadj']
          field_simp [hxpos.ne', hypos.ne', hvpos.ne']
        · have hadj' : ¬ G.Adj y x := fun h => hadj (G.adj_symm h)
          simp [normalizedKernel, hx, hy, hadj, hadj']

/-- For nonzero graph volume, a set's mass is the sum of its vertex degrees divided by total
volume. -/
theorem mass_eq_degreeVolume (hv : volume G ≠ 0) (S : Finset V) :
    mass G S = (∑ x ∈ S, degree G x) / volume G := by
  unfold mass
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [stationary, hv]

/-- A sum over all vertices splits into sums over a finite set and its complement. -/
lemma sum_split_mem {f : V → ℝ} (S : Finset V) :
    (∑ x, f x) = (∑ x ∈ S, f x) + ∑ x ∈ Sᶜ, f x :=
  (Finset.sum_add_sum_compl S f).symm

/-- Summing a function masked by finite-set membership equals summing it over that set. -/
lemma sum_ite_mem_eq {f : V → ℝ} (S : Finset V) :
    (∑ x, (if x ∈ S then f x else 0)) = ∑ x ∈ S, f x := by
  have hsplit := Finset.sum_add_sum_compl S (fun x => (if x ∈ S then f x else 0))
  rw [← hsplit]
  have h1 : (∑ x ∈ S, (if x ∈ S then f x else 0)) = ∑ x ∈ S, f x := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp [hx]
  have h2 : (∑ x ∈ Sᶜ, (if x ∈ S then f x else 0)) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    simp [Finset.mem_compl.mp hx]
  rw [h1, h2, add_zero]

/-- For nonzero graph volume, a centered indicator has zero mean. -/
theorem mean_centeredIndicator_eq_zero (hv : volume G ≠ 0) (S : Finset V) :
    mean G (centeredIndicator G S) = 0 := by
  have hmass : mass G S = (∑ x ∈ S, degree G x) / volume G :=
    mass_eq_degreeVolume G hv S
  have hvol : (∑ x, degree G x) = volume G := rfl
  have hmean : mean G (centeredIndicator G S)
      = (1 / volume G) * (∑ x, degree G x * centeredIndicator G S x) := by
    unfold mean
    simp only [stationary, hv, ite_false]
    calc
      (∑ x, (degree G x / volume G) * centeredIndicator G S x)
          = ∑ x, (1 / volume G) * (degree G x * centeredIndicator G S x) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = (1 / volume G) * (∑ x, degree G x * centeredIndicator G S x) := by rw [Finset.mul_sum]
  rw [hmean]
  have hsplit : (∑ x, degree G x * centeredIndicator G S x)
      = (∑ x ∈ S, degree G x) - mass G S * (∑ x, degree G x) := by
    have h1 : (∑ x, degree G x * (if x ∈ S then (1 : ℝ) else 0)) = ∑ x ∈ S, degree G x := by
      have hconv : (∑ x, degree G x * (if x ∈ S then (1 : ℝ) else 0))
          = ∑ x, (if x ∈ S then degree G x else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ S <;> simp [hx]
      rw [hconv, sum_ite_mem_eq]
    have h2 : (∑ x, degree G x * mass G S) = mass G S * (∑ x, degree G x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    simp only [centeredIndicator, mul_sub, Finset.sum_sub_distrib]
    rw [h1, h2]
  rw [hsplit, hmass, hvol]
  have hcancel : (∑ x ∈ S, degree G x) / volume G * volume G = ∑ x ∈ S, degree G x := by
    field_simp [hv]
  rw [hcancel, sub_self, mul_zero]

/-- For nonzero graph volume, the variance of a centered indicator is its set mass times one
minus that mass. -/
theorem variance_centeredIndicator_eq (hv : volume G ≠ 0) (S : Finset V) :
    variance G (centeredIndicator G S) = mass G S * (1 - mass G S) := by
  have hmean0 : mean G (centeredIndicator G S) = 0 :=
    mean_centeredIndicator_eq_zero G hv S
  have hmass : mass G S = (∑ x ∈ S, degree G x) / volume G :=
    mass_eq_degreeVolume G hv S
  have hvol : (∑ x, degree G x) = volume G := rfl
  rw [variance_eq_degree_weighted G hv, hmean0]
  simp only [sub_zero]
  have hsq : ∀ x, (centeredIndicator G S x)^2
      = if x ∈ S then (1 - mass G S)^2 else (mass G S)^2 := by
    intro x
    by_cases hx : x ∈ S
    · simp only [centeredIndicator, ite_eq_left hx]
    · simp only [centeredIndicator, ite_eq_right hx]
      ring
  simp_rw [hsq]
  have hconv : (∑ x, degree G x
        * (if x ∈ S then (1 - mass G S)^2 else (mass G S)^2))
      = ∑ x, (if x ∈ S then degree G x * (1 - mass G S)^2
          else degree G x * (mass G S)^2) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ S <;> simp [hx]
  rw [hconv]
  rw [← Finset.sum_add_sum_compl (s := S)
    (f := fun x => if x ∈ S then degree G x * (1 - mass G S)^2
      else degree G x * (mass G S)^2)]
  have hA : (∑ x ∈ S, (if x ∈ S then degree G x * (1 - mass G S)^2
        else degree G x * (mass G S)^2))
      = (1 - mass G S)^2 * (∑ x ∈ S, degree G x) := by
    have hstep : (∑ x ∈ S, (if x ∈ S then degree G x * (1 - mass G S)^2
          else degree G x * (mass G S)^2))
        = ∑ x ∈ S, degree G x * (1 - mass G S)^2 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp [hx]
    rw [hstep, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hB : (∑ x ∈ Sᶜ, (if x ∈ S then degree G x * (1 - mass G S)^2
        else degree G x * (mass G S)^2))
      = (mass G S)^2 * (∑ x ∈ Sᶜ, degree G x) := by
    have hstep : (∑ x ∈ Sᶜ, (if x ∈ S then degree G x * (1 - mass G S)^2
          else degree G x * (mass G S)^2))
        = ∑ x ∈ Sᶜ, degree G x * (mass G S)^2 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp [Finset.mem_compl.mp hx]
    rw [hstep, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hA, hB]
  have hsetvol : (∑ x ∈ S, degree G x) = mass G S * volume G := by
    rw [hmass]
    field_simp [hv]
  have hcomplvol : (∑ x ∈ Sᶜ, degree G x) = volume G - ∑ x ∈ S, degree G x := by
    have hsplit := sum_split_mem (S := S) (f := fun x => degree G x)
    rw [hvol] at hsplit
    linarith
  rw [hcomplvol, hsetvol]
  have hkey : (1 - mass G S)^2 * (mass G S * volume G)
      + (mass G S)^2 * (volume G - mass G S * volume G)
      = volume G * (mass G S * (1 - mass G S)) := by ring
  rw [hkey]
  field_simp [hv]

/-- A separating cut's centered indicator has zero energy when graph volume is nonzero. -/
theorem separatingCut_energy_zero (hv : volume G ≠ 0) {S : Finset V} (hsep : separates G S) :
    energy G (centeredIndicator G S) = 0 := by
  rw [energy_eq_quarter_edgeForm G hv, mul_eq_zero]
  refine Or.inr ?_
  refine Finset.sum_eq_zero fun x _ => ?_
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hadj : G.Adj x y
  · by_cases hx : x ∈ S
    · have hy : y ∈ S := by
        by_contra hy
        exact (hsep x hx y (Finset.mem_compl.mpr hy)) hadj
      simp [hadj, centeredIndicator, hx, hy]
    · have hy : y ∉ S := by
        by_contra hy
        exact (hsep y hy x (Finset.mem_compl.mpr hx)) (G.adj_symm hadj)
      simp [hadj, centeredIndicator, hx, hy]
  · simp [hadj]

/-- A separating cut with mass strictly between zero and one yields a centered indicator with
zero mean, zero energy, and positive variance. -/
theorem separatingCut_centeredIndicator (hv : volume G ≠ 0) {S : Finset V}
    (hsep : separates G S) (hm : 0 < mass G S) (hlt : mass G S < 1) :
    mean G (centeredIndicator G S) = 0 ∧
      energy G (centeredIndicator G S) = 0 ∧
      0 < variance G (centeredIndicator G S) := by
  refine ⟨mean_centeredIndicator_eq_zero G hv S, separatingCut_energy_zero G hv hsep, ?_⟩
  rw [variance_centeredIndicator_eq G hv S]
  have hrest : 0 < 1 - mass G S := by linarith
  exact mul_pos hm hrest

/-- The normalized Laplacian row of a zero-degree vertex vanishes. -/
theorem isolated_normalizedLaplacian_zero {x : V} (hx : degree G x = 0) (y : V) :
    normalizedLaplacian G x y = 0 := by
  rw [normalizedLaplacian_eq]
  by_cases hxy : x = y
  · subst hxy
    simp [hx]
  · have hnotadj : ¬ G.Adj x y := not_adj_of_degree_eq_zero G hx y
    simp [hxy, hnotadj]

/-- A zero-degree vertex has zero stationary weight when graph volume is nonzero. -/
theorem isolated_stationary_zero (hv : volume G ≠ 0) {x : V} (hx : degree G x = 0) :
    stationary G x = 0 := by
  simp [stationary, hv, hx]

/-- When graph volume is zero, the lazy kernel is the identity transition kernel. -/
theorem volume_zero_kernel_stayPut (hv : volume G = 0) (x y : V) :
    kernel G x y = if x = y then 1 else 0 := by
  have hdx : degree G x = 0 := degree_eq_zero_of_volume_eq_zero G hv x
  simp [kernel, hdx]

end NormalizedChainBridge

end Qatlib.Concepts.QuantumGibbs.FormAlgebra.GraphNormalizedChainConstruction
