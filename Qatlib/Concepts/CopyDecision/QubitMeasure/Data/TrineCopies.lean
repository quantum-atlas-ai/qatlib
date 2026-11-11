/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.DecisionRisk.HarmonicError.TrineGeometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Trine Copies

Qubit Measure constructions for Copy Decision.
Defines `copyState`, `trineState`, `basisZero`.
Proves `copyState_inner`, `copyState_unit`, `copyState_overlap`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.QubitMeasure.Data
open Qatlib.Foundations.DecisionRisk.HarmonicError

/-- Explicit tensor-product amplitudes on the full d^n-dimensional register. -/
def copyState {d : ℕ} (n : ℕ) (x : EuclideanSpace ℂ (Fin d)) :
    EuclideanSpace ℂ (Fin n → Fin d) :=
  WithLp.toLp 2 fun bits => ∏ k, x (bits k)

/-- The stated copy-decision construction satisfies `copyState_inner` with the complete displayed premises. -/
lemma copyState_inner {d : ℕ} (n : ℕ) (x y : EuclideanSpace ℂ (Fin d)) :
    inner ℂ (copyState n x) (copyState n y) = (inner ℂ x y)^n := by
  change (∑ bits : Fin n → Fin d, (∏ k, y (bits k))*star (∏ k, x (bits k))) =
    (∑ j, y j*star (x j))^n
  simp_rw [star_prod, ←Finset.prod_mul_distrib]
  exact (Fintype.sum_pow (fun j : Fin d => y j*star (x j)) n).symm

/-- The stated copy-decision construction satisfies `copyState_unit` with the complete displayed premises. -/
lemma copyState_unit {d : ℕ} (n : ℕ) (x : EuclideanSpace ℂ (Fin d)) (hx : ‖x‖=1) :
    ‖copyState n x‖=1 := by
  have hs : inner ℂ (copyState n x) (copyState n x) = 1 := by
    rw [copyState_inner]
    simp [inner_self_eq_norm_sq_to_K, hx]
  have hn : ‖copyState n x‖^2 = 1 := by
    calc
      _ = (inner ℂ (copyState n x) (copyState n x)).re := (inner_self_eq_norm_sq (𝕜 := ℂ) (copyState n x)).symm
      _ = 1 := by rw [hs]; rfl
  nlinarith [norm_nonneg (copyState n x)]

/-- The stated copy-decision construction satisfies `copyState_overlap` with the complete displayed premises. -/
lemma copyState_overlap {d : ℕ} (n : ℕ) (x y : EuclideanSpace ℂ (Fin d)) :
    ‖inner ℂ (copyState n x) (copyState n y)‖ = ‖inner ℂ x y‖^n := by
  rw [copyState_inner, norm_pow]

/-- Three concrete distinct qubit rays, with pairwise inner product -1/2. -/
def trineState (i : Fin 3) : EuclideanSpace ℂ (Fin 2) :=
  if i=0 then !₂[1,0] else if i=1 then !₂[-1/2, (Real.sqrt 3 : ℂ)/2]
    else !₂[-1/2, -(Real.sqrt 3 : ℂ)/2]

/-- The stated copy-decision construction satisfies `trineState_gram` with the complete displayed premises. -/
lemma trineState_gram (i j : Fin 3) :
    inner ℂ (trineState i) (trineState j) = if i=j then 1 else -1/2 := by
  have h3 : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  have h3c : (Real.sqrt (3:ℝ) : ℂ)^2=3 := by exact_mod_cast h3
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_two, RCLike.inner_apply]
  fin_cases i <;> fin_cases j <;> norm_num [trineState]
  all_goals ring_nf
  all_goals norm_num [h3c, map_ofNat]

/-- The stated copy-decision construction satisfies `trineState_unit` with the complete displayed premises. -/
lemma trineState_unit (i : Fin 3) : ‖trineState i‖=1 := by
  have hs : inner ℂ (trineState i) (trineState i) = 1 := by rw [trineState_gram, if_pos rfl]
  have hn : ‖trineState i‖^2=1 := by
    calc
      _ = (inner ℂ (trineState i) (trineState i)).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) (trineState i)).symm
      _ = 1 := by rw [hs]; rfl
  nlinarith [norm_nonneg (trineState i)]

/-- The stated copy-decision construction satisfies `trine_copies_unit` with the complete displayed premises. -/
lemma trine_copies_unit (n : ℕ) (i : Fin 3) : ‖copyState n (trineState i)‖=1 :=
  copyState_unit n (trineState i) (trineState_unit i)

/-- The stated copy-decision construction satisfies `trine_copies_overlap` with the complete displayed premises. -/
lemma trine_copies_overlap (n : ℕ) (i j : Fin 3) (hij : i≠j) :
    ‖inner ℂ (copyState n (trineState i)) (copyState n (trineState j))‖ = (1/2:ℝ)^n := by
  rw [copyState_overlap, trineState_gram, if_neg hij]
  norm_num

/-- Definition of basis Zero in the Qubit Measure construction. -/
def basisZero : EuclideanSpace ℂ (Fin 2) := !₂[1,0]
/-- Definition of basis One in the Qubit Measure construction. -/
def basisOne : EuclideanSpace ℂ (Fin 2) := !₂[0,1]

/-- The stated copy-decision construction satisfies `basisZero_unit` with the complete displayed premises. -/
lemma basisZero_unit : ‖basisZero‖=1 := by
  norm_num [basisZero,PiLp.norm_eq_of_L2,Fin.sum_univ_two]
/-- The stated copy-decision construction satisfies `basisOne_unit` with the complete displayed premises. -/
lemma basisOne_unit : ‖basisOne‖=1 := by
  norm_num [basisOne,PiLp.norm_eq_of_L2,Fin.sum_univ_two]
/-- The stated copy-decision construction satisfies `basis_complex_orthogonal` with the complete displayed premises. -/
lemma basis_complex_orthogonal : inner ℂ basisZero basisOne=0 := by
  norm_num [basisZero,basisOne,PiLp.inner_apply,Fin.sum_univ_two,RCLike.inner_apply]

/-- The stated copy-decision construction satisfies `trineState_eq_input` with the complete displayed premises. -/
lemma trineState_eq_input (i : Fin 3) :
    letI : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) := InnerProductSpace.complexToReal
    trineState i=trineInput basisZero basisOne i := by
  letI : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) := InnerProductSpace.complexToReal
  fin_cases i
  · rfl
  · ext k
    fin_cases k <;> norm_num [trineState,trineInput,basisZero,basisOne]
  · ext k
    fin_cases k <;> norm_num [trineState,trineInput,basisZero,basisOne]

/-- The explicit 120-degree rotation generating the three trine rays. -/
def trineRotation : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![-1/2,-(Real.sqrt 3:ℂ)/2], ![(Real.sqrt 3:ℂ)/2,-1/2]]

/-- The stated copy-decision construction satisfies `trineRotation_unitary` with the complete displayed premises. -/
lemma trineRotation_unitary : trineRotation.conjTranspose * trineRotation = 1 := by
  have h3 : (Real.sqrt (3:ℝ) : ℂ)^2=3 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3))
  ext i j
  change (∑ k : Fin 2, star (trineRotation k i) * trineRotation k j) = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply,Matrix.conjTranspose_apply,trineRotation,Fin.sum_univ_two]
  all_goals ring_nf
  all_goals norm_num [h3,map_ofNat]

/-- The stated copy-decision construction satisfies `trineRotation_action` with the complete displayed premises. -/
lemma trineRotation_action (i : Fin 3) :
    Matrix.mulVec trineRotation (fun k => trineState i k) = fun k => trineState (i+1) k := by
  have h3 : (Real.sqrt (3:ℝ) : ℂ)^2=3 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3))
  ext k
  fin_cases i <;> fin_cases k <;>
    norm_num [trineRotation,trineState,Matrix.mulVec,dotProduct,Fin.sum_univ_two, Fin.add_def]
  all_goals ring_nf
  all_goals norm_num [h3]


/-- The stated copy-decision construction satisfies `trineRotation_third_return` with the complete displayed premises. -/
lemma trineRotation_third_return :
    Matrix.mulVec trineRotation (Matrix.mulVec trineRotation
      (Matrix.mulVec trineRotation (fun k => trineState 0 k))) = fun k => trineState 0 k := by
  rw [trineRotation_action,trineRotation_action,trineRotation_action]
  rfl


/-- The concrete input ensemble has three different rays, not just three names. -/
lemma trineState_distinct_rays (i j : Fin 3) (hij : i≠j) (c : ℂ) :
    trineState i ≠ c • trineState j := by
  intro hc
  have hn := congrArg norm hc
  rw [trineState_unit, norm_smul, trineState_unit, mul_one] at hn
  have hh := congrArg (fun x => inner ℂ x (trineState j)) hc
  rw [trineState_gram, if_neg hij, inner_smul_left, trineState_gram, if_pos rfl, mul_one] at hh
  have hhn := congrArg norm hh
  norm_num at hhn
  linarith


/-- Finite first-copy/remaining-joint lower bound for the SAME concrete trine
state on n+1 copies. Both branch weights and remaining tensor states are explicit. -/
theorem trine_tensor_first_copy_lower {ι V K : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (n : ℕ) (A : ι → EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] V)
    (hA : ∀ x, ∑ a, ‖A a x‖^2=‖x‖^2)
    (M : ι → KrausMeasurement (EuclideanSpace ℂ (Fin n → Fin 2)) K) :
    (1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n) ≤
      ∑ a, decisionError (fun k i => (M a).op k (copyState n (trineState i)))
        (fun i => ‖A a (trineState i)‖^2/3) := by
  letI : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) := InnerProductSpace.complexToReal
  have h := complex_first_copy_lower A hA basisZero basisOne basisZero_unit basisOne_unit
    basis_complex_orthogonal M (fun i => copyState n (trineState i))
    (by positivity : 0 ≤ (1/2:ℝ)^n) (trine_copies_unit n) (trine_copies_overlap n)
  have he : ((1/2:ℝ)^n)^2=(1/4:ℝ)^n := by
    rw [←pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have hp : 0 < 1+(1/2:ℝ)^n := by positivity
  have hf : ((1/2:ℝ)^n)^2/(4*(1+(1/2:ℝ)^n)) =
      (1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n) := by
    rw [he,pow_succ]
    field_simp
  rw [hf] at h
  simpa only [←trineState_eq_input] using h

end Qatlib.Concepts.CopyDecision.QubitMeasure.Data
