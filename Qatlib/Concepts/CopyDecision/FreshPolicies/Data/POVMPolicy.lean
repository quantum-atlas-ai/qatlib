/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.FiniteOptimum
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# POVMPolicy

Fresh Policies constructions for Copy Decision.
Defines `povmKraus`, `qubitBorn`, `FinitePOVMPolicy`.
Proves `qubit_matrix_inner`, `povmKraus_gram`, `povmKraus_mass`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.FreshPolicies.Data
open Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError

open Matrix
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument

/-- The square-root realization of an actual finite qubit POVM. -/
def povmKraus {m : ℕ} (Λ : POVM (Fin m) (Fin 2)) (a : Fin m) : Qubit →ₗ[ℂ] Qubit :=
  (Λ.mats a ^ (1/2:ℝ)).mat.toEuclideanLin

/-- The stated copy-decision construction satisfies `qubit_matrix_inner` with the complete displayed premises. -/
private lemma qubit_matrix_inner (A : Matrix (Fin 2) (Fin 2) ℂ) (x y : Qubit) :
    inner ℂ (A.toEuclideanLin x) (A.toEuclideanLin y) =
      inner ℂ x ((A.conjTranspose*A).toEuclideanLin y) := by
  rw [← LinearMap.adjoint_inner_right,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  congr 1
  change WithLp.toLp 2 (A.conjTranspose *ᵥ (A *ᵥ WithLp.ofLp y)) =
    WithLp.toLp 2 ((A.conjTranspose*A) *ᵥ WithLp.ofLp y)
  rw [Matrix.mulVec_mulVec]

/-- The stated copy-decision construction satisfies `povmKraus_gram` with the complete displayed premises. -/
lemma povmKraus_gram {m : ℕ} (Λ : POVM (Fin m) (Fin 2)) (x y : Qubit) :
    ∑ a, inner ℂ (povmKraus Λ a x) (povmKraus Λ a y)=inner ℂ x y := by
  simp only [povmKraus, qubit_matrix_inner]
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
    inner ℂ x (A.toEuclideanLin y)) (povm_sqrt_complete Λ)
  simpa [map_sum, LinearMap.sum_apply, inner_sum, Matrix.toLpLin_apply] using h

/-- The stated copy-decision construction satisfies `povmKraus_mass` with the complete displayed premises. -/
lemma povmKraus_mass {m : ℕ} (Λ : POVM (Fin m) (Fin 2)) (x : Qubit) :
    ∑ a, ‖povmKraus Λ a x‖^2=‖x‖^2 := by
  have h := povmKraus_gram Λ x x
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- Born probability is defined from the actual effect, not from its realization. -/
def qubitBorn (E : HermitianMat (Fin 2) ℂ) (x : Qubit) : ℝ :=
  (inner ℂ x (E.mat.toEuclideanLin x)).re

/-- The stated copy-decision construction satisfies `povmKraus_born` with the complete displayed premises. -/
lemma povmKraus_born {m : ℕ} (Λ : POVM (Fin m) (Fin 2)) (a : Fin m) (x : Qubit) :
    ‖povmKraus Λ a x‖^2=qubitBorn (Λ.mats a) x := by
  have h := qubit_matrix_inner (Λ.mats a ^ (1/2:ℝ)).mat x x
  rw [HermitianMat.conjTranspose_mat, HermitianMat.pow_half_mul (Λ.nonneg a)] at h
  calc
    _ = (inner ℂ (povmKraus Λ a x) (povmKraus Λ a x)).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) (povmKraus Λ a x)).symm
    _ = qubitBorn (Λ.mats a) x := congrArg Complex.re h

/-- Actual finite POVM trees with classical feedforward and discarded outputs.
No completeness or error lower bound oracle is part of this input structure. -/
inductive FinitePOVMPolicy : ℕ → Type where
  | leaf (p : TerminalDecision) : FinitePOVMPolicy 0
  | step {n : ℕ} (m : ℕ) (Λ : POVM (Fin m) (Fin 2))
      (next : Fin m → FinitePOVMPolicy n) : FinitePOVMPolicy (n+1)

/-- Definition of povm Policy Error in the Fresh Policies construction. -/
def povmPolicyError : {n : ℕ} → FinitePOVMPolicy n → (Fin 3 → ℝ) → ℝ
  | _, .leaf p, q => ∑ i, q i*(1-p.prob i)
  | _, .step _ Λ next, q =>
      ∑ a, povmPolicyError (next a) (fun i => q i*qubitBorn (Λ.mats a) (trineState i))

/-- A classical-only continuation has exactly the same Born recursion after
replacing each discarded instrument by its POVM square-root realization. -/
def FinitePOVMPolicy.toFinite : {n : ℕ} → FinitePOVMPolicy n → FinitePolicy n
  | _, .leaf p => .leaf p
  | _, .step m Λ next => .step m (povmKraus Λ) (povmKraus_mass Λ) (povmKraus_gram Λ)
      (fun a => (next a).toFinite)

/-- The stated copy-decision construction satisfies `povmPolicyError_eq` with the complete displayed premises. -/
theorem povmPolicyError_eq {n : ℕ} (P : FinitePOVMPolicy n) (q : Fin 3 → ℝ) :
    povmPolicyError P q=policyError P.toFinite q := by
  induction P generalizing q with
  | leaf p => rfl
  | step m Λ next ih =>
    simp only [povmPolicyError, FinitePOVMPolicy.toFinite, policyError]
    simp_rw [ih, povmKraus_born]

/-- The target lower coefficient now consumes actual arbitrary finite qubit
POVMs at every node. General outcome spaces remain a separate obligation. -/
theorem finitePOVMPolicy_uniform_lower {n : ℕ} (P : FinitePOVMPolicy (n+1)) :
    (1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n) ≤ povmPolicyError P (fun _ => 1/3) := by
  rw [povmPolicyError_eq]
  exact finitePolicy_uniform_lower P.toFinite

/-- Definition of identity POVM in the Fresh Policies construction. -/
def identityPOVM : POVM (Fin 1) (Fin 2) where
  mats := fun _ => 1
  nonneg := by intro a; positivity
  normalized := by simp

/-- Definition of ignore Copy in the Fresh Policies construction. -/
def FinitePOVMPolicy.ignoreCopy {n : ℕ} (P : FinitePOVMPolicy n) :
    FinitePOVMPolicy (n+1) := .step 1 identityPOVM (fun _ => P)

/-- The stated copy-decision construction satisfies `povmPolicyError_ignoreCopy` with the complete displayed premises. -/
lemma povmPolicyError_ignoreCopy {n : ℕ} (P : FinitePOVMPolicy n) (q : Fin 3 → ℝ) :
    povmPolicyError P.ignoreCopy q=povmPolicyError P q := by
  simp [povmPolicyError, FinitePOVMPolicy.ignoreCopy, identityPOVM, qubitBorn,
    inner_self_eq_norm_sq_to_K, trineState_unit]

/-- Definition of ignored POVMCopies in the Fresh Policies construction. -/
def ignoredPOVMCopies : (n : ℕ) → FinitePOVMPolicy n
  | 0 => .leaf uniformGuess
  | n+1 => (ignoredPOVMCopies n).ignoreCopy

/-- Actual finite POVM risk range; general measurable outcome spaces are not
silently included by this definition. -/
def finitePOVMRisks (n : ℕ) (q : Fin 3 → ℝ) : Set ℝ :=
  Set.range (fun P : FinitePOVMPolicy n => povmPolicyError P q)

/-- Definition of finite POVMOptimum in the Fresh Policies construction. -/
def finitePOVMOptimum (n : ℕ) (q : Fin 3 → ℝ) : ℝ := sInf (finitePOVMRisks n q)

/-- The stated copy-decision construction satisfies `finitePOVMRisks_nonempty` with the complete displayed premises. -/
lemma finitePOVMRisks_nonempty (n : ℕ) (q : Fin 3 → ℝ) :
    (finitePOVMRisks n q).Nonempty :=
  ⟨povmPolicyError (ignoredPOVMCopies n) q, ⟨ignoredPOVMCopies n, rfl⟩⟩

/-- The stated copy-decision construction satisfies `finitePOVMRisks_bddBelow` with the complete displayed premises. -/
lemma finitePOVMRisks_bddBelow (n : ℕ) (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    BddBelow (finitePOVMRisks n q) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨P, rfl⟩
  change 0 ≤ povmPolicyError P q
  rw [povmPolicyError_eq]
  exact policyError_nonneg P.toFinite q hq

/-- The stated copy-decision construction satisfies `finitePOVMOptimum_uniform_lower` with the complete displayed premises. -/
theorem finitePOVMOptimum_uniform_lower (n : ℕ) :
    (1/4:ℝ)^(n+1)/(1+(1/2:ℝ)^n) ≤ finitePOVMOptimum (n+1) (fun _ => 1/3) := by
  apply le_csInf (finitePOVMRisks_nonempty (n+1) (fun _ => 1/3))
  rintro _ ⟨P, rfl⟩
  exact finitePOVMPolicy_uniform_lower P

end Qatlib.Concepts.CopyDecision.FreshPolicies.Data
