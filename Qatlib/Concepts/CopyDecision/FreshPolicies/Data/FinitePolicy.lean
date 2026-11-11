/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.QubitMeasure.Data.TrineCopies

/-!
# Finite Policy

Fresh Policies constructions for Copy Decision.
Defines `Qubit`, `TerminalDecision`, `FinitePolicy`.
Proves `decisionImage_inner_step`, `decisionImage_inner_leaf`, `decisionImage_normSq_leaf`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.FreshPolicies.Data
open Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError

/-- Abbreviation for Qubit in the Fresh Policies construction. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- Randomized classical terminal decision, independent of the unknown label. -/
structure TerminalDecision where
  prob : Fin 3 → ℝ
  nonneg : ∀ k, 0 ≤ prob k
  total : ∑ k, prob k=1

/-- A fixed-copy adaptive tree. Only the classical outcome indexes the next
policy: the measured qubit's quantum output is not passed to the continuation.
The canonical square qubit Kraus representation will require a separate bridge
from arbitrary finite POVMs before claiming full model coverage. -/
inductive FinitePolicy : ℕ → Type where
  | leaf (p : TerminalDecision) : FinitePolicy 0
  | step {n : ℕ} (m : ℕ) (A : Fin m → Qubit →ₗ[ℂ] Qubit)
      (mass : ∀ x, ∑ a, ‖A a x‖^2=‖x‖^2)
      (gram : ∀ x y, ∑ a, inner ℂ (A a x) (A a y)=inner ℂ x y)
      (next : Fin m → FinitePolicy n) : FinitePolicy (n+1)

/-- Actual weighted Born recursion for this same decision tree. -/
def policyError : {n : ℕ} → FinitePolicy n → (Fin 3 → ℝ) → ℝ
  | _, .leaf p, q => ∑ i, q i*(1-p.prob i)
  | _, .step _ A _ _ next, q =>
      ∑ a, policyError (next a) (fun i => q i*‖A a (trineState i)‖^2)

/-- Record environment contains the classical outcome, discarded quantum output
coordinate and the child environment; no register records the input label. -/
def PolicyEnv : {n : ℕ} → FinitePolicy n → Type
  | _, .leaf _ => Unit
  | _, .step m _ _ _ next => (a : Fin m) × (Fin 2 × PolicyEnv (next a))

/-- Typeclass instance for policy Env Fintype in the Fresh Policies construction. -/
instance policyEnvFintype : {n : ℕ} → (P : FinitePolicy n) → Fintype (PolicyEnv P)
  | _, .leaf _ => inferInstanceAs (Fintype Unit)
  | _, .step m _ _ _ next =>
      letI : (a : Fin m) → Fintype (PolicyEnv (next a)) := fun a => policyEnvFintype (next a)
      inferInstanceAs (Fintype ((a : Fin m) × (Fin 2 × PolicyEnv (next a))))

/-- Coherent record amplitude in one final-decision sector. -/
def decisionImage : {n : ℕ} → (P : FinitePolicy n) → Fin 3 → Fin 3 →
    EuclideanSpace ℂ (PolicyEnv P)
  | _, .leaf p, k, _ => WithLp.toLp 2 fun _ => (Real.sqrt (p.prob k) : ℂ)
  | _, .step _ A _ _ next, k, i => WithLp.toLp 2 fun e =>
      (A e.1 (trineState i)) e.2.1 * decisionImage (next e.1) k i e.2.2

/-- Direct inner product of two recursively constructed record amplitudes. -/
lemma decisionImage_inner_step {n m : ℕ} (A : Fin m → Qubit →ₗ[ℂ] Qubit)
    (mass : ∀ x, ∑ a, ‖A a x‖^2=‖x‖^2)
    (gram : ∀ x y, ∑ a, inner ℂ (A a x) (A a y)=inner ℂ x y)
    (next : Fin m → FinitePolicy n) (k i j : Fin 3) :
    inner ℂ (decisionImage (.step m A mass gram next) k i)
      (decisionImage (.step m A mass gram next) k j) =
      ∑ a, inner ℂ (A a (trineState i)) (A a (trineState j)) *
        inner ℂ (decisionImage (next a) k i) (decisionImage (next a) k j) := by
  change (∑ e : (a : Fin m) × (Fin 2 × PolicyEnv (next a)),
    ((A e.1 (trineState j)) e.2.1 * decisionImage (next e.1) k j e.2.2) *
      star ((A e.1 (trineState i)) e.2.1 * decisionImage (next e.1) k i e.2.2)) =
    ∑ a, (∑ c, (A a (trineState j)) c*star ((A a (trineState i)) c)) *
      (∑ b, decisionImage (next a) k j b*star (decisionImage (next a) k i b))
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, Fintype.sum_mul_sum, star_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The stated copy-decision construction satisfies `decisionImage_inner_leaf` with the complete displayed premises. -/
lemma decisionImage_inner_leaf (p : TerminalDecision) (k i j : Fin 3) :
    inner ℂ (decisionImage (.leaf p) k i) (decisionImage (.leaf p) k j) = (p.prob k : ℂ) := by
  change (∑ _ : Unit, (Real.sqrt (p.prob k) : ℂ)*star (Real.sqrt (p.prob k) : ℂ)) = _
  simp only [Fintype.sum_unique]
  rw [show star (Real.sqrt (p.prob k) : ℂ) = (Real.sqrt (p.prob k) : ℂ) from
    Complex.conj_ofReal _]
  rw [←pow_two, ←Complex.ofReal_pow, Real.sq_sqrt (p.nonneg k)]

/-- The stated copy-decision construction satisfies `decisionImage_normSq_leaf` with the complete displayed premises. -/
lemma decisionImage_normSq_leaf (p : TerminalDecision) (k i : Fin 3) :
    ‖decisionImage (.leaf p) k i‖^2=p.prob k := by
  have h := decisionImage_inner_leaf p k i i
  rw [inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

/-- The stated copy-decision construction satisfies `decisionImage_normSq_step` with the complete displayed premises. -/
lemma decisionImage_normSq_step {n m : ℕ} (A : Fin m → Qubit →ₗ[ℂ] Qubit)
    (mass : ∀ x, ∑ a, ‖A a x‖^2=‖x‖^2)
    (gram : ∀ x y, ∑ a, inner ℂ (A a x) (A a y)=inner ℂ x y)
    (next : Fin m → FinitePolicy n) (k i : Fin 3) :
    ‖decisionImage (.step m A mass gram next) k i‖^2 =
      ∑ a, ‖A a (trineState i)‖^2 * ‖decisionImage (next a) k i‖^2 := by
  have h := decisionImage_inner_step A mass gram next k i i
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- The sum over decision sectors preserves the actual n-copy Gram. -/
theorem decisionImage_gram {n : ℕ} (P : FinitePolicy n) (i j : Fin 3) :
    ∑ k, inner ℂ (decisionImage P k i) (decisionImage P k j) =
      (inner ℂ (trineState i) (trineState j))^n := by
  induction P with
  | leaf p =>
    simp only [decisionImage_inner_leaf,pow_zero]
    exact_mod_cast p.total
  | @step n m A mass gram next ih =>
    simp only [decisionImage_inner_step]
    rw [Finset.sum_comm]
    simp_rw [←Finset.mul_sum,ih]
    rw [←Finset.sum_mul,gram,pow_succ]
    ring

/-- The stated copy-decision construction satisfies `decisionImage_mass` with the complete displayed premises. -/
lemma decisionImage_mass {n : ℕ} (P : FinitePolicy n) (i : Fin 3) :
    ∑ k, ‖decisionImage P k i‖^2=1 := by
  have h := decisionImage_gram P i i
  rw [trineState_gram,if_pos rfl,one_pow] at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

/-- The stated copy-decision construction satisfies `decisionImage_correct_le_one` with the complete displayed premises. -/
lemma decisionImage_correct_le_one {n : ℕ} (P : FinitePolicy n) (i : Fin 3) :
    ‖decisionImage P i i‖ ≤ 1 := by
  have hm := decisionImage_mass P i
  have hs : ‖decisionImage P i i‖^2 ≤ ∑ k, ‖decisionImage P k i‖^2 :=
    Finset.single_le_sum (f := fun k : Fin 3 => ‖decisionImage P k i‖^2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [norm_nonneg (decisionImage P i i)]

/-- Error equality for the SAME tree, including classical randomized leaves. -/
theorem policyError_eq_decisionError {n : ℕ} (P : FinitePolicy n) (q : Fin 3 → ℝ) :
    policyError P q=decisionError (decisionImage P) q := by
  induction P generalizing q with
  | leaf p =>
    simp only [policyError,decisionError,decisionImage_normSq_leaf,Fin.sum_univ_three]
    have hs := p.total
    rw [Fin.sum_univ_three] at hs
    simp only [←hs]
    ring
  | step m A mass gram next ih =>
    simp only [policyError]
    simp_rw [ih]
    simp only [decisionError,decisionImage_normSq_step]
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring

/-- The record environment preserves the SAME full tensor-copy state's Gram. -/
theorem decisionImage_copy_gram {n : ℕ} (P : FinitePolicy n) (i j : Fin 3) :
    ∑ k, inner ℂ (decisionImage P k i) (decisionImage P k j) =
      inner ℂ (copyState n (trineState i)) (copyState n (trineState j)) := by
  rw [decisionImage_gram,copyState_inner]

/-- The stated copy-decision construction satisfies `decisionImage_overlap` with the complete displayed premises. -/
lemma decisionImage_overlap {n : ℕ} (P : FinitePolicy n) (i j : Fin 3) (hij : i≠j) :
    ‖∑ k, inner ℂ (decisionImage P k i) (decisionImage P k j)‖=(1/2:ℝ)^n := by
  rw [decisionImage_copy_gram]
  exact trine_copies_overlap n i j hij

/-- A lower bound derived from the actual tree amplitudes and actual Born error,
for arbitrary nonnegative, possibly unnormalized branch weights. -/
theorem policy_weighted_bound {n : ℕ} (P : FinitePolicy n) (q : Fin 3 → ℝ)
    (hq : ∀ i, 0 ≤ q i) :
    ((1/2:ℝ)^n)^2*(pairWeight (q 0) (q 1)+pairWeight (q 0) (q 2)+pairWeight (q 1) (q 2)) ≤
      (1+(1/2:ℝ)^n)*policyError P q := by
  rw [policyError_eq_decisionError]
  apply three_decision_error (decisionImage P) q hq (by positivity) (decisionImage_correct_le_one P)
  · simpa only [Fin.sum_univ_three] using decisionImage_overlap P 0 1 (by decide)
  · simpa only [Fin.sum_univ_three,add_comm,add_left_comm,add_assoc] using
      decisionImage_overlap P 0 2 (by decide)
  · simpa only [Fin.sum_univ_three,add_comm,add_left_comm,add_assoc] using
      decisionImage_overlap P 1 2 (by decide)

/-- The stated copy-decision construction satisfies `policyError_nonneg` with the complete displayed premises. -/
lemma policyError_nonneg {n : ℕ} (P : FinitePolicy n) (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    0 ≤ policyError P q := by
  rw [policyError_eq_decisionError]
  have h0 := hq 0
  have h1 := hq 1
  have h2 := hq 2
  unfold decisionError
  positivity

end Qatlib.Concepts.CopyDecision.FreshPolicies.Data
