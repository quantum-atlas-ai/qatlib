/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.QubitMeasure.Data.BinaryLikelihood

/-!
# Binary Posterior

Qubit Measure constructions for Copy Decision.
Defines `binaryPosteriorP`, `binaryPosteriorQ`, `binaryBranchMass`.
Proves `binaryPosterior_nonneg`, `binaryBranchMass_plus`, `binaryPosterior_diff_plus`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.QubitMeasure.Data
open Qatlib.Concepts.CopyDecision.FreshPolicies.Data Qatlib.Foundations.DecisionRisk.HarmonicError

/-- Definition of binary Posterior P in the Qubit Measure construction. -/
def binaryPosteriorP (i j : Fin 3) (hij : i≠j) (p q : ℝ) (hQ : 0 < p+q) (a : Fin 2) : ℝ :=
  p*qubitBorn ((binaryPOVM i j hij p q hQ).mats a) (trineState i)

/-- Definition of binary Posterior Q in the Qubit Measure construction. -/
def binaryPosteriorQ (i j : Fin 3) (hij : i≠j) (p q : ℝ) (hQ : 0 < p+q) (a : Fin 2) : ℝ :=
  q*qubitBorn ((binaryPOVM i j hij p q hQ).mats a) (trineState j)

/-- Definition of binary Branch Mass in the Qubit Measure construction. -/
def binaryBranchMass (i j : Fin 3) (hij : i≠j) (p q : ℝ) (hQ : 0 < p+q) (a : Fin 2) : ℝ :=
  binaryPosteriorP i j hij p q hQ a+binaryPosteriorQ i j hij p q hQ a

/-- The stated copy-decision construction satisfies `binaryPosterior_nonneg` with the complete displayed premises. -/
lemma binaryPosterior_nonneg (i j : Fin 3) (hij : i≠j) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hQ : 0 < p+q) (a : Fin 2) :
    0 ≤ binaryPosteriorP i j hij p q hQ a ∧ 0 ≤ binaryPosteriorQ i j hij p q hQ a := by
  exact ⟨mul_nonneg hp (qubitBorn_nonneg _ ((binaryPOVM i j hij p q hQ).nonneg a) _),
    mul_nonneg hq (qubitBorn_nonneg _ ((binaryPOVM i j hij p q hQ).nonneg a) _)⟩

/-- The stated copy-decision construction satisfies `binaryBranchMass_plus` with the complete displayed premises. -/
lemma binaryBranchMass_plus (i j : Fin 3) (hij : i≠j) (p q : ℝ) (hQ : 0 < p+q) :
    binaryBranchMass i j hij p q hQ 0=
      (p+q)*(binaryDisc p q+(p-q))/(2*binaryDisc p q) := by
  unfold binaryBranchMass binaryPosteriorP binaryPosteriorQ
  rw [(binaryPOVM_born_plus i j hij p q hQ).1, (binaryPOVM_born_plus i j hij p q hQ).2]
  field_simp [ne_of_gt (binaryDisc_pos hQ)]
  ring

/-- The stated copy-decision construction satisfies `binaryPosterior_diff_plus` with the complete displayed premises. -/
lemma binaryPosterior_diff_plus (i j : Fin 3) (hij : i≠j) (p q : ℝ) (hQ : 0 < p+q) :
    binaryPosteriorP i j hij p q hQ 0-binaryPosteriorQ i j hij p q hQ 0=
      (binaryDisc p q+(p-q))/2 := by
  unfold binaryPosteriorP binaryPosteriorQ
  rw [(binaryPOVM_born_plus i j hij p q hQ).1, (binaryPOVM_born_plus i j hij p q hQ).2]
  have hs := binaryDisc_sq p q
  field_simp [ne_of_gt (binaryDisc_pos hQ)]
  nlinarith only [hs]

/-- The stated copy-decision construction satisfies `binaryBranchMass_minus` with the complete displayed premises. -/
lemma binaryBranchMass_minus (i j : Fin 3) (hij : i≠j) (p q : ℝ) (hQ : 0 < p+q) :
    binaryBranchMass i j hij p q hQ 1=(p+q)-binaryBranchMass i j hij p q hQ 0 := by
  unfold binaryBranchMass binaryPosteriorP binaryPosteriorQ
  rw [binaryPOVM_born_minus i j hij p q hQ i, binaryPOVM_born_minus i j hij p q hQ j]
  ring

/-- The stated copy-decision construction satisfies `binaryPosterior_diff_minus` with the complete displayed premises. -/
lemma binaryPosterior_diff_minus (i j : Fin 3) (hij : i≠j) (p q : ℝ) (hQ : 0 < p+q) :
    binaryPosteriorP i j hij p q hQ 1-binaryPosteriorQ i j hij p q hQ 1=
      (p-q)-(binaryPosteriorP i j hij p q hQ 0-binaryPosteriorQ i j hij p q hQ 0) := by
  unfold binaryPosteriorP binaryPosteriorQ
  rw [binaryPOVM_born_minus i j hij p q hQ i, binaryPOVM_born_minus i j hij p q hQ j]
  ring

/-- The stated copy-decision construction satisfies `binaryPosterior_difference` with the complete displayed premises. -/
lemma binaryPosterior_difference (i j : Fin 3) (hij : i≠j) (p q : ℝ) (hQ : 0 < p+q) (a : Fin 2) :
    (p+q)*(binaryPosteriorP i j hij p q hQ a-binaryPosteriorQ i j hij p q hQ a)=
      (if a=0 then 1 else -1)*binaryDisc p q*binaryBranchMass i j hij p q hQ a := by
  fin_cases a
  · change (p+q)*(binaryPosteriorP i j hij p q hQ 0-binaryPosteriorQ i j hij p q hQ 0)=
      1*binaryDisc p q*binaryBranchMass i j hij p q hQ 0
    rw [binaryPosterior_diff_plus i j hij p q hQ, binaryBranchMass_plus]
    field_simp [ne_of_gt (binaryDisc_pos hQ)]
  · change (p+q)*(binaryPosteriorP i j hij p q hQ 1-binaryPosteriorQ i j hij p q hQ 1)=
      (-1)*binaryDisc p q*binaryBranchMass i j hij p q hQ 1
    rw [binaryPosterior_diff_minus i j hij p q hQ, binaryBranchMass_minus,
      binaryPosterior_diff_plus, binaryBranchMass_plus]
    field_simp [ne_of_gt (binaryDisc_pos hQ)]
    all_goals ring

/-- Division-free posterior-product invariant, valid even when the branch has
zero probability. Every posterior weight is an actual same-step Born mass. -/
theorem binaryPosterior_product (i j : Fin 3) (hij : i≠j) (p q : ℝ) (hQ : 0 < p+q) (a : Fin 2) :
    4*(p+q)^2*binaryPosteriorP i j hij p q hQ a*binaryPosteriorQ i j hij p q hQ a=
      p*q*(binaryBranchMass i j hij p q hQ a)^2 := by
  have hd := binaryPosterior_difference i j hij p q hQ a
  have hs : ((p+q)*(binaryPosteriorP i j hij p q hQ a-binaryPosteriorQ i j hij p q hQ a))^2=
      (binaryDisc p q)^2*(binaryBranchMass i j hij p q hQ a)^2 := by
    rw [hd]
    split_ifs <;> ring
  calc
    _ = (p+q)^2*(binaryBranchMass i j hij p q hQ a)^2-
        ((p+q)*(binaryPosteriorP i j hij p q hQ a-binaryPosteriorQ i j hij p q hQ a))^2 := by
      unfold binaryBranchMass
      ring
    _ = ((p+q)^2-(binaryDisc p q)^2)*(binaryBranchMass i j hij p q hQ a)^2 := by rw [hs]; ring
    _ = p*q*(binaryBranchMass i j hij p q hQ a)^2 := by rw [binaryDisc_sq]; ring

/-- The stated copy-decision construction satisfies `binaryPosterior_total` with the complete displayed premises. -/
lemma binaryPosterior_total (i j : Fin 3) (hij : i≠j) (p q : ℝ) (hQ : 0 < p+q) :
    ∑ a, binaryBranchMass i j hij p q hQ a=p+q := by
  rw [Fin.sum_univ_two, binaryBranchMass_minus]
  ring

end Qatlib.Concepts.CopyDecision.QubitMeasure.Data
