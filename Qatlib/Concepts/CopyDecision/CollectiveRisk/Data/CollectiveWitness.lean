/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.CollectiveRisk.Data.CollectivePOVM

/-!
# Collective Witness

Collective Risk constructions for Copy Decision.
Defines `trineSignedOverlap`, `trineCollectiveVector`, `trineCollectivePOVM`.
Proves `trine_copies_gram`, `trineSignedOverlap_abs`, `trineSignedOverlap_valid`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.CollectiveRisk.Data
open Qatlib.Concepts.CopyDecision.FreshPolicies.Data Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError

/-- Definition of trine Signed Overlap in the Collective Risk construction. -/
def trineSignedOverlap (N : ℕ) : ℝ := (-1/2:ℝ)^N

/-- The stated copy-decision construction satisfies `trine_copies_gram` with the complete displayed premises. -/
lemma trine_copies_gram (N : ℕ) (i j : Fin 3) :
    inner ℂ (copyState N (trineState i)) (copyState N (trineState j))=
      ((if i=j then 1 else trineSignedOverlap N:ℝ):ℂ) := by
  rw [copyState_inner, trineState_gram]
  by_cases h : i=j
  · simp [h]
  · simp only [h, ite_false, trineSignedOverlap]
    push_cast
    rfl

/-- The stated copy-decision construction satisfies `trineSignedOverlap_abs` with the complete displayed premises. -/
lemma trineSignedOverlap_abs (n : ℕ) : |trineSignedOverlap (n+2)| ≤ 1/4 := by
  have he : |trineSignedOverlap (n+2)|=(1/2:ℝ)^n*(1/4) := by
    have ha : |(-1/2:ℝ)|=1/2 := by norm_num
    rw [trineSignedOverlap, abs_pow, ha, pow_add]
    norm_num
  rw [he]
  have h : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

/-- The stated copy-decision construction satisfies `trineSignedOverlap_valid` with the complete displayed premises. -/
lemma trineSignedOverlap_valid (n : ℕ) :
    0 < 1-trineSignedOverlap (n+2) ∧ 0 < 1+2*trineSignedOverlap (n+2) := by
  have h := abs_le.mp (trineSignedOverlap_abs n)
  constructor <;> linarith [h.1, h.2]

/-- Definition of trine Collective Vector in the Collective Risk construction. -/
def trineCollectiveVector (n : ℕ) (i : Fin 3) : EuclideanSpace ℂ (Fin (n+2) → Fin 2) :=
  collectiveOrtho (fun j => copyState (n+2) (trineState j)) (trineSignedOverlap (n+2)) i

/-- The stated copy-decision construction satisfies `trineCollectiveVector_gram` with the complete displayed premises. -/
lemma trineCollectiveVector_gram (n : ℕ) (i j : Fin 3) :
    inner ℂ (trineCollectiveVector n i) (trineCollectiveVector n j)=if i=j then 1 else 0 :=
  collectiveOrtho_gram _ _ (trine_copies_gram (n+2))
    (trineSignedOverlap_valid n).1 (trineSignedOverlap_valid n).2 i j

/-- The stated copy-decision construction satisfies `trineCollectiveVector_overlap` with the complete displayed premises. -/
lemma trineCollectiveVector_overlap (n : ℕ) (i j : Fin 3) :
    inner ℂ (trineCollectiveVector n i) (copyState (n+2) (trineState j))=
      ((if i=j then collectiveAlpha (trineSignedOverlap (n+2)) else
        collectiveBeta (trineSignedOverlap (n+2)):ℝ):ℂ) :=
  collectiveOrtho_overlap _ _ (trine_copies_gram (n+2))
    (trineSignedOverlap_valid n).1 (trineSignedOverlap_valid n).2 i j

/-- A complete three-decision projective measurement on the FULL 2^(n+2)
source register. Decision zero retains the entire unused orthogonal complement. -/
def trineCollectivePOVM (n : ℕ) : POVM (Fin 3) (Fin (n+2) → Fin 2) :=
  orthogonalPairPOVM (trineCollectiveVector n 1) (trineCollectiveVector n 2)
    (by rw [trineCollectiveVector_gram, if_pos rfl])
    (by rw [trineCollectiveVector_gram, if_pos rfl])
    (by rw [trineCollectiveVector_gram, if_neg (by decide)])

/-- The stated copy-decision construction satisfies `trineCollectivePOVM_error` with the complete displayed premises. -/
theorem trineCollectivePOVM_error (n : ℕ) :
    jointError (trineCollectivePOVM n) (fun _ => (1:ℝ)/3)=
      2*(collectiveBeta (trineSignedOverlap (n+2)))^2 := by
  have hB (i j : Fin 3) :
      jointBorn (fullPureEffect (trineCollectiveVector n i)) (copyState (n+2) (trineState j))=
        (if i=j then collectiveAlpha (trineSignedOverlap (n+2)) else
          collectiveBeta (trineSignedOverlap (n+2)))^2 :=
    jointBorn_pure _ _ _ (trineCollectiveVector_overlap n i j)
  have hnorm := trine_copies_unit (n+2) (0:Fin 3)
  have hc := collectiveAlphaBeta (trineSignedOverlap (n+2))
    (trineSignedOverlap_valid n).1 (trineSignedOverlap_valid n).2
  unfold jointError trineCollectivePOVM orthogonalPairPOVM
  simp only [Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  rw [jointBorn_complement, hnorm, hB, hB, hB, hB]
  norm_num [Fin.ext_iff]
  nlinarith only [hc]

/-- The stated copy-decision construction satisfies `collectiveBeta_rational` with the complete displayed premises. -/
lemma collectiveBeta_rational (s : ℝ) (hm : 0 < 1-s) (hp : 0 < 1+2*s) :
    collectiveBeta s=s/(Real.sqrt (1+2*s)+Real.sqrt (1-s)) := by
  have hden : Real.sqrt (1+2*s)+Real.sqrt (1-s) ≠ 0 := by positivity
  have hu := Real.sq_sqrt (le_of_lt hm)
  have hv := Real.sq_sqrt (le_of_lt hp)
  unfold collectiveBeta
  apply (eq_div_iff hden).2
  nlinarith only [hu, hv]

/-- The stated copy-decision construction satisfies `trineCollectivePOVM_error_rational` with the complete displayed premises. -/
theorem trineCollectivePOVM_error_rational (n : ℕ) :
    jointError (trineCollectivePOVM n) (fun _ => (1:ℝ)/3)=
      2*(trineSignedOverlap (n+2))^2/
        (Real.sqrt (1+2*trineSignedOverlap (n+2))+Real.sqrt (1-trineSignedOverlap (n+2)))^2 := by
  rw [trineCollectivePOVM_error, collectiveBeta_rational _
    (trineSignedOverlap_valid n).1 (trineSignedOverlap_valid n).2]
  rw [div_pow, mul_div_assoc]

end Qatlib.Concepts.CopyDecision.CollectiveRisk.Data
