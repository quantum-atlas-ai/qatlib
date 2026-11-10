/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Module.Basic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GroupReps08.MainResults.AlternatingGroup

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

abbrev Pairing := V →ₗ[ℂ] V →ₗ[ℂ] ℂ

def alternatingEvenEntry (B : Pairing (V := V)) (X : V →ₗ[ℂ] V)
    (Λ Λhat Γ Γhat : V) : ℂ :=
  (1 / 2 : ℂ) * B (Λ + Λhat) (X (Γ + Γhat))

def alternatingOddEntry (B : Pairing (V := V)) (X : V →ₗ[ℂ] V)
    (Λ Λhat Γ Γhat : V) : ℂ :=
  (1 / 2 : ℂ) * B (Λ + Complex.I • Λhat) (X (Γ + Complex.I • Γhat))

theorem alternatingEvenEntry_expansion (B : Pairing (V := V)) (X : V →ₗ[ℂ] V)
    (Λ Λhat Γ Γhat : V) :
    alternatingEvenEntry B X Λ Λhat Γ Γhat
      = (1 / 2 : ℂ) * (B Λ (X Γ) + B Λ (X Γhat) + B Λhat (X Γ) + B Λhat (X Γhat)) := by
  simp only [alternatingEvenEntry, map_add, LinearMap.add_apply]
  ring

theorem alternatingOddEntry_expansion (B : Pairing (V := V)) (X : V →ₗ[ℂ] V)
    (Λ Λhat Γ Γhat : V) :
    alternatingOddEntry B X Λ Λhat Γ Γhat
      = (1 / 2 : ℂ) *
          (B Λ (X Γ) + Complex.I * B Λ (X Γhat)
            + Complex.I * B Λhat (X Γ) - B Λhat (X Γhat)) := by
  simp only [alternatingOddEntry, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_add, smul_smul, Complex.I_mul_I]
  ring

theorem alternating_entry_error_stability (a b c d ea eb ec ed : ℂ) (η : ℝ)
    (h1 : ‖ea - a‖ ≤ η) (h2 : ‖eb - b‖ ≤ η)
    (h3 : ‖ec - c‖ ≤ η) (h4 : ‖ed - d‖ ≤ η) :
    ‖(1 / 2 : ℂ) * (ea + eb + ec + ed) - (1 / 2 : ℂ) * (a + b + c + d)‖ ≤ 2 * η := by
  have hfac : (1 / 2 : ℂ) * (ea + eb + ec + ed) - (1 / 2 : ℂ) * (a + b + c + d)
      = (1 / 2 : ℂ) * ((ea - a) + (eb - b) + (ec - c) + (ed - d)) := by ring
  rw [hfac, norm_mul]
  have hcoef : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hcoef]
  have htri : ‖(ea - a) + (eb - b) + (ec - c) + (ed - d)‖ ≤ η + η + η + η := by
    calc ‖(ea - a) + (eb - b) + (ec - c) + (ed - d)‖
        ≤ ‖(ea - a) + (eb - b) + (ec - c)‖ + ‖ed - d‖ := norm_add_le _ _
      _ ≤ (‖(ea - a) + (eb - b)‖ + ‖ec - c‖) + ‖ed - d‖ := by
            gcongr; exact norm_add_le _ _
      _ ≤ ((‖ea - a‖ + ‖eb - b‖) + ‖ec - c‖) + ‖ed - d‖ := by
            gcongr; exact norm_add_le _ _
      _ ≤ η + η + η + η := by gcongr
  nlinarith [htri, h1, h2, h3, h4]

theorem alternating_entry_error_eps (a b c d ea eb ec ed : ℂ) (ε : ℝ) (hε : 0 < ε)
    (h1 : ‖ea - a‖ ≤ ε / 4) (h2 : ‖eb - b‖ ≤ ε / 4)
    (h3 : ‖ec - c‖ ≤ ε / 4) (h4 : ‖ed - d‖ ≤ ε / 4) :
    ‖(1 / 2 : ℂ) * (ea + eb + ec + ed) - (1 / 2 : ℂ) * (a + b + c + d)‖ ≤ ε := by
  have h := alternating_entry_error_stability a b c d ea eb ec ed (ε / 4) h1 h2 h3 h4
  linarith

end Qatlib.Papers.GroupReps08.MainResults.AlternatingGroup
