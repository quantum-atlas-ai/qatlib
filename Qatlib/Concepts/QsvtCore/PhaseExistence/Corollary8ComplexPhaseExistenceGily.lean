/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary8ComplexPhaseExistenceStat
import Qatlib.Concepts.QsvtCore.PhaseExistence.ComplexPolynomial
set_option warningAsError false


open Qatlib.Concepts.QsvtCore.QsVtMain

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

private theorem complex_response_parity_unique (P : Polynomial ℂ) (hp : P ≠ 0)
    (n d : ℕ) (hn : HasResponseParity n P) (hd : HasResponseParity d P) :
    n % 2 = d % 2 := by
  have he : C ((-1 : ℂ) ^ n) * P = C ((-1 : ℂ) ^ d) * P := hn.symm.trans hd
  have hs : (-1 : ℂ) ^ n = (-1 : ℂ) ^ d := C_injective (mul_right_cancel₀ hp he)
  conv_lhs at hs => rw [neg_one_pow_eq_pow_mod_two]
  conv_rhs at hs => rw [neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1 <;>
    rcases Nat.mod_two_eq_zero_or_one d with hd0 | hd1
  · omega
  · norm_num [hn0, hd1] at hs
  · norm_num [hn1, hd0] at hs
  · omega

theorem corollary8ComplexPhaseExistence : Corollary8ComplexPhaseExistence := by
  intro P d hd hdeg hpar hin hout himag
  have hP0 : P ≠ 0 := by intro h; simp [h] at hdeg; omega
  have hdegree : P.degree ≤ (d : WithBot ℕ) := degree_le_of_natDegree_le hdeg.le
  obtain ⟨Q, hpair⟩ := exists_completedPair_of_cor8_conditions P d hdegree hpar hin hout himag
  obtain ⟨base, zs, hb, hzs, hlen, hP, _⟩ := exists_response_of_completedPair hpair
  obtain ⟨Φ, hΦlen, hΦ⟩ := source_phase_real_normal_form zs hzs
  have hΦd : Φ.length = d := hΦlen.trans hlen
  have hglobal : C base * sourcePhaseResponse Φ = P := by
    rw [hΦ, ← (source_response_global_phase base zs).1, hP]
  have hminimal : ∀ Ψ : List ℝ, sourcePhaseResponse Ψ = P →
      d ≤ Ψ.length ∧ Ψ.length % 2 = d % 2 := by
    intro Ψ hΨ
    have hdegΨ : (sourcePhaseResponse Ψ).natDegree ≤ Ψ.length := by
      simpa only [sourcePhaseResponse, List.length_map] using
          (response_degree 1 (Ψ.map anglePhase)).1
    have hparΨ : HasResponseParity Ψ.length (sourcePhaseResponse Ψ) := by
      have hp := completedPair_response (base := 1) (by simp [IsPhase]) (Ψ.map anglePhase)
        (by intro z hz; obtain ⟨φ, _, rfl⟩ := List.mem_map.mp hz; exact anglePhase_isPhase φ)
      simpa only [List.length_map, sourcePhaseResponse] using hp.parityP
    rw [hΨ, hdeg] at hdegΨ
    rw [hΨ] at hparΨ
    exact ⟨hdegΨ, complex_response_parity_unique P hP0 Ψ.length d hparΨ hpar⟩
  cases Φ with
  | nil => simp at hΦd; omega
  | cons φ Φ =>
    obtain ⟨θ, hθ⟩ := source_terminal_base_absorption base φ Φ hb
    exact ⟨θ :: Φ, by simpa using hΦd, hθ.trans hglobal, hminimal⟩

end Qatlib.Concepts.QsvtCore.PhaseExistence
