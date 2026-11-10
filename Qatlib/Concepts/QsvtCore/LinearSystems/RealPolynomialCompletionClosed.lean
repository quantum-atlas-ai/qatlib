/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PolyApprox.MarkovLukacsNonnegative
import Qatlib.Concepts.QspSimulation.Achievability.RealPolynomial
set_option warningAsError false


open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QsvtCore.PolyApprox

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Polynomial Qatlib.Concepts.QsvtCore.PolyApprox
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

theorem squareResidual_nonneg {p : Polynomial ℝ} {d : ℕ}
    (hp : HasRealParity d p)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (squareResidual p).eval t := by
  intro t ht
  have hs0 := Real.sqrt_nonneg t
  have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht.2
  have hs := hb (Real.sqrt t) ⟨by linarith, hs1⟩
  have he := congrArg (Polynomial.eval (Real.sqrt t)) (squareResidual_comp hp)
  simp only [eval_comp, eval_pow, eval_X, Real.sq_sqrt ht.1, eval_sub, eval_one] at he
  rw [he]
  rcases abs_le.mp hs with ⟨hlo, hhi⟩
  nlinarith

theorem exists_completedPair_of_bounded {p : Polynomial ℝ} {d : ℕ}
    (hpdeg : p.degree ≤ (d : WithBot ℕ)) (hp : HasRealParity d p)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∃ P Q : Polynomial ℂ, CompletedPair d P Q ∧
      P + conjugatePolynomial P = C (2 : ℂ) * p.map Complex.ofRealHom ∧
      ∀ x : ℝ, (P.eval (x : ℂ)).re = p.eval x := by
  obtain ⟨rep⟩ := Qatlib.Concepts.QsvtCore.PolyApprox.exists_rep_of_nonneg (squareResidual p)
    (squareResidual_nonneg hp hb) (squareResidual_degree_le hpdeg)
  exact exists_completedPair_of_rep hpdeg hp rep

theorem exists_phases_of_bounded {p : Polynomial ℝ} {d : ℕ}
    (hpdeg : p.degree ≤ (d : WithBot ℕ)) (hp : HasRealParity d p)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∃ (base : ℂ) (zs : List ℂ), IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧
      zs.length = d ∧
      responseP base zs + conjugatePolynomial (responseP base zs) =
        C (2 : ℂ) * p.map Complex.ofRealHom ∧
      ∀ x : ℝ, ((responseP base zs).eval (x : ℂ)).re = p.eval x := by
  obtain ⟨P, Q, hpair, hpoly, hre⟩ := exists_completedPair_of_bounded hpdeg hp hb
  obtain ⟨base, zs, hbase, hzs, hn, hP, _⟩ := exists_response_of_completedPair hpair
  exact ⟨base, zs, hbase, hzs, hn, by simpa only [hP] using hpoly,
    by simpa only [hP] using hre⟩

end Qatlib.Concepts.QsvtCore.LinearSystems
