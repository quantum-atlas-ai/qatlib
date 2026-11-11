/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PolyApprox.MarkovLukacsNonnegative
import Qatlib.Concepts.QspSimulation.Achievability.RealPolynomial

/-!
# Completion of bounded real polynomials

This module completes a real polynomial bounded by one on `[-1, 1]`, with the required degree
and parity, into a complex QSP polynomial pair. Nonnegativity of `squareResidual` supplies the
completion, and phase synthesis produces a response whose real part equals the given polynomial
on every real input. The mathematical background is developed in [GilyenSuLowWiebe2019].

## Main statements

* `exists_completedPair_of_bounded`: completion with the prescribed real part.
* `exists_phases_of_bounded`: a unit phase sequence of the prescribed length realizing that real
  part.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false


open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QsvtCore.PolyApprox

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Polynomial Qatlib.Concepts.QsvtCore.PolyApprox
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

/-- A real polynomial of the stated parity bounded by one on `[-1, 1]` has nonnegative square
residual on `[0, 1]`. -/
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

/-- A real polynomial of degree at most `d`, parity `d`, and absolute value at most one on `[-1,
1]` extends to a completed complex pair whose first polynomial has that real part on the
real axis. -/
theorem exists_completedPair_of_bounded {p : Polynomial ℝ} {d : ℕ}
    (hpdeg : p.degree ≤ (d : WithBot ℕ)) (hp : HasRealParity d p)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∃ P Q : Polynomial ℂ, CompletedPair d P Q ∧
      P + conjugatePolynomial P = C (2 : ℂ) * p.map Complex.ofRealHom ∧
      ∀ x : ℝ, (P.eval (x : ℂ)).re = p.eval x := by
  obtain ⟨rep⟩ := Qatlib.Concepts.QsvtCore.PolyApprox.exists_rep_of_nonneg (squareResidual p)
    (squareResidual_nonneg hp hb) (squareResidual_degree_le hpdeg)
  exact exists_completedPair_of_rep hpdeg hp rep

/-- A real polynomial of degree at most `d`, parity `d`, and absolute value at most one on `[-1,
1]` is the real part of a unit phase response with list length `d`; see [Gilyén et al.,
Corollary 18][GilyenSuLowWiebe2019]. -/
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
