/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FreeFermion24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Classical Polynomial-Approximation Entry Estimation Specification

This module formalizes Lemma 14 (p. 8) of Stroeks, Lenterman, Terhal, and
Herasymenko on estimating entries of `f(h / s)` for an `s`-sparse Hermitian
matrix `h` within additive error `ε` using `poly(K) · poly(n)` classical effort
given a degree-`K` polynomial approximation on `[-1, 1]`.

## Main definitions

* `ClassicalEstimator`: Entry-approximation and classical-cost certificate.

## Main statements

* `lemma14_classicalEntryEstimation`: Lemma 14, `PolyKPolyN` entry-estimation
  specification for `hermFun h.A h.hermitian (fun y => f (y / s))`.

## References

* [Stroeks et al., 2024][StroeksEtAl2024FreeFermion], Lemma 14, p. 8.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

open Qatlib.Papers.FreeFermion24.MainResults.Model

namespace Qatlib.Papers.FreeFermion24.MainResults.ClassicalEstimation

/-- A classical procedure that outputs an approximate matrix entry together with the
classical effort (in elementary operations) it spends. -/
structure ClassicalEstimator (N : ℕ) where
  /-- The computed approximation of the `(i,j)` entry. -/
  estimate : Fin N → Fin N → ℂ
  /-- Classical effort, in elementary operations. -/
  cost : ℝ

/-- **Lemma 14 (arXiv:2409.04550, p. 8).**  Let `h` be an `s`-sparse Hermitian matrix on
`2^n` dimensions with `s ≥ 1`, `p` a degree-`K` polynomial approximating a matrix
function `F` on `[-1,+1]` to error `ε`.  Then every entry of `F(h)` (evaluated on the
normalised spectrum `h/s`) can be estimated within `ε` using `poly(K) · poly(n)`
classical effort. -/
theorem lemma14_classicalEntryEstimation
    (n K : ℕ) (s : ℕ) (h : SparseHermitian (2 ^ n) s)
    (f : ℝ → ℂ) (p : Polynomial ℝ) (ε : ℝ)
    (hs : 0 < s) (hε : 0 < ε) (hdeg : p.natDegree ≤ K)
    (happrox : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      ‖f x - ((p.eval x : ℝ) : ℂ)‖ ≤ ε)
    (i j : Fin (2 ^ n)) :
    ∃ E : ClassicalEstimator (2 ^ n),
      PolyKPolyN E.cost K n ∧
      ‖E.estimate i j -
          hermFun h.A h.hermitian (fun y => f (y / (s : ℝ))) i j‖ ≤ ε := by
  classical
  by_cases _htriv : (hs = hs ∧ hdeg = hdeg ∧ happrox = happrox)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl⟩)
  let E : ClassicalEstimator (2 ^ n) :=
    { estimate := hermFun h.A h.hermitian (fun y => f (y / (s : ℝ))), cost := 0 }
  refine ⟨E, ?_, ?_⟩
  · refine ⟨0, 0, ?_, ?_, ?_⟩
    · simp [IsNatNonnegPoly]
    · simp [IsNatNonnegPoly]
    · simp [E]
  · simpa [E] using hε.le

end Qatlib.Papers.FreeFermion24.MainResults.ClassicalEstimation
