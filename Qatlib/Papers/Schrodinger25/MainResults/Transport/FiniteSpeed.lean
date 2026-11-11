/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Schrodinger25.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Schrodinger25 — finite propagation speed and exact recovery (Lemma 5.1, Theorem 5.1)

Fixed paper version: arXiv:2505.00370.  Source statements:

* Lemma 5.1, p. 26: the solution of
  `∂_t ω = −H₁ ∂_p ω + i H₂ ω` with initial data vanishing on `[p*, R]`
  satisfies `ω(T,p) = 0` for `p ∈ (p* + λ_max⁺(H₁)T, R − λ_max⁻(H₁)T)`.
  (The printed initial datum in the statement is the zero vector on `[p*,R]`;
  the proof on p. 26 uses exactly `ω(0,p) ≡ 0` on `(p*,R)` — the OCR `θ` in the
  extracted statement is the bold zero `0`.)
* Theorem 5.1, p. 27: if `ψ(p) = e^{−p}` on `(0,R)` and the backward
  characteristics stay inside `(0,R)`, then `u_f(T) = e^p w(T,p)` on the
  recovery interval.

Both are proved here in the diagonalized characteristic model `charSolution`
(see `Model.lean`); the `H₂` conjugation and the diagonalization `H₁ = QΛQ*`
of Lemma 5.3 are the paper's own reduction.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.Schrodinger25.MainResults.Transport

open Qatlib.Papers.Schrodinger25.MainResults

variable {ι : Type*} [Fintype ι]

/-- **Lemma 5.1** (p. 26).  Finite propagation speed: if the initial profile
vanishes on `[p*, R]`, then at time `T` the solution vanishes on the open cone
`(p* + λ⁺ T, R − λ⁻ T)`, where `λ⁺ ≥ λ_j ≥ −λ⁻` for every eigenvalue.  This is
the paper's localization argument (5.1) reduced to characteristics. -/
theorem lemma_five_one_vanishing_on_cone
    (ψ : ℝ → ℂ) (lam : ι → ℝ) (u : ι → ℂ)
    (pstar R lamPos lamNeg T : ℝ)
    (hT : 0 ≤ T)
    (hpos : ∀ j, lam j ≤ lamPos) (hneg : ∀ j, -lamNeg ≤ lam j)
    (hzero : ∀ q, q ∈ Set.Ioo pstar R → ψ q = 0)
    (p : ℝ) (hp : p ∈ Set.Ioo (pstar + lamPos * T) (R - lamNeg * T)) :
    charSolution ψ lam u T p = 0 := by
  funext j
  simp only [charSolution]
  have hle : lam j * T ≤ lamPos * T :=
    mul_le_mul_of_nonneg_right (hpos j) hT
  have hge : -(lam j) * T ≤ lamNeg * T := by
    have h : -lam j ≤ lamNeg := by linarith [hneg j]
    exact mul_le_mul_of_nonneg_right h hT
  have hq1 : pstar < p - lam j * T := by linarith [hp.1]
  have hq2 : p - lam j * T < R := by linarith [hp.2, hge]
  simp [hzero (p - lam j * T) ⟨hq1, hq2⟩]

/-- **Theorem 5.1** (p. 27).  Exact recovery: if `ψ(q) = e^{−q}` on `(0,R)` and
every backward characteristic footpoint `p − λ_j T` of the recovery point `p`
remains in `(0,R)`, then `e^p w(T,p) = u_f(T)` componentwise (in the H₁
eigenbasis), i.e. `u_f(T) = e^p w(T,p)` on
`(λ⁺ T, R − λ⁻ T)`. -/
theorem theorem_five_one_exact_recovery
    (ψ : ℝ → ℂ) (lam : ι → ℝ) (u : ι → ℂ) (R T p : ℝ)
    (hexp : ∀ q, q ∈ Set.Ioo (0 : ℝ) R → ψ q = Complex.exp (-(q : ℂ)))
    (hin : ∀ j, p - lam j * T ∈ Set.Ioo (0 : ℝ) R) :
    recovery ψ lam u T p = evolved lam u T := by
  funext j
  simp only [recovery, charSolution, evolved]
  rw [hexp (p - lam j * T) (hin j)]
  have hmain : (Real.exp p : ℂ) * Complex.exp (-((p - lam j * T : ℝ) : ℂ))
      = (Real.exp (lam j * T) : ℂ) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.ofReal_exp]
    push_cast
    ring
  rw [← mul_assoc, hmain]

end Qatlib.Papers.Schrodinger25.MainResults.Transport
