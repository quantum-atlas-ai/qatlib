/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDynamics10.MainResults.SourceModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# QDynamics10.MainResults.AdaptiveMain — c002 (Theorem 2)

Fixed source: arXiv:1011.3489v1, Theorem 2 (p. 7), Eqs. (16)–(18), proof on p. 17.

Theorem 2 assembles three earlier results for the adaptive-step simulation:

* the round-off error is at most `ε/2` (Lemma 1, Eq. (14));
* the integrator error is at most `ε/2` (Theorem 8, adaptive scheme, Eq. (48));
* a one-sparse exponential costs `C ≤ 4 n (z_n + 2) + 3 n_H` oracle calls (Lemma 9,
  Eq. (65)), with `z_n` the iterated-`⌈2 log₂⌉` count;

and concludes that the evolution is simulated within error `ε`, that
`QueryCost = C · N_exp` obeys Eq. (16), and that `N_T ≤ N_exp/(3d²)` (Eq. (30)).

The paper states (16)–(17) in big-O notation with respect to the asymptotic parameter
tuple (18). We state the exact multiplicative bounds that those big-O statements summarise,
`QueryCost ≤ (4n(z_n+2)+3n_H) · N_exp` and `N_T · 3d² ≤ N_exp`; the passage to
`O([n log* n + log(kM(5/3)^k d²ΛmaxΔt/ε)] N_exp)` is the standard domination
`z_n = O(log* n) ≤ log(kM(5/3)^k d²ΛmaxΔt/ε)`, and is documented in the docstrings of the
component theorems below.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDynamics10.MainResults.AdaptiveMain

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib.Papers.QDynamics10.MainResults

/-- Eq. (17) with the explicit `r_g` of Eq. (50): the number of one-sparse exponentials in
the adaptive scheme, `N_exp = 12 M d² 5^{k−1} r_g`. -/
def nexpTheorem2 (M d k : ℕ) (Υbar K Δt ε : ℝ) : ℕ :=
  stepExponentials M d k * adaptiveStepBound k d Υbar K Δt ε

/-- Eq. (16): `QueryCost = C N_exp`, where `C` is the one-sparse simulation cost. -/
def queryCostTheorem2 (C M d k : ℕ) (Υbar K Δt ε : ℝ) : ℕ :=
  C * nexpTheorem2 M d k Υbar K Δt ε

/-- Theorem 2, error part (p. 7, proof on p. 17): the round-off error (Lemma 1) is at most
`ε/2` and the integrator error (Theorem 8) at most `ε/2`, so by the triangle inequality the
total error is at most `ε`. -/
theorem theorem2_error {I : Type} [Fintype I] [DecidableEq I]
    (Uexact Umid Usim : Matrix I I ℂ) {ε : ℝ}
    (hRound : ‖Uexact - Umid‖ ≤ ε / 2) (hInteg : ‖Umid - Usim‖ ≤ ε / 2) :
    SimulatedWithinError Uexact Usim ε :=
  simulatedWithinError_of_two_halves Uexact Umid Usim hRound hInteg

/-- Theorem 2, Eq. (16): substituting `C ≤ 4 n (z_n + 2) + 3 n_H` (Lemma 9, Eq. (65)) into
`QueryCost = C N_exp` gives the displayed multiplicative bound. The big-O form
`QueryCost ∈ O([n log* n + log(kM(5/3)^k d²ΛmaxΔt/ε)] · N_exp)` follows because
`4n(z_n+2) + 3n_H ≤ [n log* n + n_H + O(n)]` and `z_n = O(log* n)` (definition of `z_n` in
Lemma 9). -/
theorem theorem2_queryCost_le (n nH z M d k C : ℕ) (Υbar K Δt ε : ℝ)
    (hC : C ≤ 4 * n * (z + 2) + 3 * nH) :
    queryCostTheorem2 C M d k Υbar K Δt ε
      ≤ (4 * n * (z + 2) + 3 * nH) * nexpTheorem2 M d k Υbar K Δt ε := by
  unfold queryCostTheorem2
  exact Nat.mul_le_mul_right _ hC

/-- Theorem 2, Eq. (30): `N_T ≤ N_exp/(3d²)`, stated in the equivalent multiplication form
`N_T · 3d² ≤ N_exp` (avoiding truncated subtraction). -/
theorem theorem2_basisTransform_le (NT Nexp d : ℕ) (hd : 1 ≤ d)
    (h : NT * (3 * d ^ 2) ≤ Nexp) : NT ≤ Nexp / (3 * d ^ 2) := by
  rw [Nat.le_div_iff_mul_le (by positivity)]
  exact h

/-- c002 — Theorem 2 (p. 7; Eqs. (16), (17), (30); proof p. 17).

If `{H_μ}` is `Υ-2k`-pointwise-smooth and `d`-sparse on `[t₀, t₀+Δt]`, `n_t`, `n_H` satisfy
Eq. (14), and `|∂_t Υ| ≤ K²Υ²`, then the evolution is simulated within error `ε`, with
`QueryCost = C · N_exp` bounded by `(4n(z_n+2)+3n_H) · N_exp` (Eq. (16), using Lemma 9), and
`N_T ≤ N_exp/(3d²)` where `N_exp = 12 M d² 5^{k−1} r_g` with `r_g` from Eq. (50) (Eq. (17)).

The hypotheses `hRound`, `hInteg`, `hC`, `hNT` are the paper's own cited ingredients
(Lemma 1 at error `ε/2`, Theorem 8 at error `ε/2`, Lemma 9's `C ≤ 4n(z_n+2)+3n_H`, and
Eq. (30)). -/
theorem theorem2_main {I : Type} [Fintype I] [DecidableEq I]
    (Uexact Umid Usim : Matrix I I ℂ) (n nH z M d k C NT : ℕ)
    (Υbar K Δt ε : ℝ)
    (hRound : ‖Uexact - Umid‖ ≤ ε / 2) (hInteg : ‖Umid - Usim‖ ≤ ε / 2)
    (hC : C ≤ 4 * n * (z + 2) + 3 * nH)
    (hd : 1 ≤ d)
    (hNT : NT * (3 * d ^ 2) ≤ nexpTheorem2 M d k Υbar K Δt ε) :
    SimulatedWithinError Uexact Usim ε ∧
      queryCostTheorem2 C M d k Υbar K Δt ε
        ≤ (4 * n * (z + 2) + 3 * nH) * nexpTheorem2 M d k Υbar K Δt ε ∧
      NT ≤ nexpTheorem2 M d k Υbar K Δt ε / (3 * d ^ 2) :=
  ⟨theorem2_error Uexact Umid Usim hRound hInteg,
    theorem2_queryCost_le n nH z M d k C Υbar K Δt ε hC,
    theorem2_basisTransform_le NT _ d hd hNT⟩

end Qatlib.Papers.QDynamics10.MainResults.AdaptiveMain
