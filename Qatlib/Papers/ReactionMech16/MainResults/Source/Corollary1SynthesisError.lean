/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ReactionMech16.MainResults.Source.Theorem1TrotterEnergyError

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 1: synthesis error in the ground-state energy

Source: arXiv:1605.03590v2, Appendix D, Corollary 1 (p.16).

For `H = ∑_{j=1}^{M} h_j P_j` with `h_j ∈ ℝ` and Pauli operators `P_j`, assume the
Strang-product Trotter error is at most `Δ_{TS}(t) t` and each gate
`e^{-iH_j t/2}` is synthesized by a unitary `U_j(t)` with
`‖U_j(t) - e^{-iH_j t/2}‖₂ ≤ Δ_synth`.  Then the induced ground-state energy error
is at most `Δ_{TS} + (2M - 1) Δ_synth / t`.

The paper derives this directly from Theorem 1 and Lemma 5: Lemma 5 turns each
synthesis error at time `t/2` into a generator error `δ = Δ_synth / t` for the term
`H_j = h_j P_j`, and Theorem 1 then gives the displayed bound.  Our statement keeps
the Pauli structure (`h_j` real, `P_j` Hermitian and involutive) and the synthesis
error hypothesis, and packages the Lemma 5 step as `hterm` (the paper's "error in
each term is at most δ" with `δ = Δ_synth / t`).

Boundary: `t > 0` (the paper divides by `t`); the effective Hamiltonian is any
Hermitian `K` whose evolution is the Strang product of the synthesized generators.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators

namespace Qatlib.Papers.ReactionMech16.MainResults.Source

/-- arXiv:1605.03590v2, Corollary 1 (p.16): with synthesis error `Δ_synth` per
rotation, the ground-state energy error of the Trotter-Suzuki simulation of
`H = ∑ h_j P_j` is at most `Δ_{TS} + (2M - 1) Δ_synth / t`. -/
theorem corollary1_synthesis_ground_energy
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {M : ℕ} (hM : 1 ≤ M)
    (hcoeff : Fin M → ℝ) (P : Fin M → Matrix I I ℂ)
    (hPherm : ∀ j, (P j).IsHermitian) (hPinvol : ∀ j, P j * P j = 1)
    (Ks : Fin M → Matrix I I ℂ) (hKherm : ∀ j, (Ks j).IsHermitian)
    (K : Matrix I I ℂ) (hK : K.IsHermitian)
    (t Δ Δsynth : ℝ) (ht : 0 < t) (hΔ : 0 ≤ Δ) (hΔs : 0 ≤ Δsynth)
    (htrot : ∀ s : ℝ, 0 ≤ s →
      ‖matrixExpEvo (∑ j : Fin M, (hcoeff j) • P j) s -
        strangProduct (fun j => (hcoeff j) • P j) s‖ ≤ Δ * s)
    (hterm : ∀ j, ‖(hcoeff j) • P j - Ks j‖ ≤ Δsynth / t)
    (hKexp : ∀ s : ℝ, 0 ≤ s → matrixExpEvo K s = strangProduct Ks s) :
    |smallestEigenvalue (∑ j : Fin M, (hcoeff j) • P j)
        (hermitian_sum (fun j => (hcoeff j) • P j) (fun j => (hPherm j).smul (by
          show IsSelfAdjoint (hcoeff j)
          simp [IsSelfAdjoint]))) -
      smallestEigenvalue K hK| ≤ Δ + (2 * (M : ℝ) - 1) * (Δsynth / t) := by
  have hδ : 0 ≤ Δsynth / t := div_nonneg hΔs ht.le
  exact theorem1_trotter_ground_energy hM (fun j => (hcoeff j) • P j) Ks
    (fun j => (hPherm j).smul (by
      show IsSelfAdjoint (hcoeff j)
      simp [IsSelfAdjoint])) hKherm K hK Δ (Δsynth / t) hΔ hδ hterm htrot hKexp

end Qatlib.Papers.ReactionMech16.MainResults.Source
