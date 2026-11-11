/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TuraevViro10.MainResults.WrtBridge
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Qatlib.Papers.TuraevViro10.MainResults.HadamardTest

/-!
# The Hadamard test for the WRT matrix element

Source: G. Alagic, S. P. Jordan, R. König, B. W. Reichardt, *Approximating
Turaev–Viro 3-manifold invariants is universal for quantum computation*,
arXiv:1003.0923v1 (3 March 2010), p. 3, right column:

> "An estimate to within `ε` of the desired matrix element
> `⟨v_{C,g}| ρ_{C,g}(x) |v_{C,g}⟩` can be given, except with probability `δ`,
> using `O(log(1/δ)/ε^2)` Hadamard tests, as in [3]."

This module formalizes the *circuit* that every one of those Hadamard tests
runs, and the Born probabilities it produces.  The paper's `ρ_{C,g}(x)` is a
projective unitary representation of `MCG(g)` on `H_{C,g}` and `|v_{C,g}⟩` is a
unit vector (p. 2, right column), so the analytic inputs are `‖U v‖ = ‖v‖ = 1`
together with complex linearity of the twist action.

The circuit is modelled on the pair of ancilla branches `H × H` (`φ.1` is the
branch on which the ancilla reads `0`, `φ.2` the branch on which it reads `1`):

* `ancillaPlus v` — prepare the ancilla in `2^(-1/2) (|0⟩ + |1⟩)` and the
  register in `v`;
* `ctrl U` — apply the twist `U` on the ancilla-`1` branch;
* `phaseGate U` — the phase-shifted gate `y ↦ (-i) • U y`, used for the
  imaginary part;
* `hadamardPair` — the final Hadamard on the ancilla.

The results are the exact Born probabilities behind the paper's estimate:

* `prob0_real`, `prob0_imag` — reading the ancilla as `0` gives
  `(1 + Re⟨v|U v⟩)/2` and `(1 + Im⟨v|U v⟩)/2`;
* `readout_re`, `readout_im` — hence `2 p - 1` reads off `Re` and `Im` of the
  matrix element;
* `normSq_eq_readout` — the modulus squared `|⟨v|U v⟩|^2`, which by
  `normalizedTvInvariant_eq_normSq` is the normalized Turaev–Viro invariant, is
  the quartic `(2 p - 1)^2 + (2 q - 1)^2` in the two readout probabilities;
* `normalizedTvInvariant_eq_readout` — the same identity at the level of a
  `TuraevViroModel` built from a unit vector and its isometric twist action;
* `wrtScaled_error_le` — a matrix-element accuracy `ε` becomes the additive
  `D^(g-1) ε` accuracy of Eq. (3) for the WRT invariant;
* `wrtScale_phase_invariant` — multiplying the WRT invariant by a projective
  phase `ζ` with `‖ζ‖ = 1` leaves `TV = |WRT|^2` unchanged, which is the
  paper's statement that the central-charge phase ambiguity cancels.

Not formalized here: the construction of `ρ_{C,g}` from the `F`/`S` moves and
the `R`-symbol phases (p. 3), and the `O(log(1/δ)/ε^2)` tail bound of [3].  The
statistical step is separately derived from Chebyshev in `ReadoutSampling`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TuraevViro10.MainResults.HadamardTest

open Qatlib.Papers.TuraevViro10.MainResults.HadamardTest
open Qatlib.Papers.TuraevViro10.MainResults.WrtBridge

open Qatlib.Papers.TuraevViro10.MainResults.WrtBridge.TuraevViroModel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The complementary real-part Born probability lies in `[0,1]`.**  The
`1`-outcome branch is a genuine Bernoulli parameter as well, which is useful
when the implementation records the complementary outcome directly. -/
theorem prob1_mem_Icc (U : H → H) (hUlin : ∀ (c : ℂ) (x : H), U (c • x) = c • U x)
    (v : H) (hv : ‖v‖ = 1) (hU : ‖U v‖ = ‖v‖) :
    prob1 (hadamardPair (ctrl U (ancillaPlus v))) ∈ Set.Icc (0 : ℝ) 1 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) v (U v)
  rw [hv, hU, hv, mul_one] at h
  have hre : |(inner ℂ v (U v)).re| ≤ 1 :=
    le_trans (Complex.abs_re_le_norm _) h
  rw [prob1_real U hUlin v hv hU]
  constructor <;> nlinarith [hre, abs_le.mp hre]

/-- **The imaginary-part `0`-outcome probability lies in `[0,1]`.**  This
explicitly closes the boundedness side of the phase-shifted Hadamard test,
rather than relying on the real-part proof by analogy. -/
theorem prob0_imag_mem_Icc (U : H → H) (hUlin : ∀ (c : ℂ) (x : H), U (c • x) = c • U x)
    (v : H) (hv : ‖v‖ = 1) (hU : ‖U v‖ = ‖v‖) :
    prob0 (hadamardPair (ctrl (phaseGate U) (ancillaPlus v))) ∈ Set.Icc (0 : ℝ) 1 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) v (U v)
  rw [hv, hU, hv, mul_one] at h
  have him : |(inner ℂ v (U v)).im| ≤ 1 :=
    le_trans (Complex.abs_im_le_norm _) h
  rw [prob0_imag U hUlin v hv hU]
  constructor <;> nlinarith [him, abs_le.mp him]

/-! A concrete one-dimensional readout witness.  This is an algebraic
sanity check for the Hadamard layer; it does not construct the paper's
category-dependent `F`/`S`/`R` representation. -/

/-- The identity complex gate used by the finite Hadamard readout witness. -/
def identityReadoutGate : ℂ → ℂ := id

/-- The identity readout gate commutes with scalar multiplication. -/
theorem identityReadoutGate_linear :
    ∀ (c : ℂ) (x : ℂ), identityReadoutGate (c • x) = c • identityReadoutGate x := by
  intro c x
  rfl

/-- The identity gate has Hadamard real readout one. -/
theorem identityReadoutGate_real_readout :
    2 * prob0 (hadamardPair
      (ctrl identityReadoutGate (ancillaPlus (1 : ℂ)))) - 1 = 1 := by
  rw [readout_re identityReadoutGate identityReadoutGate_linear (1 : ℂ) (by norm_num) (by rfl)]
  norm_num [identityReadoutGate]

/-- The identity gate has Hadamard imaginary readout zero. -/
theorem identityReadoutGate_imag_readout :
    2 * prob0 (hadamardPair
      (ctrl (phaseGate identityReadoutGate) (ancillaPlus (1 : ℂ)))) - 1 = 0 := by
  rw [readout_im identityReadoutGate identityReadoutGate_linear (1 : ℂ) (by norm_num) (by rfl)]
  norm_num [identityReadoutGate]

end Qatlib.Papers.TuraevViro10.MainResults.HadamardTest
