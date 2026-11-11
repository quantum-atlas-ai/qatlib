/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumLWE25.MainResults.SourceModel
import Mathlib.Algebra.Order.Floor.Defs

set_option backward.isDefEq.respectTransparency false

/-!
# QuantumLWE25 — Gaussian state preparation and the pure-imaginary Gaussian basis
(Lemmas 31 and 37)

Fixed arXiv:2310.00644v2.

* Lemma 31, p.14: for `1 ≤ R ≤ 2^{n^c}` there is a poly(n)-size unitary `U` mapping
  `|0⟩` to a state within trace distance `2^{-Ω(n)}` of `|σ_{n,R}⟩`, using
  `2n⌈n^c log n⌉` qubits.
* Lemma 37, p.18: a poly(log t)-size quantum circuit implements the unitary
  `∑_{d∈Z_t}|d⟩⟨ψ_d|`, where `ψ_d(x) = e^{-πi(x-d)²/t}` on `x ∈ Z_t`.

Both are existence-of-a-unitary statements; the statements below quantify over the
finite matrix model `Matrix (Fin N) (Fin N) ℂ` (resp. `Matrix (ZMod t) (ZMod t) ℂ`)
and record the paper's trace-distance / gate-count conclusions.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumLWE25.MainResults

open scoped BigOperators Matrix
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- **Lemma 31 (Gaussian state preparation), p.14.** For `1 ≤ R ≤ 2^{n^c}` there is a
unitary `U` on `2n⌈n^c log n⌉` qubits whose image of `|0⟩` is `2^{-Ω(n)}`-close in trace
distance to the Gaussian state `|σ_{n,R}⟩` (modelled as `gaussianState N R`).

Proof route of the paper (p.14): prepare `⌈n^c log n⌉`-bit truncated Gaussians by the
standard reversible sampling construction, then take tensor products over the `2n`
coordinates. Gap: the truncated reversible Gaussian sampler itself and its `2^{-Ω(n)}`
tail bound; this is exactly the paper's referenced construction rather than a one-line
consequence. Candidate dependency: `Concepts.QftPreparation.LocalQft.aqFairLabelSampler`
for the fair-bit sampling layer and `ProbabilityCore.Concentration` Gaussian tails. -/
def gaussian_state_preparation {n R : ℕ} {c : ℝ}
    (hc : 0 ≤ c) (hR1 : 1 ≤ R) (hR : (R : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ c)) : Prop := ∃ (N : ℕ) (U : Matrix (Fin N) (Fin N) ℂ),
      N = 2 ^ (2 * n * Nat.ceil ((n : ℝ) ^ c * Real.log (n : ℝ))) ∧
      U ∈ Matrix.unitaryGroup (Fin N) ℂ ∧
      ∃ c' : ℝ, 0 < c' ∧
        traceDistance (outerProduct (U *ᵥ ketZero N))
          (outerProduct (gaussianState N (R : ℝ))) ≤ (2 : ℝ) ^ (-(c' * (n : ℝ)))

/-- The pure-imaginary Gaussian vector `|ψ_d⟩ = ∑_{x∈Z_t} e^{-πi(x-d)²/t}|x⟩` (p.18). -/
def psiBasis (t : ℕ) [NeZero t] (d : ZMod t) : QState (ZMod t) :=
  fun x => Complex.exp
    (-(Real.pi * Complex.I * (((x - d).val : ℝ) ^ 2) / (t : ℝ)))

/-- **Lemma 37, p.18.** There is a `poly(log t)`-size quantum circuit implementing the
unitary `∑_{d∈Z_t}|d⟩⟨ψ_d|`; in the finite model this says some unitary `U` sends the
computational basis vector `|d⟩` to `|ψ_d⟩`, with a polynomial gate count.

Proof route of the paper (p.18): `|d⟩ ↦ e^{-πid²/t}|d⟩` (a diagonal phase), then
`QFT_{Z_t}` with phase kick-back, then the phase `e^{-πix²/t} e^{-πid²/t}`; the three
steps implement the map exactly. Gap: a gate-level local-QFT-with-phases circuit and
its cost are not in the model; `QftPreparation.LocalQft.aqLocalQFT_actual_matrix_and_cost`
supplies the plain local QFT, but the two diagonal phase layers and the exact identity
`∑_x e^{2πixd/t - πix²/t - πid²/t} = e^{-πi(x-d)²/t}` remain to be built. -/
def pure_imaginary_gaussian_basis_circuit {t : ℕ} [NeZero t] : Prop := ∃ (U : Matrix (ZMod t) (ZMod t) ℂ) (gates : ℕ → ℝ),
      U ∈ Matrix.unitaryGroup (ZMod t) ℂ ∧
      (∀ d : ZMod t, U *ᵥ Ket d = psiBasis t d) ∧
      PolyBounded gates ∧
      ∃ k C : ℝ, 0 < C ∧ ∀ n, gates n ≤ C * ((Real.log (n : ℝ) + 1) ^ k)

end Qatlib.Papers.QuantumLWE25.MainResults
