/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumLWE25.MainResults.MainAlgorithm.SourceSieve
import Qatlib.Papers.QuantumLWE25.MainResults.ShortVector.SourceShortVector

set_option backward.isDefEq.respectTransparency false

/-!
# QuantumLWE25 — from classical LWE to `S|LWE⟩^phase` (Theorems 45, 46, 48, 53)

Fixed arXiv:2310.00644v2.

* c015 Theorem 45, p.24: an LWE sample is turned into an Extrapolated DCP state.
* c016 Theorem 46, p.24: an EDCP state is turned into an `S|LWE⟩^phase` state.
* c017 Theorem 48, p.27: the main LWE → `S|LWE⟩^phase` reduction.
* c018 Theorem 53, p.30: the center `c` of eq. (7) is approximately a discrete
  Gaussian of width `σ_c = α²‖e‖ / √(2(α²‖e‖² + β²q²))`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumLWE25.MainResults

open scoped BigOperators Matrix
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- The Extrapolated DCP state of eq. (7), p.24:
`∑_{j∈Z_q} ρ_σ(j−c)|j⟩|(v+j·s) mod q⟩`. -/
def edcpState {n q : ℕ} [NeZero q] (σ c : ℝ) (v s : Fin n → ZMod q) :
    QState (ZMod q × (Fin n → ZMod q)) :=
  fun p => (gaussianWeight σ (((p.1).val : ℝ) - c) : ℂ) *
    if (∀ i, p.2 i = v i + (p.1 : ZMod q) * s i) then 1 else 0

/-- The `S|LWE⟩^phase` state of eq. (8), p.24:
`∑_{e∈Z} ρ_{q/σ}(e) exp(2πi·ce/q)|(⟨a,s⟩+e) mod q⟩`. -/
def slwePhaseState {q : ℕ} [NeZero q] (σ c : ℝ) (a s : ZMod q) : QState (ZMod q) := by
  classical
  exact fun y => ∑' e : ℤ, if y = a * s + (e : ZMod q) then
      (gaussianWeight (q / σ) (e : ℝ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((c * (e : ℝ)) / (q : ℝ))) else 0

/-- The vector-`a` version of Eq. (8): the `S|LWE⟩^phase` state with public vector
`a ∈ Z_q^n` and secret `s ∈ Z_q^n`, using the pairing `⟨a,s⟩ = ∑ᵢ aᵢsᵢ`. -/
def slwePhaseStateVec {n q : ℕ} [NeZero q] (σ c : ℝ) (a s : Fin n → ZMod q) :
    QState (ZMod q) := by
  classical
  exact fun y => ∑' e : ℤ, if y = (∑ i, a i * s i) + (e : ZMod q) then
      (gaussianWeight (q / σ) (e : ℝ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((c * (e : ℝ)) / (q : ℝ))) else 0

/-- **Theorem 45, p.24.** Under `α = Ω(√n)`, `αγ√m < β < 1/(16√(m log(βq)))`, there is a
`poly(n)`-time quantum algorithm that, given a classical LWE instance `(A, Aᵀs+e)`,
outputs (with probability `1 - 2^{-Ω(n)}`) a vector `y ∈ Z_q^m ∩ B_{L_q(A)}` and an
Extrapolated DCP state of eq. (7).

The state's parameters `σ = αβq/√(α²‖e‖²+β²q²)` and `c = -α²⟨x,e⟩/(α²‖e‖²+β²q²)` are
existentially quantified in the output predicate, because the algorithm does not know
`x`, `e` (as the paper notes). Gap: Gaussian sampling over `L_q(A)` (Lemma 31 with the
coset structure), the lattice short-vector bound (Lemma 18) and the pairing analysis of
Lemma 50 are all unformalized. Candidate dependencies: `gaussian_state_preparation`,
`qary_shortest_vector_large`, `lemma50_truncation`. -/
def lwe_to_edcp {n m q : ℕ} [NeZero q] (α β γ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hm : n * Nat.log2 q ≤ m)
    (hβlo : α * γ * Real.sqrt (m : ℝ) < β)
    (hβhi : β < 1 / (16 * Real.sqrt ((m : ℝ) * Real.log (β * (q : ℝ)))))
    (hαgeo : ∃ k : ℝ, 0 < k ∧ k * Real.sqrt (n : ℝ) ≤ α) : Prop := ∃ A : QuantumAlgo (fun _ : ℕ => Matrix (Fin n) (Fin m) (ZMod q) × (Fin m → ZMod q))
        (fun _ : ℕ => (Fin m → ℤ) × QState (ZMod q × (Fin n → ZMod q))),
      (∀ (Amat : Matrix (Fin n) (Fin m) (ZMod q)) (s : Fin n → ZMod q)
          (e : Fin m → ZMod q),
        (1 - (2 : ℝ) ^ (-(1 : ℝ) * (n : ℝ))) ≤
          A.successProb 0 (Amat, e) (fun out =>
            out.1 ∈ qaryLattice Amat ∧
            ∃ (v : Fin n → ZMod q) (c σ : ℝ),
              traceDistance (outerProduct out.2) (outerProduct (edcpState σ c v s))
                ≤ (2 : ℝ) ^ (-(1 : ℝ) * (n : ℝ)))) ∧
      PolyBounded A.timeCost

/-- **Theorem 46, p.24.** There is an efficient quantum algorithm turning an EDCP state
of eq. (7) into an `S|LWE⟩^phase` state of eq. (8), together with a known
`a ← U(Z_q^n)`.

Gap: the Fourier-transform/phase-estimation step (pp.28–29) converting the joint
`(j, v+j·s)` register into the amplitude `ρ_{q/σ}(e)e^{2πice/q}` and the fresh uniform
`a`; the arithmetic is elementary but the state-level Fourier transport is not built.
Candidate dependency: `FourierRecovery.ModularFourier` (QFT Born-record laws). -/
def edcp_to_slwe_phase {n q : ℕ} [NeZero q] : Prop := ∃ B : QuantumAlgo (fun _ : ℕ => QState (ZMod q × (Fin n → ZMod q)))
        (fun _ : ℕ => (Fin n → ZMod q) × QState (ZMod q)),
      (∀ (σ c : ℝ) (v s : Fin n → ZMod q) (ψ : QState (ZMod q × (Fin n → ZMod q))),
        traceDistance (outerProduct ψ) (outerProduct (edcpState σ c v s))
            ≤ (2 : ℝ) ^ (-(1 : ℝ) * (n : ℝ)) →
          (2 : ℝ) / 3 ≤ B.successProb 0 ψ (fun out =>
            ∃ a : Fin n → ZMod q,
              traceDistance (outerProduct out.2) (outerProduct (slwePhaseStateVec σ c a s))
                ≤ (2 : ℝ) ^ (-(1 : ℝ) * (n : ℝ)))) ∧
      PolyBounded B.timeCost

/-- `SolvesSLwePhase n ℓ q T`: there is an `ℓ`-sample, time-`T` quantum algorithm for the
`S|LWE⟩^phase` problem (as a black-box hypothesis in Theorem 48). -/
def SolvesSLwePhase (n ℓ q : ℕ) [NeZero q] (T : ℝ) : Prop :=
  ∃ A : QuantumAlgo (fun _ : ℕ => (Fin n → ZMod q) × (Fin ℓ → Fin n → ZMod q))
                     (fun _ : ℕ => Fin n → ZMod q),
    (∀ (s : Fin n → ZMod q) (a : Fin ℓ → Fin n → ZMod q),
      (2 : ℝ) / 3 ≤ A.successProb 0 (s, a) (fun s' => s' = s)) ∧
    A.timeCost 0 ≤ T

/-- **Theorem 48 (Main theorem, from LWE to `S|LWE⟩^phase`), p.25.** If `S|LWE⟩^phase` is
solvable with `ℓ = 2^{o(n)}` samples and time `T(E)` for every error norm
`E = ‖e‖² ∈ [mγ²q²]`, then there is a quantum algorithm that, given a classical LWE
sample `(A, Aᵀs+e)`, outputs `s` with probability `1 - 2^{-Ω(n)}` in time
`O((T + ℓ·poly(n,q))·mγ²q²)`.

Gap: the loop over `E`, the use of Theorem 45/46 `ℓ` times and the union bound on the
success probability; all three ingredients are unformalized. Candidate dependencies:
`lwe_to_edcp`, `edcp_to_slwe_phase`. -/
def lwe_to_slwe_phase_reduction {n m q ℓ : ℕ} [NeZero q] (γ : ℝ) (hγ : 0 < γ)
    (T : ℝ → ℝ) (hT : ∀ E : ℝ, 0 ≤ E → SolvesSLwePhase n ℓ q (T E)) : Prop := ∃ B : QuantumAlgo (fun _ : ℕ => Matrix (Fin n) (Fin m) (ZMod q) × (Fin m → ZMod q))
        (fun _ : ℕ => Fin n → ZMod q),
      (∃ c : ℝ, 0 < c ∧ ∀ (Amat : Matrix (Fin n) (Fin m) (ZMod q))
          (s : Fin n → ZMod q) (e : Fin m → ZMod q),
        1 - (2 : ℝ) ^ (-(c * (n : ℝ))) ≤
          B.successProb 0 (Amat, e) (fun s' => s' = s)) ∧
      ∃ err : ℕ → ℝ, Negligible err ∧
        B.timeCost 0 ≤ (T ((m : ℝ) * γ ^ 2 * (q : ℝ) ^ 2) +
          (ℓ : ℝ) * (((n : ℝ) + (q : ℝ)) ^ 3)) *
          ((m : ℝ) * γ ^ 2 * (q : ℝ) ^ 2) + err n

/-- **Theorem 53, p.30.** The center `c` of eq. (7) approximately follows the discrete
Gaussian `D_{Z,σ_c}` with `σ_c = α²‖e‖/√(2(α²‖e‖²+β²q²))`.

Model: the law of `c` is existentially quantified (it is the pushforward of the
Theorem 45 sampling of `x`); the statement records that it is a probability density whose
total-variation distance to the discrete Gaussian of the stated width is `2^{-Ω(m)}`.
Gap: the pushforward computation for `x ~ D_{Z^m, βq√Σ/2}` and the Poisson/Banaszczyk
tail bound (pp.30–31) are not formalized (they reuse Lemma 10 and Lemma 28).
Candidate dependencies: `gaussian_state_trace_distance`, `poisson_summation_formula`. -/
def center_distribution_gaussian {m : ℕ} (α β q : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hq : 0 < q) (e : Fin m → ℝ) : Prop := ∃ (law : ℝ → ℝ) (σc : ℝ), 0 < σc ∧
      σc = α ^ 2 * Real.sqrt (∑ i, (e i) ^ 2) /
        Real.sqrt (2 * (α ^ 2 * (∑ i, (e i) ^ 2) + β ^ 2 * q ^ 2)) ∧
      (∀ c, 0 ≤ law c) ∧
      ∃ err : ℕ → ℝ, ExpSmall err ∧
        (∑' k : ℤ, |law (k : ℝ) -
          (gaussianWeight σc (k : ℝ) / (∑' j : ℤ, gaussianWeight σc (j : ℝ)))|) ≤ err m

end Qatlib.Papers.QuantumLWE25.MainResults
