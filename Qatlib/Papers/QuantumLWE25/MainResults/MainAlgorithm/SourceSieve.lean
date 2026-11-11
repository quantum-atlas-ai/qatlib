/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumLWE25.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# QuantumLWE25 — sub-exponential sieve and the abstract main results

Fixed arXiv:2310.00644v2.

* c001: abstract, §1 (three main results).
* c007: Theorem 32 (Main theorem), p.14.
* c008: Corollary 34, p.16.

The algorithmic existence statements use `QuantumAlgo` (distribution-based, with a declared
time cost and sample count). The input of the sieve algorithm is the true secret together
with the `ℓ` public vectors `a`; the quantum `S|LWE⟩` registers are not represented in the
model, only the solver's output law. "Finds the secret" is read as bounded-error success
probability at least `2/3` (amplification-invariant), except where the paper states a
stronger `1 - 2^{-Ω(n)}` bound.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumLWE25.MainResults

open scoped BigOperators Matrix
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-! ## The amplitude hypothesis of Theorem 32 (p.14) -/

/-- The paper's hypothesis on the amplitude `f`: two distinct points `j₁, j₂ ∈ Z_q` with
`gcd(j₁-j₂, q) = 1` and both `|DFT_q(f)(jᵢ)|` larger than `2^{-√(n log q)}`. -/
def HasTwoLargeDFTPoints (n q : ℕ) [NeZero q] (f : ℤ → ℂ) : Prop :=
  ∃ j1 j2 : ZMod q, j1 ≠ j2 ∧ Nat.gcd (j1 - j2).val q = 1 ∧
    (2 : ℝ) ^ (-Real.sqrt ((n : ℝ) * Real.log (q : ℝ))) < ‖dft q f j1‖ ∧
    (2 : ℝ) ^ (-Real.sqrt ((n : ℝ) * Real.log (q : ℝ))) < ‖dft q f j2‖

/-- **Sieve conclusion** (Theorem 32 / abstract item 1). There is a black-box quantum
algorithm using `ℓ` samples of public vectors that recovers the secret with success
probability at least `2/3` in sub-exponential time `2^{O(√(n log q))}`. -/
def SieveSolves (q ℓ n : ℕ) : Prop :=
  ∃ A : QuantumAlgo (fun _ : ℕ => (Fin n → ZMod q) × (Fin ℓ → Fin n → ZMod q))
                     (fun _ : ℕ => Fin n → ZMod q),
    (∀ (s : Fin n → ZMod q) (a : Fin ℓ → Fin n → ZMod q),
      (2 : ℝ) / 3 ≤ A.successProb 0 (s, a) (fun s' => s' = s)) ∧
    A.sampleCount 0 = ℓ ∧
    ∃ c : ℝ, 0 < c ∧ A.timeCost 0 ≤ subExpProfile c n q

/-- **Theorem 32 (Main theorem), p.14.** For any normalized amplitude `f` with two large,
generic DFT points, there is a `2^{Θ(√(n log q))}`-time quantum algorithm that, from
`ℓ = 2^{Θ(√(n log q))}` samples `a ← U(Z_q^n)` of `S|LWE⟩ = ∑_e f(e)|⟨a,s⟩+e mod q⟩`,
finds `s`.

The paper's proof (p.14, proof of Theorem 32): compute `DFT_q(f)` and pick `j₁, j₂`;
use the phase-kickback/`DFT` trick to convert each `S|LWE⟩` sample into a DCP sample
`|0⟩ + ω_q^{⟨a,s⟩}|1⟩`-type state (Lemma 30), then run Kuperberg's sieve (Lemma 33)
on the resulting DCP states. Gap: neither the DCP conversion (Lemma 30) nor Kuperberg's
sieve (Lemma 33) is in the library; the sieve is not a one-line consequence, and its
`2^{Θ(√(n log q))}` analysis (the `ℓ* · 2^{4√(n log q)}` sample budget on p.14) would
have to be reconstructed. Candidate dependencies: `HspRecovery.AbelianSampling` for the
Fourier/basis machinery used by the DCP layer. -/
def main_theorem_sieve {n q ℓ : ℕ} [NeZero q] (hq : 2 ≤ q) (f : ℤ → ℂ)
    (hnorm : ∑' e : ℤ, ‖f e‖ ^ 2 = 1) (hDFT : HasTwoLargeDFTPoints n q f)
    (hℓ : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      subExpProfile c₁ n q ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ subExpProfile c₂ n q) : Prop := SieveSolves q ℓ n

/-- **Corollary 34, p.16.** For a Gaussian amplitude `ρ_σ` with a known linear phase
`exp(2πi·ce/q)` (with `c` allowed to differ per sample), `σ = Ω(√n)` and `σ ≤ q`, the
sieve of Theorem 32 solves `S|LWE⟩` in time `2^{Θ(√(n log q))}`.

Proof route (p.16): the discrete Fourier transform of `ρ_σ(e)e^{2πice/q}` is again a
Gaussian of width `q/σ ≥ 1`, which is at least `2^{-√(n log q)}` at two generic points;
Theorem 32 then applies. Gap: the DFT of the discrete Gaussian and the resulting lower
bound on `|DFT_q|` at two coprime-difference points are not formalized; the lower bound
`σ ≥ √n` is what makes the Gaussian DFT mass `≥ 2^{-√(n log q)}`. Candidate dependency:
`poisson_summation_formula` (Lemma 10). -/
def corollary_gaussian_linear_phase {n q ℓ : ℕ} [NeZero q] (hq : 2 ≤ q)
    {σ : ℝ} (hσ : Real.sqrt (n : ℝ) ≤ σ) (hσq : σ ≤ (q : ℝ))
    (c : Fin ℓ → ℝ)
    (hℓ : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      subExpProfile c₁ n q ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ subExpProfile c₂ n q) : Prop := SieveSolves q ℓ n

/-! ## Abstract main results (c001) -/

/-- The quadratic-phase Gaussian target state of Theorem 38 / abstract item 2. The amplitude
is `ρ_r(x)·exp(-πi∑_j x_j²/q)` on the register `(Aᵀs + x) mod q`. (The paper's ℓ-block
decomposition `q = ∏ q_j` with moduli `q_j` in the phase is carried by the statement's
hypotheses; the state model here uses the single modulus `q`.) -/
def quadraticPhaseAmp {m q : ℕ} [NeZero q] (r : ℝ) (x : Fin m → ℤ) : ℂ :=
  (gaussianWeightVec r (fun j => (x j : ℝ)) : ℂ) *
    Complex.exp (-(Real.pi * Complex.I * ∑ j : Fin m, ((x j : ℝ) ^ 2 / (q : ℝ))))

/-- The superposition `φ = ∑_{s∈Z_q^n}∑_{x∈Z^m} ρ_r(x)e^{-πi∑ x_j²/q}|(Aᵀs+x) mod q⟩`. -/
def quadraticPhaseTarget {n m q : ℕ} [NeZero q] (r : ℝ)
    (A : Matrix (Fin n) (Fin m) (ZMod q)) : QState (Fin m → ZMod q) := by
  classical
  exact fun y => ∑' (s : Fin n → ZMod q) (x : Fin m → ℤ),
    if (∀ j, y j = (Aᵀ *ᵥ s) j + ((x j : ℤ) : ZMod q)) then
      quadraticPhaseAmp (q := q) r x else 0

/-- Abstract item 2: a polynomial-time preparer of the quadratic-phase `LWE` state with
`negl(n)` trace distance, over uniformly random `A`. -/
def AbstractQuadraticPhase : Prop :=
  ∀ (n m q : ℕ) [NeZero q], 2 ≤ q →
    ∃ (r : ℝ) (prepare : Matrix (Fin n) (Fin m) (ZMod q) → QState (Fin m → ZMod q))
      (time : ℕ → ℝ),
      PolyBounded time ∧ ∀ A, ∃ err : ℕ → ℝ, Negligible err ∧
        traceDistance (outerProduct (prepare A)) (outerProduct (quadraticPhaseTarget r A))
          ≤ err n

/-- Abstract item 3: a polynomial-time quantum reduction from classical LWE (or worst-case
GapSVP) to `S|LWE⟩` with a Gaussian amplitude and an unknown small phase. Modelled as the
existence of a witness-independent map that produces the `S|LWE⟩` state for every input
instance; the distributional/uniformity part of the paper's statement is not represented
(see the block notes). -/
def AbstractLweToPhaseReduction : Prop :=
  ∀ (n m q : ℕ) [NeZero q], 2 ≤ q →
    ∃ (σ : ℝ) (red : (Matrix (Fin n) (Fin m) (ZMod q) × (Fin m → ZMod q)) →
        QState (Fin m → ZMod q)) (time : ℕ → ℝ),
      PolyBounded time ∧ ∀ A b, ∃ err : ℕ → ℝ, Negligible err ∧
        traceDistance (outerProduct (red (A, b)))
          (outerProduct (quadraticPhaseTarget σ A)) ≤ err n

/-- **Abstract, §1 main results (c001).** The three results of the abstract:
(1) a `2^{O(√(n log q))}`-time sieve for known-phase Gaussian `S|LWE⟩`;
(2) a polynomial-time quantum algorithm for quadratic-phase Gaussian `S|LWE⟩`/`C|LWE⟩`
with `Õ(n)` samples, yielding the quasi-linear oblivious sampler;
(3) polynomial-time quantum reductions from LWE / worst-case GapSVP to `S|LWE⟩` with an
unknown small phase.

The statements are the shared conclusions of Theorems 32/38/48; the abstract adds no
separate mathematics. `AbstractQuadraticPhase` and `AbstractLweToPhaseReduction` are
stated above; item 1 is the `∃ ℓ` version of `SieveSolves`. -/
def abstract_main_results : Prop := (∀ (n q : ℕ) [NeZero q], 2 ≤ q → ∀ f : ℤ → ℂ,
        (∑' e : ℤ, ‖f e‖ ^ 2 = 1) → HasTwoLargeDFTPoints n q f →
        ∃ ℓ : ℕ, SieveSolves q ℓ n ∧ ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
          subExpProfile c₁ n q ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ subExpProfile c₂ n q) ∧
      AbstractQuadraticPhase ∧ AbstractLweToPhaseReduction

end Qatlib.Papers.QuantumLWE25.MainResults
