/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumLWE25.MainResults.MainAlgorithm.SourceSieve
import Qatlib.Papers.QuantumLWE25.MainResults.ShortVector.SourceShortVector

set_option backward.isDefEq.respectTransparency false

/-!
# QuantumLWE25 — quadratic-phase Gaussian LWE states and the oblivious sampler
(Theorems 38, Lemma 39, Corollaries 42 and 44)

Fixed arXiv:2310.00644v2.

* c011 Theorem 38, p.20: with `m = 2ℓn·ω(log n)`, `q = q₁⋯q_ℓ` coprime, and
  `√(qn) > r > 30n log n · max q_j`, a `poly(n,ℓ,log q)`-time algorithm, given
  `A ← U(Z_q^{n×m})`, outputs a state within negligible trace distance of the
  quadratic-phase Gaussian LWE state `φ`.
* c012 Lemma 39, p.20: given `A_j ← U(Z_q^{n×m/ℓ})` and `|ψ_{s,j}⟩`, recover `s mod q_j`
  in `poly(n)` time with probability `1 - negl(n)`.
* c013 Corollary 42, p.22 and c014 Corollary 44, p.23: witness-oblivious samplers under
  the quantum hardness of `LWE_{n,m,q,r/(√2q)}`.

The paper's `ω(log n)` factor is instantiated by `log n` in the hypotheses below (a
concrete lower-bound instance; the paper allows any super-logarithmic factor). The
LWE hardness assumption of Corollaries 42/44 is stated as the predicate `LWEHardness`
(no polynomial-time quantum distinguisher has non-negligible advantage), and
witness-obliviousness is Definition 40 verbatim (`WitnessObliviousSampler`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumLWE25.MainResults

open scoped BigOperators Matrix
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- **Theorem 38, p.20.** Under the stated parameter conditions, there is a
`poly(n,ℓ,log q)`-time preparer that, for `A ← U(Z_q^{n×m})`, outputs a state within
`negl(n)` trace distance of the quadratic-phase Gaussian LWE state
`φ = ∑_s∑_x ρ_r(x)e^{-πi∑_j ‖x_j‖²/q_j}|(Aᵀs+x) mod q⟩` (modelled by
`quadraticPhaseTarget`, which folds the block moduli into the single modulus `q`).

Gap: Lemma 31 (Gaussian preparation) plus the coherent `Aᵀs + x` addition and the
quadratic-phase layer of pp.20–22 are all missing; the paper's error analysis
(union/pairing bounds over the ℓ blocks) is a substantial piece. Candidate
dependencies: `gaussian_state_preparation` (Lemma 31) and the local-QFT arithmetic of
`FourierRecovery.ModularFourier`. -/
def quadratic_phase_lwe_state_preparation {n m q ℓ : ℕ} [NeZero q]
    (qj : Fin ℓ → ℕ) (hq : 2 ≤ q) (hℓn : 1 ≤ ℓ)
    (hm : 2 * ℓ * n * (Real.log (n : ℝ) + 1) ≤ (m : ℝ))
    {r : ℝ} (hr : Real.sqrt ((q : ℝ) * (n : ℝ)) > r)
    (hr' : ∀ j : Fin ℓ, 30 * (n : ℝ) * Real.log (n : ℝ) * (qj j : ℝ) < r) : Prop := ∃ (prepare : Matrix (Fin n) (Fin m) (ZMod q) → QState (Fin m → ZMod q)) (time : ℕ → ℝ),
      PolyBounded time ∧ ∀ A, ∃ err : ℕ → ℝ, Negligible err ∧
        traceDistance (outerProduct (prepare A)) (outerProduct (quadraticPhaseTarget r A))
          ≤ err n

/-- **Lemma 39, p.20.** For any block `j`, given `A_j ← U(Z_q^{n×m/ℓ})` and the state
`|ψ_{s,j}⟩ = ∑_{x_j} ρ_r(x_j)e^{-πi‖x_j‖²/q_j}|(A_jᵀs+x_j) mod q⟩`, one recovers `s mod q_j`
in `poly(n)` time with probability `1 - negl(n)`.

The output is represented in `Z_q^n` together with the congruence `s' ≡ s (mod q_j)`.
Gap: the measurement in the `{|ψ_d⟩}` basis (Lemma 37) applied blockwise, and the
concentration of the resulting distribution on `c mod q_j` (Theorem 36), are not
formalized. Candidate dependencies: `center_finding` (Theorem 36) and
`pure_imaginary_gaussian_basis_circuit` (Lemma 37). -/
def recover_secret_mod_qj {n m q ℓ : ℕ} [NeZero q] (qj : Fin ℓ → ℕ) (j : Fin ℓ)
    {r : ℝ} (hr : 0 < r) : Prop := ∃ A : QuantumAlgo (fun _ : ℕ => Fin n → ZMod q) (fun _ : ℕ => Fin n → ZMod q),
      (∃ err : ℕ → ℝ, Negligible err ∧ ∀ s : Fin n → ZMod q,
        1 - err n ≤ A.successProb 0 s
          (fun s' => ∀ i, ∃ k : ℤ, s' i - s i = (qj j : ZMod q) * (k : ZMod q))) ∧
      PolyBounded A.timeCost

/-- The unnormalized discrete-Gaussian LWE weight of `b` given public `A` (Definition 1,
p.1): `∑_{s∈Z_q^n} ∑_{e∈ℤ^m, Aᵀs+e ≡ b (mod q)} ρ_α(e)`, with the error width `α` (the
paper's `αq` for `LWE_{n,m,q,α}`). -/
def lweWeight {n m q : ℕ} [NeZero q] (α : ℝ) (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) : ℝ :=
  ∑' (s : Fin n → ZMod q) (e : Fin m → ℤ),
    if (∀ j, b j = (Aᵀ *ᵥ s) j + ((e j : ℤ) : ZMod q)) then
      gaussianWeightVec α (fun j => (e j : ℝ)) else 0

/-- The total Gaussian mass `∑_{e∈ℤ^m} ρ_α(e)`, the normalizing constant of the LWE
error distribution. -/
def gaussTotal (m : ℕ) (α : ℝ) : ℝ :=
  ∑' e : Fin m → ℤ, gaussianWeightVec α (fun j => (e j : ℝ))

/-- The probability mass of the `LWE_{n,m,q,α}` distribution at `b`, given `A`
(Definition 1, p.1): the secret is uniform on `Z_q^n` and the error is `D_{ℤ^m,α}`. -/
def lweMass {n m q : ℕ} [NeZero q] (α : ℝ) (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) : ℝ :=
  ((q : ℝ) ^ n)⁻¹ * lweWeight α A b / gaussTotal m α

/-- The distinguishing advantage of a solver `S` on `LWE_{n,m,q,α}` against uniform
samples, for a fixed public matrix `A` (Definition 1, p.1). The solver sees `(A,b)` and
outputs a guess `Bool`; the advantage is the difference in acceptance probability
between the LWE sample law `lweMass α A b` and the uniform law `q^{-m}`. -/
def lweAdvantage {n m q : ℕ} [NeZero q] (α : ℝ)
    (solver : QuantumAlgo
      (fun _ : ℕ => Matrix (Fin n) (Fin m) (ZMod q) × (Fin m → ZMod q))
      (fun _ : ℕ => Bool)) (A : Matrix (Fin n) (Fin m) (ZMod q)) : ℝ := by
  classical
  exact |(∑' b : Fin m → ZMod q,
      (lweMass α A b - ((q : ℝ) ^ m)⁻¹) *
        (if solver.prob 0 (A, b) true ≥ 1 / 2 then 1 else 0))|

/-- The paper's quantum-hardness assumption on `LWE_{n,m,q,α}` (Definition 1 / the
assumption used in Corollaries 42 and 44, p.22): no polynomial-time quantum algorithm
distinguishes `LWE_{n,m,q,α}` from uniform samples with non-negligible advantage. This is
the black-box hypothesis of the paper, stated rather than assumed as an axiom. -/
def LWEHardness (n m q : ℕ) [NeZero q] (α : ℝ) : Prop :=
  ∀ solver : QuantumAlgo
      (fun _ : ℕ => Matrix (Fin n) (Fin m) (ZMod q) × (Fin m → ZMod q))
      (fun _ : ℕ => Bool),
    PolyBounded solver.timeCost →
      ∃ err : ℕ → ℝ, Negligible err ∧ ∀ A, lweAdvantage α solver A ≤ err m

/-- `WitnessObliviousSampler n m q α`: Definition 40, p.22. A sampler `S` producing
`b ∈ Z_q^m` from `A` is witness-oblivious for `LWE_{n,m,q,α}` when

1. for uniform `A`, the output distribution of `S` is statistically indistinguishable
   from `LWE_{n,m,q,α}` (total-variation distance `≤ negl`);
2. for every extractor `E` that sees `A` (and hence for every valid extractor of
   Definition 40), the probability that `E` recovers a secret/error pair `(s,e)`
   consistent with the sampled `b` is `≤ negl`.

The sampler's output law is a probability mass `S A b` on `b`. The paper's interactive
formulation "`E` does not change the state of `S`" is captured by letting `E` depend on
`A` only, which is at least as strong a requirement on `S`. -/
def WitnessObliviousSampler (n m q : ℕ) [NeZero q] (α : ℝ) : Prop := by
  classical
  exact ∃ S : Matrix (Fin n) (Fin m) (ZMod q) → (Fin m → ZMod q) → ℝ,
    (∀ A b, 0 ≤ S A b) ∧
    (∀ A, ∑' b, S A b = 1) ∧
    (∃ err : ℕ → ℝ, Negligible err ∧ ∀ A,
      (1 / 2) * ∑' b, |S A b - lweMass α A b| ≤ err m) ∧
    (∀ E : Matrix (Fin n) (Fin m) (ZMod q) → (Fin n → ZMod q) × (Fin m → ℤ),
      ∃ err : ℕ → ℝ, Negligible err ∧ ∀ A,
        (∑' b : Fin m → ZMod q, S A b *
          (if ∃ (s : Fin n → ZMod q) (e : Fin m → ℤ),
            (∀ j, b j = (Aᵀ *ᵥ s) j + ((e j : ℤ) : ZMod q)) ∧ E A = (s, e)
           then 1 else 0)) ≤ err m)

/-- **Corollary 42, p.22.** Under the parameters of Theorem 38 and the quantum hardness
of `LWE_{n,m,q,r/(√2q)}`, there is a witness-oblivious quantum sampler for
`LWE_{n,m,q,r/(√2q)}`.

Proof route (p.22): run Theorem 38 to obtain the quadratic-phase state, measure it in the
`S|LWE⟩` form (Lemma 39 gives the secret recovery), and note that the produced samples do
not reveal the witness. Gap: the sampler-law fidelity is not modelled; only the
witness-independence and lattice membership are stated. -/
def witness_oblivious_sampler {n m q ℓ : ℕ} [NeZero q] (hq : 2 ≤ q)
    {r : ℝ} (hHard : LWEHardness n m q (r / Real.sqrt (2 * (q : ℝ)))) : Prop := WitnessObliviousSampler n m q (r / Real.sqrt (2 * (q : ℝ)))

/-- **Corollary 44, p.23.** With `m' ≤ m`, `q' ≤ q` and
`(r'/(√2q'))² ≥ (r/(√2q))² + (s√n/q')²·ω(log n)`, quantum hardness of
`LWE_{n,m,q,r/(√2q)}(D_{Z^n,s})` yields a witness-oblivious sampler for
`LWE_{n,m',q',r'/(√2q')}(D_{Z^n,s})`.

Gap: the modulus-reduction noise analysis (the displayed inequality) is not formalized;
the sampler-law fidelity is again not modelled. -/
def witness_oblivious_sampler_param {n m m' q q' : ℕ} [NeZero q] [NeZero q']
    (hq : 2 ≤ q) (hm' : m' ≤ m) (hq' : q' ≤ q) {r r' s : ℝ}
    (hnoise : (r / Real.sqrt (2 * (q : ℝ))) ^ 2 + ((s * Real.sqrt (n : ℝ)) / (q' : ℝ)) ^ 2
      ≤ (r' / Real.sqrt (2 * (q' : ℝ))) ^ 2)
    (hHard : LWEHardness n m q (r / Real.sqrt (2 * (q : ℝ)))) : Prop := WitnessObliviousSampler n m' q' (r' / Real.sqrt (2 * (q' : ℝ)))

end Qatlib.Papers.QuantumLWE25.MainResults
