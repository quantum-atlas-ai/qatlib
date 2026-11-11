/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumLWE25.MainResults.CvpReduction.SourceCvpReduction

set_option backward.isDefEq.respectTransparency false

/-!
# QuantumLWE25 — from `|DGS⟩` to `S|LWE⟩^phase` and worst-case hardness (Theorem 56,
Corollary 57)

Fixed arXiv:2310.00644v2.

* c019 Theorem 56, p.31: given an `S|LWE⟩^phase` solver for all pairs `(r,x)` in the
  theorem's range and with `m = 2^{o(n)}` samples, one can prepare the discrete Gaussian
  state `|D_{L,r₀}⟩` up to `2^{-Ω(n)}` error in time `O((m⁴+m³T)poly(n))`.
* c020 Corollary 57, p.31: consequently `GapSVP_γ` and `SIVP_γ` for `γ ∈ Õ(n/α)` are
  solvable in time `poly(n,m,T)`.

The `S|LWE⟩^phase` solver is the black box `SolvesSLwePhase`; the |DGS⟩ oracle is modelled
as an oracle producing Gaussian lattice states. The worst-case problems are stated through
the `SolvesGapSVP`/`SolvesSIVP` correctness predicates on the `LatticeInstance` stub (whose
`lamN`, `lam1Dual`, `lamNDual` fields are uninterpreted real parameters).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumLWE25.MainResults

open scoped BigOperators Matrix
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- **Theorem 56 (Main theorem, from `|DGS⟩` to `S|LWE⟩^phase`), p.31.** Let `L` be an
`n`-dimensional integer lattice, `ε < 2^{-n}` negligible, `q > 10n` of at most `poly(n)`
bits, `α ∈ (0,1/(5√n))` with `αq > 2√n`, `R` exponentially large and `r₀ > 4√n·η_ε(L)/α`.
Assume `S|LWE⟩^phase` is solvable with `m = 2^{o(n)}` samples in time `T` for every pair
`(r,x)` with `αqr₀/√n < r < 2^{2n+2}λ_n(L)` and `x ∈ L*/R`, `dist(x,L*) ≤ αq/r`. Then there
is a quantum algorithm generating a state `2^{-Ω(n)}`-close to
`|D_{L,r₀}⟩ = ∑_{v∈L} ρ_{r₀}(v)|v⟩` in time `O((m⁴+m³T)poly(n))`.

Gap: the initialization step (Theorem 59) and the polynomial number of iterative steps
(Theorem 60) that drive the width down to `r₀`, plus the parameter bookkeeping
`r < 2^{2n+2}λ_n(L)`/`R > 2^{O(n)}λ(...)`, are not formalized. Candidate dependencies:
`iterative_step` (Theorem 60), `lemma64_state_close`, `lemma66_state_close`. -/
def dgs_to_slwe_phase {n m q R : ℕ} [NeZero q] [NeZero R]
    (B : Matrix (Fin n) (Fin n) ℤ)
    {α r0 : ℝ} (hα : 0 < α) (hr0 : 0 < r0) (T : ℝ)
    (hSolve : ∀ (r : ℝ) (x : Fin n → ℝ), 0 < r → SolvesSLwePhase n m q T) : Prop := ∃ Bg : QuantumAlgo (fun _ : ℕ => (Fin n → ℝ) → QState (Fin n → ZMod R))
        (fun _ : ℕ => QState (Fin n → ZMod R)),
      (∀ (O : (Fin n → ℝ) → QState (Fin n → ZMod R)),
        1 - (2 : ℝ) ^ (-(1 : ℝ) * (n : ℝ)) ≤
          Bg.successProb 0 O (fun ψ => ∃ err : ℕ → ℝ, ExpSmall err ∧
            traceDistance (outerProduct ψ)
              (outerProduct (gaussianLatticeStateMod (R := R) B r0))
              ≤ err n)) ∧
      ∃ C kk : ℝ, 0 < C ∧
        Bg.timeCost 0 ≤ C * ((m : ℝ) ^ 4 + (m : ℝ) ^ 3 * T) * (((n : ℝ) + 1) ^ kk)

/-- Correctness predicate for a `GapSVP_γ` decider: `true` only on lattices with
`λ₁(L) ≤ 1`, and `false` on all lattices with `γ·λ₁(L) > 1`. -/
def SolvesGapSVP (γ : ℝ) (n : ℕ) (dec : LatticeInstance n → Bool) : Prop :=
  ∀ L : LatticeInstance n,
    (dec L = true → L.lamN ≤ 1) ∧ (1 < γ * L.lamN → dec L = false)

/-- Correctness predicate for a `SIVP_γ` solver: the returned vector lies in the lattice and
has norm at most `γ·λ_n(L)`. (The `LatticeInstance.lamNDual` field plays the role of
`λ_n(L)`; the stub has no separate `λ_n` field.) -/
def SolvesSIVP (γ : ℝ) (n : ℕ) (f : LatticeInstance n → (Fin n → ℝ)) : Prop :=
  ∀ L : LatticeInstance n, f L ∈ L.carrier ∧ vecNormR (f L) ≤ γ * L.lamNDual

/-- **Corollary 57, p.31.** Under the same assumption as Theorem 56, there are quantum
algorithms solving `GapSVP_γ` and `SIVP_γ` for `γ ∈ Õ(n/α)` in time `poly(n,m,T)`.

The reduction is `|DGS⟩`-to-`GapSVP`/`SIVP` (Lemmas 15, 16, 24, 25 of the paper). Gap: the
`|DGS⟩`-based lattice-problem reductions (Lemma 15/16: `GapSVP_γ` from `|DGS⟩_{O(n/α)}`, and
Lemma 24/25: `SIVP_γ` via the `n`-th minimum) are not in the library, and the time bound is
not tracked. Candidate dependencies: `dgs_to_slwe_phase` (Theorem 56). -/
def gapsvp_sivp_from_slwe {n m q : ℕ} [NeZero q] {α γ : ℝ}
    (hα : 0 < α) (hγ : 1 < γ) (T : ℝ)
    (hSolve : ∀ (r : ℝ) (x : Fin n → ℝ), 0 < r → SolvesSLwePhase n m q T) : Prop := (∃ dec : LatticeInstance n → Bool, SolvesGapSVP γ n dec) ∧
      ∃ f : LatticeInstance n → (Fin n → ℝ), SolvesSIVP γ n f

end Qatlib.Papers.QuantumLWE25.MainResults
