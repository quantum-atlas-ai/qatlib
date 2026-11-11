/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabEquiv04.MainResults.Model.ComputationDefs

/-!
# AdiabEquiv04 — spectral lemmas for the two-local grid construction (Lemmas 4.6, 4.7)

Statements of the two spectral lemmas of Section 4.5 of
arXiv:quant-ph/0405098v2 for the six-state-particle Hamiltonian `H''(s)` on the
two-dimensional grid:

* Lemma 4.6 (p. 26): for all `s ∈ [0,1]`, the compression `H''_S(s)` to the
  legal-clock subspace `S` has spectral gap `Ω(L⁻³)`, and the ground state of
  `H''_{S,final}` is the history state `|η⟩`;
* Lemma 4.7 (p. 26): for all `s ∈ [0,1]`, `Δ(H''(s)) = Ω(L⁻³)`, and the ground
  state of `H''(1)` is `ε`-close to `|η⟩`.

The concrete term-by-term grid Hamiltonian of Section 4.4 (32 families of
two-local nearest-neighbour terms on six-state particles) is not expanded in
Lean; the lemmas are stated for an abstract Hamiltonian family `H''` on the
joint computation/clock basis together with the *structural* hypothesis
verified in Claims 4.3 and 4.4: on every legal subspace block, `H''_S(s)` is
unitarily equivalent to the compressed three-local Hamiltonian `H_S(s)` of
Section 3.2.  This is exactly the paper's reduction ("due to the remark at the
end of Subsection 3.1.4, Lemma 3.12 holds here as well"), and it keeps the
statements non-vacuous: the spectral gap and the ground-state identification
are conclusions, not assumptions.  The history state is transported to the
grid by the same isometry `V` that identifies the two Hamiltonians, which is
why the conclusions quantify over such a `V`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.AdiabEquiv04.MainResults.TwoLocal

open Qatlib.Papers.AdiabEquiv04.MainResults

open Qatlib.Papers.AdiabEquiv04.MainResults.Model

/-- Compression of a family of Hamiltonians to the subspace described by `S`. -/
def compressFam {ι : Type} [Fintype ι] [DecidableEq ι] (S : ι → Prop)
    [DecidablePred S] (H : ℝ → Hamiltonian ι) (s : ℝ) : Hamiltonian ι :=
  ⟨compress S (H s), compress_isHermitian S (H s)⟩

/-- **Lemma 4.6** (arXiv:quant-ph/0405098v2, p. 26), recorded statement.  For
any `0 ≤ s ≤ 1`, the compression `H''_S(s)` to the legal-clock subspace `S` has
spectral gap `Ω(L⁻³)`; moreover the ground state of `H''_{S,final}` is the image
of the history state `|η⟩` under the isometry `V` identifying `H''_S` with the
compressed three-local Hamiltonian.

The hypothesis `hiso` records the paper's verification (Claims 4.3 and 4.4 plus
the remark at the end of Subsection 3.1.4) that each block of `H''_S` agrees,
up to a unitary change of basis, with the compressed three-local Hamiltonian
`H_S(s)` of Section 3.2. -/
def lemma_4_6_section4_gapStatement : Prop :=
  ∀ (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n)
    (S : TotalBasis n L → Prop) [DecidablePred S]
    (H : ℝ → Hamiltonian (TotalBasis n L))
    (hiso : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∃ (V : Matrix (TotalBasis n L) (TotalBasis n L) ℂ),
        Vᴴ * V = (1 : Matrix (TotalBasis n L) (TotalBasis n L) ℂ) ∧
        (compressFam S H s).mat = V * (HS n L hL2 gates s).mat * Vᴴ),
    (∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      GapAtLeast (compressFam S H s) (c / ((L : ℝ) + 1) ^ 3)) ∧
    ∃ (V : Matrix (TotalBasis n L) (TotalBasis n L) ℂ),
      Vᴴ * V = (1 : Matrix (TotalBasis n L) (TotalBasis n L) ℂ) ∧
      (compressFam S H 1).mat = V * (HS n L hL2 gates 1).mat * Vᴴ ∧
      IsGroundVector (compressFam S H 1) (V *ᵥ historyState (L := L) gates)

/-- **Lemma 4.7** (arXiv:quant-ph/0405098v2, p. 26), recorded statement.  For
all `s ∈ [0,1]`, `Δ(H''(s)) = Ω(L⁻³)`; moreover the ground state of `H''(1)` is
`ε`-close (in ℓ2 distance) to the history state `|η⟩`.

The hypotheses decompose `H''(s) = H₁(s) + H₂(s)` exactly as in the proof of
Lemma 3.18: `H₂(s)` is the clock penalty `J·H_clock` (zero on `S`, `≥ J` on
`S⊥`) and `H₁(s)` collects the remaining terms (`K` bounds `|⟨H₁⟩|`).  The
restricted gap and the final ground state are provided by Lemma 4.6 via `hS`
and `hSg`. -/
def lemma_4_7_section4_full_gapStatement : Prop :=
  ∀ (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n)
    (ε J K : ℝ) (hε : 0 < ε) (hJ : 2 * K < J) (hK0 : 0 ≤ K)
    (S : TotalBasis n L → Prop) [DecidablePred S]
    (H H₁ H₂ : ℝ → Hamiltonian (TotalBasis n L))
    (hdecomp : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (H s).mat = (H₁ s).mat + (H₂ s).mat)
    (hzero : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      compress S (H₂ s) = (0 : Matrix (TotalBasis n L) (TotalBasis n L) ℂ))
    (hpos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ ψ : Vector (TotalBasis n L),
      IsNormalized ψ → (∀ i : TotalBasis n L, S i → ψ i = 0) →
      J ≤ rayleigh (H₂ s).mat ψ)
    (hK : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ ψ : Vector (TotalBasis n L),
      IsNormalized ψ → |rayleigh (H₁ s).mat ψ| ≤ K)
    (hS : ∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      GapAtLeast (compressFam S H s) (c / ((L : ℝ) + 1) ^ 3))
    (hSg : ∃ (V : Matrix (TotalBasis n L) (TotalBasis n L) ℂ),
      Vᴴ * V = (1 : Matrix (TotalBasis n L) (TotalBasis n L) ℂ) ∧
      (compressFam S H 1).mat = V * (HS n L hL2 gates 1).mat * Vᴴ ∧
      IsGroundVector (compressFam S H 1) (V *ᵥ historyState (L := L) gates)),
    (∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      GapAtLeast (H s) (c / ((L : ℝ) + 1) ^ 3)) ∧
    ∃ ψ : Vector (TotalBasis n L), IsGroundVector (H 1) ψ ∧
      PhaseClose ψ (historyState (L := L) gates) ε

end Qatlib.Papers.AdiabEquiv04.MainResults.TwoLocal
