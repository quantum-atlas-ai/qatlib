/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MetropWeak24.SamplerImpl.NormTheory

set_option backward.isDefEq.respectTransparency false

/-!
# Weak-Measurement Quantum Metropolis Sampler Model

This module defines the shared parameters, banded quantum phase estimation (BQPE)
outcome space, jump-algebra completeness predicate, and `SamplerModel` record used
across the weak-measurement quantum Metropolis analysis.

## Main statements

* `w`, `rβH`, `tmixBound`: BQPE grid spacing, register-size threshold, and mixing-time bound.
* `BqpeOutcome`, `bitSet`, `bitsVal`, `elseSet`: three-way BQPE branch vocabulary.
* `braket`, `JumpAlgebraFull`: matrix-element form and unital jump-algebra generation.
* `SamplerModel`, `SamplerModel.pow`: bundled sampler operators, generators, and iterated steps.

## References

* [Jiang and Irani, 2024][JiangIrani2024MetropWeak], Sections 4--8, pp. 12--19.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.MetropWeak24.SamplerImpl.Model

open Qatlib.Papers.MetropWeak24.SamplerImpl
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-! ## Parameters occurring in the paper -/

/-- The BQPE grid spacing parameter `w = κ_H · 2^{-r}`. -/
def w (κH : ℝ) (r : ℕ) : ℝ := κH * (2 : ℝ) ^ (-(r : ℝ))

/-- The register-size threshold `r_βH = 1 + log κ_H + log β`. -/
def rβH (κH β : ℝ) : ℝ := 1 + Real.log κH + Real.log β

/-- The mixing-time upper bound `(1 / Υ) (log(1 / ε) + n log 2 / 2 + log |ρ|_σ^2 / 2)`. -/
def tmixBound {n : ℕ} (Υ ε : ℝ) (σ ρ : QOp n) : ℝ :=
  (1 / Υ) * (Real.log (1 / ε) + (n : ℝ) * Real.log 2 / 2 +
    Real.log (NormTheory.sigmaSq σ ρ) / 2)

/-! ## The three-way BQPE branch set `T = {0, 1, else}` -/

/-- Outcome type `T = {0, 1, else}` of banded quantum phase estimation. -/
inductive BqpeOutcome
  | zero
  | one
  | other
  deriving DecidableEq, Fintype, Repr

/-- The singleton subset `{0}` or `{1}` of the BQPE branch set. -/
def bitSet (b : Bool) : Set BqpeOutcome :=
  if b then {BqpeOutcome.one} else {BqpeOutcome.zero}

/-- The real numerical value `0` or `1` of a Boolean bit. -/
def bitsVal (b : Bool) : ℝ := if b then 1 else 0

/-- The rejected `"else"` branch `{other}` of the BQPE branch set. -/
def elseSet : Set BqpeOutcome := {BqpeOutcome.other}

/-! ## Bilinear form and the full-algebra hypothesis -/

/-- Matrix element `⟨u| A |v⟩ = ∑_i conj(u_i) (A v)_i`. -/
def braket {D : ℕ} (u : Fin D → ℂ) (A : Operator D) (v : Fin D → ℂ) : ℂ :=
  ∑ i, star (u i) * (A.mulVec v) i

/-- Jump operators generate the full `n`-qubit operator algebra as a unital algebra. -/
def JumpAlgebraFull {n : ℕ} {ι : Type*} (S : ι → QOp n) : Prop :=
  ∀ A : QOp n, ∃ (k : ℕ) (c : Fin k → ℂ) (p : Fin k → List ι),
    A = ∑ i, c i • ((p i).foldr (fun x acc => S x * acc) 1)

/-! ## The constructed objects -/

/-- Bundled parameters, states, one-step channel pieces, Lindblad drift, remainders,
spectral gap, and mixing time of the weak-measurement quantum Metropolis sampler. -/
structure SamplerModel (n : ℕ) where
  /-- The `n`-qubit Hamiltonian `H`. -/
  H : QOp n
  /-- The inverse temperature `β`. -/
  β : ℝ
  /-- A bound `κ_H` on the spectral norm of `H`. -/
  κH : ℝ
  /-- The BQPE precision parameter `g`. -/
  g : ℕ
  /-- The BQPE register-size parameter `r`. -/
  r : ℕ
  /-- The step size `τ`. -/
  τ : ℝ
  /-- The Gibbs state `ρ_β = e^{-βH} / tr(e^{-βH})`. -/
  rhoBeta : QOp n
  /-- The truncated Gibbs state `ρ_{β0}`. -/
  rhoBeta0 : QOp n
  /-- The fixed point `ρ_𝓛`. -/
  rhoL : QOp n
  /-- The one-step map `𝓔[τ]`. -/
  E : SuperOp n
  /-- The post-selected component `𝓔_C^(a)`. -/
  Ea : SuperOp n
  /-- The accepted-branch component `𝓔_C^(b)`. -/
  Eb : SuperOp n
  /-- The rejected-branch component `𝓔_C^(r)`. -/
  Er : SuperOp n
  /-- The Lindblad drift `𝓛_C`. -/
  L : SuperOp n
  /-- The drift part `𝓜_C^(a)` of `𝓔_C^(a)`. -/
  Ma : SuperOp n
  /-- The rejected drift part `𝓜_C^(rr)`. -/
  Mrr : SuperOp n
  /-- The `τ`-dependent remainder `𝓙[τ]`. -/
  J : ℝ → SuperOp n
  /-- The `τ`-dependent remainder `𝓙_C^(b)[τ]`. -/
  Jb : ℝ → SuperOp n
  /-- The `τ`-dependent remainder `𝓙_C^(r)[τ]`. -/
  Jr : ℝ → SuperOp n
  /-- The spectral gap `Υ` of the symmetrized generator `𝓛^{(s)}`. -/
  Upsilon : ℝ
  /-- The mixing time `t_mix(𝓛, ε)`. -/
  tmix : ℝ

namespace SamplerModel

variable {n : ℕ}

/-- Iterating the one-step map `𝓔` exactly `k` times (`𝓔^k`). -/
def pow (M : SamplerModel n) : ℕ → SuperOp n
  | 0 => LinearMap.id
  | (k + 1) => M.E.comp (pow M k)

end SamplerModel

end Qatlib.Papers.MetropWeak24.SamplerImpl.Model
