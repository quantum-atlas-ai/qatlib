/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CircDepthShen26.ShortTimeBlock.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Shared vocabulary for the geometric depth lower bound

Fixed source: arXiv:2610.01839v2, Sections 6-7, Eqs. (10)-(11), (119)-(147).
This file fixes the objects appearing in the lower-bound claims:

* `CausalCone C ι near r` packages the geometric circuit model's causal-cone
  property: a state whose support lies in `S` produces, after the circuit and
  the ancilla embedding, a state supported within `near`-distance `r` of `S`.
  The paper's hypothesis `dist(S,B) > a_cone` is expressed by asking that no
  `B`-site is `near`-close to any `S`-site.
* `heisenbergEvolveH H t O` is `e^{iHt} O e^{-iHt}`, the Heisenberg evolution
  `τ_t^Λ` of Lemma 24.
* `SupportWithin O X` says that `O` acts only on the sector supported on `X`.
* `expTail b x` is the exponential tail `∑_{q ≥ b} x^q/q!` used in Lemmas 18, 24.
* `XXZInstance D n` records an XXZ-type local Hamiltonian together with the
  model parameters `J, T, Δ, Δ₀` used in Theorems 3 and Lemmas 21; the field
  `isXXZ` carries the (unmodeled) statement that `H` is the uniform nearest-
  neighbor XXZ Hamiltonian of the source, which the formalization keeps as an
  explicit hypothesis rather than rebuilding the lattice.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.CircDepthShen26.ShortTimeBlock

namespace Qatlib.Papers.CircDepthShen26.DepthLowerBound

open Matrix
open scoped BigOperators

/-- Causal-cone property of a geometric circuit: states supported on `S` are
mapped (after the ancilla embedding `ι`) to states supported in the `r`-neighborhood
of `S`, where `near i j r` means that `j` lies within distance `r` of `i`. -/
def CausalCone {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ}
    (C : Circuit (Fin N)) (ι : Matrix (Fin N) I ℂ)
    (near : I → I → ℝ → Prop) (r : ℝ) : Prop :=
  ∀ (S : Finset I) (ψ : I → ℂ), (∀ i, ψ i ≠ 0 → i ∈ S) →
    ∀ j : I, (ιᴴ *ᵥ (C.matrix *ᵥ (ι *ᵥ ψ))) j ≠ 0 → ∃ i ∈ S, near i j r

/-- Heisenberg evolution `τ_t^H(O) = e^{iHt} O e^{-iHt}` of Lemma 24. -/
def heisenbergEvolveH {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (t : ℝ) (O : Matrix I I ℂ) : Matrix I I ℂ :=
  evolutionH H (-t) * O * evolutionH H t

/-- An operator acts only on the sector supported on `X`. -/
def SupportWithin {I : Type*} [Fintype I] (O : Matrix I I ℂ) (X : Finset I) : Prop :=
  ∀ v : I → ℂ, (∀ i ∈ X, v i = 0) → O *ᵥ v = 0

/-- The exponential tail `∑_{q ≥ b} x^q / q!`. -/
def expTail (b : ℕ) (x : ℝ) : ℝ :=
  ∑' q : ℕ, if b ≤ q then x ^ q / (Nat.factorial q : ℝ) else 0

/-- An XXZ-type local Hamiltonian `H_XXZ` on `n` sites with anisotropy `Δ` and
local strength `J`, together with the fixed time `T`.  The predicate `isXXZ`
is the (unmodeled) assertion that `H` is the uniform nearest-neighbor XXZ
Hamiltonian on the `D`-dimensional periodic lattice of side `ℓ_sys`; the
lower-bound statements are conditional on it. -/
structure XXZInstance (D n : ℕ) where
  /-- The Hamiltonian matrix. -/
  H : Matrix (Fin n) (Fin n) ℂ
  /-- Hermiticity of `H`. -/
  herm : Qatlib.Papers.CircDepthShen26.ShortTimeBlock.IsHermitian H
  /-- Anisotropy parameter. -/
  Δ : ℝ
  /-- Bound on the anisotropy. -/
  Δ0 : ℝ
  /-- Local interaction strength. -/
  J : ℝ
  /-- Simulation time. -/
  T : ℝ
  /-- The anisotropy bound of Theorem 3. -/
  hΔ : |Δ| ≤ Δ0
  /-- The Hamiltonian is the source's uniform nearest-neighbor XXZ family. -/
  isXXZ : Prop

end Qatlib.Papers.CircDepthShen26.DepthLowerBound
