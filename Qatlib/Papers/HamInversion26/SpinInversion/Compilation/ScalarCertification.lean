/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamInversion26.SpinInversion.Model.Blocks
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma S16, first step: one extra forward call closes a local inverter to a scalar gadget

Supplement of arXiv:2607.29382v2, Lemma S16, page S17, and Corollary S17, page S17.  A local
block inverter `P_α` using `ℓ_α` calls leaves the phase `ρ_α(x)`; the paper turns it into a
scalar gadget `S_α` using `ℓ_α + 1` calls with `S_α[U_red](x) = ρ_α(x) · I`.

In the query-word model of `Qatlib.Papers.HamInversion26.SpinInversion.Model` a
`q`-query clean circuit is a word (`Word.eval`) and the two certificates are
`Model.LocalInverter` and `Model.ScalarCert`.  This module proves the algebraic core of
Lemma S16: given a unitary oracle family `U` (the hypothesis `hU` makes the paper's implicit
unitarity explicit, since the model itself does not require it) and a clean `ℓ`-query
inverter with phase `φ`, the word obtained by prepending the identity gate followed by one
more oracle call evaluates to `φ(x) · I`:

`step 1 W` evaluates as `I · U(x) · (φ(x) U(x)ᴴ) = φ(x) · (U(x) U(x)ᴴ) = φ(x) · I`.

So the extra call is exactly the one counted by `Model.qauto` (`Σ_α (ℓ_α + 1) − 1` over the
blocks, one per block plus the seam).  The per-sector assembly over several blocks, and the
`Π_α ρ_α(x)` product of Corollary S17, are not part of this module.
-/

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.HamInversion26.SpinInversion.Compilation

open Qatlib.Papers.HamInversion26.SpinInversion.Model

set_option autoImplicit false
noncomputable section

/-- **Lemma S16, scalar-gadget step** (page S17): a clean `ℓ`-query local inverter for `U`
with phase `φ` closes to a clean `ℓ + 1`-query scalar gadget for the same phase, provided the
oracle family is unitary (`U(x) U(x)ᴴ = 1`). -/
theorem scalarCert_of_localInverter {d ℓ : ℕ} {P : Type*}
    (U : P → Matrix (Fin d) (Fin d) ℂ) (φ : P → ℂ)
    (hU : ∀ x, U x * (U x)ᴴ = 1) (h : LocalInverter ℓ U φ) :
    ScalarCert (ℓ + 1) U φ := by
  obtain ⟨W, hW⟩ := h
  refine ⟨Word.step (1 : Matrix (Fin d) (Fin d) ℂ) W, fun x => ?_⟩
  rw [Word.eval_step, hW x, Matrix.one_mul, Matrix.mul_smul, hU x]

end

end Qatlib.Papers.HamInversion26.SpinInversion.Compilation
