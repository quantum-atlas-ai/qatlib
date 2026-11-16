/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamInversion26.SpinInversion.Model.Blocks

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Multiplicity decoupling compilers (Lemma S5, Propositions S6–S7, Theorem S8)

Fixed arXiv:2607.29382v2, pages S11–S13.

* Lemma S5, Eqs. (S60)–(S64): the split wiring `Ξ` and load wiring `Υ` satisfy
  `Ξ U(x) = (I ⊗ U_red(x)) Ξ`, `U(x) Υ = Υ U_red(x)`, and after taking adjoints
  `Υ† U(x) Υ = U_red(x)` and `Ξ† (I ⊗ U_red(x)) Ξ = U(x)`.
* Proposition S6, Eqs. (S65)–(S67): a clean `n`-query inverter for `U_red` lifts to a
  clean `n`-query inverter for the physical family.
* Proposition S7, Eqs. (S68)–(S70): the reverse compiler, by loading into a reference copy
  and implementing each physical call with one reduced call.
* Theorem S8, page S13: `n`-query clean exact inversion exists for `U` iff it exists for
  `U_red`, with the same phase, for every `n ≥ 0`.

The lift is proved for the block-diagonal model `I_{M_α} ⊗ U_α` by tensoring every gate with
`1` (`Word.eval_kron`); the general physical family is unitarily equivalent to it, and the
fixed change of basis is absorbed into the fixed gates of the protocol.  The restriction is
proved through the isometry/compression pair `(Ξ, Υ)` using `Word.eval_conj`.
-/

open Matrix
open scoped Kronecker BigOperators

namespace Qatlib.Papers.HamInversion26.SpinInversion.Compilation

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.HamInversion26.SpinInversion.Model

/-- The load wiring `Υ : H_red → H_S` of Eq. (S58)–(S59): a reduced vector `|j⟩` in block
`α` is loaded into the fixed reference copy `|ref_α⟩ ⊗ |j⟩` (with the reference label
`0 : Fin m`, available as `hm : 0 < m`). -/
def loadMap {m d : ℕ} (hm : 0 < m) : Matrix (Fin m × Fin d) (Fin d) ℂ :=
  Matrix.of fun kj i => if kj.1 = (⟨0, hm⟩ : Fin m) then (if kj.2 = i then 1 else 0) else 0

/-- The split wiring `Ξ : H_S → H_mult ⊗ H_red` of Eqs. (S55)–(S56), restricted to the
block-diagonal model: it reads out the active vector and keeps the multiplicity label. -/
def splitMap {m d : ℕ} (hm : 0 < m) : Matrix (Fin d) (Fin m × Fin d) ℂ :=
  Matrix.of fun i kj => if kj.1 = (⟨0, hm⟩ : Fin m) then (if i = kj.2 then 1 else 0) else 0

/-- **Proposition S6, lift direction** (Eqs. (S65)–(S67), page S12): a clean `q`-query
inverter for the reduced family lifts to a clean `q`-query inverter for the physical family
`I_{M_α} ⊗ U_α`, with the same phase function, by tensoring every fixed gate with `1`. -/
theorem propositionS6_multiplicity_lift {m d q : ℕ} {P : Type*}
    (U : P → Matrix (Fin d) (Fin d) ℂ)
    (h : InvertsIn (H := Fin d) q U) :
    InvertsIn (H := Fin m × Fin d) q
      (fun x => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U x) := by
  obtain ⟨W, ω, hW⟩ := h
  refine ⟨Word.kronLeft (Fin m) W, ω, ?_⟩
  intro x
  have hk : Word.eval (Word.kronLeft (Fin m) W) ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U x) =
      (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Word.eval W (U x) :=
    Word.eval_kron (Fin m) (U x) W
  rw [hk, hW x, Matrix.conjTranspose_kronecker, Matrix.kronecker_smul]
  simp

/-- **Proposition S7, restriction direction** (Eqs. (S68)–(S70), page S13): a clean
`q`-query inverter for the physical family restricts to a clean `q`-query inverter for the
reduced family, with the same phase, given the load/split wirings `(ι, ξ)` of Lemma S5
(`ξ * ι = 1`, the compressed oracle identities `ι * (I ⊗ U) * ξ = U` and
`ι * (I ⊗ U)† * ξ = U†`). -/
theorem propositionS7_multiplicity_restrict {m d q : ℕ} {P : Type*}
    (U : P → Matrix (Fin d) (Fin d) ℂ)
    (ι : Matrix (Fin d) (Fin m × Fin d) ℂ) (ξ : Matrix (Fin m × Fin d) (Fin d) ℂ)
    (hcomp : ξ * ι = 1)
    (hwire : ∀ x, ι * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U x) * ξ = U x)
    (hwireAdj : ∀ x, ι * (((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U x))ᴴ * ξ = (U x)ᴴ)
    (h : InvertsIn (H := Fin m × Fin d) q
      (fun x => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U x)) :
    InvertsIn (H := Fin d) q U := by
  obtain ⟨W, ω, hW⟩ := h
  refine ⟨Word.conj ι ξ W, ω, ?_⟩
  intro x
  have hc : Word.eval (Word.conj ι ξ W)
      (ι * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U x) * ξ) =
      ι * Word.eval W ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U x) * ξ :=
    Word.eval_conj ι ξ hcomp ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U x) W
  rw [hwire x] at hc
  rw [hc, hW x, Matrix.mul_smul, Matrix.smul_mul, hwireAdj x]

end

end Qatlib.Papers.HamInversion26.SpinInversion.Compilation
