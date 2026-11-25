/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamInversion26.SpinInversion.Compilation.MultiplicityCompilation
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma S5, compressed form: the load wiring cancels the multiplicity register

Supplement of arXiv:2607.29382v2, Lemma S5, Eqs. (S60)–(S64), pages S11–S12.  The load
wiring `Υ` (`Qatlib.Papers.HamInversion26.SpinInversion.Compilation.loadMap`) sends a reduced
vector `|j⟩` to the fixed reference copy `|ref⟩ ⊗ |j⟩` of the multiplicity register, and the
split wiring `Ξ` reads the reference copy back out.  The paper uses `Υ† (I ⊗ U_red(x)) Υ = U(x)`
to supply the two wiring hypotheses `hwire`, `hwireAdj` of Proposition S7.

This module proves the wiring identities in the published block model, entrywise and for an
arbitrary matrix `U` (no unitarity is needed):

* `loadMap_apply`, `splitMap_apply` — the entries of the two wirings;
* `kronecker_mul_loadMap` — `(I_{M} ⊗ U) Υ = Υ U`, the load-side intertwiner of Lemma S5;
* `loadMap_conjTranspose_mul_loadMap` and `splitMap_mul_loadMap` — `Υ† Υ = 1` on the full
  register and `Ξ Υ = 1` on the reduced register, so `Υ` is an isometry with adjoint `Ξ` on
  the reference copy;
* `loadMap_conjTranspose_mul_kronecker_mul_loadMap` — the compressed identity
  `Υ† (I_{M} ⊗ U) Υ = U` of Eq. (S64), which is exactly `hwire`;
* `loadMap_conjTranspose_mul_conjTranspose_kronecker_mul_loadMap` — its adjoint, which is
  `hwireAdj`.

The block identity `Ξ† (I ⊗ U_red(x)) Ξ = U(x)` of Eqs. (S60)–(S63) lives on the physical
space `H_S = ⊕_α (M_α ⊗ V_α)` with `Ξ` a map into `H_mult ⊗ H_red`; that space is not the
single-block model `Fin m × Fin d` used here, so only the load-side compression is covered.
The converse direction of Proposition S7 is not formalised: its published hypothesis
`ξ * ι = 1` is an identity on the *full* space, whereas the wirings of this model satisfy
`ξ * ι` = the projection onto the reference copy and `ι * ξ = 1` on the reduced space.
-/

open Matrix
open scoped Kronecker BigOperators

namespace Qatlib.Papers.HamInversion26.SpinInversion.Compilation

open Qatlib.Papers.HamInversion26.SpinInversion.Compilation
open Qatlib.Papers.HamInversion26.SpinInversion.Model

set_option autoImplicit false
noncomputable section

/-- Entry of the load wiring: `Υ` maps `|i⟩` to the reference copy `|ref, i⟩`. -/
theorem loadMap_apply {m d : ℕ} (hm : 0 < m) (a : Fin m) (b i : Fin d) :
    loadMap (m := m) (d := d) hm (a, b) i =
      if a = (⟨0, hm⟩ : Fin m) then (if b = i then 1 else 0) else 0 :=
  rfl

/-- Entry of the split wiring: `Ξ` reads out the multiplicity label and the reduced index. -/
theorem splitMap_apply {m d : ℕ} (hm : 0 < m) (i : Fin d) (a : Fin m) (b : Fin d) :
    splitMap (m := m) (d := d) hm i (a, b) =
      if a = (⟨0, hm⟩ : Fin m) then (if i = b then 1 else 0) else 0 :=
  rfl

/-- Entry of the lifted family `I_{M} ⊗ U` in the block model. -/
theorem kronecker_one_apply {m d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ)
    (a c : Fin m) (b e : Fin d) :
    ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U) (a, b) (c, e) =
      if a = c then U b e else 0 := by
  rw [Matrix.kronecker_apply, Matrix.one_apply]
  by_cases h : a = c
  · subst h; simp
  · simp [h]

/-- The load wiring is an isometry: `Υ† Υ = 1` on the full register. -/
theorem loadMap_conjTranspose_mul_loadMap {m d : ℕ} (hm : 0 < m) :
    (loadMap (m := m) (d := d) hm)ᴴ * loadMap (m := m) (d := d) hm = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply,
    Finset.sum_eq_single ((⟨0, hm⟩ : Fin m), i)]
  · rw [Matrix.conjTranspose_apply, loadMap_apply, loadMap_apply]
    split_ifs with h <;> simp_all
  · rintro ⟨c, e⟩ - hk
    rw [Matrix.conjTranspose_apply, loadMap_apply]
    split_ifs with hc he <;> simp_all
  · intro h
    simp at h

/-- The load wiring is an isometry on the reduced register followed by the split wiring:
`Ξ Υ = 1`. -/
theorem splitMap_mul_loadMap {m d : ℕ} (hm : 0 < m) :
    splitMap (m := m) (d := d) hm * loadMap (m := m) (d := d) hm = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply,
    Finset.sum_eq_single ((⟨0, hm⟩ : Fin m), i)]
  · rw [splitMap_apply, loadMap_apply]
    split_ifs with h <;> simp_all
  · rintro ⟨c, e⟩ - hk
    rw [splitMap_apply, loadMap_apply]
    split_ifs with hc he <;> simp_all
  · intro h
    simp at h

/-- **Lemma S5, load-side intertwiner** (Eq. (S63), page S12): the loaded copy of `I ⊗ U`
acts on the image of `Υ` exactly as `U` does, `(I_{M} ⊗ U) Υ = Υ U`. -/
theorem kronecker_mul_loadMap {m d : ℕ} (hm : 0 < m) (U : Matrix (Fin d) (Fin d) ℂ) :
    ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U) * loadMap (m := m) (d := d) hm =
      loadMap (m := m) (d := d) hm * U := by
  ext k j
  obtain ⟨a, b⟩ := k
  have hlhs : (((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U) * loadMap (m := m) (d := d) hm) (a, b) j =
      (if a = (⟨0, hm⟩ : Fin m) then U b j else 0) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single ((⟨0, hm⟩ : Fin m), j)]
    · rw [kronecker_one_apply, loadMap_apply]
      split_ifs with h <;> simp_all
    · rintro ⟨c, e⟩ - hk
      rw [kronecker_one_apply, loadMap_apply]
      by_cases hc : c = (⟨0, hm⟩ : Fin m)
      · have he : e ≠ j := by
          intro h
          exact hk (by rw [hc, h])
        simp [hc, he]
      · simp [hc]
    · intro h
      simp at h
  have hrhs : (loadMap (m := m) (d := d) hm * U) (a, b) j =
      (if a = (⟨0, hm⟩ : Fin m) then U b j else 0) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [loadMap_apply]
      simp
    · intro e _ he
      rw [loadMap_apply]
      split_ifs with _ hbe
      · exact absurd hbe.symm he
      · simp
      · simp
    · intro h
      simp at h
  rw [hlhs, hrhs]

/-- **Lemma S5, compressed form** (Eq. (S64), page S12): `Υ† (I_{M} ⊗ U) Υ = U` for an
arbitrary matrix `U`. -/
theorem loadMap_conjTranspose_mul_kronecker_mul_loadMap {m d : ℕ} (hm : 0 < m)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    (loadMap (m := m) (d := d) hm)ᴴ * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U) *
      loadMap (m := m) (d := d) hm = U := by
  rw [Matrix.mul_assoc, kronecker_mul_loadMap hm U, ← Matrix.mul_assoc,
    loadMap_conjTranspose_mul_loadMap hm, Matrix.one_mul]

/-- **Lemma S5, compressed form for the adjoint** (page S12): `Υ† (I_{M} ⊗ U)ᴴ Υ = Uᴴ`, the
`hwireAdj` hypothesis of Proposition S7.  It is the adjoint of
`loadMap_conjTranspose_mul_kronecker_mul_loadMap`. -/
theorem loadMap_conjTranspose_mul_conjTranspose_kronecker_mul_loadMap {m d : ℕ} (hm : 0 < m)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    (loadMap (m := m) (d := d) hm)ᴴ * (((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U))ᴴ *
      loadMap (m := m) (d := d) hm = Uᴴ := by
  have h := congrArg Matrix.conjTranspose (loadMap_conjTranspose_mul_kronecker_mul_loadMap hm U)
  simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using h

end

end Qatlib.Papers.HamInversion26.SpinInversion.Compilation
