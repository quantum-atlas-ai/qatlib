/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecodingCoreDefs
public import Qatlib.Concepts.CodingDecoding.CssTesters.CssPauli
import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# Classical binary linear codes feeding the CSS builders

A classical binary linear code is carried by its parity-check matrix.
The component provides the codeword kernel, its dimension via rank-nullity,
the minimum-distance certificate interface, a bounded syndrome-decoding
contract, and the bridge into the CSS model together with coordinate
reindexing. No constructor assigns an unproved distance.
-/

namespace Qatlib.Concepts.ErrorCorrection.CssBuild

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open scoped Matrix

/-- A classical binary linear code over the binary field, given by checks. -/
structure ClCode (ι κ : Type*) [Fintype ι] where
  /-- The parity-check matrix whose kernel is the code. -/
  h : Matrix κ ι (ZMod 2)

/-- The codeword space is the kernel of the parity-check map. -/
def codeWords {ι κ : Type*} [Fintype ι] (c : ClCode ι κ) :
    Submodule (ZMod 2) (ι → ZMod 2) :=
  LinearMap.ker c.h.mulVecLin

/-- Membership in the code is vanishing of all parity checks. -/
theorem mem_words {ι κ : Type*} [Fintype ι] (c : ClCode ι κ) (v : ι → ZMod 2) :
    v ∈ codeWords c ↔ c.h *ᵥ v = 0 := by
  simp [codeWords, Matrix.mulVecLin]

/-- The code dimension is the kernel dimension of the check map. -/
noncomputable def codeDim {ι κ : Type*} [Fintype ι] (c : ClCode ι κ) :
    ℕ :=
  Module.finrank (ZMod 2) (codeWords c)

/-- Rank-nullity: kernel dimension plus check rank is the coordinate count. -/
theorem dim_add_rank {ι κ : Type*} [Fintype ι] (c : ClCode ι κ) :
    codeDim c + Matrix.rank c.h = Fintype.card ι := by
  have hnull := c.h.mulVecLin.finrank_range_add_finrank_ker
  have hdom : Module.finrank (ZMod 2) (ι → ZMod 2) = Fintype.card ι := by
    rw [Module.finrank_fintype_fun_eq_card]
  have hrank : Matrix.rank c.h =
      Module.finrank (ZMod 2) ↥(LinearMap.range c.h.mulVecLin) := rfl
  have hker : codeDim c =
      Module.finrank (ZMod 2) ↥(LinearMap.ker c.h.mulVecLin) := rfl
  rw [hker, hrank, add_comm, hnull]
  exact hdom

/-- The minimum Hamming weight over nonzero codewords, as extended natural. -/
noncomputable def minDist {ι κ : Type*} [Fintype ι] (c : ClCode ι κ) : ℕ∞ :=
  sInf {w : ℕ∞ | ∃ v, v ∈ codeWords c ∧ v ≠ 0 ∧ (bitWeight v : ℕ∞) = w}

/-- Any nonzero codeword bounds the minimum distance from above. -/
theorem dist_le_word {ι κ : Type*} [Fintype ι] (c : ClCode ι κ)
    {v : ι → ZMod 2} (hv : v ∈ codeWords c) (hn : v ≠ 0) :
    minDist c ≤ (bitWeight v : ℕ∞) :=
  sInf_le ⟨v, hv, hn, rfl⟩

/-- A lower bound on the distance excludes all low-weight codewords. -/
theorem dist_ge_iff {ι κ : Type*} [Fintype ι] (c : ClCode ι κ) (d : ℕ) :
    (d : ℕ∞) ≤ minDist c ↔ ∀ v ∈ codeWords c, v ≠ 0 → d ≤ bitWeight v := by
  rw [minDist, le_sInf_iff]
  constructor
  · intro h v hv hn
    have hle := h _ ⟨v, hv, hn, rfl⟩
    exact_mod_cast hle
  · rintro h w ⟨v, hv, hn, hw⟩
    subst hw
    exact_mod_cast h v hv hn

/-- Exact distance from an upper witness and a lower certificate. -/
theorem dist_eq {ι κ : Type*} [Fintype ι] (c : ClCode ι κ) (d : ℕ)
    {w : ι → ZMod 2} (hw : w ∈ codeWords c) (hn : w ≠ 0) (hwt : bitWeight w = d)
    (hlow : ∀ v ∈ codeWords c, v ≠ 0 → d ≤ bitWeight v) :
    minDist c = (d : ℕ∞) := by
  refine le_antisymm ?_ ((dist_ge_iff c d).mpr hlow)
  have hle := dist_le_word c hw hn
  rw [hwt] at hle
  exact_mod_cast hle

/-- A syndrome decoder corrects every error of weight at most `t`. -/
def BoundDecode {ι κ : Type*} [Fintype ι] (c : ClCode ι κ)
    (dec : (κ → ZMod 2) → (ι → ZMod 2)) (t : ℕ) : Prop :=
  ∀ e, bitWeight e ≤ t → dec (c.h *ᵥ e) = e

/-- A self-orthogonal classical check matrix yields a CSS code with both roles. -/
def toCss {ι κ : Type*} [Fintype ι] (c : ClCode ι κ)
    (hself : c.h * c.hᵀ = 0) : CssData ι κ κ where
  hX := c.h
  hZ := c.h
  hcompat := hself

/-- Relabel the coordinates of a CSS code by a permutation. -/
def reindexCss {ι κX κZ : Type*} [Fintype ι]
    (d : CssData ι κX κZ) (p : ι ≃ ι) : CssData ι κX κZ where
  hX := d.hX.submatrix (Equiv.refl κX) p
  hZ := d.hZ.submatrix (Equiv.refl κZ) p
  hcompat := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      Equiv.refl_apply, Matrix.zero_apply]
    have hz : ∑ k, d.hX i k * d.hZ j k = 0 := by
      have h := congrFun₂ d.hcompat i j
      simpa [Matrix.mul_apply, Matrix.transpose_apply] using h
    calc ∑ k, d.hX i (p k) * d.hZ j (p k)
        = ∑ k, d.hX i k * d.hZ j k :=
          Equiv.sum_comp p (fun k => d.hX i k * d.hZ j k)
      _ = 0 := hz

end Qatlib.Concepts.ErrorCorrection.CssBuild
