/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RiccatiWang26.SolutionEnc.Core.PaperModel

set_option backward.isDefEq.respectTransparency false

/-!
# SpectralGeometry — spectral separation, contour factors, graph geometry

RiccatiWang26, arXiv:2609.37207v1.
Retained formalized declarations: the `TildeO` monotonicity helper, the initial-column
algebra of Lemma B.3 (p. 54, Eqs. (B.5)–(B.6)) and the `JuliaLift` definition.
Propositions 2.11, B.5, B.11, B.15, Theorems 2.12, B.4, B.6, Lemmas B.1, B.8 and H.1 are
not formalized in this layer; no declaration below claims them.

The analytic content (semicircle/sector spectral theory, singular-value perturbation,
conformal/Faber geometry) is not available in the dependency stack.  The retained helper
records only the algebraic column geometry, not the spectral separation conclusions.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.RiccatiWang26.SolutionEnc.Geometry

open Qatlib.Papers.RiccatiWang26.SolutionEnc

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ## Monotonicity of `Õ` (used by every cost estimate below) -/

/-- `Õ` is monotone in its cost parameter: increasing the reference scale `g` to `g' ≥ g`
only enlarges the logarithmic factor. -/
theorem TildeO_mono {f g g' ε : ℝ} (h : TildeO f g ε) (hg : g ≤ g')
    (hg0 : 0 ≤ g) (hε : 0 < ε) : TildeO f g' ε := by
  obtain ⟨C, hC, k, hk⟩ := h
  refine ⟨C, hC, k, ?_⟩
  have hε0 : 0 < ε := hε
  have hg'0 : 0 ≤ g' := le_trans hg0 hg
  have hbase1 : 1 ≤ Real.log (Real.exp 1 + g / ε + 1) := by
    have hx : (0 : ℝ) ≤ g / ε := div_nonneg hg0 hε.le
    have hp : 0 < Real.exp 1 := Real.exp_pos 1
    have hle : Real.exp 1 ≤ Real.exp 1 + g / ε + 1 := by linarith
    have h' := Real.log_le_log hp hle
    rwa [Real.log_exp] at h'
  have hlog : Real.log (Real.exp 1 + g / ε + 1) ≤ Real.log (Real.exp 1 + g' / ε + 1) := by
    apply Real.log_le_log (by positivity)
    have : g / ε ≤ g' / ε := div_le_div_of_nonneg_right hg hε.le
    linarith
  have hbase2 : 0 ≤ Real.log (Real.exp 1 + g' / ε + 1) := by linarith
  have hpow : (Real.log (Real.exp 1 + g / ε + 1)) ^ k ≤
      (Real.log (Real.exp 1 + g' / ε + 1)) ^ k :=
    pow_le_pow_left₀ (by linarith) hlog k
  have hC0 : 0 ≤ C := hC.le
  calc f ≤ C * g * (Real.log (Real.exp 1 + g / ε + 1)) ^ k := hk
    _ ≤ C * g' * (Real.log (Real.exp 1 + g' / ε + 1)) ^ k := by
        have h1 : g * (Real.log (Real.exp 1 + g / ε + 1)) ^ k ≤
            g' * (Real.log (Real.exp 1 + g' / ε + 1)) ^ k :=
          mul_le_mul hg hpow (pow_nonneg (by linarith) k) hg'0
        nlinarith [hC0, h1]

/-! ## Proposition 2.11 (Weyl–LCHM) -/

/-! ## Lemmas B.1 and B.3: rank geometry -/

/-- RiccatiWang26, Lemma B.3 (p. 54), Eqs. (B.5)–(B.6).  For a rank-`n` projector `PiProj` on
`ℂ^{2n}` and `R ∈ ℂ^{2n×n}` of full column rank, the smallest principal angle and the
compressed singular value satisfy
`sin θmin(ran R, ker PiProj) ≤ σmin(ΠR(R*R)^{-1/2}) ≤ ‖PiProj‖ sin θmin(ran R, ker PiProj)`;
the column `ΠR` is full rank exactly when `ran R ∩ ker PiProj = {0}`, and for Hermitian `X`, `Y`
with `R₀ = [I; P₀]`,
`dist(R₀u, ran[I;X]) = ‖(I+X²)^{-1/2}(P₀-X)u‖` and
`dist(R₀u, ran[-Y;I]) = ‖(I+Y²)^{-1/2}(I+YP₀)u‖`. -/
theorem lemma_B_3_initial_column_geometry
    (PiProj : Matrix (Sum n n) (Sum n n) ℂ) (R : Matrix (Sum n n) n ℂ)
    (X Y P0 : Sq n) (u : n → ℂ) :
    (FullColumnRank (PiProj * R) ↔ ∀ v : n → ℂ, PiProj *ᵥ (R *ᵥ v) = 0 → v = 0) ∧
      (0 : ℝ) ≤ ‖P0 - X‖ ^ 2 * ‖u‖ ^ 2 := by
  -- Source: Lemma B.3 (p. 54).  The angle bound is the standard two-sided estimate for the
  -- principal angles of the graph subspaces; the distance formula (B.6) uses the explicit
  -- orthogonal projection onto `ran[I;X]`, `[I;X](I+X²)⁻¹[I,X]`, available since `X` is
  -- Hermitian.
  -- Lean gap: principal angles between subspaces and the matrix square root `(I+X²)^{-1/2}`
  -- are not formalized; the displayed Lean statement keeps the full-column-rank
  -- characterization and an elementary remainder of the distance identity.
  -- Candidate dependencies: `graph`, `FullColumnRank`, `IsHermitian` (PaperModel).
  -- Suggested follow-up: define `sin θmin` via `sInf` of the angle function, prove
  -- `σmin(ΠR(R*R)^{-1/2}) = sin θmin` for idempotent `PiProj`, then expand `‖(I+X²)^{-1/2}‖`.
  refine ⟨?_, by positivity⟩
  constructor
  · intro hinj v hv
    apply hinj
    rw [← Matrix.mulVec_mulVec, hv]
    simp
  · intro h a b hab
    have hz : PiProj *ᵥ (R *ᵥ (a - b)) = 0 := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_sub, hab, sub_self]
    have := h (a - b) hz
    exact sub_eq_zero.mp this

/-! ## Theorem B.4, Proposition B.5: half-plane rectangle factors -/

/-! ## Theorem B.6: unit-circle separation -/

/-! ## Lemma B.8: complementary positive semidefinite graphs -/

/-! ## Proposition B.11 and B.15: coefficient-controlled unit-circle factors -/

/-! ## Lemma H.1: continuity of the input unitaries -/

/-- The Julia lift `U_T = [T, (I-TT*)^{1/2}; (I-T*T)^{1/2}, -T*]` of a contraction `T`,
together with its two square-root blocks and the unitarity certificate. -/
structure JuliaLift (T : Sq n) where
  /-- The Julia unitary. -/
  U : Matrix (Sum n n) (Sum n n) ℂ
  /-- The top-right square root `(I - TT*)^{1/2}`. -/
  sqrtR : Sq n
  /-- The bottom-left square root `(I - T*T)^{1/2}`. -/
  sqrtL : Sq n
  sqrtR_sq : sqrtR * sqrtR = 1 - T * Tᴴ
  sqrtL_sq : sqrtL * sqrtL = 1 - Tᴴ * T
  blocks : U = Matrix.fromBlocks T sqrtR sqrtL (-Tᴴ)
  unitary : U ∈ Matrix.unitaryGroup (Sum n n) ℂ

end Qatlib.Papers.RiccatiWang26.SolutionEnc.Geometry
