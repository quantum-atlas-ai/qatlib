/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

set_option backward.isDefEq.respectTransparency false

/-!
# SourceLevelDifference — Lemma 5.1 of arXiv:2606.01270v2

Xiantaо Li, "Toward Efficient End-to-End Quantum Elliptic PDE Solvers: a Multilevel
Correction Algorithm for Direct Observable Estimation", arXiv:2606.01270v2 (2026-09-22).

Section 5.1, Lemma 5.1, page 12, equations (5.2) and (5.3).

The lemma expresses the `ℓ`-th level difference of a multilevel decomposition as a single
overlap (linear outputs) or a single expectation (quadratic outputs).  With the discrete Green
operator `B_ℓ = A_ℓ⁻¹` (2.16), its lifted coarse response and the Ritz correction

  `C_ℓ = P_ℓ B_{ℓ-1} P_ℓ†`,   `D_ℓ = B_ℓ - C_ℓ`   (5.1),

and the compatibility relations `g_{ℓ-1} = P_ℓ† g_ℓ` (2.20), `b_{ℓ-1} = P_ℓ† b_ℓ` (vector
half of (2.15)), `M_{ℓ-1} = P_ℓ† M_ℓ P_ℓ` (2.21), one has

  `Δ^lin_ℓ  = g_ℓ† B_ℓ b_ℓ - g_{ℓ-1}† B_{ℓ-1} b_{ℓ-1} = g_ℓ† D_ℓ b_ℓ`            (5.2)
  `Δ^quad_ℓ = b_ℓ† B_ℓ† M_ℓ B_ℓ b_ℓ - b_{ℓ-1}† B_{ℓ-1}† M_{ℓ-1} B_{ℓ-1} b_{ℓ-1}`
            `= b_ℓ† (D_ℓ† M_ℓ D_ℓ + D_ℓ† M_ℓ C_ℓ + C_ℓ† M_ℓ D_ℓ) b_ℓ`               (5.3)

Both are exact algebraic identities; they involve only the coupling relations above and the
definition (5.1).  The paper writes real coordinates; we state them over `ℂ` (the substitution
`A_{ℓ-1} = P_ℓ† A_ℓ P_ℓ` of (2.15) is not needed for either identity, only `b_{ℓ-1}=P_ℓ†b_ℓ`).
The `⪰ 0` refinement of `D_ℓ` is Lemma 5.2 and lives in `SourceRitzDecomposition`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix

namespace Qatlib.Papers.EllipticPDELi26.MainResults.GreenOperatorAlgebra

variable {nFine nCoarse : ℕ}

/-- Lifted coarse response `C_ℓ = P_ℓ B_{ℓ-1} P_ℓ†` from (5.1).  Here `P : Fin nFine → Fin
nCoarse` is the prolongation `P_ℓ` (fine rows, coarse columns) and `Bprev` is the coarse Green
operator `B_{ℓ-1} = A_{ℓ-1}⁻¹`. -/
def sourceCoarseLift (Bprev : Matrix (Fin nCoarse) (Fin nCoarse) ℂ)
    (P : Matrix (Fin nFine) (Fin nCoarse) ℂ) : Matrix (Fin nFine) (Fin nFine) ℂ :=
  P * Bprev * Pᴴ

/-- The Ritz correction `D_ℓ = B_ℓ - C_ℓ` from (5.1). -/
def sourceDetailCorrection (B : Matrix (Fin nFine) (Fin nFine) ℂ)
    (Bprev : Matrix (Fin nCoarse) (Fin nCoarse) ℂ)
    (P : Matrix (Fin nFine) (Fin nCoarse) ℂ) : Matrix (Fin nFine) (Fin nFine) ℂ :=
  B - sourceCoarseLift Bprev P

/-- **Lemma 5.1(a)**, equation (5.2).  Linear level difference as one overlap.

Source: arXiv:2606.01270v2, Section 5.1, Lemma 5.1(a), page 12.
The coarse term `g_{ℓ-1}† B_{ℓ-1} b_{ℓ-1}` equals `g_ℓ† C_ℓ b_ℓ` because `g_{ℓ-1}=P_ℓ†g_ℓ`
and `b_{ℓ-1}=P_ℓ†b_ℓ`; subtracting from `g_ℓ†B_ℓb_ℓ` gives `g_ℓ†(B_ℓ−C_ℓ)b_ℓ = g_ℓ†D_ℓb_ℓ`. -/
theorem source_levelDifference_linear
    (B : Matrix (Fin nFine) (Fin nFine) ℂ)
    (Bprev : Matrix (Fin nCoarse) (Fin nCoarse) ℂ)
    (P : Matrix (Fin nFine) (Fin nCoarse) ℂ)
    (g b : Matrix (Fin nFine) (Fin 1) ℂ)
    (gprev bprev : Matrix (Fin nCoarse) (Fin 1) ℂ)
    (hg : gprev = Pᴴ * g) (hb : bprev = Pᴴ * b) :
    gᴴ * B * b - gprevᴴ * Bprev * bprev
      = gᴴ * sourceDetailCorrection B Bprev P * b := by
  subst hg hb
  unfold sourceDetailCorrection sourceCoarseLift
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc]

/-- Core quadratic identity: if `B = C + D` then
`Bᴴ M B - Cᴴ M C = Dᴴ M D + Dᴴ M C + Cᴴ M D`.  This is the expansion of
`B_ℓ† M_ℓ B_ℓ - C_ℓ† M_ℓ C_ℓ` used in the proof of (5.3). -/
theorem quad_core (M B C D : Matrix (Fin nFine) (Fin nFine) ℂ) (hBD : B = C + D) :
    Bᴴ * M * B - Cᴴ * M * C
      = Dᴴ * M * D + Dᴴ * M * C + Cᴴ * M * D := by
  subst hBD
  rw [conjTranspose_add]
  noncomm_ring

/-- **Lemma 5.1(b)**, equation (5.3).  Quadratic level difference as one expectation.

Source: arXiv:2606.01270v2, Section 5.1, Lemma 5.1(b), page 12.
Using `b_{ℓ-1}=P_ℓ†b_ℓ` and `M_{ℓ-1}=P_ℓ†M_ℓP_ℓ`, the coarse quadratic form equals
`b_ℓ† C_ℓ† M_ℓ C_ℓ b_ℓ`; the identity then follows by expanding `B_ℓ = C_ℓ + D_ℓ`. -/
theorem source_levelDifference_quadratic
    (B : Matrix (Fin nFine) (Fin nFine) ℂ)
    (Bprev : Matrix (Fin nCoarse) (Fin nCoarse) ℂ)
    (P : Matrix (Fin nFine) (Fin nCoarse) ℂ)
    (M : Matrix (Fin nFine) (Fin nFine) ℂ)
    (Mprev : Matrix (Fin nCoarse) (Fin nCoarse) ℂ)
    (b : Matrix (Fin nFine) (Fin 1) ℂ)
    (bprev : Matrix (Fin nCoarse) (Fin 1) ℂ)
    (hb : bprev = Pᴴ * b) (hM : Mprev = Pᴴ * M * P) :
    bᴴ * (Bᴴ * M * B) * b - bprevᴴ * (Bprevᴴ * Mprev * Bprev) * bprev
      = bᴴ * ((sourceDetailCorrection B Bprev P)ᴴ * M * (sourceDetailCorrection B Bprev P)
          + (sourceDetailCorrection B Bprev P)ᴴ * M * (sourceCoarseLift Bprev P)
          + (sourceCoarseLift Bprev P)ᴴ * M * (sourceDetailCorrection B Bprev P)) * b := by
  subst hb hM
  -- The coarse form equals `bᴴ * Cᴴ * M * C * b` with `C = sourceCoarseLift Bprev P`.
  have hcoarse :
      (Pᴴ * b)ᴴ * (Bprevᴴ * (Pᴴ * M * P) * Bprev) * (Pᴴ * b)
        = bᴴ * ((sourceCoarseLift Bprev P)ᴴ * M * (sourceCoarseLift Bprev P)) * b := by
    unfold sourceCoarseLift
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hcoarse]
  -- Factor the leading `bᴴ` and trailing `b`, then apply `quad_core`.
  have hB : B = sourceCoarseLift Bprev P + sourceDetailCorrection B Bprev P := by
    unfold sourceDetailCorrection; abel
  have hcore := quad_core M B (sourceCoarseLift Bprev P)
    (sourceDetailCorrection B Bprev P) hB
  rw [show bᴴ * (Bᴴ * M * B) * b - bᴴ * ((sourceCoarseLift Bprev P)ᴴ * M * (sourceCoarseLift Bprev P)) * b
        = bᴴ * (Bᴴ * M * B - (sourceCoarseLift Bprev P)ᴴ * M * (sourceCoarseLift Bprev P)) * b by
      rw [Matrix.mul_sub, Matrix.sub_mul]]
  rw [hcore]

end Qatlib.Papers.EllipticPDELi26.MainResults.GreenOperatorAlgebra
