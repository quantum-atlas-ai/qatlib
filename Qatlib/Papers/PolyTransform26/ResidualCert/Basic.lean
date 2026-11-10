/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolyTransform26.ResidualCert.ResidualCertData
import Qatlib.Foundations.MatrixAlgebra.ResponseAlgebra.NCResponse
set_option warningAsError false
open Qatlib.Foundations.MatrixAlgebra.ResponseAlgebra

namespace Qatlib.Papers.PolyTransform26.ResidualCert

open Matrix

variable {J : Type} [Fintype J]

omit [Fintype J] in

theorem residualCoeff_rec {r : ℕ} (a0 : EuclideanSpace ℂ (Fin r))
    (Ares : J → Matrix (Fin r) (Fin r) ℂ) (j : J) (w : List J) :
    (Ares j).toEuclideanLin (residualCoeff a0 Ares w) = residualCoeff a0 Ares (j :: w) :=
  rfl

omit [Fintype J] in

theorem residualCoeff_matrixWord {r : ℕ} (a0 : EuclideanSpace ℂ (Fin r))
    (Ares : J → Matrix (Fin r) (Fin r) ℂ) (w : List J) :
    residualCoeff a0 Ares w = (matrixWord Ares w).toEuclideanLin a0 := by
  induction w with
  | nil =>
    show a0 = (1 : Matrix (Fin r) (Fin r) ℂ).toEuclideanLin a0
    apply WithLp.ofLp_injective
    simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.one_mulVec]
  | cons j w ih =>
    rw [residualCoeff, ih, matrixWord]
    apply WithLp.ofLp_injective
    simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec_mulVec]

omit [Fintype J] in

theorem matrixWord_zero_of_le {r : ℕ}
    (Ares : J → Matrix (Fin r) (Fin r) ℂ) (D : ℕ)
    (h : ∀ w : List J, w.length = D → matrixWord Ares w = 0) :
    ∀ w : List J, D ≤ w.length → matrixWord Ares w = 0 := by
  intro w
  induction w with
  | nil =>
    intro hw
    match D with
    | 0 =>
      have hz := h [] (by simp)
      simpa [matrixWord] using hz
    | Nat.succ _ => cases hw
  | cons j w ih =>
    intro hw
    by_cases hle : D ≤ w.length
    · rw [matrixWord, ih hle, Matrix.mul_zero]
    · have hD : w.length + 1 = D := by
        simp only [List.length_cons] at hw
        omega
      exact h (j :: w) (by rw [List.length_cons, hD])

omit [Fintype J] in

theorem residualCoeff_truncate {r : ℕ} (a0 : EuclideanSpace ℂ (Fin r))
    (Ares : J → Matrix (Fin r) (Fin r) ℂ) (D : ℕ)
    (h : ∀ w : List J, w.length = D → matrixWord Ares w = 0) :
    ∀ w, D ≤ w.length → residualCoeff a0 Ares w = 0 := by
  intro w hw
  have hz : matrixWord Ares w = 0 := matrixWord_zero_of_le Ares D h w hw
  rw [residualCoeff_matrixWord, hz]
  show (0 : Matrix (Fin r) (Fin r) ℂ).toEuclideanLin a0 = 0
  apply WithLp.ofLp_injective
  simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.zero_mulVec, WithLp.ofLp_zero]

omit [Fintype J] in

theorem residual_certificate_response {r D : ℕ}
    (a0 : EuclideanSpace ℂ (Fin r)) (Ares : J → Matrix (Fin r) (Fin r) ℂ)
    (cConst : ℂ) (pRow : J → Fin r → ℂ) (q : NCPoly J)
    (hqnil : q [] = cConst)
    (hq : ∀ j w, q (j :: w) = ∑ t : Fin r, pRow j t * residualCoeff a0 Ares w t)
    (hnil : ∀ w : List J, w.length = D → matrixWord Ares w = 0) :
    (let T : J → Matrix (Fin r) (Fin r) ℂ := Ares
     let H : List J → EuclideanSpace ℂ (Fin r) := residualCoeff a0 Ares
     let C : J → Fin r → ℂ := pRow
     (∀ j w, (T j).toEuclideanLin (H w) = H (j :: w)) ∧
     (∀ w, D ≤ w.length → H w = 0) ∧
     q [] = cConst ∧
     (∀ j w, q (j :: w) = ∑ x, C j x * H w x)) := by
  refine ⟨?_, ?_, hqnil, ?_⟩
  · intro j w
    exact residualCoeff_rec a0 Ares j w
  · intro w hw
    exact residualCoeff_truncate a0 Ares D hnil w hw
  · intro j w
    exact hq j w

theorem residual_certificate_nc_response {r D : ℕ}
    (a0 : EuclideanSpace ℂ (Fin r)) (Ares : J → Matrix (Fin r) (Fin r) ℂ)
    (cConst : ℂ) (pRow : J → Fin r → ℂ) (q : NCPoly J)
    (hqnil : q [] = cConst)
    (hq : ∀ j w, q (j :: w) = ∑ t : Fin r, pRow j t * residualCoeff a0 Ares w t)
    (hnil : ∀ w : List J, w.length = D → matrixWord Ares w = 0) :
    (∀ w, q w ≠ 0 → w.length ≤ D) ∧
    (∀ (S : Type) [Fintype S] [DecidableEq S] (A : J → Matrix S S ℂ),
      (ncTransition Ares A) ^ D * ncInjection (S := S) (residualCoeff a0 Ares) = 0 ∧
      cConst • (1 : Matrix S S ℂ) + ncCollection pRow A *
        (∑ t ∈ Finset.range D, (ncTransition Ares A) ^ t) *
        ncInjection (residualCoeff a0 Ares) = ncPolyEval A q) := by
  obtain ⟨hrec, htruncate, _, hcoef⟩ :=
    residual_certificate_response a0 Ares cConst pRow q hqnil hq hnil
  exact nc_response Ares (residualCoeff a0 Ares) pRow cConst q D hrec htruncate hqnil hcoef

end Qatlib.Papers.PolyTransform26.ResidualCert
