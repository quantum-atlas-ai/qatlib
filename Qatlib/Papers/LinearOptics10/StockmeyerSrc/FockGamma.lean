/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.BosonFock.BosonOperators.PermFibers
public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockExpansion
public import Qatlib.Concepts.BosonFock.BosonOperators.Basic

@[expose] public section


/-! # The actual coefficient action and the proved permanent-sector representation

The historical substitution reads rows of U, so its normalized coefficient
action corresponds to gamma(U transpose). Exact permutation-fiber counts
and occupation factorials establish that convention rather than assuming
the two matrix actions coincide.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix ComplexConjugate
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockGamma
open Qatlib.Papers.LinearOptics10.StockmeyerSrc
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.BosonFock.BosonOperators
open FockModel

/-- The actual repeated photon positions have their exact prescribed occupation count function. -/
theorem countsPick {m n : ℕ} (S : FockOccupation m n) :
    PermFibers.counts (occPick S) = fun i => (S.val i).val := by
  funext i
  simpa only [PermFibers.counts, Finset.sum_boole, Nat.cast_id] using FockExpansion.pickCount S i

/-- Matching a repeated occupation is exactly the full original assignment fiber condition. -/
theorem countsEq {m n : ℕ} (f : Fin n → Fin m) (S : FockOccupation m n) :
    PermFibers.counts f = PermFibers.counts (occPick S) ↔
      ∀ i, (Finset.univ.filter (fun k : Fin n => f k = i)).card = (S.val i).val := by
  rw [countsPick, funext_iff]
  simp only [PermFibers.counts, Finset.sum_boole, Nat.cast_id]

/-- The genuine repeated-row/column permanent is the assignment coefficient times its output factorial. -/
theorem permanentSum {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (T S : FockOccupation m n) :
    Matrix.permanent (fockSubmatrix U T S) = (occFactorial S : ℂ) * polyActGenCoeff U T S := by
  have hs := PermFibers.sumCompose (occPick S)
    (fun f : Fin n → Fin m => ∏ k, U (occPick T k) (f k))
  have hw : (∏ i, (PermFibers.counts (occPick S) i).factorial) = occFactorial S := by
    rw [countsPick]
    rfl
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  simpa only [Matrix.transpose_apply, fockSubmatrix, hw, countsEq, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul, polyActGenCoeff] using hs

/-- The public permanent-sector matrix uses the transposed historical row-substitution convention. -/
theorem repeatTranspose {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (S T : FockOccupation m n) :
    occupationMatrix Uᵀ S T = (fockSubmatrix U T S)ᵀ := by
  rfl

/-- The actual factorial-weighted pairing reads a basis coefficient with its genuine weight. -/
theorem basisRead {m n : ℕ} (S : FockOccupation m n) (a : FockCoeff m n) :
    fockInner (basisCoeff S) a = a S * (occFactorial S : ℂ) := by
  simp [fockInner, basisCoeff]

/-- The public representation denominator is the product of the actual positive factorial roots. -/
theorem rootProduct {m n : ℕ} (S T : FockOccupation m n) :
    Real.sqrt (((∏ i, (S.val i : ℕ).factorial : ℕ) : ℝ) *
      ((∏ i, (T.val i : ℕ).factorial : ℕ) : ℝ)) =
        Real.sqrt (occFactorial S : ℝ) * Real.sqrt (occFactorial T : ℝ) := by
  exact Real.sqrt_mul (Nat.cast_nonneg _) _

/-- The actual normalized polynomial amplitude is the already-proved gamma of the transposed mode matrix. -/
theorem amplitudeGamma {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (S T : FockOccupation m n) : fockAmplitude U S T = gamma m n Uᵀ S T := by
  have hs : (Real.sqrt (occFactorial S : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast FockNormalize.rootNonzero S
  have ht : (Real.sqrt (occFactorial T : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast FockNormalize.rootNonzero T
  have he := FockExpansion.innerAmplitude U S T
  rw [basisRead] at he
  unfold gamma
  rw [repeatTranspose, Matrix.permanent_transpose, permanentSum, rootProduct, Complex.ofReal_mul]
  apply (eq_div_iff (mul_ne_zero hs ht)).mpr
  calc
    _ = ((Real.sqrt (occFactorial S : ℝ) : ℂ) *
        (Real.sqrt (occFactorial T : ℝ) : ℂ)) * fockAmplitude U S T := mul_comm _ _
    _ = polyActGenCoeff U T S * (occFactorial S : ℂ) := by
      simpa only [Complex.ofReal_mul] using he.symm
    _ = _ := mul_comm _ _

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockGamma
