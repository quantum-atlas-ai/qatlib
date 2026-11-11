/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePreparation
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Qatlib.Foundations.PureStateMath

/-!
# Isometric Mixture

One scalar phase aligns an arbitrary actual overlap without changing either density.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.IsometricMixture

/-- One scalar phase aligns an arbitrary actual overlap without changing either density. -/
def overlapPhase (z : ℂ) : ℂ := Complex.exp (-(Complex.arg z*Complex.I))

/-- The chosen scalar has unit norm even when the overlap vanishes. -/
theorem overlapPhase_norm (z : ℂ) : ‖overlapPhase z‖=1 := by
  simp [overlapPhase,Complex.norm_exp]

/-- The actual aligned overlap is the nonnegative real norm. -/
theorem overlapPhase_mul (z : ℂ) : overlapPhase z*z=(‖z‖ : ℂ) := by
  have he : Complex.exp (-(Complex.arg z*Complex.I))*Complex.exp (Complex.arg z*Complex.I)=1 := by
    rw [←Complex.exp_add]
    simp
  calc
    _ = overlapPhase z*((‖z‖ : ℂ)*Complex.exp (Complex.arg z*Complex.I)) := by
      rw [Complex.norm_mul_exp_arg_mul_I]
    _ = _ := by
      unfold overlapPhase
      rw [mul_left_comm,he,mul_one]

/-- The actual purification amplitudes retain the mixture label only in the environment. -/
def amplitude {Y R S E : Type*} [Fintype S] (p : Y → ℝ)
    (K : Y → Matrix R S ℂ) (X : Y → Matrix S E ℂ) : Matrix R (Y × E) ℂ :=
  fun i c => (Real.sqrt (p c.1) : ℂ)*(K c.1*X c.1) i c.2

/-- Tracing the literal mixture environment gives the actual mixture of conjugated input Gram matrices. -/
theorem amplitude_gram {Y R S E : Type*} [Fintype Y] [Fintype S] [Fintype E]
    (p : Y → ℝ) (hp : ∀ y,0≤p y) (K : Y → Matrix R S ℂ) (X : Y → Matrix S E ℂ) :
    amplitude p K X*(amplitude p K X).conjTranspose=
      ∑ y : Y,(p y : ℂ) • (K y*(X y*(X y).conjTranspose)*(K y).conjTranspose) := by
  have hs (y : Y) : (Real.sqrt (p y) : ℂ)^2=(p y : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hp y)
  have he (y : Y) (i j : R) (e : E) :
      amplitude p K X i (y,e)*star (amplitude p K X j (y,e))=
        (p y : ℂ)*((K y*X y) i e*star ((K y*X y) j e)) := by
    simp only [amplitude,star_mul]
    rw [show star (Real.sqrt (p y) : ℂ)=(Real.sqrt (p y) : ℂ) by simp]
    calc _ = (Real.sqrt (p y) : ℂ)^2*((K y*X y) i e*star ((K y*X y) j e)) := by ring
         _ = _ := by rw [hs]
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,he,
    ←Finset.mul_sum,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  have hm : (K y*X y)*(K y*X y).conjTranspose=
      K y*(X y*(X y).conjTranspose)*(K y).conjTranspose := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  exact congrArg (fun M : Matrix R R ℂ => M i j) hm

/-- A known full-register isometry preserves the exact overlap of arbitrary purification matrices. -/
theorem isometry_overlap {R S E : Type*} [Fintype R] [Fintype S] [Fintype E] [DecidableEq S]
    (K : Matrix R S ℂ) (hK : K.conjTranspose*K=1) (X Z : Matrix S E ℂ) :
    ((K*X).conjTranspose*(K*Z)).trace=(X.conjTranspose*Z).trace := by
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [←Matrix.mul_assoc K.conjTranspose K,hK,Matrix.one_mul]

/-- The actual full purification overlap is the weighted sum of conditional overlaps under those same known isometries. -/
theorem amplitude_overlap {Y R S E : Type*} [Fintype Y] [Fintype R] [Fintype S] [Fintype E]
    [DecidableEq S] (p : Y → ℝ) (hp : ∀ y,0≤p y) (K : Y → Matrix R S ℂ)
    (hK : ∀ y,(K y).conjTranspose*K y=1) (X Z : Y → Matrix S E ℂ) :
    ((amplitude p K X).conjTranspose*amplitude p K Z).trace=
      ∑ y : Y,(p y : ℂ)*((X y).conjTranspose*Z y).trace := by
  have hs (y : Y) : (Real.sqrt (p y) : ℂ)^2=(p y : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hp y)
  have he (y : Y) (i : R) (e : E) :
      star (amplitude p K X i (y,e))*amplitude p K Z i (y,e)=
        (p y : ℂ)*(star ((K y*X y) i e)*(K y*Z y) i e) := by
    simp only [amplitude,star_mul]
    rw [show star (Real.sqrt (p y) : ℂ)=(Real.sqrt (p y) : ℂ) by simp]
    calc _ = (Real.sqrt (p y) : ℂ)^2*(star ((K y*X y) i e)*(K y*Z y) i e) := by ring
         _ = _ := by rw [hs]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,he]
  apply Finset.sum_congr rfl
  intro y _
  simp only [←Finset.mul_sum]
  congr 1
  change ((K y*X y).conjTranspose*(K y*Z y)).trace= ((X y).conjTranspose*Z y).trace
  exact isometry_overlap (K y) (hK y) (X y) (Z y)

end Qatlib.Concepts.MixedFidelity.FidelityMetric.IsometricMixture

open scoped Classical BigOperators Matrix
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.IsometricMixture

/-- Actual conditional purification tensors reindex the complete original system basis. -/
def tensorAmplitude {E S C : Type*} [Fintype E] {J : E → Type*}
    (basis : S ≃ ((e : E) → J e)) (X : (e : E) → Matrix (J e) C ℂ) :
    Matrix S (E → C) ℂ := fun s c => ∏ e : E,X e (basis s e) (c e)

/-- The exact reduced tensor matrix is the product of the actual conditional reduced matrices. -/
theorem tensorAmplitude_gram {E S C : Type*} [Fintype E] [DecidableEq E] [Fintype C]
    {J : E → Type*} [∀ e,Fintype (J e)]
    (basis : S ≃ ((e : E) → J e)) (X : (e : E) → Matrix (J e) C ℂ) (s t : S) :
    (tensorAmplitude basis X*(tensorAmplitude basis X).conjTranspose) s t=
      ∏ e : E,(X e*(X e).conjTranspose) (basis s e) (basis t e) := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,tensorAmplitude,star_prod,
    ←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (e : E) (c : C) =>
    X e (basis s e) c*star (X e (basis t e) c))).symm

/-- Tensor purification overlaps are products of actual pair overlaps under the same full basis equivalence. -/
theorem tensorAmplitude_overlap {E S C : Type*} [Fintype E] [DecidableEq E] [Fintype S] [Fintype C]
    {J : E → Type*} [∀ e,Fintype (J e)]
    (basis : S ≃ ((e : E) → J e)) (X Z : (e : E) → Matrix (J e) C ℂ) :
    ((tensorAmplitude basis X).conjTranspose*tensorAmplitude basis Z).trace=
      ∏ e : E,((X e).conjTranspose*Z e).trace := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    tensorAmplitude,star_prod,←Finset.prod_mul_distrib]
  have h (c : E → C) :
      (∑ s : S,∏ e : E,star (X e (basis s e) (c e))*Z e (basis s e) (c e))=
        ∏ e : E,∑ j : J e,star (X e j (c e))*Z e j (c e) := by
    rw [Equiv.sum_comp basis (fun js : (e : E) → J e =>
      ∏ e : E,star (X e (js e) (c e))*Z e (js e) (c e))]
    exact (Fintype.prod_sum (fun (e : E) (j : J e) =>
      star (X e j (c e))*Z e j (c e))).symm
  simp_rw [h]
  exact (Fintype.prod_sum (fun (e : E) (c : C) =>
    ∑ j : J e,star (X e j c)*Z e j c)).symm

end Qatlib.Concepts.MixedFidelity.FidelityMetric.IsometricMixture

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.IsometricMixture

/-- Unit scalar alignment leaves the literal reduced matrix unchanged. -/
theorem unit_smul_gram {S C : Type*} [Fintype C] (z : ℂ) (hz : ‖z‖=1)
    (X : Matrix S C ℂ) : (z • X)*(z • X).conjTranspose=X*X.conjTranspose := by
  have hs : star z*z=1 := by
    rw [Complex.star_def,Complex.conj_mul']
    simp only [hz,Complex.ofReal_one,one_pow]
  simp only [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hs,one_smul]

/-- Aligning the actual overlap yields its exact nonnegative real norm and preserves the same physical density. -/
theorem aligned_amplitude {S C : Type*} [Fintype S] [Fintype C]
    (X Z : Matrix S C ℂ) :
    let Z' := overlapPhase ((X.conjTranspose*Z).trace) • Z
    Z'*Z'.conjTranspose=Z*Z.conjTranspose ∧
      (X.conjTranspose*Z').trace=(‖(X.conjTranspose*Z).trace‖ : ℂ) := by
  dsimp only
  constructor
  · exact unit_smul_gram _ (overlapPhase_norm _) Z
  · rw [Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]
    exact overlapPhase_mul _

end Qatlib.Concepts.MixedFidelity.FidelityMetric.IsometricMixture

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.IsometricMixture
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- A known finite basis equivalence preserves the literal matrix trace. -/
theorem trace_basis_equiv {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I I ℂ) (e : J ≃ I) : (M.submatrix e e).trace=M.trace := by
  simpa only [Matrix.trace,Matrix.diag_apply,Matrix.submatrix_apply] using
    Equiv.sum_comp e (fun i : I => M i i)

/-- Literal finite purification amplitudes give a lower bound for the existing public root fidelity after complete known basis relabelling. -/
theorem finite_purification_lower {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (hRC : Fintype.card R≤Fintype.card C) (ρ σ : Matrix R R ℂ)
    (hρ : ρ.trace=1) (hσ : σ.trace=1) (X Z : Matrix R C ℂ)
    (hX : X*X.conjTranspose=ρ) (hZ : Z*Z.conjTranspose=σ) :
    ‖(X.conjTranspose*Z).trace‖≤
      Froot (ρ.submatrix (Fintype.equivFin R).symm (Fintype.equivFin R).symm)
        (σ.submatrix (Fintype.equivFin R).symm (Fintype.equivFin R).symm) := by
  let r := (Fintype.equivFin R).symm
  let c := (Fintype.equivFin C).symm
  let A := X.submatrix r c
  let B := Z.submatrix r c
  have hA : A*A.conjTranspose=ρ.submatrix r r := by
    simp only [A,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,hX]
  have hB : B*B.conjTranspose=σ.submatrix r r := by
    simp only [B,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,hZ]
  have htρ : (ρ.submatrix r r).trace=1 := (trace_basis_equiv ρ r).trans hρ
  have htσ : (σ.submatrix r r).trace=1 := (trace_basis_equiv σ r).trans hσ
  have hψ := isPurification_of_amplitude_gram htρ A hA
  have hφ := isPurification_of_amplitude_gram htσ B hB
  have hi : Qatlib.Foundations.PureStateMath.Inner
      (fun q : Fin (Fintype.card R) × Fin (Fintype.card C) => A q.1 q.2)
      (fun q : Fin (Fintype.card R) × Fin (Fintype.card C) => B q.1 q.2)=(X.conjTranspose*Z).trace := by
    have hh : (A.conjTranspose*B).trace=(X.conjTranspose*Z).trace := by
      simp only [A,B,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv]
      exact trace_basis_equiv _ c
    rw [←hh]
    simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Pi.star_apply,
      Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]
    rw [Fintype.sum_prod_type,Finset.sum_comm]
  have h := purification_overlap_le_froot hRC hψ hφ
  rw [hi] at h
  exact h

end Qatlib.Concepts.MixedFidelity.FidelityMetric.IsometricMixture
