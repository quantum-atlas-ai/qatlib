/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceOriginalDeflation
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Original-input, accepted-certificate nonconstant source packet: PhaseStructure.
Value and physical-word guarantees here do not certify a root proposer, Python interpreter or total costs. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section PhaseStructure

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Polynomial
open scoped Matrix.Norms.L2Operator

/-- The finite construction in `NativeSourcePhaseStructure` satisfies `integer_polynomial_conj` under the displayed hypotheses. -/
private theorem integer_polynomial_conj (a : List ℤ) :
    (rootIntegerListPolynomial a).map (starRingEnd ℂ)=rootIntegerListPolynomial a := by
  ext n
  simp [Polynomial.coeff_map,rootIntegerListPolynomial_coeff]

/-- The finite construction in `NativeSourcePhaseStructure` satisfies `sourceInsideRoots_conj` under the displayed hypotheses. -/
theorem sourceInsideRoots_conj (cs : List ℚ) (N : ℕ) (E : ℚ) :
    (sourceInsideRoots cs N E).map (fun z : ℂ => star z)=sourceInsideRoots cs N E := by
  classical
  have hr : (rootIntegerListPolynomial (sourceIntegerComplement cs N E)).roots.map
      (fun z : ℂ => star z)=(rootIntegerListPolynomial (sourceIntegerComplement cs N E)).roots := by
    have h := Polynomial.roots_map_of_injective_of_card_eq_natDegree
      (p := rootIntegerListPolynomial (sourceIntegerComplement cs N E)) (f := starRingEnd ℂ) star_injective
      (IsAlgClosed.card_roots_eq_natDegree (p := rootIntegerListPolynomial (sourceIntegerComplement cs N E)))
    simpa only [integer_polynomial_conj, show (starRingEnd ℂ : ℂ → ℂ) = (fun z => star z) from rfl] using h
  unfold sourceInsideRoots
  have h := congrArg (Multiset.filter (fun z : ℂ => ‖z‖<1)) hr
  rw [Multiset.filter_map] at h
  simpa only [Function.comp_def,norm_star] using h

/-- The finite construction in `NativeSourcePhaseStructure` satisfies `sourceIdealMonicPolynomial_conj` under the displayed hypotheses. -/
theorem sourceIdealMonicPolynomial_conj (cs : List ℚ) (N : ℕ) (E : ℚ) :
    (sourceIdealMonicPolynomial cs N E).map (starRingEnd ℂ)=sourceIdealMonicPolynomial cs N E := by
  unfold sourceIdealMonicPolynomial
  rw [Polynomial.map_multiset_prod,Multiset.map_map]
  have he : (fun r : ℂ => (X-C r).map (starRingEnd ℂ))=
      (fun r : ℂ => X-C (star r)) := by
    funext r
    simp
  simp only [Function.comp_def]
  rw [he]
  have h := sourceInsideRoots_conj cs N E
  have hprod := congrArg (fun l : Multiset ℂ => (l.map (fun r => (X-C r : ℂ[X]))).prod) h
  simpa only [Multiset.map_map, Function.comp_def] using hprod

/-- The finite construction in `NativeSourcePhaseStructure` satisfies `sourceIdealEArray_real` under the displayed hypotheses. -/
theorem sourceIdealEArray_real (cs : List ℚ) (N : ℕ) (E : ℚ) (j : Fin (sourceDegree cs N E+1)) :
    star (sourceIdealEArray cs N E j)=sourceIdealEArray cs N E j := by
  have hc := congrArg (fun p : ℂ[X] => p.coeff j.val) (sourceIdealMonicPolynomial_conj cs N E)
  simp only [Polynomial.coeff_map] at hc
  unfold sourceIdealEArray
  rw [star_mul,star_div₀]
  simpa only [Complex.star_def,Complex.conj_ofReal,mul_comm] using congrArg
    (fun z : ℂ => (Real.sqrt (sourceActualH1 cs N E : ℝ) : ℂ)/(‖sourceIdealProduct cs N E 1‖ : ℂ)*z) hc

end PhaseStructure

section Equatorial

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- Construction for source Conjugate Swap in the native source phase structure model. -/
def sourceConjugateSwap (C : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  fun i j => star (C (!i) (!j))

/-- The finite construction in `NativeSourcePhaseStructure` satisfies `sourceConjugateSwap_add` under the displayed hypotheses. -/
theorem sourceConjugateSwap_add (A B : Matrix Bool Bool ℂ) :
    sourceConjugateSwap (A+B)=sourceConjugateSwap A+sourceConjugateSwap B := by
  ext i j
  simp [sourceConjugateSwap]

/-- The finite construction in `NativeSourcePhaseStructure` satisfies `sourceConjugateSwap_mul` under the displayed hypotheses. -/
theorem sourceConjugateSwap_mul (A B : Matrix Bool Bool ℂ) :
    sourceConjugateSwap (A*B)=sourceConjugateSwap A*sourceConjugateSwap B := by
  ext i j
  cases i <;> cases j <;> simp [sourceConjugateSwap,Matrix.mul_apply] <;> ring

/-- The finite construction in `NativeSourcePhaseStructure` satisfies `sourceConjugateSwap_adjoint` under the displayed hypotheses. -/
theorem sourceConjugateSwap_adjoint (A : Matrix Bool Bool ℂ) :
    sourceConjugateSwap A.conjTranspose=(sourceConjugateSwap A).conjTranspose := by
  ext i j
  simp [sourceConjugateSwap,Matrix.conjTranspose_apply]

/-- The finite construction in `NativeSourcePhaseStructure` satisfies `sourceConjugateSwap_real_smul` under the displayed hypotheses. -/
theorem sourceConjugateSwap_real_smul (A : Matrix Bool Bool ℂ) (r : ℝ) :
    sourceConjugateSwap ((r : ℂ) • A)=(r : ℂ) • sourceConjugateSwap A := by
  ext i j
  simp [sourceConjugateSwap,mul_comm]

/-- The finite construction in `NativeSourcePhaseStructure` satisfies `sourceComplexGramNormalize_fixed` under the displayed hypotheses. -/
theorem sourceComplexGramNormalize_fixed (C : Matrix Bool Bool ℂ) (hC : sourceConjugateSwap C=C) :
    sourceConjugateSwap (sourceComplexGramNormalize C)=sourceComplexGramNormalize C := by
  unfold sourceComplexGramNormalize
  rw [sourceConjugateSwap_real_smul,sourceConjugateSwap_mul,sourceConjugateSwap_adjoint,hC]

/-- The finite construction in `NativeSourcePhaseStructure` satisfies `sourceIdealDeflation_fixed` under the displayed hypotheses. -/
theorem sourceIdealDeflation_fixed {m : ℕ} (F : Fin (m+2) → Matrix Bool Bool ℂ)
    (hF : ∀ j,sourceConjugateSwap (F j)=F j) :
    ∀ j,sourceConjugateSwap (sourceIdealDeflationStep F j)=sourceIdealDeflationStep F j := by
  intro j
  simp only [sourceIdealDeflationStep,sourceConjugateSwap_add,sourceConjugateSwap_mul,hF,
    sourceComplexGramNormalize_fixed _ (hF _)]

/-- The finite construction in `NativeSourcePhaseStructure` satisfies `sourceIdealArray_fixed` under the displayed hypotheses. -/
theorem sourceIdealArray_fixed (cs : List ℚ) (N : ℕ) (E : ℚ) (j : Fin (sourceDegree cs N E+1)) :
    sourceConjugateSwap (sourceIdealMatrixArray cs N E j)=sourceIdealMatrixArray cs N E j := by
  let a : ℝ := sourceRealArray cs N E j
  let v := sourceIdealEArray cs N E j
  let w := sourceIdealEArray cs N E j.rev
  have hv : star v=v := sourceIdealEArray_real cs N E j
  have hw : star w=w := sourceIdealEArray_real cs N E j.rev
  let C : Matrix Bool Bool ℂ := fun i j => match i,j with
    | false,false => Complex.I*(a : ℂ)-(v+star w)/2
    | true,true => -Complex.I*(a : ℂ)-(v+star w)/2
    | _,_ => (v-star w)/2
  change sourceConjugateSwap C=C
  dsimp only [C]
  rw [hw]
  ext i j
  cases i <;> cases j <;>
    simp [sourceConjugateSwap,star_sub,star_add,star_div₀,hv,hw]

/-- The finite construction in `NativeSourcePhaseStructure` satisfies `sourceComplexGramNormalize_diagonal_half` under the displayed hypotheses. -/
theorem sourceComplexGramNormalize_diagonal_half (C : Matrix Bool Bool ℂ) (hc : C≠0)
    (hC : sourceConjugateSwap C=C) :
    sourceComplexGramNormalize C false false=1/2 ∧ sourceComplexGramNormalize C true true=1/2 := by
  let P := sourceComplexGramNormalize C
  have hfix := congrFun (congrFun (sourceComplexGramNormalize_fixed C hC) false) false
  have hherm := congrFun (congrFun (sourceComplexGramNormalize_hermitian C) true) true
  have hd : P true true=P false false := by
    simpa only [sourceConjugateSwap,Bool.not_false,Matrix.conjTranspose_apply] using hherm.symm.trans hfix
  have ht := sourceComplexGramNormalize_trace C hc
  simp only [Matrix.trace,Fintype.sum_bool] at ht
  change P true true+P false false=1 at ht
  rw [hd] at ht
  have hp : P false false=1/2 := by linear_combination (1/2 : ℂ)*ht
  exact ⟨hp,hd.trans hp⟩

end Equatorial

section PhaseUnit

open scoped Matrix.Norms.L2Operator

/-- The finite construction in `NativeSourcePhaseStructure` satisfies `sourceIdealDiscoveredPhase_norm` under the displayed hypotheses. -/
theorem sourceIdealDiscoveredPhase_norm (C : Matrix Bool Bool ℂ) (hc : C≠0)
    (hC : sourceConjugateSwap C=C) (hpp : sourceComplexGramNormalize C*sourceComplexGramNormalize C=sourceComplexGramNormalize C) :
    ‖2*sourceComplexGramNormalize C false true‖=1 := by
  let P := sourceComplexGramNormalize C
  have hhalf := sourceComplexGramNormalize_diagonal_half C hc hC
  change P false false=1/2 ∧ P true true=1/2 at hhalf
  have h10 : P true false=star (P false true) := by
    have h := congrFun (congrFun (sourceComplexGramNormalize_hermitian C) true) false
    exact h.symm
  have h := congrFun (congrFun hpp false) false
  simp only [Matrix.mul_apply,Fintype.sum_bool] at h
  change P false true*P true false+P false false*P false false=P false false at h
  rw [h10,hhalf.1] at h
  have hs : P false true*star (P false true)=(1/4 : ℂ) := by linear_combination h
  have hn : ‖P false true‖^2=(1/4 : ℝ) := by
    have hr := congrArg Complex.re hs
    norm_num [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq] at hr
    simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using hr
  change ‖(2 : ℂ)*P false true‖=1
  rw [norm_mul]
  norm_num
  nlinarith [norm_nonneg (P false true)]

end PhaseUnit

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
