/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceRoundedPhases
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeEquatorialPhasePacket
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Original-input, accepted-certificate nonconstant source packet: RotorFactorization.
Value and physical-word guarantees here do not certify a root proposer, Python interpreter or total costs. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section RotorFactorization

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open scoped Matrix.Norms.L2Operator
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- The finite construction in `NativeSourceRotorFactorization` satisfies `sourceCompletionFourier_one` under the displayed hypotheses. -/
theorem sourceCompletionFourier_one (theta : ℝ) :
    fourier 1 (theta : AddCircle (2*Real.pi))=
      (Real.cos theta : ℂ)+Complex.I*(Real.sin theta : ℂ) := by
  rw [sourceCompletionFourier_real]
  simp only [Int.cast_one,one_mul,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]
  ring

/-- The finite construction in `NativeSourceRotorFactorization` satisfies `sourceIdealDeflation_inverse_rotor` under the displayed hypotheses. -/
theorem sourceIdealDeflation_inverse_rotor (P Q : Matrix Bool Bool ℂ)
    (hplus : P+Q=1) (hP : P.conjTranspose=P)
    (h00 : P false false=1/2) (h11 : P true true=1/2) (x s : ℝ) :
    star ((x : ℂ)+Complex.I*(s : ℂ)) • Q+((x : ℂ)+Complex.I*(s : ℂ)) • P=
      equatorialRotor (2*P false true) x s := by
  have hQ : Q=1-P := by rw [← hplus]; abel
  have h10 : P true false=star (P false true) := by
    exact (congrFun (congrFun hP true) false).symm
  rw [hQ]
  ext i j
  cases i <;> cases j <;>
    simp [equatorialRotor,h00,h11,h10,star_add,star_mul] <;> ring

/-- The finite construction in `NativeSourceRotorFactorization` satisfies `sourceIdealDeflation_inverse` under the displayed hypotheses. -/
theorem sourceIdealDeflation_inverse {m : ℕ} (G : Fin (m+2) → Matrix Bool Bool ℂ)
    (h : ℝ) (hh : 0<h) (hinv : SourceIdealDeflationInvariant G h)
    (hfixed : ∀ j,sourceConjugateSwap (G j)=G j) (theta : ℝ) :
    sourceCompletionCircleValue G (theta : AddCircle (2*Real.pi))=
      sourceCompletionCircleValue (sourceIdealDeflationStep G) (theta : AddCircle (2*Real.pi))*
        equatorialRotor (2*sourceComplexGramNormalize (G (Fin.last (m+1))) false true) (Real.cos theta) (Real.sin theta) := by
  have hl : G 0≠0 := norm_pos_iff.mp (hh.trans_le hinv.2.1)
  have hr : G (Fin.last (m+1))≠0 := norm_pos_iff.mp (hh.trans_le hinv.2.2)
  obtain ⟨hPQ,hQP,hplus,hPP,hQQ,hLP,hRQ,_,_⟩ := sourceIdealDeflation_endpoints G hinv.1 hl hr
  let P := sourceComplexGramNormalize (G (Fin.last (m+1)))
  let Q := sourceComplexGramNormalize (G 0)
  let t : AddCircle (2*Real.pi) := theta
  let E := fourier 1 t • Q+fourier (-1) t • P
  have hE : E∈Matrix.unitaryGroup Bool ℂ := sourceIdealDeflation_elementary_unitary P Q
    (sourceComplexGramNormalize_hermitian _) (sourceComplexGramNormalize_hermitian _) hPQ hQP hplus hPP hQQ t
  have hstep : sourceCompletionCircleValue (sourceIdealDeflationStep G) t=sourceCompletionCircleValue G t*E := sourceIdealDeflation_circle G hLP hRQ t
  have hhalf := sourceComplexGramNormalize_diagonal_half (G (Fin.last (m+1))) hr (hfixed _)
  have hstar : E.conjTranspose=equatorialRotor (2*P false true) (Real.cos theta) (Real.sin theta) := by
    change (fourier 1 t • Q+fourier (-1) t • P).conjTranspose=_
    rw [Matrix.conjTranspose_add,Matrix.conjTranspose_smul,Matrix.conjTranspose_smul,
      sourceComplexGramNormalize_hermitian,sourceComplexGramNormalize_hermitian]
    change star (fourier 1 t) • Q+star (fourier (-1) t) • P=_
    have hneg : fourier (-1) t=star (fourier 1 t) := by rw [fourier_neg,Complex.star_def]
    rw [hneg,star_star]
    change star (fourier 1 (theta : AddCircle (2*Real.pi))) • Q+fourier 1 (theta : AddCircle (2*Real.pi)) • P=_
    rw [sourceCompletionFourier_one]
    exact sourceIdealDeflation_inverse_rotor P Q hplus (sourceComplexGramNormalize_hermitian _) hhalf.1 hhalf.2 _ _
  calc
    _ = (sourceCompletionCircleValue G t*E)*E.conjTranspose := by
      rw [mul_assoc,show E*E.conjTranspose=1 from by simpa only [Matrix.star_eq_conjTranspose] using hE.2,mul_one]
    _ = sourceCompletionCircleValue (sourceIdealDeflationStep G) t*E.conjTranspose := by rw [← hstep]
    _ = _ := by rw [hstar]

/-- The finite construction in `NativeSourceRotorFactorization` satisfies `sourceIdealDeflationLoop_rotor_factorization` under the displayed hypotheses. -/
theorem sourceIdealDeflationLoop_rotor_factorization {d : ℕ} (G : Fin (d+1) → Matrix Bool Bool ℂ)
    (h : ℝ) (hh : 0<h) (hinv : SourceIdealDeflationInvariant G h)
    (hfixed : ∀ j,sourceConjugateSwap (G j)=G j) (theta : ℝ) :
    sourceCompletionCircleValue G (theta : AddCircle (2*Real.pi))=
      sourceIdealDeflationLoop G*equatorialRotorProduct (sourceIdealDiscovered G).reverse (Real.cos theta) (Real.sin theta) := by
  induction d with
  | zero => simp [sourceCompletionCircleValue,sourceCompletionFrequency,sourceIdealDeflationLoop,sourceIdealDiscovered,equatorialRotorProduct]
  | succ m ih =>
    rw [sourceIdealDeflation_inverse G h hh hinv hfixed theta,
      ih (sourceIdealDeflationStep G) (sourceIdealDeflation_invariant G h hh hinv) (sourceIdealDeflation_fixed G hfixed)]
    simp only [sourceIdealDiscovered,List.reverse_cons,equatorialRotorProduct,List.map_append,List.map_singleton,
      List.prod_append,List.prod_singleton,sourceIdealDeflationLoop,mul_assoc]

end RotorFactorization

section IdealPacket

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- The finite construction in `NativeSourceRotorFactorization` satisfies `sourceIdealDeflationLoop_fixed` under the displayed hypotheses. -/
theorem sourceIdealDeflationLoop_fixed {d : ℕ} (G : Fin (d+1) → Matrix Bool Bool ℂ)
    (hfixed : ∀ j,sourceConjugateSwap (G j)=G j) : sourceConjugateSwap (sourceIdealDeflationLoop G)=sourceIdealDeflationLoop G := by
  induction d with
  | zero => exact hfixed 0
  | succ m ih => exact ih (sourceIdealDeflationStep G) (sourceIdealDeflation_fixed G hfixed)

/-- The finite construction in `NativeSourceRotorFactorization` satisfies `source_ideal_terminal_matrix` under the displayed hypotheses. -/
theorem source_ideal_terminal_matrix (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    let B := sourceIdealDeflationLoop (sourceIdealMatrixArray cs N E)
    B=standardPhaseMatrix (B false false) := by
  let B := sourceIdealDeflationLoop (sourceIdealMatrixArray cs N E)
  have hb := source_ideal_terminal_base cs N E hE htail hparity hd hnorm
  have hf := sourceIdealDeflationLoop_fixed (sourceIdealMatrixArray cs N E) (sourceIdealArray_fixed cs N E)
  have h11 : B true true=star (B false false) := by
    exact (congrFun (congrFun hf true) true).symm
  change B=standardPhaseMatrix (B false false)
  have h01 : B false true=0 := hb.1
  have h10 : B true false=0 := hb.2.1
  ext i j
  cases i <;> cases j <;> simp [standardPhaseMatrix,h01,h10,h11]

/-- The finite construction in `NativeSourceRotorFactorization` satisfies `source_ideal_curve_packet` under the displayed hypotheses. -/
theorem source_ideal_curve_packet (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (theta : ℝ) :
    let G := sourceIdealMatrixArray cs N E
    sourceCompletionCircleValue G (theta : AddCircle (2*Real.pi))=
      standardPhaseMatrix (sourceIdealDeflationLoop G false false)*
        equatorialRotorProduct (sourceIdealDiscovered G).reverse (Real.cos theta) (Real.sin theta) := by
  let G := sourceIdealMatrixArray cs N E
  let h := sourceGrid N (sourceInputU cs N E)
  have hh : (0 : ℝ)<(h : ℝ) := by exact_mod_cast sourceGrid_pos N (sourceInputU cs N E)
  have hinv : SourceIdealDeflationInvariant G (h : ℝ) :=
    ⟨sourceIdealArray_circle_unitary cs N E hE htail hparity hd hnorm,
      source_ideal_extreme_lower cs N E hd 0 (Or.inl rfl),
      source_ideal_extreme_lower cs N E hd _ (Or.inr rfl)⟩
  have hfactor := sourceIdealDeflationLoop_rotor_factorization G (h : ℝ) hh hinv (sourceIdealArray_fixed cs N E) theta
  rw [source_ideal_terminal_matrix cs N E hE htail hparity hd hnorm] at hfactor
  exact hfactor

end IdealPacket

section RotorStability

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Matrix.Norms.L2Operator

/-- The estimate `sourceRotor_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceRotor_error (q w : ℂ) (x s : ℝ) :
    ‖equatorialRotor q x s-equatorialRotor w x s‖≤|s| * ‖q-w‖ := by
  have hid : equatorialRotor q x s-equatorialRotor w x s=
      (s : ℂ) • (standardPhaseMatrix (q-w)*standardSignalMatrix 0 1) := by
    ext i j
    cases i <;> cases j <;>
      simp [equatorialRotor,standardPhaseMatrix,standardSignalMatrix,Matrix.mul_apply] <;> ring
  have hW := unitary_norm_le_one (standardSignalMatrix_unitary 0 1 (by norm_num))
  rw [hid,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    ((norm_mul_le _ _).trans ((mul_le_mul (standardPhaseMatrix_norm_le _) hW
      (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _))) (abs_nonneg s)

/-- The actual finite word or frame satisfies `sourceRotor_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem sourceRotor_unitary (q : ℂ) (hq : ‖q‖=1) (x s : ℝ) (hs : s*s=1-x*x) :
    equatorialRotor q x s∈Matrix.unitaryGroup Bool ℂ := by
  have hqmul : q*star q=1 := by
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,hq]
    norm_num
  have hsc : (s : ℂ)*(s : ℂ)=1-(x : ℂ)*(x : ℂ) := by exact_mod_cast hs
  simp only [Complex.star_def] at hqmul
  rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose]
  ext i j
  cases i <;> cases j <;>
    simp [equatorialRotor,Matrix.mul_apply,Matrix.conjTranspose_apply] <;>
      ring_nf <;> simp only [Complex.I_sq,neg_mul,neg_neg,one_mul] <;>
        linear_combination hsc+(s : ℂ)^2*hqmul

/-- The estimate `sourceRotorProduct_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceRotorProduct_error {qs ws : List ℂ} (x s delta : ℝ)
    (hs : s*s=1-x*x) (hdelta : 0≤delta)
    (hp : List.Forall₂ (fun q w => ‖q‖=1 ∧ ‖w‖=1 ∧ ‖q-w‖≤delta) qs ws) :
    ‖equatorialRotorProduct qs x s‖≤1 ∧ ‖equatorialRotorProduct ws x s‖≤1 ∧
      ‖equatorialRotorProduct qs x s-equatorialRotorProduct ws x s‖≤(qs.length : ℝ)*delta := by
  have hsabs : |s|≤1 := by
    apply (sq_le_sq₀ (abs_nonneg s) (by norm_num : (0 : ℝ)≤1)).mp
    simpa only [sq_abs,one_pow] using (show s^2≤1 by nlinarith [sq_nonneg x])
  induction hp with
  | nil => simp [equatorialRotorProduct]
  | @cons q w qs ws hhead htail ih =>
    have hA := unitary_norm_le_one (sourceRotor_unitary q hhead.1 x s hs)
    have hB := unitary_norm_le_one (sourceRotor_unitary w hhead.2.1 x s hs)
    have hAB : ‖equatorialRotor q x s-equatorialRotor w x s‖≤delta :=
      (sourceRotor_error q w x s).trans ((mul_le_mul hsabs hhead.2.2 (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
    change ‖equatorialRotor q x s*equatorialRotorProduct qs x s‖≤1 ∧
      ‖equatorialRotor w x s*equatorialRotorProduct ws x s‖≤1 ∧ _
    refine ⟨(norm_mul_le _ _).trans ((mul_le_mul hA ih.1 (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)),
      (norm_mul_le _ _).trans ((mul_le_mul hB ih.2.1 (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)),?_⟩
    have hid : equatorialRotor q x s*equatorialRotorProduct qs x s-
        equatorialRotor w x s*equatorialRotorProduct ws x s=
        (equatorialRotor q x s-equatorialRotor w x s)*equatorialRotorProduct qs x s+
          equatorialRotor w x s*(equatorialRotorProduct qs x s-equatorialRotorProduct ws x s) := by
      rw [sub_mul,mul_sub]
      abel
    change ‖equatorialRotor q x s*equatorialRotorProduct qs x s-
      equatorialRotor w x s*equatorialRotorProduct ws x s‖≤((q::qs).length : ℝ)*delta
    rw [hid]
    calc
      _ ≤ ‖(equatorialRotor q x s-equatorialRotor w x s)*equatorialRotorProduct qs x s‖+
          ‖equatorialRotor w x s*(equatorialRotorProduct qs x s-equatorialRotorProduct ws x s)‖ := norm_add_le _ _
      _ ≤ ‖equatorialRotor q x s-equatorialRotor w x s‖*‖equatorialRotorProduct qs x s‖+
          ‖equatorialRotor w x s‖*‖equatorialRotorProduct qs x s-equatorialRotorProduct ws x s‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ delta*1+1*((qs.length : ℝ)*delta) := add_le_add
        (mul_le_mul hAB ih.1 (norm_nonneg _) hdelta)
        (mul_le_mul hB ih.2.2 (norm_nonneg _) (by norm_num))
      _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

end RotorStability

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
