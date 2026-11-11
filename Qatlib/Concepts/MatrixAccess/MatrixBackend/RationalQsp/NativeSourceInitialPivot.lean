/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceGramTrace
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Same original-input Gaussian Gram normalization and first deflation: InitialPivot.
This does not certify subsequent ideal preservation, the whole loop, interpreter or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section InitialPivot

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- The finite construction in `NativeSourceInitialPivot` satisfies `raw_diagonal_im_difference` under the displayed hypotheses. -/
theorem raw_diagonal_im_difference {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (f : Fin m → RootIntegerFactorData) (j : Fin (sourceDegree cs N E+1)) :
    (sourceRawMatrix cs N E f j false false).2-(sourceRawMatrix cs N E f j true true).2=
      2*sourceRealArray cs N E j := by
  let a := sourceRealArray cs N E j
  let v := sourceStoredE cs N E f j
  let w := ((sourceStoredE cs N E f j.rev).1,-(sourceStoredE cs N E f j.rev).2)
  let C : ℚ×ℚ := ((1/2)*(v+w).1,(1/2)*(v+w).2)
  change (gaussianRatMul (0,1) ((a,0)+gaussianRatMul (0,1) C)).2-
    (gaussianRatMul (0,-1) ((a,0)-gaussianRatMul (0,1) C)).2=2*a
  simp [gaussianRatMul]
  ring


/-- The finite construction in `NativeSourceInitialPivot` satisfies `grid_nonzero_lower` under the displayed hypotheses. -/
private theorem grid_nonzero_lower (x h : ℚ) (hh : 0<h) (hn : rootGridTruncate x h≠0) :
    h ≤ |rootGridTruncate x h| := by
  have hk : ⌊|x|/h⌋₊≠0 := by
    intro hk
    apply hn
    simp [rootGridTruncate,hk]
  have hcast : (1 : ℚ) ≤ (⌊|x|/h⌋₊ : ℚ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
  have hb : h ≤ (⌊|x|/h⌋₊ : ℚ)*h := by nlinarith
  have hb0 : (0 : ℚ) ≤ (⌊|x|/h⌋₊ : ℚ)*h := by positivity
  unfold rootGridTruncate
  split_ifs <;> simpa only [abs_neg,abs_of_nonneg hb0] using hb

/-- The finite construction in `NativeSourceInitialPivot` satisfies `source_grid_le_one` under the displayed hypotheses. -/
private theorem source_grid_le_one (N : ℕ) (u : ℚ) : sourceGrid N u ≤ 1 := by
  unfold sourceGrid
  exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))

/-- The finite construction in `NativeSourceInitialPivot` satisfies `source_eta_le_grid` under the displayed hypotheses. -/
theorem source_eta_le_grid (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E) :
    sourceInputEta cs N E ≤ sourceGrid N (sourceInputU cs N E)/16 := by
  let u := sourceInputU cs N E
  let h := sourceGrid N u
  let eta := sourceInputEta cs N E
  have hu : 0<u := sourceInputU_pos cs N E hE
  have hu1 : u ≤ 1/2 := sourceInputU_le_half cs N E
  have hh : 0<h := sourceGrid_pos N u
  have hh1 : h ≤ 1 := source_grid_le_one N u
  have he : 0<eta := by dsimp [eta,sourceInputEta]; positivity
  have hN1 : (1 : ℚ) ≤ N+1 := by have h : (0 : ℚ) ≤ N := Nat.cast_nonneg N; linarith
  have hN6 : (1 : ℚ) ≤ (N+1 : ℚ)^6 := one_le_pow₀ hN1
  have hK : (1 : ℚ) ≤ sourceK N u := by
    unfold sourceK
    apply (le_div_iff₀ (sq_pos_of_pos hu)).mpr
    norm_num only [show (2 : ℚ)^20=1048576 by norm_num]
    nlinarith
  have hL : (1 : ℚ) ≤ 128/h := (le_div_iff₀ hh).mpr (by linarith)
  have hpow : (1 : ℚ) ≤ (128/h)^(N+1) := one_le_pow₀ hL
  have hb := (source_input_budget cs N E hE).1
  change sourceK N u*eta*(128/h)^(N+1) ≤ h/16 at hb
  calc
    _ ≤ sourceK N u*eta := by nlinarith
    _ ≤ sourceK N u*eta*(128/h)^(N+1) := le_mul_of_one_le_right (by positivity) hpow
    _ ≤ h/16 := hb

/-- The finite construction in `NativeSourceInitialPivot` satisfies `source_real_last` under the displayed hypotheses. -/
private theorem source_real_last (cs : List ℚ) (N : ℕ) (E : ℚ) :
    sourceRealArray cs N E (Fin.last (sourceDegree cs N E))=
      sourceCoefficient cs N E ⟨sourceDegree cs N E,by have h := sourceDegree_le cs N E; omega⟩ := by
  unfold sourceRealArray sourceP sourceLiftedArray
  congr 1
  apply Fin.ext
  change Nat.dist (2*sourceDegree cs N E) (sourceDegree cs N E)=sourceDegree cs N E
  simp only [Nat.dist]
  omega

/-- The finite construction in `NativeSourceInitialPivot` satisfies `source_real_last_grid_lower` under the displayed hypotheses. -/
theorem source_real_last_grid_lower (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hd : 0<sourceDegree cs N E) :
    sourceGrid N (sourceInputU cs N E) ≤ |sourceRealArray cs N E (Fin.last (sourceDegree cs N E))| := by
  obtain ⟨i,hi,hv⟩ := sourceArrayDegree_leading (sourceCoefficient cs N E) hd
  have he : i=⟨sourceDegree cs N E,by have h := sourceDegree_le cs N E; omega⟩ := by
    apply Fin.ext
    exact hv.symm
  rw [he] at hi
  rw [source_real_last]
  exact grid_nonzero_lower _ _ (sourceGrid_pos _ _) hi


/-- The finite construction in `NativeSourceInitialPivot` satisfies `source_real_extreme` under the displayed hypotheses. -/
private theorem source_real_extreme (cs : List ℚ) (N : ℕ) (E : ℚ)
    (j : Fin (sourceDegree cs N E+1)) (hj : j.val=0 ∨ j.val=sourceDegree cs N E) :
    sourceRealArray cs N E j=sourceRealArray cs N E (Fin.last (sourceDegree cs N E)) := by
  rw [source_real_last]
  unfold sourceRealArray sourceP sourceLiftedArray
  congr 1
  apply Fin.ext
  change Nat.dist (2*j.val) (sourceDegree cs N E)=sourceDegree cs N E
  rcases hj with hj|hj <;> rw [hj] <;> simp only [Nat.dist] <;> omega

/-- The finite construction in `NativeSourceInitialPivot` satisfies `rounded_nonzero_of_real_lower` under the displayed hypotheses. -/
private theorem rounded_nonzero_of_real_lower {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hE : 0<E) (f : Fin m → RootIntegerFactorData) (j : Fin (sourceDegree cs N E+1))
    (ha : sourceGrid N (sourceInputU cs N E) ≤ |sourceRealArray cs N E j|) :
    ∃ i k,sourceRoundedMatrix cs N E f j i k≠(0,0) := by
  by_contra hn
  push Not at hn
  have h00 : rootGridTruncate (sourceRawMatrix cs N E f j false false).2 (sourceInputEta cs N E/8)=0 := by
    exact congrArg Prod.snd (hn false false)
  have h11 : rootGridTruncate (sourceRawMatrix cs N E f j true true).2 (sourceInputEta cs N E/8)=0 := by
    exact congrArg Prod.snd (hn true true)
  have heta : 0<sourceInputEta cs N E := by unfold sourceInputEta; positivity
  have h0 := (rootGridTruncate_spec (sourceRawMatrix cs N E f j false false).2
    (sourceInputEta cs N E/8) (by positivity)).2
  have h1 := (rootGridTruncate_spec (sourceRawMatrix cs N E f j true true).2
    (sourceInputEta cs N E/8) (by positivity)).2
  rw [h00,zero_sub,abs_neg] at h0
  rw [h11,zero_sub,abs_neg] at h1
  have ht : |(sourceRawMatrix cs N E f j false false).2-(sourceRawMatrix cs N E f j true true).2| ≤
      |(sourceRawMatrix cs N E f j false false).2|+|(sourceRawMatrix cs N E f j true true).2| := by
    simpa only [sub_zero,zero_sub,abs_neg] using
      (abs_sub_le (sourceRawMatrix cs N E f j false false).2 0
        (sourceRawMatrix cs N E f j true true).2)
  rw [raw_diagonal_im_difference,abs_mul] at ht
  norm_num at ht
  have hb := source_eta_le_grid cs N E hE
  have hh := sourceGrid_pos N (sourceInputU cs N E)
  linarith

/-- The finite construction in `NativeSourceInitialPivot` satisfies `source_initial_extreme_nonzero` under the displayed hypotheses. -/
theorem source_initial_extreme_nonzero {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hE : 0<E) (hd : 0<sourceDegree cs N E) (f : Fin m → RootIntegerFactorData)
    (j : Fin (sourceDegree cs N E+1)) (hj : j.val=0 ∨ j.val=sourceDegree cs N E) :
    ∃ i k,sourceRoundedMatrix cs N E f j i k≠(0,0) := by
  apply rounded_nonzero_of_real_lower cs N E hE f j
  rw [source_real_extreme cs N E j hj]
  exact source_real_last_grid_lower cs N E hd

/-- The finite construction in `NativeSourceInitialPivot` satisfies `source_initial_extreme_gram_guard` under the displayed hypotheses. -/
theorem source_initial_extreme_gram_guard {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hE : 0<E) (hd : 0<sourceDegree cs N E) (f : Fin m → RootIntegerFactorData)
    (j : Fin (sourceDegree cs N E+1)) (hj : j.val=0 ∨ j.val=sourceDegree cs N E) :
    (sourceGaussianGramTrace (sourceRoundedMatrix cs N E f j)).2=0 ∧
      0<(sourceGaussianGramTrace (sourceRoundedMatrix cs N E f j)).1 := by
  exact sourceGaussianGramTrace_guard _ (source_initial_extreme_nonzero cs N E hE hd f j hj)

end InitialPivot

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
