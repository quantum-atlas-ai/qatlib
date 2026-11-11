/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceDeflationLoop
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceFirstDeflation
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Same-input complete coefficient deflation and incoming normalization guards.
This does not certify discovered phases, terminal base, full interpreter or costs. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

section OriginalLoop

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- The finite construction in `NativeSourceOriginalDeflation` satisfies `source_deflation_loop` under the displayed hypotheses. -/
theorem source_deflation_loop (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (m : ℕ) (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients (sourceIntegerComplement cs N E))
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) (sourceInputEta cs N E))
 :
    let F := sourceRoundedMatrix cs N E f
    let G := sourceIdealMatrixArray cs N E
    let eta := sourceInputEta cs N E
    let h := sourceGrid N (sourceInputU cs N E)
    let K := sourceK N (sourceInputU cs N E)
    SourceDeflationLoopGuards F eta ∧
      ‖sourceDecodeCompletionMatrix (sourceDeflationLoop F eta)-sourceIdealDeflationLoop G‖≤
        (K : ℝ)*(eta : ℝ)*(30/(h : ℝ))^(sourceDegree cs N E) ∧
      ‖sourceDecodeCompletionMatrix (sourceDeflationLoop F eta)-sourceIdealDeflationLoop G‖≤(h : ℝ)/16 := by
  let F := sourceRoundedMatrix cs N E f
  let G := sourceIdealMatrixArray cs N E
  let eta := sourceInputEta cs N E
  let h := sourceGrid N (sourceInputU cs N E)
  let K := sourceK N (sourceInputU cs N E)
  let delta : ℝ := (K : ℝ)*(eta : ℝ)
  have hb := source_initial_error_budget cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted
  have hh : (0 : ℝ)<(h : ℝ) := by exact_mod_cast sourceGrid_pos N (sourceInputU cs N E)
  have hh1 : (h : ℝ)≤1 := by
    dsimp [h,sourceGrid]
    push_cast
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have he : (0 : ℝ)<(eta : ℝ) := by dsimp [eta,sourceInputEta]; positivity
  have hd0 : 0≤delta := he.le.trans hb.1
  have hlarge : (1 : ℝ)≤128/(h : ℝ) := (le_div_iff₀ hh).mpr (by linarith)
  have hpower : (30/(h : ℝ))^(sourceDegree cs N E)≤(128/(h : ℝ))^(N+1) :=
    (pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_right (by norm_num : (30 : ℝ)≤128) hh.le) _).trans
      (pow_le_pow_right₀ hlarge (Nat.le_succ_of_le (sourceDegree_le cs N E)))
  have hbudget : delta*(128/(h : ℝ))^(N+1)≤(h : ℝ)/16 := by
    dsimp only [delta,K,eta,h]
    exact_mod_cast (source_input_budget cs N E hE).1
  have hfinal : delta*(30/(h : ℝ))^(sourceDegree cs N E)≤(h : ℝ)/16 :=
    (mul_le_mul_of_nonneg_left hpower hd0).trans hbudget
  have hinv : SourceIdealDeflationInvariant G (h : ℝ) :=
    ⟨sourceIdealArray_circle_unitary cs N E hE htail hparity hd hnorm,
      source_ideal_extreme_lower cs N E hd 0 (Or.inl rfl),
      source_ideal_extreme_lower cs N E hd _ (Or.inr rfl)⟩
  have hs := sourceDeflationLoop_error F G eta (by dsimp [eta,sourceInputEta]; positivity)
    delta (h : ℝ) hh hh1 hb.1 hinv hb.2.2 (by linarith)
  exact ⟨hs.1,hs.2,hs.2.trans hfinal⟩

end OriginalLoop

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
