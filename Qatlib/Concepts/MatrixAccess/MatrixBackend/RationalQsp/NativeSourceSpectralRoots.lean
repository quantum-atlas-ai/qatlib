/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceProducerGuards
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Same original-input spectral completion: SpectralRoots.
This does not certify the full proposer, iterative deflation, interpreter or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section SpectralRoots

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Polynomial

/-- Construction for source Reciprocal Conjugate in the native source spectral roots model. -/
def sourceReciprocalConjugate (z : ℂ) : ℂ := (star z)⁻¹

/-- The finite construction in `NativeSourceSpectralRoots` satisfies `sourceF_map_conj` under the displayed hypotheses. -/
theorem sourceF_map_conj (cs : List ℚ) (N : ℕ) (E : ℚ) :
    (sourceF cs N E).map (starRingEnd ℂ)=sourceF cs N E := by
  unfold sourceF
  rw [Polynomial.map_map]
  congr 1
  ext q
  simp

/-- The finite construction in `NativeSourceSpectralRoots` satisfies `sourceF_conj_roots` under the displayed hypotheses. -/
private theorem sourceF_conj_roots (cs : List ℚ) (N : ℕ) (E : ℚ) :
    (sourceF cs N E).roots.map (fun z : ℂ => star z)=(sourceF cs N E).roots := by
  have h := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (p := sourceF cs N E) (f := starRingEnd ℂ) (star_injective)
    (IsAlgClosed.card_roots_eq_natDegree (p := sourceF cs N E))
  simpa only [sourceF_map_conj, show (starRingEnd ℂ : ℂ → ℂ) = (fun z => star z) from rfl] using h

/-- The finite construction in `NativeSourceSpectralRoots` satisfies `sourceF_reciprocalConjugate_roots` under the displayed hypotheses. -/
private theorem sourceF_reciprocalConjugate_roots (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hd : 0<sourceDegree cs N E) :
    (sourceF cs N E).roots.map sourceReciprocalConjugate=(sourceF cs N E).roots := by
  calc
    _ = ((sourceF cs N E).roots.map (fun z : ℂ => star z)).map (fun z => z⁻¹) := by
      rw [Multiset.map_map]
      rfl
    _ = (sourceF cs N E).roots.map (fun z => z⁻¹) := by rw [sourceF_conj_roots]
    _ = _ := sourceF_inverse_roots cs N E hd

/-- The finite construction in `NativeSourceSpectralRoots` satisfies `split_inside_reciprocalConjugate` under the displayed hypotheses. -/
private theorem split_inside_reciprocalConjugate (l : Multiset ℂ)
    (hmap : l.map sourceReciprocalConjugate=l)
    (hnz : ∀ z∈l,z≠0) (hunit : ∀ z∈l,‖z‖≠1) :
    l=l.filter (fun z => ‖z‖<1)+(l.filter (fun z => ‖z‖<1)).map sourceReciprocalConjugate := by
  classical
  have hout : l.filter (fun z => 1<‖z‖)=(l.filter (fun z => ‖z‖<1)).map sourceReciprocalConjugate := by
    calc
      _ = (l.map sourceReciprocalConjugate).filter (fun z => 1<‖z‖) := by rw [hmap]
      _ = (l.filter (fun z => 1<‖sourceReciprocalConjugate z‖)).map sourceReciprocalConjugate := by
        rw [Multiset.filter_map]
        rfl
      _ = _ := by
        congr 1
        apply Multiset.filter_congr
        intro z hz
        simp only [sourceReciprocalConjugate,norm_inv,norm_star]
        exact one_lt_inv₀ (norm_pos_iff.mpr (hnz z hz))
  have hnot : l.filter (fun z => ¬‖z‖<1)=l.filter (fun z => 1<‖z‖) := by
    apply Multiset.filter_congr
    intro z hz
    exact not_lt.trans (le_iff_lt_or_eq.trans (or_iff_left (Ne.symm (hunit z hz))))
  have h := Multiset.filter_add_not (fun z : ℂ => ‖z‖<1) l
  rw [hnot,hout] at h
  exact h.symm

/-- The finite construction in `NativeSourceSpectralRoots` satisfies `sourceF_roots_split` under the displayed hypotheses. -/
theorem sourceF_roots_split (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    (sourceF cs N E).roots=(sourceF cs N E).roots.filter (fun z => ‖z‖<1)+
      ((sourceF cs N E).roots.filter (fun z => ‖z‖<1)).map sourceReciprocalConjugate := by
  apply split_inside_reciprocalConjugate _ (sourceF_reciprocalConjugate_roots cs N E hd)
  · intro z hz hzero
    subst z
    exact sourceF_eval_zero_ne cs N E hd (Polynomial.isRoot_of_mem_roots hz)
  · intro z hz
    exact sourceF_no_unit_zero cs N E hE htail hparity hd hnorm z
      (Polynomial.isRoot_of_mem_roots hz)

end SpectralRoots

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
