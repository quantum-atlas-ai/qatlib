/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceTerminalBase
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeEquatorialHalfPhase
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Original-input, accepted-certificate nonconstant source packet: RoundedPhases.
Value and physical-word guarantees here do not certify a root proposer, Python interpreter or total costs. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section RoundedDiscovered

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open scoped Matrix.Norms.L2Operator

/-- The finite construction in `NativeSourceRoundedPhases` satisfies `sourceCoordinate_eq_gaussian` under the displayed hypotheses. -/
theorem sourceCoordinate_eq_gaussian (q : ℚ×ℚ) : rootRationalCoordinate q=gaussianRatComplex q := by
  apply Complex.ext <;> simp [rootRationalCoordinate,gaussianRatComplex]

/-- Construction for source Round Phases in the native source rounded phases model. -/
def sourceRoundPhases (qs : List (ℚ×ℚ)) (p : ℕ) : List (ℚ×ℚ) :=
  qs.map (fun q => nativePhasePair q.1 q.2 p)

/-- Construction for source Half Phases in the native source rounded phases model. -/
def sourceHalfPhases (qs : List (ℚ×ℚ)) (p : ℕ) : List (ℚ×ℚ) :=
  qs.map (fun q => nativeEquatorialHalfPhase q p)

/-- The estimate `sourceRoundPhases_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceRoundPhases_error {qs : List (ℚ×ℚ)} {zs : List ℂ} (p : ℕ) (rho : ℝ) (hrho : rho<1)
    (he : List.Forall₂ (fun q z => ‖rootRationalCoordinate q-z‖≤rho) qs zs)
    (hz : ∀ z∈zs,‖z‖=1) :
    List.Forall₂ (fun q z => ‖gaussianRatComplex q‖=1 ∧
      ‖gaussianRatComplex q-z‖≤2*rho+1/(16*(2 : ℝ)^p)) (sourceRoundPhases qs p) zs := by
  induction he with
  | nil => exact List.Forall₂.nil
  | @cons q z qs zs hhead htail ih =>
    exact List.Forall₂.cons
      (nativePhasePair_error_of_unit q.1 q.2 p z rho (hz z List.mem_cons_self) hrho
        (by rwa [← sourceCoordinate_eq_gaussian]))
      (ih (fun w hw => hz w (List.mem_cons_of_mem _ hw)))

/-- The finite construction in `NativeSourceRoundedPhases` satisfies `rational_norm_equation` under the displayed hypotheses. -/
private theorem rational_norm_equation (q : ℚ×ℚ) (hq : ‖gaussianRatComplex q‖=1) :
    q.1*q.1+q.2*q.2=1 := by
  have hs : ‖gaussianRatComplex q‖^2=(1 : ℝ) := by rw [hq]; norm_num
  rw [Complex.sq_norm,Complex.normSq_apply] at hs
  norm_num [gaussianRatComplex] at hs
  exact_mod_cast hs

/-- The estimate `sourceHalfPhases_squared_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceHalfPhases_squared_error {qs : List (ℚ×ℚ)} {zs : List ℂ} (p : ℕ) (rho : ℝ)
    (he : List.Forall₂ (fun q z => ‖gaussianRatComplex q‖=1 ∧
      ‖gaussianRatComplex q-z‖≤2*rho+1/(16*(2 : ℝ)^p)) qs zs) :
    List.Forall₂ (fun u z => ‖gaussianRatComplex u‖=1 ∧
      ‖(gaussianRatComplex u)^2-z‖≤2*rho+3/(16*(2 : ℝ)^p)) (sourceHalfPhases qs p) zs := by
  induction he with
  | nil => exact List.Forall₂.nil
  | @cons q z qs zs hhead htail ih =>
    refine List.Forall₂.cons ⟨nativeEquatorialHalfPhase_norm q p,?_⟩ ih
    calc
      _ ≤ ‖(gaussianRatComplex (nativeEquatorialHalfPhase q p))^2-gaussianRatComplex q‖+
          ‖gaussianRatComplex q-z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 1/(8*(2 : ℝ)^p)+(2*rho+1/(16*(2 : ℝ)^p)) :=
        add_le_add (nativeEquatorialHalfPhase_square_error q p (rational_norm_equation q hhead.1)) hhead.2
      _ = _ := by ring

end RoundedDiscovered

section OriginalRounded

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- Construction for source Packet Precision in the native source rounded phases model. -/
def sourcePacketPrecision (cs : List ℚ) (N : ℕ) (E : ℚ) : ℕ :=
  sourceCeilLog2 ((N+1 : ℚ)/sourceInputU cs N E)

/-- The finite construction in `NativeSourceRoundedPhases` satisfies `source_rounded_halves` under the displayed hypotheses. -/
theorem source_rounded_halves (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
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
    let p := sourcePacketPrecision cs N E
    let C := sourceDeflationLoop F eta
    let b := nativePhasePair (C false false).1 (C false false).2 p
    ‖gaussianRatComplex b‖=1 ∧
      ‖gaussianRatComplex b-sourceIdealDeflationLoop G false false‖≤(h : ℝ)/8+1/(16*(2 : ℝ)^p) ∧
      List.Forall₂ (fun u z => ‖gaussianRatComplex u‖=1 ∧
        ‖(gaussianRatComplex u)^2-z‖≤7*(h : ℝ)/20+3/(16*(2 : ℝ)^p))
        (sourceHalfPhases (sourceRoundPhases (sourceDiscoveredGaussian F eta).reverse p) p) (sourceIdealDiscovered G).reverse := by
  let F := sourceRoundedMatrix cs N E f
  let G := sourceIdealMatrixArray cs N E
  let eta := sourceInputEta cs N E
  let h := sourceGrid N (sourceInputU cs N E)
  let p := sourcePacketPrecision cs N E
  let C := sourceDeflationLoop F eta
  have hs := source_discovered_error_grid cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted
  have hh1 : (h : ℝ)≤1 := by
    dsimp [h,sourceGrid]
    push_cast
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have he : List.Forall₂ (fun q z => ‖rootRationalCoordinate q-z‖≤7*(h : ℝ)/40)
      (sourceDiscoveredGaussian F eta) (sourceIdealDiscovered G) := by
    apply (List.forall₂_map_left_iff
      (R := fun z w : ℂ => ‖z-w‖≤7*(h : ℝ)/40) (f := rootRationalCoordinate)).mp
    rw [sourceDiscovered_decode]
    exact hs.1
  have hrev := List.forall₂_reverse_iff.mpr he
  have hz : ∀ z∈(sourceIdealDiscovered G).reverse,‖z‖=1 := by
    intro z hmem
    exact hs.2.1 z (List.mem_reverse.mp hmem)
  have hr := sourceRoundPhases_error p (7*(h : ℝ)/40) (by linarith) hrev hz
  have hhalf := sourceHalfPhases_squared_error p (7*(h : ℝ)/40) hr
  have hb := source_actual_terminal_base cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted
  have hbe : ‖gaussianRatComplex (C false false)-sourceIdealDeflationLoop G false false‖≤(h : ℝ)/16 := by
    rw [← sourceCoordinate_eq_gaussian]
    exact hb.2.1
  have hround := nativePhasePair_error_of_unit (C false false).1 (C false false).2 p
    (sourceIdealDeflationLoop G false false) ((h : ℝ)/16) hb.1 (by linarith) hbe
  refine ⟨hround.1,?_,?_⟩
  · convert hround.2 using 1; ring
  · have heq : 2*(7*(h : ℝ)/40)+3/(16*(2 : ℝ)^p)=7*(h : ℝ)/20+3/(16*(2 : ℝ)^p) := by ring
    simpa only [heq] using hhalf

end OriginalRounded

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
