/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceRoundedPhases
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourcePacketPadding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Original-input, accepted-certificate nonconstant source packet: PacketAccuracy.
Value and physical-word guarantees here do not certify a root proposer, Python interpreter or total costs. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section PacketBudget

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- The finite construction in `NativeSourcePacketAccuracy` satisfies `source_output_rounding_budget` under the displayed hypotheses. -/
theorem source_output_rounding_budget (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E) :
    1/(16*(2 : ℝ)^(sourcePacketPrecision cs N E))≤(sourceInputU cs N E : ℝ)/(16*(N+1 : ℝ)) := by
  let u := sourceInputU cs N E
  let p := sourcePacketPrecision cs N E
  have hu : 0<u := sourceInputU_pos cs N E hE
  have hc : (N+1 : ℚ)/u≤(2 : ℚ)^p := sourceCeilLog2_envelope _ (by positivity)
  have hcross : (N+1 : ℚ)≤(2 : ℚ)^p*u := (div_le_iff₀ hu).mp hc
  have hrec : (1 : ℚ)/(2 : ℚ)^p≤u/(N+1 : ℚ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    simpa only [one_mul,mul_comm] using hcross
  have hsmall := div_le_div_of_nonneg_right hrec (by norm_num : (0 : ℚ)≤16)
  have hq : (1 : ℚ)/(16*(2 : ℚ)^p)≤u/(16*(N+1 : ℚ)) := by
    convert hsmall using 1 <;>
      field_simp [show (N+1 : ℚ)≠0 by positivity]
  have hr := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at hr
  exact hr

/-- The finite construction in `NativeSourcePacketAccuracy` satisfies `numeric_budget` under the displayed hypotheses. -/
private theorem numeric_budget (M d u h r : ℝ) (hM : 2≤M) (hu : 0≤u) (hh : 0≤h) (hr : 0≤r)
    (hd : d≤M) (hhb : h≤u/(64*M)) (hrb : r≤u/(16*M)) :
    h/8+r+d*(7*h/20+3*r)≤u/4 := by
  have hhm := (le_div_iff₀ (show 0<64*M by positivity)).mp hhb
  have hrm := (le_div_iff₀ (show 0<16*M by positivity)).mp hrb
  have hM2h : 0≤(M-2)*h := mul_nonneg (by linarith) hh
  have hM2r : 0≤(M-2)*r := mul_nonneg (by linarith) hr
  have hdh := mul_le_mul_of_nonneg_right hd hh
  have hdr := mul_le_mul_of_nonneg_right hd hr
  nlinarith

/-- The finite construction in `NativeSourcePacketAccuracy` satisfies `source_packet_budget` under the displayed hypotheses. -/
theorem source_packet_budget (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (hd : 0<sourceDegree cs N E) :
    let u := sourceInputU cs N E
    let h := sourceGrid N u
    let p := sourcePacketPrecision cs N E
    let r := 1/(16*(2 : ℝ)^p)
    (h : ℝ)/8+r+(sourceDegree cs N E : ℝ)*(7*(h : ℝ)/20+3*r)≤(u : ℝ)/4 := by
  let u := sourceInputU cs N E
  let h := sourceGrid N u
  let p := sourcePacketPrecision cs N E
  let r : ℝ := 1/(16*(2 : ℝ)^p)
  have hu : 0<u := sourceInputU_pos cs N E hE
  have hh : (0 : ℝ)<(h : ℝ) := by exact_mod_cast sourceGrid_pos N u
  have hM : (2 : ℝ)≤N+1 := by
    have hN : 1≤N := (Nat.succ_le_of_lt hd).trans (sourceDegree_le cs N E)
    exact_mod_cast Nat.add_le_add_right hN 1
  have hdM : (sourceDegree cs N E : ℝ)≤N+1 := by
    exact_mod_cast Nat.le_succ_of_le (sourceDegree_le cs N E)
  have hgrid : (h : ℝ)≤(u : ℝ)/(64*(N+1 : ℝ)) := by exact_mod_cast sourceGrid_upper N u hu
  exact numeric_budget (N+1 : ℝ) (sourceDegree cs N E) u h r hM (by exact_mod_cast hu.le)
    hh.le (by positivity) hdM hgrid (source_output_rounding_budget cs N E hE)

end PacketBudget

section PacketAccuracy

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open scoped Matrix.Norms.L2Operator

/-- The finite construction in `NativeSourcePacketAccuracy` satisfies `squared_pair` under the displayed hypotheses. -/
private theorem squared_pair {us : List GaussianRat} {qs : List ℂ} (delta : ℝ)
    (hp : List.Forall₂ (fun u q => ‖gaussianRatComplex u‖=1 ∧ ‖(gaussianRatComplex u)^2-q‖≤delta) us qs)
    (hq : ∀ q∈qs,‖q‖=1) :
    List.Forall₂ (fun z q => ‖z‖=1 ∧ ‖q‖=1 ∧ ‖z-q‖≤delta)
      (us.map (fun u => (gaussianRatComplex u)^2)) qs := by
  induction hp with
  | nil => exact List.Forall₂.nil
  | @cons u q us qs hhead htail ih =>
    exact List.Forall₂.cons ⟨by rw [norm_pow,hhead.1,one_pow],hq q List.mem_cons_self,hhead.2⟩
      (ih (fun q hmem => hq q (List.mem_cons_of_mem _ hmem)))

/-- The estimate `boundary_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem boundary_error (base : GaussianRat) (us : List GaussianRat) (z : ℂ) (qs : List ℂ)
    (x s db delta : ℝ) (hs : s*s=1-x*x) (hdb : 0≤db) (hdelta : 0≤delta)
    (hb : ‖gaussianRatComplex base-z‖≤db) (hz : ‖z‖=1)
    (hp : List.Forall₂ (fun u q => ‖gaussianRatComplex u‖=1 ∧ ‖(gaussianRatComplex u)^2-q‖≤delta) us qs)
    (hq : ∀ q∈qs,‖q‖=1) :
    let data := nativeEquatorialBoundaryPacket base us
    ‖standardMatrixWord (gaussianRatComplex data.base) x s (data.phases.map gaussianRatComplex)-
      standardPhaseMatrix z*equatorialRotorProduct qs x s‖≤db+(us.length : ℝ)*delta := by
  have hu : ∀ u∈us,‖gaussianRatComplex u‖=1 := ((List.forall₂_and_left us qs).mp hp).1
  dsimp only
  rw [nativeEquatorialBoundaryPacket_matrix base us x s hu]
  have hprod := sourceRotorProduct_error x s delta hs hdelta (squared_pair delta hp hq)
  simp only [List.length_map] at hprod
  have hD := (standardPhaseMatrix_error (gaussianRatComplex base) z).trans hb
  have hDz : ‖standardPhaseMatrix z‖≤1 := (standardPhaseMatrix_norm_le z).trans_eq hz
  have hid : standardPhaseMatrix (gaussianRatComplex base)*
      equatorialRotorProduct (us.map (fun u => (gaussianRatComplex u)^2)) x s-
      standardPhaseMatrix z*equatorialRotorProduct qs x s=
      (standardPhaseMatrix (gaussianRatComplex base)-standardPhaseMatrix z)*
        equatorialRotorProduct (us.map (fun u => (gaussianRatComplex u)^2)) x s+
      standardPhaseMatrix z*(equatorialRotorProduct (us.map (fun u => (gaussianRatComplex u)^2)) x s-
        equatorialRotorProduct qs x s) := by
    rw [sub_mul,mul_sub]
    abel
  rw [hid]
  calc
    _ ≤ ‖(standardPhaseMatrix (gaussianRatComplex base)-standardPhaseMatrix z)*
          equatorialRotorProduct (us.map (fun u => (gaussianRatComplex u)^2)) x s‖+
        ‖standardPhaseMatrix z*(equatorialRotorProduct (us.map (fun u => (gaussianRatComplex u)^2)) x s-
          equatorialRotorProduct qs x s)‖ := norm_add_le _ _
    _ ≤ ‖standardPhaseMatrix (gaussianRatComplex base)-standardPhaseMatrix z‖*
          ‖equatorialRotorProduct (us.map (fun u => (gaussianRatComplex u)^2)) x s‖+
        ‖standardPhaseMatrix z‖*‖equatorialRotorProduct (us.map (fun u => (gaussianRatComplex u)^2)) x s-
          equatorialRotorProduct qs x s‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ db*1+1*((us.length : ℝ)*delta) := add_le_add
      (mul_le_mul hD hprod.1 (norm_nonneg _) hdb)
      (mul_le_mul hDz hprod.2.2 (norm_nonneg _) (by norm_num))
    _ = _ := by ring

/-- Construction for source Unpadded Halves in the native source packet accuracy model. -/
def sourceUnpaddedHalves {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ) (f : Fin m → RootIntegerFactorData) : List GaussianRat :=
  let F := sourceRoundedMatrix cs N E f
  let eta := sourceInputEta cs N E
  let p := sourcePacketPrecision cs N E
  sourceHalfPhases (sourceRoundPhases (sourceDiscoveredGaussian F eta).reverse p) p

/-- Construction for source Packet Base in the native source packet accuracy model. -/
def sourcePacketBase {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ) (f : Fin m → RootIntegerFactorData) : GaussianRat :=
  let C := sourceDeflationLoop (sourceRoundedMatrix cs N E f) (sourceInputEta cs N E)
  nativePhasePair (C false false).1 (C false false).2 (sourcePacketPrecision cs N E)

/-- Construction for source Padded Halves in the native source packet accuracy model. -/
def sourcePaddedHalves {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ) (f : Fin m → RootIntegerFactorData) : List GaussianRat :=
  sourceUnpaddedHalves cs N E f++sourcePaddingHalves ((N-sourceDegree cs N E)/2)

/-- Construction for source Boundary Packet in the native source packet accuracy model. -/
def sourceBoundaryPacket {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ) (f : Fin m → RootIntegerFactorData) : PhaseData :=
  nativeEquatorialBoundaryPacket (sourcePacketBase cs N E f) (sourcePaddedHalves cs N E f)

/-- The same emitted instruction list satisfies `source_unpadded_length` with the displayed gate and query accounting. -/
theorem source_unpadded_length {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ) (f : Fin m → RootIntegerFactorData) :
    (sourceUnpaddedHalves cs N E f).length=sourceDegree cs N E := by
  simp only [sourceUnpaddedHalves,sourceHalfPhases,sourceRoundPhases,List.length_map,List.length_reverse]
  have hl := congrArg List.length (sourceDiscovered_decode (sourceRoundedMatrix cs N E f) (sourceInputEta cs N E))
  simpa only [List.length_map,sourceDiscovered_length] using hl

/-- The finite construction in `NativeSourcePacketAccuracy` satisfies `source_unpadded_unit` under the displayed hypotheses. -/
theorem source_unpadded_unit {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ) (f : Fin m → RootIntegerFactorData) :
    ∀ u∈sourceUnpaddedHalves cs N E f,‖gaussianRatComplex u‖=1 := by
  intro u hu
  change u∈List.map (fun q => nativeEquatorialHalfPhase q (sourcePacketPrecision cs N E)) _ at hu
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hu
  exact nativeEquatorialHalfPhase_norm q _

/-- The finite construction in `NativeSourcePacketAccuracy` satisfies `source_padded_unit` under the displayed hypotheses. -/
theorem source_padded_unit {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ) (f : Fin m → RootIntegerFactorData) :
    ∀ u∈sourcePaddedHalves cs N E f,‖gaussianRatComplex u‖=1 := by
  intro u hu
  rcases List.mem_append.mp hu with hu|hu
  · exact source_unpadded_unit cs N E f u hu
  · exact sourcePaddingHalves_norm _ u hu

/-- The estimate `source_boundary_packet_spec` retains the actual parameter, input-error and normalization budgets. -/
theorem source_boundary_packet_spec {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) (f : Fin m → RootIntegerFactorData) :
    (sourceBoundaryPacket cs N E f).phases.length=N ∧
      ‖gaussianRatComplex (sourceBoundaryPacket cs N E f).base‖=1 ∧
      ∀ z∈(sourceBoundaryPacket cs N E f).phases,‖gaussianRatComplex z‖=1 := by
  have hs := nativeEquatorialBoundaryPacket_spec (sourcePacketBase cs N E f) (sourcePaddedHalves cs N E f)
    (nativePhasePair_norm _ _ _) (source_padded_unit cs N E f)
  refine ⟨hs.1.trans ?_,hs.2⟩
  exact source_padding_length cs N E hparity hd _ (source_unpadded_length cs N E f)

/-- The estimate `source_boundary_packet_error` retains the actual parameter, input-error and normalization budgets. -/
theorem source_boundary_packet_error (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
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
    (theta : ℝ) :
    let data := sourceBoundaryPacket cs N E f
    let G := sourceIdealMatrixArray cs N E
    ‖standardMatrixWord (gaussianRatComplex data.base) (Real.cos theta) (Real.sin theta)
        (data.phases.map gaussianRatComplex)-sourceCompletionCircleValue G (theta : AddCircle (2*Real.pi))‖≤
      (sourceInputU cs N E : ℝ)/4 := by
  let G := sourceIdealMatrixArray cs N E
  let h := sourceGrid N (sourceInputU cs N E)
  let p := sourcePacketPrecision cs N E
  let r : ℝ := 1/(16*(2 : ℝ)^p)
  let b := sourcePacketBase cs N E f
  let us := sourceUnpaddedHalves cs N E f
  let k := (N-sourceDegree cs N E)/2
  let qs := (sourceIdealDiscovered G).reverse
  let data := sourceBoundaryPacket cs N E f
  have hh : (0 : ℝ)<(h : ℝ) := by exact_mod_cast sourceGrid_pos N (sourceInputU cs N E)
  have hsc : Real.sin theta*Real.sin theta=1-Real.cos theta*Real.cos theta := by
    nlinarith [Real.sin_sq_add_cos_sq theta]
  have hround := source_rounded_halves cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted
  have hq : ∀ q∈qs,‖q‖=1 := by
    intro q hmem
    exact source_ideal_discovered_unit cs N E hE htail hparity hd hnorm q (List.mem_reverse.mp hmem)
  have hhalf : List.Forall₂ (fun u q => ‖gaussianRatComplex u‖=1 ∧
      ‖(gaussianRatComplex u)^2-q‖≤7*(h : ℝ)/20+3*r) us qs := by
    have hf := hround.2.2
    change List.Forall₂ (fun u q => ‖gaussianRatComplex u‖=1 ∧
      ‖(gaussianRatComplex u)^2-q‖≤7*(h : ℝ)/20+3/(16*(2 : ℝ)^p)) us qs at hf
    have hr3 : (3 : ℝ)/(16*(2 : ℝ)^p)=3*r := by dsimp [r]; ring
    simpa only [hr3] using hf
  have hB := source_ideal_terminal_base cs N E hE htail hparity hd hnorm
  have he := boundary_error b us (sourceIdealDeflationLoop G false false) qs (Real.cos theta) (Real.sin theta)
    ((h : ℝ)/8+r) (7*(h : ℝ)/20+3*r) hsc (by positivity) (by positivity)
    hround.2.1 hB.2.2 hhalf hq
  have hu : ∀ u∈us,‖gaussianRatComplex u‖=1 := source_unpadded_unit cs N E f
  have hpu : ∀ u∈us++sourcePaddingHalves k,‖gaussianRatComplex u‖=1 := source_padded_unit cs N E f
  have heq : standardMatrixWord (gaussianRatComplex data.base) (Real.cos theta) (Real.sin theta)
        (data.phases.map gaussianRatComplex)=
      standardMatrixWord (gaussianRatComplex (nativeEquatorialBoundaryPacket b us).base)
        (Real.cos theta) (Real.sin theta) ((nativeEquatorialBoundaryPacket b us).phases.map gaussianRatComplex) := by
    change standardMatrixWord (gaussianRatComplex (nativeEquatorialBoundaryPacket b (us++sourcePaddingHalves k)).base)
        (Real.cos theta) (Real.sin theta) ((nativeEquatorialBoundaryPacket b (us++sourcePaddingHalves k)).phases.map gaussianRatComplex)=_
    rw [nativeEquatorialBoundaryPacket_matrix b (us++sourcePaddingHalves k) _ _ hpu,
      nativeEquatorialBoundaryPacket_matrix b us _ _ hu,sourceAppendPadding_product us k _ _ hsc]
  have hfactor := source_ideal_curve_packet cs N E hE htail hparity hd hnorm theta
  change sourceCompletionCircleValue G (theta : AddCircle (2*Real.pi))=
    standardPhaseMatrix (sourceIdealDeflationLoop G false false)*equatorialRotorProduct qs (Real.cos theta) (Real.sin theta) at hfactor
  change ‖standardMatrixWord (gaussianRatComplex data.base) (Real.cos theta) (Real.sin theta)
      (data.phases.map gaussianRatComplex)-sourceCompletionCircleValue G (theta : AddCircle (2*Real.pi))‖≤_
  rw [heq,hfactor]
  have hlen := source_unpadded_length cs N E f
  change us.length=sourceDegree cs N E at hlen
  apply he.trans
  rw [hlen]
  exact source_packet_budget cs N E hE hd

end PacketAccuracy

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
