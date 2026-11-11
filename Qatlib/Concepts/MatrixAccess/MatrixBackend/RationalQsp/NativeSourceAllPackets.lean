/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceConstantPacket
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceZeroDegreePacket
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Actual source zero/constant/N=0 dispatch and the original-input all-branch packet.
Accepted raw roots are required only on the nonconstant path; proposer execution and total fees remain outside this value theorem. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section AllBranches

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Polynomial
open scoped Classical

/-- Construction for source All Boundary Packet in the native source all packets model. -/
def sourceAllBoundaryPacket {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ) (f : Fin m → RootIntegerFactorData) : PhaseData :=
  if N=0 then sourceZeroDegreeBoundaryPacket cs E
  else if ∀ j : Fin (N+1),sourceCoefficient cs N E j=0 then sourceZeroBoundaryPacket N
  else if sourceDegree cs N E=0 then sourceConstantBoundaryPacket cs N E
  else sourceBoundaryPacket cs N E f

/-- Construction for Source Nonconstant Raw Certificate in the native source all packets model. -/
def SourceNonconstantRawCertificate {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (content : ℤ) (f : Fin m → RootIntegerFactorData) : Prop :=
  content≠0 ∧
    rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients (sourceIntegerComplement cs N E) ∧
    ∀ j,RootIntegerFactorGuards (f j) (sourceInputEta cs N E)

/-- The estimate `source_all_boundary_packet_spec` retains the actual parameter, input-error and normalization budgets. -/
theorem source_all_boundary_packet_spec {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ)
    (f : Fin m → RootIntegerFactorData)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0) :
    (sourceAllBoundaryPacket cs N E f).phases.length=N ∧
      ‖gaussianRatComplex (sourceAllBoundaryPacket cs N E f).base‖=1 ∧
      ∀ z∈(sourceAllBoundaryPacket cs N E f).phases,‖gaussianRatComplex z‖=1 := by
  unfold sourceAllBoundaryPacket
  split_ifs with hN hz hd
  · subst N
    exact source_zero_degree_packet_spec cs E
  · exact sourceZeroPacket_spec N
  · exact source_constant_packet_spec cs N E hd hz hparity
  · exact source_boundary_packet_spec cs N E hparity (Nat.pos_of_ne_zero hd) f

/-- The finite construction in `NativeSourceAllPackets` satisfies `source_all_native_uniform` under the displayed hypotheses. -/
theorem source_all_native_uniform {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤ 1)
    (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcert : 0<N → 0<sourceDegree cs N E → SourceNonconstantRawCertificate cs N E content f) :
    let data := nativePacketFromStandard (sourceAllBoundaryPacket cs N E f)
    ∀ x∈Set.Icc (-1 : ℝ) 1,
      |((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (x : ℂ)).re-
        (nativeChebyshevPolynomialFrom 0 cs).eval x|≤ 13*(sourceInputU cs N E : ℝ)/32 := by
  dsimp only
  intro x hx
  have hu : (0 : ℝ)<(sourceInputU cs N E : ℝ) := by exact_mod_cast sourceInputU_pos cs N E hE
  unfold sourceAllBoundaryPacket
  split_ifs with hN hz hd
  · subst N
    exact (source_zero_degree_uniform cs E hE htail hnorm x hx).trans (by linarith)
  · exact (source_zero_native_uniform cs N E hE htail hnorm hz x hx).trans (by linarith)
  · exact (source_constant_native_uniform cs N E hE htail hnorm hd x hx).trans (by linarith)
  · have hdpos : 0<sourceDegree cs N E := Nat.pos_of_ne_zero hd
    obtain ⟨hc,hg,ha⟩ := hcert (Nat.pos_of_ne_zero hN) hdpos
    exact source_native_uniform cs N E hE htail hparity hdpos hnorm m content f hc hg ha x hx

/-- The finite construction in `NativeSourceAllPackets` satisfies `source_all_posterior_accepts` under the displayed hypotheses. -/
theorem source_all_posterior_accepts {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤ 1)
    (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcert : 0<N → 0<sourceDegree cs N E → SourceNonconstantRawCertificate cs N E content f) :
    let data := sourceAllBoundaryPacket cs N E f
    nativeChebyshevPacketCheck cs (sourceResidual cs data) data E=true := by
  have hs := source_all_boundary_packet_spec cs N E f hparity
  exact sourcePacket_accepts_of_original_uniform cs N E hE (sourceAllBoundaryPacket cs N E f) hs.1 hs.2.1 hs.2.2
    (source_all_native_uniform cs N E hE htail hparity hnorm content f hcert)

/-- The estimate `source_all_residual_mass_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem source_all_residual_mass_bound {m : ℕ} (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x|≤ 1)
    (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcert : 0<N → 0<sourceDegree cs N E → SourceNonconstantRawCertificate cs N E content f) :
    let data := sourceAllBoundaryPacket cs N E f
    (nativeChebyshevMass (sourceResidual cs data) : ℝ)≤ 13*(E : ℝ)/32 := by
  let data := sourceAllBoundaryPacket cs N E f
  let delta : ℝ := 13*(sourceInputU cs N E : ℝ)/32
  have hu : (0 : ℝ)<(sourceInputU cs N E : ℝ) := by exact_mod_cast sourceInputU_pos cs N E hE
  have hs := source_all_boundary_packet_spec cs N E f hparity
  have hres : ∀ x∈Set.Icc (-1 : ℝ) 1,
      |(nativeChebyshevPolynomialFrom 0 (sourceResidual cs data)).eval x|≤ delta := by
    intro x hx
    have hi := congrArg (fun q : Polynomial ℝ => q.eval x) (sourceResidual_identity cs data)
    simp only [Polynomial.eval_sub,nativeResponseRealCoefficients_eval] at hi
    rw [←hi]
    exact source_all_native_uniform cs N E hE htail hparity hnorm content f hcert x hx
  have hm := nativeChebyshevMass_of_uniform (sourceResidual cs data) delta hres
  have hl := sourceResidual_length_le cs data
  rw [hs.1] at hl
  have hR : ((sourceResidual cs data).length : ℝ)≤ (max (N+1) cs.length : ℝ) := by exact_mod_cast hl
  exact hm.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hR (by norm_num)) (by positivity)).trans (source_posterior_budget cs N E))

end AllBranches

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
