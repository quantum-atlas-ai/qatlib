/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceRotorFactorization
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Original-input, accepted-certificate nonconstant source packet: PacketPadding.
Value and physical-word guarantees here do not certify a root proposer, Python interpreter or total costs. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section PacketPadding

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- Construction for source Padding Halves in the native source packet padding model. -/
def sourcePaddingHalves : ℕ → List GaussianRat
  | 0 => []
  | k+1 => (1,0)::(0,1)::sourcePaddingHalves k

/-- The finite construction in `NativeSourcePacketPadding` satisfies `sourcePaddingHalves_eq_repeat` under the displayed hypotheses. -/
theorem sourcePaddingHalves_eq_repeat (k : ℕ) :
    sourcePaddingHalves k=(List.replicate k ([(1,0),(0,1)] : List GaussianRat)).flatten := by
  induction k with
  | zero => rfl
  | succ k ih => simp [sourcePaddingHalves,List.replicate_succ,ih]

/-- The same emitted instruction list satisfies `sourcePaddingHalves_length` with the displayed gate and query accounting. -/
theorem sourcePaddingHalves_length (k : ℕ) : (sourcePaddingHalves k).length=2*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [sourcePaddingHalves,List.length_cons,ih]; omega

/-- The finite construction in `NativeSourcePacketPadding` satisfies `sourcePaddingHalves_norm` under the displayed hypotheses. -/
theorem sourcePaddingHalves_norm (k : ℕ) : ∀ u∈sourcePaddingHalves k,‖gaussianRatComplex u‖=1 := by
  induction k with
  | zero => simp [sourcePaddingHalves]
  | succ k ih =>
    intro u hu
    rcases List.mem_cons.mp hu with hu|hu
    · subst u; norm_num [gaussianRatComplex]
    rcases List.mem_cons.mp hu with hu|hu
    · subst u; norm_num [gaussianRatComplex]
    · exact ih u hu

/-- The finite construction in `NativeSourcePacketPadding` satisfies `sourceRotor_pair_cancel` under the displayed hypotheses. -/
theorem sourceRotor_pair_cancel (x s : ℝ) (hs : s*s=1-x*x) :
    equatorialRotor 1 x s*equatorialRotor (-1) x s=1 := by
  have hstar : equatorialRotor (-1) x s=(equatorialRotor 1 x s).conjTranspose := by
    ext i j
    cases i <;> cases j <;> simp [equatorialRotor,Matrix.conjTranspose_apply]
  rw [hstar]
  simpa only [Matrix.star_eq_conjTranspose] using (sourceRotor_unitary 1 (by norm_num) x s hs).2

/-- The finite construction in `NativeSourcePacketPadding` satisfies `sourcePaddingHalves_product` under the displayed hypotheses. -/
theorem sourcePaddingHalves_product (k : ℕ) (x s : ℝ) (hs : s*s=1-x*x) :
    equatorialRotorProduct ((sourcePaddingHalves k).map (fun u => (gaussianRatComplex u)^2)) x s=1 := by
  induction k with
  | zero => simp [sourcePaddingHalves,equatorialRotorProduct]
  | succ k ih =>
    change equatorialRotor ((gaussianRatComplex ((1,0) : GaussianRat))^2) x s*
      (equatorialRotor ((gaussianRatComplex ((0,1) : GaussianRat))^2) x s*
        equatorialRotorProduct ((sourcePaddingHalves k).map (fun u => (gaussianRatComplex u)^2)) x s)=1
    rw [ih,mul_one]
    norm_num [gaussianRatComplex]
    exact sourceRotor_pair_cancel x s hs

/-- The finite construction in `NativeSourcePacketPadding` satisfies `sourceAppendPadding_product` under the displayed hypotheses. -/
theorem sourceAppendPadding_product (us : List GaussianRat) (k : ℕ) (x s : ℝ) (hs : s*s=1-x*x) :
    equatorialRotorProduct ((us++sourcePaddingHalves k).map (fun u => (gaussianRatComplex u)^2)) x s=
      equatorialRotorProduct (us.map (fun u => (gaussianRatComplex u)^2)) x s := by
  simp only [List.map_append,equatorialRotorProduct,List.prod_append]
  rw [show ((List.map (fun q => equatorialRotor q x s)
      (List.map (fun u => gaussianRatComplex u ^ 2) (sourcePaddingHalves k))).prod)=1 from sourcePaddingHalves_product k x s hs,mul_one]

/-- The same emitted instruction list satisfies `source_padding_length` with the displayed gate and query accounting. -/
theorem source_padding_length (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) (us : List GaussianRat)
    (hlen : us.length=sourceDegree cs N E) :
    (us++sourcePaddingHalves ((N-sourceDegree cs N E)/2)).length=N := by
  rw [List.length_append,sourcePaddingHalves_length,hlen]
  have hle := sourceDegree_le cs N E
  have hmod := sourceDegree_parity cs N E hparity hd
  omega

end PacketPadding

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
