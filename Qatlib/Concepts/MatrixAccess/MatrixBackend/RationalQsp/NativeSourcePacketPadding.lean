/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceRotorFactorization
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
public import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

@[expose] public section

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

/-- Padding with k pairs gives exactly k repetitions of the ordered Gaussian-rational pair (1, 0),
(0, 1). -/
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

/-- Every rational half phase in the padding list has complex norm one for any number of pairs. -/
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

/-- If s squared equals one minus x squared, the equatorial rotors at coordinates 1 and −1
multiply in that order to the identity. -/
theorem sourceRotor_pair_cancel (x s : ℝ) (hs : s*s=1-x*x) :
    equatorialRotor 1 x s*equatorialRotor (-1) x s=1 := by
  have hstar : equatorialRotor (-1) x s=(equatorialRotor 1 x s).conjTranspose := by
    ext i j
    cases i <;> cases j <;> simp [equatorialRotor,Matrix.conjTranspose_apply]
  rw [hstar]
  simpa only [Matrix.star_eq_conjTranspose] using (sourceRotor_unitary 1 (by norm_num) x s hs).2

/-- When s squared equals one minus x squared, the rotor product of the squared padding
coordinates is the identity for every k. -/
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

/-- Appending padding leaves the rotor product of the squared half phases unchanged at every x and
s with s squared equal to one minus x squared. -/
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
