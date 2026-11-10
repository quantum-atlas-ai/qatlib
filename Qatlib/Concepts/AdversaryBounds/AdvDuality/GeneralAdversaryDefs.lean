/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Instances.Real.Lemmas
import Qatlib.Concepts.Execution.KrausRefinement
import Qatlib.Concepts.InstrumentCore.PovmBridge.MeasurementNetwork
import Qatlib.Concepts.QueryComplexity.DegreeMethod.AlphabetAdversary
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Optimization
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversary
import Qatlib.Concepts.SdpDuality.StrongDuality.PsdConeGeometry
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
open Qatlib.Concepts.GramQueryCore.FilteredCert

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal
open Qatlib

def outcomeEvent {H E : Type} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]
    (label : H → E) (y : E) : Finset H :=
  Finset.filter (fun h => label h = y) Finset.univ

noncomputable def labelPovm {H E : Type} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]
    (label : H → E) : E → Matrix H H ℂ :=
  fun y => Matrix.diagonal fun h => if label h = y then 1 else 0

theorem labelPovm_apply {H E : Type} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]
    (label : H → E) (y : E) (h h' : H) :
    labelPovm label y h h' = if h = h' then (if label h = y then 1 else 0) else 0 := by
  simp [labelPovm, Matrix.diagonal_apply]

theorem labelPovm_posSemidef {H E : Type} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]
    (label : H → E) (y : E) : Matrix.PosSemidef (labelPovm label y) := by
  refine Matrix.PosSemidef.diagonal ?_
  intro h
  by_cases hh : label h = y <;> simp [hh]

private theorem labelPovm_sum_entries {H E : Type} [Fintype H] [DecidableEq H] [Fintype E]
    [DecidableEq E] (label : H → E) (h h' : H) :
    (∑ y, labelPovm label y) h h' = if h = h' then 1 else 0 := by
  have h1 : (∑ y, labelPovm label y) = fun a => ∑ y, (labelPovm label y) a :=
    Finset.sum_fn Finset.univ (fun y => labelPovm label y)
  have h2 : (∑ y, (labelPovm label y) h) = fun a => ∑ y, (labelPovm label y) h a :=
    Finset.sum_fn Finset.univ (fun y => (labelPovm label y) h)
  rw [h1]
  (try dsimp only)
  rw [h2]
  (try dsimp only)
  by_cases hh : h = h'
  · subst hh
    simp only [labelPovm, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single (label h)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · simp [labelPovm, hh]

theorem labelPovm_sum_one {H E : Type} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]
    (label : H → E) : (∑ y, labelPovm label y) = (1 : Matrix H H ℂ) := by
  ext h h'
  rw [labelPovm_sum_entries label h h']
  simp [Matrix.one_apply]

theorem isPovm_labelPovm {H E : Type} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]
    (label : H → E) : IsPovm (labelPovm label) := by
  refine ⟨fun y => labelPovm_posSemidef label y, ?_⟩
  ext h h'
  rw [labelPovm_sum_entries label h h']
  simp [Matrix.one_apply]

theorem labelPovm_mulVec {H E : Type} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]
    (label : H → E) (y : E) (psi : QState H) (h : H) :
    (labelPovm label y *ᵥ psi) h = if label h = y then psi h else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single h]
  · by_cases hh : label h = y <;> simp [labelPovm, hh]
  · intro j _ hj
    simp [labelPovm, Ne.symm hj]
  · simp

theorem labelPovm_povmProb {H E : Type} [Fintype H] [DecidableEq H] [Fintype E] [DecidableEq E]
    (label : H → E) (y : E) (psi : QState H) :
    povmProb (labelPovm label) y psi = MeasureProb psi (outcomeEvent label y) := by
  classical
  unfold povmProb
  rw [inner_apply]
  have hmul : ∀ h, (labelPovm label y *ᵥ psi) h = if label h = y then psi h else 0 :=
    fun h => labelPovm_mulVec label y psi h
  have hmul' : ∀ h, (starRingEnd ℂ) (psi h) * (labelPovm label y *ᵥ psi) h =
      (starRingEnd ℂ) (psi h) * (if label h = y then psi h else 0) := by
    intro h
    rw [hmul h]
  rw [Finset.sum_congr rfl fun h _ => hmul' h]
  have hsplit : (∑ h, (starRingEnd ℂ) (psi h) * (if label h = y then psi h else 0)) =
      ∑ h ∈ Finset.univ.filter (fun h => label h = y), (starRingEnd ℂ) (psi h) * psi h := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : label h = y <;> simp [hh]
  rw [hsplit]
  have hinner : ∀ h : H, (starRingEnd ℂ) (psi h) * psi h = ((‖psi h‖ ^ 2 : ℝ) : ℂ) := by
    intro h
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hre : (∑ h ∈ Finset.univ.filter (fun h => label h = y), (starRingEnd ℂ) (psi h) * psi h) =
      ((∑ h ∈ Finset.univ.filter (fun h => label h = y), ‖psi h‖ ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl fun h _ => hinner h]
    exact (Complex.ofReal_sum (Finset.univ.filter (fun h => label h = y))
      (fun h => ‖psi h‖ ^ 2)).symm
  rw [hre, Complex.ofReal_re]
  rfl

theorem genAdvFilter_eq_filterDelta {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (input : X → Fin n → Bool) (Gamma : Matrix X X ℂ) (i : Fin n) :
    genAdvFilter input Gamma i = gramFilterDelta input i ⊙ Gamma := by
  ext x y
  by_cases h : input x i = input y i <;>
    simp [genAdvFilter, gramFilterDelta, Matrix.hadamard_apply, h]

section PovmDilation
open scoped MatrixOrder

theorem sqrt_gram {H : Type} [Fintype H] [DecidableEq H] (A : Matrix H H ℂ) (hA : A.PosSemidef) :
    (CFC.sqrt A)ᴴ * CFC.sqrt A = A := by
  rw [← Matrix.star_eq_conjTranspose, (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

noncomputable def povmLiftMatrix {H Y : Type} [Fintype H] [DecidableEq H]
    (out : Y → Matrix H H ℂ) : Matrix (Y × H) H ℂ := fun yh h => CFC.sqrt (out yh.1) yh.2 h

theorem povmLift_gram {H Y : Type} [Fintype H] [DecidableEq H] [Fintype Y]
    (out : Y → Matrix H H ℂ) (hout : IsPovm out) :
    (povmLiftMatrix out)ᴴ * povmLiftMatrix out = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, povmLiftMatrix]
  have hterm (y : Y) : (∑ h, star (CFC.sqrt (out y) h i) * CFC.sqrt (out y) h j) = out y i j :=
    congrArg (fun M : Matrix H H ℂ => M i j) (sqrt_gram (out y) (hout.1 y))
  simp_rw [hterm]
  rw [← Matrix.sum_apply, hout.2]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem lift_inner_rect {H K : Type} [Fintype H] [Fintype K]
    (V : Matrix K H ℂ) (u : QState H) (v : QState K) :
    Qatlib.Foundations.PureStateMath.Inner (V *ᵥ u) v = Qatlib.Foundations.PureStateMath.Inner u (Vᴴ *ᵥ v) := by
  simp only [Qatlib.Foundations.PureStateMath.Inner]
  rw [Matrix.star_mulVec, dotProduct_mulVec]

theorem povmLift_inner {H Y : Type} [Fintype H] [DecidableEq H] [Fintype Y]
    (out : Y → Matrix H H ℂ) (hout : IsPovm out) (u v : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (povmLiftMatrix out *ᵥ u) (povmLiftMatrix out *ᵥ v) = Qatlib.Foundations.PureStateMath.Inner u v := by
  rw [lift_inner_rect, Matrix.mulVec_mulVec, povmLift_gram out hout, Matrix.one_mulVec]

theorem povmLift_normalized {H Y : Type} [Fintype H] [DecidableEq H] [Fintype Y]
    (out : Y → Matrix H H ℂ) (hout : IsPovm out) (v : QState H) (hv : Normalized v) :
    Normalized (povmLiftMatrix out *ᵥ v) := by
  classical
  rw [normalized_iff_inner_self, povmLift_inner out hout]
  exact (normalized_iff_inner_self v).mp hv

theorem povmLift_born {H Y : Type} [Fintype H] [DecidableEq H] [Fintype Y] [DecidableEq Y]
    (out : Y → Matrix H H ℂ) (hout : IsPovm out) (v : QState H) (y : Y) :
    MeasureProb (povmLiftMatrix out *ᵥ v) (outcomeEvent Prod.fst y) = povmProb out y v := by
  have hbranch : MeasureProb (povmLiftMatrix out *ᵥ v) (outcomeEvent Prod.fst y) =
      ∑ h, ‖(CFC.sqrt (out y) *ᵥ v) h‖ ^ 2 := by
    simp only [MeasureProb, BornProb, outcomeEvent, Finset.sum_filter,
      Fintype.sum_prod_type, povmLiftMatrix, Matrix.mulVec, dotProduct]
    simp
  rw [hbranch]
  have hsqr : ∑ h, ‖(CFC.sqrt (out y) *ᵥ v) h‖ ^ 2 =
      (Qatlib.Foundations.PureStateMath.Inner (CFC.sqrt (out y) *ᵥ v) (CFC.sqrt (out y) *ᵥ v)).re := by
    simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Complex.re_sum,
        Pi.star_apply, RCLike.star_def]
    apply Finset.sum_congr rfl
    intro h _
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [hsqr, lift_inner_rect, Matrix.mulVec_mulVec, sqrt_gram _ (hout.1 y)]
  rfl

end PovmDilation

noncomputable def instrumentReadout {Y : Type} [Fintype Y] {D E : ℕ}
    (I : Instrument Y D E) (y : Y) : Operator D :=
  ∑ k : Fin E × Fin D, ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (y,k))ᴴ * (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (y,k)

theorem instrumentReadout_isPovm {Y : Type} [Fintype Y] {D E : ℕ}
    (I : Instrument Y D E) : IsPovm (instrumentReadout I) := by
  constructor
  · intro y
    exact Matrix.posSemidef_sum _ (fun k _ => Matrix.posSemidef_conjTranspose_mul_self _)
  · ext i j
    have h :=
        congrArg (fun M : Operator D => M i j)
        (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily_complete I)
    by_cases he : i = j <;>
      simpa only [instrumentReadout, Matrix.sum_apply, Fintype.sum_prod_type,
        Matrix.one_apply, he, ite_true, ite_false] using! h

theorem instrumentReadout_prob {Y : Type} [Fintype Y] {D E : ℕ}
    (I : Instrument Y D E) (y : Y) (psi : QState (Fin D)) :
    povmProb (instrumentReadout I) y psi = (Matrix.trace (I.branch y (outerProduct psi))).re := by
  have h : Qatlib.Foundations.PureStateMath.Inner psi (instrumentReadout I y *ᵥ psi) =
      Matrix.trace (I.branch y (outerProduct psi)) := by
    rw [← Qatlib.Concepts.InstrumentCore.PovmBridge.trace_mul_outerProduct, (Qatlib.Concepts.Execution.KrausRefinement.Instrument.branch_apply_eq_kraus I),
      Matrix.trace_sum, instrumentReadout, Finset.sum_mul, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact (Matrix.trace_mul_cycle ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (y,k)) (outerProduct psi) ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (y,k))ᴴ).symm
  exact congrArg Complex.re h

abbrev FourBitWord := Fin 4 → Bool

def fourBitCode (w : FourBitWord) : ℕ := ∑ i : Fin 4, if w i then 2 ^ (3-i.val) else 0

private def fourBitIntegerTable : List (List ℤ) := [
  [0, 0, 578143, 0, 578143, 183237, 707052, 0, 0, 707052, 183237, -211669, 0, -211669, 0, 0],
  [0, 0, 707052, 0, 183237, 578143, -211669, 0, 0, 578143, -211669, 183237, 0, 707052, 0, 0],
  [578143, 707052, 0, 578143, 0, 0, 0, 183237, 183237, 0, 0, 0, -211669, 0, 707052, -211669],
  [0, 0, 578143, 0, -211669, 707052, 183237, 0, 0, 183237, 707052, 578143, 0, -211669, 0, 0],
  [578143, 183237, 0, -211669, 0, 0, 0, 707052, 707052, 0, 0, 0, 578143, 0, 183237, -211669],
  [183237, 578143, 0, 707052, 0, 0, 0, 578143, -211669, 0, 0, 0, 707052, 0, -211669, 183237],
  [707052, -211669, 0, 183237, 0, 0, 0, 578143, -211669, 0, 0, 0, 183237, 0, 578143, 707052],
  [0, 0, 183237, 0, 707052, 578143, 578143, 0, 0, -211669, -211669, 707052, 0, 183237, 0, 0],
  [0, 0, 183237, 0, 707052, -211669, -211669, 0, 0, 578143, 578143, 707052, 0, 183237, 0, 0],
  [707052, 578143, 0, 183237, 0, 0, 0, -211669, 578143, 0, 0, 0, 183237, 0, -211669, 707052],
  [183237, -211669, 0, 707052, 0, 0, 0, -211669, 578143, 0, 0, 0, 707052, 0, 578143, 183237],
  [-211669, 183237, 0, 578143, 0, 0, 0, 707052, 707052, 0, 0, 0, -211669, 0, 183237, 578143],
  [0, 0, -211669, 0, 578143, 707052, 183237, 0, 0, 183237, 707052, -211669, 0, 578143, 0, 0],
  [-211669, 707052, 0, -211669, 0, 0, 0, 183237, 183237, 0, 0, 0, 578143, 0, 707052, 578143],
  [0, 0, 707052, 0, 183237, -211669, 578143, 0, 0, -211669, 578143, 183237, 0, 707052, 0, 0],
  [0, 0, -211669, 0, -211669, 183237, 707052, 0, 0, 707052, 183237, 578143, 0, 578143, 0, 0]]

def fourBitInteger : Matrix FourBitWord FourBitWord ℤ := fun x y =>
  ((fourBitIntegerTable.getD (fourBitCode x) []).getD (fourBitCode y) 0)
def fourBitQ : Matrix FourBitWord FourBitWord ℚ := fun x y => (fourBitInteger x y : ℚ) / 1000005
noncomputable def fourBitGamma : Matrix FourBitWord FourBitWord ℂ := fun x y => (fourBitQ x y : ℂ)

abbrev PhasePaddingSpace (n q : ℕ) (W H : Type) := (Fin n × Fin q) × (W × H × Fin q)

def phasePaddingSwap {n q : ℕ} {W H : Type} (active : H → Bool)
    (r : PhasePaddingSpace n q W H) : PhasePaddingSpace n q W H :=
  if active r.2.2.1 then r else ((r.1.1,r.2.2.2),r.2.1,r.2.2.1,r.1.2)

theorem phasePaddingSwap_involutive {n q : ℕ} {W H : Type} (active : H → Bool) :
    Function.Involutive (phasePaddingSwap (n := n) (q := q) (W := W) active) := by
  rintro ⟨⟨i,p⟩,w,h,z⟩
  cases ha : active h <;> simp [phasePaddingSwap, ha]

noncomputable def phasePaddingWord {n q : ℕ} {W H : Type}
    [Fintype W] [DecidableEq W] [Fintype H] [DecidableEq H] (active : H → Bool) :
    Circuit (PhasePaddingSpace n q W H) :=
  [.gate (permMatrix (phasePaddingSwap active)), .query, .gate (permMatrix (phasePaddingSwap active))]

noncomputable def phasePaddingInput {n q : ℕ} [NeZero q] {W H : Type}
    (v : QState ((Fin n × Fin q) × (W × H))) : QState (PhasePaddingSpace n q W H) :=
  fun r => if r.2.2.2 = 0 then v (r.1,r.2.1,r.2.2.1) else 0

open Qatlib

def spectralDomainEmbedding {X Y : Type} [DecidableEq Y] (e : X → Y) : Matrix Y X ℂ :=
    fun y x => if e x=y then 1 else 0

def iteratedWordSplit (n d : ℕ) : (Fin (n^(d+1)) → Bool) ≃ (Fin n → (Fin (n^d) → Bool)) where
  toFun := fun w i j => w ((powIndexSplit n d).symm (j,i))
  invFun := fun bs c => bs ((powIndexSplit n d) c).2 ((powIndexSplit n d) c).1
  left_inv := by intro w; funext c; simp
  right_inv := by intro bs; funext i j; simp

def booleanQueryGamma : Matrix Bool Bool ℂ := fun x y => if x ≠ y then 1 else 0

def zeroDepthWordEquiv (n : ℕ) : (Fin (n^0) → Bool) ≃ Bool := Equiv.funUnique (Fin 1) Bool

def zeroDepthGamma (n : ℕ) : Matrix (Fin (n^0) → Bool) (Fin (n^0) → Bool) ℂ :=
  booleanQueryGamma.submatrix (zeroDepthWordEquiv n) (zeroDepthWordEquiv n)

def iteratedAdversaryStep {n : ℕ} (f : (Fin n → Bool) → Bool)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (d : ℕ)
    (B : Matrix (Fin (n^d) → Bool) (Fin (n^d) → Bool) ℂ) :
    Matrix (Fin (n^(d+1)) → Bool) (Fin (n^(d+1)) → Bool) ℂ :=
  ((‖B‖^(n-1))⁻¹ : ℝ) •
    (weightedAdvGamma (fun (_ : Fin n) => iterateTotal f d) f A (fun _ => B)).submatrix
      (iteratedWordSplit n d) (iteratedWordSplit n d)

def iteratedAdversaryGamma {n : ℕ} (f : (Fin n → Bool) → Bool)
    (A : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    (d : ℕ) → Matrix (Fin (n^d) → Bool) (Fin (n^d) → Bool) ℂ
  | 0 => zeroDepthGamma n
  | d+1 => iteratedAdversaryStep f A d (iteratedAdversaryGamma f A d)

def normalizeWordAdversary {n : ℕ} (G : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  ((maxFilterNorm (fun w : Fin n → Bool => w) G)⁻¹ : ℝ) • G

def flatBooleanCompose {n m l : ℕ} (e : Fin l ≃ Fin m × Fin n)
    (f : (Fin n → Bool) → Bool) (g : (Fin m → Bool) → Bool) (w : Fin l → Bool) : Bool :=
  f (fun i => g (fun j => w (e.symm (j,i))))

def flatCertificateBlock {n m l : ℕ} (e : Fin l ≃ Fin m × Fin n)
    (T : Finset (Fin l)) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => e.symm (j,i) ∈ T)

def flatCertificateUnion {n m l : ℕ} (e : Fin l ≃ Fin m × Fin n)
    (S : Finset (Fin n)) (T : Fin n → Finset (Fin m)) : Finset (Fin l) :=
  S.biUnion (fun i => (T i).image (fun j => e.symm (j,i)))

def forcedOuterCertificate {n m l : ℕ} (e : Fin l ≃ Fin m × Fin n)
    (g : (Fin m → Bool) → Bool) (w : Fin l → Bool) (T : Finset (Fin l)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => IsCertificate g (fun j => w (e.symm (j,i))) (flatCertificateBlock e T i))

end Qatlib.Concepts.AdversaryBounds.AdvDuality
