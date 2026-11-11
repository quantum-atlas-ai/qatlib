/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PaidFiniteOutput
import Qatlib.Concepts.SpinorSampling.NativeRecords.LittleEndianEncoding
import Qatlib.Concepts.SpinorSampling.Retained.PrefixSupply
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PaidExecutionTrace

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Complete supplied-prefix address instrument on fixed storage wires

The original dyadic little-endian supplied prefix is tensored with the
retained spin on a fixed suffix wire. Actual complete address projectors
produce the exact full-register native-capture fibres and retain all
non-renormalized branch masses, including the original 1/M factors.
-/

set_option autoImplicit false
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge

/-- Executable original low-endian address bits with all three actual spin/storage baseline wires zero. -/
def factoryAddressBits (d r : ℕ) (x : PairGrid d r) : Reg (d*r+3) :=
  Fin.snoc (Fin.snoc (Fin.snoc (positionBits d r x) false) false) false

/-- The controller computes the original double-shift match from only its finite measured addresses. -/
def factoryAddressMatch (d r : ℕ) (j : Fin d) (x y : PairGrid d r) : Bool :=
  decide (y=observedDoubleShift d r j x)

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib
open Qatlib.Concepts.SpinorSampling.Retained.PrefixSupply
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.SpinorSampling.Model

/-- The first dr+1 wires are the original supplied prefix; the two fixed suffix slots are untouched storage. -/
def freshFactoryLayout (d r : ℕ) :
    Reg (d*r+3) ≃ (((PairGrid d r × Bool) × Bool) × Bool) :=
  (regSuccEquiv (d*r+2)).trans
    ((Equiv.prodCongr (regSuccEquiv (d*r+1)) (Equiv.refl Bool)).trans
      (Equiv.prodCongr (Equiv.prodCongr (spinLayoutEquiv d r) (Equiv.refl Bool)) (Equiv.refl Bool)))

/-- The ordinary fresh prefix is tensored with the original retained spin and one clean unused slot. -/
def freshPhysicalPrefix (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ) (u : Bool → ℂ) :
    QState (Reg (d*r+3)) := fun q =>
  let p := freshFactoryLayout d r q
  suppliedSpinAt ψ p.1.1.1 p.1.1.2 * u p.1.2 * Ket false p.2

/-- The source tensor has exactly the retained input mass, with one ordinary normalized supplied copy. -/
theorem freshPhysicalPrefix_mass (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x,qubitMass (ψ x)=1) (u : Bool → ℂ) :
    (∑ q : Reg (d*r+3), BornProb (freshPhysicalPrefix d r ψ u) q)=qubitMass u := by
  let f : (((PairGrid d r × Bool) × Bool) × Bool) → ℝ := fun p =>
    ‖suppliedSpinAt ψ p.1.1.1 p.1.1.2 * u p.1.2 * Ket false p.2‖^2
  change (∑ q, f (freshFactoryLayout d r q))=qubitMass u
  rw [Equiv.sum_comp (freshFactoryLayout d r) f]
  have hs := supplied_spin_state_normalized (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
    (pairFieldCoordinates d r ψ hψ)
  have hm : (∑ x : PairGrid d r, ∑ s : Bool, ‖suppliedSpinAt ψ x s‖^2)=1 := by
    simpa only [Normalized,Fintype.sum_prod_type,suppliedSpinAt,BornProb] using hs
  simp only [Fintype.sum_prod_type]
  have he (x : PairGrid d r) :
      (∑ spin : Bool, ∑ stored : Bool, ∑ clean : Bool, f (((x,spin),stored),clean)) =
        (∑ spin : Bool, ‖suppliedSpinAt ψ x spin‖^2)*qubitMass u := by
    simp [f,
      Qatlib.Foundations.PureStateMath.Ket,qubitMass,Complex.sq_norm]
    ring
  simp_rw [he]
  rw [← Finset.sum_mul,hm,one_mul]

/-- The live input spin is the final wire of the original dr+1 preparation prefix. -/
def factoryLive (d r : ℕ) : Fin (d*r+3) := ⟨d*r,by omega⟩
/-- The retained spin stays at the first fixed suffix storage wire. -/
def factoryFirst (d r : ℕ) : Fin (d*r+3) := ⟨d*r+1,by omega⟩
/-- The second capture uses the other fixed suffix storage wire. -/
def factorySecond (d r : ℕ) : Fin (d*r+3) := ⟨d*r+2,by omega⟩

/-- Decoding the executable controller bits gives the exact original source layout and clean suffix wires. -/
theorem factoryAddressBits_layout (d r : ℕ) (x : PairGrid d r) :
    freshFactoryLayout d r (factoryAddressBits d r x)=(((x,false),false),false) := by
  have hc {n : ℕ} (i : Fin n) : Fin.castAdd 1 i=i.castSucc := Fin.ext rfl
  have hz (n : ℕ) : Fin.natAdd n (0 : Fin 1)=Fin.last n := Fin.ext rfl
  simp [freshFactoryLayout,spinLayoutEquiv,regSuccEquiv,Fin.succFunEquiv,
    factoryAddressBits,hc,hz,positionEquiv_positionBits]

/-- The executable encoder agrees with the prior semantic inverse without evaluating a choice-based inverse. -/
theorem factoryAddressBits_eq_inverse (d r : ℕ) (x : PairGrid d r) :
    factoryAddressBits d r x=(freshFactoryLayout d r).symm (((x,false),false),false) := by
  apply (freshFactoryLayout d r).injective
  rw [factoryAddressBits_layout,Equiv.apply_symm_apply]

/-- The actual finite classical match decision equals the original periodic double shift. -/
theorem factoryAddressMatch_eq (d r : ℕ) (j : Fin d) (x y : PairGrid d r) :
    factoryAddressMatch d r j x y=decide (y=pairDoubleShift d r j x) := by
  simp only [factoryAddressMatch,observedDoubleShift_eq]

/-- Embedding the three spin bits changes none of the actual source address bits. -/
theorem freshFactoryLayout_embed (d r : ℕ) (z : Reg (d*r+3))
    (t : Reg 3) :
    freshFactoryLayout d r
      (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tofEmb
        (factoryLive d r) (factoryFirst d r) (factorySecond d r) t z) =
      ((((freshFactoryLayout d r z).1.1.1,t 0),t 1),t 2) := by
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · change positionEquiv d r
          (Fin.init (Fin.init (Fin.init
            (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tofEmb
              (factoryLive d r) (factoryFirst d r) (factorySecond d r) t z)))) =
          positionEquiv d r (Fin.init (Fin.init (Fin.init z)))
        congr 1
        funext i
        have ha : i.castSucc.castSucc.castSucc≠factoryLive d r := by
          intro h
          have e := congrArg Fin.val h
          have hi := i.isLt
          simp only [Fin.val_castSucc,factoryLive] at e
          omega
        have hb : i.castSucc.castSucc.castSucc≠factoryFirst d r := by
          intro h
          have e := congrArg Fin.val h
          have hi := i.isLt
          simp only [Fin.val_castSucc,factoryFirst] at e
          omega
        have hc : i.castSucc.castSucc.castSucc≠factorySecond d r := by
          intro h
          have e := congrArg Fin.val h
          have hi := i.isLt
          simp only [Fin.val_castSucc,factorySecond] at e
          omega
        simp only [Fin.init,Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tofEmb,
          ite_eq_right ha,ite_eq_right hb,ite_eq_right hc]
      · change Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tofEmb
          (factoryLive d r) (factoryFirst d r) (factorySecond d r) t z (factoryLive d r)=t 0
        simp [Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tofEmb]
    · change Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tofEmb
        (factoryLive d r) (factoryFirst d r) (factorySecond d r) t z (factoryFirst d r)=t 1
      simp [Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tofEmb,
        factoryLive,factoryFirst,Fin.ext_iff]
  · change Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tofEmb
      (factoryLive d r) (factoryFirst d r) (factorySecond d r) t z (factorySecond d r)=t 2
    simp [Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tofEmb,
      factoryLive,factoryFirst,factorySecond,Fin.ext_iff]

/-- Every actual canonical address branch has the original supplied spin amplitude and unchanged retained amplitudes. -/
theorem freshPhysicalPrefix_branch_amplitude (d r : ℕ)
    (ψ : PairGrid d r → Bool → ℂ) (u : Bool → ℂ) (x : PairGrid d r) (t : Reg 3) :
    freshPhysicalPrefix d r ψ u
      (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tofEmb
        (factoryLive d r) (factoryFirst d r) (factorySecond d r) t
        (factoryAddressBits d r x)) = suppliedSpinAt ψ x (t 0)*u (t 1)*Ket false (t 2) := by
  unfold freshPhysicalPrefix
  rw [freshFactoryLayout_embed]
  simp only [factoryAddressBits_eq_inverse,Equiv.apply_symm_apply]

open Qatlib.Concepts.SpinorSampling.Retained.NativeCapture
open Qatlib.Concepts.SpinorSampling.Retained.PhysicalCapture

/-- The physical prefix address is measured without observing either stored spin. -/
def measuredFreshPrefixState (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (u : Bool → ℂ) (x : PairGrid d r) : QState (Reg (d*r+3)) := fun q =>
  if (freshFactoryLayout d r q).1.1.1=x then freshPhysicalPrefix d r ψ u q else 0

/-- The address-measurement branch is literally the full-register three-wire fibre with the original supplied amplitudes. -/
theorem measuredFreshPrefixState_fibre (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (u : Bool → ℂ) (x : PairGrid d r) :
    measuredFreshPrefixState d r ψ u x =
      physicalTripleState (factoryLive d r) (factoryFirst d r) (factorySecond d r)
        (factoryAddressBits d r x) (captureTriple (suppliedSpinAt ψ x) u (Ket false)) := by
  have hab : factoryLive d r≠factoryFirst d r := by
    simp [factoryLive,factoryFirst,Fin.ext_iff]
  have hac : factoryLive d r≠factorySecond d r := by
    simp [factoryLive,factorySecond,Fin.ext_iff]
  have hbc : factoryFirst d r≠factorySecond d r := by
    simp [factoryFirst,factorySecond,Fin.ext_iff]
  funext q
  unfold measuredFreshPrefixState
  by_cases h : (freshFactoryLayout d r q).1.1.1=x
  · let t := captureReg (freshFactoryLayout d r q).1.1.2
      (freshFactoryLayout d r q).1.2 (freshFactoryLayout d r q).2
    have rebuilt : (tofEmb (factoryLive d r) (factoryFirst d r) (factorySecond d r) t (factoryAddressBits d r x) = q) := by
      apply (freshFactoryLayout d r).injective
      rw [freshFactoryLayout_embed]
      simp only [factoryAddressBits_eq_inverse,Equiv.apply_symm_apply,t,
        captureReg_live,captureReg_first,captureReg_second]
      rw [← h]
    rw [ite_eq_left h,← rebuilt,freshPhysicalPrefix_branch_amplitude,
      physicalTripleState_amplitude _ _ _ hab hac hbc]
    rfl
  · rw [ite_eq_right h]
    symm
    have hk (t : Reg 3) :
        Ket (tofEmb (factoryLive d r) (factoryFirst d r) (factorySecond d r) t
          (factoryAddressBits d r x)) q=(0 : ℂ) := by
      have hn : q≠tofEmb (factoryLive d r) (factoryFirst d r) (factorySecond d r) t
          (factoryAddressBits d r x) := by
        intro e
        have hx := congrArg (fun z => (freshFactoryLayout d r z).1.1.1) e
        rw [freshFactoryLayout_embed] at hx
        simp only [factoryAddressBits_eq_inverse,Equiv.apply_symm_apply] at hx
        exact h hx
      simp [Qatlib.Foundations.PureStateMath.Ket,hn]
    simp only [physicalTripleState,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hk,
      mul_zero,Finset.sum_const_zero]

/-- The exact address branches partition the original supplied-prefix state; none is rejected or renormalized for free. -/
theorem measuredFreshPrefixState_complete (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (u : Bool → ℂ) : (∑ x,measuredFreshPrefixState d r ψ u x)=freshPhysicalPrefix d r ψ u := by
  funext q
  simp [measuredFreshPrefixState]

/-- The literal source normalization at each address pays its 1/M branch mass. -/
theorem suppliedSpinAt_mass {S : Type*} [Fintype S] (ψ : S → Bool → ℂ)
    (hψ : ∀ x,qubitMass (ψ x)=1) (x : S) :
    qubitMass (suppliedSpinAt ψ x)=1/(Fintype.card S : ℝ) := by
  have hs (b : Bool) : suppliedSpinAt ψ x b=ψ x b/(Real.sqrt (Fintype.card S : ℝ) : ℂ) := by
    simp [suppliedSpinAt,suppliedSpinState,complexSpinor_parts]
  have hd : Complex.normSq (Real.sqrt (Fintype.card S : ℝ) : ℂ)=(Fintype.card S : ℝ) := by
    rw [Complex.normSq_ofReal,Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp only [qubitMass,hs,Complex.normSq_div,hd,← add_div]
  change qubitMass (ψ x)/(Fintype.card S : ℝ)=_
  rw [hψ x]

/-- The actual source address measurement retains the unknown memory mass and has the exact paid 1/M address factor. -/
theorem measuredFreshPrefixState_mass (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x,qubitMass (ψ x)=1) (u : Bool → ℂ) (x : PairGrid d r) :
    (∑ q : Reg (d*r+3), BornProb (measuredFreshPrefixState d r ψ u x) q)=
      (1/(Fintype.card (PairGrid d r) : ℝ))*qubitMass u := by
  let f : (((PairGrid d r × Bool) × Bool) × Bool) → ℝ := fun p =>
    if p.1.1.1=x then ‖suppliedSpinAt ψ p.1.1.1 p.1.1.2*u p.1.2*Ket false p.2‖^2 else 0
  have hq (q : Reg (d*r+3)) : BornProb (measuredFreshPrefixState d r ψ u x) q=
      f (freshFactoryLayout d r q) := by
    simp only [BornProb,measuredFreshPrefixState,freshPhysicalPrefix,f]
    split_ifs <;> simp
  simp_rw [hq]
  rw [Equiv.sum_comp (freshFactoryLayout d r) f]
  simp only [Fintype.sum_prod_type]
  have he (y : PairGrid d r) :
      (∑ spin : Bool, ∑ stored : Bool, ∑ clean : Bool, f (((y,spin),stored),clean)) =
        if y=x then qubitMass (suppliedSpinAt ψ y)*qubitMass u else 0 := by
    by_cases hy : y=x
    · subst y
      simp [f,Qatlib.Foundations.PureStateMath.Ket,qubitMass,Complex.sq_norm]
      ring
    · simp [f,hy]
  simp_rw [he]
  simp [suppliedSpinAt_mass ψ hψ]

/-- This is the actual diagonal address-measurement operator on the original complete physical register. -/
def factoryAddressProjector (d r : ℕ) (x : PairGrid d r) :
    Matrix (Reg (d*r+3)) (Reg (d*r+3)) ℂ :=
  Matrix.diagonal (fun q => if (freshFactoryLayout d r q).1.1.1=x then 1 else 0)

/-- The projector acts exactly as the non-renormalized measured source branch. -/
theorem factoryAddressProjector_apply (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (u : Bool → ℂ) (x : PairGrid d r) :
    ApplyGate (factoryAddressProjector d r x) (freshPhysicalPrefix d r ψ u)=
      measuredFreshPrefixState d r ψ u x := by
  funext q
  simp [ApplyGate,Matrix.mulVec,dotProduct,Matrix.diagonal_apply,factoryAddressProjector,measuredFreshPrefixState]

/-- All address measurement effects sum to the identity on every full-register state. -/
theorem factoryAddressProjector_complete (d r : ℕ) :
    (∑ x : PairGrid d r,factoryAddressProjector d r x)=
      (1 : Matrix (Reg (d*r+3)) (Reg (d*r+3)) ℂ) := by
  ext q z
  simp only [Matrix.sum_apply]
  by_cases h : q=z
  · subst z
    simp [factoryAddressProjector]
  · simp [factoryAddressProjector,h]

/-- The address operators are their own Kraus effects, with no hidden access to the stored spin. -/
theorem factoryAddressProjector_effect (d r : ℕ) (x : PairGrid d r) :
    (factoryAddressProjector d r x).conjTranspose*factoryAddressProjector d r x=
      factoryAddressProjector d r x := by
  unfold factoryAddressProjector
  rw [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  congr 1
  funext q
  split_ifs <;> simp_all


open Qatlib.Concepts.SpinorSampling.FiniteExecution.MeasuredReset
open Qatlib.Concepts.SpinorSampling.Retained.PhysicalBell

/-- One ordinary prefix supply acts only on the already cleaned prefix and preserves the unchanged storage fibre. -/
def ordinaryPrefixFactory (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (stored : QState (Reg (d*r+3))) : QState (Reg (d*r+3)) :=
  freshPhysicalPrefix d r ψ (fun s => stored
    (Function.update (fun _ : Fin (d*r+3) => false) (factoryFirst d r) s))

/-- On the actual cleanup output this is exactly tensoring one new supplied copy with the unknown retained spin. -/
theorem ordinaryPrefixFactory_retained (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (u : Bool → ℂ) :
    ordinaryPrefixFactory d r ψ (retainedCleanState (factoryFirst d r) u)=
      freshPhysicalPrefix d r ψ u := by
  unfold ordinaryPrefixFactory
  simp_rw [retainedCleanState_read]

/-- The first-copy boundary includes the actual address measurement, native capture, spectator measurement and conditional cleanup on the same physical wires. -/
def canonicalFirstStorageBoundary (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (x : PairGrid d r) : QState (Reg (d*r+3)) :=
  let known := tofEmb (factoryLive d r) (factoryFirst d r) (factorySecond d r)
    (captureReg false false false) (factoryAddressBits d r x)
  Run (1 : Matrix (Reg (d*r+3)) (Reg (d*r+3)) ℂ)
    (measuredClearProgram (retainedCleanupWires (factoryFirst d r)) known)
    (ApplyGate (measuredMaskMatrix (retainedCleanupWires (factoryFirst d r)) known)
      (Run (1 : Matrix (Reg (d*r+3)) (Reg (d*r+3)) ℂ)
        (captureSwapProgram (d*r+3) (factoryLive d r) (factoryFirst d r))
        (ApplyGate (factoryAddressProjector d r x) (freshPhysicalPrefix d r ψ (Ket false)))))

/-- The actual state before requesting copy two retains exactly the original unknown spin on its original storage wire. -/
theorem canonicalFirstStorageBoundary_eq (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (x : PairGrid d r) : canonicalFirstStorageBoundary d r ψ x=
      retainedCleanState (factoryFirst d r) (suppliedSpinAt ψ x) := by
  have hab : factoryLive d r≠factoryFirst d r := by simp [factoryLive,factoryFirst,Fin.ext_iff]
  have hac : factoryLive d r≠factorySecond d r := by simp [factoryLive,factorySecond,Fin.ext_iff]
  have hbc : factoryFirst d r≠factorySecond d r := by simp [factoryFirst,factorySecond,Fin.ext_iff]
  dsimp only [canonicalFirstStorageBoundary]
  rw [factoryAddressProjector_apply,measuredFreshPrefixState_fibre]
  exact physical_first_capture_measured_cleanup _ _ _ hab hac hbc _ _

/-- At most one actual physical spin survives between the two source requests; no address or work qubit is hidden in the boundary. -/
theorem canonicalFirstStorageBoundary_one_spin (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (x : PairGrid d r) : AtMostOnePhysicalSpin (canonicalFirstStorageBoundary d r ψ x) :=
  Or.inr ⟨factoryFirst d r,suppliedSpinAt ψ x,canonicalFirstStorageBoundary_eq d r ψ x⟩

/-- Two actual canonical supplied prefixes are measured, captured and cleaned sequentially on the same unchanged storage wires. -/
def canonicalCapturedPair (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (x y : PairGrid d r) : QState (Reg (d*r+3)) :=
  let clean := canonicalFirstStorageBoundary d r ψ x
  let next := ApplyGate (factoryAddressProjector d r y) (ordinaryPrefixFactory d r ψ clean)
  Run (1 : Matrix (Reg (d*r+3)) (Reg (d*r+3)) ℂ)
    (captureSwapProgram (d*r+3) (factoryLive d r) (factorySecond d r)) next

/-- Actual complete address instruments, measured cleanup and two supplied-prefix calls produce the correct pair without a supplied state or moment certificate. -/
theorem canonicalCapturedPair_state (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (x y : PairGrid d r) :
    canonicalCapturedPair d r ψ x y=
      physicalTripleState (factoryLive d r) (factoryFirst d r) (factorySecond d r)
        (factoryAddressBits d r y)
        (captureTriple (Ket false) (suppliedSpinAt ψ x) (suppliedSpinAt ψ y)) := by
  have hab : factoryLive d r≠factoryFirst d r := by simp [factoryLive,factoryFirst,Fin.ext_iff]
  have hac : factoryLive d r≠factorySecond d r := by simp [factoryLive,factorySecond,Fin.ext_iff]
  have hbc : factoryFirst d r≠factorySecond d r := by simp [factoryFirst,factorySecond,Fin.ext_iff]
  dsimp only [canonicalCapturedPair]
  rw [canonicalFirstStorageBoundary_eq,ordinaryPrefixFactory_retained,
    factoryAddressProjector_apply,measuredFreshPrefixState_fibre,
    physical_second_capture _ _ _ hab hac hbc]

/-- The actual full-register two-supply execution and native conditional readout generate the complete joint source law, including misses. -/
theorem canonicalCapturedPair_joint_Born (d r : ℕ) (ψ : PairGrid d r → Bool → ℂ)
    (hψ : ∀ x,qubitMass (ψ x)=1) (τ : PairGrid d r → PairGrid d r)
    (x y : PairGrid d r) (out : Reg 2) :
    BornProb (Run (1 : Matrix (Reg (d*r+3)) (Reg (d*r+3)) ℂ)
      (physicalBellProgram (factoryFirst d r) (factorySecond d r) (decide (y=τ x)))
      (canonicalCapturedPair d r ψ x y))
      (tofEmb (factoryLive d r) (factoryFirst d r) (factorySecond d r)
        (captureReg false (out 0) (out 1)) (factoryAddressBits d r y)) =
      (pairedBellLaw ψ hψ τ).prob (x,y,out) := by
  have hab : factoryLive d r≠factoryFirst d r := by simp [factoryLive,factoryFirst,Fin.ext_iff]
  have hac : factoryLive d r≠factorySecond d r := by simp [factoryLive,factorySecond,Fin.ext_iff]
  have hbc : factoryFirst d r≠factorySecond d r := by simp [factoryFirst,factorySecond,Fin.ext_iff]
  rw [canonicalCapturedPair_state,physicalBellProgram_triple_Born _ _ _ hab hac hbc]
  rw [pairedBellLaw_actual_Born,twoCapturedSpins_eq]

/-- Clearing every measured full-register wire produces the true all-zero basis register. -/
theorem measuredClearBits_all_zero (n : ℕ) (x : Reg n) :
    measuredClearBits (allPhysicalWires n) x=(fun _ => false) := by
  funext k
  rw [measuredClearBits_apply]
  simp [allPhysicalWires,List.mem_ofFn]

/-- Every final computational readout, including zero-probability branches, is cleaned by its actual conditional correction word without changing its scalar amplitude. -/
theorem actualFullReadout_cleanup (n : ℕ) (φ : QState (Reg n)) (out : Reg n) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (measuredClearProgram (allPhysicalWires n) out)
      (φ out • Ket out)=φ out • Ket (fun _ : Fin n => false) := by
  rw [Qatlib.Concepts.StoppingCore.InterruptBridge.run_smul,
    measuredClearProgram_basis,measuredClearBits_all_zero]

/-- Current and unused-copy branches retain no unknown quantum wire after their actual complete readout and reset. -/
theorem actualFullReadout_zero_memory (n : ℕ) (φ : QState (Reg n)) (out : Reg n) :
    AtMostOnePhysicalSpin
      (Run (1 : Matrix (Reg n) (Reg n) ℂ) (measuredClearProgram (allPhysicalWires n) out)
        (φ out • Ket out)) :=
  Or.inl ⟨φ out,actualFullReadout_cleanup n φ out⟩

/-- Only the original dr address wires are measured before capture; both storage wires are excluded. -/
def canonicalAddressWires (d r : ℕ) : List (Fin (d*r+3)) :=
  List.ofFn (fun i : Fin (d*r) => ⟨i.val,by have hi := i.isLt; omega⟩)

/-- Reading precisely the trace's original address wires is equivalent to the canonical source address projector. -/
theorem canonicalAddressWires_condition (d r : ℕ) (q : Reg (d*r+3)) (x : PairGrid d r) :
    (∀ w∈canonicalAddressWires d r,q w=factoryAddressBits d r x w) ↔
      (freshFactoryLayout d r q).1.1.1=x := by
  have hx : positionEquiv d r (Fin.init (Fin.init (Fin.init (factoryAddressBits d r x))))=x := by
    have he := congrArg (fun p : (((PairGrid d r × Bool) × Bool) × Bool) => p.1.1.1)
      (factoryAddressBits_layout d r x)
    exact he
  constructor
  · intro hq
    change positionEquiv d r (Fin.init (Fin.init (Fin.init q)))=x
    rw [← hx]
    congr 1
    funext i
    have hi : (⟨i.val,by have hi := i.isLt; omega⟩ : Fin (d*r+3))∈canonicalAddressWires d r := by
      simp only [canonicalAddressWires,List.mem_ofFn]
      exact ⟨i,rfl⟩
    exact hq _ hi
  · intro hq w hw
    change positionEquiv d r (Fin.init (Fin.init (Fin.init q)))=x at hq
    have he : Fin.init (Fin.init (Fin.init q))=
        Fin.init (Fin.init (Fin.init (factoryAddressBits d r x))) :=
      (positionEquiv d r).injective (hq.trans hx.symm)
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hw
    rw [← hi]
    exact congrFun he i

/-- The measurement operation named by the paid address trace is the identical full-register projector used in its state and Born proof. -/
theorem canonicalAddressWires_projector (d r : ℕ) (x : PairGrid d r) :
    measuredMaskMatrix (canonicalAddressWires d r) (factoryAddressBits d r x)=
      factoryAddressProjector d r x := by
  unfold measuredMaskMatrix factoryAddressProjector
  congr 1
  funext q
  simp only [canonicalAddressWires_condition]

/-- The complete readout event in the same paid trace is exactly the unnormalized computational-basis outcome state. -/
theorem fullReadoutMask_apply (n : ℕ) (φ : QState (Reg n)) (out : Reg n) :
    ApplyGate (measuredMaskMatrix (allPhysicalWires n) out) φ=φ out • Ket out := by
  funext q
  rw [measuredMaskMatrix_apply]
  have he : (∀ w∈allPhysicalWires n,q w=out w) ↔ q=out := by
    constructor
    · intro h
      funext w
      exact h w (by simp [allPhysicalWires,List.mem_ofFn])
    · intro h w _
      rw [h]
  by_cases hq : q=out
  · subst q
    simp [Qatlib.Foundations.PureStateMath.Ket]
  · simp [he,hq,Qatlib.Foundations.PureStateMath.Ket]

/-- The literal full measurement action and its actual conditional correction clear every quantum wire while preserving its outcome amplitude. -/
theorem fullReadoutMask_cleanup (n : ℕ) (φ : QState (Reg n)) (out : Reg n) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (measuredClearProgram (allPhysicalWires n) out)
      (ApplyGate (measuredMaskMatrix (allPhysicalWires n) out) φ)=
        φ out • Ket (fun _ : Fin n => false) := by
  rw [fullReadoutMask_apply,actualFullReadout_cleanup]


/-- Current and discarded branches have no quantum memory after their literal full measurement and conditional native reset. -/
theorem fullReadoutMask_zero_memory (n : ℕ) (φ : QState (Reg n)) (out : Reg n) :
    AtMostOnePhysicalSpin
      (Run (1 : Matrix (Reg n) (Reg n) ℂ) (measuredClearProgram (allPhysicalWires n) out)
        (ApplyGate (measuredMaskMatrix (allPhysicalWires n) out) φ)) :=
  Or.inl ⟨φ out,fullReadoutMask_cleanup n φ out⟩

/-- The same canonical physical record determines every native operation, measurement and cleanup in this Bell run. -/
def canonicalBellPhysicalTrace (d r : ℕ) (j : Fin d)
    (x y : PairGrid d r) (out : Reg 2) : List (PairPhysicalAction (d*r+3)) :=
  bellPhysicalTrace (factoryLive d r) (factoryFirst d r) (factorySecond d r)
    (canonicalAddressWires d r) (factoryAddressBits d r x) (factoryAddressBits d r y)
    (factoryAddressMatch d r j x y) out

/-- All fees are derived from the actual canonical-address trace and the same observed pair, with both captures charged on a miss. -/
theorem canonicalBellPhysicalTrace_resources (d r : ℕ) (j : Fin d)
    (x y : PairGrid d r) (out : Reg 2) :
    ((canonicalBellPhysicalTrace d r j x y out).map PairPhysicalAction.copies).sum=2 ∧
    ((canonicalBellPhysicalTrace d r j x y out).map PairPhysicalAction.queries).sum=0 ∧
    ((canonicalBellPhysicalTrace d r j x y out).map PairPhysicalAction.gates).sum≤
      6+(if y=pairDoubleShift d r j x then 2 else 0)+12*(d*r+3) ∧
    ((canonicalBellPhysicalTrace d r j x y out).map PairPhysicalAction.measurements).sum≤4*(d*r+3) ∧
    ((canonicalBellPhysicalTrace d r j x y out).map PairPhysicalAction.resets).sum≤2*(d*r+3) := by
  have ha : (canonicalAddressWires d r).length≤d*r+3 := by
    simp only [canonicalAddressWires,List.length_ofFn]
    omega
  simpa only [canonicalBellPhysicalTrace,factoryAddressMatch_eq,decide_eq_true_eq] using
    bellPhysicalTrace_resources (factoryLive d r) (factoryFirst d r) (factorySecond d r)
      (canonicalAddressWires d r) ha (factoryAddressBits d r x) (factoryAddressBits d r y)
      (decide (y=pairDoubleShift d r j x)) out


end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
