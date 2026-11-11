/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBornBridge

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Complete raw native current observations

The same fair-neighbor coin and complete physical register outcome generate
the canonical signed address record. Normalization and weighted pushforward
are proved from the actual native Born circuit, with every work bit retained.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Concepts.SpinorSampling.NativeRecords.RawCurrentRecords
open Qatlib
open Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpinorSampling.Model

/-- One physical current measurement retains the actual fair-neighbor coin and every measured register bit, before extracting its signed address record. -/
def nativeCurrentRawLaw (d r : ℕ) (j : Fin d) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) : FinDist (Bool × Reg (registerWidth d r)) where
  prob z := BornProb (Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
    (velocityProgram d r j z.1) (encodeAmplitude d r (suppliedAncillaState a b c k))) z.2/2
  nonneg z := div_nonneg (sq_nonneg _) (by norm_num)
  sum_one := by
    simp only [Fintype.sum_prod_type, ← Finset.sum_div]
    have he (coin : Bool) : (∑ x : Reg (registerWidth d r),
        BornProb (Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
          (velocityProgram d r j coin) (encodeAmplitude d r (suppliedAncillaState a b c k))) x)=1 :=
      native_velocity_normalized d r j coin a b c k hz
    simp_rw [he]
    norm_num

/-- The full physical layout decodes the same address and test bit used by the actual signed record. -/
theorem raw_velocity_decode_basis (d r : ℕ) (coin : Bool) (s : Fin d → Fin (2^r))
    (spin test : Bool) (work : Reg (r-2)) :
    velocityRecord d r coin (basisAt d r s spin test work)=
      (s,if coin then test else !test) := by
  have h := decode_basis_at d r s spin test work
  have hs := congrArg (fun z : LayoutData d r => z.1) h
  have ht := congrArg (fun z : LayoutData d r => z.2.2.1) h
  change siteAddress d r (basisAt d r s spin test work)=s at hs
  change basisAt d r s spin test work (testWire d r)=test at ht
  simp only [velocityRecord, hs, ht]

/-- Summing all actual spin and work observations gives exactly the signed-address marginal, with no postselection or uncharged branch. -/
theorem raw_velocity_weighted_marginal (d r : ℕ) (coin : Bool)
    (ψ : QState (Reg (registerWidth d r))) (f : ((Fin d → Fin (2^r)) × Bool) → ℝ) :
    (∑ x : Reg (registerWidth d r), BornProb ψ x*f (velocityRecord d r coin x)) =
      ∑ out : (Fin d → Fin (2^r)) × Bool,
        physicalVelocityMass d r ψ out*f (out.1,if coin then out.2 else !out.2) := by
  have hrec (s : Fin d → Fin (2^r)) (spin test : Bool) (work : Reg (r-2)) :
      velocityRecord d r coin ((layoutEquiv d r).symm (s,spin,test,work)) =
        (s,if coin then test else !test) :=
    raw_velocity_decode_basis d r coin s spin test work
  calc _ = ∑ z : LayoutData d r, BornProb ψ ((layoutEquiv d r).symm z)*
              f (velocityRecord d r coin ((layoutEquiv d r).symm z)) :=
              ((layoutEquiv d r).symm.sum_comp _).symm
       _ = _ := by
         simp only [Fintype.sum_prod_type, physicalVelocityMass, Finset.sum_mul]
         simp_rw [hrec]
         apply Finset.sum_congr rfl
         intro s _
         simp only [basisAt]
         exact Finset.sum_comm

/-- Any numerical function of the observed native signed record has exactly the expectation of the existing physical current instrument. -/
theorem nativeCurrentRawLaw_record_expect (d r : ℕ) (j : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (f : ((Fin d → Fin (2^r)) × Bool) → ℝ) :
    (nativeCurrentRawLaw d r j a b c k hz).expect
      (fun z => f (velocityRecord d r z.1 z.2)) =
        (nativeCurrentLaw d r j a b c k hz).expect f := by
  unfold FinDist.expect nativeCurrentRawLaw
  rw [Fintype.sum_prod_type]
  have he (coin : Bool) :
      (∑ x : Reg (registerWidth d r),
        BornProb (Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
          (velocityProgram d r j coin) (encodeAmplitude d r (suppliedAncillaState a b c k))) x/2*
          f (velocityRecord d r coin x)) =
      (∑ out : (Fin d → Fin (2^r)) × Bool,
        physicalVelocityMass d r
          (Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
            (velocityProgram d r j coin) (encodeAmplitude d r (suppliedAncillaState a b c k))) out*
              f (out.1,if coin then out.2 else !out.2))/2 := by
    calc _ = (∑ x : Reg (registerWidth d r),
          BornProb (Run (1 : Matrix (Reg (registerWidth d r)) (Reg (registerWidth d r)) ℂ)
            (velocityProgram d r j coin) (encodeAmplitude d r (suppliedAncillaState a b c k))) x*
              f (velocityRecord d r coin x))/2 := by
                rw [Finset.sum_div]
                apply Finset.sum_congr rfl
                intro x _
                ring
         _ = _ := by rw [raw_velocity_weighted_marginal]
  simp_rw [he]
  simp only [Fintype.sum_bool, nativeCurrentLaw, nativeCurrentWeight, Fintype.sum_prod_type]
  dsimp
  rw [← add_div, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Bool.not_true,Bool.not_false]
  ring

/-- Two full raw physical observations push forward to exactly two independent native signed records, with their own coins and all measured register bits retained. -/
theorem nativeCurrentRawLaw_pair_expect (d r : ℕ) (j : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (F : ((Fin d → Fin (2^r)) × Bool) → ((Fin d → Fin (2^r)) × Bool) → ℝ) :
    (independentPairLaw (nativeCurrentRawLaw d r j a b c k hz)
      (nativeCurrentRawLaw d r j a b c k hz)).expect (fun z =>
        F (velocityRecord d r z.1.1 z.1.2) (velocityRecord d r z.2.1 z.2.2)) =
      (nativeCurrentLaw d r j a b c k hz).expect (fun l =>
        (nativeCurrentLaw d r j a b c k hz).expect (F l)) := by
  let p := nativeCurrentRawLaw d r j a b c k hz
  let record := fun z : Bool × Reg (registerWidth d r) => velocityRecord d r z.1 z.2
  have hpair : (independentPairLaw p p).expect (fun z => F (record z.1) (record z.2)) =
      p.expect (fun l => p.expect (fun out => F (record l) (record out))) := by
    unfold FinDist.expect independentPairLaw
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro out _
    ring
  change (independentPairLaw p p).expect (fun z => F (record z.1) (record z.2)) = _
  rw [hpair]
  have hinner (l : Bool × Reg (registerWidth d r)) :
      p.expect (fun out => F (record l) (record out)) =
        (nativeCurrentLaw d r j a b c k hz).expect (F (record l)) :=
    nativeCurrentRawLaw_record_expect d r j a b c k hz (F (record l))
  simp_rw [hinner]
  exact nativeCurrentRawLaw_record_expect d r j a b c k hz
    (fun l => (nativeCurrentLaw d r j a b c k hz).expect (F l))

end Qatlib.Concepts.SpinorSampling.NativeRecords.RawCurrentRecords
