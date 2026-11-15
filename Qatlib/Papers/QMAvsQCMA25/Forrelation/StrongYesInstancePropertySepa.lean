/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.WalshMoment.Forrelation.StrongYesInstancePropertyStat
public import Qatlib.Concepts.WalshMoment.Forrelation.SpectralForrelationBasicsSepa
public import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences
public import Qatlib.Concepts.WalshMoment.Forrelation.BooleanHadamardPhase

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.WalshMoment.Forrelation.SpectralForrelationBasicsSepa Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.WalshMoment.Forrelation.SpectralForrelationBasicsSepa
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.HspRecovery.ReductionCore
namespace Qatlib.Papers.QMAvsQCMA25.Forrelation.StrongYesInstancePropertySepa

open Qatlib
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib
open Qatlib
open scoped BigOperators
open Classical

set_option autoImplicit false

noncomputable def strongFailProb_absVersion (n ℓ : ℕ) (κ t1 t2 : ℝ) (v : ℕ) : ℝ :=
  (1 / (Fintype.card (Fin ℓ → Reg n) : ℝ)) *
    ∑ s : Fin ℓ → Reg n, ∑ u : Reg n → Bool,
      strongBernoulliWeight_absVersion n ℓ κ s u *
        (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)

def StrongYesInstanceProperty_absVersion : Prop :=
  ∀ (n ℓ : ℕ) (κ ρ : ℝ) (v : ℕ),
    0 < ℓ → 0 ≤ κ → κ ≤ 1 → 0 ≤ ρ →
    ∀ (t1 t2 : ℝ),
      t1 = (1 + κ) / 2 + (v : ℝ) / ℓ + ρ →
      t2 = (1 + 3 * κ) / 2 - 15 * κ ^ 2 / 4 - 5 * κ / ℓ - ρ →
      t1 < t2 →
      strongFailProb_absVersion n ℓ κ t1 t2 v ≤
        (ℓ : ℝ) ^ 6 * (2 : ℝ) ^ (-(n : ℤ)) +
          2 * (ℓ : ℝ) ^ 2 *
            Real.exp (-(ρ ^ 2 * (2 : ℝ) ^ n / (2 * (ℓ : ℝ) ^ 2)))

/-- The original strong failure probability equals its absolute-value formulation. -/
theorem strongFailProb_original_eq_absVersion (n ℓ : ℕ) (κ t1 t2 : ℝ) (v : ℕ) :
    strongFailProb n ℓ κ t1 t2 v = strongFailProb_absVersion n ℓ κ t1 t2 v := by
  simp only [strongFailProb, strongFailProb_absVersion,
    strongBernoulliWeight_original_eq_absVersion]

/-- The original strong yes-instance property is equivalent to its absolute-value formulation. -/
theorem strongYesInstanceProperty_original_iff_absVersion :
    StrongYesInstanceProperty ↔ StrongYesInstanceProperty_absVersion := by
  simp only [StrongYesInstanceProperty, StrongYesInstanceProperty_absVersion,
    strongFailProb_original_eq_absVersion]

example : gammaOfMultiset 1 2 (fun _ : Fin 2 => ZeroStr 1) (fun _ : Fin 1 => true) = 2 := by
  rw [gammaOfMultiset_eq_characterSquare]
  norm_num [bitDot, ZeroStr]

example : gammaOfMultiset 1 2 (fun _ : Fin 2 => fun _ : Fin 1 => true)
    (fun _ : Fin 1 => true) = 2 := by
  rw [gammaOfMultiset_eq_characterSquare]
  norm_num [bitDot, ZeroStr]

example : gammaOfMultiset 1 0 (fun i : Fin 0 => Fin.elim0 i)
    (fun _ : Fin 1 => true) = 0 := by
  simp [gammaOfMultiset]

section Signs

private def charSignR {n : ℕ} (z w : Reg n) : ℝ :=
  ∏ i, (if z i && w i then (-1 : ℝ) else 1)

/-- The complex coercion of `charSignR` is minus one when `bitDot` is true and one otherwise. -/
private theorem charSignC_bitDot {n : ℕ} (z w : Reg n) :
    (charSignR z w : ℂ) = if bitDot z w then (-1 : ℂ) else 1 := by
  have key : Qatlib.Concepts.PauliClifford.ExactRank.booleanCharacter
      (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n z) (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n w)
      = if bitDot z w then (-1 : ℂ) else 1 := by
    rw [Qatlib.Concepts.WalshMoment.Forrelation.booleanCharacter_regBooleanEquiv_apply]
    have hzero : bitDot z w = false ↔
        (∑ i, Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv (z i && w i)) = 0 := by
      simpa [bitDot, Qatlib.Concepts.WalshMoment.Forrelation.booleanDot_regBooleanEquiv] using!
        Qatlib.Concepts.HspRecovery.ReductionCore.booleanDotBool_eq_false_iff z w
    cases hb : bitDot z w with
    | false =>
        have h0 : (∑ i,
            Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv (z i && w i)) = 0 :=
            hzero.mp hb
        simp [h0]
    | true =>
        have hne : (∑ i, Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv (z i && w i)) ≠ 0 := by
          intro hz
          have : bitDot z w = false := hzero.mpr hz
          simp [hb] at this
        have hone : (∑ i, Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv (z i && w i)) = 1 := by
          have hv : (∑ i, Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv (z i && w i)).val < 2 :=
            ZMod.val_lt _
          have hv0 : (∑ i, Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv (z i && w i)).val ≠ 0 :=
            fun hval => hne ((ZMod.val_eq_zero _).mp hval)
          have : (∑ i,
              Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv
              (z i && w i)).val = 1 := by omega
          apply ZMod.val_injective 2
          simpa using! this
        simp [Qatlib.Concepts.WalshMoment.Forrelation.zmod2_stdAddChar_one, hone]
  have hprod : ((charSignR z w : ℂ)) =
      ∏ i, (if z i && w i then (-1 : ℂ) else 1) := by
    rw [charSignR, Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun i _ => by
      by_cases h : z i && w i <;> simp [h]
  rw [hprod,
      ← Qatlib.Concepts.WalshMoment.Forrelation.booleanCharacter_regBooleanEquiv_sign, key]

/-- The real character sign is minus one when `bitDot` is true and one otherwise. -/
private theorem charSignR_bitDot {n : ℕ} (z w : Reg n) :
    charSignR z w = if bitDot z w then (-1 : ℝ) else 1 := by
  apply Complex.ofReal_injective
  rw [charSignC_bitDot]
  by_cases h : bitDot z w <;> simp [h]

/-- Multiplication of character signs corresponds to XOR of their second arguments. -/
private theorem charSignR_mul {n : ℕ} (z x y : Reg n) :
    charSignR z x * charSignR z y = charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) := by
  unfold charSignR Qatlib.Concepts.WalshMoment.Forrelation.regXor
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by
    by_cases hz : z i <;> by_cases hx : x i <;> by_cases hy : y i <;>
      simp [hz, hx, hy, Bool.and, Bool.xor]

/-- The register type `Reg n` has cardinality two to the power `n`. -/
private theorem card_reg (n : ℕ) : Fintype.card (Reg n) = 2 ^ n := by
  rw [show Fintype.card (Reg n) = Fintype.card (Fin n → Bool) from rfl,
    Fintype.card_pi]
  simp

/-- The sum of a character is the register cardinality at the zero string and zero otherwise. -/
private theorem charSum_eq {n : ℕ} (w : Reg n) :
    ∑ z : Reg n, charSignR z w =
      if w = ZeroStr n then (Fintype.card (Reg n) : ℝ) else 0 := by
  have h := bv_orthogonality w (ZeroStr n)
  have hsimp : ∀ z : Reg n,
      (∏ i,
        ((if w i && z i then (-1 : ℂ) else 1) *
          (if ZeroStr n i && z i then (-1 : ℂ) else 1))) =
      ((charSignR z w : ℂ)) := by
    intro z
    rw [charSignR, Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun i _ => by
      have h0 : ZeroStr n i = false := rfl
      by_cases hw : w i <;> by_cases hz : z i <;> simp [hw, hz, h0]
  rw [Finset.sum_congr rfl (fun z _ => hsimp z)] at h
  rcases Decidable.em (w = ZeroStr n) with hw | hw
  · rw [ite_eq_left hw]
    have hcard : ∀ i, w i = ZeroStr n i := fun i => by rw [hw]
    rw [ite_eq_left hcard] at h
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, h, card_reg]
    push_cast
    ring
  · rw [ite_eq_right hw]
    have hne : ¬ ∀ i, w i = ZeroStr n i := by
      intro hall; exact hw (funext (fun i => hall i))
    rw [ite_eq_right hne] at h
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, h]
    simp

/-- Each entry of `HadamardN` is the corresponding character sign multiplied by the Hadamard
normalization factor. -/
private theorem hadamardN_entry {n : ℕ} (z x : Reg n) :
    HadamardN n z x = ((Real.sqrt 2 : ℂ)⁻¹) ^ n * (charSignR z x : ℂ) := by
  rw [hadamardN_apply]
  congr 1
  rw [charSignR, Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun i _ => by
    by_cases hz : z i <;> by_cases hx : x i <;> simp [hz, hx]

/-- The square of the Hadamard normalization factor is the reciprocal register cardinality,
viewed in the complex numbers. -/
private theorem sqrt2inv_pow_sq {n : ℕ} :
    (((Real.sqrt 2 : ℂ)⁻¹) ^ n) ^ 2 = ((Fintype.card (Reg n) : ℝ)⁻¹ : ℂ) := by
  rw [pow_two, ← mul_pow, inv_sqrt2_mul_self, inv_pow, card_reg]
  push_cast
  ring

end Signs

section Entries

private noncomputable def uEntry {n : ℕ} (u : Reg n → Bool) (x y : Reg n) : ℝ :=
  (Fintype.card (Reg n) : ℝ)⁻¹ *
    ∑ z : Reg n, (if u z then 1 else 0) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y)

/-- Register XOR is commutative. -/
private theorem regXor_comm {n : ℕ} (x y : Reg n) : Qatlib.Concepts.WalshMoment.Forrelation.regXor x y = Qatlib.Concepts.WalshMoment.Forrelation.regXor y x := by
  unfold Qatlib.Concepts.WalshMoment.Forrelation.regXor
  funext i
  exact Bool.xor_comm (x i) (y i)

/-- The kernel `uEntry` is symmetric in its register arguments. -/
private theorem uEntry_symm {n : ℕ} (u : Reg n → Bool) (x y : Reg n) :
    uEntry u x y = uEntry u y x := by
  unfold uEntry
  exact congrArg _ (Finset.sum_congr rfl fun z _ => by
    rw [regXor_comm])

/-- Expands the coordinates of a state after projection onto `S`, application of `HadamardN`,
and projection onto `U`. -/
private theorem vecEntry_eq {n : ℕ} (S U : Reg n → Bool) (ψ : QState (Reg n)) (z : Reg n) :
    ((charProjector n U * HadamardN n * charProjector n S).mulVec ψ) z =
      if U z then ((Real.sqrt 2 : ℂ)⁻¹) ^ n *
        ∑ x : Reg n, (charSignR z x : ℂ) * (if S x then ψ x else 0) else 0 := by
  have hsplit : (charProjector n U * HadamardN n * charProjector n S).mulVec ψ =
      (charProjector n U).mulVec
        ((HadamardN n).mulVec ((charProjector n S).mulVec ψ)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hsplit]
  have houter : ((charProjector n U).mulVec
      ((HadamardN n).mulVec ((charProjector n S).mulVec ψ))) z =
      (if U z then (1 : ℂ) else 0) *
        ((HadamardN n).mulVec ((charProjector n S).mulVec ψ)) z := by
    simp only [charProjector, Matrix.mulVec_diagonal]
  rw [houter]
  have hmid : ((HadamardN n).mulVec ((charProjector n S).mulVec ψ)) z =
      ∑ x : Reg n, ((Real.sqrt 2 : ℂ)⁻¹) ^ n *
        (charSignR z x : ℂ) * ((charProjector n S).mulVec ψ) x := by
    rw [Matrix.mulVec]
    exact Finset.sum_congr rfl fun x _ => by
      show HadamardN n z x * _ = _
      rw [hadamardN_entry z x]
  rw [hmid]
  by_cases hU : U z
  · rw [ite_eq_left hU, ite_eq_left hU, one_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hinner : ((charProjector n S).mulVec ψ) x =
        (if S x then (1 : ℂ) else 0) * ψ x := by
      simp only [charProjector, Matrix.mulVec_diagonal]
    rw [hinner]
    by_cases hS : S x
    · simp only [hS, ite_true]
      ring
    · simp [hS]
  · rw [ite_eq_right hU, ite_eq_right hU, zero_mul]

/-- The squared complex norm is the real part of the product with the complex conjugate. -/
private theorem cnorm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = (z * (starRingEnd ℂ z)).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- Complex conjugation fixes the Hadamard normalization factor. -/
private theorem csqrt2_conj (n : ℕ) :
    (starRingEnd ℂ) (((Real.sqrt 2 : ℂ)⁻¹) ^ n) = ((Real.sqrt 2 : ℂ)⁻¹) ^ n := by
  rw [map_pow, map_inv₀, Complex.conj_ofReal]

/-- Expands each squared output amplitude of the projected Hadamard transform as a double
character sum. -/
private theorem mass_z_eq {n : ℕ} (S U : Reg n → Bool) (ψ : QState (Reg n)) (z : Reg n) :
    ‖((charProjector n U * HadamardN n * charProjector n S).mulVec ψ) z‖ ^ 2 =
      if U z then
        ∑ x : Reg n, ∑ y : Reg n,
          ((ψ x * (starRingEnd ℂ (ψ y))).re *
            ((if S x then 1 else 0) * (if S y then 1 else 0) *
              charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) * (Fintype.card (Reg n) : ℝ)⁻¹))
      else 0 := by
  rw [vecEntry_eq]
  by_cases hU : U z
  · rw [ite_eq_left hU, cnorm_sq_eq]
    set c : ℂ := ((Real.sqrt 2 : ℂ)⁻¹) ^ n with hcdef
    set A : ℂ := ∑ x : Reg n, (charSignR z x : ℂ) * (if S x then ψ x else 0) with hAdef
    have hcconj : (starRingEnd ℂ) c = c := csqrt2_conj n
    have hc2 : c * c = ((Fintype.card (Reg n) : ℝ)⁻¹ : ℂ) := by
      conv_lhs => rw [← pow_two]
      rw [hcdef]
      exact sqrt2inv_pow_sq
    rw [map_mul, hcconj,
      show c * A * (c * (starRingEnd ℂ A)) = c * c * (A * (starRingEnd ℂ A)) from by ring,
      hc2]
    have houter : (((Fintype.card (Reg n) : ℝ)⁻¹ : ℂ) * (A * (starRingEnd ℂ A))).re =
        (Fintype.card (Reg n) : ℝ)⁻¹ * ((A * (starRingEnd ℂ A)).re) := by
      have hscalar : ∀ (k : ℝ) (W : ℂ), (((k : ℂ))⁻¹ * W).re = k⁻¹ * W.re := by
        intro k W
        rw [Complex.mul_re, ← Complex.ofReal_inv, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
      exact hscalar _ _
    have hconjA : (starRingEnd ℂ A) =
        ∑ y : Reg n, (charSignR z y : ℂ) * (if S y then (starRingEnd ℂ (ψ y)) else 0) := by
      rw [hAdef, map_sum]
      exact Finset.sum_congr rfl fun y _ => by
        rw [map_mul, Complex.conj_ofReal]
        by_cases hS : S y <;> simp [hS]
    have key1 : ∀ (r s : ℝ) (w : ℂ), (r : ℂ) * ((s : ℂ) * w) = ((r * s : ℝ) : ℂ) * w := by
      intro r s w
      rw [← mul_assoc, ← Complex.ofReal_mul]
    have hmul : A * (starRingEnd ℂ A) =
        ∑ x : Reg n, ∑ y : Reg n,
          (((charSignR z x * (if S x then 1 else 0)) * (charSignR z y * (if S y then 1 else 0)) : ℝ) : ℂ) *
            (ψ x * (starRingEnd ℂ (ψ y))) := by
      rw [hAdef, hconjA, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hx : S x <;> by_cases hy : S y <;>
        simp only [hx, hy, ite_true, ite_false, Complex.ofReal_mul, Complex.ofReal_zero,
          zero_mul, mul_zero, mul_one, Bool.false_eq_true,
          ite_false]
      all_goals ring
    have hre2 : ((A * (starRingEnd ℂ A)).re) =
        ∑ x : Reg n, ∑ y : Reg n,
          ((ψ x * (starRingEnd ℂ (ψ y))).re *
            (charSignR z x * (if S x then 1 else 0) * (charSignR z y * (if S y then 1 else 0)))) := by
      rw [hmul, Complex.re_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, ]
      ring
    rw [houter, hre2, ite_eq_left hU]
    rw [show (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ x : Reg n, ∑ y : Reg n,
          ((ψ x * (starRingEnd ℂ (ψ y))).re *
            (charSignR z x * (if S x then 1 else 0) * (charSignR z y * (if S y then 1 else 0))) : ℝ) =
        ∑ x : Reg n, ∑ y : Reg n,
          ((ψ x * (starRingEnd ℂ (ψ y))).re *
            ((if S x then 1 else 0) * (if S y then 1 else 0) *
              charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) * (Fintype.card (Reg n) : ℝ)⁻¹)) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by
          rw [← charSignR_mul z x y]
          ring]
  · rw [ite_eq_right hU]
    simp [hU]

/-- Moves the outer register sum to the innermost position in a triple finite sum. -/
private theorem sum_comm3 {n : ℕ} {M : Type*} [AddCommMonoid M]
    (F : Reg n → Reg n → Reg n → M) :
    (∑ z : Reg n, ∑ x : Reg n, ∑ y : Reg n, F z x y) =
      ∑ x : Reg n, ∑ y : Reg n, ∑ z : Reg n, F z x y := by
  have step1 : (∑ z : Reg n, ∑ x : Reg n, ∑ y : Reg n, F z x y) =
      ∑ x : Reg n, ∑ z : Reg n, ∑ y : Reg n, F z x y := Finset.sum_comm
  have step2 : ∀ x : Reg n, (∑ z : Reg n, ∑ y : Reg n, F z x y) =
      ∑ y : Reg n, ∑ z : Reg n, F z x y := fun x => Finset.sum_comm
  rw [step1]
  exact Finset.sum_congr rfl fun x _ => step2 x

/-- Expresses the forrelation witness mass as a quadratic expression involving `uEntry` and the
support indicator. -/
private theorem forrWitnessMass_eq_quad {n : ℕ} (S U : Reg n → Bool) (ψ : QState (Reg n)) :
    forrWitnessMass n S U ψ =
      ∑ x : Reg n, ∑ y : Reg n,
        ((ψ x * (starRingEnd ℂ (ψ y))).re) *
          ((if S x then 1 else 0) * (if S y then 1 else 0) * uEntry U x y) := by
  unfold forrWitnessMass
  rw [norm_toEuclidean_fromVec_sq]
  have hites : ∀ (b : Bool) (W : ℝ), (if b then 1 else 0) * W = if b then W else 0 := by
    intro b W
    cases b <;> simp
  rw [Finset.sum_congr rfl (fun z _ => mass_z_eq S U ψ z)]
  have hbridge : (∑ z : Reg n,
      if U z then
        ∑ x : Reg n, ∑ y : Reg n,
          ((ψ x * (starRingEnd ℂ (ψ y))).re *
            ((if S x then 1 else 0) * (if S y then 1 else 0) *
              charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) * (Fintype.card (Reg n) : ℝ)⁻¹))
      else 0) =
      ∑ z : Reg n, ∑ x : Reg n, ∑ y : Reg n,
        (if U z then 1 else 0 : ℝ) *
          ((ψ x * (starRingEnd ℂ (ψ y))).re *
            ((if S x then 1 else 0) * (if S y then 1 else 0) *
              charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) * (Fintype.card (Reg n) : ℝ)⁻¹)) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : U z
    · rw [ite_eq_left hz]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [ite_eq_left hz, one_mul]
    · rw [ite_eq_right hz]
      simp [hz]
  rw [hbridge,
    sum_comm3 (fun z x y =>
      (if U z then 1 else 0 : ℝ) *
        ((ψ x * (starRingEnd ℂ (ψ y))).re *
          ((if S x then 1 else 0) * (if S y then 1 else 0) *
            charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) * (Fintype.card (Reg n) : ℝ)⁻¹)))]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hc : ∀ z : Reg n,
      (if U z then 1 else 0 : ℝ) *
        ((ψ x * (starRingEnd ℂ (ψ y))).re *
          ((if S x then 1 else 0) * (if S y then 1 else 0) *
            charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) * (Fintype.card (Reg n) : ℝ)⁻¹)) =
      (((ψ x * (starRingEnd ℂ (ψ y))).re) *
          ((if S x then 1 else 0) * (if S y then 1 else 0) *
            (Fintype.card (Reg n) : ℝ)⁻¹)) *
        ((if U z then 1 else 0) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y)) := fun z => by ring
  rw [Finset.sum_congr rfl (fun z _ => hc z), ← Finset.mul_sum]
  unfold uEntry
  ring

end Entries

section FourierCounts

private def rawGamma {n ℓ : ℕ} (s : Fin ℓ → Reg n) (y : Reg n) : ℝ :=
  ∑ i : Fin ℓ, ∑ j : Fin ℓ, charSignR y (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j))

private def pairCount {n ℓ : ℕ} (s : Fin ℓ → Reg n) (w : Reg n) : ℕ :=
  ∑ i : Fin ℓ, ∑ j : Fin ℓ, if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = w then 1 else 0

private def quadCount {n ℓ : ℕ} (s : Fin ℓ → Reg n) (w : Reg n) : ℕ :=
  ∑ i : Fin ℓ, ∑ j : Fin ℓ, ∑ k : Fin ℓ, ∑ l : Fin ℓ,
    if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) = w then 1 else 0

/-- Multiplying `gammaOfMultiset` by the multiset length gives `rawGamma`. -/
private theorem gamma_mul_ell {n ℓ : ℕ} (s : Fin ℓ → Reg n) (y : Reg n) :
    (ℓ : ℝ) * gammaOfMultiset n ℓ s y = rawGamma s y := by
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · subst hℓ
    simp [rawGamma]
  · have hne : ((ℓ : ℝ)) ≠ 0 := by exact_mod_cast hℓ.ne'
    have hone : ((ℓ : ℝ)) * (1 / (ℓ : ℝ)) = 1 := by field_simp
    unfold gammaOfMultiset rawGamma
    rw [← mul_assoc, hone, one_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      (charSignR_bitDot y (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j))).symm

/-- Expresses `rawGamma` as a double sum of signs determined by the bit dot product with
pairwise XORs. -/
private theorem rawGamma_eq_bitDotSum {n ℓ : ℕ} (s : Fin ℓ → Reg n) (y : Reg n) :
    rawGamma s y =
      ∑ i : Fin ℓ, ∑ j : Fin ℓ,
        (if bitDot y (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) then (-1 : ℝ) else 1) := by
  unfold rawGamma
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    charSignR_bitDot y (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j))

/-- Register XOR is associative. -/
private theorem regXor_assoc {n : ℕ} (x y z : Reg n) :
    Qatlib.Concepts.WalshMoment.Forrelation.regXor x (Qatlib.Concepts.WalshMoment.Forrelation.regXor y z) = Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) z := by
  funext k
  simp [Qatlib.Concepts.WalshMoment.Forrelation.regXor]

/-- XOR of a register with itself is the zero string. -/
private theorem regXor_invol {n : ℕ} (x : Reg n) : Qatlib.Concepts.WalshMoment.Forrelation.regXor x x = ZeroStr n := by
  funext k
  simp [Qatlib.Concepts.WalshMoment.Forrelation.regXor, ZeroStr]

/-- The zero string is a left identity for register XOR. -/
private theorem regXor_zero_left {n : ℕ} (x : Reg n) : Qatlib.Concepts.WalshMoment.Forrelation.regXor (ZeroStr n) x = x := by
  funext k; simp [Qatlib.Concepts.WalshMoment.Forrelation.regXor, ZeroStr]

/-- A nested XOR vanishes exactly when the XOR of the first two registers equals the third. -/
private theorem regXor_cancel {n : ℕ} (x y w : Reg n) :
    Qatlib.Concepts.WalshMoment.Forrelation.regXor x (Qatlib.Concepts.WalshMoment.Forrelation.regXor y w) = ZeroStr n ↔ Qatlib.Concepts.WalshMoment.Forrelation.regXor x y = w := by
  constructor
  · intro h
    have h2 : Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) w = ZeroStr n := by
      rw [← regXor_assoc]; exact h
    have h3 := congrArg (fun t : Reg n => Qatlib.Concepts.WalshMoment.Forrelation.regXor t w) h2

    have hL : Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) w) w = Qatlib.Concepts.WalshMoment.Forrelation.regXor x y := by
      funext k
      simp [Qatlib.Concepts.WalshMoment.Forrelation.regXor]
    rw [hL] at h3
    rwa [regXor_zero_left] at h3
  · intro h
    rw [regXor_assoc, h, regXor_invol]

/-- The character transform of `rawGamma` is the register cardinality times `pairCount`. -/
private theorem sum_rawGamma_mul_sign {n ℓ : ℕ} (s : Fin ℓ → Reg n) (w : Reg n) :
    (∑ z : Reg n, rawGamma s z * charSignR z w) =
      (Fintype.card (Reg n) : ℝ) * (pairCount s w : ℝ) := by
  unfold rawGamma
  simp only [Finset.sum_mul]
  have hswap : ∀ (F : Reg n → Fin ℓ → Fin ℓ → ℝ),
      (∑ z : Reg n, ∑ i : Fin ℓ, ∑ j : Fin ℓ, F z i j) =
        ∑ i : Fin ℓ, ∑ j : Fin ℓ, ∑ z : Reg n, F z i j := by
    intro F
    have step1 : (∑ z : Reg n, ∑ i : Fin ℓ, ∑ j : Fin ℓ, F z i j) =
        ∑ i : Fin ℓ, ∑ z : Reg n, ∑ j : Fin ℓ, F z i j := Finset.sum_comm
    have step2 : ∀ i : Fin ℓ, (∑ z : Reg n, ∑ j : Fin ℓ, F z i j) =
        ∑ j : Fin ℓ, ∑ z : Reg n, F z i j := fun i => Finset.sum_comm
    rw [step1]
    exact Finset.sum_congr rfl fun i _ => step2 i
  have hsw := hswap (fun (z : Reg n) (i j : Fin ℓ) =>
    (charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) * charSignR z w : ℝ))
  have hR : (Fintype.card (Reg n) : ℝ) * (pairCount s w : ℝ) =
      ∑ i : Fin ℓ, ∑ j : Fin ℓ,
        (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = w then (Fintype.card (Reg n) : ℝ) else 0) := by
    unfold pairCount
    simp only [Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = w
    · simp [h]
    · simp [h]
  rw [hsw, hR]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hz : ∀ z : Reg n,
      charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) * charSignR z w = charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) w)) := by
    intro z
    rw [← charSignR_mul z (s i) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) w), ← charSignR_mul z (s j) w,
      ← charSignR_mul z (s i) (s j)]
    ring
  rw [Finset.sum_congr rfl (fun z _ => hz z), charSum_eq]
  by_cases hw : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = w
  · have hz2 : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) w) = ZeroStr n := by
      rw [regXor_assoc, hw, regXor_invol]
    rw [ite_eq_left hz2, ite_eq_left hw]
  · have hz2 : ¬ (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) w) = ZeroStr n) := by
      intro h
      exact hw ((regXor_cancel (s i) (s j) w).mp h)
    rw [ite_eq_right hz2, ite_eq_right hw]

/-- The zero string is a right identity for register XOR. -/
private theorem regXor_zero_right {n : ℕ} (x : Reg n) : Qatlib.Concepts.WalshMoment.Forrelation.regXor x (ZeroStr n) = x := by
  funext k; simp [Qatlib.Concepts.WalshMoment.Forrelation.regXor, ZeroStr]

/-- The XOR of two registers vanishes exactly when they are equal. -/
private theorem regXor_eq_zero {n : ℕ} (x y : Reg n) : Qatlib.Concepts.WalshMoment.Forrelation.regXor x y = ZeroStr n ↔ x = y := by
  constructor
  · intro h
    have h1 : Qatlib.Concepts.WalshMoment.Forrelation.regXor x (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) = y := by
      rw [regXor_assoc, regXor_invol, regXor_zero_left]
    rw [h, regXor_zero_right] at h1
    exact h1
  · intro h
    rw [h, regXor_invol]

/-- The sum of three multiplied characters is the register cardinality when their arguments XOR
to zero, and zero otherwise. -/
private theorem sum_sign_triple {n : ℕ} (x y w : Reg n) :
    ∑ z : Reg n, charSignR z x * charSignR z y * charSignR z w =
      if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) w = ZeroStr n then (Fintype.card (Reg n) : ℝ) else 0 := by
  have hzz : ∀ z : Reg n,
      charSignR z x * charSignR z y * charSignR z w = charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) w) := by
    intro z
    rw [charSignR_mul z x y, charSignR_mul z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) w]
  rw [Finset.sum_congr rfl (fun z _ => hzz z), charSum_eq]

/-- The character transform of the square of `rawGamma` is the register cardinality times
`quadCount`. -/
private theorem sum_rawGamma_sq_mul_sign {n ℓ : ℕ} (s : Fin ℓ → Reg n) (w : Reg n) :
    (∑ z : Reg n, rawGamma s z * rawGamma s z * charSignR z w) =
      (Fintype.card (Reg n) : ℝ) * (quadCount s w : ℝ) := by
  have hsq : ∀ z : Reg n, rawGamma s z * rawGamma s z =
      ∑ i : Fin ℓ, ∑ j : Fin ℓ, ∑ k : Fin ℓ, ∑ l : Fin ℓ,
        charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)) := by
    intro z
    unfold rawGamma
    have step1 : (∑ i : Fin ℓ, ∑ j : Fin ℓ, charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j))) *
        (∑ k : Fin ℓ, ∑ l : Fin ℓ, charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) =
        ∑ i : Fin ℓ, ∑ k : Fin ℓ,
          (∑ j : Fin ℓ, charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j))) *
          (∑ l : Fin ℓ, charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) :=
      Finset.sum_mul_sum _ _ _ _
    have step2 : ∀ (i k : Fin ℓ),
        (∑ j : Fin ℓ, charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j))) *
          (∑ l : Fin ℓ, charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) =
        ∑ j : Fin ℓ, ∑ l : Fin ℓ,
          charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)) :=
      fun _ _ => Finset.sum_mul_sum _ _ _ _
    have step3 : ∀ i : Fin ℓ,
        (∑ k : Fin ℓ, ∑ j : Fin ℓ, ∑ l : Fin ℓ,
          charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) =
        (∑ j : Fin ℓ, ∑ k : Fin ℓ, ∑ l : Fin ℓ,
          charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) :=
      fun _ => Finset.sum_comm
    rw [step1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl (fun k _ => step2 i k), step3 i]
  have hR : (Fintype.card (Reg n) : ℝ) * (quadCount s w : ℝ) =
      ∑ i : Fin ℓ, ∑ j : Fin ℓ, ∑ k : Fin ℓ, ∑ l : Fin ℓ,
        (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) = w then
          (Fintype.card (Reg n) : ℝ) else 0) := by
    unfold quadCount
    simp only [Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases h : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) = w
    · simp [h]
    · simp [h]
  have hswap4 : ∀ (F : Reg n → Fin ℓ → Fin ℓ → Fin ℓ → Fin ℓ → ℝ),
      (∑ z : Reg n, ∑ i : Fin ℓ, ∑ j : Fin ℓ, ∑ k : Fin ℓ, ∑ l : Fin ℓ, F z i j k l) =
        ∑ i : Fin ℓ, ∑ j : Fin ℓ, ∑ k : Fin ℓ, ∑ l : Fin ℓ, ∑ z : Reg n, F z i j k l := by
    intro F
    have e1 : (∑ z : Reg n, ∑ i : Fin ℓ, ∑ j : Fin ℓ, ∑ k : Fin ℓ, ∑ l : Fin ℓ, F z i j k l) =
        ∑ i : Fin ℓ, ∑ z : Reg n, ∑ j : Fin ℓ, ∑ k : Fin ℓ, ∑ l : Fin ℓ, F z i j k l :=
      Finset.sum_comm
    have e2 : ∀ i : Fin ℓ, (∑ z : Reg n, ∑ j : Fin ℓ, ∑ k : Fin ℓ, ∑ l : Fin ℓ, F z i j k l) =
        ∑ j : Fin ℓ, ∑ z : Reg n, ∑ k : Fin ℓ, ∑ l : Fin ℓ, F z i j k l :=
      fun _ => Finset.sum_comm
    have e3 : ∀ (i j : Fin ℓ), (∑ z : Reg n, ∑ k : Fin ℓ, ∑ l : Fin ℓ, F z i j k l) =
        ∑ k : Fin ℓ, ∑ z : Reg n, ∑ l : Fin ℓ, F z i j k l :=
      fun _ _ => Finset.sum_comm
    have e4 : ∀ (i j k : Fin ℓ), (∑ z : Reg n, ∑ l : Fin ℓ, F z i j k l) =
        ∑ l : Fin ℓ, ∑ z : Reg n, F z i j k l :=
      fun _ _ _ => Finset.sum_comm
    rw [e1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e2 i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [e3 i j]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [e4 i j k]
  simp only [hsq, Finset.sum_mul]
  have hsw := hswap4 (fun (z : Reg n) (i j k l : Fin ℓ) =>
    (charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)) * charSignR z w : ℝ))
  rw [hsw, hR]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hassoc : Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)) =
      Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) := by rw [← regXor_assoc]
  rw [sum_sign_triple (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)) w]
  by_cases hw : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) = w
  · have h0 : Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) w = ZeroStr n := by
      rw [hassoc, hw, regXor_invol]
    rw [ite_eq_left h0, ite_eq_left hw]
  · have h0 : ¬ (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) w = ZeroStr n) := by
      intro h
      have h1 : Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)) = w :=
        (regXor_eq_zero _ w).mp h
      rw [hassoc] at h1
      exact hw h1
    rw [ite_eq_right h0, ite_eq_right hw]

end FourierCounts

section TaylorQuad

/-- For nonnegative `x`, one minus the exponential of negative `x` is at most `x`. -/
private theorem one_sub_exp_le {x : ℝ} (_hx : 0 ≤ x) : 1 - Real.exp (-x) ≤ x := by
  have h := Real.add_one_le_exp (-x)
  linarith

/-- For nonnegative `t`, the exponential dominates its quadratic Taylor polynomial at zero. -/
private theorem one_add_add_half_le_exp {t : ℝ} (ht : 0 ≤ t) :
    1 + t + t ^ 2 / 2 ≤ Real.exp t := by
  have h1i : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 t :=
    continuous_const.intervalIntegrable 0 t
  have hexp : ∫ s in 0..t, Real.exp s = Real.exp t - Real.exp 0 := by
    have hint : IntervalIntegrable (deriv Real.exp) MeasureTheory.volume 0 t := by
      rw [Real.deriv_exp]
      exact Real.continuous_exp.intervalIntegrable 0 t
    have h := intervalIntegral.integral_deriv_eq_sub (f := Real.exp)
      (fun x _ => Real.differentiableAt_exp (x := x)) hint
    rw [Real.deriv_exp] at h
    simp
  have hs : ∫ s in 0..t, s = t ^ 2 / 2 - 0 ^ 2 / 2 := by
    have hf : ∀ x ∈ Set.uIcc (0 : ℝ) t, DifferentiableAt ℝ (fun u => u * u / 2) x := by
      intro x _
      fun_prop
    have hd : IntervalIntegrable (deriv (fun u : ℝ => u * u / 2)) MeasureTheory.volume 0 t := by
      have heq : ∀ u : ℝ, deriv (fun v => v * v / 2) u = u := by
        intro u
        have h3 : HasDerivAt (fun v : ℝ => v * v / 2) ((1 * u + u * 1) / 2) u :=
          ((hasDerivAt_id u).mul (hasDerivAt_id u)).div_const (2 : ℝ)
        have h4 : HasDerivAt (fun v : ℝ => v * v / 2) u u :=
          h3.congr_deriv (by ring)
        exact h4.deriv
      have hii : IntervalIntegrable (fun u : ℝ => u) MeasureTheory.volume 0 t :=
        continuous_id.intervalIntegrable 0 t
      rw [funext heq]
      exact hii
    have h := intervalIntegral.integral_deriv_eq_sub (f := fun u => u * u / 2) hf hd
    simp
  have h2i : IntervalIntegrable (fun s : ℝ => s) MeasureTheory.volume 0 t :=
    continuous_id.intervalIntegrable 0 t
  have hline : ∫ s in 0..t, ((1 : ℝ) + s) = t + t ^ 2 / 2 := by
    have hsplit : ∫ s in 0..t, ((1 : ℝ) + s) = (∫ s in 0..t, (1 : ℝ)) + ∫ s in 0..t, s :=
      intervalIntegral.integral_add h1i h2i
    rw [hsplit, intervalIntegral.integral_const (1 : ℝ), hs]
    simp
  have hlin : IntervalIntegrable (fun s : ℝ => (1 : ℝ) + s) MeasureTheory.volume 0 t :=
    (by continuity : Continuous (fun s : ℝ => (1 : ℝ) + s)).intervalIntegrable 0 t
  have hEi : IntervalIntegrable Real.exp MeasureTheory.volume 0 t :=
    Real.continuous_exp.intervalIntegrable 0 t
  have hmono : (∫ s in 0..t, (1 : ℝ) + s) ≤ ∫ s in 0..t, Real.exp s :=
    intervalIntegral.integral_mono_on ht hlin hEi
      (fun s _ => by rw [add_comm]; exact Real.add_one_le_exp s)
  rw [hline, hexp] at hmono
  have hfinal : t + t ^ 2 / 2 ≤ Real.exp t - 1 := by
    simpa using! hmono
  linarith

/-- For nonnegative `t`, one minus the exponential of negative `t` is at least `t` minus half
its square. -/
private theorem sub_sq_half_le_one_sub_exp {t : ℝ} (ht : 0 ≤ t) :
    t - t ^ 2 / 2 ≤ 1 - Real.exp (-t) := by
  have hm : 0 < 1 + t + t ^ 2 / 2 := by nlinarith
  have h1 : Real.exp (-t) * (1 + t + t ^ 2 / 2) ≤ 1 := by
    have hkey : Real.exp (-t) * (1 + t + t ^ 2 / 2) ≤ Real.exp (-t) * Real.exp t :=
      mul_le_mul_of_nonneg_left (one_add_add_half_le_exp ht) (le_of_lt (Real.exp_pos (-t)))
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hkey
    simpa using! hkey
  have h2 : (1 - t + t ^ 2 / 2) * (1 + t + t ^ 2 / 2) = 1 + t ^ 4 / 4 := by ring
  have h3 : Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
    by_contra hcontra
    have hlt : (1 - t + t ^ 2 / 2) < Real.exp (-t) := lt_of_not_ge hcontra
    have hgt : (1 - t + t ^ 2 / 2) * (1 + t + t ^ 2 / 2) <
        Real.exp (-t) * (1 + t + t ^ 2 / 2) :=
      mul_lt_mul_of_pos_right hlt hm
    rw [h2] at hgt
    have ht4 : 0 ≤ t ^ 4 := by positivity
    linarith
  linarith

/-- The character sign with the zero string as its first argument equals one. -/
private theorem charSignR_one_left {n : ℕ} (w : Reg n) : charSignR (ZeroStr n) w = 1 := by
  unfold charSignR ZeroStr
  simp

/-- At the zero string, `gammaOfMultiset` equals the multiset length. -/
private theorem gamma_zero {n ℓ : ℕ} (s : Fin ℓ → Reg n) :
    gammaOfMultiset n ℓ s (ZeroStr n) = (ℓ : ℝ) := by
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · subst hℓ
    unfold gammaOfMultiset
    simp
  · have hℝ : ((ℓ : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hrg : rawGamma s (ZeroStr n) = ((ℓ : ℝ)) * (ℓ : ℝ) := by
      unfold rawGamma
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
          charSignR_one_left (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j))))]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have h := gamma_mul_ell s (ZeroStr n)
    rw [hrg] at h
    exact mul_left_cancel₀ hℝ h

/-- Diagonalizes the real quadratic character kernel as a weighted sum of squares of character
sums. -/
private theorem quad_char_identity {n : ℕ} (c : Reg n → ℝ) (φ : Reg n → ℝ) :
    (∑ x : Reg n, ∑ y : Reg n, φ x * φ y *
      ((Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, c z * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y))) =
      (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, c z * (∑ x : Reg n, φ x * charSignR z x) ^ 2 := by
  have hbody : ∀ (x y z : Reg n),
      φ x * φ y * ((Fintype.card (Reg n) : ℝ)⁻¹ * (c z *
        (charSignR z x * charSignR z y))) =
      (Fintype.card (Reg n) : ℝ)⁻¹ * c z *
        ((φ x * charSignR z x) * (φ y * charSignR z y)) := fun _ _ _ => by ring
  have step1 : (∑ x : Reg n, ∑ y : Reg n, φ x * φ y *
      ((Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, c z * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y))) =
      ∑ x : Reg n, ∑ y : Reg n, ∑ z : Reg n,
        φ x * φ y * ((Fintype.card (Reg n) : ℝ)⁻¹ *
          (c z * (charSignR z x * charSignR z y))) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [← charSignR_mul z x y]
  have step2 : (∑ x : Reg n, ∑ y : Reg n, ∑ z : Reg n,
      φ x * φ y * ((Fintype.card (Reg n) : ℝ)⁻¹ *
        (c z * (charSignR z x * charSignR z y)))) =
      ∑ z : Reg n, ∑ x : Reg n, ∑ y : Reg n,
        φ x * φ y * ((Fintype.card (Reg n) : ℝ)⁻¹ *
          (c z * (charSignR z x * charSignR z y))) :=
    (sum_comm3 (fun z x y =>
      φ x * φ y * ((Fintype.card (Reg n) : ℝ)⁻¹ *
        (c z * (charSignR z x * charSignR z y))))).symm
  rw [step1, step2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hpull : ∀ (K : ℝ) (f g : Reg n → ℝ),
      (∑ x : Reg n, ∑ y : Reg n, K * (f x * g y)) =
        K * ((∑ x : Reg n, f x) * (∑ y : Reg n, g y)) := by
    intro K f g
    have inner : ∀ x : Reg n,
        (∑ y : Reg n, K * (f x * g y)) = f x * (K * ∑ y : Reg n, g y) := by
      intro x
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => inner x), ← Finset.sum_mul]
    ring
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hbody x y z))]
  rw [hpull ((Fintype.card (Reg n) : ℝ)⁻¹ * c z)
      (fun x => φ x * charSignR z x) (fun y => φ y * charSignR z y), pow_two]
  ring

section EntryDefs

private noncomputable def pAll {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n) (z : Reg n) : ℝ :=
  1 - Real.exp (-(κ * gammaOfMultiset n ℓ s z)) / 2

private noncomputable def pExp {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n) (z : Reg n) : ℝ :=
  if z = ZeroStr n then 0 else pAll κ s z

private noncomputable def quadEntry {n : ℕ} (c : Reg n → ℝ) (x y : Reg n) : ℝ :=
  (Fintype.card (Reg n) : ℝ)⁻¹ * ∑ z : Reg n, c z * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y)

private noncomputable def aCoeff {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n) (z : Reg n) : ℝ :=
  1 / 2 + κ / 2 * gammaOfMultiset n ℓ s z - κ ^ 2 / 4 * gammaOfMultiset n ℓ s z ^ 2

private noncomputable def bCoeff {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n) (z : Reg n) : ℝ :=
  1 / 2 + κ / 2 * gammaOfMultiset n ℓ s z

private noncomputable def aEntry {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n) (x y : Reg n) : ℝ :=
  (if Qatlib.Concepts.WalshMoment.Forrelation.regXor x y = ZeroStr n then 1 / 2 else 0) +
    (κ / (2 * ℓ)) * (pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) : ℝ) -
    (κ ^ 2 / (4 * ℓ ^ 2)) * (quadCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) : ℝ)

private noncomputable def bEntry {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n) (x y : Reg n) : ℝ :=
  (if Qatlib.Concepts.WalshMoment.Forrelation.regXor x y = ZeroStr n then 1 / 2 else 0) +
    (κ / (2 * ℓ)) * (pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) : ℝ)

/-- The register cardinality is positive as a real number. -/
private theorem card_reg_pos (n : ℕ) : (0 : ℝ) < (Fintype.card (Reg n) : ℝ) := by
  have h : ((Fintype.card (Reg n) : ℝ)) = ((2 : ℝ)) ^ n := by
    rw [card_reg, Nat.cast_pow, Nat.cast_two]
  rw [h]
  positivity

/-- The real register cardinality is nonzero. -/
private theorem card_reg_ne_zero (n : ℕ) : ((Fintype.card (Reg n) : ℝ)) ≠ 0 :=
  ne_of_gt (card_reg_pos n)

/-- The real coercion of a nonzero natural number is nonzero. -/
private theorem cast_ℓ_ne_zero {ℓ : ℕ} (hℓ : ℓ ≠ 0) : ((ℓ : ℝ)) ≠ 0 :=
  Nat.cast_ne_zero.mpr hℓ

/-- Expresses the quadratic form of `quadEntry` as a normalized weighted sum of squared
character sums. -/
private theorem quad_diff_eq {n : ℕ} (c : Reg n → ℝ) (φ : Reg n → ℝ) :
    (∑ x : Reg n, ∑ y : Reg n, φ x * φ y * quadEntry c x y) =
      (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, c z * (∑ x : Reg n, φ x * charSignR z x) ^ 2 :=
  quad_char_identity c φ

/-- Pointwise equal kernels give equal quadratic sums against the same function. -/
private theorem quad_sum_congr' {n : ℕ} (f g : Reg n → Reg n → ℝ) (φ : Reg n → ℝ)
    (h : ∀ x y, f x y = g x y) :
    (∑ x : Reg n, ∑ y : Reg n, φ x * φ y * f x y) =
      (∑ x : Reg n, ∑ y : Reg n, φ x * φ y * g x y) :=
  Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [h x y]

/-- The quadratic sum of a difference of kernels is the difference of their quadratic sums. -/
private theorem quad_sub_split {n : ℕ} (c d : Reg n → ℝ) (φ : Reg n → ℝ) :
    (∑ x : Reg n, ∑ y : Reg n,
        φ x * φ y * (quadEntry c x y - quadEntry d x y)) =
      (∑ x : Reg n, ∑ y : Reg n, φ x * φ y * quadEntry c x y) -
        (∑ x : Reg n, ∑ y : Reg n, φ x * φ y * quadEntry d x y) := by
  have e1 : ∀ x : Reg n,
      (∑ y : Reg n, φ x * φ y * (quadEntry c x y - quadEntry d x y)) =
        (∑ y : Reg n, φ x * φ y * quadEntry c x y) -
          (∑ y : Reg n, φ x * φ y * quadEntry d x y) := by
    intro x
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => mul_sub _ _ _
  calc (∑ x : Reg n, ∑ y : Reg n,
        φ x * φ y * (quadEntry c x y - quadEntry d x y))
      = ∑ x : Reg n, ((∑ y : Reg n, φ x * φ y * quadEntry c x y) -
          (∑ y : Reg n, φ x * φ y * quadEntry d x y)) :=
        Finset.sum_congr rfl fun x _ => e1 x
    _ = (∑ x : Reg n, ∑ y : Reg n, φ x * φ y * quadEntry c x y) -
          (∑ x : Reg n, ∑ y : Reg n, φ x * φ y * quadEntry d x y) := by
        rw [Finset.sum_sub_distrib]

/-- The kernel `quadEntry` preserves pointwise addition of coefficients. -/
private theorem quadEntry_add {n : ℕ} (c d : Reg n → ℝ) (x y : Reg n) :
    quadEntry (fun z => c z + d z) x y = quadEntry c x y + quadEntry d x y := by
  unfold quadEntry
  rw [show ∑ z : Reg n, (c z + d z) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) =
      (∑ z : Reg n, c z * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y)) +
        (∑ z : Reg n, d z * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y)) from by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => add_mul (c z) (d z) _]
  rw [mul_add]

/-- The kernel `quadEntry` preserves pointwise subtraction of coefficients. -/
private theorem quadEntry_sub {n : ℕ} (c d : Reg n → ℝ) (x y : Reg n) :
    quadEntry (fun z => c z - d z) x y = quadEntry c x y - quadEntry d x y := by
  unfold quadEntry
  rw [show ∑ z : Reg n, (c z - d z) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) =
      (∑ z : Reg n, c z * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y)) -
        (∑ z : Reg n, d z * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y)) from by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => sub_mul (c z) (d z) _]
  rw [mul_sub]

/-- For nonzero multiset length, the normalized character transform of `gammaOfMultiset` equals
`pairCount` divided by that length. -/
private theorem invN_sum_gamma_mul_sign {n ℓ : ℕ} (hℓ : ℓ ≠ 0) (s : Fin ℓ → Reg n)
    (w : Reg n) :
    (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, gammaOfMultiset n ℓ s z * charSignR z w =
      (pairCount s w : ℝ) / (ℓ : ℝ) := by
  have hN := card_reg_ne_zero n
  have hℝ := cast_ℓ_ne_zero hℓ
  have hγ : ∀ z : Reg n,
      gammaOfMultiset n ℓ s z = rawGamma s z / (ℓ : ℝ) := by
    intro z
    have h := gamma_mul_ell s z
    rw [eq_div_iff (cast_ℓ_ne_zero hℓ), mul_comm]
    exact h
  have hrew : ∑ z : Reg n, gammaOfMultiset n ℓ s z * charSignR z w =
      ((Fintype.card (Reg n) : ℝ) * (pairCount s w : ℝ)) / (ℓ : ℝ) := by
    rw [Finset.sum_congr rfl (fun z (_ : z ∈ Finset.univ) => by
        rw [hγ z, div_mul_eq_mul_div]),
      ← Finset.sum_div, sum_rawGamma_mul_sign]
  rw [hrew]
  field_simp

/-- For nonzero multiset length, the normalized character transform of squared `gammaOfMultiset`
equals `quadCount` divided by the squared length. -/
private theorem invN_sum_gamma_sq_mul_sign {n ℓ : ℕ} (hℓ : ℓ ≠ 0) (s : Fin ℓ → Reg n)
    (w : Reg n) :
    (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, gammaOfMultiset n ℓ s z ^ 2 * charSignR z w =
      (quadCount s w : ℝ) / ((ℓ : ℝ) ^ 2) := by
  have hN := card_reg_ne_zero n
  have hℝ := cast_ℓ_ne_zero hℓ
  have hγ1 : ∀ z : Reg n,
      gammaOfMultiset n ℓ s z = rawGamma s z / (ℓ : ℝ) := by
    intro z
    have h := gamma_mul_ell s z
    rw [eq_div_iff (cast_ℓ_ne_zero hℓ), mul_comm]
    exact h
  have hγ : ∀ z : Reg n,
      gammaOfMultiset n ℓ s z ^ 2 = rawGamma s z ^ 2 / ((ℓ : ℝ) ^ 2) := by
    intro z
    rw [hγ1 z, div_pow]
  have hsq : ∑ z : Reg n, rawGamma s z ^ 2 * charSignR z w =
      ∑ z : Reg n, rawGamma s z * rawGamma s z * charSignR z w :=
    Finset.sum_congr rfl fun z (_ : z ∈ Finset.univ) => by rw [pow_two]
  have hrew : ∑ z : Reg n, gammaOfMultiset n ℓ s z ^ 2 * charSignR z w =
      ((Fintype.card (Reg n) : ℝ) * (quadCount s w : ℝ)) / ((ℓ : ℝ) ^ 2) := by
    rw [Finset.sum_congr rfl (fun z (_ : z ∈ Finset.univ) => by
        rw [hγ z, div_mul_eq_mul_div]),
      ← Finset.sum_div, hsq, sum_rawGamma_sq_mul_sign]
  rw [hrew]
  field_simp

/-- The constant coefficient one half gives a diagonal `quadEntry` kernel with diagonal value
one half. -/
private theorem quadEntry_half_eq {n : ℕ} (x y : Reg n) :
    quadEntry (fun _ => 1 / 2) x y = if Qatlib.Concepts.WalshMoment.Forrelation.regXor x y = ZeroStr n then 1 / 2 else 0 := by
  unfold quadEntry
  have h : ∑ z : Reg n, (1 / 2) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y)
      = (1 / 2) * ∑ z : Reg n, charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) := by
    rw [Finset.mul_sum]
  rw [h, charSum_eq]
  by_cases hw : Qatlib.Concepts.WalshMoment.Forrelation.regXor x y = ZeroStr n
  · rw [ite_eq_left hw, ite_eq_left hw]
    field_simp
  · rw [ite_eq_right hw, ite_eq_right hw]
    ring

/-- A constant scalar factor can be pulled out of `quadEntry`. -/
private theorem quadEntry_const_mul {n : ℕ} (k : ℝ) (c : Reg n → ℝ) (x y : Reg n) :
    quadEntry (fun z => k * c z) x y = k * quadEntry c x y := by
  unfold quadEntry
  have h : ∑ z : Reg n, (k * c z) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y)
      = k * ∑ z : Reg n, c z * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [h]
  ring

/-- Computes `quadEntry` for half the parameter times `gammaOfMultiset` using `pairCount`. -/
private theorem quadEntry_gamma_two_terms {n ℓ : ℕ} (hℓ : ℓ ≠ 0) (κ : ℝ) (s : Fin ℓ → Reg n)
    (x y : Reg n) :
    quadEntry (fun z => κ / 2 * gammaOfMultiset n ℓ s z) x y =
      κ / (2 * ℓ) * (pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) : ℝ) := by
  rw [quadEntry_const_mul]
  have h := invN_sum_gamma_mul_sign hℓ s (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y)
  unfold quadEntry
  rw [h]
  field_simp

/-- Computes `quadEntry` for one quarter of the squared parameter times squared
`gammaOfMultiset` using `quadCount`. -/
private theorem quadEntry_gamma_sq_term {n ℓ : ℕ} (hℓ : ℓ ≠ 0) (κ : ℝ) (s : Fin ℓ → Reg n)
    (x y : Reg n) :
    quadEntry (fun z => κ ^ 2 / 4 * gammaOfMultiset n ℓ s z ^ 2) x y =
      κ ^ 2 / (4 * ((ℓ : ℝ) ^ 2)) * (quadCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) : ℝ) := by
  rw [quadEntry_const_mul]
  have h := invN_sum_gamma_sq_mul_sign hℓ s (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y)
  unfold quadEntry
  rw [h]
  field_simp

/-- The kernel obtained from `aCoeff` is `aEntry` when the multiset length is nonzero. -/
private theorem quadEntry_aCoeff_eq {n ℓ : ℕ} (hℓ : ℓ ≠ 0) (κ : ℝ) (s : Fin ℓ → Reg n)
    (x y : Reg n) :
    quadEntry (aCoeff κ s) x y = aEntry κ s x y := by
  have hsplit : quadEntry (aCoeff κ s) x y =
      quadEntry (fun _ => 1 / 2) x y +
        (quadEntry (fun z => κ / 2 * gammaOfMultiset n ℓ s z) x y -
          quadEntry (fun z => κ ^ 2 / 4 * gammaOfMultiset n ℓ s z ^ 2) x y) := by
    have hfun : (aCoeff κ s) = fun z => (1 / 2) +
        (κ / 2 * gammaOfMultiset n ℓ s z - κ ^ 2 / 4 * gammaOfMultiset n ℓ s z ^ 2) := by
      funext z
      unfold aCoeff
      ring
    rw [hfun, quadEntry_add, quadEntry_sub]
  rw [hsplit, quadEntry_half_eq, quadEntry_gamma_two_terms hℓ, quadEntry_gamma_sq_term hℓ]
  unfold aEntry
  ring

/-- The kernel obtained from `bCoeff` is `bEntry` when the multiset length is nonzero. -/
private theorem quadEntry_bCoeff_eq {n ℓ : ℕ} (hℓ : ℓ ≠ 0) (κ : ℝ) (s : Fin ℓ → Reg n)
    (x y : Reg n) :
    quadEntry (bCoeff κ s) x y = bEntry κ s x y := by
  have hsplit : quadEntry (bCoeff κ s) x y =
      quadEntry (fun _ => 1 / 2) x y +
        quadEntry (fun z => κ / 2 * gammaOfMultiset n ℓ s z) x y := by
    have hfun : (bCoeff κ s) = fun z => (1 / 2) + κ / 2 * gammaOfMultiset n ℓ s z := by
      funext z
      unfold bCoeff
      ring
    rw [hfun, quadEntry_add]
  rw [hsplit, quadEntry_half_eq, quadEntry_gamma_two_terms hℓ]
  unfold bEntry
  ring

/-- For a nonnegative parameter, `pAll` lies between `aCoeff` and `bCoeff` pointwise. -/
private theorem aCoeff_le_pAll_le_bCoeff {n ℓ : ℕ} (κ : ℝ) (hκ : 0 ≤ κ)
    (s : Fin ℓ → Reg n) (z : Reg n) :
    aCoeff κ s z ≤ pAll κ s z ∧ pAll κ s z ≤ bCoeff κ s z := by
  have hg : 0 ≤ κ * gammaOfMultiset n ℓ s z :=
    mul_nonneg hκ (gammaOfMultiset_nonneg n ℓ s z)
  constructor
  · have hlow := sub_sq_half_le_one_sub_exp hg
    unfold aCoeff pAll
    have h3 : κ / 2 * gammaOfMultiset n ℓ s z
        = (κ * gammaOfMultiset n ℓ s z) / 2 := by ring
    have h2 : κ ^ 2 / 4 * gammaOfMultiset n ℓ s z ^ 2
        = (κ * gammaOfMultiset n ℓ s z) ^ 2 / 4 := by ring
    rw [h3, h2]
    linarith
  · have hup := one_sub_exp_le hg
    unfold bCoeff pAll
    have h3 : κ / 2 * gammaOfMultiset n ℓ s z
        = (κ * gammaOfMultiset n ℓ s z) / 2 := by ring
    rw [h3]
    linarith

/-- Under the stated nonnegativity and nonzero-length assumptions, the quadratic form of
`aEntry` is bounded above by that of `quadEntry` applied to `pAll`. -/
private theorem quad_aEntry_le_pAll {n ℓ : ℕ} (κ : ℝ) (hκ : 0 ≤ κ) (hℓ : ℓ ≠ 0)
    (s : Fin ℓ → Reg n) (φ : Reg n → ℝ) :
    (∑ x : Reg n, ∑ y : Reg n, φ x * φ y * aEntry κ s x y) ≤
      ∑ x : Reg n, ∑ y : Reg n, φ x * φ y * quadEntry (pAll κ s) x y := by
  rw [quad_sum_congr' (aEntry κ s) (quadEntry (aCoeff κ s)) φ
    (fun x y => (quadEntry_aCoeff_eq hℓ κ s x y).symm)]
  have hcoef : ∀ z : Reg n, aCoeff κ s z - pAll κ s z ≤ 0 :=
    fun z => sub_nonpos.mpr (aCoeff_le_pAll_le_bCoeff κ hκ s z).1
  have hdiff : (∑ x : Reg n, ∑ y : Reg n,
      φ x * φ y * (quadEntry (aCoeff κ s) x y - quadEntry (pAll κ s) x y)) =
      (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, (aCoeff κ s z - pAll κ s z) *
          (∑ x : Reg n, φ x * charSignR z x) ^ 2 := by
    have hcomb : ∀ x y : Reg n,
        φ x * φ y * (quadEntry (aCoeff κ s) x y - quadEntry (pAll κ s) x y) =
        φ x * φ y * quadEntry (fun z => aCoeff κ s z - pAll κ s z) x y := by
      intro x y
      rw [quadEntry_sub]
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hcomb x y))]
    exact quad_diff_eq _ φ
  have hsum : ∑ z : Reg n, (aCoeff κ s z - pAll κ s z) *
      (∑ x : Reg n, φ x * charSignR z x) ^ 2 ≤ 0 :=
    Finset.sum_nonpos (fun z _ => mul_nonpos_of_nonpos_of_nonneg (hcoef z) (sq_nonneg _))
  have hnonpos : (∑ x : Reg n, ∑ y : Reg n,
      φ x * φ y * (quadEntry (aCoeff κ s) x y - quadEntry (pAll κ s) x y)) ≤ 0 := by
    rw [hdiff]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (card_reg_pos n).le) hsum
  rw [quad_sub_split] at hnonpos
  linarith

/-- Under the stated nonnegativity and nonzero-length assumptions, the quadratic form of
`quadEntry` applied to `pAll` is bounded above by that of `bEntry`. -/
private theorem quad_pAll_le_bEntry {n ℓ : ℕ} (κ : ℝ) (hκ : 0 ≤ κ) (hℓ : ℓ ≠ 0)
    (s : Fin ℓ → Reg n) (φ : Reg n → ℝ) :
    (∑ x : Reg n, ∑ y : Reg n, φ x * φ y * quadEntry (pAll κ s) x y) ≤
      ∑ x : Reg n, ∑ y : Reg n, φ x * φ y * bEntry κ s x y := by
  have hcoef : ∀ z : Reg n, pAll κ s z - bCoeff κ s z ≤ 0 :=
    fun z => sub_nonpos.mpr (aCoeff_le_pAll_le_bCoeff κ hκ s z).2
  have hdiff : (∑ x : Reg n, ∑ y : Reg n,
      φ x * φ y * (quadEntry (pAll κ s) x y - quadEntry (bCoeff κ s) x y)) =
      (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, (pAll κ s z - bCoeff κ s z) *
          (∑ x : Reg n, φ x * charSignR z x) ^ 2 := by
    have hcomb : ∀ x y : Reg n,
        φ x * φ y * (quadEntry (pAll κ s) x y - quadEntry (bCoeff κ s) x y) =
        φ x * φ y * quadEntry (fun z => pAll κ s z - bCoeff κ s z) x y := by
      intro x y
      rw [quadEntry_sub]
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hcomb x y))]
    exact quad_diff_eq _ φ
  have hsum : ∑ z : Reg n, (pAll κ s z - bCoeff κ s z) *
      (∑ x : Reg n, φ x * charSignR z x) ^ 2 ≤ 0 :=
    Finset.sum_nonpos (fun z _ => mul_nonpos_of_nonpos_of_nonneg (hcoef z) (sq_nonneg _))
  have hnonpos : (∑ x : Reg n, ∑ y : Reg n,
      φ x * φ y * (quadEntry (pAll κ s) x y - quadEntry (bCoeff κ s) x y)) ≤ 0 := by
    rw [hdiff]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (card_reg_pos n).le) hsum
  rw [quad_sub_split] at hnonpos
  have hentry : (∑ x : Reg n, ∑ y : Reg n, φ x * φ y * quadEntry (pAll κ s) x y) ≤
      (∑ x : Reg n, ∑ y : Reg n, φ x * φ y * quadEntry (bCoeff κ s) x y) := by
    linarith
  rw [quad_sum_congr' (quadEntry (bCoeff κ s)) (bEntry κ s) φ
    (fun x y => quadEntry_bCoeff_eq hℓ κ s x y)] at hentry
  exact hentry

/-- The quadratic form for `pExp` equals that for `pAll` minus the contribution of the zero
character. -/
private theorem quad_pExp_eq {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n) (φ : Reg n → ℝ) :
    (∑ x : Reg n, ∑ y : Reg n, φ x * φ y * quadEntry (pExp κ s) x y) =
      (∑ x : Reg n, ∑ y : Reg n, φ x * φ y * quadEntry (pAll κ s) x y) -
        (pAll κ s (ZeroStr n) / (Fintype.card (Reg n) : ℝ)) * (∑ x : Reg n, φ x) ^ 2 := by
  have hdiff : (∑ x : Reg n, ∑ y : Reg n,
      φ x * φ y * (quadEntry (pExp κ s) x y - quadEntry (pAll κ s) x y)) =
      (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, (pExp κ s z - pAll κ s z) *
          (∑ x : Reg n, φ x * charSignR z x) ^ 2 := by
    have hcomb : ∀ x y : Reg n,
        φ x * φ y * (quadEntry (pExp κ s) x y - quadEntry (pAll κ s) x y) =
        φ x * φ y * quadEntry (fun z => pExp κ s z - pAll κ s z) x y := by
      intro x y
      rw [quadEntry_sub]
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hcomb x y))]
    exact quad_diff_eq _ φ
  have hsingle : ∑ z : Reg n, (pExp κ s z - pAll κ s z) *
      (∑ x : Reg n, φ x * charSignR z x) ^ 2 =
      -pAll κ s (ZeroStr n) * (∑ x : Reg n, φ x) ^ 2 := by
    have hz : ∀ z : Reg n, (pExp κ s z - pAll κ s z) *
        (∑ x : Reg n, φ x * charSignR z x) ^ 2 =
        (if z = ZeroStr n then -pAll κ s (ZeroStr n) * (∑ x : Reg n, φ x) ^ 2 else 0) := by
      intro z
      unfold pExp
      by_cases hz0 : z = ZeroStr n
      · subst hz0
        rw [ite_eq_left rfl]
        have hchi : (∑ x : Reg n, φ x * charSignR (ZeroStr n) x) = ∑ x : Reg n, φ x :=
          Finset.sum_congr rfl fun x _ => by rw [charSignR_one_left x, mul_one]
        rw [hchi]
        simp
      · rw [ite_eq_right hz0, ite_eq_right hz0, sub_self, zero_mul]
    rw [Finset.sum_congr rfl (fun z (_ : z ∈ Finset.univ) => hz z)]
    rw [Finset.sum_ite_eq' Finset.univ (ZeroStr n)
      (fun _ => -pAll κ s (ZeroStr n) * (∑ x : Reg n, φ x) ^ 2)]
    simp
  have hkey : (∑ x : Reg n, ∑ y : Reg n, φ x * φ y * quadEntry (pExp κ s) x y) -
      (∑ x : Reg n, ∑ y : Reg n, φ x * φ y * quadEntry (pAll κ s) x y) =
      -(pAll κ s (ZeroStr n) / (Fintype.card (Reg n) : ℝ)) * (∑ x : Reg n, φ x) ^ 2 := by
    rw [← quad_sub_split, hdiff, hsingle]
    rw [div_eq_mul_inv]
    ring
  linarith

end EntryDefs

end TaylorQuad

section Goodness

/-- The Boolean register equivalence sends register XOR to addition. -/
private theorem regBE_xor {n : ℕ} (x y : Reg n) :
    regBooleanEquiv n (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) = regBooleanEquiv n x + regBooleanEquiv n y := by
  funext i
  simp only [regBooleanEquiv_apply, Qatlib.Concepts.WalshMoment.Forrelation.regXor, Pi.add_apply]
  cases hx : x i <;> cases hy : y i <;> simp [hx, hy]; decide

private def xorSet {n ℓ : ℕ} (s : Fin ℓ → Reg n) (O : Finset (Fin ℓ)) : Reg n :=
  (regBooleanEquiv n).symm (∑ i ∈ O, regBooleanEquiv n (s i))

/-- The inverse Boolean register equivalence sends zero to the zero string. -/
private theorem regBE_symm_zero {n : ℕ} : (regBooleanEquiv n).symm 0 = ZeroStr n := by
  rw [← regBooleanEquiv_zeroStr n, Equiv.symm_apply_apply]

/-- The XOR over an empty index set is the zero string. -/
private theorem xorSet_empty {n ℓ : ℕ} (s : Fin ℓ → Reg n) : xorSet s ∅ = ZeroStr n := by
  simp [xorSet, regBE_symm_zero]

/-- Inserting a new index into an XOR set XORs its register value with the previous result. -/
private theorem xorSet_insert {n ℓ : ℕ} (s : Fin ℓ → Reg n) (i : Fin ℓ) {O : Finset (Fin ℓ)}
    (hi : i ∉ O) : xorSet s (insert i O) = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (xorSet s O) := by
  apply (regBooleanEquiv n).injective
  simp only [xorSet]
  rw [Finset.sum_insert hi, regBE_xor]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The XOR set of two distinct indices equals the XOR of their register values. -/
private theorem xorSet_pair {n ℓ : ℕ} (s : Fin ℓ → Reg n) (i j : Fin ℓ) (hij : i ≠ j) :
    xorSet s (Finset.cons i (Finset.cons j ∅ (Finset.notMem_empty j))
        (by simp [hij])) = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) := by
  apply (regBooleanEquiv n).injective
  simp only [xorSet]
  rw [Finset.sum_cons, Finset.sum_cons, Finset.sum_empty, add_zero, regBE_xor,
    Equiv.apply_symm_apply]

private def StrongGood {n ℓ : ℕ} (s : Fin ℓ → Reg n) : Prop :=
  ∀ O : Finset (Fin ℓ), 0 < O.card → O.card ≤ 6 → xorSet s O ≠ ZeroStr n

/-- A sequence satisfying `StrongGood` is injective. -/
private theorem strongGood_injective {n ℓ : ℕ} (s : Fin ℓ → Reg n) (hgood : StrongGood s) :
    Function.Injective s := by
  intro i j hij
  by_cases h : i = j
  · exact h
  · exfalso
    refine hgood (Finset.cons i (Finset.cons j ∅ (Finset.notMem_empty j))
      (by simp [h])) (by rw [Finset.card_cons, Finset.card_cons]; simp)
      (by rw [Finset.card_cons, Finset.card_cons]; simp) ?_
    rw [xorSet_pair s i j h, ← hij]
    simp []

/-- The support of a sequence satisfying `StrongGood` has cardinality equal to its length. -/
private theorem strongGood_supportCard {n ℓ : ℕ} (s : Fin ℓ → Reg n) (hgood : StrongGood s) :
    supportCard (multisetInd s) = ℓ := by
  have hinj := strongGood_injective s hgood
  unfold supportCard multisetInd
  have himg : (Finset.univ.filter fun x : Reg n => decide (∃ i, s i = x))
      = Finset.univ.image s := by
    ext x
    simp
  rw [himg, Finset.card_image_of_injOn (fun a _ b _ hab => hinj hab)]
  simp

/-- For an injective sequence, `pairCount` at zero equals the sequence length. -/
private theorem pairCount_zero_of_injective {n ℓ : ℕ} (s : Fin ℓ → Reg n)
    (hinj : Function.Injective s) : pairCount s (ZeroStr n) = ℓ := by
  unfold pairCount
  have h : ∀ i j : Fin ℓ,
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = ZeroStr n then 1 else 0) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp []
    · rw [ite_eq_right (fun hcon => hij (hinj ((regXor_eq_zero _ _).mp hcon))), ite_eq_right hij]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h i j))]
  simp

/-- Two pairs with equal XOR and equal first entries have equal second entries. -/
private theorem pair_match {n : ℕ} (x y z t w : Reg n) (hxy : Qatlib.Concepts.WalshMoment.Forrelation.regXor x y = w)
    (hzt : Qatlib.Concepts.WalshMoment.Forrelation.regXor z t = w) (hxz : z = x) : t = y := by
  apply (regBooleanEquiv n).injective
  have e1 : regBooleanEquiv n x + regBooleanEquiv n y = regBooleanEquiv n w := by
    rw [← regBE_xor, hxy]
  have e2 : regBooleanEquiv n z + regBooleanEquiv n t = regBooleanEquiv n w := by
    rw [← regBE_xor, hzt]
  rw [hxz] at e2
  exact add_left_cancel (e2.trans e1.symm)

/-- Two pairs with equal XOR and equal second entries have equal first entries. -/
private theorem pair_match' {n : ℕ} (x y z t w : Reg n) (hxy : Qatlib.Concepts.WalshMoment.Forrelation.regXor x y = w)
    (hzt : Qatlib.Concepts.WalshMoment.Forrelation.regXor z t = w) (hyt : t = y) : x = z := by
  have hc1 : Qatlib.Concepts.WalshMoment.Forrelation.regXor y x = w := by rw [regXor_comm]; exact hxy
  have hc2 : Qatlib.Concepts.WalshMoment.Forrelation.regXor t z = w := by rw [regXor_comm]; exact hzt
  rw [hyt] at hc2
  exact (pair_match y x y z w hc1 hc2 rfl).symm

/-- A finite set of cardinality at least three contains three pairwise distinct elements. -/
private theorem exists_three_of_card {α : Type*} [DecidableEq α] {S : Finset α}
    (h : 3 ≤ S.card) :
    ∃ x y z : α, x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hne
  have h2 : (S.erase x).Nonempty := by
    have he := Finset.card_erase_of_mem hx
    exact Finset.card_pos.mp (by omega)
  obtain ⟨y, hy⟩ := h2
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  have h3 : ((S.erase x).erase y).Nonempty := by
    have h1 := Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hyx, (Finset.mem_erase.mp hy).2⟩)
    have h0 := Finset.card_erase_of_mem hx
    exact Finset.card_pos.mp (by omega)
  obtain ⟨z, hz⟩ := h3
  have hzy : z ≠ y := (Finset.mem_erase.mp hz).1
  have hzx : z ≠ x := (Finset.mem_erase.mp ((Finset.mem_erase.mp hz).2)).1
  exact ⟨x, y, z, hx, (Finset.mem_erase.mp hy).2,
    (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2, hyx.symm,
    hzx.symm, hzy.symm⟩

/-- The cardinality of the set of index pairs with prescribed XOR equals `pairCount`. -/
private theorem filter_card_eq_pairCount {n ℓ : ℕ} (s : Fin ℓ → Reg n) (w : Reg n) :
    (Finset.univ.filter fun p : Fin ℓ × Fin ℓ => Qatlib.Concepts.WalshMoment.Forrelation.regXor (s p.1) (s p.2) = w).card
      = pairCount s w := by
  have h1 : (Finset.univ.filter fun p : Fin ℓ × Fin ℓ => Qatlib.Concepts.WalshMoment.Forrelation.regXor (s p.1) (s p.2) = w).card
      = ∑ p ∈ Finset.univ.filter
          (fun p : Fin ℓ × Fin ℓ => Qatlib.Concepts.WalshMoment.Forrelation.regXor (s p.1) (s p.2) = w), 1 := by
    simp
  rw [h1, Finset.sum_filter, Fintype.sum_prod_type]
  unfold pairCount
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by simp

/-- For a sequence satisfying `StrongGood`, any nonzero register has `pairCount` at most two. -/
private theorem pairCount_le_two {n ℓ : ℕ} (s : Fin ℓ → Reg n) (hgood : StrongGood s)
    {w : Reg n} (hw : w ≠ ZeroStr n) : pairCount s w ≤ 2 := by
  have hinj := strongGood_injective s hgood
  by_contra hcon
  push Not at hcon
  have h3c : 3 ≤ (Finset.univ.filter
      fun p : Fin ℓ × Fin ℓ => Qatlib.Concepts.WalshMoment.Forrelation.regXor (s p.1) (s p.2) = w).card := by
    rw [filter_card_eq_pairCount]
    omega
  obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, h12, h13, h23⟩ :=
    exists_three_of_card (α := Fin ℓ × Fin ℓ) h3c
  have hw1 : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s a₁.1) (s a₁.2) = w := by simpa using! (Finset.mem_filter.mp ha₁).2
  have hw2 : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s a₂.1) (s a₂.2) = w := by simpa using! (Finset.mem_filter.mp ha₂).2
  have hw3 : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s a₃.1) (s a₃.2) = w := by simpa using! (Finset.mem_filter.mp ha₃).2
  have hnofix : ∀ p : Fin ℓ × Fin ℓ, Qatlib.Concepts.WalshMoment.Forrelation.regXor (s p.1) (s p.2) = w → p.1 ≠ p.2 := by
    intro p hpw hpp
    rw [hpp, regXor_invol] at hpw
    exact hw hpw.symm
  have hi12 : a₁.1 ≠ a₂.1 := by
    intro h
    exact h12 (Prod.ext h (hinj (pair_match (s a₁.1) (s a₁.2) (s a₂.1) (s a₂.2) w hw1 hw2
      (congrArg s h.symm))).symm)
  have hj12 : a₁.2 ≠ a₂.2 := by
    intro h
    exact h12 (Prod.ext (hinj (pair_match' (s a₁.1) (s a₁.2) (s a₂.1) (s a₂.2) w hw1 hw2
      (congrArg s h).symm)) h)
  by_cases hcol : a₁.1 = a₂.2 ∨ a₂.1 = a₁.2
  · have hsw : a₁.1 = a₂.2 ∧ a₂.1 = a₁.2 := by
      rcases hcol with h | h
      · refine ⟨h, ?_⟩
        have hc : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s a₁.1) (s a₂.1) = w := by
          rw [congrArg s h, regXor_comm]
          exact hw2
        exact hinj (pair_match (s a₁.1) (s a₁.2) (s a₁.1) (s a₂.1) w hw1 hc rfl)
      · refine ⟨?_, h⟩
        have hc : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s a₁.2) (s a₁.1) = w := by
          rw [regXor_comm]
          exact hw1
        exact (hinj (pair_match (s a₁.2) (s a₁.1) (s a₂.1) (s a₂.2) w hc hw2
          (congrArg s h))).symm
    have hx1 : a₃.1 ≠ a₁.1 := by
      intro hh
      exact h13 (Prod.ext hh (hinj (pair_match (s a₁.1) (s a₁.2) (s a₃.1) (s a₃.2) w hw1 hw3
        (congrArg s hh)))).symm
    have hx2 : a₃.1 ≠ a₁.2 := by
      intro hh
      have hh2 : a₃.1 = a₂.1 := hh.trans hsw.2.symm
      exact h23 (Prod.ext hh2 (hinj (pair_match (s a₂.1) (s a₂.2) (s a₃.1)
        (s a₃.2) w hw2 hw3 (congrArg s hh2)))).symm
    have hx3 : a₃.2 ≠ a₁.1 := by
      intro hh
      have hh2 : a₃.2 = a₂.2 := hh.trans hsw.1
      exact h23 (Prod.ext (hinj (pair_match' (s a₃.1) (s a₃.2) (s a₂.1) (s a₂.2) w hw3 hw2
        (congrArg s hh2.symm))) hh2).symm
    have hx4 : a₃.2 ≠ a₁.2 := by
      intro hh
      exact h13 (Prod.ext (hinj (pair_match' (s a₃.1) (s a₃.2) (s a₁.1) (s a₁.2) w hw3 hw1
        (congrArg s hh.symm))) hh).symm
    have hd1 : a₃.2 ∉ (∅ : Finset (Fin ℓ)) := Finset.notMem_empty _
    have hd2 : a₃.1 ∉ insert a₃.2 (∅ : Finset (Fin ℓ)) := by
      simp [hnofix a₃ hw3]
    have e1 : a₁.2 ≠ a₃.1 := fun h => hx2 h.symm
    have e2 : a₁.2 ≠ a₃.2 := fun h => hx4 h.symm
    have e3 : a₁.1 ≠ a₃.1 := fun h => hx1 h.symm
    have e4 : a₁.1 ≠ a₃.2 := fun h => hx3 h.symm
    have hd3 : a₁.2 ∉ insert a₃.1 (insert a₃.2 (∅ : Finset (Fin ℓ))) := by
      simp [Finset.mem_insert, e1, e2]
    have hd4 : a₁.1 ∉ insert a₁.2 (insert a₃.1 (insert a₃.2 (∅ : Finset (Fin ℓ)))) := by
      simp [Finset.mem_insert, e3, e4, hnofix a₁ hw1]
    have hOcard : (insert a₁.1 (insert a₁.2 (insert a₃.1 (insert a₃.2
        (∅ : Finset (Fin ℓ)))))).card = 4 := by
      rw [Finset.card_insert_of_notMem hd4, Finset.card_insert_of_notMem hd3,
        Finset.card_insert_of_notMem hd2, Finset.card_insert_of_notMem hd1]
      simp
    have hOxor : xorSet s (insert a₁.1 (insert a₁.2 (insert a₃.1 (insert a₃.2
        (∅ : Finset (Fin ℓ)))))) = ZeroStr n := by
      rw [xorSet_insert _ _ hd4, xorSet_insert _ _ hd3, xorSet_insert _ _ hd2,
        xorSet_insert _ _ hd1, xorSet_empty s, regXor_zero_right, hw3, regXor_assoc,
        ← hw1, regXor_invol]
    exact absurd hOxor (hgood _ (by rw [hOcard]; norm_num) (by rw [hOcard]; norm_num))
  · push Not at hcol
    have hd1 : a₂.2 ∉ (∅ : Finset (Fin ℓ)) := Finset.notMem_empty _
    have hd2 : a₂.1 ∉ insert a₂.2 (∅ : Finset (Fin ℓ)) := by
      simp [hnofix a₂ hw2]
    have e1 : a₁.2 ≠ a₂.1 := fun h => hcol.2 h.symm
    have e2 : a₁.1 ≠ a₂.2 := fun h => hcol.1 h
    have hd3 : a₁.2 ∉ insert a₂.1 (insert a₂.2 (∅ : Finset (Fin ℓ))) := by
      simp [Finset.mem_insert, e1, hj12]
    have hd4 : a₁.1 ∉ insert a₁.2 (insert a₂.1 (insert a₂.2 (∅ : Finset (Fin ℓ)))) := by
      simp [Finset.mem_insert, e2, hi12, hnofix a₁ hw1]
    have hOcard : (insert a₁.1 (insert a₁.2 (insert a₂.1 (insert a₂.2
        (∅ : Finset (Fin ℓ)))))).card = 4 := by
      rw [Finset.card_insert_of_notMem hd4, Finset.card_insert_of_notMem hd3,
        Finset.card_insert_of_notMem hd2, Finset.card_insert_of_notMem hd1]
      simp
    have hOxor : xorSet s (insert a₁.1 (insert a₁.2 (insert a₂.1 (insert a₂.2
        (∅ : Finset (Fin ℓ)))))) = ZeroStr n := by
      rw [xorSet_insert _ _ hd4, xorSet_insert _ _ hd3, xorSet_insert _ _ hd2,
        xorSet_insert _ _ hd1, xorSet_empty s, regXor_zero_right, hw2, regXor_assoc,
        ← hw1, regXor_invol]
    exact absurd hOxor (hgood _ (by rw [hOcard]; norm_num) (by rw [hOcard]; norm_num))

end Goodness

section Moments

/-- A vector over `ZMod 2` added to itself is zero. -/
private theorem bv_add_self {n : ℕ} (v : Fin n → ZMod 2) : v + v = 0 := by
  funext i
  exact eq_neg_iff_add_eq_zero.mp (ZMod.neg_eq_self_mod_two (v i)).symm

/-- The XOR of four registers vanishes exactly when the XORs of the two pairs are equal. -/
private theorem xor4_zero_iff_pair {n : ℕ} (a b c d : Reg n) :
    Qatlib.Concepts.WalshMoment.Forrelation.regXor a (Qatlib.Concepts.WalshMoment.Forrelation.regXor b (Qatlib.Concepts.WalshMoment.Forrelation.regXor c d)) = ZeroStr n ↔ Qatlib.Concepts.WalshMoment.Forrelation.regXor c d = Qatlib.Concepts.WalshMoment.Forrelation.regXor a b := by
  constructor
  · intro h
    have hBE : regBooleanEquiv n a + (regBooleanEquiv n b +
        (regBooleanEquiv n c + regBooleanEquiv n d)) = 0 := by
      have h2 : regBooleanEquiv n (Qatlib.Concepts.WalshMoment.Forrelation.regXor a (Qatlib.Concepts.WalshMoment.Forrelation.regXor b (Qatlib.Concepts.WalshMoment.Forrelation.regXor c d))) = 0 := by
        rw [h, regBooleanEquiv_zeroStr]
      rw [regBE_xor, regBE_xor, regBE_xor] at h2
      exact h2
    apply (regBooleanEquiv n).injective
    rw [regBE_xor, regBE_xor]
    have e1 : (regBooleanEquiv n a + regBooleanEquiv n b) +
        (regBooleanEquiv n a + (regBooleanEquiv n b +
          (regBooleanEquiv n c + regBooleanEquiv n d))) =
        regBooleanEquiv n a + regBooleanEquiv n b := by
      rw [hBE, add_zero]
    have e2 : (regBooleanEquiv n a + regBooleanEquiv n b) +
        (regBooleanEquiv n a + (regBooleanEquiv n b +
          (regBooleanEquiv n c + regBooleanEquiv n d))) =
        regBooleanEquiv n c + regBooleanEquiv n d := by
      rw [show (regBooleanEquiv n a + regBooleanEquiv n b) +
          (regBooleanEquiv n a + (regBooleanEquiv n b +
            (regBooleanEquiv n c + regBooleanEquiv n d))) =
          ((regBooleanEquiv n a + regBooleanEquiv n b) +
            (regBooleanEquiv n a + regBooleanEquiv n b)) +
          (regBooleanEquiv n c + regBooleanEquiv n d) from by abel,
        bv_add_self _, zero_add]
    exact e2.symm.trans e1
  · intro h
    have hBE : regBooleanEquiv n c + regBooleanEquiv n d =
        regBooleanEquiv n a + regBooleanEquiv n b := by
      rw [← regBE_xor, ← regBE_xor]
      exact congrArg (regBooleanEquiv n) h
    apply (regBooleanEquiv n).injective
    rw [regBE_xor, regBE_xor, regBE_xor, regBooleanEquiv_zeroStr]
    rw [show regBooleanEquiv n a + (regBooleanEquiv n b +
        (regBooleanEquiv n c + regBooleanEquiv n d)) =
        (regBooleanEquiv n a + regBooleanEquiv n b) +
        (regBooleanEquiv n c + regBooleanEquiv n d) from by abel,
      hBE, bv_add_self _]

/-- Expresses `quadCount` at zero as a sum of pair counts over all index pairs. -/
private theorem quadCount_zero_split {n ℓ : ℕ} (s : Fin ℓ → Reg n) :
    quadCount s (ZeroStr n) = ∑ i, ∑ j, pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) := by
  unfold quadCount pairCount
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases h : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l) = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)
  · rw [ite_eq_left ((xor4_zero_iff_pair (s i) (s j) (s k) (s l)).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hcon => h ((xor4_zero_iff_pair (s i) (s j) (s k) (s l)).mp hcon)),
      ite_eq_right h]

/-- The sum of two distinct terms of a natural-valued function is at most its total finite sum. -/
private theorem two_single_le_sum {α : Type*} [DecidableEq α] [Fintype α] (g : α → ℕ)
    (a b : α) (hab : a ≠ b) : g a + g b ≤ ∑ x, g x := by
  have h1 : ∑ x, g x = g a + ∑ x ∈ (Finset.univ.erase a), g x := by
    have hins : g a + ∑ x ∈ (Finset.univ.erase a), g x = ∑ x, g x := by
      conv_rhs => rw [← Finset.insert_erase (Finset.mem_univ a)]
      rw [Finset.sum_insert (Finset.notMem_erase a Finset.univ)]
    exact hins.symm
  rw [h1]
  have h2 : g b ≤ ∑ x ∈ (Finset.univ.erase a), g x :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩)
  omega

/-- The zero-register pair count is at least the sequence length. -/
private theorem pairCount_zero_ge {n ℓ : ℕ} (s : Fin ℓ → Reg n) :
    ℓ ≤ pairCount s (ZeroStr n) := by
  unfold pairCount
  have h : ∀ i : Fin ℓ, (1 : ℕ) ≤
      ∑ j : Fin ℓ, (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = ZeroStr n then 1 else 0) := by
    intro i
    have hterm : (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s i) = ZeroStr n then (1 : ℕ) else 0) = 1 :=
      ite_eq_left (regXor_invol (s i))
    exact le_trans (le_of_eq hterm.symm)
      (Finset.single_le_sum
        (f := fun j => (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = ZeroStr n then 1 else 0))
        (fun _ _ => by simp) (Finset.mem_univ i))
  calc ℓ = ∑ _i, 1 := by simp
    _ ≤ ∑ i, ∑ j : Fin ℓ, (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = ZeroStr n then 1 else 0) :=
        Finset.sum_le_sum (fun i _ => h i)

/-- Two distinct indices give a pairwise XOR whose pair count is at least two. -/
private theorem pairCount_ge_two {n ℓ : ℕ} (s : Fin ℓ → Reg n) (i j : Fin ℓ) (hij : i ≠ j) :
    2 ≤ pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) := by
  unfold pairCount
  have hrow : (∑ j' : Fin ℓ, (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j') = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) then 1 else 0)) +
      (∑ j' : Fin ℓ, (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (s j') = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) then 1 else 0)) ≤
      ∑ x, ∑ j' : Fin ℓ, (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s x) (s j') = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) then 1 else 0) :=
    two_single_le_sum
      (g := fun i' => ∑ j' : Fin ℓ,
        (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i') (s j') = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) then 1 else 0)) i j hij
  have h1 : (1 : ℕ) ≤
      ∑ j' : Fin ℓ, (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j') = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) then 1 else 0) := by
    have hterm : (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) then (1 : ℕ) else 0) = 1 :=
      ite_eq_left rfl
    exact le_trans (le_of_eq hterm.symm)
      (Finset.single_le_sum
        (f := fun j' => (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j') = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) then 1 else 0))
        (fun _ _ => by simp) (Finset.mem_univ j))
  have h2 : (1 : ℕ) ≤
      ∑ j' : Fin ℓ, (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (s j') = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) then 1 else 0) := by
    have hterm : (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (s i) = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) then (1 : ℕ) else 0) = 1 := by
      rw [regXor_comm]
      exact ite_eq_left rfl
    exact le_trans (le_of_eq hterm.symm)
      (Finset.single_le_sum
        (f := fun j' => (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (s j') = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) then 1 else 0))
        (fun _ _ => by simp) (Finset.mem_univ i))
  omega

/-- Bounds the zero-register quadruple count below by the sequence length times the length plus
twice its natural predecessor. -/
private theorem quadCount_zero_ge {n ℓ : ℕ} (s : Fin ℓ → Reg n) :
    ℓ * (ℓ + 2 * (ℓ - 1)) ≤ quadCount s (ZeroStr n) := by
  rw [quadCount_zero_split]
  have hrow : ∀ i : Fin ℓ, ℓ + 2 * (ℓ - 1) ≤
      ∑ j, pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) := by
    intro i
    have hsplit : ∑ j, pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) =
        pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s i)) +
          ∑ j ∈ (Finset.univ.erase i), pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) := by
      have hins : pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s i)) +
          ∑ j ∈ (Finset.univ.erase i), pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) =
          ∑ j, pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) := by
        conv_rhs => rw [← Finset.insert_erase (Finset.mem_univ i)]
        rw [Finset.sum_insert (Finset.notMem_erase i Finset.univ)]
      exact hins.symm
    rw [hsplit, regXor_invol]
    have hdiag : ℓ ≤ pairCount s (ZeroStr n) := pairCount_zero_ge s
    have hoff : ∀ j ∈ (Finset.univ.erase i), (2 : ℕ) ≤
        pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) := by
      intro j hj
      exact pairCount_ge_two s i j (Ne.symm (Finset.mem_erase.mp hj).1)
    have hcard : (Finset.univ.erase i : Finset (Fin ℓ)).card = ℓ - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have hoffsum : 2 * (ℓ - 1) ≤
        ∑ j ∈ (Finset.univ.erase i), pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) := by
      calc 2 * (ℓ - 1) = ∑ _j ∈ (Finset.univ.erase i), 2 := by
            rw [Finset.sum_const, hcard, Nat.nsmul_eq_mul, Nat.mul_comm]
        _ ≤ ∑ j ∈ (Finset.univ.erase i), pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) :=
            Finset.sum_le_sum hoff
    omega
  have hconst : ∑ _i : Fin ℓ, (ℓ + 2 * (ℓ - 1)) = ℓ * (ℓ + 2 * (ℓ - 1)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  calc ℓ * (ℓ + 2 * (ℓ - 1)) = ∑ _i : Fin ℓ, (ℓ + 2 * (ℓ - 1)) := hconst.symm
    _ ≤ ∑ i, ∑ j, pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) :=
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)

/-- For a sequence satisfying `StrongGood`, bounds the zero-register quadruple count above by
the sequence length times the length plus twice its natural predecessor. -/
private theorem quadCount_zero_le {n ℓ : ℕ} (s : Fin ℓ → Reg n) (hgood : StrongGood s) :
    quadCount s (ZeroStr n) ≤ ℓ * (ℓ + 2 * (ℓ - 1)) := by
  have hinj := strongGood_injective s hgood
  rw [quadCount_zero_split]
  have hrow : ∀ i : Fin ℓ,
      ∑ j, pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) ≤ ℓ + 2 * (ℓ - 1) := by
    intro i
    have hsplit : ∑ j, pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) =
        pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s i)) +
          ∑ j ∈ (Finset.univ.erase i), pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) := by
      have hins : pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s i)) +
          ∑ j ∈ (Finset.univ.erase i), pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) =
          ∑ j, pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) := by
        conv_rhs => rw [← Finset.insert_erase (Finset.mem_univ i)]
        rw [Finset.sum_insert (Finset.notMem_erase i Finset.univ)]
      exact hins.symm
    rw [hsplit, regXor_invol, pairCount_zero_of_injective s hinj]
    have hoff : ∀ j ∈ (Finset.univ.erase i), pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) ≤ 2 := by
      intro j hj
      have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
      have hw : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) ≠ ZeroStr n := by
        intro hcon
        exact hij (hinj ((regXor_eq_zero _ _).mp hcon))
      exact pairCount_le_two s hgood hw
    have hcard : (Finset.univ.erase i : Finset (Fin ℓ)).card = ℓ - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have hoffsum : ∑ j ∈ (Finset.univ.erase i), pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) ≤ 2 * (ℓ - 1) := by
      calc ∑ j ∈ (Finset.univ.erase i), pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) ≤
            ∑ _j ∈ (Finset.univ.erase i), 2 := Finset.sum_le_sum hoff
        _ = 2 * (ℓ - 1) := by
            rw [Finset.sum_const, hcard, Nat.nsmul_eq_mul, Nat.mul_comm]
    omega
  have hconst : ∑ _i : Fin ℓ, (ℓ + 2 * (ℓ - 1)) = ℓ * (ℓ + 2 * (ℓ - 1)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  calc ∑ i, ∑ j, pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) ≤ ∑ _i : Fin ℓ, (ℓ + 2 * (ℓ - 1)) :=
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
    _ = ℓ * (ℓ + 2 * (ℓ - 1)) := hconst

/-- The character sign with the zero string as its second argument equals one. -/
private theorem charSignR_zero_right {n : ℕ} (z : Reg n) : charSignR z (ZeroStr n) = 1 := by
  rw [charSignR]
  simp [ZeroStr]

/-- For a nonempty injective sequence, the sum of `gammaOfMultiset` equals the register
cardinality. -/
private theorem sum_gamma_eq_card {n ℓ : ℕ} (s : Fin ℓ → Reg n) (hℓ : ℓ ≠ 0)
    (hinj : Function.Injective s) :
    ∑ z : Reg n, gammaOfMultiset n ℓ s z = (Fintype.card (Reg n) : ℝ) := by
  have h1 := sum_rawGamma_mul_sign s (ZeroStr n)
  simp only [charSignR_zero_right, mul_one] at h1
  rw [pairCount_zero_of_injective s hinj] at h1
  have h2 : (ℓ : ℝ) * ∑ z, gammaOfMultiset n ℓ s z = ∑ z, rawGamma s z := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => gamma_mul_ell s z
  rw [← h2] at h1
  have hN : (Fintype.card (Reg n) : ℝ) * (ℓ : ℝ) = (ℓ : ℝ) * (Fintype.card (Reg n) : ℝ) :=
    mul_comm _ _
  rw [hN] at h1
  exact mul_left_cancel₀ ((cast_ℓ_ne_zero hℓ)) h1

/-- For nonzero sequence length, bounds the sum of squared `gammaOfMultiset` below by the
register cardinality times three minus twice the reciprocal length. -/
private theorem sum_gamma_sq_ge {n ℓ : ℕ} (s : Fin ℓ → Reg n) (hℓ : ℓ ≠ 0) :
    (Fintype.card (Reg n) : ℝ) * (3 - 2 / (ℓ : ℝ)) ≤
      ∑ z : Reg n, gammaOfMultiset n ℓ s z ^ 2 := by
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hℓ)
  have h1 : ∑ z : Reg n, rawGamma s z * rawGamma s z =
      (Fintype.card (Reg n) : ℝ) * (quadCount s (ZeroStr n) : ℝ) := by
    have h := sum_rawGamma_sq_mul_sign s (ZeroStr n)
    simp only [charSignR_zero_right, mul_one] at h
    exact h
  have hge : (ℓ : ℝ) * ((ℓ + 2 * (ℓ - 1) : ℕ) : ℝ) ≤ (quadCount s (ZeroStr n) : ℝ) := by
    exact_mod_cast quadCount_zero_ge s
  have h2 : ∑ z : Reg n, gammaOfMultiset n ℓ s z ^ 2 =
      (∑ z : Reg n, rawGamma s z * rawGamma s z) / ((ℓ : ℝ) ^ 2) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hg : rawGamma s z * rawGamma s z =
        ((ℓ : ℝ)) ^ 2 * gammaOfMultiset n ℓ s z ^ 2 := by
      have h3 := gamma_mul_ell s z
      rw [← h3]
      ring
    rw [hg]
    exact (mul_div_cancel_left₀ _
      (show ((ℓ : ℝ) ^ 2) ≠ 0 by positivity)).symm
  rw [h2, h1, le_div_iff₀ (show (0 : ℝ) < (ℓ : ℝ) ^ 2 by positivity), mul_assoc]
  have hid : (3 - 2 / (ℓ : ℝ)) * ((ℓ : ℝ) ^ 2) = (ℓ : ℝ) * ((ℓ + 2 * (ℓ - 1) : ℕ) : ℝ) := by
    have h1le : (1 : ℕ) ≤ ℓ := Nat.pos_of_ne_zero hℓ
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub h1le, Nat.cast_one]
    field_simp
    ring
  rw [hid]
  exact mul_le_mul_of_nonneg_left hge (by positivity)

end Moments

section Peel

/-- The Boolean register equivalence sends an XOR set to the sum of its Boolean register values. -/
private theorem regBE_xorSet {n ℓ : ℕ} (s : Fin ℓ → Reg n) (O : Finset (Fin ℓ)) :
    regBooleanEquiv n (xorSet s O) = ∑ i ∈ O, regBooleanEquiv n (s i) :=
  Equiv.apply_symm_apply _ _

private def symdiff {ℓ : ℕ} (O : Finset (Fin ℓ)) (x : Fin ℓ) : Finset (Fin ℓ) :=
  if x ∈ O then O.erase x else insert x O

/-- Toggling an index in an XOR set XORs the corresponding register with the original XOR set. -/
private theorem xorSet_symdiff {n ℓ : ℕ} (s : Fin ℓ → Reg n) (O : Finset (Fin ℓ)) (x : Fin ℓ) :
    xorSet s (symdiff O x) = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s x) (xorSet s O) := by
  by_cases h : x ∈ O
  · have h1 : xorSet s O = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s x) (xorSet s (O.erase x)) := by
      apply (regBooleanEquiv n).injective
      rw [regBE_xor, regBE_xorSet, regBE_xorSet]
      have hsplit : regBooleanEquiv n (s x) + ∑ i ∈ O.erase x, regBooleanEquiv n (s i)
          = ∑ i ∈ O, regBooleanEquiv n (s i) := by
        conv_rhs => rw [← Finset.insert_erase h]
        rw [Finset.sum_insert (Finset.notMem_erase x O)]
      rw [hsplit]
    unfold symdiff
    rw [ite_eq_left h, h1, regXor_assoc, regXor_invol, regXor_zero_left]
  · unfold symdiff
    rw [ite_eq_right h]
    exact xorSet_insert s x h

/-- Toggling an index distinct from a member of a finite set preserves that membership. -/
private theorem symdiff_mem {ℓ : ℕ} {i x : Fin ℓ} {T : Finset (Fin ℓ)}
    (hi : i ∈ T) (hxi : x ≠ i) : i ∈ symdiff T x := by
  unfold symdiff
  by_cases hx : x ∈ T
  · rw [ite_eq_left hx]
    exact Finset.mem_erase.mpr ⟨Ne.symm hxi, hi⟩
  · rw [ite_eq_right hx]
    exact Finset.mem_insert.mpr (Or.inr hi)

/-- Toggling one index increases finite-set cardinality by at most one. -/
private theorem symdiff_card {ℓ : ℕ} (T : Finset (Fin ℓ)) (x : Fin ℓ) :
    (symdiff T x).card ≤ T.card + 1 := by
  unfold symdiff
  by_cases hx : x ∈ T
  · rw [ite_eq_left hx]
    have := Finset.card_erase_of_mem hx
    omega
  · rw [ite_eq_right hx, Finset.card_insert_of_notMem hx]

/-- The XOR of six registers vanishes exactly when the corresponding sum of Boolean register
vectors is zero. -/
private theorem xor6_zero_iff_BE {n : ℕ} (a b c d e f : Reg n) :
    Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor a b) (Qatlib.Concepts.WalshMoment.Forrelation.regXor c d)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor e f) = ZeroStr n ↔
      ((regBooleanEquiv n a + regBooleanEquiv n b) +
        ((regBooleanEquiv n c + regBooleanEquiv n d) +
          (regBooleanEquiv n e + regBooleanEquiv n f))) = 0 := by
  constructor
  · intro h
    have h2 : regBooleanEquiv n
        (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor a b) (Qatlib.Concepts.WalshMoment.Forrelation.regXor c d)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor e f)) = 0 := by
      rw [h, regBooleanEquiv_zeroStr]
    rw [regBE_xor, regBE_xor, regBE_xor, regBE_xor, regBE_xor] at h2
    have hac : (regBooleanEquiv n a + regBooleanEquiv n b) +
        ((regBooleanEquiv n c + regBooleanEquiv n d) +
          (regBooleanEquiv n e + regBooleanEquiv n f)) =
        regBooleanEquiv n a + regBooleanEquiv n b +
        (regBooleanEquiv n c + regBooleanEquiv n d) +
        (regBooleanEquiv n e + regBooleanEquiv n f) := by abel
    rw [hac]
    exact h2
  · intro h
    apply (regBooleanEquiv n).injective
    rw [regBE_xor, regBE_xor, regBE_xor, regBE_xor, regBE_xor, regBooleanEquiv_zeroStr]
    have hac : regBooleanEquiv n a + regBooleanEquiv n b +
        (regBooleanEquiv n c + regBooleanEquiv n d) +
        (regBooleanEquiv n e + regBooleanEquiv n f) =
        (regBooleanEquiv n a + regBooleanEquiv n b) +
        ((regBooleanEquiv n c + regBooleanEquiv n d) +
          (regBooleanEquiv n e + regBooleanEquiv n f)) := by abel
    rw [hac]
    exact h

/-- For a sequence satisfying `StrongGood`, a vanishing XOR of six indexed values forces the
first index to equal one of the other five. -/
private theorem peel_disj {n ℓ : ℕ} (s : Fin ℓ → Reg n) (hgood : StrongGood s)
    (i j k l m o : Fin ℓ)
    (h : Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
        = ZeroStr n) :
    i = j ∨ i = k ∨ i = l ∨ i = m ∨ i = o := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne1, hne2, hne3, hne4, hne5⟩ := hcon
  obtain ⟨T1, hT1, hm1, hc1, hx1⟩ : ∃ T1 : Finset (Fin ℓ),
      T1 = insert i (∅ : Finset (Fin ℓ)) ∧ i ∈ T1 ∧ T1.card = 1 ∧
        xorSet s T1 = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (xorSet s ∅) := by
    refine ⟨insert i ∅, rfl, Finset.mem_insert_self i ∅, by simp, ?_⟩
    rw [xorSet_insert s i (Finset.notMem_empty i)]
  obtain ⟨T2, hT2, hm2, hx2⟩ : ∃ T2 : Finset (Fin ℓ),
      T2 = symdiff T1 j ∧ i ∈ T2 ∧ xorSet s T2 = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (xorSet s T1) :=
    ⟨symdiff T1 j, rfl, symdiff_mem hm1 (Ne.symm hne1), xorSet_symdiff s T1 j⟩
  obtain ⟨T3, hT3, hm3, hx3⟩ : ∃ T3 : Finset (Fin ℓ),
      T3 = symdiff T2 k ∧ i ∈ T3 ∧ xorSet s T3 = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (xorSet s T2) :=
    ⟨symdiff T2 k, rfl, symdiff_mem hm2 (Ne.symm hne2), xorSet_symdiff s T2 k⟩
  obtain ⟨T4, hT4, hm4, hx4⟩ : ∃ T4 : Finset (Fin ℓ),
      T4 = symdiff T3 l ∧ i ∈ T4 ∧ xorSet s T4 = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s l) (xorSet s T3) :=
    ⟨symdiff T3 l, rfl, symdiff_mem hm3 (Ne.symm hne3), xorSet_symdiff s T3 l⟩
  obtain ⟨T5, hT5, hm5, hx5⟩ : ∃ T5 : Finset (Fin ℓ),
      T5 = symdiff T4 m ∧ i ∈ T5 ∧ xorSet s T5 = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (xorSet s T4) :=
    ⟨symdiff T4 m, rfl, symdiff_mem hm4 (Ne.symm hne4), xorSet_symdiff s T4 m⟩
  obtain ⟨T6, hT6, hm6, hx6⟩ : ∃ T6 : Finset (Fin ℓ),
      T6 = symdiff T5 o ∧ i ∈ T6 ∧ xorSet s T6 = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s o) (xorSet s T5) :=
    ⟨symdiff T5 o, rfl, symdiff_mem hm5 (Ne.symm hne5), xorSet_symdiff s T5 o⟩
  have hc2 : T2.card ≤ T1.card + 1 := by rw [hT2]; exact symdiff_card T1 j
  have hc3 : T3.card ≤ T2.card + 1 := by rw [hT3]; exact symdiff_card T2 k
  have hc4 : T4.card ≤ T3.card + 1 := by rw [hT4]; exact symdiff_card T3 l
  have hc5 : T5.card ≤ T4.card + 1 := by rw [hT5]; exact symdiff_card T4 m
  have hc6 : T6.card ≤ T5.card + 1 := by rw [hT6]; exact symdiff_card T5 o
  have hcard : T6.card ≤ 6 := by omega
  have hzero : xorSet s T6 = ZeroStr n := by
    rw [hx6, hx5, hx4, hx3, hx2, hx1, xorSet_empty s, regXor_zero_right]
    apply (regBooleanEquiv n).injective
    rw [regBooleanEquiv_zeroStr, regBE_xor, regBE_xor, regBE_xor, regBE_xor, regBE_xor]
    have hBE : (regBooleanEquiv n (s i) + regBooleanEquiv n (s j)) +
        ((regBooleanEquiv n (s k) + regBooleanEquiv n (s l)) +
          (regBooleanEquiv n (s m) + regBooleanEquiv n (s o))) = 0 :=
      (xor6_zero_iff_BE (s i) (s j) (s k) (s l) (s m) (s o)).mp h
    have hac : regBooleanEquiv n (s o) + (regBooleanEquiv n (s m) +
        (regBooleanEquiv n (s l) + (regBooleanEquiv n (s k) +
          (regBooleanEquiv n (s j) + regBooleanEquiv n (s i))))) =
        (regBooleanEquiv n (s i) + regBooleanEquiv n (s j)) +
        ((regBooleanEquiv n (s k) + regBooleanEquiv n (s l)) +
          (regBooleanEquiv n (s m) + regBooleanEquiv n (s o))) := by abel
    rw [hac]
    exact hBE
  exact hgood T6 (Finset.card_pos.mpr ⟨i, hm6⟩) hcard hzero

/-- Sequences agreeing on an index set have equal XORs over that set. -/
private theorem xorSet_congr {n ℓ : ℕ} (T : Finset (Fin ℓ)) (a b : Fin ℓ → Reg n)
    (h : ∀ i ∈ T, a i = b i) : xorSet a T = xorSet b T := by
  apply (regBooleanEquiv n).injective
  rw [regBE_xorSet, regBE_xorSet]
  exact Finset.sum_congr rfl fun i hi => by rw [h i hi]

/-- For a nonempty index set, bounds the number of register sequences whose XOR over that set
vanishes by the total number of sequences divided by the register cardinality. -/
private theorem fiber_card_le {n ℓ : ℕ} (O : Finset (Fin ℓ)) (hO : 0 < O.card) :
    (Finset.univ.filter (fun s : Fin ℓ → Reg n => xorSet s O = ZeroStr n)).card
      * Fintype.card (Reg n) ≤ (Fintype.card (Reg n)) ^ ℓ := by
  classical
  obtain ⟨j₀, hj₀⟩ := Finset.card_pos.mp hO
  have hsplit : ∀ s : Fin ℓ → Reg n, xorSet s O
      = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j₀) (xorSet s (O.erase j₀)) := by
    intro s
    conv_lhs => rw [← Finset.insert_erase hj₀]
    rw [xorSet_insert s j₀ (Finset.notMem_erase j₀ O)]
  have hj : ∀ s ∈ Finset.univ.filter (fun s : Fin ℓ → Reg n => xorSet s O = ZeroStr n),
      s j₀ = xorSet s (O.erase j₀) := by
    intro s hs
    have hx : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j₀) (xorSet s (O.erase j₀)) = ZeroStr n := by
      rw [← hsplit s]
      exact (Finset.mem_filter.mp hs).2
    exact (regXor_eq_zero _ _).mp hx
  have hinj : Function.Injective
    (fun p : ↥((Finset.univ.filter
          (fun s : Fin ℓ → Reg n => xorSet s O = ZeroStr n)) ×ˢ
          (Finset.univ : Finset (Reg n))) => Function.update p.1.1 j₀ p.1.2) := by
    intro ⟨⟨s, v⟩, hmem⟩ ⟨⟨s', v'⟩, hmem'⟩ heq
    have hoff : ∀ i : Fin ℓ, i ≠ j₀ → s i = s' i := by
      intro i hi
      have h := congrFun heq i
      simp [Function.update, hi] at h
      exact h
    have hvv : v = v' := by
      have h := congrFun heq j₀
      simp [Function.update] at h
      exact h
    have hs : s ∈ Finset.univ.filter
        (fun s : Fin ℓ → Reg n => xorSet s O = ZeroStr n) := (Finset.mem_product.mp hmem).1
    have hs' : s' ∈ Finset.univ.filter
        (fun s : Fin ℓ → Reg n => xorSet s O = ZeroStr n) := (Finset.mem_product.mp hmem').1
    have hagree : s j₀ = s' j₀ := by
      rw [hj s hs, hj s' hs']
      exact xorSet_congr (O.erase j₀) s s'
        (fun i hi => hoff i (Finset.ne_of_mem_erase hi))
    refine Subtype.ext (Prod.ext_iff.mpr ⟨funext fun i => ?_, hvv⟩)
    by_cases hi : i = j₀
    · subst hi
      exact hagree
    · exact hoff i hi
  have hcardprod : (Finset.univ.filter
        (fun s : Fin ℓ → Reg n => xorSet s O = ZeroStr n)).card
      * Fintype.card (Reg n)
      = Fintype.card ↥((Finset.univ.filter
          (fun s : Fin ℓ → Reg n => xorSet s O = ZeroStr n)) ×ˢ
          (Finset.univ : Finset (Reg n))) := by
    rw [Fintype.card_coe, Finset.card_product, Finset.card_univ]
  rw [hcardprod]
  refine le_trans (Fintype.card_le_of_injective _ hinj) ?_
  rw [Fintype.card_pi_const]

/-- The number of nonempty index subsets of cardinality at most six is at most the sixth power
of the index type size. -/
private theorem small_set_card_le {ℓ : ℕ} :
    (Finset.univ.filter (fun O : Finset (Fin ℓ) => 0 < O.card ∧ O.card ≤ 6)).card
      ≤ ℓ ^ 6 := by
  classical
  have henum : ∀ O : Finset (Fin ℓ), 0 < O.card → O.card ≤ 6 →
      ∃ g : Fin 6 → Fin ℓ, Finset.image g Finset.univ = O := by
    intro O hpos hle
    obtain ⟨e⟩ : Nonempty (Fin O.card ≃o ↥O) := ⟨O.orderIsoOfFin rfl⟩
    refine ⟨fun j => if h : (j : ℕ) < O.card then ((e ⟨(j : ℕ), h⟩ : ↥O) : Fin ℓ)
        else ((e ⟨0, hpos⟩ : ↥O) : Fin ℓ), ?_⟩
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      by_cases h : (j : ℕ) < O.card
      · simp only [dite_eq_left h]
        exact Subtype.coe_prop _
      · simp only [dite_eq_right h]
        exact Subtype.coe_prop _
    · intro hx
      refine ⟨Fin.castLE hle (e.symm ⟨x, hx⟩), ?_⟩
      have hlt : ((Fin.castLE hle (e.symm ⟨x, hx⟩) : Fin 6) : ℕ) < O.card :=
        (e.symm ⟨x, hx⟩).isLt
      simp only [dite_eq_left hlt]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  have hsub : (Finset.univ.filter (fun O : Finset (Fin ℓ) => 0 < O.card ∧ O.card ≤ 6)) ≤
      Finset.univ.image (fun g : Fin 6 → Fin ℓ => Finset.image g Finset.univ) := by
    intro O hO
    rw [Finset.mem_image]
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hO).2
    obtain ⟨g, hg⟩ := henum O h1 h2
    exact ⟨g, Finset.mem_univ g, hg⟩
  calc (Finset.univ.filter (fun O : Finset (Fin ℓ) => 0 < O.card ∧ O.card ≤ 6)).card
      ≤ (Finset.univ.image
          (fun g : Fin 6 → Fin ℓ => Finset.image g Finset.univ)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 6 → Fin ℓ)).card := Finset.card_image_le
    _ = ℓ ^ 6 := by rw [Finset.card_univ, Fintype.card_pi_const, Fintype.card_fin]

/-- Bounds the number of sequences failing `StrongGood` by the sixth power of the sequence
length times the total number of sequences divided by the register cardinality. -/
private theorem strongGood_filter_card_le {n ℓ : ℕ} :
    (Finset.univ.filter (fun s : Fin ℓ → Reg n => ¬StrongGood s)).card
      * Fintype.card (Reg n) ≤ ℓ ^ 6 * (Fintype.card (Reg n)) ^ ℓ := by
  have hbad : (Finset.univ.filter (fun s : Fin ℓ → Reg n => ¬StrongGood s)) ≤
      (Finset.univ.filter (fun O : Finset (Fin ℓ) => 0 < O.card ∧ O.card ≤ 6)).biUnion
        (fun O => Finset.univ.filter
          (fun s : Fin ℓ → Reg n => xorSet s O = ZeroStr n)) := by
    intro s hs
    have hex : ∃ O : Finset (Fin ℓ), 0 < O.card ∧ O.card ≤ 6 ∧
        xorSet s O = ZeroStr n := by
      by_contra hcon
      refine (Finset.mem_filter.mp hs).2 ?_
      intro O h1 h2 hz
      exact hcon ⟨O, h1, h2, hz⟩
    obtain ⟨O, h1, h2, hz⟩ := hex
    refine Finset.mem_biUnion.mpr ⟨O,
      Finset.mem_filter.mpr ⟨Finset.mem_univ O, ⟨h1, h2⟩⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, hz⟩
  calc (Finset.univ.filter (fun s : Fin ℓ → Reg n => ¬StrongGood s)).card
      * Fintype.card (Reg n) ≤
        ((Finset.univ.filter (fun O : Finset (Fin ℓ) => 0 < O.card ∧ O.card ≤ 6)).biUnion
          (fun O => Finset.univ.filter
            (fun s : Fin ℓ → Reg n => xorSet s O = ZeroStr n))).card
          * Fintype.card (Reg n) :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hbad)
    _ ≤ (∑ O ∈ Finset.univ.filter (fun O : Finset (Fin ℓ) => 0 < O.card ∧ O.card ≤ 6),
          (Finset.univ.filter
            (fun s : Fin ℓ → Reg n => xorSet s O = ZeroStr n)).card)
          * Fintype.card (Reg n) :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ O ∈ Finset.univ.filter (fun O : Finset (Fin ℓ) => 0 < O.card ∧ O.card ≤ 6),
          ((Finset.univ.filter
            (fun s : Fin ℓ → Reg n => xorSet s O = ZeroStr n)).card
            * Fintype.card (Reg n)) := by
        rw [Finset.sum_mul]
    _ ≤ ∑ O ∈ Finset.univ.filter (fun O : Finset (Fin ℓ) => 0 < O.card ∧ O.card ≤ 6),
          (Fintype.card (Reg n)) ^ ℓ :=
        Finset.sum_le_sum fun O hO => fiber_card_le O (Finset.mem_filter.mp hO).2.1
    _ = (Finset.univ.filter (fun O : Finset (Fin ℓ) => 0 < O.card ∧ O.card ≤ 6)).card
          * (Fintype.card (Reg n)) ^ ℓ := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ ≤ ℓ ^ 6 * (Fintype.card (Reg n)) ^ ℓ :=
        Nat.mul_le_mul_right _ small_set_card_le

end Peel

section Cubic

/-- If two vectors over `ZMod 2` sum to zero, they are equal. -/
private theorem bv_add_eq_zero_eq {n : ℕ} (X Y : Fin n → ZMod 2) (h : X + Y = 0) : Y = X := by
  funext i
  have hi : X i + Y i = 0 := congrFun h i
  rw [show Y i = -X i from eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hi),
    ZMod.neg_eq_self_mod_two]

/-- An XOR of four registers equals an XOR of two registers exactly when the combined XOR of all
six vanishes. -/
private theorem xor4_eq_xor2_iff {n : ℕ} (a b c d e f : Reg n) :
    Qatlib.Concepts.WalshMoment.Forrelation.regXor c (Qatlib.Concepts.WalshMoment.Forrelation.regXor d (Qatlib.Concepts.WalshMoment.Forrelation.regXor e f)) = Qatlib.Concepts.WalshMoment.Forrelation.regXor a b ↔
      Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor a b) (Qatlib.Concepts.WalshMoment.Forrelation.regXor c d)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor e f) = ZeroStr n := by
  constructor
  · intro h
    apply (regBooleanEquiv n).injective
    rw [regBE_xor, regBE_xor, regBE_xor, regBE_xor, regBE_xor, regBooleanEquiv_zeroStr]
    have hc := congrArg (regBooleanEquiv n) h
    rw [regBE_xor, regBE_xor, regBE_xor, regBE_xor] at hc
    rw [show (regBooleanEquiv n a + regBooleanEquiv n b + (regBooleanEquiv n c +
        regBooleanEquiv n d)) + (regBooleanEquiv n e + regBooleanEquiv n f) =
        (regBooleanEquiv n a + regBooleanEquiv n b) +
        (regBooleanEquiv n c + (regBooleanEquiv n d +
          (regBooleanEquiv n e + regBooleanEquiv n f))) from by abel, hc,
      bv_add_self _]
  · intro h
    have hBE : (regBooleanEquiv n a + regBooleanEquiv n b) +
        ((regBooleanEquiv n c + regBooleanEquiv n d) +
          (regBooleanEquiv n e + regBooleanEquiv n f)) = 0 :=
      (xor6_zero_iff_BE a b c d e f).mp h
    have hY : (regBooleanEquiv n c + regBooleanEquiv n d) +
        (regBooleanEquiv n e + regBooleanEquiv n f) =
        regBooleanEquiv n a + regBooleanEquiv n b :=
      bv_add_eq_zero_eq _ _ hBE
    apply (regBooleanEquiv n).injective
    rw [regBE_xor, regBE_xor, regBE_xor, regBE_xor]
    rw [show regBooleanEquiv n c + (regBooleanEquiv n d +
        (regBooleanEquiv n e + regBooleanEquiv n f)) =
        (regBooleanEquiv n c + regBooleanEquiv n d) +
        (regBooleanEquiv n e + regBooleanEquiv n f) from by abel]
    exact hY

/-- Expands `rawGamma` as a character sum weighted by `pairCount`. -/
private theorem rawGamma_eq_chi_sum {n ℓ : ℕ} (s : Fin ℓ → Reg n) (z : Reg n) :
    rawGamma s z = ∑ w : Reg n, (pairCount s w : ℝ) * charSignR z w := by
  have hinner : ∀ i j : Fin ℓ, charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) =
      ∑ w : Reg n, (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = w then (1 : ℝ) else 0) * charSignR z w := by
    intro i j
    have hconv : ∀ w : Reg n,
        (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = w then (1 : ℝ) else 0) * charSignR z w =
          (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = w then charSignR z w else 0) := by
      intro w
      by_cases h : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = w <;> simp [h]
    rw [Finset.sum_congr rfl fun w _ => hconv w, Finset.sum_ite_eq]
    simp
  have hswap : ∀ F : Reg n → Fin ℓ → Fin ℓ → ℝ,
      (∑ i, ∑ j, ∑ w : Reg n, F w i j) = ∑ w : Reg n, ∑ i, ∑ j, F w i j := by
    intro F
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_comm,
      Finset.sum_comm]
  unfold rawGamma
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hinner i j, hswap]
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold pairCount
  rw [Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by
    by_cases h : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = w <;> simp [h]

private def sextCount {n ℓ : ℕ} (s : Fin ℓ → Reg n) : ℕ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ o,
    (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
        = ZeroStr n then 1 else 0)

/-- Summing the product of `pairCount` and `quadCount` over registers gives `sextCount`. -/
private theorem sum_pairCount_mul_quadCount {n ℓ : ℕ} (s : Fin ℓ → Reg n) :
    ∑ w : Reg n, pairCount s w * quadCount s w = sextCount s := by
  have hstep : ∀ w : Reg n, pairCount s w * quadCount s w =
      ∑ i, ∑ j, (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = w then quadCount s w else 0) := by
    intro w
    unfold pairCount
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by
      by_cases h : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j) = w <;> simp [h]
  rw [Finset.sum_congr rfl fun w _ => hstep w, Finset.sum_comm]
  unfold sextCount
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  unfold quadCount
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun o _ => ?_
  by_cases h : Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s l) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))) = Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)
  · rw [ite_eq_left h, ite_eq_left ((xor4_eq_xor2_iff (s i) (s j) (s k) (s l) (s m) (s o)).mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun hcon => h ((xor4_eq_xor2_iff (s i) (s j) (s k) (s l)
      (s m) (s o)).mpr hcon))]

/-- The sum of cubed `rawGamma` equals the register cardinality times `sextCount`. -/
private theorem sum_rawGamma_cubic {n ℓ : ℕ} (s : Fin ℓ → Reg n) :
    ∑ z : Reg n, rawGamma s z * rawGamma s z * rawGamma s z =
      (Fintype.card (Reg n) : ℝ) * (sextCount s : ℝ) := by
  have hexp : ∑ z : Reg n, rawGamma s z * rawGamma s z * rawGamma s z =
      ∑ w : Reg n, (pairCount s w : ℝ) *
        ∑ z : Reg n, rawGamma s z * rawGamma s z * charSignR z w := by
    have hstep : ∀ z : Reg n, rawGamma s z * rawGamma s z * rawGamma s z =
        ∑ w : Reg n, rawGamma s z * rawGamma s z *
          ((pairCount s w : ℝ) * charSignR z w) := by
      intro z
      rw [rawGamma_eq_chi_sum s z, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun z _ => hstep z, Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [hexp]
  have h2 : ∀ w : Reg n, (pairCount s w : ℝ) *
      ∑ z : Reg n, rawGamma s z * rawGamma s z * charSignR z w =
      (Fintype.card (Reg n) : ℝ) * ((pairCount s w * quadCount s w : ℕ) : ℝ) := by
    intro w
    have h3 := sum_rawGamma_sq_mul_sign s w
    rw [h3, Nat.cast_mul]
    ring
  rw [Finset.sum_congr rfl fun w _ => h2 w, ← Finset.mul_sum, ← Nat.cast_sum,
    sum_pairCount_mul_quadCount]

/-- A sum of four Boolean register vectors vanishes exactly when the corresponding register XOR
vanishes. -/
private theorem BE_sum4_zero_iff_xor4 {n : ℕ} (a b c d : Reg n) :
    regBooleanEquiv n a + (regBooleanEquiv n b +
        (regBooleanEquiv n c + regBooleanEquiv n d)) = 0 ↔
      Qatlib.Concepts.WalshMoment.Forrelation.regXor a (Qatlib.Concepts.WalshMoment.Forrelation.regXor b (Qatlib.Concepts.WalshMoment.Forrelation.regXor c d)) = ZeroStr n := by
  constructor
  · intro h
    apply (regBooleanEquiv n).injective
    rw [regBE_xor, regBE_xor, regBE_xor, h, regBooleanEquiv_zeroStr]
  · intro h
    have h2 : regBooleanEquiv n (Qatlib.Concepts.WalshMoment.Forrelation.regXor a (Qatlib.Concepts.WalshMoment.Forrelation.regXor b (Qatlib.Concepts.WalshMoment.Forrelation.regXor c d))) = 0 := by
      rw [h, regBooleanEquiv_zeroStr]
    rw [regBE_xor, regBE_xor, regBE_xor] at h2
    exact h2

/-- Summing the indicator of a predicate conjoined with equality to a fixed index gives the
predicate indicator at that index. -/
private theorem sum_ite_and_eq {ι : Type*} [DecidableEq ι] [Fintype ι]
    (P : ι → Prop) [DecidablePred P] (i : ι) :
    ∑ x, (if P x ∧ i = x then (1 : ℕ) else 0) = if P i then 1 else 0 := by
  have hpair : ∀ x : ι, (if P x ∧ i = x then (1 : ℕ) else 0)
      = if i = x then (if P x then 1 else 0) else 0 := by
    intro x
    by_cases h : i = x <;> by_cases hx : P x <;> simp [h, hx]
  rw [Finset.sum_congr rfl fun x _ => hpair x, Finset.sum_ite_eq]
  simp

/-- Rotates the outermost index of a sixfold finite sum to the innermost position. -/
private theorem sum6_rot {ℓ : ℕ} (F : Fin ℓ → Fin ℓ → Fin ℓ → Fin ℓ → Fin ℓ → Fin ℓ → ℕ) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ o, F i j k l m o) =
      ∑ j, ∑ k, ∑ l, ∑ m, ∑ o, ∑ i, F i j k l m o := by
  have r1 : (∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ o, F i j k l m o) =
      ∑ j, ∑ i, ∑ k, ∑ l, ∑ m, ∑ o, F i j k l m o :=
    Finset.sum_comm (f := fun i j => ∑ k, ∑ l, ∑ m, ∑ o, F i j k l m o)
  have r2 : (∑ j, ∑ i, ∑ k, ∑ l, ∑ m, ∑ o, F i j k l m o) =
      ∑ j, ∑ k, ∑ i, ∑ l, ∑ m, ∑ o, F i j k l m o :=
    Finset.sum_congr rfl fun j _ =>
      Finset.sum_comm (f := fun i k => ∑ l, ∑ m, ∑ o, F i j k l m o)
  have r3 : (∑ j, ∑ k, ∑ i, ∑ l, ∑ m, ∑ o, F i j k l m o) =
      ∑ j, ∑ k, ∑ l, ∑ i, ∑ m, ∑ o, F i j k l m o :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_comm (f := fun i l => ∑ m, ∑ o, F i j k l m o)
  have r4 : (∑ j, ∑ k, ∑ l, ∑ i, ∑ m, ∑ o, F i j k l m o) =
      ∑ j, ∑ k, ∑ l, ∑ m, ∑ i, ∑ o, F i j k l m o :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ =>
      Finset.sum_comm (f := fun i m => ∑ o, F i j k l m o)
  have r5 : (∑ j, ∑ k, ∑ l, ∑ m, ∑ i, ∑ o, F i j k l m o) =
      ∑ j, ∑ k, ∑ l, ∑ m, ∑ o, ∑ i, F i j k l m o :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
      Finset.sum_comm (f := fun i o => F i j k l m o)
  rw [r1, r2, r3, r4, r5]

/-- Cancels the repeated vector in the first and third positions of the specified six-term sum
over `ZMod 2`. -/
private theorem BE_cancel13 {n : ℕ} (A B D E F : Fin n → ZMod 2) :
    ((A + B) + ((A + D) + (E + F)) = 0) ↔ (B + (D + (E + F)) = 0) := by
  constructor
  · intro h
    have h2 : (A + A) + (B + (D + (E + F))) = 0 := by
      rw [show (A + A) + (B + (D + (E + F))) = (A + B) + ((A + D) + (E + F)) from by abel]
      exact h
    rw [bv_add_self A, zero_add] at h2
    exact h2
  · intro h
    rw [show (A + B) + ((A + D) + (E + F)) = (A + A) + (B + (D + (E + F))) from by abel,
      bv_add_self A, zero_add]
    exact h

/-- Cancels the repeated vector in the first and fourth positions of the specified six-term sum
over `ZMod 2`. -/
private theorem BE_cancel14 {n : ℕ} (A B C E F : Fin n → ZMod 2) :
    ((A + B) + ((C + A) + (E + F)) = 0) ↔ (B + (C + (E + F)) = 0) := by
  constructor
  · intro h
    have h2 : (A + A) + (B + (C + (E + F))) = 0 := by
      rw [show (A + A) + (B + (C + (E + F))) = (A + B) + ((C + A) + (E + F)) from by abel]
      exact h
    rw [bv_add_self A, zero_add] at h2
    exact h2
  · intro h
    rw [show (A + B) + ((C + A) + (E + F)) = (A + A) + (B + (C + (E + F))) from by abel,
      bv_add_self A, zero_add]
    exact h

/-- Cancels the repeated vector in the first and fifth positions of the specified six-term sum
over `ZMod 2`. -/
private theorem BE_cancel15 {n : ℕ} (A B C D F : Fin n → ZMod 2) :
    ((A + B) + ((C + D) + (A + F)) = 0) ↔ (B + (C + (D + F)) = 0) := by
  constructor
  · intro h
    have h2 : (A + A) + (B + (C + (D + F))) = 0 := by
      rw [show (A + A) + (B + (C + (D + F))) = (A + B) + ((C + D) + (A + F)) from by abel]
      exact h
    rw [bv_add_self A, zero_add] at h2
    exact h2
  · intro h
    rw [show (A + B) + ((C + D) + (A + F)) = (A + A) + (B + (C + (D + F))) from by abel,
      bv_add_self A, zero_add]
    exact h

/-- Cancels the repeated vector in the first and sixth positions of the specified six-term sum
over `ZMod 2`. -/
private theorem BE_cancel16 {n : ℕ} (A B C D E : Fin n → ZMod 2) :
    ((A + B) + ((C + D) + (E + A)) = 0) ↔ (B + (C + (D + E)) = 0) := by
  constructor
  · intro h
    have h2 : (A + A) + (B + (C + (D + E))) = 0 := by
      rw [show (A + A) + (B + (C + (D + E))) = (A + B) + ((C + D) + (E + A)) from by abel]
      exact h
    rw [bv_add_self A, zero_add] at h2
    exact h2
  · intro h
    rw [show (A + B) + ((C + D) + (E + A)) = (A + A) + (B + (C + (D + E))) from by abel,
      bv_add_self A, zero_add]
    exact h

/-- For a sequence satisfying `StrongGood`, `sextCount` is at most five times the length times
the zero-register quadruple count. -/
private theorem sextCount_le {n ℓ : ℕ} (s : Fin ℓ → Reg n) (hgood : StrongGood s) :
    sextCount s ≤ 5 * ℓ * quadCount s (ZeroStr n) := by
  have hpw : ∀ i j k l m o : Fin ℓ,
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n then (1 : ℕ) else 0) ≤
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n ∧ j = i then (1 : ℕ) else 0) +
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n ∧ k = i then (1 : ℕ) else 0) +
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n ∧ l = i then (1 : ℕ) else 0) +
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n ∧ m = i then (1 : ℕ) else 0) +
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n ∧ o = i then (1 : ℕ) else 0) := by
    intro i j k l m o
    by_cases h6 : Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)))
        (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o)) = ZeroStr n
    · have hite : ∀ p : Fin ℓ, i = p →
          (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
              = ZeroStr n ∧ p = i then (1 : ℕ) else 0) = 1 := by
        intro p hip
        exact ite_eq_left ⟨h6, hip.symm⟩
      rw [ite_eq_left h6]
      rcases peel_disj s hgood i j k l m o h6 with h | h | h | h | h
      · rw [hite j h]; omega
      · rw [hite k h]; omega
      · rw [hite l h]; omega
      · rw [hite m h]; omega
      · rw [hite o h]; omega
    · rw [ite_eq_right h6]
      omega
  have ecoll : ∀ (p j k l m o : Fin ℓ),
      (∑ i : Fin ℓ, (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)))
          (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o)) = ZeroStr n ∧ p = i then (1 : ℕ) else 0)) =
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s p) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n then (1 : ℕ) else 0) := by
    intro p j k l m o
    have hsplit : ∀ i : Fin ℓ,
        ((if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
            = ZeroStr n ∧ p = i then (1 : ℕ) else 0)) =
        (if p = i then (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)))
            (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o)) = ZeroStr n then (1 : ℕ) else 0) else 0) := by
      intro i
      by_cases h1 : p = i <;> by_cases h2 : Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j))
          (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o)) = ZeroStr n <;> simp [h1, h2]
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_ite_eq]
    simp
  have econvj : ∀ j k l m o : Fin ℓ,
      ((if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n then (1 : ℕ) else 0)) =
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s l) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))) = ZeroStr n then (1 : ℕ) else 0) := by
    intro j k l m o
    rw [regXor_invol (s j), regXor_zero_left, ← regXor_assoc]
  have econvk : ∀ j k l m o : Fin ℓ,
      ((if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n then (1 : ℕ) else 0)) =
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s l) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))) = ZeroStr n then (1 : ℕ) else 0) := by
    intro j k l m o
    have hiff : (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)))
          (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o)) = ZeroStr n) ↔
        (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s l) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))) = ZeroStr n) := by
      rw [xor6_zero_iff_BE (s k) (s j) (s k) (s l) (s m) (s o)]
      exact (BE_cancel13 (regBooleanEquiv n (s k)) (regBooleanEquiv n (s j))
        (regBooleanEquiv n (s l)) (regBooleanEquiv n (s m)) (regBooleanEquiv n (s o))).trans
        (BE_sum4_zero_iff_xor4 (s j) (s l) (s m) (s o))
    by_cases h6 : Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)))
        (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o)) = ZeroStr n
    · rw [ite_eq_left h6, ite_eq_left (hiff.mp h6)]
    · rw [ite_eq_right h6, ite_eq_right (fun hQ => h6 (hiff.mpr hQ))]
  have econvl : ∀ j k l m o : Fin ℓ,
      ((if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s l) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n then (1 : ℕ) else 0)) =
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))) = ZeroStr n then (1 : ℕ) else 0) := by
    intro j k l m o
    have hiff : (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s l) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)))
          (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o)) = ZeroStr n) ↔
        (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))) = ZeroStr n) := by
      rw [xor6_zero_iff_BE (s l) (s j) (s k) (s l) (s m) (s o)]
      exact (BE_cancel14 (regBooleanEquiv n (s l)) (regBooleanEquiv n (s j))
        (regBooleanEquiv n (s k)) (regBooleanEquiv n (s m)) (regBooleanEquiv n (s o))).trans
        (BE_sum4_zero_iff_xor4 (s j) (s k) (s m) (s o))
    by_cases h6 : Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s l) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)))
        (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o)) = ZeroStr n
    · rw [ite_eq_left h6, ite_eq_left (hiff.mp h6)]
    · rw [ite_eq_right h6, ite_eq_right (fun hQ => h6 (hiff.mpr hQ))]
  have econvm : ∀ j k l m o : Fin ℓ,
      ((if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n then (1 : ℕ) else 0)) =
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s l) (s o))) = ZeroStr n then (1 : ℕ) else 0) := by
    intro j k l m o
    have hiff : (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)))
          (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o)) = ZeroStr n) ↔
        (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s l) (s o))) = ZeroStr n) := by
      rw [xor6_zero_iff_BE (s m) (s j) (s k) (s l) (s m) (s o)]
      exact (BE_cancel15 (regBooleanEquiv n (s m)) (regBooleanEquiv n (s j))
        (regBooleanEquiv n (s k)) (regBooleanEquiv n (s l)) (regBooleanEquiv n (s o))).trans
        (BE_sum4_zero_iff_xor4 (s j) (s k) (s l) (s o))
    by_cases h6 : Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)))
        (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o)) = ZeroStr n
    · rw [ite_eq_left h6, ite_eq_left (hiff.mp h6)]
    · rw [ite_eq_right h6, ite_eq_right (fun hQ => h6 (hiff.mpr hQ))]
  have econvo : ∀ j k l m o : Fin ℓ,
      ((if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s o) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n then (1 : ℕ) else 0)) =
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s l) (s m))) = ZeroStr n then (1 : ℕ) else 0) := by
    intro j k l m o
    have hiff : (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s o) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)))
          (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o)) = ZeroStr n) ↔
        (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s j) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s l) (s m))) = ZeroStr n) := by
      rw [xor6_zero_iff_BE (s o) (s j) (s k) (s l) (s m) (s o)]
      exact (BE_cancel16 (regBooleanEquiv n (s o)) (regBooleanEquiv n (s j))
        (regBooleanEquiv n (s k)) (regBooleanEquiv n (s l)) (regBooleanEquiv n (s m))).trans
        (BE_sum4_zero_iff_xor4 (s j) (s k) (s l) (s m))
    by_cases h6 : Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s o) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l)))
        (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o)) = ZeroStr n
    · rw [ite_eq_left h6, ite_eq_left (hiff.mp h6)]
    · rw [ite_eq_right h6, ite_eq_right (fun hQ => h6 (hiff.mpr hQ))]
  have hpj : (∑ j, ∑ k, ∑ l, ∑ m, ∑ o, ∑ i,
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n ∧ j = i then (1 : ℕ) else 0)) =
      ℓ * quadCount s (ZeroStr n) := by
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun o _ => ecoll j j k l m o,
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun o _ => econvj j k l m o]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
    rfl
  have hpk : (∑ j, ∑ k, ∑ l, ∑ m, ∑ o, ∑ i,
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n ∧ k = i then (1 : ℕ) else 0)) =
      ℓ * quadCount s (ZeroStr n) := by
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun o _ => ecoll k j k l m o,
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun o _ => econvk j k l m o]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul,
      ← Finset.mul_sum]
    rfl
  have hpl : (∑ j, ∑ k, ∑ l, ∑ m, ∑ o, ∑ i,
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n ∧ l = i then (1 : ℕ) else 0)) =
      ℓ * quadCount s (ZeroStr n) := by
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun o _ => ecoll l j k l m o,
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun o _ => econvl j k l m o]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul,
      ← Finset.mul_sum]
    rfl
  have hpm : (∑ j, ∑ k, ∑ l, ∑ m, ∑ o, ∑ i,
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n ∧ m = i then (1 : ℕ) else 0)) =
      ℓ * quadCount s (ZeroStr n) := by
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun o _ => ecoll m j k l m o,
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun o _ => econvm j k l m o]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul,
      ← Finset.mul_sum]
    rfl
  have hpo : (∑ j, ∑ k, ∑ l, ∑ m, ∑ o, ∑ i,
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n ∧ o = i then (1 : ℕ) else 0)) =
      ℓ * quadCount s (ZeroStr n) := by
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun o _ => ecoll o j k l m o,
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun o _ => econvo j k l m o]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul,
      ← Finset.mul_sum]
    rfl
  unfold sextCount
  have hrot : (∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ o,
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n then (1 : ℕ) else 0)) =
      (∑ j, ∑ k, ∑ l, ∑ m, ∑ o, ∑ i,
      (if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n then (1 : ℕ) else 0)) :=
    sum6_rot (fun i j k l m o =>
      if Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s i) (s j)) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s k) (s l))) (Qatlib.Concepts.WalshMoment.Forrelation.regXor (s m) (s o))
          = ZeroStr n then (1 : ℕ) else 0)
  rw [hrot]
  refine le_trans (Finset.sum_le_sum (s := Finset.univ) fun j _ =>
    Finset.sum_le_sum (s := Finset.univ) fun k _ =>
    Finset.sum_le_sum (s := Finset.univ) fun l _ =>
    Finset.sum_le_sum (s := Finset.univ) fun m _ =>
    Finset.sum_le_sum (s := Finset.univ) fun o _ =>
    Finset.sum_le_sum (s := Finset.univ) fun i _ => hpw i j k l m o) ?_
  simp only [Finset.sum_add_distrib]
  rw [hpj, hpk, hpl, hpm, hpo, Nat.mul_assoc]
  omega

/-- For a nonempty sequence satisfying `StrongGood`, the sum of cubed `gammaOfMultiset` is at
most fifteen times the register cardinality. -/
private theorem sum_gamma_cubic_le {n ℓ : ℕ} (s : Fin ℓ → Reg n) (hgood : StrongGood s)
    (hℓ : ℓ ≠ 0) :
    ∑ z : Reg n, gammaOfMultiset n ℓ s z ^ 3 ≤ 15 * (Fintype.card (Reg n) : ℝ) := by
  have hpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hℓ
  have hℓℝ : ((ℓ : ℝ)) ≠ 0 := cast_ℓ_ne_zero hℓ
  have hd0 : (0 : ℝ) < ((ℓ : ℝ) ^ 3) := pow_pos hpos 3
  have hγ : ∀ z : Reg n, gammaOfMultiset n ℓ s z = rawGamma s z / (ℓ : ℝ) := by
    intro z
    rw [eq_div_iff hℓℝ, mul_comm]
    exact gamma_mul_ell s z
  have hterm : ∀ z : Reg n, gammaOfMultiset n ℓ s z ^ 3
      = rawGamma s z ^ 3 / ((ℓ : ℝ) ^ 3) := by
    intro z
    rw [hγ z, div_pow]
  have hcube : ∀ z : Reg n, rawGamma s z ^ 3
      = rawGamma s z * rawGamma s z * rawGamma s z := by
    intro z
    rw [pow_three]
    ring
  rw [Finset.sum_congr rfl fun z _ => hterm z, ← Finset.sum_div,
    Finset.sum_congr rfl fun z _ => hcube z, sum_rawGamma_cubic s]
  have hsex : (sextCount s : ℝ) ≤ 15 * ((ℓ : ℝ) ^ 3) := by
    have hQ : quadCount s (ZeroStr n) ≤ 3 * ℓ * ℓ := by
      have h1 := quadCount_zero_le s hgood
      have h2 : ℓ + 2 * (ℓ - 1) ≤ 3 * ℓ := by omega
      calc quadCount s (ZeroStr n) ≤ ℓ * (ℓ + 2 * (ℓ - 1)) := h1
        _ ≤ ℓ * (3 * ℓ) := Nat.mul_le_mul_left ℓ h2
        _ = 3 * ℓ * ℓ := by ring
    have hnat : sextCount s ≤ 15 * (ℓ * ℓ * ℓ) := by
      calc sextCount s ≤ 5 * ℓ * quadCount s (ZeroStr n) := sextCount_le s hgood
        _ ≤ 5 * ℓ * (3 * ℓ * ℓ) := Nat.mul_le_mul_left (5 * ℓ) hQ
        _ = 15 * (ℓ * ℓ * ℓ) := by ring
    refine le_trans (Nat.cast_le.2 hnat) ?_
    push_cast
    exact le_of_eq (by ring)
  have hN : (0 : ℝ) ≤ (Fintype.card (Reg n) : ℝ) := Nat.cast_nonneg _
  rw [div_le_iff₀ hd0]
  calc (Fintype.card (Reg n) : ℝ) * (sextCount s : ℝ) ≤
        (Fintype.card (Reg n) : ℝ) * (15 * ((ℓ : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_left hsex hN
    _ = 15 * (Fintype.card (Reg n) : ℝ) * ((ℓ : ℝ) ^ 3) := by ring

end Cubic

section WeightNorm

private noncomputable def bernFactor {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n)
    (y : Reg n) (b : Bool) : ℝ :=
  if b then pExp κ s y else 1 - pExp κ s y

/-- For a nonnegative parameter, `pExp` takes values in the closed unit interval. -/
private theorem pExp_mem_Icc {n ℓ : ℕ} (κ : ℝ) (hκ : 0 ≤ κ) (s : Fin ℓ → Reg n)
    (z : Reg n) : pExp κ s z ∈ Set.Icc (0 : ℝ) 1 := by
  have hγ : 0 ≤ κ * gammaOfMultiset n ℓ s z :=
    mul_nonneg hκ (gammaOfMultiset_nonneg n ℓ s z)
  have h1 : (Real.exp (-(κ * gammaOfMultiset n ℓ s z))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have h0 : (0 : ℝ) ≤ Real.exp (-(κ * gammaOfMultiset n ℓ s z)) :=
    Real.exp_nonneg _
  unfold pExp
  by_cases hz : z = ZeroStr n
  · rw [ite_eq_left hz]
    norm_num
  · rw [ite_eq_right hz]
    unfold pAll
    constructor <;> linarith

/-- The value of `pExp` at the zero string is zero. -/
private theorem pExp_zero {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n) :
    pExp κ s (ZeroStr n) = 0 := by
  unfold pExp
  simp

/-- The two Boolean values of `bernFactor` sum to one. -/
private theorem bernFactor_sum {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n) (y : Reg n) :
    ∑ b : Bool, bernFactor κ s y b = 1 := by
  unfold bernFactor
  simp

/-- The strong Bernoulli weight factors as the product of its coordinate Bernoulli factors. -/
private theorem strongBernoulliWeight_eq_prod {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n)
    (u : Reg n → Bool) :
    strongBernoulliWeight n ℓ κ s u = ∏ y : Reg n, bernFactor κ s y (u y) := by
  have hpExp0 : pExp κ s (ZeroStr n) = 0 := by
    unfold pExp
    simp
  unfold strongBernoulliWeight bernFactor
  have heatom : ∀ y : Reg n,
      Real.exp (-(κ * gammaOfMultiset n ℓ s y)) =
        Real.exp (-(κ : ℝ) * gammaOfMultiset n ℓ s y) := fun y => by
    congr 1
    ring
  by_cases hu0 : u (ZeroStr n)
  · rw [ite_eq_left hu0]
    have hprod : ∏ y : Reg n, (if u y then pExp κ s y else 1 - pExp κ s y) = 0 := by
      have hf : (if u (ZeroStr n) then pExp κ s (ZeroStr n) else 1 - pExp κ s (ZeroStr n))
          = 0 := by
        rw [ite_eq_left hu0, hpExp0]
      exact Finset.prod_eq_zero (Finset.mem_univ (ZeroStr n)) hf
    exact hprod.symm
  · rw [ite_eq_right hu0]
    refine Finset.prod_congr rfl fun y _ => ?_
    by_cases hy : y = ZeroStr n
    · subst hy
      rw [ite_eq_left rfl, ite_eq_right hu0, hpExp0]
      norm_num
    · rw [ite_eq_right hy]
      have hpE : pExp κ s y = 1 - Real.exp (-(κ : ℝ) * gammaOfMultiset n ℓ s y) / 2 := by
        unfold pExp pAll
        rw [ite_eq_right hy, heatom y]
      by_cases huy : u y
      · rw [ite_eq_left huy, ite_eq_left huy, hpE]
      · rw [ite_eq_right huy, ite_eq_right huy, hpE]
        ring

/-- The strong Bernoulli weights sum to one over all Boolean register functions. -/
private theorem strongBernoulliWeight_sum {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n) :
    ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u = 1 := by
  rw [Finset.sum_congr rfl fun u _ => strongBernoulliWeight_eq_prod κ s u]
  have hswap : ∑ u : Reg n → Bool, ∏ y : Reg n, bernFactor κ s y (u y)
      = ∑ u ∈ Fintype.piFinset (fun _ : Reg n => (Finset.univ : Finset Bool)),
          ∏ y : Reg n, bernFactor κ s y (u y) :=
    Finset.sum_congr rfl fun u _ => rfl
  rw [hswap, ← Finset.prod_univ_sum
      (t := fun _ : Reg n => (Finset.univ : Finset Bool))
      (f := fun y b => bernFactor κ s y b)]
  simp only [bernFactor_sum]
  exact Finset.prod_const_one

end WeightNorm

section EntryTail

/-- Every real character sign has absolute value one. -/
private theorem abs_charSignR {n : ℕ} (z w : Reg n) : |charSignR z w| = 1 := by
  rw [charSignR_bitDot z w]
  by_cases h : bitDot z w <;> simp [h]

private def bernFinDist {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : FinDist Bool where
  prob b := if b then q else 1 - q
  nonneg b := by cases b <;> simp [h0, sub_nonneg.mpr h1]
  sum_one := by norm_num

private noncomputable def devCoord {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n)
    (z x y : Reg n) (b : Bool) : ℝ :=
  ((if b then 1 else 0) - pExp κ s z) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) /
    (Fintype.card (Reg n) : ℝ)

private noncomputable def devEntry {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n)
    (u : Reg n → Bool) (x y : Reg n) : ℝ :=
  ∑ z ∈ (Finset.univ : Finset (Reg n)).filter (· ≠ ZeroStr n), devCoord κ s z x y (u z)

/-- Bounds the moment generating function of a single deviation coordinate by a Gaussian
exponential with denominator twice the squared register cardinality. -/
private theorem coord_mgf_le {n ℓ : ℕ} (κ : ℝ) (hκ : 0 ≤ κ) (s : Fin ℓ → Reg n)
    (z x y : Reg n) (τ : ℝ) :
    ∑ b : Bool, bernFactor κ s z b * Real.exp (τ * devCoord κ s z x y b) ≤
      Real.exp (τ ^ 2 / (2 * (Fintype.card (Reg n) : ℝ) ^ 2)) := by
  have hq := pExp_mem_Icc κ hκ s z
  have hN : (0 : ℝ) < (Fintype.card (Reg n) : ℝ) := card_reg_pos n
  have habs := abs_charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y)
  have hprob : ∀ b : Bool, (bernFinDist hq.1 hq.2).prob b = bernFactor κ s z b := by
    intro b
    unfold bernFinDist bernFactor
    cases b <;> rfl
  have hexp0 : (bernFinDist hq.1 hq.2).expect (devCoord κ s z x y) = 0 := by
    simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, hprob]
    rw [Fintype.sum_bool]
    unfold bernFactor devCoord
    norm_num
    ring
  have hc : ∀ b : Bool, |(if b then 1 else 0) - pExp κ s z| ≤ 1 := by
    have hq1 := (pExp_mem_Icc κ hκ s z).1
    have hq2 := (pExp_mem_Icc κ hκ s z).2
    intro b
    cases b
    · show |(0 : ℝ) - pExp κ s z| ≤ 1
      rw [zero_sub, abs_neg, abs_of_nonneg hq1]
      exact hq2
    · show |(1 : ℝ) - pExp κ s z| ≤ 1
      rw [abs_le]
      constructor <;> linarith
  have habsle : ∀ b : Bool, |devCoord κ s z x y b| ≤ 1 / (Fintype.card (Reg n) : ℝ) := by
    intro b
    have h1 : |devCoord κ s z x y b|
        = |(if b then 1 else 0) - pExp κ s z| / (Fintype.card (Reg n) : ℝ) := by
      unfold devCoord
      rw [abs_div, abs_mul, habs, abs_of_pos hN, mul_one]
    have hcanc : (1 / (Fintype.card (Reg n) : ℝ)) * (Fintype.card (Reg n) : ℝ) = 1 := by
      field_simp
    rw [h1, div_le_iff₀ hN, hcanc]
    exact hc b
  have hmem : ∀ b : Bool, devCoord κ s z x y b ∈ Set.Icc
      (-(1 / (Fintype.card (Reg n) : ℝ))) (1 / (Fintype.card (Reg n) : ℝ)) :=
    fun b => abs_le.mp (habsle b)
  have hinv : (0 : ℝ) < 1 / (Fintype.card (Reg n) : ℝ) := by positivity
  have hmain := finite_hoeffding_centered_mgf Bool (bernFinDist hq.1 hq.2) (devCoord κ s z x y)
    (-(1 / (Fintype.card (Reg n) : ℝ))) (1 / (Fintype.card (Reg n) : ℝ)) τ
    (by linarith) hmem
  rw [hexp0] at hmain
  simp only [sub_zero] at hmain
  have hsum : ∑ b : Bool, bernFactor κ s z b * Real.exp (τ * devCoord κ s z x y b) =
      (bernFinDist hq.1 hq.2).expect (fun b => Real.exp (τ * devCoord κ s z x y b)) := by
    simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, hprob]
  rw [hsum]
  have hd : (1 / (Fintype.card (Reg n) : ℝ) - -(1 / (Fintype.card (Reg n) : ℝ))) =
      2 / (Fintype.card (Reg n) : ℝ) := by ring
  rw [hd] at hmain
  have hfin : τ ^ 2 * (2 / (Fintype.card (Reg n) : ℝ)) ^ 2 / 8
      = τ ^ 2 / (2 * (Fintype.card (Reg n) : ℝ) ^ 2) := by
    field_simp
    ring
  rw [hfin] at hmain
  exact hmain

/-- Bounds the moment generating function of `devEntry` by a Gaussian exponential with
denominator twice the register cardinality. -/
private theorem devEntry_mgf_le {n ℓ : ℕ} (κ : ℝ) (hκ : 0 ≤ κ) (s : Fin ℓ → Reg n)
    (x y : Reg n) (τ : ℝ) :
    ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
        Real.exp (τ * devEntry κ s u x y) ≤
      Real.exp (τ ^ 2 / (2 * (Fintype.card (Reg n) : ℝ))) := by
  have hN := card_reg_pos n
  have hN0 := card_reg_ne_zero n
  have hbf : ∀ (y : Reg n) (b : Bool), (0 : ℝ) ≤ bernFactor κ s y b := by
    intro y b
    have hq1 := (pExp_mem_Icc κ hκ s y).1
    have hq2 := (pExp_mem_Icc κ hκ s y).2
    unfold bernFactor
    cases b <;> simp <;> linarith
  have hprod : ∀ u : Reg n → Bool,
      strongBernoulliWeight n ℓ κ s u * Real.exp (τ * devEntry κ s u x y) =
        ∏ w : Reg n, (bernFactor κ s w (u w) *
          (if w ≠ ZeroStr n then Real.exp (τ * devCoord κ s w x y (u w)) else 1)) := by
    intro u
    rw [strongBernoulliWeight_eq_prod κ s u]
    have hE : Real.exp (τ * devEntry κ s u x y) =
        ∏ z ∈ (Finset.univ : Finset (Reg n)).filter (· ≠ ZeroStr n),
          Real.exp (τ * devCoord κ s z x y (u z)) := by
      unfold devEntry
      rw [Finset.mul_sum, Real.exp_sum]
    have h2 : ∏ z ∈ (Finset.univ : Finset (Reg n)).filter (· ≠ ZeroStr n),
          Real.exp (τ * devCoord κ s z x y (u z)) =
        ∏ z : Reg n, (if z ≠ ZeroStr n then
          Real.exp (τ * devCoord κ s z x y (u z)) else 1) :=
      by rw [Finset.prod_filter]
    rw [hE, h2]
    simp only [Finset.prod_mul_distrib]
  have hswap : ∑ u : Reg n → Bool,
        ∏ w : Reg n, (bernFactor κ s w (u w) *
          (if w ≠ ZeroStr n then Real.exp (τ * devCoord κ s w x y (u w)) else 1)) =
      ∑ u ∈ Fintype.piFinset (fun _ : Reg n => (Finset.univ : Finset Bool)),
        ∏ w : Reg n, (bernFactor κ s w (u w) *
          (if w ≠ ZeroStr n then Real.exp (τ * devCoord κ s w x y (u w)) else 1)) :=
    Finset.sum_congr rfl fun u _ => rfl
  rw [Finset.sum_congr rfl fun u _ => hprod u, hswap, ← Finset.prod_univ_sum
      (t := fun _ : Reg n => (Finset.univ : Finset Bool))
      (f := fun w b => bernFactor κ s w b *
        (if w ≠ ZeroStr n then Real.exp (τ * devCoord κ s w x y b) else 1))]
  have hcoord : ∀ w : Reg n, (∑ b : Bool, bernFactor κ s w b *
        (if w ≠ ZeroStr n then Real.exp (τ * devCoord κ s w x y b) else 1)) ≤
      (if w ≠ ZeroStr n then Real.exp (τ ^ 2 / (2 * (Fintype.card (Reg n) : ℝ) ^ 2)) else 1) := by
    intro w
    by_cases hw : w ≠ ZeroStr n
    · rw [ite_eq_left hw]
      have h2 : ∀ b : Bool, bernFactor κ s w b *
          (if w ≠ ZeroStr n then Real.exp (τ * devCoord κ s w x y b) else 1) =
          bernFactor κ s w b * Real.exp (τ * devCoord κ s w x y b) := fun b => by
        rw [ite_eq_left hw]
      rw [Finset.sum_congr rfl fun b _ => h2 b]
      exact coord_mgf_le κ hκ s w x y τ
    · rw [ite_eq_right hw]
      have h1 : ∑ b : Bool, bernFactor κ s w b *
          (if w ≠ ZeroStr n then Real.exp (τ * devCoord κ s w x y b) else 1) = 1 := by
        rw [Finset.sum_congr rfl fun b _ => by rw [ite_eq_right hw, mul_one]]
        exact bernFactor_sum κ s w
      rw [h1]
  have hnn : ∀ w : Reg n, (0 : ℝ) ≤ ∑ b : Bool, bernFactor κ s w b *
      (if w ≠ ZeroStr n then Real.exp (τ * devCoord κ s w x y b) else 1) :=
    fun w => Finset.sum_nonneg fun b _ => mul_nonneg (hbf w b) (by
      by_cases hw : w ≠ ZeroStr n
      · rw [ite_eq_left hw]; exact Real.exp_nonneg _
      · rw [ite_eq_right hw]; norm_num)
  have hone : (1 : ℝ) ≤ Real.exp (τ ^ 2 / (2 * (Fintype.card (Reg n) : ℝ) ^ 2)) :=
    Real.one_le_exp (by positivity)
  have hpt : ∀ w : Reg n, (0 : ℝ) ≤
      (if w ≠ ZeroStr n then Real.exp (τ ^ 2 / (2 * (Fintype.card (Reg n) : ℝ) ^ 2)) else 1) ∧
      (if w ≠ ZeroStr n then Real.exp (τ ^ 2 / (2 * (Fintype.card (Reg n) : ℝ) ^ 2)) else 1) ≤
        Real.exp (τ ^ 2 / (2 * (Fintype.card (Reg n) : ℝ) ^ 2)) := by
    intro w
    by_cases hw : w ≠ ZeroStr n
    · rw [ite_eq_left hw]
      exact ⟨Real.exp_nonneg _, le_refl _⟩
    · rw [ite_eq_right hw]
      exact ⟨by norm_num, hone⟩
  calc (∏ w : Reg n, ∑ b : Bool, bernFactor κ s w b *
          (if w ≠ ZeroStr n then Real.exp (τ * devCoord κ s w x y b) else 1)) ≤
        ∏ w : Reg n, (if w ≠ ZeroStr n then
          Real.exp (τ ^ 2 / (2 * (Fintype.card (Reg n) : ℝ) ^ 2)) else 1) :=
          Finset.prod_le_prod₀ (fun w _ => hnn w) (fun w _ => hcoord w)
    _ ≤ ∏ w : Reg n, Real.exp (τ ^ 2 / (2 * (Fintype.card (Reg n) : ℝ) ^ 2)) :=
          Finset.prod_le_prod₀ (fun w _ => (hpt w).1) (fun w _ => (hpt w).2)
    _ = Real.exp ((Fintype.card (Reg n) : ℝ) *
          (τ ^ 2 / (2 * (Fintype.card (Reg n) : ℝ) ^ 2))) := by
          rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
    _ = Real.exp (τ ^ 2 / (2 * (Fintype.card (Reg n) : ℝ))) := by
          congr 1
          field_simp

/-- A Gaussian moment generating function bound yields the stated exponential upper-tail bound
under the strong Bernoulli weights. -/
private theorem signed_tail {n ℓ : ℕ} (κ : ℝ) (hκ : 0 ≤ κ) (s : Fin ℓ → Reg n)
    (g : (Reg n → Bool) → ℝ)
    (hmgf : ∀ τ : ℝ, ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
        Real.exp (τ * g u) ≤ Real.exp (τ ^ 2 / (2 * (Fintype.card (Reg n) : ℝ))))
    {u₀ : ℝ} (hu₀ : 0 ≤ u₀) :
    ∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter (fun u => u₀ ≤ g u),
      strongBernoulliWeight n ℓ κ s u ≤
      Real.exp (-(u₀ ^ 2 * (Fintype.card (Reg n) : ℝ) / 2)) := by
  have hN := card_reg_pos n
  set τ : ℝ := u₀ * (Fintype.card (Reg n) : ℝ) with hτdef
  have hτpos : (0 : ℝ) ≤ τ := by
    dsimp [τ]
    exact mul_nonneg hu₀ hN.le
  have hWnn : ∀ u : Reg n → Bool, (0 : ℝ) ≤ strongBernoulliWeight n ℓ κ s u :=
    fun u => strongBernoulliWeight_nonneg n ℓ κ hκ s u

  have hptw : ∀ u : Reg n → Bool,
      (if u₀ ≤ g u then strongBernoulliWeight n ℓ κ s u else 0) ≤
        strongBernoulliWeight n ℓ κ s u * Real.exp (τ * (g u - u₀)) := by
    intro u
    by_cases hu : u₀ ≤ g u
    · rw [ite_eq_left hu]
      have hkey : (1 : ℝ) ≤ Real.exp (τ * (g u - u₀)) := by
        refine Real.one_le_exp ?_
        exact mul_nonneg hτpos (by linarith)
      calc strongBernoulliWeight n ℓ κ s u
          = strongBernoulliWeight n ℓ κ s u * 1 := (mul_one _).symm
        _ ≤ strongBernoulliWeight n ℓ κ s u * Real.exp (τ * (g u - u₀)) :=
            mul_le_mul_of_nonneg_left hkey (hWnn u)
    · rw [ite_eq_right hu]
      exact mul_nonneg (hWnn u) (Real.exp_nonneg _)

  have hfil : ∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter (fun u => u₀ ≤ g u),
        strongBernoulliWeight n ℓ κ s u =
      ∑ u : Reg n → Bool, (if u₀ ≤ g u then strongBernoulliWeight n ℓ κ s u else 0) :=
    by rw [Finset.sum_filter]
  rw [hfil]
  calc ∑ u : Reg n → Bool, (if u₀ ≤ g u then strongBernoulliWeight n ℓ κ s u else 0) ≤
        ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
          Real.exp (τ * (g u - u₀)) := Finset.sum_le_sum (fun u _ => hptw u)
    _ = Real.exp (-(τ * u₀)) * ∑ u : Reg n → Bool,
          strongBernoulliWeight n ℓ κ s u * Real.exp (τ * g u) := by
        have hsplit : ∀ u : Reg n → Bool,
            strongBernoulliWeight n ℓ κ s u * Real.exp (τ * (g u - u₀)) =
              Real.exp (-(τ * u₀)) * (strongBernoulliWeight n ℓ κ s u * Real.exp (τ * g u)) := by
          intro u
          have hexp : Real.exp (τ * (g u - u₀)) =
              Real.exp (τ * g u) * Real.exp (-(τ * u₀)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hexp]
          ring
        rw [Finset.sum_congr rfl fun u _ => hsplit u, Finset.mul_sum]
    _ ≤ Real.exp (-(τ * u₀)) * Real.exp (τ ^ 2 / (2 * (Fintype.card (Reg n) : ℝ))) :=
        mul_le_mul_of_nonneg_left (hmgf τ) (Real.exp_nonneg _)
    _ = Real.exp (-(u₀ ^ 2 * (Fintype.card (Reg n) : ℝ) / 2)) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [τ]
        field_simp
        ring

/-- Bounds the two-sided tail of `devEntry` by twice the corresponding Gaussian exponential. -/
private theorem devEntry_tail_two {n ℓ : ℕ} (κ : ℝ) (hκ : 0 ≤ κ) (s : Fin ℓ → Reg n)
    (x y : Reg n) {u₀ : ℝ} (hu₀ : 0 ≤ u₀) :
    ∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => u₀ ≤ |devEntry κ s u x y|),
      strongBernoulliWeight n ℓ κ s u ≤
      2 * Real.exp (-(u₀ ^ 2 * (Fintype.card (Reg n) : ℝ) / 2)) := by
  have hmgf : ∀ τ : ℝ, ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
      Real.exp (τ * devEntry κ s u x y) ≤
      Real.exp (τ ^ 2 / (2 * (Fintype.card (Reg n) : ℝ))) :=
    fun τ => devEntry_mgf_le κ hκ s x y τ
  have hpos := signed_tail κ hκ s (fun u => devEntry κ s u x y) hmgf hu₀
  have hneg := signed_tail κ hκ s (fun u => -devEntry κ s u x y)
    (fun τ => by
      have hcongr : ∀ u : Reg n → Bool,
          τ * (-devEntry κ s u x y) = (-τ) * devEntry κ s u x y := fun u => by ring
      have hrw : ∑ u : Reg n → Bool,
          strongBernoulliWeight n ℓ κ s u * Real.exp (τ * (-devEntry κ s u x y)) =
          ∑ u : Reg n → Bool,
          strongBernoulliWeight n ℓ κ s u * Real.exp ((-τ) * devEntry κ s u x y) :=
        Finset.sum_congr rfl fun u _ => by rw [hcongr u]
      have hpow : (-τ) ^ 2 = τ ^ 2 := by ring
      rw [hrw]
      exact le_trans (hmgf (-τ)) (by rw [hpow])) hu₀
  have hWnn : ∀ u : Reg n → Bool, (0 : ℝ) ≤ strongBernoulliWeight n ℓ κ s u :=
    fun u => strongBernoulliWeight_nonneg n ℓ κ hκ s u
  have hcover : ∀ u : Reg n → Bool,
      (if u₀ ≤ |devEntry κ s u x y| then strongBernoulliWeight n ℓ κ s u else 0) ≤
      (if u₀ ≤ devEntry κ s u x y then strongBernoulliWeight n ℓ κ s u else 0) +
      (if u₀ ≤ -devEntry κ s u x y then strongBernoulliWeight n ℓ κ s u else 0) := by
    intro u
    have hW := hWnn u
    by_cases hA : u₀ ≤ |devEntry κ s u x y|
    · by_cases hd : devEntry κ s u x y ≤ 0
      · rw [abs_of_nonpos hd] at hA
        rw [abs_of_nonpos hd, ite_eq_left hA]
        by_cases hB : u₀ ≤ devEntry κ s u x y
        · rw [ite_eq_left hB]; linarith
        · rw [ite_eq_right hB]; linarith
      · have hd' : 0 < devEntry κ s u x y := by linarith
        rw [abs_of_pos hd'] at hA
        rw [abs_of_pos hd', ite_eq_left hA]
        by_cases hC : u₀ ≤ -devEntry κ s u x y
        · rw [ite_eq_left hC]; linarith
        · rw [ite_eq_right hC]; linarith
    · rw [ite_eq_right hA]
      apply add_nonneg
      · by_cases hB : u₀ ≤ devEntry κ s u x y
        · rw [ite_eq_left hB]; exact hW
        · rw [ite_eq_right hB]
      · by_cases hC : u₀ ≤ -devEntry κ s u x y
        · rw [ite_eq_left hC]; exact hW
        · rw [ite_eq_right hC]
  have hfil : ∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => u₀ ≤ |devEntry κ s u x y|),
        strongBernoulliWeight n ℓ κ s u =
      ∑ u : Reg n → Bool, (if u₀ ≤ |devEntry κ s u x y| then
        strongBernoulliWeight n ℓ κ s u else 0) :=
    by rw [Finset.sum_filter]
  have hfilpos : ∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => u₀ ≤ devEntry κ s u x y),
        strongBernoulliWeight n ℓ κ s u =
      ∑ u : Reg n → Bool, (if u₀ ≤ devEntry κ s u x y then
        strongBernoulliWeight n ℓ κ s u else 0) :=
    by rw [Finset.sum_filter]
  have hfilneg : ∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => u₀ ≤ -devEntry κ s u x y),
        strongBernoulliWeight n ℓ κ s u =
      ∑ u : Reg n → Bool, (if u₀ ≤ -devEntry κ s u x y then
        strongBernoulliWeight n ℓ κ s u else 0) :=
    by rw [Finset.sum_filter]
  rw [hfil]
  have hpos' : ∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => u₀ ≤ devEntry κ s u x y),
        strongBernoulliWeight n ℓ κ s u ≤
      Real.exp (-(u₀ ^ 2 * (Fintype.card (Reg n) : ℝ) / 2)) := hpos
  have hneg' : ∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => u₀ ≤ -devEntry κ s u x y),
        strongBernoulliWeight n ℓ κ s u ≤
      Real.exp (-(u₀ ^ 2 * (Fintype.card (Reg n) : ℝ) / 2)) := hneg
  have h1 : ∑ u : Reg n → Bool, (if u₀ ≤ |devEntry κ s u x y| then
        strongBernoulliWeight n ℓ κ s u else 0) ≤
      (∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
          (fun u => u₀ ≤ devEntry κ s u x y),
          strongBernoulliWeight n ℓ κ s u) +
      (∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
          (fun u => u₀ ≤ -devEntry κ s u x y),
          strongBernoulliWeight n ℓ κ s u) := by
    calc ∑ u : Reg n → Bool, (if u₀ ≤ |devEntry κ s u x y| then
            strongBernoulliWeight n ℓ κ s u else 0) ≤
          ∑ u : Reg n → Bool, ((if u₀ ≤ devEntry κ s u x y then
              strongBernoulliWeight n ℓ κ s u else 0) +
            (if u₀ ≤ -devEntry κ s u x y then strongBernoulliWeight n ℓ κ s u else 0)) :=
            Finset.sum_le_sum fun u _ => hcover u
      _ = (∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
              (fun u => u₀ ≤ devEntry κ s u x y),
              strongBernoulliWeight n ℓ κ s u) +
            (∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
              (fun u => u₀ ≤ -devEntry κ s u x y),
              strongBernoulliWeight n ℓ κ s u) := by
            rw [Finset.sum_add_distrib, hfilpos, hfilneg]
  linarith

/-- Decomposes the difference between `uEntry` and the `pExp` kernel into `devEntry` and the
zero-string correction. -/
private theorem uEntry_sub_pExpEntry {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n)
    (u : Reg n → Bool) (x y : Reg n) :
    uEntry u x y - quadEntry (pExp κ s) x y =
      devEntry κ s u x y + (if u (ZeroStr n) then 1 else 0) / (Fintype.card (Reg n) : ℝ) := by
  have hzero : pExp κ s (ZeroStr n) = 0 := by
    unfold pExp
    simp
  have hchi0 : charSignR (ZeroStr n) (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) = 1 := charSignR_one_left _
  have hmain : uEntry u x y - quadEntry (pExp κ s) x y =
      (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, ((if u z then 1 else 0) - pExp κ s z) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) := by
    have hsplit' : ∀ z : Reg n,
        (if u z then 1 else 0) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) -
          pExp κ s z * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) =
        ((if u z then 1 else 0) - pExp κ s z) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) := fun _ => by ring
    unfold uEntry quadEntry
    rw [← mul_sub, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun z (_ : z ∈ Finset.univ) => hsplit' z]
  have hsplit : ∑ z : Reg n, ((if u z then 1 else 0) - pExp κ s z) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) =
      ∑ z ∈ (Finset.univ : Finset (Reg n)).filter (· ≠ ZeroStr n),
        ((if u z then 1 else 0) - pExp κ s z) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) +
      ((if u (ZeroStr n) then 1 else 0) - pExp κ s (ZeroStr n)) * charSignR (ZeroStr n)
        (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Reg n))
      (· ≠ ZeroStr n)
      (fun z => ((if u z then 1 else 0) - pExp κ s z) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y))]
    have hnf : (Finset.univ : Finset (Reg n)).filter (fun z => ¬z ≠ ZeroStr n) = {ZeroStr n} := by
      ext z
      simp
    rw [hnf]
    simp
  have hdev : devEntry κ s u x y =
      (∑ z ∈ (Finset.univ : Finset (Reg n)).filter (· ≠ ZeroStr n),
        ((if u z then 1 else 0) - pExp κ s z) * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y)) /
      (Fintype.card (Reg n) : ℝ) := by
    unfold devEntry devCoord
    rw [Finset.sum_div]
  rw [hmain, hsplit, hzero, hchi0, sub_zero, mul_one, hdev]
  field_simp

/-- Bounds the weighted probability that a kernel entry deviates from its `pExp` value by more
than the threshold divided by the nonzero sequence length. -/
private theorem entry_absdev_tail {n ℓ : ℕ} (κ : ℝ) (hκ : 0 ≤ κ) (s : Fin ℓ → Reg n)
    (x y : Reg n) {ρ : ℝ} (hρ : 0 ≤ ρ) (hℓ : ℓ ≠ 0) :
    ∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y|),
      strongBernoulliWeight n ℓ κ s u ≤
      2 * Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * (ℓ : ℝ) ^ 2))) := by
  have hℓℝ : ((ℓ : ℝ)) ≠ 0 := cast_ℓ_ne_zero hℓ
  have hu₀ : (0 : ℝ) ≤ ρ / (ℓ : ℝ) := div_nonneg hρ (by positivity)
  have hzero : ∀ u : Reg n → Bool, u (ZeroStr n) = true →
      strongBernoulliWeight n ℓ κ s u = 0 := by
    intro u hu
    rw [strongBernoulliWeight_eq_prod κ s u]
    have hz : bernFactor κ s (ZeroStr n) (u (ZeroStr n)) = 0 := by
      unfold bernFactor
      rw [ite_eq_left hu]
      exact pExp_zero κ s
    exact Finset.prod_eq_zero (f := fun y : Reg n => bernFactor κ s y (u y))
      (Finset.mem_univ (ZeroStr n)) hz
  have hptw : ∀ u : Reg n → Bool,
      (if ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y| then
        strongBernoulliWeight n ℓ κ s u else 0) ≤
      (if ρ / (ℓ : ℝ) ≤ |devEntry κ s u x y| then
        strongBernoulliWeight n ℓ κ s u else 0) := by
    intro u
    by_cases hu : u (ZeroStr n)
    · have hw : strongBernoulliWeight n ℓ κ s u = 0 := hzero u (by simp [hu])
      rw [hw]
      simp
    · have hEq : uEntry u x y - quadEntry (pExp κ s) x y = devEntry κ s u x y := by
        rw [uEntry_sub_pExpEntry κ s u x y, ite_eq_right (by simp [hu])]
        simp
      by_cases hc : ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y|
      · have hdevlt : ρ / (ℓ : ℝ) < |devEntry κ s u x y| := by
          rw [← hEq]
          exact hc
        rw [ite_eq_left hc, ite_eq_left (le_of_lt hdevlt)]
      · rw [ite_eq_right hc]
        by_cases h2 : ρ / (ℓ : ℝ) ≤ |devEntry κ s u x y|
        · rw [ite_eq_left h2]; exact strongBernoulliWeight_nonneg n ℓ κ hκ s u
        · rw [ite_eq_right h2]
  have hfilE : ∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y|),
        strongBernoulliWeight n ℓ κ s u =
      ∑ u : Reg n → Bool, (if ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y| then
        strongBernoulliWeight n ℓ κ s u else 0) :=
    by rw [Finset.sum_filter]
  have hfilD : ∑ u : Reg n → Bool, (if ρ / (ℓ : ℝ) ≤ |devEntry κ s u x y| then
        strongBernoulliWeight n ℓ κ s u else 0) =
      ∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => ρ / (ℓ : ℝ) ≤ |devEntry κ s u x y|),
        strongBernoulliWeight n ℓ κ s u :=
    by rw [Finset.sum_filter]
  have htail := devEntry_tail_two κ hκ s x y hu₀
  have hℓ2 : ((ℓ : ℝ)) ^ 2 ≠ 0 := pow_ne_zero 2 hℓℝ
  have hexpo : -((ρ / (ℓ : ℝ)) ^ 2 * (Fintype.card (Reg n) : ℝ) / 2)
      = -(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * (ℓ : ℝ) ^ 2)) := by
    rw [div_pow]
    field_simp
  rw [hfilE]
  refine le_trans (Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => hptw u)) ?_
  rw [hfilD]
  have h2 : 2 * Real.exp (-((ρ / (ℓ : ℝ)) ^ 2 * (Fintype.card (Reg n) : ℝ) / 2)) =
      2 * Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * (ℓ : ℝ) ^ 2))) := by
    rw [hexpo]
  exact le_trans htail (le_of_eq h2)

end EntryTail

section EntryBounds

/-- For a nonempty sequence satisfying `StrongGood`, each diagonal `bEntry` equals one half plus
half the parameter. -/
private theorem bEntry_diag {n ℓ : ℕ} (hℓ : ℓ ≠ 0) (κ : ℝ) (s : Fin ℓ → Reg n)
    (hgood : StrongGood s) (x : Reg n) :
    bEntry κ s x x = 1 / 2 + κ / 2 := by
  have hinj := strongGood_injective s hgood
  have hℓℝ : ((ℓ : ℝ)) ≠ 0 := cast_ℓ_ne_zero hℓ
  unfold bEntry
  rw [regXor_invol, ite_eq_left rfl, pairCount_zero_of_injective s hinj]
  have hterm : (κ / (2 * (ℓ : ℕ))) * ((ℓ : ℝ)) = κ / 2 := by
    field_simp
  rw [hterm]

/-- For a nonempty sequence satisfying `StrongGood` and a nonnegative parameter, off-diagonal
`bEntry` values lie between zero and the parameter divided by the length. -/
private theorem bEntry_offdiag {n ℓ : ℕ} (hℓ : ℓ ≠ 0) {κ : ℝ} (hκ : 0 ≤ κ)
    (s : Fin ℓ → Reg n) (hgood : StrongGood s) {x y : Reg n} (hxy : x ≠ y) :
    0 ≤ bEntry κ s x y ∧ bEntry κ s x y ≤ κ / (ℓ : ℝ) := by
  have hℓℝ : ((ℓ : ℝ)) ≠ 0 := cast_ℓ_ne_zero hℓ
  have hw : Qatlib.Concepts.WalshMoment.Forrelation.regXor x y ≠ ZeroStr n := fun h => hxy ((regXor_eq_zero x y).mp h)
  have hpc := pairCount_le_two s hgood hw
  have hκℓ : (0 : ℝ) ≤ κ / (ℓ : ℝ) := div_nonneg hκ (by positivity)
  unfold bEntry
  rw [ite_eq_right hw]
  constructor
  · have : (0 : ℝ) ≤ (κ / (2 * (ℓ : ℕ))) * ((pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) : ℕ) : ℝ) :=
      mul_nonneg (by positivity) (by positivity)
    simpa using! this
  · have h2 : ((2 : ℕ) : ℝ) = 2 := rfl
    have hterm : (κ / (2 * (ℓ : ℕ))) * ((pairCount s (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) : ℕ) : ℝ) ≤
        (κ / (2 * (ℓ : ℕ))) * (2 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast hpc
    have heq : (κ / (2 * (ℓ : ℕ))) * (2 : ℝ) = κ / (ℓ : ℝ) := by
      field_simp
    linarith

/-- Bounds the weighted probability of any excessive kernel-entry deviation on the sequence
support by the stated union-bound expression. -/
private theorem union_entry_tail {n ℓ : ℕ} (κ : ℝ) (hκ : 0 ≤ κ) (s : Fin ℓ → Reg n)
    (hgood : StrongGood s) {ρ : ℝ} (hρ : 0 ≤ ρ) (hℓ : ℓ ≠ 0) :
    ∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => ∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
          ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y|),
      strongBernoulliWeight n ℓ κ s u ≤
    2 * ((ℓ : ℝ)) ^ 2 * Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * (ℓ : ℝ) ^ 2))) := by
  have hℓℝ : ((ℓ : ℝ)) ≠ 0 := cast_ℓ_ne_zero hℓ
  set suppFin : Finset (Reg n) := Finset.univ.filter (fun x => multisetInd s x) with hsupp
  have hcard : suppFin.card = ℓ := by
    rw [hsupp]
    exact strongGood_supportCard s hgood

  have hind : ∀ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => ∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
          ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y|),
      strongBernoulliWeight n ℓ κ s u ≤
      ∑ x ∈ suppFin, ∑ y ∈ suppFin,
        (if ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y| then
          strongBernoulliWeight n ℓ κ s u else 0) := by
    intro u hu
    obtain ⟨x, y, hx, hy, hlt⟩ := (Finset.mem_filter.mp hu).2
    have hxm : x ∈ suppFin := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    have hym : y ∈ suppFin := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
    have hy : strongBernoulliWeight n ℓ κ s u ≤ ∑ y' ∈ suppFin,
        (if ρ / (ℓ : ℝ) < |uEntry u x y' - quadEntry (pExp κ s) x y'| then
          strongBernoulliWeight n ℓ κ s u else 0) := by
      refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.singleton_subset_iff.mpr hym) ?_)
      · rw [Finset.sum_singleton, ite_eq_left hlt]
      · intro y' _ _
        split
        · exact strongBernoulliWeight_nonneg n ℓ κ hκ s u
        · norm_num
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.singleton_subset_iff.mpr hxm) ?_)
    · rw [Finset.sum_singleton]
      exact hy
    · intro x' _ _
      apply Finset.sum_nonneg
      intro y' _
      split
      · exact strongBernoulliWeight_nonneg n ℓ κ hκ s u
      · norm_num

  have hswap : ∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => ∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
          ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y|),
      ∑ x ∈ suppFin, ∑ y ∈ suppFin,
        (if ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y| then
          strongBernoulliWeight n ℓ κ s u else 0) =
      ∑ x ∈ suppFin, ∑ y ∈ suppFin,
      ∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => ∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
          ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y|),
        (if ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y| then
          strongBernoulliWeight n ℓ κ s u else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm

  have hterm : ∀ x ∈ suppFin, ∀ y ∈ suppFin,
      (∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => ∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
          ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y|),
        (if ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y| then
          strongBernoulliWeight n ℓ κ s u else 0)) ≤
      2 * Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * (ℓ : ℝ) ^ 2))) := by
    intro x _ y _
    have hsub : (∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => ∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
          ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y|),
        (if ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y| then
          strongBernoulliWeight n ℓ κ s u else 0)) ≤
      ∑ u : Reg n → Bool,
        (if ρ / (ℓ : ℝ) < |uEntry u x y - quadEntry (pExp κ s) x y| then
          strongBernoulliWeight n ℓ κ s u else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun u _ _ => by
        split
        · exact strongBernoulliWeight_nonneg n ℓ κ hκ s u
        · norm_num)
    refine le_trans hsub ?_
    rw [← Finset.sum_filter]
    exact entry_absdev_tail κ hκ s x y hρ hℓ
  have hsum : ∑ x ∈ suppFin, ∑ y ∈ suppFin,
      (2 * Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * (ℓ : ℝ) ^ 2)))) =
      2 * ((ℓ : ℝ)) ^ 2 * Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * (ℓ : ℝ) ^ 2))) := by
    have hc : ∑ x ∈ suppFin, ∑ y ∈ suppFin,
        (2 * Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * (ℓ : ℝ) ^ 2)))) =
        (((suppFin.card : ℕ) : ℝ) * (((suppFin.card : ℕ)) : ℝ)) *
        (2 * Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * (ℓ : ℝ) ^ 2)))) := by
      rw [Finset.sum_const, Finset.sum_const]
      simp only [nsmul_eq_mul]
      ring
    rw [hc, hcard]
    ring
  refine le_trans (Finset.sum_le_sum (fun u hu => hind u hu)) ?_
  rw [hswap]
  refine le_trans (Finset.sum_le_sum fun x hx =>
    Finset.sum_le_sum fun y hy => hterm x hx y hy) ?_
  rw [hsum]

end EntryBounds

section SoundChain

/-- Diagonalizes the complex quadratic character kernel as a weighted sum of character sums
multiplied by their conjugates. -/
private theorem quad_char_identity_cplx {n : ℕ} (c : Reg n → ℝ) (φ : Reg n → ℂ) :
    (∑ x : Reg n, ∑ y : Reg n, (φ x * (starRingEnd ℂ (φ y))) *
      (quadEntry c x y : ℂ)) =
      ((Fintype.card (Reg n) : ℝ)⁻¹ : ℂ) *
        ∑ z : Reg n, (c z : ℂ) *
          ((∑ x : Reg n, φ x * (charSignR z x : ℂ)) *
            (starRingEnd ℂ (∑ y : Reg n, φ y * (charSignR z y : ℂ)))) := by
  have hcast : ∀ (z x y : Reg n),
      (((Fintype.card (Reg n) : ℝ)⁻¹ * (c z * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y)) : ℝ) : ℂ) =
        ((Fintype.card (Reg n) : ℝ)⁻¹ : ℂ) *
          ((c z : ℂ) * ((charSignR z x : ℂ) * (charSignR z y : ℂ))) := by
    intro z x y
    rw [show charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y) = charSignR z x * charSignR z y from
      (charSignR_mul z x y).symm]
    push_cast
    ring
  have h1 : ∀ (x y : Reg n), (quadEntry c x y : ℂ) =
      ∑ z : Reg n,
        (((Fintype.card (Reg n) : ℝ)⁻¹ * (c z * charSignR z (Qatlib.Concepts.WalshMoment.Forrelation.regXor x y)) : ℝ) : ℂ) := by
    intro x y
    unfold quadEntry
    rw [Finset.mul_sum, Complex.ofReal_sum]
  have step1 : (∑ x : Reg n, ∑ y : Reg n, (φ x * (starRingEnd ℂ (φ y))) *
      (quadEntry c x y : ℂ)) =
      ∑ x : Reg n, ∑ y : Reg n, ∑ z : Reg n,
        (φ x * (starRingEnd ℂ (φ y))) *
          (((Fintype.card (Reg n) : ℝ)⁻¹ : ℂ) *
            ((c z : ℂ) * ((charSignR z x : ℂ) * (charSignR z y : ℂ)))) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [h1 x y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hcast z x y]
  have step2 : (∑ x : Reg n, ∑ y : Reg n, ∑ z : Reg n,
      (φ x * (starRingEnd ℂ (φ y))) *
        (((Fintype.card (Reg n) : ℝ)⁻¹ : ℂ) *
          ((c z : ℂ) * ((charSignR z x : ℂ) * (charSignR z y : ℂ))))) =
      ∑ z : Reg n, ∑ x : Reg n, ∑ y : Reg n,
      (φ x * (starRingEnd ℂ (φ y))) *
        (((Fintype.card (Reg n) : ℝ)⁻¹ : ℂ) *
          ((c z : ℂ) * ((charSignR z x : ℂ) * (charSignR z y : ℂ)))) :=
    Eq.trans
      (sum_comm3 (fun x y z : Reg n =>
        (φ x * (starRingEnd ℂ (φ y))) *
          (((Fintype.card (Reg n) : ℝ)⁻¹ : ℂ) *
            ((c z : ℂ) * ((charSignR z x : ℂ) * (charSignR z y : ℂ))))))
      (sum_comm3 (fun a b d : Reg n =>
        (φ d * (starRingEnd ℂ (φ a))) *
          (((Fintype.card (Reg n) : ℝ)⁻¹ : ℂ) *
            ((c b : ℂ) * ((charSignR b d : ℂ) * (charSignR b a : ℂ))))))
  have hconj : ∀ (z : Reg n),
      (starRingEnd ℂ (∑ y : Reg n, φ y * (charSignR z y : ℂ))) =
        ∑ y : Reg n, (starRingEnd ℂ (φ y)) * (charSignR z y : ℂ) := by
    intro z
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, Complex.conj_ofReal]
  rw [step1, step2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hpre : ∀ x y : Reg n,
      (φ x * (starRingEnd ℂ (φ y))) *
        (((Fintype.card (Reg n) : ℝ)⁻¹ : ℂ) *
          ((c z : ℂ) * ((charSignR z x : ℂ) * (charSignR z y : ℂ)))) =
      (((Fintype.card (Reg n) : ℝ)⁻¹ : ℂ) * (c z : ℂ)) *
        ((φ x * (charSignR z x : ℂ)) *
          (starRingEnd ℂ (φ y) * (charSignR z y : ℂ))) := fun _ _ => by ring
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hpre x y))]
  have hpull : ∀ (K : ℂ) (f g : Reg n → ℂ),
      (∑ x : Reg n, ∑ y : Reg n, K * (f x * g y)) =
        K * ((∑ x : Reg n, f x) * ∑ y : Reg n, g y) := by
    intro K f g
    have inner : ∀ x : Reg n,
        (∑ y : Reg n, K * (f x * g y)) = f x * (K * ∑ y : Reg n, g y) := by
      intro x
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => inner x), ← Finset.sum_mul]
    ring
  rw [hpull (((Fintype.card (Reg n) : ℝ)⁻¹ : ℂ) * (c z : ℂ))
      (fun x => φ x * (charSignR z x : ℂ))
      (fun y => (starRingEnd ℂ (φ y)) * (charSignR z y : ℂ)),
    hconj z]
  ring

/-- Expresses the real part of the complex quadratic character kernel as a normalized weighted
sum of squared norms of character sums. -/
private theorem quad_char_identity_cplx_re {n : ℕ} (c : Reg n → ℝ) (φ : Reg n → ℂ) :
    (∑ x : Reg n, ∑ y : Reg n,
        ((φ x * (starRingEnd ℂ (φ y))) * (quadEntry c x y : ℂ)).re) =
      (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, c z * Complex.normSq (∑ x : Reg n, φ x * (charSignR z x : ℂ)) := by
  have hkey : ∀ z : Reg n,
      ((c z : ℂ) * ((∑ x : Reg n, φ x * (charSignR z x : ℂ)) *
          (starRingEnd ℂ (∑ y : Reg n, φ y * (charSignR z y : ℂ))))) =
        Complex.ofReal (c z *
          Complex.normSq (∑ x : Reg n, φ x * (charSignR z x : ℂ))) := by
    intro z
    have hinner : ((∑ x : Reg n, φ x * (charSignR z x : ℂ)) *
          (starRingEnd ℂ (∑ y : Reg n, φ y * (charSignR z y : ℂ)))) =
        Complex.ofReal
          (Complex.normSq (∑ x : Reg n, φ x * (charSignR z x : ℂ))) := by
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
    rw [hinner, ← Complex.ofReal_mul]
  have hlhs : ((∑ x : Reg n, ∑ y : Reg n,
        (φ x * (starRingEnd ℂ (φ y))) * (quadEntry c x y : ℂ))).re =
      ∑ x : Reg n, ∑ y : Reg n,
        ((φ x * (starRingEnd ℂ (φ y))) * (quadEntry c x y : ℂ)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [Complex.re_sum]
  have hrhs : Complex.ofReal ((Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, c z * Complex.normSq (∑ x : Reg n, φ x * (charSignR z x : ℂ))) =
      ((Fintype.card (Reg n) : ℝ)⁻¹ : ℂ) *
        ∑ z : Reg n, (c z : ℂ) *
          ((∑ x : Reg n, φ x * (charSignR z x : ℂ)) *
            (starRingEnd ℂ (∑ y : Reg n, φ y * (charSignR z y : ℂ)))) := by
    rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sum]
    exact congrArg _ (Finset.sum_congr rfl fun z _ => (hkey z).symm)
  rw [← hlhs, quad_char_identity_cplx c φ, ← hrhs, Complex.ofReal_re]

/-- For a nonnegative parameter, `pExp` is bounded above by `bCoeff` pointwise. -/
private theorem pExp_le_bCoeff {n ℓ : ℕ} {κ : ℝ} (hκ : 0 ≤ κ) (s : Fin ℓ → Reg n)
    (z : Reg n) : pExp κ s z ≤ bCoeff κ s z := by
  by_cases hz : z = ZeroStr n
  · have hg := gammaOfMultiset_nonneg n ℓ s z
    have hnn : (0 : ℝ) ≤ κ / 2 * gammaOfMultiset n ℓ s z := mul_nonneg (by positivity) hg
    unfold pExp bCoeff
    rw [ite_eq_left hz]
    have h2 : (0 : ℝ) ≤ 1 / 2 + κ / 2 * gammaOfMultiset n ℓ s z := by linarith
    linarith
  · unfold pExp
    rw [ite_eq_right hz]
    exact (aCoeff_le_pAll_le_bCoeff κ hκ s z).2

/-- For a nonnegative parameter, `bCoeff` is pointwise nonnegative. -/
private theorem bCoeff_nonneg {n ℓ : ℕ} {κ : ℝ} (hκ : 0 ≤ κ) (s : Fin ℓ → Reg n)
    (z : Reg n) : 0 ≤ bCoeff κ s z := by
  have hg := gammaOfMultiset_nonneg n ℓ s z
  have hnn : (0 : ℝ) ≤ κ / 2 * gammaOfMultiset n ℓ s z := mul_nonneg (by positivity) hg
  unfold bCoeff
  linarith

/-- The real part of a complex number times the conjugate of another is at most the product of
their norms. -/
private theorem re_le_norm_mul {a b : ℂ} : (a * (starRingEnd ℂ b)).re ≤ ‖a‖ * ‖b‖ := by
  have h1 : (a * (starRingEnd ℂ b)).re ≤ |(a * (starRingEnd ℂ b)).re| := le_abs_self _
  have h2 : |(a * (starRingEnd ℂ b)).re| ≤ ‖a * (starRingEnd ℂ b)‖ :=
    RCLike.abs_re_le_norm (a * (starRingEnd ℂ b))
  rw [norm_mul, Complex.norm_conj] at h2
  exact le_trans h1 h2

/-- The absolute real part of a complex number times the conjugate of another is at most the
product of their norms. -/
private theorem abs_re_le_norm_mul {a b : ℂ} :
    |(a * (starRingEnd ℂ b)).re| ≤ ‖a‖ * ‖b‖ := by
  have h := re_le_norm_mul (a := a) (b := b)
  have h' := re_le_norm_mul (a := -a) (b := b)
  rw [neg_mul, Complex.neg_re, norm_neg] at h'
  exact abs_le.2 ⟨by linarith, h⟩

/-- For a vector supported on at most `m` points with squared norm sum at most one, the square
of the sum of norms is at most `m`. -/
private theorem ind_sum_sq_le {n : ℕ} (Δ : Reg n → Bool) (φ : Reg n → ℂ)
    (hφ : ∀ x : Reg n, ‖φ x‖ = (if Δ x then 1 else 0) * ‖φ x‖)
    (hsq : ∑ x : Reg n, ‖φ x‖ ^ 2 ≤ 1) {m : ℕ} (hm : supportCard Δ ≤ m) :
    (∑ x : Reg n, ‖φ x‖) ^ 2 ≤ (m : ℝ) := by
  have h1 : ∑ x : Reg n, ‖φ x‖ = ∑ x ∈ Finset.univ.filter (fun x => Δ x), ‖φ x‖ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : Δ x
    · rw [ite_eq_left hx]
    · rw [ite_eq_right hx, hφ x, ite_eq_right hx, zero_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.filter (fun x => Δ x))
    (fun x => ‖φ x‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow] at hcs
  have hsub : ∑ x ∈ Finset.univ.filter (fun x => Δ x), ‖φ x‖ ^ 2 ≤ 1 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_) hsq
    intro x _ _
    exact sq_nonneg _
  have hone : ∑ _x ∈ Finset.univ.filter (fun x => Δ x), (1 : ℝ) =
      ((Finset.univ.filter (fun x => Δ x)).card : ℝ) := by
    rw [Finset.sum_const, Nat.smul_one_eq_cast]
  have hcardle : ((Finset.univ.filter (fun x => Δ x)).card : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  calc (∑ x : Reg n, ‖φ x‖) ^ 2
      = (∑ x ∈ Finset.univ.filter (fun x => Δ x), ‖φ x‖) ^ 2 := by rw [h1]
    _ ≤ (∑ x ∈ Finset.univ.filter (fun x => Δ x), ‖φ x‖ ^ 2) *
          ∑ _x ∈ Finset.univ.filter (fun x => Δ x), (1 : ℝ) := hcs
    _ = (∑ x ∈ Finset.univ.filter (fun x => Δ x), ‖φ x‖ ^ 2) *
          ((Finset.univ.filter (fun x => Δ x)).card : ℝ) := by rw [hone]
    _ ≤ 1 * (m : ℝ) := mul_le_mul hsub hcardle (Nat.cast_nonneg _) zero_le_one
    _ = (m : ℝ) := by norm_num

/-- Under the stated support, goodness, parameter, and entry-deviation assumptions, bounds
`spectralForrelation` by half of one plus the parameter, plus the relative support size and
deviation allowance. -/
private theorem sound_chain {n ℓ : ℕ} (hℓ : ℓ ≠ 0) {κ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (s : Fin ℓ → Reg n) (hgood : StrongGood s) (u : Reg n → Bool)
    (hu0 : u (ZeroStr n) = false) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdev : ∀ x y : Reg n, multisetInd s x → multisetInd s y →
      |uEntry u x y - quadEntry (pExp κ s) x y| ≤ ρ / (ℓ : ℝ))
    (Δ : Reg n → Bool) (hsub : ∀ x : Reg n, Δ x → multisetInd s x)
    {v : ℕ} (hv : supportCard Δ ≤ v) :
    spectralForrelation n Δ u ≤ (1 + κ) / 2 + (v : ℝ) / (ℓ : ℝ) + ρ := by
  have hℓℝ : ((ℓ : ℝ)) ≠ 0 := cast_ℓ_ne_zero hℓ
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by positivity
  have hnnB : (0 : ℝ) ≤ κ / (ℓ : ℝ) := div_nonneg hκ hℓpos.le
  obtain ⟨ψ, hψnorm, hmass⟩ :=
    (spectralForrelationBasics n Δ u).2.2.2.1 (spectralForrelation n Δ u) le_rfl

  have huEq : ∀ x y : Reg n,
      uEntry u x y = quadEntry (pExp κ s) x y + devEntry κ s u x y := by
    intro x y
    have h := uEntry_sub_pExpEntry κ s u x y
    rw [hu0] at h
    simp at h
    linarith

  have hmassE : forrWitnessMass n Δ u ψ =
      ∑ x : Reg n, ∑ y : Reg n,
        ((ψ x * (starRingEnd ℂ (ψ y))).re * (if Δ x then 1 else 0) * (if Δ y then 1 else 0) *
          quadEntry (pExp κ s) x y) +
      ∑ x : Reg n, ∑ y : Reg n,
        ((ψ x * (starRingEnd ℂ (ψ y))).re * (if Δ x then 1 else 0) * (if Δ y then 1 else 0) *
          devEntry κ s u x y) := by
    rw [forrWitnessMass_eq_quad Δ u ψ]
    simp only [← mul_assoc]
    have hsplit : ∀ x y : Reg n,
        ((ψ x * (starRingEnd ℂ (ψ y))).re * (if Δ x then 1 else 0) * (if Δ y then 1 else 0) *
          uEntry u x y) =
        ((ψ x * (starRingEnd ℂ (ψ y))).re * (if Δ x then 1 else 0) * (if Δ y then 1 else 0) *
          quadEntry (pExp κ s) x y) +
        ((ψ x * (starRingEnd ℂ (ψ y))).re * (if Δ x then 1 else 0) * (if Δ y then 1 else 0) *
          devEntry κ s u x y) := by
      intro x y
      rw [huEq x y]
      ring
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hsplit x y))]
    simp only [Finset.sum_add_distrib]

  set φ : Reg n → ℂ := fun x => if Δ x then ψ x else 0 with hφdef
  have hφnorm : ∀ x : Reg n, ‖φ x‖ = (if Δ x then 1 else 0) * ‖φ x‖ := by
    intro x
    by_cases hx : Δ x
    · rw [hφdef]
      simp [hx]
    · rw [hφdef]
      simp [hx]
  have hφsq : ∑ x : Reg n, ‖φ x‖ ^ 2 ≤ 1 := by
    have hle : ∀ x : Reg n, ‖φ x‖ ^ 2 ≤ ‖ψ x‖ ^ 2 := by
      intro x
      by_cases hx : Δ x
      · rw [hφdef]
        simp [hx]
      · rw [hφdef]
        simp [hx]
    refine le_trans (Finset.sum_le_sum fun x _ => hle x) ?_
    exact le_of_eq hψnorm

  have hbridge : ∀ x y : Reg n,
      ((φ x * (starRingEnd ℂ (φ y)) * (quadEntry (pExp κ s) x y : ℂ)).re) =
      (ψ x * (starRingEnd ℂ (ψ y))).re * (if Δ x then 1 else 0) * (if Δ y then 1 else 0) *
        quadEntry (pExp κ s) x y := by
    intro x y
    by_cases hx : Δ x <;> by_cases hy : Δ y <;>
      simp [hφdef, hx, hy, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hE1 : ∑ x : Reg n, ∑ y : Reg n,
      ((ψ x * (starRingEnd ℂ (ψ y))).re * (if Δ x then 1 else 0) * (if Δ y then 1 else 0) *
        quadEntry (pExp κ s) x y) =
      (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, pExp κ s z * Complex.normSq
          (∑ x : Reg n, φ x * (charSignR z x : ℂ)) := by
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => (hbridge x y).symm))]
    exact quad_char_identity_cplx_re (pExp κ s) φ
  have hE2 : (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, pExp κ s z * Complex.normSq (∑ x : Reg n, φ x * (charSignR z x : ℂ)) ≤
      (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, bCoeff κ s z * Complex.normSq (∑ x : Reg n, φ x * (charSignR z x : ℂ)) :=
    mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) =>
        mul_le_mul_of_nonneg_right (pExp_le_bCoeff hκ s z) (Complex.normSq_nonneg _))
      (inv_nonneg.mpr (card_reg_pos n).le)
  have hE3 : (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, bCoeff κ s z * Complex.normSq (∑ x : Reg n, φ x * (charSignR z x : ℂ)) =
      ∑ x : Reg n, ∑ y : Reg n, ((φ x * (starRingEnd ℂ (φ y))).re * bEntry κ s x y) := by
    rw [← quad_char_identity_cplx_re (bCoeff κ s) φ]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [quadEntry_bCoeff_eq hℓ κ s x y]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

  have hentry : ∀ x y : Reg n,
      ((φ x * (starRingEnd ℂ (φ y))).re * bEntry κ s x y) ≤
      ‖φ x‖ * ‖φ y‖ * (if x = y then 1 / 2 + κ / 2 else κ / (ℓ : ℝ)) := by
    intro x y
    have hA : (0 : ℝ) ≤ 1 / 2 + κ / 2 := by
      have : (0 : ℝ) ≤ κ / 2 := div_nonneg hκ zero_le_two
      linarith
    by_cases hxy : x = y
    · subst hxy
      rw [ite_eq_left rfl, bEntry_diag hℓ κ s hgood x]
      exact mul_le_mul (re_le_norm_mul (a := φ x) (b := φ x)) (le_refl _)
        hA (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    · rw [ite_eq_right hxy]
      have hb := bEntry_offdiag hℓ hκ s hgood hxy
      exact mul_le_mul (re_le_norm_mul (a := φ x) (b := φ y)) hb.2
        hb.1 (mul_nonneg (norm_nonneg _) (norm_nonneg _))

  have hsplitW : ∀ x y : Reg n,
      ‖φ x‖ * ‖φ y‖ * (if x = y then 1 / 2 + κ / 2 else κ / (ℓ : ℝ)) ≤
      (1 / 2 + κ / 2) * (‖φ x‖ * ‖φ x‖ * (if x = y then (1 : ℝ) else 0)) +
        κ / (ℓ : ℝ) * (‖φ x‖ * ‖φ y‖) := by
    intro x y
    have hnn : (0 : ℝ) ≤ ‖φ x‖ * ‖φ x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hB : (0 : ℝ) ≤ κ / (ℓ : ℝ) * (‖φ x‖ * ‖φ x‖) := mul_nonneg hnnB hnn
    by_cases hxy : x = y
    · subst hxy
      rw [ite_eq_left rfl, ite_eq_left rfl]
      linarith
    · rw [ite_eq_right hxy, ite_eq_right hxy, mul_zero, mul_zero, zero_add]
      exact le_of_eq (by ring)
  have hinner0 : ∀ x : Reg n,
      (∑ y : Reg n, (1 / 2 + κ / 2) * (‖φ x‖ * ‖φ x‖ * (if x = y then (1 : ℝ) else 0))) =
      (1 / 2 + κ / 2) * (‖φ x‖ * ‖φ x‖) := by
    intro x
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hi : ∑ y : Reg n, (if x = y then (1 : ℝ) else 0) = 1 := by
      simp
    rw [hi]
    ring
  have hsumW : (∑ x : Reg n, ∑ y : Reg n,
      ((1 / 2 + κ / 2) * (‖φ x‖ * ‖φ x‖ * (if x = y then (1 : ℝ) else 0)) +
        κ / (ℓ : ℝ) * (‖φ x‖ * ‖φ y‖))) =
      (1 / 2 + κ / 2) * (∑ x : Reg n, ‖φ x‖ * ‖φ x‖) +
        κ / (ℓ : ℝ) * ((∑ x : Reg n, ‖φ x‖) * ∑ y : Reg n, ‖φ y‖) := by
    have h1 : ∑ x : Reg n, ∑ y : Reg n,
        (1 / 2 + κ / 2) * (‖φ x‖ * ‖φ x‖ * (if x = y then (1 : ℝ) else 0)) =
        (1 / 2 + κ / 2) * (∑ x : Reg n, ‖φ x‖ * ‖φ x‖) := by
      rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hinner0 x), ← Finset.mul_sum]
    have h2 : ∑ x : Reg n, ∑ y : Reg n, κ / (ℓ : ℝ) * (‖φ x‖ * ‖φ y‖) =
        κ / (ℓ : ℝ) * ((∑ x : Reg n, ‖φ x‖) * ∑ y : Reg n, ‖φ y‖) := by
      simp only [← Finset.mul_sum, Finset.sum_mul_sum]
    simp only [Finset.sum_add_distrib]
    rw [h1, h2]
  have hsqv : (∑ x : Reg n, ‖φ x‖) ^ 2 ≤ (v : ℝ) :=
    ind_sum_sq_le Δ φ hφnorm hφsq hv
  have hsubfin : (Finset.univ.filter (fun x => Δ x)) ⊆
      (Finset.univ.filter (fun x => multisetInd s x)) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub x (Finset.mem_filter.mp hx).2⟩
  have hcardΔℓ : supportCard Δ ≤ ℓ := by
    calc supportCard Δ = (Finset.univ.filter (fun x => Δ x)).card := rfl
      _ ≤ (Finset.univ.filter (fun x => multisetInd s x)).card := Finset.card_le_card hsubfin
      _ = ℓ := strongGood_supportCard s hgood
  have hsql : (∑ x : Reg n, ‖φ x‖) ^ 2 ≤ (ℓ : ℝ) :=
    ind_sum_sq_le Δ φ hφnorm hφsq hcardΔℓ

  have hEsum : ∑ x : Reg n, ∑ y : Reg n,
      ((φ x * (starRingEnd ℂ (φ y))).re * bEntry κ s x y) ≤
      (1 / 2 + κ / 2) * 1 + κ / (ℓ : ℝ) * ((v : ℝ) * 1) := by
    have hA : (0 : ℝ) ≤ 1 / 2 + κ / 2 := by
      have : (0 : ℝ) ≤ κ / 2 := div_nonneg hκ zero_le_two
      linarith
    refine le_trans (Finset.sum_le_sum fun x _ =>
      Finset.sum_le_sum fun y _ => hentry x y) ?_
    refine le_trans (Finset.sum_le_sum fun x _ =>
      Finset.sum_le_sum fun y _ => hsplitW x y) ?_
    rw [hsumW]
    have hleft : (1 / 2 + κ / 2) * (∑ x : Reg n, ‖φ x‖ * ‖φ x‖) ≤
        (1 / 2 + κ / 2) * 1 := by
      refine mul_le_mul_of_nonneg_left ?_ hA
      exact le_trans (Finset.sum_le_sum fun x _ => by rw [sq]) hφsq
    have hright : κ / (ℓ : ℝ) * ((∑ x : Reg n, ‖φ x‖) * ∑ y : Reg n, ‖φ y‖) ≤
        κ / (ℓ : ℝ) * ((v : ℝ) * 1) := by
      refine mul_le_mul_of_nonneg_left ?_ hnnB
      have hsq : (∑ x : Reg n, ‖φ x‖) * ∑ y : Reg n, ‖φ y‖
          = (∑ x : Reg n, ‖φ x‖) ^ 2 := by rw [sq]
      rw [hsq]
      linarith
    linarith

  have hDentry : ∀ x y : Reg n,
      |((ψ x * (starRingEnd ℂ (ψ y))).re * (if Δ x then 1 else 0) * (if Δ y then 1 else 0) *
        devEntry κ s u x y)| ≤
      ((if Δ x then 1 else 0) * (if Δ y then 1 else 0)) * (‖φ x‖ * ‖φ y‖) * (ρ / (ℓ : ℝ)) := by
    intro x y
    by_cases hx : Δ x
    · by_cases hy : Δ y
      · rw [ite_eq_left hx, ite_eq_left hy]
        have hR : (ψ x * (starRingEnd ℂ (ψ y))).re =
            (φ x * (starRingEnd ℂ (φ y))).re := by
          rw [hφdef]
          simp [hx, hy]
        have hdeq : devEntry κ s u x y =
            uEntry u x y - quadEntry (pExp κ s) x y := by
          rw [huEq x y]
          ring
        have hd : |devEntry κ s u x y| ≤ ρ / (ℓ : ℝ) := by
          rw [hdeq]
          exact hdev x y (hsub x hx) (hsub y hy)
        rw [hR]
        have habs : |(φ x * (starRingEnd ℂ (φ y))).re| ≤ ‖φ x‖ * ‖φ y‖ :=
          abs_re_le_norm_mul (a := φ x) (b := φ y)
        calc |(φ x * (starRingEnd ℂ (φ y))).re * 1 * 1 * devEntry κ s u x y|
            = |(φ x * (starRingEnd ℂ (φ y))).re| * |devEntry κ s u x y| := by
                rw [mul_one, mul_one, abs_mul]
          _ ≤ (‖φ x‖ * ‖φ y‖) * (ρ / (ℓ : ℝ)) :=
              mul_le_mul habs hd (abs_nonneg _)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = (1 * 1) * (‖φ x‖ * ‖φ y‖) * (ρ / (ℓ : ℝ)) := by ring
      · rw [ite_eq_left hx, ite_eq_right hy]
        simp
    · rw [ite_eq_right hx]
      simp
  have hDabs : |(∑ x : Reg n, ∑ y : Reg n,
      ((ψ x * (starRingEnd ℂ (ψ y))).re * (if Δ x then 1 else 0) * (if Δ y then 1 else 0) *
        devEntry κ s u x y))| ≤ ρ := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ Finset.univ) ?_
    refine le_trans (Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ Finset.univ) ?_
    refine le_trans (Finset.sum_le_sum fun x _ =>
      Finset.sum_le_sum fun y _ => hDentry x y) ?_
    have hentry' : ∀ x y : Reg n,
        ((if Δ x then 1 else 0) * (if Δ y then 1 else 0)) * (‖φ x‖ * ‖φ y‖) * (ρ / (ℓ : ℝ)) =
        ((if Δ x then 1 else 0) * ‖φ x‖) * ((if Δ y then 1 else 0) * ‖φ y‖) * (ρ / (ℓ : ℝ)) :=
      fun _ _ => by ring
    have hsumI : (∑ x : Reg n, (if Δ x then 1 else 0) * ‖φ x‖) = ∑ x : Reg n, ‖φ x‖ :=
      Finset.sum_congr rfl fun x _ => (hφnorm x).symm
    have hsum0 : (∑ x : Reg n, ∑ y : Reg n,
        ((if Δ x then 1 else 0) * (if Δ y then 1 else 0)) * (‖φ x‖ * ‖φ y‖) * (ρ / (ℓ : ℝ))) =
        (ρ / (ℓ : ℝ)) * ((∑ x : Reg n, (if Δ x then 1 else 0) * ‖φ x‖) *
          ∑ x : Reg n, (if Δ x then 1 else 0) * ‖φ x‖) := by
      rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
        Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hentry' x y))]
      simp only [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul_sum]
      ring
    rw [hsum0, hsumI]
    have hsq : (∑ x : Reg n, ‖φ x‖) * (∑ x : Reg n, ‖φ x‖) =
        (∑ x : Reg n, ‖φ x‖) ^ 2 := by rw [sq]
    rw [hsq]
    have hmul : (ρ / (ℓ : ℝ)) * (ℓ : ℝ) = ρ := by field_simp
    calc (ρ / (ℓ : ℝ)) * (∑ x : Reg n, ‖φ x‖) ^ 2 ≤ (ρ / (ℓ : ℝ)) * (ℓ : ℝ) :=
        mul_le_mul_of_nonneg_left hsql (div_nonneg hρ hℓpos.le)
      _ = ρ := hmul

  have hDle : (∑ x : Reg n, ∑ y : Reg n,
      ((ψ x * (starRingEnd ℂ (ψ y))).re * (if Δ x then 1 else 0) * (if Δ y then 1 else 0) *
        devEntry κ s u x y)) ≤ ρ :=
    le_trans (le_abs_self _) hDabs
  have hEle : (∑ x : Reg n, ∑ y : Reg n,
      ((ψ x * (starRingEnd ℂ (ψ y))).re * (if Δ x then 1 else 0) * (if Δ y then 1 else 0) *
        quadEntry (pExp κ s) x y)) ≤ (1 + κ) / 2 + (v : ℝ) / (ℓ : ℝ) := by
    have hc : (∑ x : Reg n, ∑ y : Reg n,
        ((ψ x * (starRingEnd ℂ (ψ y))).re * (if Δ x then 1 else 0) * (if Δ y then 1 else 0) *
          quadEntry (pExp κ s) x y)) ≤
        (1 / 2 + κ / 2) * 1 + κ / (ℓ : ℝ) * ((v : ℝ) * 1) := by
      calc (∑ x : Reg n, ∑ y : Reg n,
          ((ψ x * (starRingEnd ℂ (ψ y))).re * (if Δ x then 1 else 0) * (if Δ y then 1 else 0) *
            quadEntry (pExp κ s) x y))
          = (Fintype.card (Reg n) : ℝ)⁻¹ *
              ∑ z : Reg n, pExp κ s z * Complex.normSq
                (∑ x : Reg n, φ x * (charSignR z x : ℂ)) := hE1
        _ ≤ (Fintype.card (Reg n) : ℝ)⁻¹ *
              ∑ z : Reg n, bCoeff κ s z * Complex.normSq
                (∑ x : Reg n, φ x * (charSignR z x : ℂ)) := hE2
        _ = ∑ x : Reg n, ∑ y : Reg n,
              ((φ x * (starRingEnd ℂ (φ y))).re * bEntry κ s x y) := hE3
        _ ≤ (1 / 2 + κ / 2) * 1 + κ / (ℓ : ℝ) * ((v : ℝ) * 1) := hEsum
    have hκv : κ / (ℓ : ℝ) * ((v : ℝ) * 1) ≤ (v : ℝ) / (ℓ : ℝ) := by
      have hvκ : κ * (v : ℝ) ≤ (v : ℝ) := by
        have h1 := mul_le_mul_of_nonneg_left hκ1 (Nat.cast_nonneg v)
        linarith
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hℓpos hℓpos]
      have hkey : κ * ((v : ℝ) * 1) * (ℓ : ℝ) ≤ (v : ℝ) * (ℓ : ℝ) := by
        have h1 : κ * ((v : ℝ) * 1) = κ * (v : ℝ) := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_right hvκ hℓpos.le
      exact hkey
    have h1 : (1 / 2 + κ / 2) * 1 = (1 + κ) / 2 := by ring
    linarith
  refine le_trans hmass ?_
  rw [hmassE]
  linarith

end SoundChain

section Completeness

/-- A Boolean register function that is true at the zero string has zero strong Bernoulli
weight. -/
private theorem bernWeight_zero_of_u0 {n ℓ : ℕ} (κ : ℝ) (s : Fin ℓ → Reg n)
    (u : Reg n → Bool) (hu0 : u (ZeroStr n) = true) :
    strongBernoulliWeight n ℓ κ s u = 0 := by
  rw [strongBernoulliWeight_eq_prod κ s u]
  have hz : bernFactor κ s (ZeroStr n) (u (ZeroStr n)) = 0 := by
    unfold bernFactor
    rw [ite_eq_left hu0]
    exact pExp_zero κ s
  exact Finset.prod_eq_zero (f := fun y : Reg n => bernFactor κ s y (u y))
    (Finset.mem_univ (ZeroStr n)) hz

/-- For an injective sequence, the square of the character sum over its support equals
`rawGamma`. -/
private theorem supp_charSum_sq {n ℓ : ℕ} (s : Fin ℓ → Reg n)
    (hinj : Function.Injective s) (z : Reg n) :
    (∑ x ∈ Finset.univ.filter (fun x => multisetInd s x), charSignR z x) ^ 2
      = rawGamma s z := by
  have himg : (Finset.univ.filter (fun x => multisetInd s x)) = Finset.univ.image s := by
    ext x
    simp [multisetInd]
  have h1 : (∑ x ∈ Finset.univ.filter (fun x => multisetInd s x), charSignR z x)
      = ∑ i : Fin ℓ, charSignR z (s i) := by
    rw [himg, Finset.sum_image]
    exact fun a _ b _ hab => hinj hab
  rw [h1]
  unfold rawGamma
  rw [sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    charSignR_mul z (s i) (s j)

/-- For an injective sequence, the square of its support-indicator character sum equals the
length times `gammaOfMultiset`. -/
private theorem supp_charSum_sq' {n ℓ : ℕ} (s : Fin ℓ → Reg n)
    (hinj : Function.Injective s) (z : Reg n) :
    (∑ x : Reg n, (if multisetInd s x then (1 : ℝ) else 0) * charSignR z x) ^ 2
      = ((ℓ : ℝ)) * gammaOfMultiset n ℓ s z := by
  have hfil : (∑ x : Reg n, (if multisetInd s x then (1 : ℝ) else 0) * charSignR z x)
      = ∑ x ∈ Finset.univ.filter (fun x => multisetInd s x), charSignR z x := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun x _ => by
      by_cases hx : multisetInd s x <;> simp [hx]
  rw [hfil, supp_charSum_sq s hinj z, gamma_mul_ell]

/-- For a nonempty injective sequence, the normalized quadratic sum over its support equals the
normalized coefficient-weighted sum of `gammaOfMultiset`. -/
private theorem flat_quad_entry_eq {n ℓ : ℕ} (hℓ : ℓ ≠ 0) (c : Reg n → ℝ)
    (s : Fin ℓ → Reg n) (hinj : Function.Injective s) :
    ((ℓ : ℝ))⁻¹ * (∑ x : Reg n, ∑ y : Reg n,
        (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
          quadEntry c x y) =
      (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, c z * gammaOfMultiset n ℓ s z := by
  rw [quad_diff_eq c (fun x => if multisetInd s x then (1 : ℝ) else 0)]
  simp only [supp_charSum_sq' s hinj]
  field_simp
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- For a nonempty injective sequence, the flat quadratic expression for `pExp` equals its
normalized `gammaOfMultiset`-weighted sum. -/
private theorem flat_E_eq {n ℓ : ℕ} (hℓ : ℓ ≠ 0) (κ : ℝ) (s : Fin ℓ → Reg n)
    (hinj : Function.Injective s) :
    ((ℓ : ℝ))⁻¹ * (∑ x : Reg n, ∑ y : Reg n,
        (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
          quadEntry (pExp κ s) x y) =
      (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, pExp κ s z * gammaOfMultiset n ℓ s z :=
  flat_quad_entry_eq hℓ (pExp κ s) s hinj

/-- For a nonempty sequence satisfying `StrongGood` and a nonnegative parameter, establishes the
stated explicit lower bound on the normalized `pExp`-weighted gamma sum. -/
private theorem flat_E_ge {n ℓ : ℕ} (hℓ : ℓ ≠ 0) {κ : ℝ} (hκ : 0 ≤ κ)
    (s : Fin ℓ → Reg n) (hgood : StrongGood s) :
    1 / 2 + 3 * κ / 2 - κ / (ℓ : ℝ) - 15 * κ ^ 2 / 4 -
        ((ℓ : ℝ) / (2 * (Fintype.card (Reg n) : ℝ)) +
          κ * ((ℓ : ℝ)) ^ 2 / (2 * (Fintype.card (Reg n) : ℝ))) ≤
      (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, pExp κ s z * gammaOfMultiset n ℓ s z := by
  have hinj := strongGood_injective s hgood
  have hℓℝ : ((ℓ : ℝ)) ≠ 0 := cast_ℓ_ne_zero hℓ
  have hℓpos : (0 : ℝ) < ((ℓ : ℝ)) := by positivity
  have hNne : (Fintype.card (Reg n) : ℝ) ≠ 0 := card_reg_ne_zero n

  have hsumγ : ∑ z : Reg n, gammaOfMultiset n ℓ s z = (Fintype.card (Reg n) : ℝ) :=
    sum_gamma_eq_card s hℓ hinj
  have hsumγ2 := sum_gamma_sq_ge s hℓ
  have hsumγ3 := sum_gamma_cubic_le s hgood hℓ

  have haco : ∀ z : Reg n, aCoeff κ s z * gammaOfMultiset n ℓ s z =
      (1 / 2) * gammaOfMultiset n ℓ s z +
        (κ / 2) * gammaOfMultiset n ℓ s z ^ 2 -
        (κ ^ 2 / 4) * gammaOfMultiset n ℓ s z ^ 3 := fun z => by
    unfold aCoeff
    ring
  have hexp : ∑ z : Reg n, aCoeff κ s z * gammaOfMultiset n ℓ s z =
      (1 / 2) * ∑ z : Reg n, gammaOfMultiset n ℓ s z +
        (κ / 2) * ∑ z : Reg n, gammaOfMultiset n ℓ s z ^ 2 -
        (κ ^ 2 / 4) * ∑ z : Reg n, gammaOfMultiset n ℓ s z ^ 3 := by
    rw [Finset.sum_congr rfl (fun z _ => haco z), Finset.sum_sub_distrib,
      Finset.sum_add_distrib,
      show ∑ z : Reg n, (1 / 2) * gammaOfMultiset n ℓ s z =
          (1 / 2) * ∑ z : Reg n, gammaOfMultiset n ℓ s z from by rw [Finset.mul_sum],
      show ∑ z : Reg n, (κ / 2) * gammaOfMultiset n ℓ s z ^ 2 =
          (κ / 2) * ∑ z : Reg n, gammaOfMultiset n ℓ s z ^ 2 from by rw [Finset.mul_sum],
      show ∑ z : Reg n, (κ ^ 2 / 4) * gammaOfMultiset n ℓ s z ^ 3 =
          (κ ^ 2 / 4) * ∑ z : Reg n, gammaOfMultiset n ℓ s z ^ 3 from by
            rw [Finset.mul_sum]]

  have hcore : 1 / 2 + 3 * κ / 2 - κ / (ℓ : ℝ) - 15 * κ ^ 2 / 4 ≤
      (Fintype.card (Reg n) : ℝ)⁻¹ *
        ∑ z : Reg n, aCoeff κ s z * gammaOfMultiset n ℓ s z := by
    have h2 : (κ / 2) * ((Fintype.card (Reg n) : ℝ) * (3 - 2 / ((ℓ : ℝ)))) ≤
        (κ / 2) * ∑ z : Reg n, gammaOfMultiset n ℓ s z ^ 2 :=
      mul_le_mul_of_nonneg_left hsumγ2 (by positivity)
    have h3 : (κ ^ 2 / 4) * ∑ z : Reg n, gammaOfMultiset n ℓ s z ^ 3 ≤
        (κ ^ 2 / 4) * (15 * (Fintype.card (Reg n) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsumγ3 (by positivity)
    have hidx : (Fintype.card (Reg n) : ℝ)⁻¹ *
        ((1 / 2) * (Fintype.card (Reg n) : ℝ) +
          (κ / 2) * ((Fintype.card (Reg n) : ℝ) * (3 - 2 / ((ℓ : ℝ)))) -
          (κ ^ 2 / 4) * (15 * (Fintype.card (Reg n) : ℝ))) =
        1 / 2 + 3 * κ / 2 - κ / ((ℓ : ℝ)) - 15 * κ ^ 2 / 4 := by
      field_simp
      ring
    calc 1 / 2 + 3 * κ / 2 - κ / ((ℓ : ℝ)) - 15 * κ ^ 2 / 4
        = (Fintype.card (Reg n) : ℝ)⁻¹ *
            ((1 / 2) * (Fintype.card (Reg n) : ℝ) +
              (κ / 2) * ((Fintype.card (Reg n) : ℝ) * (3 - 2 / ((ℓ : ℝ)))) -
              (κ ^ 2 / 4) * (15 * (Fintype.card (Reg n) : ℝ))) := hidx.symm
      _ ≤ (Fintype.card (Reg n) : ℝ)⁻¹ *
            ((1 / 2) * ∑ z : Reg n, gammaOfMultiset n ℓ s z +
              (κ / 2) * ∑ z : Reg n, gammaOfMultiset n ℓ s z ^ 2 -
              (κ ^ 2 / 4) * ∑ z : Reg n, gammaOfMultiset n ℓ s z ^ 3) := by
            refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (card_reg_pos n).le)
            rw [hsumγ]
            linarith
      _ = (Fintype.card (Reg n) : ℝ)⁻¹ *
            ∑ z : Reg n, aCoeff κ s z * gammaOfMultiset n ℓ s z := by rw [← hexp]

  have hpAll₀ : pAll κ s (ZeroStr n) ≤ 1 / 2 + κ / 2 * ((ℓ : ℝ)) := by
    have hb := (aCoeff_le_pAll_le_bCoeff κ hκ s (ZeroStr n)).2
    unfold bCoeff at hb
    rw [gamma_zero s] at hb
    exact hb

  have hloss : pAll κ s (ZeroStr n) * ((ℓ : ℝ)) / (Fintype.card (Reg n) : ℝ) ≤
      ((ℓ : ℝ)) / (2 * (Fintype.card (Reg n) : ℝ)) +
        κ * ((ℓ : ℝ)) ^ 2 / (2 * (Fintype.card (Reg n) : ℝ)) := by
    have h1 : pAll κ s (ZeroStr n) * ((ℓ : ℝ)) ≤ (1 / 2 + κ / 2 * ((ℓ : ℝ))) * ((ℓ : ℝ)) :=
      mul_le_mul_of_nonneg_right hpAll₀ hℓpos.le
    have h2 : (1 / 2 + κ / 2 * ((ℓ : ℝ))) * ((ℓ : ℝ)) / (Fintype.card (Reg n) : ℝ) =
        ((ℓ : ℝ)) / (2 * (Fintype.card (Reg n) : ℝ)) +
          κ * ((ℓ : ℝ)) ^ 2 / (2 * (Fintype.card (Reg n) : ℝ)) := by
      field_simp
    calc pAll κ s (ZeroStr n) * ((ℓ : ℝ)) / (Fintype.card (Reg n) : ℝ)
        ≤ (1 / 2 + κ / 2 * ((ℓ : ℝ))) * ((ℓ : ℝ)) / (Fintype.card (Reg n) : ℝ) :=
          (div_le_div_iff_of_pos_right (card_reg_pos n)).mpr h1
      _ = ((ℓ : ℝ)) / (2 * (Fintype.card (Reg n) : ℝ)) +
          κ * ((ℓ : ℝ)) ^ 2 / (2 * (Fintype.card (Reg n) : ℝ)) := h2

  have hsumII : ∑ x : Reg n, (if multisetInd s x then (1 : ℝ) else 0) = ((ℓ : ℝ)) := by
    have h1 : ∑ x : Reg n, (if multisetInd s x then (1 : ℝ) else 0)
        = ((supportCard (multisetInd s) : ℕ) : ℝ) := by
      unfold supportCard
      simp
    rw [h1, strongGood_supportCard s hgood]

  have hE1 := flat_E_eq hℓ κ s hinj
  have hp := quad_pExp_eq κ s (fun x => if multisetInd s x then (1 : ℝ) else 0)
  rw [hsumII] at hp
  rw [hp] at hE1
  have hsplitE : ((ℓ : ℝ))⁻¹ *
      ((∑ x : Reg n, ∑ y : Reg n,
          (if multisetInd s x then (1 : ℝ) else 0) *
            (if multisetInd s y then (1 : ℝ) else 0) *
            quadEntry (pAll κ s) x y) -
        pAll κ s (ZeroStr n) / (Fintype.card (Reg n) : ℝ) * ((ℓ : ℝ)) ^ 2) =
      ((ℓ : ℝ))⁻¹ * (∑ x : Reg n, ∑ y : Reg n,
          (if multisetInd s x then (1 : ℝ) else 0) *
            (if multisetInd s y then (1 : ℝ) else 0) *
            quadEntry (pAll κ s) x y) -
        pAll κ s (ZeroStr n) * ((ℓ : ℝ)) / (Fintype.card (Reg n) : ℝ) := by
    field_simp
  rw [hsplitE] at hE1
  have hmid := quad_aEntry_le_pAll κ hκ hℓ s
    (fun x => if multisetInd s x then (1 : ℝ) else 0)
  have hA1 := flat_quad_entry_eq hℓ (aCoeff κ s) s hinj
  have hqa : (∑ x : Reg n, ∑ y : Reg n,
      (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
        quadEntry (aCoeff κ s) x y) =
    (∑ x : Reg n, ∑ y : Reg n,
      (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
        aEntry κ s x y) :=
    quad_sum_congr' _ _ _ (fun x y => quadEntry_aCoeff_eq hℓ κ s x y)
  rw [hqa] at hA1
  have hℓinvnn : (0 : ℝ) ≤ ((ℓ : ℝ))⁻¹ := by positivity
  have hqE_le : ((ℓ : ℝ))⁻¹ * (∑ x : Reg n, ∑ y : Reg n,
      (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
        aEntry κ s x y) ≤
    ((ℓ : ℝ))⁻¹ * (∑ x : Reg n, ∑ y : Reg n,
      (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
        quadEntry (pAll κ s) x y) :=
    mul_le_mul_of_nonneg_left hmid hℓinvnn
  linarith

/-- For a sequence satisfying `StrongGood`, the real sum of its support indicator equals its
length. -/
private theorem supp_ind_sum {n ℓ : ℕ} (s : Fin ℓ → Reg n) (hgood : StrongGood s) :
    ∑ x : Reg n, (if multisetInd s x then (1 : ℝ) else 0) = ((ℓ : ℝ)) := by
  have h1 : ∑ x : Reg n, (if multisetInd s x then (1 : ℝ) else 0)
      = ((supportCard (multisetInd s) : ℕ) : ℝ) := by
    unfold supportCard
    simp
  rw [h1, strongGood_supportCard s hgood]

private noncomputable def flatWitness {n ℓ : ℕ} (s : Fin ℓ → Reg n) : QState (Reg n) :=
  fun x => if multisetInd s x then ((Real.sqrt (((ℓ : ℝ))⁻¹) : ℝ) : ℂ) else 0

/-- The flat witness of a nonempty sequence satisfying `StrongGood` is normalized. -/
private theorem flatWitness_normalized {n ℓ : ℕ} (hℓ : ℓ ≠ 0) (s : Fin ℓ → Reg n)
    (hgood : StrongGood s) :
    Normalized (flatWitness s) := by
  have hinj := strongGood_injective s hgood
  have hℓpos : (0 : ℝ) < ((ℓ : ℝ)) := by positivity
  have hsq : ∀ x : Reg n,
      ‖flatWitness s x‖ ^ 2 = (if multisetInd s x then ((ℓ : ℝ))⁻¹ else 0) := by
    intro x
    have hn : ∀ t : ℝ, ‖((t : ℝ) : ℂ)‖ ^ 2 = t ^ 2 := by
      intro t
      rw [Complex.norm_real, Real.norm_eq_abs]
      simp
    unfold flatWitness
    by_cases hx : multisetInd s x = true
    · simp only [hx, ite_true, hn]
      rw [Real.sq_sqrt (inv_nonneg.mpr hℓpos.le)]
    · simp [hx]
  unfold Normalized
  rw [Finset.sum_congr rfl (fun x _ => hsq x)]
  rw [show ∑ x : Reg n, (if multisetInd s x then ((ℓ : ℝ))⁻¹ else 0) =
      ((ℓ : ℝ))⁻¹ * ∑ x : Reg n, (if multisetInd s x then (1 : ℝ) else 0) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by
          by_cases hx : multisetInd s x <;> simp [hx]]
  rw [supp_ind_sum s hgood, inv_mul_cancel₀ (cast_ℓ_ne_zero hℓ)]

/-- Expresses the forrelation mass of the flat witness as the length-normalized sum of `uEntry`
over the sequence support. -/
private theorem flat_mass_eq {n ℓ : ℕ} (s : Fin ℓ → Reg n) (u : Reg n → Bool) :
    forrWitnessMass n (multisetInd s) u (flatWitness s) =
      ((ℓ : ℝ))⁻¹ * ∑ x : Reg n, ∑ y : Reg n,
        (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
          uEntry u x y := by
  rw [forrWitnessMass_eq_quad]
  have hpt : ∀ x y : Reg n,
      ((flatWitness s x * (starRingEnd ℂ (flatWitness s y))).re) *
        ((if multisetInd s x then 1 else 0) * (if multisetInd s y then 1 else 0) *
          uEntry u x y) =
      ((ℓ : ℝ))⁻¹ * ((if multisetInd s x then (1 : ℝ) else 0) *
        (if multisetInd s y then (1 : ℝ) else 0) * uEntry u x y) := by
    intro x y
    by_cases hx : multisetInd s x = true <;> by_cases hy : multisetInd s y = true
    · simp only [flatWitness, hx, hy, ite_true]
      simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      rw [Real.mul_self_sqrt (inv_nonneg.mpr (by positivity))]
    · simp [flatWitness, hx, hy]
    · simp [flatWitness, hx, hy]
    · simp [flatWitness, hx, hy]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hpt x y))]
  simp only [Finset.mul_sum]

/-- The stated goodness, entry-deviation, and threshold assumptions establish `IsStrongYes` for
the sequence support and Boolean register function. -/
private theorem complete_chain {n ℓ : ℕ} (hℓ : ℓ ≠ 0) {κ ρ t1 t2 : ℝ} (hκ : 0 ≤ κ)
    (hκ1 : κ ≤ 1) (v : ℕ) (s : Fin ℓ → Reg n) (hgood : StrongGood s) (u : Reg n → Bool)
    (hu0 : u (ZeroStr n) = false) (hρ : 0 ≤ ρ)
    (hdev : ∀ x y : Reg n, multisetInd s x → multisetInd s y →
      |uEntry u x y - quadEntry (pExp κ s) x y| ≤ ρ / ((ℓ : ℝ)))
    (ht1 : t1 = (1 + κ) / 2 + (v : ℝ) / ((ℓ : ℝ)) + ρ)
    (hval : t2 + ρ ≤ 1 / 2 + 3 * κ / 2 - κ / ((ℓ : ℝ)) - 15 * κ ^ 2 / 4 -
        (((ℓ : ℝ)) / (2 * (Fintype.card (Reg n) : ℝ)) +
          κ * ((ℓ : ℝ)) ^ 2 / (2 * (Fintype.card (Reg n) : ℝ)))) :
    IsStrongYes t1 t2 v (multisetInd s) u := by
  have hinj := strongGood_injective s hgood
  have hℓℝ : ((ℓ : ℝ)) ≠ 0 := cast_ℓ_ne_zero hℓ
  have hℓpos : (0 : ℝ) < ((ℓ : ℝ)) := by positivity

  have hcard2 : ∑ x : Reg n, ∑ y : Reg n,
      (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) =
      ((ℓ : ℝ)) ^ 2 := by
    rw [← Finset.sum_mul_sum, supp_ind_sum s hgood]
    ring

  have hdevsum : ((ℓ : ℝ))⁻¹ * (∑ x : Reg n, ∑ y : Reg n,
      (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
        (quadEntry (pExp κ s) x y - uEntry u x y)) ≤ ρ := by
    have hpt : ∀ x y : Reg n,
        (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
            (quadEntry (pExp κ s) x y - uEntry u x y) ≤
        (ρ / ((ℓ : ℝ))) * ((if multisetInd s x then (1 : ℝ) else 0) *
          (if multisetInd s y then (1 : ℝ) else 0)) := by
      intro x y
      by_cases hx : multisetInd s x = true
      · by_cases hy : multisetInd s y = true
        · simp only [hx, hy, ite_true, one_mul]
          have h1 : quadEntry (pExp κ s) x y - uEntry u x y ≤
              |uEntry u x y - quadEntry (pExp κ s) x y| := by
            rw [← neg_sub]
            exact neg_le_abs _
          exact le_trans h1 (by simpa using! hdev x y hx hy)
        · simp [hx, hy]
      · simp [hx]
    have hsumle : (∑ x : Reg n, ∑ y : Reg n,
        (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
          (quadEntry (pExp κ s) x y - uEntry u x y)) ≤
        ∑ x : Reg n, ∑ y : Reg n,
        (ρ / ((ℓ : ℝ))) * ((if multisetInd s x then (1 : ℝ) else 0) *
          (if multisetInd s y then (1 : ℝ) else 0)) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpt x y
    have hconst : (∑ x : Reg n, ∑ y : Reg n,
        (ρ / ((ℓ : ℝ))) * ((if multisetInd s x then (1 : ℝ) else 0) *
          (if multisetInd s y then (1 : ℝ) else 0))) =
        (ρ / ((ℓ : ℝ))) * ((ℓ : ℝ)) ^ 2 := by
      calc (∑ x : Reg n, ∑ y : Reg n,
          (ρ / ((ℓ : ℝ))) * ((if multisetInd s x then (1 : ℝ) else 0) *
            (if multisetInd s y then (1 : ℝ) else 0)))
          = (ρ / ((ℓ : ℝ))) * ∑ x : Reg n, ∑ y : Reg n,
              (if multisetInd s x then (1 : ℝ) else 0) *
                (if multisetInd s y then (1 : ℝ) else 0) := by
            simp only [Finset.mul_sum]
        _ = (ρ / ((ℓ : ℝ))) * ((ℓ : ℝ)) ^ 2 := by rw [hcard2]
    calc ((ℓ : ℝ))⁻¹ * (∑ x : Reg n, ∑ y : Reg n,
        (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
          (quadEntry (pExp κ s) x y - uEntry u x y))
        ≤ ((ℓ : ℝ))⁻¹ * ((ρ / ((ℓ : ℝ))) * ((ℓ : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left (le_trans hsumle (le_of_eq hconst)) (by positivity)
      _ = ρ := by
          field_simp

  have hvalchain : t2 ≤ spectralForrelation n (multisetInd s) u := by
    have hmass_le := (spectralForrelationBasics n (multisetInd s) u).2.2.1
      (flatWitness s) (flatWitness_normalized hℓ s hgood)
    have hkey : ((ℓ : ℝ))⁻¹ * (∑ x : Reg n, ∑ y : Reg n,
        (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
          uEntry u x y) ≥
        ((ℓ : ℝ))⁻¹ * (∑ x : Reg n, ∑ y : Reg n,
          (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
            quadEntry (pExp κ s) x y) - ρ := by
      have hsumdist : (∑ x : Reg n, ∑ y : Reg n,
          (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
            quadEntry (pExp κ s) x y) -
          (∑ x : Reg n, ∑ y : Reg n,
          (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
            uEntry u x y) =
          ∑ x : Reg n, ∑ y : Reg n,
          (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
            (quadEntry (pExp κ s) x y - uEntry u x y) := by
        have hinner : ∀ x : Reg n,
            (∑ y : Reg n,
              (if multisetInd s x then (1 : ℝ) else 0) *
                (if multisetInd s y then (1 : ℝ) else 0) *
                quadEntry (pExp κ s) x y) -
            (∑ y : Reg n,
              (if multisetInd s x then (1 : ℝ) else 0) *
                (if multisetInd s y then (1 : ℝ) else 0) * uEntry u x y) =
            ∑ y : Reg n,
              (if multisetInd s x then (1 : ℝ) else 0) *
                (if multisetInd s y then (1 : ℝ) else 0) *
                (quadEntry (pExp κ s) x y - uEntry u x y) := by
          intro x
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun y _ => by ring
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun x _ => hinner x
      have h1 : ((ℓ : ℝ))⁻¹ * (∑ x : Reg n, ∑ y : Reg n,
          (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
            quadEntry (pExp κ s) x y) - ((ℓ : ℝ))⁻¹ * (∑ x : Reg n, ∑ y : Reg n,
          (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
            uEntry u x y) =
          ((ℓ : ℝ))⁻¹ * (∑ x : Reg n, ∑ y : Reg n,
            (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
              (quadEntry (pExp κ s) x y - uEntry u x y)) := by
        rw [← hsumdist, mul_sub]
      linarith [hdevsum, h1]
    have hEeq := flat_E_eq hℓ κ s hinj
    have hEge := flat_E_ge hℓ hκ s hgood
    calc t2 ≤ ((ℓ : ℝ))⁻¹ * (∑ x : Reg n, ∑ y : Reg n,
          (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
            quadEntry (pExp κ s) x y) - ρ := by
          linarith [hEeq, hEge, hval]
      _ ≤ ((ℓ : ℝ))⁻¹ * (∑ x : Reg n, ∑ y : Reg n,
          (if multisetInd s x then (1 : ℝ) else 0) * (if multisetInd s y then (1 : ℝ) else 0) *
            uEntry u x y) := hkey
      _ = forrWitnessMass n (multisetInd s) u (flatWitness s) := (flat_mass_eq s u).symm
      _ ≤ spectralForrelation n (multisetInd s) u := hmass_le
  refine ⟨hvalchain, ?_⟩
  intro Δ hsub hcard
  rw [ht1]
  exact sound_chain hℓ hκ hκ1 s hgood u hu0 hρ hdev Δ hsub hcard

end Completeness

section Assembly

/-- Strong Bernoulli weights are nonnegative when the parameter is nonnegative. -/
private theorem bernWeight_nonneg {n ℓ : ℕ} (κ : ℝ) (hκ : 0 ≤ κ) (s : Fin ℓ → Reg n)
    (u : Reg n → Bool) : 0 ≤ strongBernoulliWeight n ℓ κ s u := by
  rw [strongBernoulliWeight_eq_prod κ s u]
  refine Finset.prod_nonneg fun y _ => ?_
  unfold bernFactor
  by_cases hy : u y = true
  · rw [ite_eq_left hy]
    exact (pExp_mem_Icc κ hκ s y).1
  · rw [ite_eq_right hy]
    exact sub_nonneg.mpr (pExp_mem_Icc κ hκ s y).2

/-- The total strong Bernoulli weight of failures of `IsStrongYes` is at most one for a
nonnegative parameter. -/
private theorem fail_mass_le_one {n ℓ : ℕ} (κ : ℝ) (hκ : 0 ≤ κ) (t1 t2 : ℝ) (v : ℕ)
    (s : Fin ℓ → Reg n) :
    (∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
      (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)) ≤ 1 := by
  calc (∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
        (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1))
      ≤ ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u * 1 := by
        refine Finset.sum_le_sum fun u _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (bernWeight_nonneg κ hκ s u)
        by_cases h : IsStrongYes t1 t2 v (multisetInd s) u <;> simp [h]
    _ = ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u :=
        Finset.sum_congr rfl fun u _ => by ring
    _ = 1 := strongBernoulliWeight_sum κ s

/-- The strong failure probability is at most one for a nonnegative parameter. -/
private theorem strongFailProb_le_one (n ℓ : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) (t1 t2 : ℝ) (v : ℕ) :
    strongFailProb n ℓ κ t1 t2 v ≤ 1 := by
  have hcardpos : (0 : ℝ) < (Fintype.card (Fin ℓ → Reg n) : ℝ) := by
    have h : (0 : ℕ) < Fintype.card (Fin ℓ → Reg n) :=
      Fintype.card_pos_iff.mpr ⟨fun _ => ZeroStr n⟩
    exact_mod_cast h
  unfold strongFailProb
  have hsum : (∑ s : Fin ℓ → Reg n, ∑ u : Reg n → Bool,
      strongBernoulliWeight n ℓ κ s u *
        (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)) ≤
      (Fintype.card (Fin ℓ → Reg n) : ℝ) := by
    calc (∑ s : Fin ℓ → Reg n, ∑ u : Reg n → Bool,
          strongBernoulliWeight n ℓ κ s u *
            (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1))
        ≤ ∑ s : Fin ℓ → Reg n, 1 :=
          Finset.sum_le_sum fun s _ => fail_mass_le_one κ hκ t1 t2 v s
      _ = (Fintype.card (Fin ℓ → Reg n) : ℝ) := by simp
  have h1 : (1 / (Fintype.card (Fin ℓ → Reg n) : ℝ)) *
      (Fintype.card (Fin ℓ → Reg n) : ℝ) = 1 := by
    field_simp
  calc (1 / (Fintype.card (Fin ℓ → Reg n) : ℝ)) *
        (∑ s : Fin ℓ → Reg n, ∑ u : Reg n → Bool,
          strongBernoulliWeight n ℓ κ s u *
            (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1))
      ≤ (1 / (Fintype.card (Fin ℓ → Reg n) : ℝ)) *
          (Fintype.card (Fin ℓ → Reg n) : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := h1

/-- Under the stated goodness and threshold assumptions, bounds the strong Bernoulli failure
mass by the explicit Gaussian union-bound expression. -/
private theorem fail_mass_bound {n ℓ : ℕ} (hℓ : ℓ ≠ 0) {κ ρ t1 t2 : ℝ} (hκ : 0 ≤ κ)
    (hκ1 : κ ≤ 1) (hρ : 0 ≤ ρ) (v : ℕ) (s : Fin ℓ → Reg n) (hgood : StrongGood s)
    (ht1 : t1 = (1 + κ) / 2 + (v : ℝ) / ((ℓ : ℝ)) + ρ)
    (hval : t2 + ρ ≤ 1 / 2 + 3 * κ / 2 - κ / ((ℓ : ℝ)) - 15 * κ ^ 2 / 4 -
      (((ℓ : ℝ)) / (2 * (Fintype.card (Reg n) : ℝ)) +
        κ * ((ℓ : ℝ)) ^ 2 / (2 * (Fintype.card (Reg n) : ℝ)))) :
    (∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
      (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)) ≤
    2 * ((ℓ : ℝ)) ^ 2 *
      Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * ((ℓ : ℝ)) ^ 2))) := by

  have hptw : ∀ u : Reg n → Bool,
      strongBernoulliWeight n ℓ κ s u *
          (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1) ≤
      strongBernoulliWeight n ℓ κ s u *
        ((if u (ZeroStr n) then (1 : ℝ) else 0) +
          (if (∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
            ρ / ((ℓ : ℝ)) < |uEntry u x y - quadEntry (pExp κ s) x y|)
              then (1 : ℝ) else 0)) := by
    intro u
    have hge0 : 0 ≤ strongBernoulliWeight n ℓ κ s u := bernWeight_nonneg κ hκ s u
    have hind : (0 : ℝ) ≤ (if (∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
          ρ / ((ℓ : ℝ)) < |uEntry u x y - quadEntry (pExp κ s) x y|)
            then (1 : ℝ) else 0) := by
      by_cases hx : (∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
        ρ / ((ℓ : ℝ)) < |uEntry u x y - quadEntry (pExp κ s) x y|)
      · rw [ite_eq_left hx]
        norm_num
      · rw [ite_eq_right hx]
    by_cases hu0 : u (ZeroStr n) = true
    · have h1 : (if IsStrongYes t1 t2 v (multisetInd s) u then (0 : ℝ) else 1) ≤
          (if u (ZeroStr n) then (1 : ℝ) else 0) +
            (if (∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
              ρ / ((ℓ : ℝ)) < |uEntry u x y - quadEntry (pExp κ s) x y|)
                then (1 : ℝ) else 0) := by
        rw [ite_eq_left hu0]
        have h2 : (if IsStrongYes t1 t2 v (multisetInd s) u then (0 : ℝ) else 1) ≤ 1 := by
          by_cases hIs : IsStrongYes t1 t2 v (multisetInd s) u <;> simp [hIs]
        linarith
      exact mul_le_mul_of_nonneg_left h1 hge0
    · by_cases hd : (∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
          ρ / ((ℓ : ℝ)) < |uEntry u x y - quadEntry (pExp κ s) x y|)
      · have h1 : (if IsStrongYes t1 t2 v (multisetInd s) u then (0 : ℝ) else 1) ≤
            (if u (ZeroStr n) then (1 : ℝ) else 0) +
              (if (∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
                ρ / ((ℓ : ℝ)) < |uEntry u x y - quadEntry (pExp κ s) x y|)
                  then (1 : ℝ) else 0) := by
          rw [ite_eq_left hd]
          have h2 : (if IsStrongYes t1 t2 v (multisetInd s) u then (0 : ℝ) else 1) ≤ 1 := by
            by_cases hIs : IsStrongYes t1 t2 v (multisetInd s) u <;> simp [hIs]
          have h3 : (0 : ℝ) ≤ (if u (ZeroStr n) then (1 : ℝ) else 0) := by
            by_cases hu : u (ZeroStr n) = true <;> simp [hu]
          linarith
        exact mul_le_mul_of_nonneg_left h1 hge0
      · have hdev : ∀ x y : Reg n, multisetInd s x → multisetInd s y →
            |uEntry u x y - quadEntry (pExp κ s) x y| ≤ ρ / ((ℓ : ℝ)) := by
          intro x y hx hy
          by_contra hcon
          exact absurd ⟨x, y, hx, hy, lt_of_not_ge hcon⟩ hd
        simp only [Bool.not_eq_true] at hu0
        have hisy := complete_chain hℓ hκ hκ1 v s hgood u hu0 hρ hdev ht1 hval
        rw [ite_eq_left hisy, ite_eq_right hd]
        simp [hu0]

  have h0 : (∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
      (if u (ZeroStr n) then (1 : ℝ) else 0)) = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    by_cases hu : u (ZeroStr n) = true
    · rw [ite_eq_left hu, mul_one]
      exact bernWeight_zero_of_u0 κ s u hu
    · rw [ite_eq_right hu, mul_zero]

  have hD : (∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
      (if (∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
        ρ / ((ℓ : ℝ)) < |uEntry u x y - quadEntry (pExp κ s) x y|)
          then (1 : ℝ) else 0)) ≤
      2 * ((ℓ : ℝ)) ^ 2 *
        Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * ((ℓ : ℝ)) ^ 2))) := by
    rw [show (∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
        (if (∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
          ρ / ((ℓ : ℝ)) < |uEntry u x y - quadEntry (pExp κ s) x y|)
            then (1 : ℝ) else 0)) =
      ∑ u ∈ (Finset.univ : Finset (Reg n → Bool)).filter
        (fun u => ∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
          ρ / ((ℓ : ℝ)) < |uEntry u x y - quadEntry (pExp κ s) x y|),
        strongBernoulliWeight n ℓ κ s u from by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun u _ => by
        by_cases hu : (∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
          ρ / ((ℓ : ℝ)) < |uEntry u x y - quadEntry (pExp κ s) x y|)
        · simp []
        · simp []]
    exact union_entry_tail κ hκ s hgood hρ hℓ
  calc (∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
        (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1))
      ≤ (∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
          ((if u (ZeroStr n) then (1 : ℝ) else 0) +
            (if (∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
              ρ / ((ℓ : ℝ)) < |uEntry u x y - quadEntry (pExp κ s) x y|)
                then (1 : ℝ) else 0))) :=
        Finset.sum_le_sum fun u _ => hptw u
    _ = (∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
          (if u (ZeroStr n) then (1 : ℝ) else 0)) +
        (∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
          (if (∃ x y : Reg n, multisetInd s x ∧ multisetInd s y ∧
            ρ / ((ℓ : ℝ)) < |uEntry u x y - quadEntry (pExp κ s) x y|)
              then (1 : ℝ) else 0)) := by
        rw [Finset.sum_congr rfl fun u _ => mul_add _ _ _, Finset.sum_add_distrib]
    _ ≤ 2 * ((ℓ : ℝ)) ^ 2 *
        Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * ((ℓ : ℝ)) ^ 2))) := by
        linarith [h0, hD]

end Assembly

set_option maxHeartbeats 1000000 in

/-- Establishes `StrongYesInstanceProperty`. -/
theorem strongYesInstanceProperty : StrongYesInstanceProperty := by
  intro n ℓ κ ρ v hℓ hκ hκ1 hρ t1 t2 ht1 ht2 hlt
  have hℓpos : (0 : ℝ) < ((ℓ : ℝ)) := by positivity
  have hNpos : (0 : ℝ) < (Fintype.card (Reg n) : ℝ) := card_reg_pos n
  have hNne : (Fintype.card (Reg n) : ℝ) ≠ 0 := card_reg_ne_zero n

  have hzpow : (2 : ℝ) ^ (-(n : ℤ)) = ((Fintype.card (Reg n) : ℝ))⁻¹ := by
    rw [zpow_neg, zpow_natCast, card_reg]
    push_cast
    ring
  have hzpow' : (2 : ℝ) ^ (n : ℕ) = ((Fintype.card (Reg n) : ℝ)) := by
    rw [card_reg]
    push_cast
    ring

  have hscard : (Fintype.card (Fin ℓ → Reg n) : ℝ) =
      ((Fintype.card (Reg n) : ℝ)) ^ ((ℓ : ℕ)) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  have hscardpos : (0 : ℝ) < (Fintype.card (Fin ℓ → Reg n) : ℝ) := by
    rw [hscard]
    positivity
  by_cases hcase : 1 ≤ ((ℓ : ℝ)) ^ 6 * (2 : ℝ) ^ (-(n : ℤ)) +
      2 * ((ℓ : ℝ)) ^ 2 *
        Real.exp (-(ρ ^ 2 * (2 : ℝ) ^ (n : ℕ) / (2 * ((ℓ : ℝ)) ^ 2)))
  · exact le_trans (strongFailProb_le_one n ℓ κ hκ t1 t2 v) hcase
  · push Not at hcase
    have h6 : (0 : ℝ) ≤ ((ℓ : ℝ)) ^ 6 * (2 : ℝ) ^ (-(n : ℤ)) := by positivity
    have hE : (0 : ℝ) ≤ 2 * ((ℓ : ℝ)) ^ 2 *
        Real.exp (-(ρ ^ 2 * (2 : ℝ) ^ (n : ℕ) / (2 * ((ℓ : ℝ)) ^ 2))) := by positivity
    have hA : ((ℓ : ℝ)) ^ 6 * ((Fintype.card (Reg n) : ℝ))⁻¹ < 1 := by
      rw [← hzpow]
      linarith
    have hB : 2 * ((ℓ : ℝ)) ^ 2 *
        Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * ((ℓ : ℝ)) ^ 2))) < 1 := by
      rw [← hzpow']
      linarith

    have hℓ6 : ((ℓ : ℝ)) ^ 6 < (Fintype.card (Reg n) : ℝ) := by
      rw [← div_eq_mul_inv] at hA
      exact (div_lt_one₀ hNpos).mp hA

    have hρ2 : ((ℓ : ℝ)) ^ 2 < ρ ^ 2 * (Fintype.card (Reg n) : ℝ) := by
      have h2ℓpos : (0 : ℝ) < 2 * ((ℓ : ℝ)) ^ 2 := by positivity
      have hexp : Real.exp
            (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * ((ℓ : ℝ)) ^ 2))) <
          1 / (2 * ((ℓ : ℝ)) ^ 2) := by
        rw [lt_div_iff₀ h2ℓpos, mul_comm]
        exact hB
      have hle : (1 : ℝ) - ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * ((ℓ : ℝ)) ^ 2) ≤
          Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * ((ℓ : ℝ)) ^ 2))) := by
        have h := Real.add_one_le_exp
          (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * ((ℓ : ℝ)) ^ 2)))
        linarith
      have h12 : (1 : ℝ) / (2 * ((ℓ : ℝ)) ^ 2) ≤ 1 / 2 := by
        have hℓ1 : (1 : ℝ) ≤ ((ℓ : ℝ)) := by
          exact_mod_cast Nat.succ_le_of_lt hℓ
        have hℓsq : (1 : ℝ) ≤ ((ℓ : ℝ)) ^ 2 := one_le_pow₀ hℓ1
        rw [div_le_div_iff₀ h2ℓpos (by norm_num)]
        have h2 : (2 : ℝ) * 1 ≤ 2 * ((ℓ : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hℓsq (by norm_num)
        linarith
      have hx : (1 : ℝ) / 2 <
          ρ ^ 2 * (Fintype.card (Reg n) : ℝ) / (2 * ((ℓ : ℝ)) ^ 2) := by
        linarith
      rw [lt_div_iff₀ h2ℓpos] at hx
      have hhalf : (1 : ℝ) / 2 * (2 * ((ℓ : ℝ)) ^ 2) = ((ℓ : ℝ)) ^ 2 := by ring
      linarith

    have hrk : 2 * ρ < κ := by
      rw [ht1, ht2] at hlt
      have hmul : ((1 + κ) / 2 + (v : ℝ) / ((ℓ : ℝ)) + ρ) * 2 <
          ((1 + 3 * κ) / 2 - 15 * κ ^ 2 / 4 - 5 * κ / ((ℓ : ℝ)) - ρ) * 2 :=
        mul_lt_mul_of_pos_right hlt two_pos
      have hL : ((1 + κ) / 2 + (v : ℝ) / ((ℓ : ℝ)) + ρ) * 2 =
          1 + κ + 2 * (v : ℝ) / ((ℓ : ℝ)) + 2 * ρ := by ring
      have hR : ((1 + 3 * κ) / 2 - 15 * κ ^ 2 / 4 - 5 * κ / ((ℓ : ℝ)) - ρ) * 2 =
          1 + 3 * κ - 15 * κ ^ 2 / 2 - 10 * κ / ((ℓ : ℝ)) - 2 * ρ := by ring
      rw [hL, hR] at hmul
      have hnn1 : (0 : ℝ) ≤ 15 * κ ^ 2 / 2 := by positivity
      have hnn2 : (0 : ℝ) ≤ 10 * κ / ((ℓ : ℝ)) := by positivity
      have hnn3 : (0 : ℝ) ≤ 2 * (v : ℝ) / ((ℓ : ℝ)) := by positivity
      linarith
    have hκpos : (0 : ℝ) < κ := by linarith
    have hℓ1 : (1 : ℝ) ≤ ((ℓ : ℝ)) := by
      exact_mod_cast Nat.succ_le_of_lt hℓ

    have hℓ2N : ((ℓ : ℝ)) ^ 2 < 6 * κ * (Fintype.card (Reg n) : ℝ) := by
      have h1 : ρ ^ 2 < (κ / 2) ^ 2 := by nlinarith [hrk, hρ]
      have h3 : ρ ^ 2 * (Fintype.card (Reg n) : ℝ) <
          (κ / 2) ^ 2 * (Fintype.card (Reg n) : ℝ) :=
        mul_lt_mul_of_pos_right h1 hNpos
      have h2 : (κ / 2) ^ 2 * (Fintype.card (Reg n) : ℝ) ≤
          κ * (Fintype.card (Reg n) : ℝ) := by
        have hhalf : (κ / 2) ^ 2 ≤ κ := by nlinarith [hκ1, hκpos]
        exact mul_le_mul_of_nonneg_right hhalf hNpos.le
      have h6κN : κ * (Fintype.card (Reg n) : ℝ) <
          6 * κ * (Fintype.card (Reg n) : ℝ) := by
        nlinarith [hκpos, hNpos]
      linarith [hρ2, h3, h2, h6κN]

    have hℓ3 : ((ℓ : ℝ)) ^ 3 ≤ 2 * (Fintype.card (Reg n) : ℝ) := by
      have hℓ6' : (1 : ℝ) ≤ ((ℓ : ℝ)) ^ 3 := one_le_pow₀ hℓ1
      have hp : ((ℓ : ℝ)) ^ 3 ≤ ((ℓ : ℝ)) ^ 6 := by nlinarith [hℓ6']
      have h6 : ((ℓ : ℝ)) ^ 6 ≤ (Fintype.card (Reg n) : ℝ) := le_of_lt hℓ6
      linarith

    have hval : t2 + ρ ≤ 1 / 2 + 3 * κ / 2 - κ / ((ℓ : ℝ)) - 15 * κ ^ 2 / 4 -
        (((ℓ : ℝ)) / (2 * (Fintype.card (Reg n) : ℝ)) +
          κ * ((ℓ : ℝ)) ^ 2 / (2 * (Fintype.card (Reg n) : ℝ))) := by
      have hp1 : κ * ((ℓ : ℝ)) ^ 2 / (2 * (Fintype.card (Reg n) : ℝ)) ≤
          κ / ((ℓ : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) hℓpos]
        nlinarith [hℓ3, hκ]
      have hp2 : ((ℓ : ℝ)) / (2 * (Fintype.card (Reg n) : ℝ)) ≤
          3 * (κ / ((ℓ : ℝ))) := by
        have hp2' : ((ℓ : ℝ)) / (2 * (Fintype.card (Reg n) : ℝ)) ≤
            3 * κ / ((ℓ : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity) hℓpos]
          nlinarith [hℓ2N]
        have hE : 3 * κ / ((ℓ : ℝ)) = 3 * (κ / ((ℓ : ℝ))) := by ring
        rw [hE] at hp2'
        exact hp2'
      have hEq : (1 + 3 * κ) / 2 = 1 / 2 + 3 * κ / 2 := by ring
      rw [ht2, hEq]
      have hEqL : (1 / 2 + 3 * κ / 2 - 15 * κ ^ 2 / 4 - 5 * κ / ((ℓ : ℝ)) - ρ) + ρ =
          1 / 2 + 3 * κ / 2 - 15 * κ ^ 2 / 4 - 5 * (κ / ((ℓ : ℝ))) := by ring
      rw [hEqL]
      linarith

    unfold strongFailProb
    have hsplit : (∑ s : Fin ℓ → Reg n, ∑ u : Reg n → Bool,
        strongBernoulliWeight n ℓ κ s u *
          (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)) =
        (∑ s ∈ (Finset.univ : Finset (Fin ℓ → Reg n)).filter
          (fun s => StrongGood s),
          ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
            (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)) +
        (∑ s ∈ (Finset.univ : Finset (Fin ℓ → Reg n)).filter
          (fun s => ¬StrongGood s),
          ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
            (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)) := by
      rw [Finset.sum_filter_add_sum_filter_not]
    rw [hsplit]

    have hgoodle : (∑ s ∈ (Finset.univ : Finset (Fin ℓ → Reg n)).filter
          (fun s => StrongGood s),
          ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
            (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)) ≤
        (Fintype.card (Fin ℓ → Reg n) : ℝ) *
          (2 * ((ℓ : ℝ)) ^ 2 *
            Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) /
              (2 * ((ℓ : ℝ)) ^ 2)))) := by
      have hmem : ∀ s ∈ (Finset.univ : Finset (Fin ℓ → Reg n)).filter
          (fun s => StrongGood s),
          (∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
            (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)) ≤
          2 * ((ℓ : ℝ)) ^ 2 *
            Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) /
              (2 * ((ℓ : ℝ)) ^ 2))) := by
        intro s hs
        exact fail_mass_bound (show ℓ ≠ 0 by omega) hκ hκ1 hρ v s
          (Finset.mem_filter.mp hs).2 ht1 hval
      calc (∑ s ∈ (Finset.univ : Finset (Fin ℓ → Reg n)).filter
            (fun s => StrongGood s),
            ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
              (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1))
          ≤ (∑ s ∈ (Finset.univ : Finset (Fin ℓ → Reg n)).filter
              (fun s => StrongGood s),
              2 * ((ℓ : ℝ)) ^ 2 *
                Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) /
                  (2 * ((ℓ : ℝ)) ^ 2)))) :=
            Finset.sum_le_sum hmem
        _ ≤ (∑ s : Fin ℓ → Reg n, 2 * ((ℓ : ℝ)) ^ 2 *
              Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) /
                (2 * ((ℓ : ℝ)) ^ 2)))) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset (fun s : Fin ℓ → Reg n => StrongGood s) Finset.univ)
              (fun s _ _ => by positivity)
        _ = (Fintype.card (Fin ℓ → Reg n) : ℝ) *
              (2 * ((ℓ : ℝ)) ^ 2 *
                Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) /
                  (2 * ((ℓ : ℝ)) ^ 2)))) := by
            rw [Finset.sum_const, Finset.card_univ]
            simp

    have hbadle : (∑ s ∈ (Finset.univ : Finset (Fin ℓ → Reg n)).filter
          (fun s => ¬StrongGood s),
          ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
            (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)) ≤
        ((ℓ : ℝ)) ^ 6 * (Fintype.card (Fin ℓ → Reg n) : ℝ) /
          (Fintype.card (Reg n) : ℝ) := by
      have h1 : (∑ s ∈ (Finset.univ : Finset (Fin ℓ → Reg n)).filter
            (fun s => ¬StrongGood s),
            ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
              (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)) ≤
          (((Finset.univ : Finset (Fin ℓ → Reg n)).filter
            (fun s => ¬StrongGood s)).card : ℝ) := by
        calc (∑ s ∈ (Finset.univ : Finset (Fin ℓ → Reg n)).filter
              (fun s => ¬StrongGood s),
              ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
                (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1))
            ≤ (∑ s ∈ (Finset.univ : Finset (Fin ℓ → Reg n)).filter
                (fun s => ¬StrongGood s), (1 : ℝ)) :=
              Finset.sum_le_sum fun s _ => fail_mass_le_one κ hκ t1 t2 v s
          _ = (((Finset.univ : Finset (Fin ℓ → Reg n)).filter
              (fun s => ¬StrongGood s)).card : ℝ) := by
            rw [Finset.sum_const]
            simp
      have hc2 : (((Finset.univ : Finset (Fin ℓ → Reg n)).filter
            (fun s => ¬StrongGood s)).card : ℝ) * (Fintype.card (Reg n) : ℝ) ≤
          ((ℓ : ℝ)) ^ 6 * ((Fintype.card (Reg n) : ℝ)) ^ ((ℓ : ℕ)) := by
        have hn := strongGood_filter_card_le (n := n) (ℓ := ℓ)
        exact_mod_cast hn
      rw [← hscard] at hc2
      have hcb : (((Finset.univ : Finset (Fin ℓ → Reg n)).filter
            (fun s => ¬StrongGood s)).card : ℝ) ≤
          ((ℓ : ℝ)) ^ 6 * (Fintype.card (Fin ℓ → Reg n) : ℝ) /
            (Fintype.card (Reg n) : ℝ) := by
        rw [le_div_iff₀ hNpos]
        exact hc2
      linarith [h1, hcb]

    have hsumle : ((∑ s ∈ (Finset.univ : Finset (Fin ℓ → Reg n)).filter
          (fun s => StrongGood s),
          ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
            (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)) +
        (∑ s ∈ (Finset.univ : Finset (Fin ℓ → Reg n)).filter
          (fun s => ¬StrongGood s),
          ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
            (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1))) ≤
        (Fintype.card (Fin ℓ → Reg n) : ℝ) *
          (2 * ((ℓ : ℝ)) ^ 2 *
            Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) /
              (2 * ((ℓ : ℝ)) ^ 2)))) +
        ((ℓ : ℝ)) ^ 6 * (Fintype.card (Fin ℓ → Reg n) : ℝ) /
          (Fintype.card (Reg n) : ℝ) := by
      linarith
    have hdiv : (1 / (Fintype.card (Fin ℓ → Reg n) : ℝ)) *
        ((Fintype.card (Fin ℓ → Reg n) : ℝ) *
            (2 * ((ℓ : ℝ)) ^ 2 *
              Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) /
                (2 * ((ℓ : ℝ)) ^ 2)))) +
          ((ℓ : ℝ)) ^ 6 * (Fintype.card (Fin ℓ → Reg n) : ℝ) /
            (Fintype.card (Reg n) : ℝ)) =
        2 * ((ℓ : ℝ)) ^ 2 *
            Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) /
              (2 * ((ℓ : ℝ)) ^ 2))) +
          ((ℓ : ℝ)) ^ 6 * ((Fintype.card (Reg n) : ℝ))⁻¹ := by
      field_simp
    calc (1 / (Fintype.card (Fin ℓ → Reg n) : ℝ)) *
          ((∑ s ∈ (Finset.univ : Finset (Fin ℓ → Reg n)).filter
              (fun s => StrongGood s),
              ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
                (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)) +
            (∑ s ∈ (Finset.univ : Finset (Fin ℓ → Reg n)).filter
              (fun s => ¬StrongGood s),
              ∑ u : Reg n → Bool, strongBernoulliWeight n ℓ κ s u *
                (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)))
        ≤ (1 / (Fintype.card (Fin ℓ → Reg n) : ℝ)) *
          ((Fintype.card (Fin ℓ → Reg n) : ℝ) *
              (2 * ((ℓ : ℝ)) ^ 2 *
                Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) /
                  (2 * ((ℓ : ℝ)) ^ 2)))) +
            ((ℓ : ℝ)) ^ 6 * (Fintype.card (Fin ℓ → Reg n) : ℝ) /
              (Fintype.card (Reg n) : ℝ)) :=
          mul_le_mul_of_nonneg_left hsumle (by positivity)
      _ = 2 * ((ℓ : ℝ)) ^ 2 *
            Real.exp (-(ρ ^ 2 * (Fintype.card (Reg n) : ℝ) /
              (2 * ((ℓ : ℝ)) ^ 2))) +
          ((ℓ : ℝ)) ^ 6 * ((Fintype.card (Reg n) : ℝ))⁻¹ := hdiv
      _ = ((ℓ : ℝ)) ^ 6 * (2 : ℝ) ^ (-(n : ℤ)) +
          2 * ((ℓ : ℝ)) ^ 2 *
            Real.exp (-(ρ ^ 2 * (2 : ℝ) ^ (n : ℕ) / (2 * ((ℓ : ℝ)) ^ 2))) := by
          rw [hzpow, hzpow']
          ring

end Qatlib.Papers.QMAvsQCMA25.Forrelation.StrongYesInstancePropertySepa
