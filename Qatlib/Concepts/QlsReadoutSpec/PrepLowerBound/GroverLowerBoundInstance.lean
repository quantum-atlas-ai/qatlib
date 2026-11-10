/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryLowerBounds
import Qatlib.Foundations.PureStateMath.Qubit
set_option warningAsError false


open Qatlib.Concepts.QueryComplexity.AdversarySearch

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound

open Matrix

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

def uniformQState : QState I := fun _ => ((Real.sqrt (Fintype.card I : ℝ))⁻¹ : ℂ)

def uniformProjector : Matrix I I ℂ :=
  ((Fintype.card I : ℝ))⁻¹ • Matrix.of fun _ _ => (1 : ℂ)

def groverMatrix : Matrix I I ℂ :=
  ((Real.sqrt (Fintype.card I : ℝ))⁻¹ : ℂ) •
      ((1 : ℂ) • (1 : Matrix I I ℂ) - uniformProjector (I := I)) +
  uniformProjector (I := I)

def groverInverse : Matrix I I ℂ :=
  (Real.sqrt (Fintype.card I : ℝ)) •
      ((1 : ℂ) • (1 : Matrix I I ℂ) - uniformProjector (I := I)) +
  uniformProjector (I := I)

def bState (x : I) : QState I :=
  fun y =>
    ((Real.sqrt (Fintype.card I : ℝ))⁻¹ : ℂ) -
      if y = x then ((Real.sqrt (Fintype.card I : ℝ))⁻¹ * 2 : ℂ) else 0

def bOracle (x : I) : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ :=
  (1 : ℂ) • (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) -
    (2 : ℂ) • Matrix.of
      (fun (p q : (I × Bool) × W) =>
        if p.1.1 = q.1.1 ∧ q.1.1 = x then (1 : ℂ) else 0)

def solverStart (ν₀ : QState Bool) (ω₀ : QState W) : QState ((I × Bool) × W) :=
  fun p => (uniformQState (I := I) p.1.1) * ν₀ p.1.2 * ω₀ p.2

def solutionTarget (ν₀ : QState Bool) (ω₀ : QState W) (x : I) :
    QState ((I × Bool) × W) :=
  fun p =>
    (NormedSpace.normalize
      (stateVector (groverInverse (I := I) *ᵥ bState (I := I) x)) p.1.1) *
    ν₀ p.1.2 * ω₀ p.2

omit [Fintype I] [DecidableEq I] in

private lemma real_matrix_smul (r : ℝ) (A : Matrix I I ℂ) :
    r • A = (r : ℂ) • A := by
  ext i j
  rfl

omit [DecidableEq I] in

@[simp] theorem uniformProjector_apply (i j : I) :
    uniformProjector (I := I) i j = ((Fintype.card I : ℝ)⁻¹ : ℂ) := by
  simp [uniformProjector, Complex.real_smul]

omit [DecidableEq I] in

theorem uniformProjector_idempotent [Nonempty I] :
    uniformProjector (I := I) * uniformProjector (I := I) = uniformProjector (I := I) := by
  have hc : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext i j
  simp only [Matrix.mul_apply, uniformProjector_apply, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  push_cast
  field_simp

omit [DecidableEq I] in

theorem uniformProjector_selfAdjoint :
    (uniformProjector (I := I))ᴴ = uniformProjector (I := I) := by
  ext i j
  simp [uniformProjector, Matrix.conjTranspose_apply]

theorem uniformProjector_complement [Nonempty I] :
    uniformProjector (I := I) * (1 - uniformProjector (I := I)) = 0 ∧
      (1 - uniformProjector (I := I)) * uniformProjector (I := I) = 0 ∧
      (1 - uniformProjector (I := I)) * (1 - uniformProjector (I := I)) =
        1 - uniformProjector (I := I) := by
  have hP := uniformProjector_idempotent (I := I)
  simp only [mul_sub, sub_mul, one_mul, mul_one, hP, sub_self, sub_zero, and_self]

theorem groverMatrix_inverse [Nonempty I] :
    groverMatrix (I := I) * groverInverse (I := I) = 1 ∧
      groverInverse (I := I) * groverMatrix (I := I) = 1 := by
  have hs : Real.sqrt (Fintype.card I : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    exact_mod_cast Fintype.card_pos
  have hP := uniformProjector_idempotent (I := I)
  have hQ := uniformProjector_complement (I := I)
  have hsc : ((Real.sqrt (Fintype.card I : ℝ))⁻¹ : ℂ) *
      (Real.sqrt (Fintype.card I : ℝ) : ℂ) = 1 := by
    simp [hs]
  have hsc' := hsc
  rw [mul_comm] at hsc'
  constructor <;>
    simp only [groverMatrix, groverInverse, one_smul, real_matrix_smul, add_mul, mul_add,
      smul_mul_assoc, Matrix.mul_smul, smul_smul, hQ.2.2, hQ.2.1, hQ.1, hP, hsc, hsc',
      smul_zero, one_smul, add_zero, zero_add, sub_add_cancel]

omit [Fintype I] in

theorem bOracle_marked_column (x i : I) (b : Bool) (w : Unit) :
    bOracle (W := Unit) x ((i, b), w) ((x, false), ()) =
      if i = x then (if b = false then (-1 : ℂ) else -2) else 0 := by
  cases w
  by_cases hi : i = x
  · subst i
    cases b <;> norm_num [bOracle]
  · simp [bOracle, hi]

theorem bOracle_marked_gram (x : I) :
    ((bOracle (W := Unit) x)ᴴ * bOracle (W := Unit) x)
      ((x, false), ()) ((x, false), ()) = 5 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, bOracle_marked_column]
  norm_num [map_ofNat]

theorem bOracle_not_unitary (x : I) :
    bOracle (W := Unit) x ∉ Matrix.unitaryGroup ((I × Bool) × Unit) ℂ := by
  intro h
  have hh := Unitary.star_mul_self_of_mem h
  have hd := congrArg (fun A : Matrix ((I × Bool) × Unit) ((I × Bool) × Unit) ℂ =>
    A ((x, false), ()) ((x, false), ())) hh
  simp only [Matrix.star_eq_conjTranspose, bOracle_marked_gram, Matrix.one_apply_eq] at hd
  norm_num at hd

theorem grover_ratio_bounds (d : ℝ) (hd : 8 ≤ d) :
    4 / d ≤ (5 * d ^ 2 - 8 * d + 4) / d ^ 3 ∧
      (5 * d ^ 2 - 8 * d + 4) / d ^ 3 ≤ 5 / d := by
  have hd0 : 0 < d := by linarith
  have h4 : 4 / d = 4 * d ^ 2 / d ^ 3 := by field_simp
  have h5 : 5 / d = 5 * d ^ 2 / d ^ 3 := by field_simp
  rw [h4, h5]
  constructor
  · apply div_le_div_of_nonneg_right _ (pow_nonneg hd0.le 3)
    have hp : 0 ≤ d * (d - 8) := mul_nonneg hd0.le (by linarith)
    nlinarith
  · apply div_le_div_of_nonneg_right _ (pow_nonneg hd0.le 3)
    linarith

theorem bOracle_not_unitary_conjugate (x : I)
    (U : Matrix ((I × Bool) × Unit) ((I × Bool) × Unit) ℂ)
    (hU : U ∈ Matrix.unitaryGroup ((I × Bool) × Unit) ℂ) :
    U * workspaceBitOracle (W := Unit) (fun y : I => decide (y = x)) * U ≠
      bOracle (W := Unit) x := by
  intro h
  apply bOracle_not_unitary x
  rw [← h]
  exact mul_mem (mul_mem hU (workspaceBitOracle_unitary _)) hU

theorem bOracle_preparation_leak (x : I) :
    (bOracle (W := Unit) x *ᵥ solverStart (I := I) (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket ()))
      ((x, true), ()) = -2 * ((Real.sqrt (Fintype.card I : ℝ))⁻¹ : ℂ) := by
  have hiff : ∀ i : I, (x = i ∧ i = x) ↔ i = x :=
    fun i => ⟨fun h => h.2, fun h => ⟨h.symm, h⟩⟩
  simp [Matrix.mulVec, dotProduct, bOracle, solverStart, uniformQState, Qatlib.Foundations.PureStateMath.Ket,
    Fintype.sum_prod_type, hiff]

theorem bOracle_preparation_ne (x : I) :
    bOracle (W := Unit) x *ᵥ solverStart (I := I) (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket ()) ≠
      (fun p : (I × Bool) × Unit => bState x p.1.1 * Qatlib.Foundations.PureStateMath.Ket false p.1.2 * Qatlib.Foundations.PureStateMath.Ket () p.2) := by
  letI : Nonempty I := ⟨x⟩
  have hs : Real.sqrt (Fintype.card I : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    exact_mod_cast Fintype.card_pos
  have hu : ((Real.sqrt (Fintype.card I : ℝ))⁻¹ : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero hs
  intro he
  have hp := congrFun he ((x, true), ())
  rw [bOracle_preparation_leak] at hp
  simp [Qatlib.Foundations.PureStateMath.Ket, hu] at hp

open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 300000

omit [DecidableEq I] in

private theorem uniform_mulVec (v : QState I) (i : I) :
    (uniformProjector (I := I)*ᵥv) i = ((Fintype.card I:ℝ)⁻¹:ℂ)*(∑ j,v j) := by
  simp only [Matrix.mulVec,dotProduct,uniformProjector_apply,Finset.mul_sum]

theorem grover_uniform_b (x : I) :
    uniformProjector (I := I)*ᵥbState x =
      ((1-2/(Fintype.card I:ℝ):ℝ):ℂ) • uniformQState (I := I) := by
  letI : Nonempty I := ⟨x⟩
  have hc : (Fintype.card I:ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext i
  rw [uniform_mulVec]
  simp only [bState,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,Pi.smul_apply,smul_eq_mul,uniformQState]
  push_cast
  rw [mul_sub,← mul_assoc,inv_mul_cancel₀ hc,one_mul]
  ring

theorem grover_inverse_b (x : I) :
    groverInverse (I := I)*ᵥbState x =
      fun i => (((1-2/(Fintype.card I:ℝ)+2/Real.sqrt (Fintype.card I:ℝ)):ℝ):ℂ) *
        (uniformQState (I := I) i) - if i=x then 2 else 0 := by
  letI : Nonempty I := ⟨x⟩
  have hd : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : Real.sqrt (Fintype.card I:ℝ) ≠ 0 := by positivity
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card I): (0:ℝ) ≤ _)
  ext i
  simp only [groverInverse,one_smul,Matrix.add_mulVec,Matrix.smul_mulVec,
    Matrix.sub_mulVec,Matrix.one_mulVec,grover_uniform_b,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Complex.real_smul,
    smul_eq_mul,uniformQState,bState]
  by_cases hi : i=x
  · simp only [if_pos hi]
    push_cast
    have hdC : (Fintype.card I:ℂ) = (Real.sqrt (Fintype.card I:ℝ):ℂ)^2 := by exact_mod_cast hsq.symm
    rw [hdC]
    field_simp
    ring
  · simp only [if_neg hi,sub_zero]
    push_cast
    have hdC : (Fintype.card I:ℂ) = (Real.sqrt (Fintype.card I:ℝ):ℂ)^2 := by exact_mod_cast hsq.symm
    rw [hdC]
    field_simp
    ring

theorem grover_solution_norm_sq (x : I) :
    ‖stateVector (groverInverse (I := I)*ᵥbState x)‖^2 =
      (5*(Fintype.card I:ℝ)^2-8*(Fintype.card I:ℝ)+4)/(Fintype.card I:ℝ)^2 := by
  letI : Nonempty I := ⟨x⟩
  let d : ℝ := Fintype.card I
  let s := Real.sqrt d
  let a := (1-2/d+2/s)/s
  have hd : 0 < d := by
    change (0:ℝ) < (Fintype.card I:ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card I)
  have hs : 0 < s := Real.sqrt_pos.mpr hd
  have hsq : s^2=d := Real.sq_sqrt hd.le
  rw [stateVector_norm_sq,grover_inverse_b]
  unfold MeasureProb BornProb
  have he (i : I) : ‖((((1-2/(Fintype.card I:ℝ)+2/Real.sqrt (Fintype.card I:ℝ)):ℝ):ℂ)*
      uniformQState (I := I) i-if i=x then 2 else 0)‖^2 =
      a^2+(if i=x then (4-4*a) else 0) := by
    have hc : (((1-2/(Fintype.card I:ℝ)+2/Real.sqrt (Fintype.card I:ℝ)):ℝ):ℂ)*
        uniformQState (I := I) i = (a:ℂ) := by
      dsimp [a,d,s,uniformQState]
      push_cast
      ring
    rw [hc]
    by_cases hi : i=x
    · simp only [if_pos hi]
      rw [← Complex.ofReal_ofNat,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      ring
    · simp only [if_neg hi,sub_zero,add_zero,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [Finset.sum_congr rfl (fun i _ => he i),Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  change d*a^2+(4-4*a) = (5*d^2-8*d+4)/d^2
  dsimp [a]
  rw [← hsq]
  field_simp
  ring

theorem groverInverse_norm (hcard : 2 ≤ Fintype.card I) :
    ‖groverInverse (I := I)‖ = Real.sqrt (Fintype.card I:ℝ) := by
  letI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  let s := Real.sqrt (Fintype.card I:ℝ)
  let Q : Matrix I I ℂ := 1-uniformProjector (I := I)
  have hs : 1 ≤ s := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    exact_mod_cast (show 1 ≤ Fintype.card I by omega)
  have hQ : Qᴴ=Q := by
    simp only [Q,Matrix.conjTranspose_sub,Matrix.conjTranspose_one,uniformProjector_selfAdjoint]
  have hQn : ‖Q‖ ≤ 1 := by
    have hh := Matrix.l2_opNorm_conjTranspose_mul_self Q
    rw [hQ,show Q*Q=Q from (uniformProjector_complement (I := I)).2.2] at hh
    nlinarith [norm_nonneg Q]
  have he : groverInverse (I := I)=1+(s-1) • Q := by
    simp only [groverInverse,one_smul,Q,s,sub_smul,one_smul]
    abel
  have hu : ‖groverInverse (I := I)‖ ≤ s := by
    rw [he]
    calc
      ‖(1:Matrix I I ℂ)+(s-1) • Q‖ ≤ ‖(1:Matrix I I ℂ)‖+‖(s-1) • Q‖ := norm_add_le _ _
      _ ≤ 1+(s-1)*1 := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hs)]
        exact add_le_add (by rw [← Matrix.diagonal_one,Matrix.l2_opNorm_diagonal]; simp)
            (mul_le_mul_of_nonneg_left hQn (sub_nonneg.mpr hs))
      _ = s := by ring
  obtain ⟨i,j,hij⟩ := Fintype.one_lt_card_iff.mp (show 1<Fintype.card I by omega)
  let v : QState I :=
      Qatlib.Foundations.PureStateMath.Ket i-Qatlib.Foundations.PureStateMath.Ket j
  have hv : v≠0 := by
    intro h
    have hh := congrFun h i
    simp [v,Qatlib.Foundations.PureStateMath.Ket,hij] at hh
  have hp : uniformProjector (I := I)*ᵥv=0 := by
    ext k
    rw [uniform_mulVec]
    simp [v,Qatlib.Foundations.PureStateMath.Ket,Finset.sum_sub_distrib]
  have hm : groverInverse (I := I)*ᵥv=s • v := by
    simp only [groverInverse,one_smul,Matrix.add_mulVec,Matrix.smul_mulVec,
      Matrix.sub_mulVec,Matrix.one_mulVec,hp,sub_zero,add_zero,s]
  have hl := stateVector_mulVec_norm_le (groverInverse (I := I)) v
  rw [hm,(show stateVector (s • v)=s • stateVector v from rfl),norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (le_trans zero_le_one hs)] at hl
  have hvn : 0<‖stateVector v‖ := norm_pos_iff.mpr (fun h => hv ((stateVector_eq_zero_iff v).mp h))
  apply le_antisymm hu
  nlinarith

theorem grover_solution_norm_bounds (x : I) (hcard : 4 ≤ Fintype.card I) :
    0<‖stateVector (groverInverse (I := I)*ᵥbState x)‖ ∧
    ‖stateVector (groverInverse (I := I)*ᵥbState x)‖ ≤ Real.sqrt 5 := by
  let d : ℝ := Fintype.card I
  have hd : 4≤d := by
    change (4:ℝ)≤(Fintype.card I:ℝ)
    exact_mod_cast hcard
  have hd0 : 0<d := by linarith
  have hh := grover_solution_norm_sq x
  change ‖stateVector (groverInverse (I := I)*ᵥbState x)‖^2=(5*d^2-8*d+4)/d^2 at hh
  have hlow : 0<(5*d^2-8*d+4)/d^2 := by
    apply div_pos _ (sq_pos_of_pos hd0)
    nlinarith [sq_nonneg (d-4)]
  have hup : (5*d^2-8*d+4)/d^2≤5 := by
    apply (div_le_iff₀ (sq_pos_of_pos hd0)).mpr
    nlinarith
  constructor
  · nlinarith [norm_nonneg (stateVector (groverInverse (I := I)*ᵥbState x))]
  · have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
    nlinarith [Real.sqrt_nonneg (5:ℝ)]

theorem grover_solution_marked_lower (x : I) (hcard : 4≤Fintype.card I) :
    2-1/Real.sqrt (Fintype.card I:ℝ)-2/(Fintype.card I:ℝ) ≤
      ‖(groverInverse (I := I)*ᵥbState x) x‖ := by
  let d : ℝ := Fintype.card I
  let s := Real.sqrt d
  have hd : 4≤d := by
    change (4:ℝ)≤(Fintype.card I:ℝ)
    exact_mod_cast hcard
  have hd0 : 0<d := by linarith
  have hs0 : 0<s := Real.sqrt_pos.mpr hd0
  have he : (groverInverse (I := I)*ᵥbState x) x = (((1-2/d+2/s)/s-2:ℝ):ℂ) := by
    rw [grover_inverse_b]
    simp only [uniformQState]
    dsimp [d,s]
    push_cast
    ring
  rw [he,Complex.norm_real,Real.norm_eq_abs]
  change 2-1/s-2/d ≤ |(1-2/d+2/s)/s-2|
  have hs2 : s^2=d := Real.sq_sqrt hd0.le
  have ha : (1-2/d+2/s)/s≤1/s+2/d := by
    apply (div_le_iff₀ hs0).mpr
    have hc : (1/s+2/d)*s=1+2/s := by rw [← hs2]; field_simp
    rw [hc]
    have := div_nonneg (by norm_num : (0:ℝ)≤2) hd0.le
    linarith
  have hab := neg_le_abs ((1-2/d+2/s)/s-2)
  linarith

theorem grover_normalized_marked_lower (x : I) (hcard : 4≤Fintype.card I) :
    (2-1/Real.sqrt (Fintype.card I:ℝ)-2/(Fintype.card I:ℝ))/Real.sqrt 5 ≤
      ‖NormedSpace.normalize (stateVector (groverInverse (I := I)*ᵥbState x)) x‖ := by
  have hn := grover_solution_norm_bounds x hcard
  have hm := grover_solution_marked_lower x hcard
  have he : ‖NormedSpace.normalize (stateVector (groverInverse (I := I)*ᵥbState x)) x‖ =
      ‖(groverInverse (I := I)*ᵥbState x) x‖ / ‖stateVector (groverInverse (I := I)*ᵥbState x)‖ := by
    simp only [NormedSpace.normalize,PiLp.smul_apply,Real.norm_eq_abs,norm_smul,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    simp [div_eq_mul_inv,mul_comm]
  rw [he]
  exact div_le_div₀ (norm_nonneg _) hm hn.1 hn.2

theorem grover_normalized_marked_five_sixths (x : I) (hcard : 150≤Fintype.card I) :
    5/6 ≤ ‖NormedSpace.normalize (stateVector (groverInverse (I := I)*ᵥbState x)) x‖ := by
  let d : ℝ := Fintype.card I
  have hd : 150≤d := by
    change (150:ℝ)≤(Fintype.card I:ℝ)
    exact_mod_cast hcard
  have hs : 12≤Real.sqrt d := by
    apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
    norm_num
    linarith
  have h1 : 1/Real.sqrt d≤1/12 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have h2 : 2/d≤2/150 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
  have h5 : Real.sqrt 5≤9/4 := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
    nlinarith [Real.sqrt_nonneg (5:ℝ)]
  have hg := grover_normalized_marked_lower x (by omega : 4≤Fintype.card I)
  have hnum : (571:ℝ)/300≤2-1/Real.sqrt d-2/d := by linarith
  have hf : (571:ℝ)/675 ≤ (2-1/Real.sqrt d-2/d)/Real.sqrt 5 := by
    have hh := div_le_div₀ (by linarith : (0:ℝ)≤2-1/Real.sqrt d-2/d) hnum
      (by positivity : (0:ℝ)<Real.sqrt 5) h5
    norm_num at hh
    simpa only [one_div] using hh
  change (2-1/Real.sqrt d-2/d)/Real.sqrt 5≤_ at hg
  linarith

end Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
