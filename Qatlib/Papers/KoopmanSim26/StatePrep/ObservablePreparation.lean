/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Papers.FixedPtSearch14.FixedPoint.SearchCore
import Mathlib.Tactic

/-!
# Coherent preparation of observable amplitudes

This module realizes the observable input preparation of [ZhangEtAl2026] using finite index and
value registers together with a Boolean success register. `preparation` applies a uniform index
transform, computes a value code, applies the complex amplitude gate `amplitudeGate`, and
uncomputes the code. `actual_success_amplitude` and `actual_success_probability` derive the
successful amplitudes and their total mass directly from this matrix construction.

For a nonzero `target`, `actual_postselection` identifies `postselected` with the normalized
complex target, preserving its coordinate phases. Balanced amplitude assumptions give a
probability lower bound and an inverse square root overhead bound. The module also provides an
explicit four gate preparation program and probability dependent amplitude amplification with
separate preparation and marked oracle access counts.

## Main statements

- `preparation_unitary` proves unitarity when the positive scale bounds all encoded values.
* `actual_success_probability` gives success mass equal to `targetNormSq` divided by 2^n G^2,
  and `actual_postselection` identifies the normalized output.
* `balanced_actual_probability` and `balanced_actual_overhead` derive the bounds eta c^2 and
  1/(c sqrt(eta)).
* `prepared_observables_aa` proves amplified success at least 1/2 with explicit access counts,
  while `preparation_program` gives the finite gate implementation.

## References

* [Zhang et al., 2026][ZhangEtAl2026], Quantum simulation of real-world nonlinear dynamics via
  Koopman method.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Papers.FixedPtSearch14.FixedPoint
open scoped Classical
set_option warningAsError false

namespace Qatlib.Papers.KoopmanSim26.StatePrep.Observables

/-- The Boolean gate whose false input column has amplitudes a and sqrt(1 - normSq(a)), with the
second column chosen using the conjugate of a. -/
noncomputable def amplitudeGate (a : ℂ) : Matrix Bool Bool ℂ :=
  fun r s => if s then (if r then star a else -(Real.sqrt (1-Complex.normSq a) : ℂ))
    else (if r then (Real.sqrt (1-Complex.normSq a) : ℂ) else a)

/-- The complex amplitude gate is unitary whenever the squared norm of its prescribed success
amplitude is at most one. -/
theorem amplitudeGate_unitary (a : ℂ) (ha : Complex.normSq a ≤ 1) :
    amplitudeGate a ∈ Matrix.unitaryGroup Bool ℂ := by
  have hs : (Real.sqrt (1-Complex.normSq a) : ℂ) * (Real.sqrt (1-Complex.normSq a) : ℂ) =
      1 - star a * a := by
    rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt (sub_nonneg.mpr ha), Complex.ofReal_sub,
      Complex.ofReal_one, Complex.normSq_eq_conj_mul_self]
    rfl
  change (Real.sqrt (1-Complex.normSq a) : ℂ) * (Real.sqrt (1-Complex.normSq a) : ℂ) =
    1 - (starRingEnd ℂ) a * a at hs
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext r s
  cases r <;> cases s <;>
    simp [amplitudeGate, Matrix.mul_apply, Matrix.conjTranspose_apply]
  all_goals first | linear_combination hs | ring

/-- The bitwise exclusive or of two value register strings. -/
def xorValue {m : ℕ} (v w : Reg m) : Reg m := fun k => v k ^^ w k

/-- The reversible basis map that adds the index's encoded value into the value register by
exclusive or while preserving the index and Boolean register. -/
def evaluateCode {n m : ℕ} (b : Reg n → Reg m) (x : Reg n × (Reg m × Bool)) :
    Reg n × (Reg m × Bool) := (x.1, (xorValue x.2.1 (b x.1), x.2.2))

/-- Applying the encoded value evaluation map twice restores every basis configuration. -/
theorem evaluateCode_involutive {n m : ℕ} (b : Reg n → Reg m) :
    Function.Involutive (evaluateCode b) := by
  intro ⟨j,v,r⟩
  change (j, (xorValue (xorValue v (b j)) (b j), r)) = (j,(v,r))
  have hx : xorValue (xorValue v (b j)) (b j) = v := by
    funext k
    simp [xorValue]
  exact congrArg (fun w : Reg m => (j,(w,r))) hx

/-- The permutation matrix implementing the reversible encoded value evaluation map
`evaluateCode`. -/
noncomputable def computeGate {n m : ℕ} (b : Reg n → Reg m) :
    Matrix (Reg n × (Reg m × Bool)) (Reg n × (Reg m × Bool)) ℂ := permMatrix (evaluateCode b)

/-- The coherent encoded value computation gate is unitary for every encoding function. -/
theorem computeGate_unitary {n m : ℕ} (b : Reg n → Reg m) :
    computeGate b ∈ Matrix.unitaryGroup (Reg n × (Reg m × Bool)) ℂ :=
  permMatrix_unitary (evaluateCode_involutive b)

/-- The gate that preserves the index and value registers and applies `amplitudeGate` with
amplitude `value v / G` to the Boolean register controlled by the value code v. -/
noncomputable def rotateGate {n m : ℕ} (value : Reg m → ℂ) (G : ℝ) :
    Matrix (Reg n × (Reg m × Bool)) (Reg n × (Reg m × Bool)) ℂ :=
  TensorGate (1 : Matrix (Reg n) (Reg n) ℂ) (select (fun v => amplitudeGate (value v / G)))

/-- The tensor product of the n qubit Hadamard transform on the index register with the identity
on the value and Boolean registers. -/
noncomputable def uniformGate (n m : ℕ) :
    Matrix (Reg n × (Reg m × Bool)) (Reg n × (Reg m × Bool)) ℂ :=
  TensorGate (HadamardN n) (1 : Matrix (Reg m × Bool) (Reg m × Bool) ℂ)

/-- The preparation matrix obtained by applying the uniform transform, computing the encoded
value, applying its controlled amplitude gate, and uncomputing the encoded value. -/
noncomputable def preparation {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ) (G : ℝ) :=
  computeGate b * rotateGate (n := n) value G * computeGate b * uniformGate n m

/-- The basis configuration with zero index and value strings and Boolean register false. -/
def seed (n m : ℕ) : Reg n × (Reg m × Bool) := (ZeroStr n, (ZeroStr m, false))

/-- The observable amplitude vector obtained by decoding the encoded value at each index. -/
def target {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ) : QState (Reg n) :=
  fun j => value (b j)

/-- The complete preparation matrix is unitary when G is positive and bounds the norm of every
decoded value. -/
theorem preparation_unitary {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hvalue : ∀ v, ‖value v‖ ≤ G) :
    preparation b value G ∈ Matrix.unitaryGroup (Reg n × (Reg m × Bool)) ℂ := by
  have hrot (v : Reg m) : amplitudeGate (value v / G) ∈ Matrix.unitaryGroup Bool ℂ := by
    apply amplitudeGate_unitary
    rw [Complex.normSq_eq_norm_sq]
    have hn : ‖value v / (G : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hG]
      exact (div_le_one hG).mpr (hvalue v)
    nlinarith [norm_nonneg (value v / (G : ℂ))]
  have hR := tensorGate_unitary
    (show (1 : Matrix (Reg n) (Reg n) ℂ) ∈ Matrix.unitaryGroup (Reg n) ℂ by simp)
    (select_unitary _ hrot)
  have hH := tensorGate_unitary (hadamardN_unitary n)
    (show (1 : Matrix (Reg m × Bool) (Reg m × Bool) ℂ) ∈ Matrix.unitaryGroup (Reg m × Bool) ℂ by simp)
  exact (Matrix.unitaryGroup _ ℂ).mul_mem
    ((Matrix.unitaryGroup _ ℂ).mul_mem ((Matrix.unitaryGroup _ ℂ).mul_mem
      (computeGate_unitary b) hR) (computeGate_unitary b)) hH

/-- The amplitude of a state after coherent computation at a configuration x equals its original
amplitude at `evaluateCode b x`. -/
theorem compute_apply {n m : ℕ} (b : Reg n → Reg m)
    (ψ : QState (Reg n × (Reg m × Bool))) (x : Reg n × (Reg m × Bool)) :
    (computeGate b *ᵥ ψ) x = ψ (evaluateCode b x) :=
  applyGate_permMatrix (evaluateCode_involutive b) ψ x

/-- For fixed index and value code, the controlled rotation acts on the two Boolean amplitudes
by the matrix `amplitudeGate (value v / G)`. -/
theorem rotate_apply {n m : ℕ} (value : Reg m → ℂ) (G : ℝ)
    (ψ : QState (Reg n × (Reg m × Bool))) (j : Reg n) (v : Reg m) (r : Bool) :
    (rotateGate value G *ᵥ ψ) (j,(v,r)) =
      ∑ s : Bool, amplitudeGate (value v / G) r s * ψ (j,(v,s)) := by
  simp [rotateGate, TensorGate, select, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply]

/-- Applying the uniform gate to the seed produces uniform index amplitudes supported on the
zero value register and Boolean false. -/
theorem uniform_amplitude (n m : ℕ) (j : Reg n) (v : Reg m) (r : Bool) :
    (uniformGate n m *ᵥ Ket (seed n m)) (j,(v,r)) =
      (Uniform (Reg n) j) * (if v=ZeroStr m ∧ r=false then 1 else 0) := by
  change ApplyGate (uniformGate n m) (Ket (seed n m)) (j,(v,r)) = _
  rw [applyGate_eq_mulVec_ket]
  change HadamardN n j (ZeroStr n) *
    (1 : Matrix (Reg m × Bool) (Reg m × Bool) ℂ) (v,r) (ZeroStr m,false) = _
  simp only [Matrix.one_apply, Prod.mk.injEq]
  have hU := congrFun (applyGate_hadamardN_ket_zero n) j
  rw [applyGate_eq_mulVec_ket] at hU
  rw [hU]

/-- The prepared state is supported on the zero value register, where its amplitude is the
uniform index amplitude times the corresponding entry of the target controlled amplitude
gate. -/
theorem preparation_amplitude {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (j : Reg n) (v : Reg m) (r : Bool) :
    (preparation b value G *ᵥ Ket (seed n m)) (j,(v,r)) =
      if v=ZeroStr m then Uniform (Reg n) j * amplitudeGate (target b value j / G) r false else 0 := by
  simp only [preparation, ← Matrix.mulVec_mulVec]
  rw [compute_apply, rotate_apply]
  simp only [compute_apply, evaluateCode]
  have hx : xorValue (xorValue v (b j)) (b j) = v := by
    funext k
    simp [xorValue]
  simp only [hx, uniform_amplitude]
  by_cases hv : v=ZeroStr m
  · subst v
    have hzero : xorValue (ZeroStr m) (b j) = b j := by funext k; simp [xorValue, ZeroStr]
    simp [hzero, target, mul_comm]
  · simp [hv]

/-- The successful basis configurations, with arbitrary index, zero value register, and Boolean
register false. -/
def goodSet (n m : ℕ) : Finset (Reg n × (Reg m × Bool)) :=
  Finset.univ.filter (fun x => x.2.1=ZeroStr m ∧ x.2.2=false)

/-- The mass on `goodSet` is the sum over indices of the squared norms of the amplitudes with
zero value register and Boolean false. -/
theorem measure_good {n m : ℕ} (ψ : QState (Reg n × (Reg m × Bool))) :
    MeasureProb ψ (goodSet n m) = ∑ j, ‖ψ (j,(ZeroStr m,false))‖^2 := by
  simp [goodSet, MeasureProb, Finset.sum_filter, Fintype.sum_prod_type, BornProb]

/-- Each successful prepared amplitude equals the target amplitude at that index divided by
sqrt(2^n) G. For positive G, this preserves the phase of every nonzero target amplitude, as
in the observable preparation construction of [ZhangEtAl2026]. -/
theorem actual_success_amplitude {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (j : Reg n) :
    (preparation b value G *ᵥ Ket (seed n m)) (j,(ZeroStr m,false)) =
      target b value j / ((Real.sqrt ((2:ℝ)^n) * G : ℝ) : ℂ) := by
  rw [preparation_amplitude]
  simp [amplitudeGate, Uniform]
  ring

/-- The sum of squared norms of the decoded observable target amplitudes. -/
noncomputable def targetNormSq {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ) : ℝ :=
  ∑ j, ‖target b value j‖^2

/-- For positive G, the prepared state's success mass is `targetNormSq b value` divided by 2^n
G^2, giving the explicit observable preparation probability described in [ZhangEtAl2026]. -/
theorem actual_success_probability {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (_hG : 0 < G) :
    MeasureProb (preparation b value G *ᵥ Ket (seed n m)) (goodSet n m) =
      targetNormSq b value / ((2:ℝ)^n * G^2) := by
  rw [measure_good]
  simp_rw [actual_success_amplitude]
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs,
    div_pow, sq_abs, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (2:ℝ)^n)]
  rw [← Finset.sum_div]
  rfl

/-- A nonzero target vector has strictly positive sum of squared amplitude norms. -/
theorem targetNormSq_pos {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (hu : target b value ≠ 0) : 0 < targetNormSq b value := by
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hu
  apply Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨j, Finset.mem_univ _, ?_⟩
  exact sq_pos_of_pos (norm_pos_iff.mpr hj)

/-- The successful index amplitude vector divided by the square root of the prepared state's
total success mass. -/
noncomputable def postselected {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ) (G : ℝ) :
    QState (Reg n) := fun j =>
  (preparation b value G *ᵥ Ket (seed n m)) (j,(ZeroStr m,false)) /
    (Real.sqrt (MeasureProb (preparation b value G *ᵥ Ket (seed n m)) (goodSet n m)) : ℂ)

/-- For positive G, the square root of the success mass equals the target norm divided by
sqrt(2^n) G. -/
theorem actual_success_sqrt {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) :
    Real.sqrt (MeasureProb (preparation b value G *ᵥ Ket (seed n m)) (goodSet n m)) =
    Real.sqrt (targetNormSq b value) / (Real.sqrt ((2:ℝ)^n) * G) := by
  have hS0 : 0 ≤ targetNormSq b value := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [actual_success_probability b value G hG, Real.sqrt_div hS0, Real.sqrt_mul (by positivity),
    Real.sqrt_sq hG.le]

/-- For positive G and a nonzero target, postselection yields the target vector divided by its
norm, as required by the observable preparation construction of [ZhangEtAl2026]. The
resulting index state is normalized. -/
theorem actual_postselection {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hu : target b value ≠ 0) :
    postselected b value G = (fun j => target b value j / (Real.sqrt (targetNormSq b value) : ℂ)) ∧
      Normalized (postselected b value G) := by
  have hS : 0 < targetNormSq b value := targetNormSq_pos b value hu
  have hroot : (Real.sqrt (targetNormSq b value) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hS).ne'
  have hden : ((Real.sqrt ((2:ℝ)^n) * G : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (Real.sqrt_pos.mpr (by positivity : 0 < (2:ℝ)^n)) hG).ne'
  have hGc : (G : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
  have hNc : (Real.sqrt ((2:ℝ)^n) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < (2:ℝ)^n)).ne'
  have heq : postselected b value G = (fun j => target b value j / (Real.sqrt (targetNormSq b value) : ℂ)) := by
    funext j
    rw [postselected, actual_success_amplitude, actual_success_sqrt b value G hG]
    push_cast
    field_simp [hroot, hGc, hNc]
  refine ⟨heq, ?_⟩
  rw [heq]
  unfold Normalized
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs, Real.sq_sqrt hS.le]
  rw [← Finset.sum_div]
  exact div_self hS.ne'

/-- If at least an eta fraction of indices have target amplitude norm at least cG, with positive
G, c, and eta, then the squared target norm is at least eta 2^n c^2 G^2. -/
theorem balanced_target_norm {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G c η : ℝ) (hG : 0 < G) (hc : 0 < c) (_hη : 0 < η) (S : Finset (Reg n))
    (hcard : η * (2:ℝ)^n ≤ S.card)
    (hbig : ∀ j ∈ S, c * G ≤ ‖target b value j‖) :
    η * (2:ℝ)^n * c^2 * G^2 ≤ targetNormSq b value := by
  have hsum : (S.card : ℝ) * (c*G)^2 ≤ ∑ j ∈ S, ‖target b value j‖^2 := by
    calc
      _ = ∑ _j ∈ S, (c*G)^2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun j hj => by
        exact (sq_le_sq₀ (mul_nonneg hc.le hG.le) (norm_nonneg _)).2 (hbig j hj)
  have hsub : (∑ j ∈ S, ‖target b value j‖^2) ≤ targetNormSq b value := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro j _ _
    positivity
  have hmul := mul_le_mul_of_nonneg_right hcard (sq_nonneg (c*G))
  nlinarith [hsum.trans hsub]

/-- For positive G, c, and eta, a set containing at least an eta fraction of the indices with
amplitude norms at least cG gives prepared success mass at least eta c^2, realizing the
balanced observable probability bound of [ZhangEtAl2026]. -/
theorem balanced_actual_probability {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G c η : ℝ) (hG : 0 < G) (hc : 0 < c) (hη : 0 < η) (S : Finset (Reg n))
    (hcard : η * (2:ℝ)^n ≤ S.card)
    (hbig : ∀ j ∈ S, c * G ≤ ‖target b value j‖) :
    η*c^2 ≤ MeasureProb (preparation b value G *ᵥ Ket (seed n m)) (goodSet n m) := by
  rw [actual_success_probability b value G hG]
  apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^n * G^2)).mpr
  nlinarith [balanced_target_norm b value G c η hG hc hη S hcard hbig]

/-- When positive G bounds every decoded value norm, the actual success mass of the prepared
state is at most one. -/
theorem actual_probability_le_one {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hvalue : ∀ v, ‖value v‖ ≤ G) :
    MeasureProb (preparation b value G *ᵥ Ket (seed n m)) (goodSet n m) ≤ 1 := by
  rw [actual_success_probability b value G hG]
  apply (div_le_one (by positivity : 0 < (2:ℝ)^n * G^2)).mpr
  calc
    targetNormSq b value ≤ ∑ _j : Reg n, G^2 := by
      apply Finset.sum_le_sum
      intro j _
      exact (sq_le_sq₀ (norm_nonneg _) hG.le).2 (hvalue (b j))
    _ = (2:ℝ)^n * G^2 := by simp

/-- For positive G, the inverse square root of the success mass equals sqrt(2^n) G divided by
the target norm. -/
theorem actual_overhead {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) :
    1 / Real.sqrt (MeasureProb (preparation b value G *ᵥ Ket (seed n m)) (goodSet n m)) =
      Real.sqrt ((2:ℝ)^n) * G / Real.sqrt (targetNormSq b value) := by
  rw [actual_success_sqrt b value G hG]
  simp

/-- For positive G, c, and eta, balanced target amplitudes bound sqrt(2^n) G divided by the
target norm by 1/(c sqrt(eta)), giving the conditional amplification overhead in
[ZhangEtAl2026]. -/
theorem balanced_actual_overhead {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G c η : ℝ) (hG : 0 < G) (hc : 0 < c) (hη : 0 < η) (S : Finset (Reg n))
    (hcard : η * (2:ℝ)^n ≤ S.card)
    (hbig : ∀ j ∈ S, c * G ≤ ‖target b value j‖) :
    Real.sqrt ((2:ℝ)^n) * G / Real.sqrt (targetNormSq b value) ≤ 1/(c*Real.sqrt η) := by
  rw [← actual_overhead b value G hG]
  have hs := Real.sqrt_le_sqrt (balanced_actual_probability b value G c η hG hc hη S hcard hbig)
  rw [Real.sqrt_mul hη.le, Real.sqrt_sq hc.le] at hs
  apply one_div_le_one_div_of_le (mul_pos hc (Real.sqrt_pos.mpr hη))
  simpa only [mul_comm] using! hs

/-- Chooses the phase marking peak round count at angle arcsin(sqrt(p)) when p is less than 1/2,
and zero rounds otherwise. -/
noncomputable def aaRounds (p : ℝ) : ℕ :=
  if p < 1/2 then phaseMarkPeakRounds (Real.arcsin (Real.sqrt p)) else 0

/-- For a unitary preparation with marked probability p in (0, 1], the selected round count k
achieves marked probability at least 1/2 using exactly 2k + 1 preparation accesses and k
marked oracle accesses. The preparation access count is at most (pi/2 + 1)/sqrt(p). -/
theorem actual_aa_success_and_count {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (hp0 : 0 < MeasureProb (preparedAAState A j) S)
    (hp1 : MeasureProb (preparedAAState A j) S ≤ 1) :
    let p := MeasureProb (preparedAAState A j) S
    let k := aaRounds p
    1/2 ≤ MeasureProb (Run (preparedMark S) (preparedAACircuit A j k) (Ket j)) S ∧
    preparedInputQueries (preparedAAWord j k) = 2*k+1 ∧
    preparedDataQueries (preparedAAWord j k) = k ∧
    (preparedInputQueries (preparedAAWord j k) : ℝ) ≤ (Real.pi/2+1) / Real.sqrt p := by
  (try dsimp only)
  let p := MeasureProb (preparedAAState A j) S
  change 1/2 ≤ MeasureProb (Run (preparedMark S) (preparedAACircuit A j (aaRounds p)) (Ket j)) S ∧
    preparedInputQueries (preparedAAWord j (aaRounds p)) = 2*aaRounds p+1 ∧
    preparedDataQueries (preparedAAWord j (aaRounds p)) = aaRounds p ∧
    (preparedInputQueries (preparedAAWord j (aaRounds p)) : ℝ) ≤ (Real.pi/2+1) / Real.sqrt p
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hs1 : Real.sqrt p ≤ 1 := (Real.sqrt_le_one).2 hp1
  have hsquare : (Real.sqrt p)^2 = p := Real.sq_sqrt hp0.le
  have hsSin : Real.sin (Real.arcsin (Real.sqrt p)) = Real.sqrt p :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg p]) hs1
  have hθ0 : 0 < Real.arcsin (Real.sqrt p) := Real.arcsin_pos.mpr hs0
  by_cases hp : p < 1/2
  · have hslt : Real.sqrt p < 1 := by nlinarith
    have hθ1 : Real.arcsin (Real.sqrt p) < Real.pi/2 := Real.arcsin_lt_pi_div_two.mpr hslt
    have hmass : p = (Real.sin (Real.arcsin (Real.sqrt p)))^2 := by rw [hsSin, hsquare]
    have hsuccess := phase_mark_peak_success A j S (Real.arcsin (Real.sqrt p)) hA hθ0 hθ1 hmass
    have hr := phase_mark_peak_rounds_bound (Real.arcsin (Real.sqrt p)) hθ0
    have hsθ : Real.sqrt p ≤ Real.arcsin (Real.sqrt p) := by
      simpa only [hsSin] using! Real.sin_le hθ0.le
    have hledger := prepared_aa_separate_access_word A j S
      (phaseMarkPeakRounds (Real.arcsin (Real.sqrt p))) hA
    simp only [aaRounds, hp, if_true]
    refine ⟨?_, hledger.2.2.1, hledger.2.1, ?_⟩
    · rw [← hmass] at hsuccess
      linarith
    · rw [hledger.2.2.1]
      apply (le_div_iff₀ hs0).mpr
      have hk : (0:ℝ) ≤ phaseMarkPeakRounds (Real.arcsin (Real.sqrt p)) := Nat.cast_nonneg _
      have hmul := mul_le_mul_of_nonneg_left hsθ hk
      push_cast
      nlinarith [hr.1]
  · have hledger := prepared_aa_separate_access_word A j S 0 hA
    simp only [aaRounds, hp, if_false]
    refine ⟨?_, hledger.2.2.1, hledger.2.1, ?_⟩
    · simpa [preparedAACircuit, preparedAAState] using! (show 1/2 ≤ p by linarith)
    · rw [hledger.2.2.1]
      apply (le_div_iff₀ hs0).mpr
      norm_num
      linarith [Real.pi_pos]

/-- For bounded observable values and a nonzero target, the probability dependent amplification
count k achieves success at least 1/2 with exactly 2k + 1 preparation accesses and k marked
oracle accesses. The preparation access count is at most (pi/2 + 1) sqrt(2^n) G divided by
the target norm. -/
theorem prepared_observables_aa {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hvalue : ∀ v, ‖value v‖ ≤ G) (hu : target b value ≠ 0) :
    let A := preparation b value G
    let p := MeasureProb (preparedAAState A (seed n m)) (goodSet n m)
    let k := aaRounds p
    1/2 ≤ MeasureProb (Run (preparedMark (goodSet n m))
      (preparedAACircuit A (seed n m) k) (Ket (seed n m))) (goodSet n m) ∧
    preparedInputQueries (preparedAAWord (seed n m) k) = 2*k+1 ∧
    preparedDataQueries (preparedAAWord (seed n m) k) = k ∧
    (preparedInputQueries (preparedAAWord (seed n m) k) : ℝ) ≤
      (Real.pi/2+1) * (Real.sqrt ((2:ℝ)^n) * G / Real.sqrt (targetNormSq b value)) := by
  have hp : 0 < MeasureProb (preparation b value G *ᵥ Ket (seed n m)) (goodSet n m) := by
    rw [actual_success_probability b value G hG]
    exact div_pos (targetNormSq_pos b value hu) (by positivity)
  have ha := actual_aa_success_and_count (preparation b value G)
    (preparation_unitary b value G hG hvalue) (seed n m) (goodSet n m) hp
    (actual_probability_le_one b value G hG hvalue)
  refine ⟨ha.1, ha.2.1, ha.2.2.1, ?_⟩
  have hr := actual_overhead b value G hG
  change 1 / Real.sqrt
      (MeasureProb (preparedAAState (preparation b value G) (seed n m)) (goodSet n m)) = _ at hr
  have hb := ha.2.2.2
  have hb' : (preparedInputQueries (preparedAAWord (seed n m)
    (aaRounds (MeasureProb (preparedAAState (preparation b value G) (seed n m)) (goodSet n m)))) : ℝ) ≤
    (Real.pi/2+1) * (1 / Real.sqrt (MeasureProb (preparedAAState (preparation b value G) (seed n m)) (goodSet n m))) := by
    simpa only [one_div, div_eq_mul_inv, one_mul] using! hb
  rw [hr] at hb'
  exact hb'

/-- The three primitive operation labels for observable preparation: uniform index generation,
coherent value computation, and controlled amplitude rotation. -/
inductive PrepareOp where
  | uniform
  | compute
  | rotate
  deriving DecidableEq

/-- The preparation operation list in execution order: uniform generation, value computation,
controlled rotation, and value uncomputation using the same computation gate. -/
def preparationOps : List PrepareOp := [.uniform, .compute, .rotate, .compute]

/-- Assigns to each preparation operation label its uniform, coherent computation, or controlled
amplitude matrix. -/
noncomputable def prepareOpMatrix {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ) (G : ℝ) :
    PrepareOp → Matrix (Reg n × (Reg m × Bool)) (Reg n × (Reg m × Bool)) ℂ
  | .uniform => uniformGate n m
  | .compute => computeGate b
  | .rotate => rotateGate value G

/-- The gate circuit obtained by replacing each entry of `preparationOps` with its corresponding
matrix gate. -/
noncomputable def preparationCircuit {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ) (G : ℝ) :
    Circuit (Reg n × (Reg m × Bool)) :=
  preparationOps.map (fun op => Step.gate (prepareOpMatrix b value G op))

/-- Executing the preparation circuit acts by the matrix `preparation` on every input state. Its
four gates consist of two computation gates, one controlled rotation, and one uniform
transform. -/
theorem preparation_program {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (ψ : QState (Reg n × (Reg m × Bool))) :
    Run 1 (preparationCircuit b value G) ψ = preparation b value G *ᵥ ψ ∧
    preparationOps.count .compute = 2 ∧ preparationOps.count .rotate = 1 ∧
    preparationOps.count .uniform = 1 ∧ GateCount (preparationCircuit b value G) = 4 := by
  constructor
  · simp only [preparationCircuit, preparationOps, List.map_cons, List.map_nil, prepareOpMatrix,
      run_gate, run_nil, ApplyGate, preparation, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · simp [preparationOps, preparationCircuit]

/-- If the initial marked mass is sin(theta)^2 for theta strictly between zero and pi/2, then
each marked amplitude after k rounds is its original prepared amplitude multiplied by
sin((2k + 1) theta)/sin(theta). -/
theorem actual_marked_amplitude {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (θ : ℝ) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2)
    (hmass : MeasureProb (preparedAAState A j) S = (Real.sin θ)^2) (i : I) (hi : i ∈ S) :
    Run (preparedMark S) (preparedAACircuit A j k) (Ket j) i =
      ((Real.sin ((2*(k:ℝ)+1)*θ) / Real.sin θ : ℝ) : ℂ) * preparedAAState A j i := by
  rw [prepared_aa_actual_rotation A j S θ k hA hθ0 hθ1 hmass]
  simp [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, collapse_apply, hi]

/-- For positive G, c, and eta, bounded observable values and a nonzero target satisfying the
balanced amplitude assumptions give a selected amplification word using at most (pi/2 +
1)/(c sqrt(eta)) preparation accesses. -/
theorem balanced_prepared_aa_count {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G c η : ℝ) (hG : 0 < G) (hc : 0 < c) (hη : 0 < η)
    (hvalue : ∀ v, ‖value v‖ ≤ G) (hu : target b value ≠ 0) (S : Finset (Reg n))
    (hcard : η * (2:ℝ)^n ≤ S.card)
    (hbig : ∀ j ∈ S, c * G ≤ ‖target b value j‖) :
    let p := MeasureProb (preparedAAState (preparation b value G) (seed n m)) (goodSet n m)
    (preparedInputQueries (preparedAAWord (seed n m) (aaRounds p)) : ℝ) ≤
      (Real.pi/2+1) / (c*Real.sqrt η) := by
  have ha := (prepared_observables_aa b value G hG hvalue hu).2.2.2
  have hb := balanced_actual_overhead b value G c η hG hc hη S hcard hbig
  calc
    _ ≤ (Real.pi/2+1) * (Real.sqrt ((2:ℝ)^n) * G / Real.sqrt (targetNormSq b value)) := ha
    _ ≤ (Real.pi/2+1) * (1/(c*Real.sqrt η)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end Qatlib.Papers.KoopmanSim26.StatePrep.Observables
