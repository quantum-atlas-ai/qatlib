/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Foundations.PureStateMath.Tensor
public import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform

@[expose] public section
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QueryComplexity.FourierModel.FourierDefs

open Matrix

open scoped BigOperators

set_option linter.unusedSectionVars false

variable {q n : ℕ} [NeZero q] {W : Type} [Fintype W] [DecidableEq W]

abbrev XReg (q n : ℕ) := Fin n → ZMod q

abbrev AReg (q n : ℕ) (W : Type) := (Fin n × ZMod q) × W

abbrev JointReg (q n : ℕ) (W : Type) := XReg q n × AReg q n W

noncomputable def fourierTensor (σ : XReg q n) : QState (XReg q n) :=
  fun x => ∏ i, charState (σ i) (x i)

noncomputable def uniformInitialState (ψ_init : QState (AReg q n W)) :
    QState (JointReg q n W) :=
  TensorState (Uniform (XReg q n)) ψ_init

noncomputable def phaseOracleQ (x : XReg q n) :
    Matrix (AReg q n W) (AReg q n W) ℂ :=
  fun a a' => if a = a' then ZMod.stdAddChar (a.1.2 * x a.1.1) else 0

noncomputable def jointPhaseOracle : Matrix (JointReg q n W) (JointReg q n W) ℂ :=
  fun p p' => if p = p' then ZMod.stdAddChar (p.2.1.2 * p.1 p.2.1.1) else 0

def supportCard (σ : XReg q n) : ℕ :=
  Finset.card (Finset.univ.filter fun i => σ i ≠ 0)

def MemKnowledgeSupport (ψ : QState (JointReg q n W)) (t : ℕ) : Prop :=
  ∃ w : XReg q n → QState (AReg q n W),
    ψ = fun p =>
      ∑ σ ∈ Finset.univ.filter fun σ => supportCard σ ≤ t,
        TensorState (fourierTensor σ) (w σ) p

noncomputable def jointGate (U : Matrix (AReg q n W) (AReg q n W) ℂ) :
    Matrix (JointReg q n W) (JointReg q n W) ℂ :=
  fun p p' => if p.1 = p'.1 then U p.2 p'.2 else 0

noncomputable def jointLift (C : Circuit (AReg q n W)) : Circuit (JointReg q n W) :=
  C.map fun s =>
    match s with
    | .gate U => .gate (jointGate U)
    | .query => .query

/-- A diagonal complex matrix whose diagonal entries have norm one is unitary. -/
private theorem mem_unitaryGroup_diag {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (d : I → ℂ)
    (hM : ∀ i j : I, M i j = if i = j then d i else 0) (hd : ∀ i : I, ‖d i‖ = 1) :
    M ∈ Matrix.unitaryGroup I ℂ := by
  have hcentry : ∀ i j : I, (star M) i j = if j = i then star (d j) else 0 := by
    intro i j
    rw [Matrix.star_apply, hM j i]
    by_cases h : j = i
    · simp [h]
    · rw [ite_eq_right h, ite_eq_right h, star_zero]
  have tone : ∀ i : I, d i * star (d i) = 1 := by
    intro i
    rw [RCLike.star_def, mul_comm, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hd i]
    norm_num
  have tone' : ∀ i : I, star (d i) * d i = 1 := fun i => by rw [mul_comm]; exact tone i
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  simp only [Matrix.mul_apply, hcentry, hM, ite_mul, mul_ite, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.one_apply]
  by_cases h : i = j
  · rw [ite_eq_left h, ite_eq_left h.symm]
    exact tone' _
  · rw [ite_eq_right h, ite_eq_right (fun hh => h hh.symm)]

/-- Adding a single-coordinate frequency to `fourierTensor` multiplies its value by the
corresponding additive character. -/
theorem fourierTensor_add_single (σ : XReg q n) (i : Fin n) (c : ZMod q) (x : XReg q n) :
    fourierTensor (σ + Pi.single i c) x = ZMod.stdAddChar (c * x i) * fourierTensor σ x := by
  have key : ∀ j : Fin n, charState ((σ + Pi.single i c : XReg q n) j) (x j)
      = charState (σ j) (x j) * (if i = j then ZMod.stdAddChar (c * x i) else 1) := by
    intro j
    rw [charState_apply, charState_apply, Pi.add_apply, Pi.single_apply]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, add_mul, AddChar.map_add_eq_mul, ite_eq_left rfl]
      ring
    · rw [ite_eq_right (fun h => hij h.symm), add_zero, ite_eq_right hij, mul_one]
  simp only [fourierTensor]
  rw [Finset.prod_congr rfl fun j _ => key j, Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq, Finset.mem_univ, ite_true]
  ring

set_option maxHeartbeats 800000 in

/-- Adding a single-coordinate frequency increases support cardinality by at most one. -/
theorem supportCard_add_single_le (σ : XReg q n) (i : Fin n) (c : ZMod q) :
    supportCard (σ + Pi.single i c) ≤ supportCard σ + 1 := by
  have hsub : ∀ j ∈ Finset.univ.filter fun j => (σ + Pi.single i c : XReg q n) j ≠ 0,
      j ∈ insert i (Finset.univ.filter fun j => σ j ≠ 0) := by
    intro j hj
    have hj' : (σ + Pi.single i c : XReg q n) j ≠ 0 := (Finset.mem_filter.mp hj).2
    rw [Pi.add_apply, Pi.single_apply] at hj'
    by_cases h : i = j
    · rw [ite_eq_left h.symm] at hj'
      exact Finset.mem_insert.mpr (Or.inl h.symm)
    · rw [ite_eq_right (fun h' => h h'.symm), add_zero] at hj'
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj'⟩))
  calc supportCard (σ + Pi.single i c)
      = (Finset.univ.filter fun j => (σ + Pi.single i c : XReg q n) j ≠ 0).card := rfl
    _ ≤ (insert i (Finset.univ.filter fun j => σ j ≠ 0)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter fun j => σ j ≠ 0).card + 1 := Finset.card_insert_le _ _
    _ = supportCard σ + 1 := rfl

/-- The register type `XReg q n` has cardinality `q` to the power `n`. -/
private theorem card_xReg : Fintype.card (XReg q n) = q ^ n := by
  rw [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The register type `XReg q n` has positive cardinality. -/
private theorem card_xReg_pos : 0 < Fintype.card (XReg q n) := by
  rw [card_xReg]
  exact Nat.pos_of_ne_zero (pow_ne_zero n (NeZero.ne q))

/-- Every algorithm state is the sum of its computational basis kets scaled by their amplitudes. -/
private theorem eq_sum_ket_smul (v : QState (AReg q n W)) :
    v = ∑ a : AReg q n W, v a • Ket a := by
  funext b
  rw [Finset.sum_apply, Finset.sum_eq_single b]
  · simp
  · intro a _ ha
    show v a * (if b = a then (1 : ℂ) else 0) = 0
    rw [ite_eq_right (Ne.symm ha), mul_zero]
  · simp

/-- Tensoring with a fixed first state distributes over a finite sum in the second state,
coordinatewise. -/
private theorem tensorState_sum_apply {κ : Type*} (f : QState (XReg q n))
    (g : κ → QState (AReg q n W)) (s : Finset κ) (p : JointReg q n W) :
    TensorState f (∑ k ∈ s, g k) p = ∑ k ∈ s, TensorState f (g k) p := by
  simp only [TensorState, Finset.sum_apply, Finset.mul_sum]

/-- Tensoring with a fixed first state distributes over a finite conditional sum in the second
state, coordinatewise. -/
private theorem tensorState_sum_ite_apply {κ : Type*} (f : QState (XReg q n))
    (g : κ → QState (AReg q n W)) (c : κ → Prop) [DecidablePred c] (s : Finset κ)
    (p : JointReg q n W) :
    TensorState f (∑ k ∈ s, if c k then g k else 0) p
      = ∑ k ∈ s, if c k then TensorState f (g k) p else 0 := by
  simp only [TensorState, Finset.sum_apply, ite_apply, Pi.zero_apply, Finset.mul_sum,
    mul_ite, mul_zero]

/-- A joint algorithm gate acts on the algorithm factor of a tensor state while preserving its
input-register factor. -/
theorem jointGate_mulVec_tensorState (U : Matrix (AReg q n W) (AReg q n W) ℂ)
    (f : QState (XReg q n)) (v : QState (AReg q n W)) :
    jointGate (q := q) (n := n) (W := W) U *ᵥ TensorState f v = TensorState f (U *ᵥ v) := by
  have hJG : jointGate (q := q) (n := n) (W := W) U
      = TensorGate (1 : Matrix (XReg q n) (XReg q n) ℂ) U := by
    ext p p'
    obtain ⟨x, a⟩ := p
    obtain ⟨x', a'⟩ := p'
    by_cases h : x = x' <;> simp [jointGate, tensorGate_apply, h]
  calc jointGate (q := q) (n := n) (W := W) U *ᵥ TensorState f v
      = ApplyGate (TensorGate (1 : Matrix (XReg q n) (XReg q n) ℂ) U) (TensorState f v) := by
        rw [hJG]
        rfl
    _ = TensorState (ApplyGate (1 : Matrix (XReg q n) (XReg q n) ℂ) f) (ApplyGate U v) :=
        applyGate_tensorGate _ _ _ _
    _ = TensorState f (U *ᵥ v) := by
        rw [applyGate_one]
        rfl

/-- Joint lifting sends the empty circuit to the empty circuit. -/
@[simp] theorem jointLift_nil : jointLift (q := q) (n := n) (W := W) [] = [] := rfl

/-- Joint lifting transforms a leading gate into its joint gate and recursively lifts the tail. -/
@[simp] theorem jointLift_gate (U : Matrix (AReg q n W) (AReg q n W) ℂ)
    (C : Circuit (AReg q n W)) :
    jointLift (q := q) (n := n) (W := W) (Step.gate U :: C)
      = Step.gate (jointGate U) :: jointLift C := rfl

/-- Joint lifting preserves a leading query and recursively lifts the tail. -/
@[simp] theorem jointLift_query (C : Circuit (AReg q n W)) :
    jointLift (q := q) (n := n) (W := W) (Step.query :: C)
      = Step.query :: jointLift C := rfl

/-- The phase oracle over `ZMod q` is unitary. -/
theorem phaseOracleQ_unitary (x : XReg q n) :
    phaseOracleQ (q := q) (n := n) (W := W) x ∈ Matrix.unitaryGroup (AReg q n W) ℂ :=
  mem_unitaryGroup_diag (phaseOracleQ (q := q) (n := n) (W := W) x)
    (fun a => ZMod.stdAddChar (a.1.2 * x a.1.1)) (fun _ _ => rfl)
    (fun _ => norm_stdAddChar _)

/-- The Fourier tensor states are orthonormal. -/
theorem fourierTensor_orthonormal (σ τ : XReg q n) :
    Inner (fourierTensor (q := q) (n := n) σ) (fourierTensor (q := q) (n := n) τ)
      = if σ = τ then 1 else 0 := by
  have hq : 0 < q := NeZero.pos q
  have hne : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hsq : (Real.sqrt (q : ℝ) : ℂ) * (Real.sqrt (q : ℝ) : ℂ) = (q : ℂ) := by
    have h2 : (Real.sqrt (q : ℝ) : ℂ) ^ 2 = (q : ℂ) :=
      by exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq.le)
    rw [← h2, pow_two]
  have hterm : ∀ x : XReg q n, (starRingEnd ℂ) (fourierTensor σ x) * fourierTensor τ x
      = ∏ i : Fin n, ((Real.sqrt (q : ℝ) : ℂ)⁻¹ * (Real.sqrt (q : ℝ) : ℂ)⁻¹
          * ZMod.stdAddChar ((τ i - σ i) * x i)) := by
    intro x
    have hchi : ∀ i : Fin n, ZMod.stdAddChar (-(σ i * x i)) * ZMod.stdAddChar (τ i * x i)
          = ZMod.stdAddChar ((τ i - σ i) * x i) := by
      intro i
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    have h1 : ∀ i : Fin n, (starRingEnd ℂ) (charState (σ i) (x i)) * charState (τ i) (x i)
        = (Real.sqrt (q : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar (-(σ i * x i))
            * ((Real.sqrt (q : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar (τ i * x i)) := by
      intro i
      rw [charState_apply, charState_apply, map_mul, map_inv₀, Complex.conj_ofReal,
        conj_stdAddChar]
    calc (starRingEnd ℂ) (fourierTensor σ x) * fourierTensor τ x
        = (∏ i : Fin n, (starRingEnd ℂ) (charState (σ i) (x i)))
            * ∏ i : Fin n, charState (τ i) (x i) := by
          show (starRingEnd ℂ) (∏ i : Fin n, charState (σ i) (x i))
              * ∏ i : Fin n, charState (τ i) (x i) = _
          rw [map_prod]
      _ = ∏ i : Fin n, (starRingEnd ℂ) (charState (σ i) (x i)) * charState (τ i) (x i) :=
          Finset.prod_mul_distrib.symm
      _ = ∏ i : Fin n, (Real.sqrt (q : ℝ) : ℂ)⁻¹ * (Real.sqrt (q : ℝ) : ℂ)⁻¹
            * (ZMod.stdAddChar (-(σ i * x i)) * ZMod.stdAddChar (τ i * x i)) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [h1 i]
          ring
      _ = _ := Finset.prod_congr rfl fun i _ => by rw [hchi i]
  have hinner : ∀ i : Fin n, ∑ a : ZMod q, (Real.sqrt (q : ℝ) : ℂ)⁻¹
          * (Real.sqrt (q : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar ((τ i - σ i) * a)
      = if σ i = τ i then 1 else 0 := by
    intro i
    rw [← Finset.mul_sum, sum_stdAddChar_mul]
    by_cases h : τ i - σ i = 0
    · have h' : σ i = τ i := ((sub_eq_zero).mp h).symm
      rw [ite_eq_left h, ite_eq_left h']
      rw [← mul_inv, hsq, inv_mul_cancel₀ hne]
    · have h' : σ i ≠ τ i := fun he => h (sub_eq_zero.mpr he.symm)
      rw [ite_eq_right h, ite_eq_right h', mul_zero]
  rw [inner_apply, Finset.sum_congr rfl fun x _ => hterm x,
    show (∑ x : XReg q n, ∏ i : Fin n, (Real.sqrt (q : ℝ) : ℂ)⁻¹
            * (Real.sqrt (q : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar ((τ i - σ i) * x i))
      = ∏ i : Fin n, ∑ a : ZMod q, (Real.sqrt (q : ℝ) : ℂ)⁻¹
            * (Real.sqrt (q : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar ((τ i - σ i) * a) by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ],
    Finset.prod_congr rfl fun i _ => hinner i]
  by_cases hστ : σ = τ
  · subst hστ
    simp
  · rw [ite_eq_right hστ]
    obtain ⟨j, hj⟩ : ∃ j : Fin n, σ j ≠ τ j :=
      not_forall.mp fun hall => hστ (funext hall)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [ite_eq_right hj])

/-- The uniform initial state is the tensor product of the zero-frequency Fourier state and the
initial algorithm state. -/
theorem uniformInitialState_eq_fourierTensor (ψ_init : QState (AReg q n W)) :
    uniformInitialState (q := q) (n := n) (W := W) ψ_init
      = TensorState (fourierTensor (q := q) (n := n) 0) ψ_init := by
  have hsqrt : ∀ m : ℕ, Real.sqrt (((q ^ m : ℕ) : ℝ)) = (Real.sqrt ((q : ℝ))) ^ m := by
    intro m
    rw [Nat.cast_pow]
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
  have hprod : fourierTensor (q := q) (n := n) 0
      = fun _ => (Real.sqrt (q : ℝ) : ℂ)⁻¹ ^ n := by
    funext x
    have hchi : ∀ i : Fin n, ZMod.stdAddChar ((0 : ZMod q) * x i) = 1 := fun i => by
      rw [zero_mul, AddChar.map_zero_eq_one]
    calc fourierTensor (0 : XReg q n) x
        = ∏ i : Fin n, (Real.sqrt (q : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar ((0 : ZMod q) * x i) := rfl
      _ = ∏ i : Fin n, (Real.sqrt (q : ℝ) : ℂ)⁻¹ ^ 1 := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [hchi i]
          ring
      _ = (Real.sqrt (q : ℝ) : ℂ)⁻¹ ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]
  have hunif : Uniform (XReg q n) = fun _ => (Real.sqrt (q : ℝ) : ℂ)⁻¹ ^ n := by
    funext x
    simp only [Uniform]
    rw [card_xReg, hsqrt n, Complex.ofReal_pow, ← inv_pow]
  rw [uniformInitialState, hunif, hprod]

/-- A normalized algorithm state gives a normalized uniform initial state. -/
theorem normalized_uniformInitialState {ψ_init : QState (AReg q n W)}
    (hψ : Normalized ψ_init) :
    Normalized (uniformInitialState (q := q) (n := n) (W := W) ψ_init) := by
  rw [uniformInitialState]
  exact normalized_tensorState (normalized_uniform card_xReg_pos) hψ

/-- The joint phase oracle is unitary. -/
theorem jointPhaseOracle_unitary :
    jointPhaseOracle (q := q) (n := n) (W := W)
      ∈ Matrix.unitaryGroup (JointReg q n W) ℂ :=
  mem_unitaryGroup_diag (jointPhaseOracle (q := q) (n := n) (W := W))
    (fun p => ZMod.stdAddChar (p.2.1.2 * p.1 p.2.1.1)) (fun _ _ => rfl)
    (fun _ => norm_stdAddChar _)

/-- On a Fourier tensor and algorithm basis ket, a joint phase query adds the queried
single-coordinate frequency and preserves the algorithm ket. -/
theorem jointPhaseOracle_apply_fourierTensor (σ : XReg q n) (i : Fin n) (c : ZMod q) (w : W) :
    jointPhaseOracle (q := q) (n := n) (W := W) *ᵥ
        TensorState (fourierTensor (q := q) (n := n) σ) (Ket ((i, c), w))
      = TensorState (fourierTensor (q := q) (n := n) (σ + Pi.single i c)) (Ket ((i, c), w)) := by
  funext p
  obtain ⟨x, a⟩ := p
  have hdiag : (jointPhaseOracle *ᵥ TensorState (fourierTensor σ) (Ket ((i, c), w))) (x, a)
      = ZMod.stdAddChar (a.1.2 * x a.1.1) * (fourierTensor σ x * Ket ((i, c), w) a) := by
    simp only [Matrix.mulVec, dotProduct, jointPhaseOracle, TensorState]
    rw [Finset.sum_eq_single (x, a)]
    · rw [ite_eq_left rfl]
    · intro p' _ hp'
      rw [ite_eq_right (Ne.symm hp')]
      ring
    · simp
  rw [hdiag, tensorState_apply, fourierTensor_add_single σ i c x, ket_apply]
  by_cases ha : a = ((i, c), w)
  · subst ha
    simp
  · rw [ite_eq_right ha]
    ring

/-- A joint phase query increases the knowledge-support bound by at most one. -/
theorem jointPhaseOracle_mem_knowledge_support {t : ℕ} {ψ : QState (JointReg q n W)}
    (hψ : MemKnowledgeSupport (q := q) (n := n) (W := W) ψ t) :
    MemKnowledgeSupport (jointPhaseOracle (q := q) (n := n) (W := W) *ᵥ ψ) (t + 1) := by
  obtain ⟨w, hw⟩ := hψ
  refine ⟨fun τ => ∑ σ ∈ Finset.univ.filter fun σ => supportCard σ ≤ t,
      ∑ a : AReg q n W,
        if σ + Pi.single a.1.1 a.1.2 = τ then w σ a • Ket a else 0, ?_⟩
  funext p
  set S2 : Finset (XReg q n) := Finset.univ.filter fun σ => supportCard σ ≤ t with hS2def
  set S1 : Finset (XReg q n) := Finset.univ.filter fun τ => supportCard τ ≤ t + 1 with hS1def
  have hmem : ∀ σ ∈ S2, ∀ a : AReg q n W, σ + Pi.single a.1.1 a.1.2 ∈ S1 := by
    intro σ hσ a
    rw [hS2def] at hσ
    rw [hS1def]
    have hσ' : supportCard σ ≤ t := (Finset.mem_filter.mp hσ).2
    have h1 := supportCard_add_single_le σ a.1.1 a.1.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  have hdiag : (jointPhaseOracle *ᵥ ψ) p
      = ZMod.stdAddChar (p.2.1.2 * p.1 p.2.1.1) * ψ p := by
    simp only [Matrix.mulVec, dotProduct, jointPhaseOracle]
    rw [Finset.sum_eq_single p]
    · rw [ite_eq_left rfl]
    · intro p' _ hp'
      rw [ite_eq_right (Ne.symm hp')]
      ring
    · simp
  have hket : ∀ σ : XReg q n, w σ p.2
      = ∑ a : AReg q n W, w σ a * Ket a p.2 := by
    intro σ
    conv_lhs => rw [eq_sum_ket_smul (w σ)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hper : ∀ (σ : XReg q n) (a : AReg q n W),
      ZMod.stdAddChar (p.2.1.2 * p.1 p.2.1.1) * (fourierTensor σ p.1 * (w σ a * Ket a p.2))
        = TensorState (fourierTensor (σ + Pi.single a.1.1 a.1.2)) (w σ a • Ket a) p := by
    intro σ a
    simp only [TensorState, Pi.smul_apply, smul_eq_mul]
    rw [fourierTensor_add_single σ a.1.1 a.1.2 p.1]
    by_cases hpa : p.2 = a
    · subst hpa
      ring
    · rw [ket_ne hpa]
      ring
  have e1 : (jointPhaseOracle *ᵥ ψ) p
      = ZMod.stdAddChar (p.2.1.2 * p.1 p.2.1.1) * ψ p := hdiag
  have e2 : ZMod.stdAddChar (p.2.1.2 * p.1 p.2.1.1) * ψ p
      = ∑ σ ∈ S2, ZMod.stdAddChar (p.2.1.2 * p.1 p.2.1.1) * (fourierTensor σ p.1 * w σ p.2) := by
    rw [hw]
    simp only [TensorState]
    rw [Finset.mul_sum]
  have e3 : ∑ σ ∈ S2, ZMod.stdAddChar (p.2.1.2 * p.1 p.2.1.1) * (fourierTensor σ p.1 * w σ p.2)
      = ∑ σ ∈ S2, ∑ a : AReg q n W,
            TensorState (fourierTensor (σ + Pi.single a.1.1 a.1.2)) (w σ a • Ket a) p := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hket σ, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => hper σ a
  have e4a : ∀ σ ∈ S2, ∀ a : AReg q n W,
      TensorState (fourierTensor (σ + Pi.single a.1.1 a.1.2)) (w σ a • Ket a) p
        = ∑ τ ∈ S1, if σ + Pi.single a.1.1 a.1.2 = τ then
            TensorState (fourierTensor (σ + Pi.single a.1.1 a.1.2)) (w σ a • Ket a) p else 0 := by
    intro σ hσ a
    rw [Finset.sum_ite_eq, ite_eq_left (hmem σ hσ a)]
  have e4 : ∑ σ ∈ S2, ∑ a : AReg q n W,
            TensorState (fourierTensor (σ + Pi.single a.1.1 a.1.2)) (w σ a • Ket a) p
      = ∑ τ ∈ S1, ∑ σ ∈ S2, ∑ a : AReg q n W,
            if σ + Pi.single a.1.1 a.1.2 = τ then
              TensorState (fourierTensor (σ + Pi.single a.1.1 a.1.2)) (w σ a • Ket a) p else 0 := by
    rw [Finset.sum_comm (s := S1) (t := S2)]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.sum_comm (s := S1)]
    exact Finset.sum_congr rfl fun a _ => e4a σ hσ a
  have e5 : (∑ τ ∈ S1, ∑ σ ∈ S2, ∑ a : AReg q n W,
            if σ + Pi.single a.1.1 a.1.2 = τ then
              TensorState (fourierTensor (σ + Pi.single a.1.1 a.1.2)) (w σ a • Ket a) p else 0)
      = ∑ τ ∈ S1, ∑ σ ∈ S2, ∑ a : AReg q n W,
            if σ + Pi.single a.1.1 a.1.2 = τ then
              TensorState (fourierTensor τ) (w σ a • Ket a) p else 0 := by
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : σ + Pi.single a.1.1 a.1.2 = τ
    · rw [ite_eq_left h, ite_eq_left h, h]
    · rw [ite_eq_right h, ite_eq_right h]
  have e6 : (∑ τ ∈ S1, ∑ σ ∈ S2, ∑ a : AReg q n W,
            if σ + Pi.single a.1.1 a.1.2 = τ then
              TensorState (fourierTensor τ) (w σ a • Ket a) p else 0)
      = ∑ τ ∈ S1, TensorState (fourierTensor τ)
            (∑ σ ∈ S2, ∑ a : AReg q n W,
              if σ + Pi.single a.1.1 a.1.2 = τ then w σ a • Ket a else 0) p := by
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [tensorState_sum_apply]
    exact Finset.sum_congr rfl fun σ _ => (tensorState_sum_ite_apply _ _ _ _ _).symm
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))

/-- Applying a joint algorithm gate preserves the knowledge-support bound. -/
theorem jointGate_mem_knowledge_support (U : Matrix (AReg q n W) (AReg q n W) ℂ)
    {t : ℕ} {ψ : QState (JointReg q n W)}
    (hψ : MemKnowledgeSupport (q := q) (n := n) (W := W) ψ t) :
    MemKnowledgeSupport (jointGate (q := q) (n := n) (W := W) U *ᵥ ψ) t := by
  classical
  obtain ⟨w, hw⟩ := hψ
  refine ⟨fun σ => U *ᵥ w σ, ?_⟩
  funext p
  have hdistr : ∀ σ : XReg q n,
      ∑ p' : JointReg q n W, jointGate U p p' * TensorState (fourierTensor σ) (w σ) p'
        = TensorState (fourierTensor σ) (U *ᵥ w σ) p := by
    intro σ
    rw [← jointGate_mulVec_tensorState U (fourierTensor σ) (w σ)]
    rfl
  calc (jointGate U *ᵥ ψ) p
      = ∑ p' : JointReg q n W,
          jointGate U p p' * ∑ σ ∈ Finset.univ.filter fun σ => supportCard σ ≤ t,
            TensorState (fourierTensor σ) (w σ) p' := by
        conv_lhs => rw [hw]
        rfl
    _ = ∑ p' : JointReg q n W,
          ∑ σ ∈ Finset.univ.filter fun σ => supportCard σ ≤ t,
            jointGate U p p' * TensorState (fourierTensor σ) (w σ) p' :=
        Finset.sum_congr rfl fun p' _ => Finset.mul_sum _ _ _
    _ = ∑ σ ∈ Finset.univ.filter fun σ => supportCard σ ≤ t,
          ∑ p' : JointReg q n W,
            jointGate U p p' * TensorState (fourierTensor σ) (w σ) p' :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun σ _ => hdistr σ

/-- Joint lifting preserves circuit query count. -/
theorem queryCount_jointLift (C : Circuit (AReg q n W)) :
    QueryCount (jointLift (q := q) (n := n) (W := W) C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
      cases s with
      | gate U => simp only [jointLift_gate, queryCount_gate, ih]
      | query => simp only [jointLift_query, queryCount_query, ih]

/-- Running a jointly lifted circuit increases the knowledge-support bound by at most its query
count. -/
theorem run_jointLift_mem_knowledge_support (C : Circuit (AReg q n W))
    {t : ℕ} {ψ : QState (JointReg q n W)}
    (hψ : MemKnowledgeSupport (q := q) (n := n) (W := W) ψ t) :
    MemKnowledgeSupport
      (Run jointPhaseOracle (jointLift (q := q) (n := n) (W := W) C) ψ)
      (t + QueryCount C) := by
  induction C generalizing ψ t with
  | nil => simpa using hψ
  | cons s C ih =>
      cases s with
      | gate U =>
          simp only [jointLift_gate, run_gate, queryCount_gate]
          exact ih (jointGate_mem_knowledge_support U hψ)
      | query =>
          simp only [jointLift_query, run_query, queryCount_query]
          have hidx : t + (QueryCount C + 1) = (t + 1) + QueryCount C := by omega
          rw [hidx]
          exact ih (jointPhaseOracle_mem_knowledge_support hψ)

/-- A joint algorithm gate is unitary exactly when the original algorithm gate is unitary. -/
theorem jointGate_mem_unitaryGroup_iff (U : Matrix (AReg q n W) (AReg q n W) ℂ) :
    jointGate (q := q) (n := n) (W := W) U ∈ Matrix.unitaryGroup (JointReg q n W) ℂ
      ↔ U ∈ Matrix.unitaryGroup (AReg q n W) ℂ := by
  have hJG : jointGate (q := q) (n := n) (W := W) U
      = TensorGate (1 : Matrix (XReg q n) (XReg q n) ℂ) U := by
    ext p p'
    obtain ⟨x, a⟩ := p
    obtain ⟨x', a'⟩ := p'
    by_cases h : x = x' <;> simp [jointGate, tensorGate_apply, h]
  have hTG : (jointGate U)ᴴ * jointGate U
      = TensorGate (1 : Matrix (XReg q n) (XReg q n) ℂ) (Uᴴ * U) := by
    rw [hJG, tensorGate_conjTranspose, tensorGate_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  simp only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  constructor
  · intro hG
    rw [hTG] at hG
    have x₀ : XReg q n := 0
    ext a b
    have hE : (Uᴴ * U) a b
        = (TensorGate (1 : Matrix (XReg q n) (XReg q n) ℂ) (Uᴴ * U)) (x₀, a) (x₀, b) := by
      simp [tensorGate_apply]
    rw [hE, congrFun (congrFun hG (x₀, a)) (x₀, b)]
    simp [Matrix.one_apply, Prod.mk.injEq]
  · intro hU
    rw [hTG, hU, tensorGate_one]

/-- A jointly lifted circuit is unitary exactly when the original circuit is unitary. -/
theorem isUnitaryCircuit_jointLift (C : Circuit (AReg q n W)) :
    IsUnitaryCircuit (jointLift (q := q) (n := n) (W := W) C) ↔ IsUnitaryCircuit C := by
  constructor
  · intro h U hU
    have hmem : Step.gate (jointGate U) ∈ jointLift C := List.mem_map_of_mem hU
    exact (jointGate_mem_unitaryGroup_iff U).mp (h _ hmem)
  · intro h V hV
    simp only [jointLift, List.mem_map] at hV
    obtain ⟨s, hs, hfsv⟩ := hV
    cases s with
    | gate U =>
        simp only [Step.gate.injEq] at hfsv
        rw [← hfsv]
        exact (jointGate_mem_unitaryGroup_iff U).mpr (h U hs)
    | query => simp at hfsv

/-- Running a jointly lifted unitary circuit from a normalized uniform initial state preserves
normalization. -/
theorem run_jointLift_normalized (C : Circuit (AReg q n W)) (hC : IsUnitaryCircuit C)
    {ψ_init : QState (AReg q n W)} (hψ : Normalized ψ_init) :
    Normalized (Run jointPhaseOracle (jointLift (q := q) (n := n) (W := W) C)
      (uniformInitialState (q := q) (n := n) (W := W) ψ_init)) :=
  IsUnitaryCircuit.normalized_run ((isUnitaryCircuit_jointLift C).mpr hC) jointPhaseOracle_unitary
    (normalized_uniformInitialState hψ)

/-- The uniform initial state has knowledge support bounded by zero. -/
theorem uniformInitialState_mem_knowledge_support_zero (ψ_init : QState (AReg q n W)) :
    MemKnowledgeSupport (uniformInitialState (q := q) (n := n) (W := W) ψ_init) 0 := by
  refine ⟨fun τ => if τ = 0 then ψ_init else 0, ?_⟩
  have hfilter : (Finset.univ.filter fun σ : XReg q n => supportCard σ ≤ 0) = {0} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      by_contra hσ
      have hex : ∃ i : Fin n, σ i ≠ 0 :=
        not_forall.mp fun hall => hσ (funext hall)
      obtain ⟨i, hi⟩ := hex
      have hcardpos : 0 < supportCard σ := by
        unfold supportCard
        have hmemi : i ∈ Finset.univ.filter fun j => σ j ≠ 0 :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
        have := Finset.card_ne_zero_of_mem hmemi
        omega
      omega
    · intro h
      subst h
      simp [supportCard]
  funext p
  rw [hfilter, Finset.sum_singleton, uniformInitialState_eq_fourierTensor]
  simp

/-- Running a jointly lifted circuit from the uniform initial state gives knowledge support
bounded by the query count. -/
theorem prop3_2_uniform_states_knowledge_support (C : Circuit (AReg q n W))
    (ψ_init : QState (AReg q n W)) :
    MemKnowledgeSupport
      (Run jointPhaseOracle (jointLift (q := q) (n := n) (W := W) C)
        (uniformInitialState (q := q) (n := n) (W := W) ψ_init))
      (QueryCount C) := by
  have h := run_jointLift_mem_knowledge_support C
    (uniformInitialState_mem_knowledge_support_zero ψ_init)
  rwa [Nat.zero_add] at h

end Qatlib.Concepts.QueryComplexity.FourierModel.FourierDefs
