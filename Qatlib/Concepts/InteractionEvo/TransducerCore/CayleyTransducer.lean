/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.InteractionEvo.TransducerCore.CayleyApproxOrderedPropagatorStat
public import Qatlib.Concepts.LchsSimulation.TimeOrdered.OrderedFrozenSegment
public import Qatlib.Concepts.InteractionEvo.SegmentProduct.SegmentProductPerturbation

@[expose] public section
open Qatlib.Concepts.InteractionEvo.CayleyTransform Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

set_option autoImplicit false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.InteractionEvo.SegmentProduct
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.TransducerCore
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {ιS ιA : Type} [Fintype ιS] [DecidableEq ιS] [Fintype ιA] [DecidableEq ιA]

noncomputable def cayleyMidpointMap (H : ℝ → Matrix ιS ιS ℂ) (α T : ℝ) {J : ℕ}
    (j : Fin J) : Matrix ιS ιS ℂ :=
  (cayleyShift (((α⁻¹ : ℝ) : ℂ) • H (((j : ℕ) : ℝ) * T / J)) (α * T / J))⁻¹ *
    cayleyPartialProduct H α T J j

noncomputable def localCatalystVec (a0 : ιA) (O : Matrix (ιA × ιS) (ιA × ιS) ℂ) (w : ℝ)
    (y : ιS → ℂ) : (ιA × ιS) → ℂ :=
  (Real.sqrt (w / 2) : ℂ) • ((1 + Complex.I • O) *ᵥ (encodingFiber a0 *ᵥ y))

noncomputable def localCatalystMap {H : ℝ → Matrix ιS ιS ℂ} {T α : ℝ} {J : ℕ}
    (a0 : ιA) (oracle : HamTOracle a0 H T α J) (j : Fin J) : Matrix (ιA × ιS) ιS ℂ :=
  (Real.sqrt (α * T / J / 2) : ℂ) •
    ((1 + Complex.I • oracle.O j) *
      ((encodingFiber a0 * cayleyMidpointMap H α T j : Matrix (ιA × ιS) ιS ℂ)))

noncomputable def catalystMap {H : ℝ → Matrix ιS ιS ℂ} {T α : ℝ} {J : ℕ}
    (a0 : ιA) (oracle : HamTOracle a0 H T α J) :
    Matrix ((ιA × ιS) × Fin J) ιS ℂ :=
  Matrix.of fun (as, j) s => localCatalystMap a0 oracle j as s

noncomputable def cayleyReflC (w : ℝ) : ℝ := (1 - w / 2) / (1 + w / 2)

noncomputable def cayleyReflS (w : ℝ) : ℝ := Real.sqrt (2 * w) / (1 + w / 2)

noncomputable def ancillaProjector (a0 : ιA) : Matrix (ιA × ιS) (ιA × ιS) ℂ :=
  rangeProjector (encodingFiber a0)

noncomputable def cayleyReflection (a0 : ιA) (w : ℝ) :
    Matrix (ιS ⊕ (ιA × ιS)) (ιS ⊕ (ιA × ιS)) ℂ :=
  Matrix.fromBlocks
    ((cayleyReflC w : ℂ) • 1)
    (-(Complex.I * (cayleyReflS w : ℂ)) • (encodingFiber a0)ᴴ)
    ((cayleyReflS w : ℂ) • encodingFiber a0)
    (Complex.I • (1 - ((1 - cayleyReflC w : ℝ) : ℂ) • ancillaProjector a0))

def sliceEmbed {J : ℕ} (j : Fin J) :
    Matrix (ιS ⊕ ((ιA × ιS) × Fin J)) (ιS ⊕ (ιA × ιS)) ℂ :=
  Matrix.of fun tgt src =>
    match tgt, src with
    | Sum.inl s, Sum.inl s' => if s = s' then 1 else 0
    | Sum.inr (as, j'), Sum.inr as' => if j' = j ∧ as = as' then 1 else 0
    | _, _ => 0

noncomputable def cayleyReflectionAt (a0 : ιA) (w : ℝ) {J : ℕ} (j : Fin J) :
    Matrix (ιS ⊕ ((ιA × ιS) × Fin J)) (ιS ⊕ ((ιA × ιS) × Fin J)) ℂ :=
  1 + ((sliceEmbed j * (cayleyReflection a0 w - 1) :
      Matrix (ιS ⊕ ((ιA × ιS) × Fin J)) (ιS ⊕ (ιA × ιS)) ℂ) * (sliceEmbed j)ᴴ)

noncomputable def transducerCircuit (a0 : ιA) (w : ℝ) (J : ℕ) :
    Matrix (ιS ⊕ ((ιA × ιS) × Fin J)) (ιS ⊕ ((ιA × ιS) × Fin J)) ℂ :=
  ((List.finRange J).map (cayleyReflectionAt a0 w)).reverse.prod

noncomputable def cayleyTransducer (a0 : ιA) (w : ℝ) {J : ℕ}
    (O : Fin J → Matrix (ιA × ιS) (ιA × ιS) ℂ) :
    Matrix (ιS ⊕ ((ιA × ιS) × Fin J)) (ιS ⊕ ((ιA × ιS) × Fin J)) ℂ :=
  transducerCircuit a0 w J * oracleDirectSum O

/-- For positive `w`, the squared Cayley reflection coefficients sum to one. -/
theorem cayleyRefl_coefficients {w : ℝ} (hw : 0 < w) :
    cayleyReflC w ^ 2 + cayleyReflS w ^ 2 = 1 := by
  have hd : 1 + w / 2 ≠ 0 := ne_of_gt (by linarith)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * w)
  unfold cayleyReflC cayleyReflS
  rw [div_pow, div_pow, hs]
  field_simp
  ring

/-- For positive `w`, the Cayley reflection coefficients satisfy the three catalyst matching
identities. -/
theorem cayleyRefl_catalyst_coefficients {w : ℝ} (hw : 0 < w) :
    cayleyReflS w * Real.sqrt (w / 2) = 1 - cayleyReflC w ∧
    cayleyReflS w = (1 + cayleyReflC w) * Real.sqrt (w / 2) ∧
    cayleyReflS w * (w / 2) = (1 - cayleyReflC w) * Real.sqrt (w / 2) := by
  have hd : 1 + w / 2 ≠ 0 := ne_of_gt (by linarith)
  have hr : Real.sqrt (2 * w) = 2 * Real.sqrt (w / 2) := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [show 2 * w = 4 * (w / 2) by ring, Real.sqrt_mul (by norm_num)]
    norm_num [h4]
  have hs := Real.sq_sqrt (by positivity : 0 ≤ w / 2)
  unfold cayleyReflC cayleyReflS
  rw [hr]
  constructor
  · field_simp; nlinarith
  constructor
  · field_simp; ring
  · field_simp; nlinarith

/-- The Cayley reflection is unitary for positive `w`. -/
theorem cayleyReflection_unitary (a0 : ιA) {w : ℝ} (hw : 0 < w) :
    cayleyReflection a0 w ∈ Matrix.unitaryGroup (ιS ⊕ (ιA × ιS)) ℂ := by
  let V : Matrix (ιA × ιS) ιS ℂ := encodingFiber a0
  let P := ancillaProjector (ιS := ιS) a0
  have hv : Vᴴ * V = 1 := encodingFiber_isIsometry a0
  have hp : P * P = P := (rangeProjector_isOrthogonalProjector hv).1
  have hph : Pᴴ = P := (rangeProjector_isOrthogonalProjector hv).2
  have hpv : P * V = V := rangeProjector_mul hv
  have hvp : Vᴴ * P = Vᴴ := by
    have h := congrArg Matrix.conjTranspose hpv
    simpa only [Matrix.conjTranspose_mul, hph, Matrix.conjTranspose_conjTranspose] using! h
  have hc : (cayleyReflC w : ℂ)^2 + (cayleyReflS w : ℂ)^2 = 1 := by
    exact_mod_cast cayleyRefl_coefficients hw
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold cayleyReflection
  change (Matrix.fromBlocks ((cayleyReflC w : ℂ) • 1)
    (-(Complex.I * (cayleyReflS w : ℂ)) • Vᴴ)
    ((cayleyReflS w : ℂ) • V)
    (Complex.I • (1 - ((1 - cayleyReflC w : ℝ) : ℂ) • P)))ᴴ *
    (Matrix.fromBlocks ((cayleyReflC w : ℂ) • 1)
    (-(Complex.I * (cayleyReflS w : ℂ)) • Vᴴ)
    ((cayleyReflS w : ℂ) • V)
    (Complex.I • (1 - ((1 - cayleyReflC w : ℝ) : ℂ) • P))) = 1
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  apply Matrix.fromBlocks_inj.mpr
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_conjTranspose, hph, RCLike.star_def, map_neg, map_mul, map_sub, map_one,
    Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub, Complex.ofReal_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, hv, hpv, hvp, hp, smul_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← add_smul, ← pow_two, ← pow_two, hc, one_smul]
  · module
  · module
  · change _ = _ at hp
    have hvv : V * Vᴴ = P := rfl
    rw [hvv]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring_nf
    simp only [Complex.I_sq]
    linear_combination hc * P i j

def sliceIndex {J : ℕ} (j : Fin J) :
    (ιS ⊕ (ιA × ιS)) → (ιS ⊕ ((ιA × ιS) × Fin J)) :=
  Sum.map id (fun a => (a, j))

omit [Fintype ιS] [Fintype ιA] [DecidableEq ιS] [DecidableEq ιA] in

/-- The index map embedding a fixed time slice is injective. -/
theorem sliceIndex_injective {J : ℕ} (j : Fin J) :
    Function.Injective (sliceIndex (ιS := ιS) (ιA := ιA) j) := by
  intro x y h
  cases x <;> cases y <;> simp_all [sliceIndex]

omit [Fintype ιS] [Fintype ιA] in

/-- The slice embedding matrix has entry one exactly at the corresponding slice index, and zero
elsewhere. -/
theorem sliceEmbed_entry {J : ℕ} (j : Fin J)
    (t : ιS ⊕ ((ιA × ιS) × Fin J)) (s : ιS ⊕ (ιA × ιS)) :
    sliceEmbed j t s = if t = sliceIndex j s then 1 else 0 := by
  cases t with
  | inl t => cases s <;> simp [sliceEmbed, sliceIndex]
  | inr t =>
    rcases t with ⟨a, k⟩
    cases s <;> simp [sliceEmbed, sliceIndex, Prod.ext_iff, and_comm]

/-- The slice embedding is an isometry. -/
theorem sliceEmbed_isIsometry {J : ℕ} (j : Fin J) :
    IsIsometry (sliceEmbed (ιS := ιS) (ιA := ιA) j) := by
  unfold IsIsometry
  ext s r
  rw [Matrix.mul_apply]
  have hs (x : ιS ⊕ ((ιA × ιS) × Fin J)) :
      star (sliceEmbed j x s) = if x = sliceIndex j s then 1 else 0 := by
    rw [sliceEmbed_entry]
    split <;> simp
  simp only [Matrix.conjTranspose_apply, hs]
  simp only [sliceEmbed_entry]
  rw [sum_fiber_mul_left]
  simp only [(sliceIndex_injective j).eq_iff, Matrix.one_apply]

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid in

/-- Extending a unitary matrix through an isometry by acting as the identity on the
complementary subspace gives a unitary matrix. -/
theorem cayley_unitary_extension {B C : Type} [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (E : Matrix B C ℂ) (R : Matrix C C ℂ)
    (hE : Eᴴ * E = 1) (hR : Rᴴ * R = 1) :
    (1 + (E * (R - 1) : Matrix B C ℂ) * Eᴴ) ∈ Matrix.unitaryGroup B ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
  have he (X : Matrix C B ℂ) : Eᴴ * (E * X : Matrix B B ℂ) = X := by
    rw [← Matrix.mul_assoc, hE, Matrix.one_mul]
  calc
    _ = 1 + (E * ((Rᴴ - 1) + (R - 1) + (Rᴴ - 1) * (R - 1)) : Matrix B C ℂ) * Eᴴ := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_assoc, he]
      abel
    _ = 1 := by
      have hh : (Rᴴ - 1) + (R - 1) + (Rᴴ - 1) * (R - 1) = 0 := by
        noncomm_ring [hR]
      rw [hh, Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- The Cayley reflection localized to a time slice is unitary for positive `w`. -/
theorem cayleyReflectionAt_unitary (a0 : ιA) {w : ℝ} (hw : 0 < w) {J : ℕ} (j : Fin J) :
    cayleyReflectionAt a0 w j ∈
      Matrix.unitaryGroup (ιS ⊕ ((ιA × ιS) × Fin J)) ℂ := by
  apply cayley_unitary_extension _ _ (sliceEmbed_isIsometry j)
  simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    using! cayleyReflection_unitary (ιS := ιS) a0 hw

/-- The transducer circuit is unitary for positive `w`. -/
theorem transducerCircuit_unitary (a0 : ιA) {w : ℝ} (hw : 0 < w) (J : ℕ) :
    transducerCircuit a0 w J ∈
      Matrix.unitaryGroup (ιS ⊕ ((ιA × ιS) × Fin J)) ℂ := by
  unfold transducerCircuit
  apply Submonoid.list_prod_mem
  intro R hR
  rw [List.mem_reverse, List.mem_map] at hR
  rcases hR with ⟨j, _, rfl⟩
  exact cayleyReflectionAt_unitary a0 hw j

/-- The direct sum oracle is unitary when every slice oracle is unitary. -/
theorem oracleDirectSum_unitary {J : ℕ} (O : Fin J → Matrix (ιA × ιS) (ιA × ιS) ℂ)
    (hO : ∀ j, O j ∈ Matrix.unitaryGroup (ιA × ιS) ℂ) :
    oracleDirectSum (ιS := ιS) O ∈
      Matrix.unitaryGroup (ιS ⊕ ((ιA × ιS) × Fin J)) ℂ := by
  have h : ∀ j, (O j)ᴴ * O j = 1 := by
    intro j
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using! hO j
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  simp only [oracleDirectSum, hamTMatrix, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.blockDiagonal_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
    zero_add, add_zero, ← Matrix.blockDiagonal_mul]
  simp only [h]
  rw [show (fun _ : Fin J => (1 : Matrix (ιA × ιS) (ιA × ιS) ℂ)) = 1 from rfl,
    Matrix.blockDiagonal_one, Matrix.fromBlocks_one]

/-- For positive `w`, the public Cayley reflection coefficient satisfies its required linear
identity. -/
theorem cayleyRefl_public_coefficient {w : ℝ} (hw : 0 < w) :
    cayleyReflC w * (w / 2) - (1 - cayleyReflC w) = -w / 2 := by
  have hd : 1 + w / 2 ≠ 0 := ne_of_gt (by linarith)
  unfold cayleyReflC
  field_simp
  ring

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in

/-- For a Hermitian unitary oracle with the specified compressed block, the Cayley reflection
transforms the midpoint public state and restores the local catalyst. -/
theorem cayleyReflection_midpoint_identity (a0 : ιA)
    (O : Matrix (ιA × ιS) (ιA × ιS) ℂ) (hOherm : O.IsHermitian)
    (hOunit : O ∈ Matrix.unitaryGroup (ιA × ιS) ℂ)
    (M : Matrix ιS ιS ℂ)
    (hblock : compress (encodingFiber a0) O (encodingFiber a0) = M)
    {w : ℝ} (hw : 0 < w) (y : ιS → ℂ) :
    cayleyReflection a0 w *ᵥ
        Sum.elim (cayleyShift M w *ᵥ y) (O *ᵥ localCatalystVec a0 O w y) =
      Sum.elim ((2 • (1 : Matrix ιS ιS ℂ) - cayleyShift M w) *ᵥ y)
        (localCatalystVec a0 O w y) := by
  let V : Matrix (ιA × ιS) ιS ℂ := encodingFiber a0
  let P := ancillaProjector (ιS := ιS) a0
  let r : ℂ := Real.sqrt (w / 2)
  let c : ℂ := cayleyReflC w
  let s : ℂ := cayleyReflS w
  let a : ℂ := (w / 2 : ℝ)
  have hOO : O * O = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hOherm.eq]
      using! hOunit
  have hv : Vᴴ * V = 1 := encodingFiber_isIsometry a0
  have hb : Vᴴ * O * V = M := hblock
  have hvy : Vᴴ *ᵥ (V *ᵥ y) = y := by rw [Matrix.mulVec_mulVec, hv, Matrix.one_mulVec]
  have hoy : O *ᵥ (O *ᵥ (V *ᵥ y)) = V *ᵥ y := by
    rw [Matrix.mulVec_mulVec, hOO, Matrix.one_mulVec]
  have hmy : Vᴴ *ᵥ (O *ᵥ (V *ᵥ y)) = M *ᵥ y := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hb]
  have hpv : P *ᵥ (V *ᵥ y) = V *ᵥ y := by
    change (V * Vᴴ : Matrix (ιA × ιS) (ιA × ιS) ℂ) *ᵥ (V *ᵥ y) = _
    rw [← Matrix.mulVec_mulVec, hvy]
  have hpo : P *ᵥ (O *ᵥ (V *ᵥ y)) = V *ᵥ (M *ᵥ y) := by
    change (V * Vᴴ : Matrix (ιA × ιS) (ιA × ιS) ℂ) *ᵥ (O *ᵥ (V *ᵥ y)) = _
    rw [← Matrix.mulVec_mulVec, hmy]
  have hx : localCatalystVec a0 O w y = r • (V *ᵥ y + Complex.I • (O *ᵥ (V *ᵥ y))) := by
    simp only [localCatalystVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, r, V]
  have hOx : O *ᵥ localCatalystVec a0 O w y =
      r • (O *ᵥ (V *ᵥ y) + Complex.I • (V *ᵥ y)) := by
    rw [hx, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hoy]
  have hsr : s * r = 1 - c := by
    dsimp only [s, r, c]
    exact_mod_cast (cayleyRefl_catalyst_coefficients hw).1
  have hs : s = (1 + c) * r := by
    dsimp only [s, r, c]
    exact_mod_cast (cayleyRefl_catalyst_coefficients hw).2.1
  have hsa : s * a = (1 - c) * r := by
    dsimp only [s, a, c, r]
    exact_mod_cast (cayleyRefl_catalyst_coefficients hw).2.2
  have hca : c * a - (1 - c) = -a := by
    dsimp only [c, a]
    exact_mod_cast (show cayleyReflC w * (w / 2) - (1 - cayleyReflC w) = -(w / 2) by
      simpa only [neg_div] using! cayleyRefl_public_coefficient hw)
  simp only [cayleyReflection, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr, Complex.ofReal_sub, Complex.ofReal_one]
  change Sum.elim
    ((c • (1 : Matrix ιS ιS ℂ)) *ᵥ (cayleyShift M w *ᵥ y) +
      (-(Complex.I * s) • Vᴴ) *ᵥ (O *ᵥ localCatalystVec a0 O w y))
    ((s • V) *ᵥ (cayleyShift M w *ᵥ y) +
      (Complex.I • (1 - (1 - c) • P)) *ᵥ (O *ᵥ localCatalystVec a0 O w y)) = _
  apply congrArg₂ Sum.elim
  · simp only [cayleyShift, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      hOx, Matrix.mulVec_smul, Matrix.mulVec_add, hmy, hvy,
      Matrix.sub_mulVec, two_smul, Matrix.add_mulVec]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [a] at hca
    push_cast at hca ⊢
    ring_nf
    simp only [Complex.I_sq]
    linear_combination hsr * y i + Complex.I * (hca - hsr) * (M *ᵥ y) i
  · simp only [cayleyShift, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      hx, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.sub_mulVec, hpv, hpo, hoy]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [a] at hsa
    push_cast at hsa ⊢
    ring_nf
    simp only [Complex.I_sq]
    linear_combination hs * (V *ᵥ y) i + Complex.I * hsa * (V *ᵥ (M *ᵥ y)) i

/-- For the specified Hermitian block encoding, the Cayley reflection implements a local Cayley
step while restoring its catalyst. -/
theorem cayleyReflection_local_identity (a0 : ιA)
    (O : Matrix (ιA × ιS) (ιA × ιS) ℂ) (hOherm : O.IsHermitian)
    (hOunit : O ∈ Matrix.unitaryGroup (ιA × ιS) ℂ)
    (M : Matrix ιS ιS ℂ) (hM : M.IsHermitian)
    (hblock : compress (encodingFiber a0) O (encodingFiber a0) = M)
    {w : ℝ} (hw : 0 < w) (ψ : ιS → ℂ) :
    cayleyReflection a0 w *ᵥ
        Sum.elim ψ (O *ᵥ localCatalystVec a0 O w ((cayleyShift M w)⁻¹ *ᵥ ψ)) =
      Sum.elim (cayleyStep M w *ᵥ ψ)
        (localCatalystVec a0 O w ((cayleyShift M w)⁻¹ *ᵥ ψ)) := by
  have h := cayleyReflection_midpoint_identity a0 O hOherm hOunit M hblock hw
    ((cayleyShift M w)⁻¹ *ᵥ ψ)
  have hinv := Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (cayleyShift_isUnit M hM w))
  simpa only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, cayleyStep] using! h

/-- Every grid point with index at most `J` lies in the interval from zero to positive `T` when
`J` is positive. -/
theorem cayley_grid_mem {T : ℝ} {J k : ℕ} (hT : 0 < T) (hJ : 0 < J) (hk : k ≤ J) :
    (k : ℝ) * T / J ∈ Set.Icc 0 T := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  constructor
  · positivity
  · apply (div_le_iff₀ hJR).2
    simpa only [mul_comm] using!
      mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ J by exact_mod_cast hk) hT.le

omit [Fintype ιS] [DecidableEq ιS] in

/-- Real rescaling preserves Hermiticity of Hamiltonian samples at valid grid points. -/
theorem cayley_grid_hermitian (H : ℝ → Matrix ιS ιS ℂ) {T α : ℝ} {J k : ℕ}
    (hT : 0 < T) (hJ : 0 < J) (hk : k ≤ J)
    (hH : ∀ t ∈ Set.Icc 0 T, (H t).IsHermitian) :
    ((((α⁻¹ : ℝ) : ℂ) • H ((k : ℝ) * T / J))).IsHermitian := by
  change _ᴴ = _
  rw [Matrix.conjTranspose_smul, (hH _ (cayley_grid_mem hT hJ hk)).eq]
  simp only [RCLike.star_def, Complex.conj_ofReal]

/-- Every valid partial Cayley product is unitary when the Hamiltonian is Hermitian throughout
the time interval. -/
theorem cayleyPartialProduct_unitary (H : ℝ → Matrix ιS ιS ℂ) {T α : ℝ} {J k : ℕ}
    (hT : 0 < T) (hJ : 0 < J) (hk : k ≤ J)
    (hH : ∀ t ∈ Set.Icc 0 T, (H t).IsHermitian) :
    cayleyPartialProduct H α T J k ∈ Matrix.unitaryGroup ιS ℂ := by
  unfold cayleyPartialProduct
  apply Submonoid.list_prod_mem
  intro U hU
  rw [List.mem_reverse, List.mem_map] at hU
  rcases hU with ⟨j, hj, rfl⟩
  apply cayleyStep_unitary
  exact cayley_grid_hermitian H hT hJ ((List.mem_range.mp hj).le.trans hk) hH

/-- The Cayley midpoint map has norm at most one under the Hermiticity and positive grid
assumptions. -/
theorem cayleyMidpointMap_norm_le (H : ℝ → Matrix ιS ιS ℂ) {T α : ℝ} {J : ℕ}
    (hT : 0 < T) (hJ : 0 < J) (j : Fin J)
    (hH : ∀ t ∈ Set.Icc 0 T, (H t).IsHermitian) :
    ‖cayleyMidpointMap H α T j‖ ≤ 1 := by
  have hi := cayleyShift_inv_norm_le _
    (cayley_grid_hermitian H (α := α) hT hJ j.isLt.le hH) (α * T / J)
  have hp := l2_norm_unitary_le_one (cayleyPartialProduct_unitary H (α := α) hT hJ j.isLt.le hH)
  exact (norm_mul_le _ _).trans (by simpa using! mul_le_mul hi hp (norm_nonneg _) zero_le_one)

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid in

/-- The local catalyst Gram matrix is the midpoint Gram matrix scaled by `α * T / J` when that
scale is nonnegative. -/
theorem localCatalystMap_gram {H : ℝ → Matrix ιS ιS ℂ} {T α : ℝ} {J : ℕ}
    (a0 : ιA) (oracle : HamTOracle a0 H T α J) (j : Fin J)
    (hw : 0 ≤ α * T / J) :
    (localCatalystMap a0 oracle j)ᴴ * localCatalystMap a0 oracle j =
      ((α * T / J : ℝ) : ℂ) •
        ((cayleyMidpointMap H α T j)ᴴ * cayleyMidpointMap H α T j) := by
  let O := oracle.O j
  let V : Matrix (ιA × ιS) ιS ℂ := encodingFiber a0
  let Y := cayleyMidpointMap H α T j
  let K := 1 + Complex.I • O
  have hoh : Oᴴ = O := (oracle.hermitian j).eq
  have hoo : O * O = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      (oracle.hermitian j).eq] using! oracle.unitary j
  have hk : Kᴴ * K = 2 • (1 : Matrix (ιA × ιS) (ιA × ιS) ℂ) := by
    simp only [K, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, hoh, RCLike.star_def, Complex.conj_I,
      Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hoo]
    ext i k
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, two_smul]
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hv : Vᴴ * V = 1 := encodingFiber_isIsometry a0
  have hr : (Real.sqrt (α * T / J / 2) : ℂ)^2 = ((α * T / J / 2 : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (div_nonneg hw (by norm_num : (0 : ℝ) ≤ 2))
  change ((Real.sqrt (α * T / J / 2) : ℂ) • (K * (V * Y : Matrix (ιA × ιS) ιS ℂ)))ᴴ *
    ((Real.sqrt (α * T / J / 2) : ℂ) • (K * (V * Y : Matrix (ιA × ιS) ιS ℂ))) = _
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, RCLike.star_def,
    Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two]
  have he : (Yᴴ * Vᴴ * Kᴴ) *
      (K * (V * Y : Matrix (ιA × ιS) ιS ℂ)) = 2 • (Yᴴ * Y) := by
    calc
      _ = Yᴴ * (Vᴴ * (Kᴴ * K) * V : Matrix ιS ιS ℂ) * Y := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hk, two_smul]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hv]
        exact (two_smul ℕ (Yᴴ * Y)).symm
  rw [he, hr, two_smul, smul_add, ← add_smul]
  congr 1
  push_cast
  ring

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid in

/-- The global catalyst Gram matrix is the sum of the local catalyst Gram matrices. -/
theorem catalystMap_gram {H : ℝ → Matrix ιS ιS ℂ} {T α : ℝ} {J : ℕ}
    (a0 : ιA) (oracle : HamTOracle a0 H T α J) :
    (catalystMap a0 oracle)ᴴ * catalystMap a0 oracle =
      ∑ j : Fin J, (localCatalystMap a0 oracle j)ᴴ * localCatalystMap a0 oracle j := by
  ext s t
  simp only [catalystMap, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.sum_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- The squared catalyst map norm is at most `α * T` under the positive parameter and
Hermiticity assumptions. -/
theorem catalystMap_norm_sq_le {H : ℝ → Matrix ιS ιS ℂ} {T α : ℝ} {J : ℕ}
    (a0 : ιA) (oracle : HamTOracle a0 H T α J)
    (hα : 0 < α) (hT : 0 < T) (hJ : 0 < J)
    (hH : ∀ t ∈ Set.Icc 0 T, (H t).IsHermitian) :
    ‖catalystMap a0 oracle‖ ^ 2 ≤ α * T := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hw : 0 ≤ α * T / J := by positivity
  have hl (j : Fin J) : ‖(localCatalystMap a0 oracle j)ᴴ * localCatalystMap a0 oracle j‖ ≤
      α * T / J := by
    rw [localCatalystMap_gram a0 oracle j hw, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hw, Matrix.l2_opNorm_conjTranspose_mul_self]
    have hy := cayleyMidpointMap_norm_le H (α := α) hT hJ j hH
    calc
      _ ≤ (α * T / J) * (1 * 1) := by gcongr
      _ = _ := by ring
  calc
    _ = ‖(catalystMap a0 oracle)ᴴ * catalystMap a0 oracle‖ := by
      rw [Matrix.l2_opNorm_conjTranspose_mul_self]; ring
    _ = ‖∑ j : Fin J, (localCatalystMap a0 oracle j)ᴴ * localCatalystMap a0 oracle j‖ := by
      rw [catalystMap_gram]
    _ ≤ ∑ j : Fin J, ‖(localCatalystMap a0 oracle j)ᴴ * localCatalystMap a0 oracle j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin J, α * T / J := Finset.sum_le_sum (fun j _ => hl j)
    _ = α * T := by simp; field_simp

/-- The conjugate transpose of a reversed matrix product is the forward product of the conjugate
transposes. -/
theorem cayley_reverse_adjoint (f : ℕ → Matrix ιS ιS ℂ) (l : List ℕ) :
    ((l.map f).reverse.prod)ᴴ = (l.map (fun j => (f j)ᴴ)).prod := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, Matrix.conjTranspose_mul, ih]

/-- The difference of reversed products of contractions is bounded by the sum of the factor
differences. -/
theorem cayley_reverse_product_perturbation (f g : ℕ → Matrix ιS ιS ℂ) (J : ℕ)
    (hf : ∀ j < J, ‖f j‖ ≤ 1) (hg : ∀ j < J, ‖g j‖ ≤ 1) :
    ‖((List.range J).map f).reverse.prod - ((List.range J).map g).reverse.prod‖ ≤
      ∑ j ∈ Finset.range J, ‖f j - g j‖ := by
  rw [← Matrix.l2_opNorm_conjTranspose
    (((List.range J).map f).reverse.prod - ((List.range J).map g).reverse.prod),
    Matrix.conjTranspose_sub, cayley_reverse_adjoint, cayley_reverse_adjoint]
  have h := segment_product_perturbation_contraction_sum ιS
    (fun j => (f j)ᴴ) (fun j => (g j)ᴴ) J
    (by intro j hj; simpa only [Matrix.l2_opNorm_conjTranspose] using! hf j hj)
    (by intro j hj; simpa only [Matrix.l2_opNorm_conjTranspose] using! hg j hj)
  simpa only [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose] using! h

/-- The reversed product of consecutive ordered evolutions equals the ordered evolution over the
full grid interval. -/
theorem cayley_ordered_grid_product (H : ℝ → Matrix ιS ιS ℂ) (hcont : Continuous H)
    (T : ℝ) (J k : ℕ) :
    ((List.range k).map (fun j : ℕ => orderedEvolution (fun u => Complex.I • H u)
      ((j : ℝ) * T / J) (((j + 1 : ℕ) : ℝ) * T / J))).reverse.prod =
      orderedEvolution (fun u => Complex.I • H u) 0 ((k : ℝ) * T / J) := by
  have hc : Continuous (fun u => Complex.I • H u) := by fun_prop
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one, one_mul, ih]
    exact (orderedEvolution_cocycle _ hc 0 ((k : ℝ) * T / J)
      (((k + 1 : ℕ) : ℝ) * T / J))

/-- Integrating the stated Lipschitz deviation from the left endpoint gives at most `β * (t-s)^2
/ 2`. -/
theorem cayley_lipschitz_integral (H : ℝ → Matrix ιS ιS ℂ) (hcont : Continuous H)
    {s t β : ℝ} (hst : s ≤ t)
    (hlip : ∀ u ∈ Set.Icc s t, ‖H u - H s‖ ≤ β * |u - s|) :
    (∫ u in s..t, ‖H u - H s‖) ≤ β * (t - s)^2 / 2 := by
  have hf : IntervalIntegrable (fun u => ‖H u - H s‖) MeasureTheory.volume s t :=
    (hcont.sub continuous_const).norm.intervalIntegrable s t
  have hg : IntervalIntegrable (fun u => β * (u - s)) MeasureTheory.volume s t :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable s t
  calc
    _ ≤ ∫ u in s..t, β * (u - s) := intervalIntegral.integral_mono_on hst hf hg (by
      intro u hu; simpa only [abs_of_nonneg (sub_nonneg.mpr hu.1)] using! hlip u hu)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (f := fun u : ℝ => u) (g := fun _ : ℝ => s)
          (continuous_id.intervalIntegrable s t)
          (continuous_const.intervalIntegrable s t), integral_id,
        intervalIntegral.integral_const]
      ring

/-- Rescaling a Hamiltonian by the inverse of `α` is equivalent to rescaling its evolution time
by the same factor. -/
theorem cayley_rescale_evolution (M : Matrix ιS ιS ℂ) (α w : ℝ) :
    HamiltonianEvolution (((α⁻¹ : ℝ) : ℂ) • M) w = HamiltonianEvolution M (w / α) := by
  unfold HamiltonianEvolution
  rw [smul_smul]
  congr 2
  push_cast
  ring

set_option maxHeartbeats 800000 in

/-- The Cayley product approximates the ordered evolution with error at most `β*T^2/(2*J) +
(α*T)^3/(12*J^2)` under the stated regularity and step size assumptions. -/
theorem cayleyProduct_orderedEvolution_error (H : ℝ → Matrix ιS ιS ℂ)
    (hcont : Continuous H) {T α β : ℝ} {J : ℕ}
    (hα : 0 < α) (hT : 0 < T) (_hβ : 0 ≤ β) (hJ : 0 < J) (hw : α * T / J ≤ 1)
    (hH : ∀ t ∈ Set.Icc 0 T, (H t).IsHermitian)
    (hnorm : ∀ t ∈ Set.Icc 0 T, ‖H t‖ ≤ α)
    (hlip : ∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, ‖H t - H s‖ ≤ β * |t - s|) :
    ‖cayleyProduct H α T J - orderedEvolution (fun t => Complex.I • H t) 0 T‖ ≤
      β * T ^ 2 / (2 * (J : ℝ)) + (α * T) ^ 3 / (12 * (J : ℝ) ^ 2) := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  let w := α * T / J
  let δ := T / J
  let τ := fun j : ℕ => (j : ℝ) * T / J
  let f := gridCayleyStep H α T J
  let g := fun j : ℕ => orderedEvolution (fun u => Complex.I • H u) (τ j) (τ (j + 1))
  have hwpos : 0 < w := by dsimp [w]; positivity
  have hτ (j : ℕ) (hj : j < J) : τ j ≤ τ (j + 1) := by
    dsimp [τ]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hT.le) hJR.le
  have hδ (j : ℕ) : τ (j + 1) - τ j = δ := by dsimp [τ, δ]; push_cast; ring
  have hseg (j : ℕ) (hj : j < J) : Set.Icc (τ j) (τ (j + 1)) ⊆ Set.Icc 0 T := by
    intro u hu
    exact ⟨(cayley_grid_mem hT hJ hj.le).1.trans hu.1,
      hu.2.trans (cayley_grid_mem hT hJ (Nat.succ_le_of_lt hj)).2⟩
  have hf (j : ℕ) (hj : j < J) : ‖f j‖ ≤ 1 := by
    exact l2_norm_unitary_le_one (cayleyStep_unitary _
      (cayley_grid_hermitian H (α := α) hT hJ hj.le hH) w)
  have hg (j : ℕ) (hj : j < J) : ‖g j‖ ≤ 1 :=
    l2_norm_unitary_le_one (orderedEvolution_unitary_on_segment H hcont (hτ j hj)
      (fun u hu => hH u (hseg j hj hu)))
  have herr (j : ℕ) (hj : j < J) : ‖f j - g j‖ ≤ w^3 / 12 + β * δ^2 / 2 := by
    let M := (((α⁻¹ : ℝ) : ℂ) • H (τ j))
    have hm : M.IsHermitian := cayley_grid_hermitian H (α := α) hT hJ hj.le hH
    have hmn : ‖M‖ ≤ 1 := by
      calc
        _ = α⁻¹ * ‖H (τ j)‖ := by
          simp only [M, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hα)]
        _ ≤ α⁻¹ * α := mul_le_mul_of_nonneg_left
          (hnorm _ (cayley_grid_mem hT hJ hj.le)) (inv_nonneg.mpr hα.le)
        _ = 1 := inv_mul_cancel₀ hα.ne'
    have hc := cayleyStep_evolution_error M hm hmn
      (show |w| ≤ 1 by rw [abs_of_pos hwpos]; exact hw)
    rw [abs_of_pos hwpos] at hc
    have htime : w / α = δ := by dsimp [w, δ]; field_simp
    have he : HamiltonianEvolution M w = HamiltonianEvolution (H (τ j)) δ := by
      rw [cayley_rescale_evolution _ α w, htime]
    have hd := orderedEvolution_frozen_segment_error_on_segment H hcont (hτ j hj)
      (fun u hu => hH u (hseg j hj hu))
    have hi := cayley_lipschitz_integral H hcont (hτ j hj) (by
      intro u hu
      exact hlip _ (cayley_grid_mem hT hJ hj.le) u (hseg j hj hu))
    rw [hδ j] at hd hi
    rw [he] at hc
    calc
      _ ≤ ‖f j - HamiltonianEvolution (H (τ j)) δ‖ +
          ‖HamiltonianEvolution (H (τ j)) δ - g j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ w^3 / 12 + β * δ^2 / 2 := add_le_add hc (by
        simpa only [norm_sub_rev] using! hd.trans hi)
  have hgp : ((List.range J).map g).reverse.prod =
      orderedEvolution (fun u => Complex.I • H u) 0 T := by
    have h := cayley_ordered_grid_product H hcont T J J
    have ht : (J : ℝ) * T / J = T := by field_simp
    rw [ht] at h
    exact h
  rw [← hgp]
  change ‖((List.range J).map f).reverse.prod - ((List.range J).map g).reverse.prod‖ ≤ _
  calc
    _ ≤ ∑ j ∈ Finset.range J, ‖f j - g j‖ := cayley_reverse_product_perturbation f g J hf hg
    _ ≤ ∑ _j ∈ Finset.range J, (w^3 / 12 + β * δ^2 / 2) :=
      Finset.sum_le_sum (fun j hj => herr j (Finset.mem_range.mp hj))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [w, δ]
      field_simp
      ring

/-- The adjoint slice embedding restricts a vector to the selected slice indices. -/
theorem sliceEmbed_adjoint_mulVec {J : ℕ} (j : Fin J)
    (v : (ιS ⊕ ((ιA × ιS) × Fin J)) → ℂ) :
    (sliceEmbed j)ᴴ *ᵥ v = fun s => v (sliceIndex j s) := by
  ext s
  have hs (x : ιS ⊕ ((ιA × ιS) × Fin J)) :
      star (sliceEmbed j x s) = if x = sliceIndex j s then 1 else 0 := by
    rw [sliceEmbed_entry]
    split <;> simp
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, hs]
  exact sum_fiber_mul_left _ _

/-- The slice embedding preserves the public component and places the private component only in
the chosen slice. -/
theorem sliceEmbed_mulVec {J : ℕ} (j : Fin J) (v : (ιS ⊕ (ιA × ιS)) → ℂ) :
    sliceEmbed j *ᵥ v = Sum.elim (fun s => v (Sum.inl s))
      (fun (a, k) => if k = j then v (Sum.inr a) else 0) := by
  ext t
  cases t with
  | inl s => simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, sliceEmbed, eq_comm]
  | inr t =>
    rcases t with ⟨a, k⟩
    by_cases hk : k = j
    · subst k
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, sliceEmbed, eq_comm]
    · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, sliceEmbed, hk]

/-- The next partial Cayley product is the next grid step multiplied by the current partial
product. -/
theorem cayleyPartialProduct_succ (H : ℝ → Matrix ιS ιS ℂ) (α T : ℝ) (J k : ℕ) :
    cayleyPartialProduct H α T J (k + 1) =
      gridCayleyStep H α T J k * cayleyPartialProduct H α T J k := by
  simp only [cayleyPartialProduct, List.range_succ, List.map_append, List.map_cons,
    List.map_nil, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one, one_mul]

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid in

/-- Applying the local catalyst map equals the local catalyst vector evaluated on the inverse
shifted partial evolution. -/
theorem localCatalystMap_mulVec {H : ℝ → Matrix ιS ιS ℂ} {T α : ℝ} {J : ℕ}
    (a0 : ιA) (oracle : HamTOracle a0 H T α J) (j : Fin J) (ψ : ιS → ℂ) :
    localCatalystMap a0 oracle j *ᵥ ψ = localCatalystVec a0 (oracle.O j) (α * T / J)
      ((cayleyShift (((α⁻¹ : ℝ) : ℂ) • H ((j : ℝ) * T / J)) (α * T / J))⁻¹ *ᵥ
        (cayleyPartialProduct H α T J j *ᵥ ψ)) := by
  let r : ℂ := Real.sqrt (α * T / J / 2)
  let K := 1 + Complex.I • oracle.O j
  let V : Matrix (ιA × ιS) ιS ℂ := encodingFiber a0
  let B := cayleyShift (((α⁻¹ : ℝ) : ℂ) • H ((j : ℝ) * T / J)) (α * T / J)
  let P := cayleyPartialProduct H α T J j
  change (r • (K * (V * (B⁻¹ * P) : Matrix (ιA × ιS) ιS ℂ))) *ᵥ ψ =
    r • (K *ᵥ (V *ᵥ (B⁻¹ *ᵥ (P *ᵥ ψ))))
  simp only [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid in

/-- The extended matrix acts by adding the embedded change of the compressed vector under `R`. -/
theorem cayley_extension_mulVec {B C : Type} [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (E : Matrix B C ℂ) (R : Matrix C C ℂ) (v : B → ℂ) :
    (1 + (E * (R - 1) : Matrix B C ℂ) * Eᴴ) *ᵥ v =
      v + E *ᵥ (R *ᵥ (Eᴴ *ᵥ v) - Eᴴ *ᵥ v) := by
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.sub_mulVec]

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid in

/-- A localized Cayley reflection acts on the public component and chosen private slice while
preserving the other slices. -/
theorem cayleyReflectionAt_action (a0 : ιA) (w : ℝ) {J : ℕ} (j : Fin J)
    (u : ιS → ℂ) (v : ((ιA × ιS) × Fin J) → ℂ) :
    cayleyReflectionAt a0 w j *ᵥ Sum.elim u v =
      Sum.elim
        (fun s => (cayleyReflection a0 w *ᵥ Sum.elim u (fun a => v (a, j))) (Sum.inl s))
        (fun (a, k) => if k = j then
          (cayleyReflection a0 w *ᵥ Sum.elim u (fun a => v (a, j))) (Sum.inr a)
          else v (a, k)) := by
  let E := sliceEmbed (ιS := ιS) (ιA := ιA) j
  let R := cayleyReflection (ιS := ιS) a0 w
  let z := Sum.elim u (fun a => v (a, j))
  have hz : Eᴴ *ᵥ Sum.elim u v = z := by
    rw [sliceEmbed_adjoint_mulVec]
    ext s
    cases s <;> rfl
  change (1 + (E * (R - 1) : Matrix (ιS ⊕ ((ιA × ιS) × Fin J))
      (ιS ⊕ (ιA × ιS)) ℂ) * Eᴴ) *ᵥ Sum.elim u v = _
  refine Eq.trans (cayley_extension_mulVec E R (Sum.elim u v)) ?_
  rw [hz]
  rw [sliceEmbed_mulVec]
  ext t
  cases t with
  | inl s => simp only [Pi.add_apply, Sum.elim_inl, Pi.sub_apply, z]; abel
  | inr t =>
    rcases t with ⟨a, k⟩
    by_cases hk : k = j
    · subst k
      simp only [Pi.add_apply, Sum.elim_inr, ite_true, Pi.sub_apply, z]
      abel
    · simp only [Pi.add_apply, Sum.elim_inr, ite_eq_right hk, add_zero]

noncomputable def cayleyTransducerState {H : ℝ → Matrix ιS ιS ℂ} {T α : ℝ} {J : ℕ}
    (a0 : ιA) (oracle : HamTOracle a0 H T α J) (ψ : ιS → ℂ) (k : ℕ) :
    (ιS ⊕ ((ιA × ιS) × Fin J)) → ℂ :=
  Sum.elim (cayleyPartialProduct H α T J k *ᵥ ψ)
    (fun (a, j) => if (j : ℕ) < k then (localCatalystMap a0 oracle j *ᵥ ψ) a
      else (oracle.O j *ᵥ (localCatalystMap a0 oracle j *ᵥ ψ)) a)

set_option maxHeartbeats 800000 in

/-- The reflection at slice `k` advances the Cayley transducer state from step `k` to step
`k+1`. -/
theorem cayleyTransducerState_step {H : ℝ → Matrix ιS ιS ℂ} {T α : ℝ} {J k : ℕ}
    (a0 : ιA) (oracle : HamTOracle a0 H T α J) (ψ : ιS → ℂ)
    (hα : 0 < α) (hT : 0 < T) (hJ : 0 < J) (hk : k < J)
    (hH : ∀ t ∈ Set.Icc 0 T, (H t).IsHermitian) :
    cayleyReflectionAt a0 (α * T / J) ⟨k, hk⟩ *ᵥ
        cayleyTransducerState a0 oracle ψ k = cayleyTransducerState a0 oracle ψ (k + 1) := by
  let j : Fin J := ⟨k, hk⟩
  let M := (((α⁻¹ : ℝ) : ℂ) • H ((k : ℝ) * T / J))
  let w := α * T / J
  let u := cayleyPartialProduct H α T J k *ᵥ ψ
  have hw : 0 < w := by dsimp [w]; positivity
  have hm : M.IsHermitian := cayley_grid_hermitian H (α := α) hT hJ hk.le hH
  have hl := cayleyReflection_local_identity a0 (oracle.O j) (oracle.hermitian j)
    (oracle.unitary j) M hm (oracle.block j) hw u
  have hx := localCatalystMap_mulVec a0 oracle j ψ
  change localCatalystMap a0 oracle j *ᵥ ψ =
    localCatalystVec a0 (oracle.O j) w ((cayleyShift M w)⁻¹ *ᵥ u) at hx
  rw [← hx] at hl
  have hn : cayleyStep M w *ᵥ u = cayleyPartialProduct H α T J (k + 1) *ᵥ ψ := by
    rw [cayleyPartialProduct_succ, ← Matrix.mulVec_mulVec]
    rfl
  rw [hn] at hl
  unfold cayleyTransducerState
  rw [cayleyReflectionAt_action]
  simp only [Nat.lt_irrefl, ite_false]
  rw [hl]
  ext t
  cases t with
  | inl s => rfl
  | inr t =>
    rcases t with ⟨a, l⟩
    by_cases hj : l = j
    · subst l
      simp only [Sum.elim_inr, j, Nat.lt_succ_self, ite_true]
    · have hne : (l : ℕ) ≠ k := fun he => hj (Fin.ext he)
      have hiff : (l : ℕ) < k + 1 ↔ (l : ℕ) < k := by omega
      have hj' : l ≠ (⟨k, hk⟩ : Fin J) := hj
      simp only [Sum.elim_inr, ite_eq_right hj', hiff]

/-- The reversed product of the first `k` slice reflections advances the initial transducer
state to step `k`. -/
theorem cayleyTransducer_prefix {H : ℝ → Matrix ιS ιS ℂ} {T α : ℝ} {J : ℕ}
    (a0 : ιA) (oracle : HamTOracle a0 H T α J) (ψ : ιS → ℂ)
    (hα : 0 < α) (hT : 0 < T) (hJ : 0 < J)
    (hH : ∀ t ∈ Set.Icc 0 T, (H t).IsHermitian) (k : ℕ) (hk : k ≤ J) :
    ((((List.finRange J).take k).map (cayleyReflectionAt a0 (α * T / J))).reverse.prod) *ᵥ
        cayleyTransducerState a0 oracle ψ 0 = cayleyTransducerState a0 oracle ψ k := by
  induction k with
  | zero => simp only [List.take_zero, List.map_nil, List.reverse_nil, List.prod_nil, Matrix.one_mulVec]
  | succ k ih =>
    have hk' : k < J := Nat.lt_of_succ_le hk
    have hlen : k < (List.finRange J).length := by simpa only [List.length_finRange] using! hk'
    have hget : (List.finRange J)[k]'hlen = (⟨k, hk'⟩ : Fin J) := by
      apply Fin.ext
      simp
    have hword : (((List.finRange J).take (k + 1)).map
        (cayleyReflectionAt (ιS := ιS) a0 (α * T / J))).reverse.prod =
        cayleyReflectionAt (ιS := ιS) a0 (α * T / J) ⟨k, hk'⟩ *
          (((List.finRange J).take k).map (cayleyReflectionAt (ιS := ιS) a0 (α * T / J))).reverse.prod := by
      rw [List.take_succ_eq_append_getElem hlen, hget]
      simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
        List.reverse_cons, List.reverse_nil, List.prod_append, List.prod_cons,
        List.prod_nil, mul_one, one_mul]
    rw [hword, ← Matrix.mulVec_mulVec, ih hk'.le]
    exact cayleyTransducerState_step a0 oracle ψ hα hT hJ hk' hH

/-- Each slice of the global catalyst vector equals the corresponding local catalyst map applied
to the input. -/
theorem catalystMap_mulVec_slice {H : ℝ → Matrix ιS ιS ℂ} {T α : ℝ} {J : ℕ}
    (a0 : ιA) (oracle : HamTOracle a0 H T α J) (ψ : ιS → ℂ) (a : ιA × ιS) (j : Fin J) :
    (catalystMap a0 oracle *ᵥ ψ) (a, j) = (localCatalystMap a0 oracle j *ᵥ ψ) a := rfl

omit [DecidableEq ιS] [DecidableEq ιA] in

/-- The Hamiltonian oracle matrix applies each slice oracle to that slice of its input vector. -/
theorem hamTMatrix_mulVec_slice {J : ℕ}
    (O : Fin J → Matrix (ιA × ιS) (ιA × ιS) ℂ) (v : ((ιA × ιS) × Fin J) → ℂ)
    (a : ιA × ιS) (j : Fin J) :
    (hamTMatrix O *ᵥ v) (a, j) = (O j *ᵥ (fun b => v (b, j))) a := by
  simp [hamTMatrix, Matrix.blockDiagonal, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

/-- The direct sum oracle maps the public input and catalyst to the initial Cayley transducer
state. -/
theorem oracleDirectSum_initial_state {H : ℝ → Matrix ιS ιS ℂ} {T α : ℝ} {J : ℕ}
    (a0 : ιA) (oracle : HamTOracle a0 H T α J) (ψ : ιS → ℂ) :
    oracleDirectSum oracle.O *ᵥ Sum.elim ψ (catalystMap a0 oracle *ᵥ ψ) =
      cayleyTransducerState a0 oracle ψ 0 := by
  simp only [oracleDirectSum, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
  ext t
  cases t with
  | inl s => simp [cayleyTransducerState, cayleyPartialProduct]
  | inr t =>
    rcases t with ⟨a, j⟩
    simp only [Sum.elim_inr, cayleyTransducerState, Nat.not_lt_zero, ite_false,
      hamTMatrix_mulVec_slice, catalystMap_mulVec_slice]

/-- The final Cayley transducer state contains the Cayley evolved public input and the restored
catalyst. -/
theorem cayleyTransducer_final_state {H : ℝ → Matrix ιS ιS ℂ} {T α : ℝ} {J : ℕ}
    (a0 : ιA) (oracle : HamTOracle a0 H T α J) (ψ : ιS → ℂ) :
    cayleyTransducerState a0 oracle ψ J =
      Sum.elim (cayleyProduct H α T J *ᵥ ψ) (catalystMap a0 oracle *ᵥ ψ) := by
  ext t
  cases t with
  | inl s => rfl
  | inr t =>
    rcases t with ⟨a, j⟩
    simp only [cayleyTransducerState, Sum.elim_inr, ite_eq_left j.isLt, catalystMap_mulVec_slice]

/-- The Cayley transducer applies `cayleyProduct` to the public input while returning the
catalyst unchanged. -/
theorem cayleyTransducer_identity {H : ℝ → Matrix ιS ιS ℂ} {T α : ℝ} {J : ℕ}
    (a0 : ιA) (oracle : HamTOracle a0 H T α J)
    (hα : 0 < α) (hT : 0 < T) (hJ : 0 < J)
    (hH : ∀ t ∈ Set.Icc 0 T, (H t).IsHermitian) (ψ0 : ιS → ℂ) :
    cayleyTransducer a0 (α * T / J) oracle.O *ᵥ
        Sum.elim ψ0 (catalystMap a0 oracle *ᵥ ψ0) =
      Sum.elim (cayleyProduct H α T J *ᵥ ψ0) (catalystMap a0 oracle *ᵥ ψ0) := by
  have h := cayleyTransducer_prefix a0 oracle ψ0 hα hT hJ hH J le_rfl
  have ht : (List.finRange J).take J = List.finRange J := by
    simpa only [List.length_finRange] using! (List.take_length (l := List.finRange J))
  rw [ht, ← transducerCircuit, cayleyTransducer_final_state] at h
  rw [cayleyTransducer, ← Matrix.mulVec_mulVec, oracleDirectSum_initial_state]
  exact h

end Qatlib.Concepts.InteractionEvo.TransducerCore
