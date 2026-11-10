/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary
import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.GramQueryCore.GramRealization

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

noncomputable def gramQuerySign {n : ℕ} (f : Fin n → Bool) (i : Fin (n + 1)) : ℂ :=
  if h : i.val < n then (if f ⟨i.val, h⟩ then -1 else 1) else 1

noncomputable def gramPhaseQuery (n R : ℕ) (f : Fin n → Bool) :
    Matrix (Fin (n + 1) × Fin R) (Fin (n + 1) × Fin R) ℂ :=
  Matrix.diagonal (fun iw => gramQuerySign f iw.1)

def gramQueryWitness {X : Type} [Fintype X] [DecidableEq X] (n T : ℕ)
    (input : X → Fin n → Bool) (G : Fin (T + 1) → Matrix X X ℂ)
    (M : Fin T → Fin (n + 1) → Matrix X X ℂ) : Prop :=
  (∀ x y, G 0 x y = 1) ∧
    ∀ t : Fin T, (∀ i, (M t i).PosSemidef) ∧
      (∑ i, M t i) = G ⟨t.val, by omega⟩ ∧
      (∑ i, Matrix.diagonal (fun x => star (gramQuerySign (input x) i)) * M t i *
        Matrix.diagonal (fun x => gramQuerySign (input x) i)) = G ⟨t.val + 1, by omega⟩

noncomputable def gramBitLift (n R : ℕ) [NeZero n] :
    Matrix ((Fin n × Bool) × Fin R) (Fin (n + 1) × Fin R) ℂ := fun q iw =>
  if _h : iw.1.val < n then
    if q.1.1.val = iw.1.val ∧ q.2 = iw.2 then
      ((Real.sqrt 2 : ℂ)⁻¹) * (if q.1.2 then -1 else 1) else 0
  else if q.1.1.val = 0 ∧ q.2 = iw.2 then (Real.sqrt 2 : ℂ)⁻¹ else 0

theorem gram_positive_matrix_actual_factorization :
    ∀ (X : Type) [Fintype X] [DecidableEq X] (A : Matrix X X ℂ),
      A.PosSemidef → ∃ V : Matrix X X ℂ, Vᴴ * V = A := by
  intro X _ _ A hA
  obtain ⟨V, hV⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨V, by simpa only [Matrix.star_eq_conjTranspose] using! hV.symm⟩

theorem gram_equal_inner_action {H X : Type} [Fintype H] [DecidableEq H]
    [Fintype X] [DecidableEq X] (V W : Matrix H X ℂ) (h : Vᴴ * V = Wᴴ * W)
    (a b : EuclideanSpace ℂ X) :
    inner ℂ (Matrix.toEuclideanLin V a) (Matrix.toEuclideanLin V b) =
      inner ℂ (Matrix.toEuclideanLin W a) (Matrix.toEuclideanLin W b) := by
  change inner ℂ (toEuclidean_fromVec (V *ᵥ a.ofLp)) (toEuclidean_fromVec (V *ᵥ b.ofLp)) =
    inner ℂ (toEuclidean_fromVec (W *ᵥ a.ofLp)) (toEuclidean_fromVec (W *ᵥ b.ofLp))
  rw [inner_euclidean_fromVec, inner_euclidean_fromVec]
  simp only [Qatlib.Foundations.PureStateMath.Inner, Matrix.star_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency true in

theorem gram_equal_actual_unitary_transport :
    ∀ (H X : Type) [Fintype H] [DecidableEq H] [Fintype X] [DecidableEq X]
      (V W : Matrix H X ℂ), Vᴴ * V = Wᴴ * W →
      ∃ U : Matrix H H ℂ, U ∈ Matrix.unitaryGroup H ℂ ∧ U * V = W := by
  intro H X _ _ _ _ V W hGram
  letI : InnerProductSpace ℂ (EuclideanSpace ℂ H) := inferInstance
  let v := Matrix.toEuclideanLin V
  let w := Matrix.toEuclideanLin W
  have hinner (a b : EuclideanSpace ℂ X) : inner ℂ (v a) (v b) = inner ℂ (w a) (w b) :=
    gram_equal_inner_action V W hGram a b
  have hker : v.ker ≤ w.ker := by
    intro a ha
    change v a = 0 at ha
    change w a = 0
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    simpa only [ha, inner_zero_left] using! (hinner a a).symm
  let L : v.range →ₗ[ℂ] EuclideanSpace ℂ H :=
    (v.ker.liftQ w hker).comp v.quotKerEquivRange.symm.toLinearMap
  letI : InnerProductSpace ℂ v.range := Submodule.innerProductSpace v.range
  have hL (a : EuclideanSpace ℂ X) (ha : v a ∈ v.range) : L ⟨v a, ha⟩ = w a := by
    change (v.ker.liftQ w hker) (v.quotKerEquivRange.symm ⟨v a, ha⟩) = w a
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hLis : ∀ a b : v.range, inner ℂ (L a) (L b) = inner ℂ a b := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    rw [hL a' ⟨a', rfl⟩, hL b' ⟨b', rfl⟩]
    exact (hinner a' b').symm
  let e := (L.isometryOfInner hLis).extend
  have he : Function.Surjective e :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := e.toLinearMap) rfl).mp e.injective
  let E := LinearIsometryEquiv.ofSurjective e he
  let U : Matrix H H ℂ := Matrix.toEuclideanLin.symm E.toLinearEquiv.toLinearMap
  have hu : U ∈ Matrix.unitaryGroup H ℂ := by
    exact E.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun H ℂ) (EuclideanSpace.basisFun H ℂ)
  refine ⟨U, hu, ?_⟩
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.toLin_mul (EuclideanSpace.basisFun X ℂ).toBasis
      (EuclideanSpace.basisFun H ℂ).toBasis (EuclideanSpace.basisFun H ℂ).toBasis]
  rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hUmap : Matrix.toEuclideanLin U = E.toLinearEquiv.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply _
  rw [hUmap]
  change E.toLinearEquiv.toLinearMap.comp v = w
  apply LinearMap.ext
  intro a
  change e (v a) = w a
  rw [LinearIsometry.extend_apply (L.isometryOfInner hLis) ⟨v a, LinearMap.mem_range_self v a⟩]
  exact hL a _

theorem gramQuerySign_star_mul_self {n : ℕ} (f : Fin n → Bool) (i : Fin (n + 1)) :
    star (gramQuerySign f i) * gramQuerySign f i = 1 := by
  unfold gramQuerySign
  split_ifs <;> norm_num

theorem gramPhaseQuery_unitary (n R : ℕ) (f : Fin n → Bool) :
    gramPhaseQuery n R f ∈ Matrix.unitaryGroup (Fin (n + 1) × Fin R) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, gramPhaseQuery,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext iw
  exact gramQuerySign_star_mul_self f iw.1

theorem gramBitLift_active (n R : ℕ) [NeZero n] (a : Fin n) (w : Fin R)
    (q : (Fin n × Bool) × Fin R) :
    gramBitLift n R q (a.castSucc, w) =
      if q.1.1 = a ∧ q.2 = w then
        ((Real.sqrt 2 : ℂ)⁻¹) * (if q.1.2 then -1 else 1) else 0 := by
  simp only [gramBitLift, Fin.val_castSucc, a.isLt, dite_true]
  congr 1
  exact propext (and_congr_left (fun _ => Fin.ext_iff.symm))

theorem gramBitLift_idle (n R : ℕ) [NeZero n] (w : Fin R)
    (q : (Fin n × Bool) × Fin R) :
    gramBitLift n R q (Fin.last n, w) =
      if q.1.1 = 0 ∧ q.2 = w then (Real.sqrt 2 : ℂ)⁻¹ else 0 := by
  simp only [gramBitLift, Fin.val_last, lt_self_iff_false, dite_false]
  congr 1
  exact propext (and_congr_left (fun _ => by simp only [Fin.ext_iff, Fin.val_zero]))

private theorem gram_inverse_sqrt_two_sq : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1 / 2 := by
  rw [inv_pow]
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [hs]
  norm_num

private theorem gramBitLift_gram_active_active (n R : ℕ) [NeZero n]
    (a b : Fin n) (w v : Fin R) :
    ((gramBitLift n R)ᴴ * gramBitLift n R) (a.castSucc, w) (b.castSucc, v) =
      if a = b ∧ w = v then 1 else 0 := by
  classical
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      gramBitLift_active]
  by_cases hab : a = b <;> by_cases hwv : w = v
  all_goals simp_all [ite_and, mul_ite, eq_comm]
  field_simp

private theorem gramBitLift_gram_active_idle (n R : ℕ) [NeZero n]
    (a : Fin n) (w v : Fin R) :
    ((gramBitLift n R)ᴴ * gramBitLift n R) (a.castSucc, w) (Fin.last n, v) = 0 := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    gramBitLift_active, gramBitLift_idle]
  by_cases ha : a = 0 <;> by_cases hwv : w = v
  all_goals simp_all [ite_and, mul_ite, eq_comm]

private theorem gramBitLift_gram_idle_idle (n R : ℕ) [NeZero n] (w v : Fin R) :
    ((gramBitLift n R)ᴴ * gramBitLift n R) (Fin.last n, w) (Fin.last n, v) =
      if w = v then 1 else 0 := by
  classical
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, gramBitLift_idle]
  by_cases hwv : w = v
  all_goals simp_all [ite_and, mul_ite, eq_comm]
  field_simp

noncomputable def gramQueriedColumns {H X : Type} [Fintype H]
    (O : X → Matrix H H ℂ) (V : Matrix H X ℂ) : Matrix H X ℂ :=
  fun h x => (O x *ᵥ (fun j => V j x)) h

theorem gram_actual_circuit_of_column_updates (H X : Type) [Fintype H] [DecidableEq H]
    [Fintype X] [DecidableEq X] (T : ℕ) (j : H) (O : X → Matrix H H ℂ)
    (V : Fin (T + 1) → Matrix H X ℂ)
    (h0 : ∀ x y, ((V 0)ᴴ * V 0) x y = 1)
    (hstep : ∀ t : Fin T,
      (gramQueriedColumns O (V t.castSucc))ᴴ * gramQueriedColumns O (V t.castSucc) =
        (V t.succ)ᴴ * V t.succ) :
    ∃ C : Circuit H, QueryCount C = T ∧ IsUnitaryCircuit C ∧
      ∀ x : X, Run (O x) C (Qatlib.Foundations.PureStateMath.Ket j) = fun h => V (Fin.last T) h x := by
  let S : Matrix H X ℂ := fun h _ => Qatlib.Foundations.PureStateMath.Ket j h
  have hS : Sᴴ * S = (V 0)ᴴ * V 0 := by
    ext x y
    rw [h0]
    change Qatlib.Foundations.PureStateMath.Inner
        (Qatlib.Foundations.PureStateMath.Ket j)
        (Qatlib.Foundations.PureStateMath.Ket j) = 1
    exact (normalized_iff_inner_self _).mp (normalized_ket j)
  obtain ⟨U0, hU0, hU0V⟩ := gram_equal_actual_unitary_transport H X S (V 0) hS
  have hrun (t : ℕ) (ht : t ≤ T) :
      ∃ C : Circuit H, QueryCount C = t ∧ IsUnitaryCircuit C ∧
        ∀ x : X, Run (O x) C (Qatlib.Foundations.PureStateMath.Ket j) = fun h => V ⟨t, by omega⟩ h x := by
    induction t with
    | zero =>
      refine ⟨[Step.gate U0], by simp, by simpa using! hU0, ?_⟩
      intro x
      simp only [Run, ApplyGate]
      funext h
      exact congrArg (fun A : Matrix H X ℂ => A h x) hU0V
    | succ t ih =>
      obtain ⟨C, hCq, hCu, hCr⟩ := ih (by omega)
      let tf : Fin T := ⟨t, by omega⟩
      obtain ⟨U, hU, hUV⟩ := gram_equal_actual_unitary_transport H X
        (gramQueriedColumns O (V tf.castSucc)) (V tf.succ) (hstep tf)
      refine ⟨C ++ [Step.query, Step.gate U], by simp [queryCount_append, hCq],
        (isUnitaryCircuit_append _ _).mpr ⟨hCu, by simpa using! hU⟩, ?_⟩
      intro x
      rw [run_append, hCr]
      simp only [Run, ApplyGate]
      funext h
      exact congrArg (fun A : Matrix H X ℂ => A h x) hUV
  exact hrun T le_rfl

private theorem gramBitLift_gram_idle_active (n R : ℕ) [NeZero n]
    (a : Fin n) (w v : Fin R) :
    ((gramBitLift n R)ᴴ * gramBitLift n R) (Fin.last n, w) (a.castSucc, v) = 0 := by
  have hh := congrArg
    (fun A : Matrix (Fin (n + 1) × Fin R) (Fin (n + 1) × Fin R) ℂ =>
      A (Fin.last n, w) (a.castSucc, v))
    (Matrix.isHermitian_conjTranspose_mul_self (gramBitLift n R)).eq
  simp only [Matrix.conjTranspose_apply, gramBitLift_gram_active_idle, star_zero] at hh
  exact hh.symm

theorem gramBitLift_isIsometry (n R : ℕ) [NeZero n] : IsIsometry (gramBitLift n R) := by
  unfold IsIsometry
  ext ⟨i, w⟩ ⟨j, v⟩
  refine Fin.lastCases ?_ (fun a => ?_) i
  · refine Fin.lastCases ?_ (fun b => ?_) j
    · rw [gramBitLift_gram_idle_idle]
      simp [Matrix.one_apply]
    · rw [gramBitLift_gram_idle_active]
      have hn : Fin.last n ≠ b.castSucc := by
        intro h
        have := congrArg Fin.val h
        change n = b.val at this
        omega
      simp [hn]
  · refine Fin.lastCases ?_ (fun b => ?_) j
    · rw [gramBitLift_gram_active_idle]
      simp
    · rw [gramBitLift_gram_active_active]
      simp [Matrix.one_apply]

theorem gramBitLift_query_intertwining (n R : ℕ) [NeZero n] (f : Fin n → Bool) :
    workspaceBitOracle (W := Fin R) f * gramBitLift n R =
      gramBitLift n R * gramPhaseQuery n R f := by
  ext ⟨⟨a, b⟩, w⟩ ⟨i, v⟩
  change ApplyGate (workspaceBitOracle (W := Fin R) f)
    (fun q => gramBitLift n R q (i, v)) ((a, b), w) = _
  rw [applyGate_workspaceBitOracle_mk, gramPhaseQuery, Matrix.mul_diagonal]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [gramBitLift_idle, gramQuerySign]
  · simp only [gramBitLift_active]
    by_cases haj : a = j
    · subst j
      cases b <;> cases hf : f a <;> by_cases hwv : w = v <;> simp [gramQuerySign, hf, hwv]
    · simp [haj]

theorem gram_idle_phase_actual_single_bit_query_bridge :
    ∀ (n R : ℕ) [NeZero n] (f : Fin n → Bool), IsIsometry (gramBitLift n R) ∧
      workspaceBitOracle (W := Fin R) f * gramBitLift n R =
        gramBitLift n R * gramPhaseQuery n R f := by
  intro n R _ f
  exact ⟨gramBitLift_isIsometry n R, gramBitLift_query_intertwining n R f⟩

theorem gramQuerySign_conjugate_scalar {n : ℕ} (f : Fin n → Bool)
    (i : Fin (n + 1)) (z : ℂ) :
    star (gramQuerySign f i) * z * gramQuerySign f i = z := by
  calc
    _ = z * (star (gramQuerySign f i) * gramQuerySign f i) := by ring
    _ = _ := by rw [gramQuerySign_star_mul_self, mul_one]

theorem gramQueryWitness_diagonal_one {X : Type} [Fintype X] [DecidableEq X]
    {n T : ℕ} {input : X → Fin n → Bool} {G : Fin (T + 1) → Matrix X X ℂ}
    {M : Fin T → Fin (n + 1) → Matrix X X ℂ} (h : gramQueryWitness n T input G M) :
    ∀ t : Fin (T + 1), ∀ x : X, G t x x = 1 := by
  intro t
  refine Fin.induction ?_ (fun i ih => ?_) t
  · intro x
    exact h.1 x x
  · intro x
    have hb := congrArg (fun A : Matrix X X ℂ => A x x) (h.2 i).2.1
    have ha := congrArg (fun A : Matrix X X ℂ => A x x) (h.2 i).2.2
    simp only [Matrix.sum_apply] at hb
    simp only [Matrix.sum_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      gramQuerySign_conjugate_scalar] at ha
    exact ha.symm.trans (hb.trans (ih x))

theorem gramQueryWitness_posSemidef {X : Type} [Fintype X] [DecidableEq X]
    {n T : ℕ} {input : X → Fin n → Bool} {G : Fin (T + 1) → Matrix X X ℂ}
    {M : Fin T → Fin (n + 1) → Matrix X X ℂ} (h : gramQueryWitness n T input G M) :
    ∀ t : Fin (T + 1), (G t).PosSemidef := by
  intro t
  refine Fin.induction ?_ (fun i _ => ?_) t
  · have h0 : G 0 = (fun _ _ => (1 : ℂ)) := by ext x y; exact h.1 x y
    rw [h0]
    convert! Matrix.posSemidef_conjTranspose_mul_self (fun (_ : Unit) (_ : X) => (1 : ℂ)) using 1
    ext x y
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  · change (G ⟨i.val + 1, by omega⟩).PosSemidef
    rw [← (h.2 i).2.2]
    apply Matrix.posSemidef_sum _
    intro j _
    have hp := Matrix.PosSemidef.conjTranspose_mul_mul_same ((h.2 i).1 j)
      (Matrix.diagonal (fun x => gramQuerySign (input x) j))
    simpa only [Matrix.diagonal_conjTranspose] using! hp

noncomputable def gramDirectSumMatrix {Q X Y : Type} (F : Q → Matrix X X ℂ) :
    Matrix (Q × (X ⊕ Y)) X ℂ := fun iw x =>
  match iw.2 with
  | Sum.inl a => F iw.1 a x
  | Sum.inr _ => 0

theorem gramDirectSumMatrix_gram {Q X Y : Type} [Fintype Q] [Fintype X] [Fintype Y]
    (F : Q → Matrix X X ℂ) :
    (gramDirectSumMatrix (Y := Y) F)ᴴ * gramDirectSumMatrix F = ∑ i, (F i)ᴴ * F i := by
  ext x y
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_sum_type, gramDirectSumMatrix, Matrix.sum_apply]

theorem gramDirectSumMatrix_queried {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    {n : ℕ} (input : X → Fin n → Bool) (F : Fin (n + 1) → Matrix X X ℂ) :
    gramQueriedColumns (fun x => Matrix.diagonal
      (fun iw : Fin (n + 1) × (X ⊕ Y) => gramQuerySign (input x) iw.1))
      (gramDirectSumMatrix F) = gramDirectSumMatrix
        (fun i => F i * Matrix.diagonal (fun x => gramQuerySign (input x) i)) := by
  ext ⟨i, w⟩ x
  cases w <;> simp [gramQueriedColumns, Matrix.mulVec_diagonal,
    gramDirectSumMatrix, Matrix.mul_diagonal, mul_comm]

noncomputable def gramOutputMatrix {X Z : Type} [DecidableEq Z] (n : ℕ)
    (label : X → Z) (B : Matrix X X ℂ) :
    Matrix (Fin (n + 1) × (X ⊕ (Z × X))) X ℂ := fun iw x =>
  match iw.2 with
  | Sum.inl _ => 0
  | Sum.inr za => if iw.1 = 0 ∧ za.1 = label x then B za.2 x else 0

theorem gramOutputMatrix_gram {X Z : Type} [Fintype X] [DecidableEq X]
    [Fintype Z] [DecidableEq Z] (n : ℕ) (label : X → Z) (B : Matrix X X ℂ)
    (hcross : ∀ x y, label x ≠ label y → (Bᴴ * B) x y = 0) :
    (gramOutputMatrix n label B)ᴴ * gramOutputMatrix n label B = Bᴴ * B := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_sum_type, gramOutputMatrix, star_zero, zero_mul, Finset.sum_const_zero, zero_add]
  by_cases hxy : label x = label y
  · simp [hxy, ite_and, mul_ite]
  · have hz := hcross x y hxy
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at hz
    rw [hz]
    simp [ite_and, mul_ite, Ne.symm hxy]

noncomputable def gramOutputReadout {X Z : Type} (n : ℕ) (fallback : Z) :
    Fin (n + 1) × (X ⊕ (Z × X)) → Z := fun iw =>
  match iw.2 with
  | Sum.inl _ => fallback
  | Sum.inr za => za.1

theorem gramOutputMatrix_support {X Z : Type} [DecidableEq Z] (n : ℕ)
    (label : X → Z) (B : Matrix X X ℂ) (fallback : Z) (x : X)
    (iw : Fin (n + 1) × (X ⊕ (Z × X))) (hiw : gramOutputReadout n fallback iw ≠ label x) :
    gramOutputMatrix n label B iw x = 0 := by
  rcases iw with ⟨i, w⟩
  cases w with
  | inl a => rfl
  | inr za =>
    change za.1 ≠ label x at hiw
    simp [gramOutputMatrix, hiw]

theorem gram_witness_sum_workspace_realization
    (X Z : Type) [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Z] [DecidableEq Z]
    (n T : ℕ) (input : X → Fin n → Bool) (label : X → Z)
    (G : Fin (T + 1) → Matrix X X ℂ) (M : Fin T → Fin (n + 1) → Matrix X X ℂ)
    (hw : gramQueryWitness n T input G M)
    (hlabel : ∀ x y, label x ≠ label y → G (Fin.last T) x y = 0) :
    ∃ (C : Circuit (Fin (n + 1) × (X ⊕ (Z × X))))
      (j : Fin (n + 1) × (X ⊕ (Z × X)))
      (readout : Fin (n + 1) × (X ⊕ (Z × X)) → Z),
      QueryCount C = T ∧ IsUnitaryCircuit C ∧
      ∀ x : X, MeasureProb
        (Run (Matrix.diagonal (fun iw : Fin (n + 1) × (X ⊕ (Z × X)) =>
          gramQuerySign (input x) iw.1)) C (Qatlib.Foundations.PureStateMath.Ket j))
        (Finset.univ.filter (fun iw => readout iw = label x)) = 1 := by
  choose F hF using (fun t : Fin T => fun i : Fin (n + 1) =>
    gram_positive_matrix_actual_factorization X (M t i) ((hw.2 t).1 i))
  obtain ⟨B, hB⟩ := gram_positive_matrix_actual_factorization X (G (Fin.last T))
    (gramQueryWitness_posSemidef hw (Fin.last T))
  let H := Fin (n + 1) × (X ⊕ (Z × X))
  let O : X → Matrix H H ℂ := fun x => Matrix.diagonal (fun iw => gramQuerySign (input x) iw.1)
  let out := gramOutputMatrix n label B
  have hout : outᴴ * out = G (Fin.last T) := by
    rw [gramOutputMatrix_gram n label B (fun x y hxy => by rw [hB]; exact hlabel x y hxy), hB]
  let V : Fin (T + 1) → Matrix H X ℂ := fun t =>
    if ht : t.val < T then gramDirectSumMatrix (F ⟨t.val, ht⟩) else out
  have hGram (t : Fin (T + 1)) : (V t)ᴴ * V t = G t := by
    by_cases ht : t.val < T
    · dsimp [V]
      rw [dif_pos ht, gramDirectSumMatrix_gram]
      simp_rw [hF]
      exact (hw.2 ⟨t.val, ht⟩).2.1
    · have he : t = Fin.last T := by apply Fin.ext; simp only [Fin.val_last]; omega
      subst t
      simpa only [V, Fin.val_last, lt_self_iff_false, dif_neg, not_false_eq_true] using! hout
  have h0 : ∀ x y, ((V 0)ᴴ * V 0) x y = 1 := by
    intro x y
    rw [hGram]
    exact hw.1 x y
  have hstep (t : Fin T) :
      (gramQueriedColumns O (V t.castSucc))ᴴ * gramQueriedColumns O (V t.castSucc) =
        (V t.succ)ᴴ * V t.succ := by
    have hv : V t.castSucc = gramDirectSumMatrix (F t) := by
      dsimp [V]
      rw [if_pos t.isLt]
    rw [hv]
    have hquery : gramQueriedColumns O (gramDirectSumMatrix (F t)) =
        gramDirectSumMatrix (fun i => F t i * Matrix.diagonal (fun x => gramQuerySign (input x) i)) := by
      ext ⟨i, w⟩ x
      cases w <;> simp [gramQueriedColumns, O, Matrix.mulVec_diagonal,
        gramDirectSumMatrix, Matrix.mul_diagonal, mul_comm]
    simp_rw [hquery]
    rw [gramDirectSumMatrix_gram, hGram]
    calc
      _ = ∑ i, Matrix.diagonal (fun x => star (gramQuerySign (input x) i)) * M t i *
          Matrix.diagonal (fun x => gramQuerySign (input x) i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose]
        calc
          _ = Matrix.diagonal (fun x => star (gramQuerySign (input x) i)) *
              ((F t i)ᴴ * F t i) * Matrix.diagonal (fun x => gramQuerySign (input x) i) := by
            simp only [Matrix.mul_assoc]
            rfl
          _ = _ := by rw [hF]
      _ = _ := (hw.2 t).2.2
  let x0 : X := Classical.choice inferInstance
  let j : H := (0, Sum.inl x0)
  obtain ⟨C, hCq, hCu, hCr⟩ := gram_actual_circuit_of_column_updates H X T j O V h0 hstep
  let readout : H → Z := gramOutputReadout n (label x0)
  refine ⟨C, j, readout, hCq, hCu, ?_⟩
  intro x
  have hvlast : V (Fin.last T) = out := by simp [V]
  rw [hCr, hvlast]
  have hn : Normalized (fun iw => out iw x) := by
    apply (normalized_iff_inner_self _).mpr
    change (outᴴ * out) x x = 1
    rw [hout]
    exact gramQueryWitness_diagonal_one hw (Fin.last T) x
  rw [MeasureProb, Finset.sum_filter]
  calc
    _ = ∑ iw : H, BornProb (fun iw => out iw x) iw := by
      apply Finset.sum_congr rfl
      intro iw _
      split_ifs with hiw
      · rfl
      · have hz : out iw x = 0 := gramOutputMatrix_support n label B (label x0) x iw hiw
        simp [BornProb, hz]
    _ = 1 := hn

theorem gram_witness_actual_exact_phase_query_algorithm :
    ∀ (X Z : Type) [Fintype X] [DecidableEq X] [Nonempty X]
      [Fintype Z] [DecidableEq Z] (n T : ℕ) (input : X → Fin n → Bool)
      (label : X → Z) (G : Fin (T + 1) → Matrix X X ℂ)
      (M : Fin T → Fin (n + 1) → Matrix X X ℂ), gramQueryWitness n T input G M →
      (∀ x y, label x ≠ label y → G ⟨T, by omega⟩ x y = 0) →
      ∃ (R : ℕ) (C : Circuit (Fin (n + 1) × Fin R)) (j : Fin (n + 1) × Fin R)
        (readout : Fin (n + 1) × Fin R → Z), 0 < R ∧ QueryCount C = T ∧
        (∀ U, Step.gate U ∈ C → U ∈ Matrix.unitaryGroup _ ℂ) ∧
        ∀ x : X, MeasureProb (Run (gramPhaseQuery n R (input x)) C (Qatlib.Foundations.PureStateMath.Ket j))
          (Finset.univ.filter (fun z => readout z = label x)) = 1 := by
  intro X Z _ _ _ _ _ n T input label G M hw hlabel
  obtain ⟨C, j, readout, hCq, hCu, hCr⟩ :=
    gram_witness_sum_workspace_realization X Z n T input label G M hw hlabel
  let W := X ⊕ (Z × X)
  let R := Fintype.card W
  let e : (Fin (n + 1) × W) ≃ (Fin (n + 1) × Fin R) :=
    Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin W)
  let readout' : Fin (n + 1) × Fin R → Z := fun iw => readout (e.symm iw)
  have hR : 0 < R := Fintype.card_pos
  have hleg := relabelCircuit_legality_resources e C
  refine ⟨R, relabelCircuit e C, e j, readout', hR, hleg.2.1.trans hCq, hleg.1.mpr hCu, ?_⟩
  intro x
  let S := Finset.univ.filter (fun iw => readout iw = label x)
  have hS : Finset.univ.filter (fun iw => readout' iw = label x) = S.map e.toEmbedding := by
    ext iw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hiw
      refine ⟨e.symm iw, ?_, e.apply_symm_apply iw⟩
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using! hiw
    · rintro ⟨a, ha, rfl⟩
      change readout (e.symm (e a)) = label x
      rw [Equiv.symm_apply_apply]
      exact (Finset.mem_filter.mp ha).2
  have hO : relabelGate e (Matrix.diagonal
      (fun iw : Fin (n + 1) × W => gramQuerySign (input x) iw.1)) = gramPhaseQuery n R (input x) := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp [relabelGate, gramPhaseQuery, e]
    · have hne : e.symm a ≠ e.symm b := fun he => hab (e.symm.injective he)
      simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply,
        hne, hab, if_false, gramPhaseQuery]
  have hket : relabelState e (Qatlib.Foundations.PureStateMath.Ket j) = Qatlib.Foundations.PureStateMath.Ket (e j) := by
    funext iw
    simp [relabelState, Qatlib.Foundations.PureStateMath.Ket, Equiv.symm_apply_eq]
  have hprob := (run_relabelCircuit_readout e (Matrix.diagonal
    (fun iw : Fin (n + 1) × W => gramQuerySign (input x) iw.1)) C (Qatlib.Foundations.PureStateMath.Ket j) S).2
  rw [hO, hket, ← hS] at hprob
  exact hprob.trans (hCr x)

end Qatlib.Concepts.GramQueryCore.GramRealization
