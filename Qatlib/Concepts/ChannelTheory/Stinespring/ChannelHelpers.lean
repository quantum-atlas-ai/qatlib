/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import QuantumInfo.Channels.Unbundled

/-!
# A conditional-swap channel and its environment

A normalized two-dimensional environment is swapped with the qubit in each
free sector, while blocked sectors retain their labels. The resulting isometry
gives explicit Kraus operators, a completely positive trace-preserving map, and
an equality between the operator-sum and partial-trace descriptions. Matrix-unit
formulas describe its action on free and blocked sectors.

This finite-dimensional construction illustrates [Stinespring1955] and
[Kraus1971]; see [Paulsen, dilation theory][Paulsen2002] for the operator-algebraic
background.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel

open Matrix
open scoped BigOperators

/-- The local basis labels, consisting of a qubit at each free label in `F` and a separate
blocked sector indexed by `B`. -/
abbrev LocalState (F B : Type) := Sum (F × Fin 2) B

variable {F B : Type} [Fintype F] [Fintype B] [DecidableEq F] [DecidableEq B]

/-- The two environment amplitudes `sqrt (1 - p)` and `sqrt p`, indexed by `Fin 2`. -/
noncomputable def localEnvironment (p : ℝ) (a : Fin 2) : ℂ :=
  if a = 0 then (Real.sqrt (1-p) : ℂ) else (Real.sqrt p : ℂ)

/-- The environment vector `localEnvironment p` is normalized when `0 ≤ p ≤ 1`. -/
theorem localEnvironment_normalized (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Qatlib.Foundations.PureStateMath.Normalized (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localEnvironment p) := by
  change (∑ a : Fin 2,
      ‖Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localEnvironment p a‖ ^ 2) = 1
  simp only [Fin.sum_univ_two, Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localEnvironment, ↓reduceIte,
    show (1 : Fin 2) ≠ 0 by decide, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sq_sqrt (sub_nonneg.mpr hp1), Real.sq_sqrt hp]
  ring

/-- The permutation that swaps the local qubit and environment bit in the free sector and fixes
the blocked sector. -/
def localSwapPermutation : Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B × Fin 2 → Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B × Fin 2
  | (Sum.inl (z,a), e) => (Sum.inl (z,e), a)
  | (Sum.inr z, e) => (Sum.inr z, e)

omit [Fintype F] [Fintype B] [DecidableEq F] [DecidableEq B] in

/-- Applying `localSwapPermutation` twice returns the original local state and environment bit. -/
theorem localSwapPermutation_involutive :
    Function.Involutive (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapPermutation (F := F) (B := B)) := by
  rintro ⟨s,e⟩
  rcases s with ⟨z,a⟩ | z <;> rfl

/-- The permutation matrix implementing `localSwapPermutation` on the local system and its
environment. -/
def localConditionalSwap :
    Matrix (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B × Fin 2) (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B × Fin 2) ℂ :=
  Qatlib.Foundations.PureStateMath.permMatrix Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapPermutation

/-- The conditional swap matrix `localConditionalSwap` is unitary. -/
theorem localConditionalSwap_unitary :
    Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localConditionalSwap (F := F) (B := B) ∈
      Matrix.unitaryGroup (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B × Fin 2) ℂ :=
  Qatlib.Foundations.PureStateMath.permMatrix_unitary Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapPermutation_involutive

/-- The matrix that appends the environment vector `q` to each local basis state. -/
def prepareLocalEnvironment (q : Fin 2 → ℂ) :
    Matrix (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B × Fin 2) (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B) ℂ :=
  fun u t => if u.1 = t then q u.2 else 0

/-- The Kraus matrix for environment outcome `e` after preparing `q` and conditionally swapping
the local qubit with the environment. -/
def localSwapKraus (q : Fin 2 → ℂ) (e : Fin 2) :
    Matrix (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B) (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B) ℂ
  | Sum.inl (z,a), Sum.inl (w,b) => if z = w then if e = b then q a else 0 else 0
  | Sum.inr z, Sum.inr w => if z = w then q e else 0
  | _, _ => 0

/-- The matrix obtained by stacking the conditional swap Kraus matrices along the environment
index. -/
def localSwapIsometry (q : Fin 2 → ℂ) :
    Matrix (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B × Fin 2) (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B) ℂ :=
  fun u t => Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus (F := F) (B := B) q u.2 u.1 t

/-- Preparing the environment and then applying the conditional swap yields `localSwapIsometry
q`. -/
theorem localConditionalSwap_mul_prepare (q : Fin 2 → ℂ) :
    Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localConditionalSwap (F := F) (B := B) * Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment (F := F) (B := B) q =
      Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapIsometry (F := F) (B := B) q := by
  ext u t
  change Qatlib.Foundations.PureStateMath.ApplyGate (Qatlib.Foundations.PureStateMath.permMatrix Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapPermutation)
    (fun w => Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment (F := F) (B := B) q w t) u = _
  rw [Qatlib.Foundations.PureStateMath.applyGate_permMatrix Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapPermutation_involutive]
  rcases u with ⟨s,e⟩
  rcases s with ⟨z,a⟩ | z <;> rcases t with ⟨w,b⟩ | w
  · simp only [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapPermutation, Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment, Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapIsometry,
      Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus, Sum.inl.injEq, Prod.mk.injEq]
    split_ifs <;> simp_all
  · simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapPermutation,
      Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment, Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapIsometry, Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus]
  · simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapPermutation,
      Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment, Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapIsometry, Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus]
  · simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapPermutation,
      Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment, Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapIsometry, Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus]

/-- The sum of conjugate amplitude products of a normalized environment vector is one. -/
private theorem local_environment_inner (q : Fin 2 → ℂ) (hq : Qatlib.Foundations.PureStateMath.Normalized q) :
    (∑ e, star (q e) * q e) = (1 : ℂ) := by
  simpa only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply] using
      (Qatlib.Foundations.PureStateMath.normalized_iff_inner_self q).mp hq

/-- Appending a normalized environment vector defines an isometry. -/
theorem prepareLocalEnvironment_isometry (q : Fin 2 → ℂ) (hq : Qatlib.Foundations.PureStateMath.Normalized q) :
    (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment (F := F) (B := B) q)ᴴ * Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment (F := F) (B := B) q = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · by_cases hij : i = j
    · subst j
      simpa only [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment, ↓reduceIte, Matrix.one_apply, if_true] using
        local_environment_inner q hq
    · simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment, hij]
  · intro k _ hki
    simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment, hki]
  · simp

/-- The stacked conditional swap matrix is an isometry when the environment vector is
normalized. -/
theorem localSwapIsometry_isometry (q : Fin 2 → ℂ) (hq : Qatlib.Foundations.PureStateMath.Normalized q) :
    (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapIsometry (F := F) (B := B) q)ᴴ * Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapIsometry (F := F) (B := B) q = 1 := by
  rw [← Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localConditionalSwap_mul_prepare, Matrix.conjTranspose_mul]
  have hU : (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localConditionalSwap (F := F) (B := B))ᴴ *
      Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localConditionalSwap (F := F) (B := B) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localConditionalSwap_unitary
  calc
    (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment (F := F) (B := B) q)ᴴ * (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localConditionalSwap (F := F) (B := B))ᴴ *
        (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localConditionalSwap (F := F) (B := B) * Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment (F := F) (B := B) q) =
        (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment (F := F) (B := B) q)ᴴ *
          ((Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localConditionalSwap (F := F) (B := B))ᴴ * Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localConditionalSwap (F := F) (B := B)) *
            Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment (F := F) (B := B) q := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU, Matrix.mul_one, Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment_isometry q hq]

/-- The conditional swap Kraus matrices satisfy the completeness relation for a normalized
environment vector. -/
theorem localSwapKraus_complete (q : Fin 2 → ℂ) (hq : Qatlib.Foundations.PureStateMath.Normalized q) :
    (∑ e, (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus (F := F) (B := B) q e)ᴴ * Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus (F := F) (B := B) q e) = 1 := by
  have he : (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapIsometry (F := F) (B := B) q)ᴴ * Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapIsometry (F := F) (B := B) q =
      ∑ e, (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus (F := F) (B := B) q e)ᴴ * Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus (F := F) (B := B) q e := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapIsometry, Matrix.sum_apply]
    rw [Finset.sum_comm]
  rw [← he]
  exact Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapIsometry_isometry q hq

/-- The completely positive matrix map given by the conditional swap Kraus family associated
with `q`. -/
noncomputable def localSwapMap (q : Fin 2 → ℂ) :
    MatrixMap (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B) (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B) ℂ :=
  MatrixMap.of_kraus (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus (F := F) (B := B) q) (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus (F := F) (B := B) q)

/-- The map `localSwapMap q` is completely positive for every environment vector `q`. -/
theorem localSwapMap_completelyPositive (q : Fin 2 → ℂ) :
    (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap (F := F) (B := B) q).IsCompletelyPositive :=
  MatrixMap.of_kraus_isCompletelyPositive (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus (F := F) (B := B) q)

/-- The map `localSwapMap q` preserves the trace when `q` is normalized. -/
theorem localSwapMap_tracePreserving (q : Fin 2 → ℂ) (hq : Qatlib.Foundations.PureStateMath.Normalized q) :
    (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap (F := F) (B := B) q).IsTracePreserving :=
  MatrixMap.IsTracePreserving.of_kraus_isTracePreserving _ _ (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus_complete q hq)

/-- The conditional-swap operator sum equals conjugation by its dilation followed
by an environment partial trace, as in [Stinespring's representation][Stinespring1955]. -/
theorem localSwapMap_eq_traceRight (q : Fin 2 → ℂ)
    (A : Matrix (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B) (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B) ℂ) :
    Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap q A = Matrix.traceRight
      (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapIsometry (F := F) (B := B) q * A * (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapIsometry (F := F) (B := B) q)ᴴ) := by
  ext i j
  simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap, MatrixMap.of_kraus, Matrix.traceRight, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapIsometry]

/-- The vector supported at the free label `z`, with qubit amplitudes given by `q` and zero
blocked component. -/
def localFreeVector (q : Fin 2 → ℂ) (z : F) : Qatlib.Foundations.PureStateMath.QState (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B)
  | Sum.inl (w,a) => if w = z then q a else 0
  | Sum.inr _ => 0

omit [Fintype F] [Fintype B] in

/-- A free-sector Kraus column is `localFreeVector q z` when the environment outcome equals the
input bit, and is zero otherwise. -/
theorem localSwapKraus_free_column (q : Fin 2 → ℂ) (e a : Fin 2) (z : F)
    (i : Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B) :
    Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus q e i (Sum.inl (z,a)) =
      if e = a then Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localFreeVector q z i else 0 := by
  rcases i with ⟨w,b⟩ | w
  · by_cases hw : w = z <;> by_cases he : e = a
    <;> simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus, Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localFreeVector, hw, he]
  · simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus,
      Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localFreeVector]

omit [Fintype F] [Fintype B] in

/-- A blocked-sector Kraus column is the corresponding basis vector multiplied by the
environment amplitude `q e`. -/
theorem localSwapKraus_blocked_column (q : Fin 2 → ℂ) (e : Fin 2) (z : B)
    (i : Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B) :
    Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus q e i (Sum.inr z) = q e * Qatlib.Foundations.PureStateMath.Ket (Sum.inr z) i := by
  rcases i with ⟨w,b⟩ | w
  · simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus,
      Qatlib.Foundations.PureStateMath.Ket]
  · by_cases hw : w = z <;> simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus, Qatlib.Foundations.PureStateMath.Ket, hw]

/-- The image of a matrix unit under `localSwapMap` is the sum of products of the corresponding
Kraus columns and their conjugates. -/
theorem localSwapMap_single_apply (q : Fin 2 → ℂ)
    (x y i j : Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B) :
    Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap q (Matrix.single x y 1) i j =
      ∑ e, Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus (F := F) (B := B) q e i x * star (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus (F := F) (B := B) q e j y) := by
  simp only [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap, MatrixMap.of_kraus, LinearMap.coe_sum, LinearMap.coe_mk,
    AddHom.coe_mk, Finset.sum_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro e _
  rw [Matrix.mul_apply, Finset.sum_eq_single y]
  · simp only [Matrix.mul_single_apply_same, mul_one, Matrix.conjTranspose_apply]
  · intro k _ hky
    rw [Matrix.mul_single_apply_of_ne 1 x y i k hky, zero_mul]
  · simp

/-- A free-sector matrix unit maps to the outer product of the associated free vectors when its
qubit indices agree, and to zero otherwise. -/
theorem localSwapMap_free_free (q : Fin 2 → ℂ) (z w : F) (a b : Fin 2) :
    Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap (F := F) (B := B) q
      (Matrix.single (Sum.inl (z,a)) (Sum.inl (w,b)) 1) =
    if a = b then Matrix.vecMulVec (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localFreeVector q z) (star (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localFreeVector q w))
      else 0 := by
  ext i j
  rw [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap_single_apply]
  simp_rw [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus_free_column]
  rw [Finset.sum_eq_single a]
  · by_cases hab : a = b <;> simp [hab, Matrix.vecMulVec, Pi.star_apply]
  · intro e _ hea
    simp [hea]
  · simp

/-- A free-to-blocked matrix unit maps to the corresponding free-vector and blocked-basis outer
product scaled by the conjugate input amplitude. -/
theorem localSwapMap_free_blocked (q : Fin 2 → ℂ) (z : F) (w : B) (a : Fin 2) :
    Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap q (Matrix.single (Sum.inl (z,a)) (Sum.inr w) 1) =
      star (q a) • Matrix.vecMulVec (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localFreeVector q z) (star (Qatlib.Foundations.PureStateMath.Ket (Sum.inr w))) := by
  ext i j
  rw [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap_single_apply]
  rcases i with ⟨r,c⟩ | r <;> rcases j with ⟨t,d⟩ | t
  · simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus,
      Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localFreeVector, Matrix.vecMulVec, Qatlib.Foundations.PureStateMath.Ket, Pi.star_apply]
  · by_cases hr : r = z <;> by_cases ht : t = w
    <;> simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus, Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localFreeVector, hr, ht, Matrix.vecMulVec, Qatlib.Foundations.PureStateMath.Ket,
      Pi.star_apply, Matrix.smul_apply, mul_comm]
  · simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus,
      Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localFreeVector, Matrix.vecMulVec, Qatlib.Foundations.PureStateMath.Ket, Pi.star_apply]
  · simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus,
      Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localFreeVector, Matrix.vecMulVec, Qatlib.Foundations.PureStateMath.Ket, Pi.star_apply]

/-- A blocked-to-free matrix unit maps to the corresponding blocked-basis and free-vector outer
product scaled by the input amplitude. -/
theorem localSwapMap_blocked_free (q : Fin 2 → ℂ) (z : B) (w : F) (b : Fin 2) :
    Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap q (Matrix.single (Sum.inr z) (Sum.inl (w,b)) 1) =
      q b • Matrix.vecMulVec (Qatlib.Foundations.PureStateMath.Ket (Sum.inr z)) (star (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localFreeVector q w)) := by
  ext i j
  rw [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap_single_apply]
  simp_rw [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus_free_column, Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus_blocked_column]
  rw [Finset.sum_eq_single b]
  · simp [Matrix.vecMulVec, Pi.star_apply, Matrix.smul_apply, mul_assoc]
  · intro e _ heb
    simp [heb]
  · simp

/-- For a normalized environment vector, `localSwapMap` fixes every matrix unit in the blocked
sector. -/
theorem localSwapMap_blocked_blocked (q : Fin 2 → ℂ) (hq : Qatlib.Foundations.PureStateMath.Normalized q) (z w : B) :
    Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap (F := F) (B := B) q (Matrix.single (Sum.inr z) (Sum.inr w) 1) =
      Matrix.single (Sum.inr z) (Sum.inr w) 1 := by
  have hsum : q 0 * star (q 0) + q 1 * star (q 1) = 1 := by
    simpa only [Fin.sum_univ_two, mul_comm] using local_environment_inner q hq
  ext i j
  rw [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap_single_apply]
  rcases i with ⟨r,c⟩ | r <;> rcases j with ⟨t,d⟩ | t
  · simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus,
      Matrix.single]
  · simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus,
      Matrix.single]
  · simp [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus,
      Matrix.single]
  · by_cases hr : r = z <;> by_cases ht : t = w
    <;> simp_all [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapKraus, Matrix.single] <;> aesop

/-- For `0 ≤ p ≤ 1`, the local heat-bath map is completely positive and trace preserving, and
equals the partial trace of its prepared conditional swap dilation. -/
theorem localHeatBath_physical_consumer (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap (F := F) (B := B) (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localEnvironment p)).IsCompletelyPositive ∧
    (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap (F := F) (B := B) (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localEnvironment p)).IsTracePreserving ∧
    ∀ A : Matrix (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B) (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.LocalState F B) ℂ,
      Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localEnvironment p) A = Matrix.traceRight
        ((Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localConditionalSwap (F := F) (B := B) *
            Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment (F := F) (B := B) (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localEnvironment p)) * A *
          (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localConditionalSwap (F := F) (B := B) *
            Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.prepareLocalEnvironment (F := F) (B := B) (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localEnvironment p))ᴴ) := by
  refine ⟨Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap_completelyPositive _,
    Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap_tracePreserving _ (Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localEnvironment_normalized p hp hp1), ?_⟩
  intro A
  rw [Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localConditionalSwap_mul_prepare]
  exact Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel.localSwapMap_eq_traceRight _ A

end Qatlib.Concepts.ChannelTheory.Stinespring.ConditionalSwapChannel
