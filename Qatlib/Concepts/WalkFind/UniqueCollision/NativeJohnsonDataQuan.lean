/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.NativeJohnsonDataStat
import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary
import Mathlib.Data.Finset.Sort
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Mathlib.Tactic.Tauto

/-!
# Native data access for the Johnson walk

This module constructs oracle circuits for Johnson-walk collision search with input data stored
alongside the subset state. It proves that loading preserves amplitudes and normalization, and
that the stored collision phase flip implements the input-marked reflection used in
[Ambainis2007ElementDistinctness].

The setup circuit loads an `r`-element subset with `r` queries. Each native walk step uses one
loading query and one erasure query, while the stored phase flip uses none. The theorem
`nativeJohnsonData_answer` packages these circuits and their semantics into `NativeJohnsonData`.

## Main statements

* `nativeSetup_word`: preparation of the loaded uniform state using `r` queries.
* `nativeWalkWord_semantics`: implementation of `jwWalkBig` on loaded states.
* `nativeJohnsonData_answer`: the native Johnson data-access contract.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.WalkFind.WalkSpectrum
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.WalkFind.UniqueCollision

open Matrix Qatlib.Concepts.WalkFind.UniqueCollision
open scoped Classical BigOperators

/-- For a fixed input, the loaded basis map is injective on Johnson states. -/
theorem loadedBasis_injective {N M r : ℕ} (x : Fin N → ZMod M) :
    Function.Injective (loadedBasis (r:=r) x) := by
  intro p q hpq
  exact congrArg (fun z => z.2.1) hpq

/-- The amplitude of a loaded state at the basis label of `p` is the original amplitude at `p`. -/
theorem loadedState_at_basis {N M r : ℕ} [NeZero M]
    (x : Fin N → ZMod M) (ψ : QState (JRState N r)) (p : JRState N r) :
    loadedState x ψ (loadedBasis x p) = ψ p := by
  simp [loadedState, (loadedBasis_injective x).eq_iff]

/-- The matrix embedding Johnson basis states into their loaded labels has Gram matrix equal to
the identity. -/
theorem loadedBasis_isometry {N M r : ℕ} [NeZero M] (x : Fin N → ZMod M) :
    let E : Matrix (LoadedSpace N M r) (JRState N r) ℂ :=
      fun q p => if q = loadedBasis x p then 1 else 0
    Eᴴ*E = 1 := by
  (try dsimp only)
  ext p p'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (loadedBasis x p)]
  · simp [Matrix.one_apply, (loadedBasis_injective x).eq_iff]
  · intro q _ hq
    simp [hq]
  · simp

/-- Loading the input data preserves normalization of a Johnson-walk state. -/
theorem loadedState_normalized {N M r : ℕ} [NeZero M]
    (x : Fin N → ZMod M) {ψ : QState (JRState N r)} (hψ : Normalized ψ) :
    Normalized (loadedState x ψ) := by
  let E : Matrix (LoadedSpace N M r) (JRState N r) ℂ :=
    fun q p => if q = loadedBasis x p then 1 else 0
  have hE : Eᴴ*E = 1 := loadedBasis_isometry x
  have hstate : loadedState x ψ = E *ᵥ ψ := by
    ext q
    simp [loadedState, E, Matrix.mulVec, dotProduct]
  have hi : Qatlib.Foundations.PureStateMath.Inner (E *ᵥ ψ) (E *ᵥ ψ) = Qatlib.Foundations.PureStateMath.Inner ψ ψ := by
    simp only [Qatlib.Foundations.PureStateMath.Inner, Matrix.star_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    rw [hE, Matrix.vecMul_one]
  rw [hstate, normalized_iff_inner_self]
  exact hi.trans ((normalized_iff_inner_self ψ).mp hψ)

/-- On a correctly loaded basis label, the stored collision predicate is equivalent to the
input-marked predicate. -/
theorem storedCollision_at_basis {N M r k : ℕ} (x : Fin N → ZMod M)
    (p : JRState N r) :
    storedCollision k (loadedBasis x p) ↔ markedInput k x p := by
  constructor
  · rintro ⟨S, hS, hcard, v, hv⟩
    refine ⟨S, hS, hcard, v, ?_⟩
    intro i hi
    have hip : i ∈ p.val.1 := hS hi
    simpa [loadedBasis, hip] using! hv i hi
  · rintro ⟨S, hS, hcard, v, hv⟩
    refine ⟨S, hS, hcard, v, ?_⟩
    intro i hi
    simpa [loadedBasis, hS hi] using! hv i hi

/-- The query-free diagonal circuit that negates labels whose stored data contain a collision of
size `k`. -/
def nativeStoredFlip (N M r k : ℕ) [NeZero M] : Circuit (LoadedSpace N M r) :=
  [.gate (Matrix.diagonal (fun q => if storedCollision k q then (-1 : ℂ) else 1))]

/-- The stored collision phase-flip circuit is unitary. -/
theorem nativeStoredFlip_unitary (N M r k : ℕ) [NeZero M] :
    IsUnitaryCircuit (nativeStoredFlip N M r k) := by
  have h : Matrix.diagonal (fun q : LoadedSpace N M r =>
      if storedCollision k q then (-1 : ℂ) else 1) ∈
      Matrix.unitaryGroup (LoadedSpace N M r) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext q
    split_ifs <;> simp_all
  simpa [nativeStoredFlip] using! h

/-- The stored collision phase flip uses zero oracle queries. -/
theorem nativeStoredFlip_queries (N M r k : ℕ) [NeZero M] :
    QueryCount (nativeStoredFlip N M r k) = 0 := rfl

/-- On loaded states, the stored collision flip implements `inputFlip` on the underlying Johnson
state. -/
theorem nativeStoredFlip_semantics {N M r k : ℕ} [NeZero M]
    (x : Fin N → ZMod M) (ψ : QState (JRState N r)) :
    Run (alphabetOracle x) (nativeStoredFlip N M r k) (loadedState x ψ) =
      loadedState x (inputFlip k x *ᵥ ψ) := by
  ext q
  by_cases hq : ∃ p, q = loadedBasis x p
  · obtain ⟨p, rfl⟩ := hq
    simp [nativeStoredFlip, Run, ApplyGate, loadedState_at_basis,
      Matrix.mulVec_diagonal, inputFlip, storedCollision_at_basis]
  · have hn : ∀ p, q ≠ loadedBasis x p := fun p hp => hq ⟨p, hp⟩
    simp [nativeStoredFlip, Run, ApplyGate, Matrix.mulVec_diagonal, loadedState, hn]

/-- The involutive address permutation that swaps the state's distinguished address with the
selected address. -/
def nativeAddressRoute {N M r : ℕ} (select : JRState N r → Fin N) :
    Equiv.Perm (LoadedSpace N M r) where
  toFun q := ((Equiv.swap q.2.1.val.2 (select q.2.1) q.1.1, q.1.2), q.2)
  invFun q := ((Equiv.swap q.2.1.val.2 (select q.2.1) q.1.1, q.1.2), q.2)
  left_inv q := by simp
  right_inv q := by simp

/-- The involutive permutation that swaps the oracle answer register with the stored value at
the selected address. -/
def nativeDataStore {N M r : ℕ} (select : JRState N r → Fin N) :
    Equiv.Perm (LoadedSpace N M r) where
  toFun q := ((q.1.1, q.2.2 (select q.2.1)),
    (q.2.1, Function.update q.2.2 (select q.2.1) q.1.2))
  invFun q := ((q.1.1, q.2.2 (select q.2.1)),
    (q.2.1, Function.update q.2.2 (select q.2.1) q.1.2))
  left_inv q := by ext i <;> simp [Function.update_idem]
  right_inv q := by ext i <;> simp [Function.update_idem]

/-- A permutation matrix sends the basis ket at `p` to the basis ket at its permuted label. -/
private theorem native_perm_ket {H : Type} [Fintype H] [DecidableEq H]
    (f : Equiv.Perm H) (p : H) : permMatrix f *ᵥ Qatlib.Foundations.PureStateMath.Ket p = Qatlib.Foundations.PureStateMath.Ket (f p) := by
  ext q
  simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, permMatrix]

/-- Route to a selected address, query its value, swap the answer into stored data, and restore
the address register. -/
def nativeLoadRound {N M r : ℕ} [NeZero M] (select : JRState N r → Fin N) :
    Circuit (LoadedSpace N M r) :=
  [.gate (permMatrix (nativeAddressRoute select)), .query,
    .gate (permMatrix (nativeDataStore select)), .gate (permMatrix (nativeAddressRoute select))]

/-- A native loading round is a unitary circuit. -/
theorem nativeLoadRound_unitary {N M r : ℕ} [NeZero M] (select : JRState N r → Fin N) :
    IsUnitaryCircuit (nativeLoadRound (M:=M) select) := by
  have hR := permMatrix_unitary_of_injective (nativeAddressRoute (M:=M) select).injective
  have hD := permMatrix_unitary_of_injective (nativeDataStore (M:=M) select).injective
  simp [nativeLoadRound, hR, hD]

/-- When the selected stored entry is zero, a loading round fills it with the input value and
restores the oracle register. -/
theorem nativeLoadRound_run {N M r : ℕ} [NeZero M] (select : JRState N r → Fin N)
    (x data : Fin N → ZMod M) (p : JRState N r) (hz : data (select p) = 0) :
    Run (alphabetOracle x) (nativeLoadRound select) (Qatlib.Foundations.PureStateMath.Ket ((p.val.2,0),(p,data))) =
      Qatlib.Foundations.PureStateMath.Ket ((p.val.2,0),(p,Function.update data (select p) (x (select p)))) := by
  simp only [nativeLoadRound, Run, ApplyGate]
  rw [native_perm_ket]
  have hr : nativeAddressRoute (M:=M) select ((p.val.2,0),(p,data)) =
      ((select p,0),(p,data)) := by simp [nativeAddressRoute]
  rw [hr]
  change permMatrix (nativeAddressRoute select) *ᵥ
    (permMatrix (nativeDataStore select) *ᵥ
      (permMatrix (alphabetShift x) *ᵥ Qatlib.Foundations.PureStateMath.Ket ((select p,0),(p,data)))) = _
  rw [native_perm_ket]
  simp only [alphabetShift, Equiv.coe_fn_mk, zero_add]
  rw [native_perm_ket]
  simp only [nativeDataStore, Equiv.coe_fn_mk, hz]
  rw [native_perm_ket]
  simp [nativeAddressRoute]

/-- Concatenate loading rounds for a list of state-dependent address selectors. -/
def nativeLoadList {N M r : ℕ} [NeZero M] :
    List (JRState N r → Fin N) → Circuit (LoadedSpace N M r)
  | [] => []
  | select::rest => nativeLoadRound select ++ nativeLoadList rest

/-- A list of loading rounds is unitary and uses one query for each selector. -/
theorem nativeLoadList_resources {N M r : ℕ} [NeZero M]
    (ss : List (JRState N r → Fin N)) :
    IsUnitaryCircuit (nativeLoadList (M:=M) ss) ∧ QueryCount (nativeLoadList (M:=M) ss) = ss.length := by
  induction ss with
  | nil => simp [nativeLoadList]
  | cons s ss ih =>
    refine ⟨(isUnitaryCircuit_append _ _).mpr ⟨nativeLoadRound_unitary s, ih.1⟩, ?_⟩
    simp [nativeLoadList, nativeLoadRound, QueryCount, ih.2]

/-- Distinct selected addresses with initially zero entries are loaded with their input values,
leaving all other stored entries unchanged. -/
theorem nativeLoadList_run {N M r : ℕ} [NeZero M]
    (ss : List (JRState N r → Fin N)) (x data : Fin N → ZMod M) (p : JRState N r)
    (hn : (ss.map (fun select => select p)).Nodup)
    (hz : ∀ i ∈ ss.map (fun select => select p), data i = 0) :
    Run (alphabetOracle x) (nativeLoadList ss) (Qatlib.Foundations.PureStateMath.Ket ((p.val.2,0),(p,data))) =
      Qatlib.Foundations.PureStateMath.Ket ((p.val.2,0),(p,fun i => if i ∈ ss.map (fun select => select p) then x i else data i)) := by
  induction ss generalizing data with
  | nil => simp [nativeLoadList]
  | cons s ss ih =>
    have hs : s p ∉ ss.map (fun select => select p) := (List.nodup_cons.mp hn).1
    rw [nativeLoadList, run_append, nativeLoadRound_run s x data p (hz _ (by simp))]
    rw [ih _ (List.nodup_cons.mp hn).2 (by
      intro i hi
      have his : i ≠ s p := by intro h; subst i; exact hs hi
      simp [Function.update, his, hz i (by simp [hi])])]
    apply congrArg (fun data => Qatlib.Foundations.PureStateMath.Ket ((p.val.2,0),(p,data)))
    funext i
    by_cases his : i = s p
    · subst i; simp [hs]
    · simp [his, Function.update]

/-- The matrix of a circuit for a fixed oracle, with gates multiplied in execution order. -/
private def nativeCircuitMatrix {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) : Circuit H → Matrix H H ℂ
  | [] => 1
  | .gate U::cs => nativeCircuitMatrix O cs * U
  | .query::cs => nativeCircuitMatrix O cs * O

/-- Running a circuit equals applying its circuit matrix to the initial state. -/
private theorem nativeCircuitMatrix_spec {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (cs : Circuit H) (ψ : QState H) :
    Run O cs ψ = nativeCircuitMatrix O cs *ᵥ ψ := by
  induction cs generalizing ψ with
  | nil => simp [nativeCircuitMatrix]
  | cons g cs ih =>
    cases g <;> simp only [Run, ApplyGate, ih, Matrix.mulVec_mulVec, nativeCircuitMatrix]

/-- Push a state forward along a basis-label map by summing amplitudes of labels with the same
image. -/
def nativeBasisEmbedding {P H : Type} [Fintype P] [DecidableEq H]
    (e : P → H) (ψ : QState P) : QState H := fun y => ∑ p, if y = e p then ψ p else 0

/-- Embedding a basis ket gives the basis ket at the image label. -/
@[simp] theorem nativeBasisEmbedding_ket {P H : Type} [Fintype P] [DecidableEq P] [DecidableEq H]
    (e : P → H) (p : P) : nativeBasisEmbedding e (Qatlib.Foundations.PureStateMath.Ket p) = Qatlib.Foundations.PureStateMath.Ket (e p) := by
  ext y
  unfold nativeBasisEmbedding
  rw [Finset.sum_eq_single p]
  · simp [Qatlib.Foundations.PureStateMath.Ket]
  · intro q _ hq; simp [Qatlib.Foundations.PureStateMath.Ket, hq]
  · simp

/-- The zero-one matrix of a basis-label map. -/
private def nativeBasisMatrix {P H : Type} [Fintype P] [DecidableEq H]
    (e : P → H) : Matrix H P ℂ := fun y p => if y = e p then 1 else 0

/-- The basis embedding is matrix multiplication by `nativeBasisMatrix`. -/
private theorem nativeBasisMatrix_spec {P H : Type} [Fintype P] [DecidableEq H]
    (e : P → H) (ψ : QState P) : nativeBasisEmbedding e ψ = nativeBasisMatrix e *ᵥ ψ := by
  ext y
  simp [nativeBasisEmbedding, nativeBasisMatrix, Matrix.mulVec, dotProduct, ite_mul]

/-- Circuit semantics established on all embedded basis kets extend to every state by linearity. -/
theorem nativeBasisWord_semantics {P H : Type} [Fintype P] [DecidableEq P]
    [Fintype H] [DecidableEq H] (e e' : P → H) (O : Matrix H H ℂ)
    (cs : Circuit H) (K : Matrix P P ℂ)
    (hb : ∀ p, Run O cs (Qatlib.Foundations.PureStateMath.Ket (e p)) = nativeBasisEmbedding e' (K *ᵥ Qatlib.Foundations.PureStateMath.Ket p)) (ψ : QState P) :
    Run O cs (nativeBasisEmbedding e ψ) = nativeBasisEmbedding e' (K *ᵥ ψ) := by
  have hm : nativeCircuitMatrix O cs * nativeBasisMatrix e = nativeBasisMatrix e' * K := by
    ext y p
    have h := congrFun (hb p) y
    rw [nativeCircuitMatrix_spec] at h
    simpa [nativeBasisEmbedding, nativeBasisMatrix, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Qatlib.Foundations.PureStateMath.Ket, ite_mul] using! h
  rw [nativeBasisMatrix_spec, nativeCircuitMatrix_spec, Matrix.mulVec_mulVec, hm,
    nativeBasisMatrix_spec, Matrix.mulVec_mulVec]

/-- The address in position `j` of the increasing enumeration of the stored subset. -/
def nativeSlot {N r : ℕ} (j : Fin r) (p : JRState N r) : Fin N :=
  p.val.1.orderEmbOfFin p.property.1 j

/-- The circuit loading each address of the stored `r`-element subset once. -/
def nativeSubsetLoad (N M r : ℕ) [NeZero M] : Circuit (LoadedSpace N M r) :=
  nativeLoadList (List.ofFn (fun j : Fin r => nativeSlot j))

/-- Subset loading is unitary and uses exactly `r` oracle queries. -/
theorem nativeSubsetLoad_resources (N M r : ℕ) [NeZero M] :
    IsUnitaryCircuit (nativeSubsetLoad N M r) ∧ QueryCount (nativeSubsetLoad N M r) = r := by
  simpa [nativeSubsetLoad] using!
      nativeLoadList_resources (M:=M) (List.ofFn (fun j : Fin r => nativeSlot j))

/-- Subset loading sends the zero-data basis label of a Johnson state to its input-loaded basis
label. -/
theorem nativeSubsetLoad_ket {N M r : ℕ} [NeZero M] (x : Fin N → ZMod M) (p : JRState N r) :
    Run (alphabetOracle x) (nativeSubsetLoad N M r)
      (Qatlib.Foundations.PureStateMath.Ket (loadedBasis (fun _ => (0 : ZMod M)) p)) = Qatlib.Foundations.PureStateMath.Ket (loadedBasis x p) := by
  have hinj : Function.Injective (fun j : Fin r => nativeSlot j p) :=
    p.val.1.orderEmbOfFin p.property.1 |>.injective
  have hmem (i : Fin N) : (∃ j : Fin r, nativeSlot j p = i) ↔ i ∈ p.val.1 := by
    change i ∈ Set.range (p.val.1.orderEmbOfFin p.property.1) ↔ i ∈ p.val.1
    rw [Finset.range_orderEmbOfFin]
    rfl
  have h := nativeLoadList_run (List.ofFn (fun j : Fin r => nativeSlot j)) x (fun _ => 0) p
    (by simpa only [List.map_ofFn] using! List.nodup_ofFn.mpr hinj) (by simp)
  simpa [nativeSubsetLoad, loadedBasis, List.map_ofFn, hmem] using! h

/-- Subset loading transforms any zero-data loaded state into the corresponding input-loaded
state. -/
theorem nativeSubsetLoad_semantics {N M r : ℕ} [NeZero M]
    (x : Fin N → ZMod M) (ψ : QState (JRState N r)) :
    Run (alphabetOracle x) (nativeSubsetLoad N M r)
      (loadedState (fun _ => (0 : ZMod M)) ψ) = loadedState x ψ := by
  have h := nativeBasisWord_semantics (loadedBasis (fun _ => (0 : ZMod M))) (loadedBasis x)
    (alphabetOracle x) (nativeSubsetLoad N M r) 1 (fun p => by
      rw [Matrix.one_mulVec, nativeBasisEmbedding_ket]
      exact nativeSubsetLoad_ket x p) ψ
  simpa only [nativeBasisEmbedding, loadedState, Matrix.one_mulVec] using! h

/-- For `r < N`, a unitary matrix prepares the zero-data loaded uniform Johnson state from a
basis ket. -/
theorem nativeInitialPreparation (N M r : ℕ) [NeZero M] (hr : r < N) :
    ∃ (init : LoadedSpace N M r) (P : Matrix (LoadedSpace N M r) (LoadedSpace N M r) ℂ),
      P ∈ Matrix.unitaryGroup (LoadedSpace N M r) ℂ ∧
      P *ᵥ Qatlib.Foundations.PureStateMath.Ket init = loadedState (fun _ => (0 : ZMod M)) (jwStartBig N r) := by
  classical
  have hcard : 0 < Fintype.card (JRState N r) := by
    rw [jrState_card]
    exact Nat.mul_pos (Nat.choose_pos hr.le) (by omega)
  letI : Nonempty (JRState N r) := Fintype.card_pos_iff.mp hcard
  let p : JRState N r := Classical.choice inferInstance
  let init := loadedBasis (fun _ => (0 : ZMod M)) p
  let amplitude : LoadedSpace N M r → ℝ := fun q =>
    ∑ p : JRState N r, if q = loadedBasis (fun _ => (0 : ZMod M)) p then
      1/Real.sqrt (Fintype.card (JRState N r) : ℝ) else 0
  have hamp : ∀ q, 0 ≤ amplitude q := by
    intro q
    apply Finset.sum_nonneg
    intro p _
    split_ifs <;> positivity
  have hstate : (fun q => (amplitude q : ℂ)) =
      loadedState (fun _ => (0 : ZMod M)) (jwStartBig N r) := by
    ext q
    simp [amplitude, loadedState, jwStartBig, Complex.ofReal_sum, apply_ite]
  have hnormalized : Normalized (fun q => (amplitude q : ℂ)) := by
    rw [hstate]
    exact loadedState_normalized _ (jwStartBig_normSq N r hr)
  have hsquare : ∑ q, (amplitude q)^2 = 1 := by
    simpa only [Normalized, Complex.norm_real, Real.norm_eq_abs, sq_abs] using! hnormalized
  refine ⟨init, Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare amplitude init,
    Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare_unitary amplitude init hamp hsquare, ?_⟩
  rw [Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare_mulVec_ket amplitude init hamp, hstate]

/-- For `r < N`, a unitary setup circuit prepares the input-loaded uniform Johnson state using
exactly `r` queries. -/
theorem nativeSetup_word (N M r : ℕ) [NeZero M] (hr : r < N) :
    ∃ (init : LoadedSpace N M r) (setup : Circuit (LoadedSpace N M r)),
      IsUnitaryCircuit setup ∧ QueryCount setup = r ∧
      ∀ x : Fin N → ZMod M,
        Run (alphabetOracle x) setup (Qatlib.Foundations.PureStateMath.Ket init) = loadedState x (jwStartBig N r) := by
  obtain ⟨init, P, hP, hprep⟩ := nativeInitialPreparation N M r hr
  obtain ⟨hload, hqueries⟩ := nativeSubsetLoad_resources N M r
  refine ⟨init, [.gate P] ++ nativeSubsetLoad N M r, ?_, ?_, ?_⟩
  · exact (isUnitaryCircuit_append _ _).mpr ⟨by simp [hP], hload⟩
  · simp [hqueries]
  · intro x
    rw [run_append, run_gate, run_nil]
    change Run (alphabetOracle x) (nativeSubsetLoad N M r)
        (P *ᵥ Qatlib.Foundations.PureStateMath.Ket init) = _
    rw [hprep, nativeSubsetLoad_semantics]

/-- The matrix with entry `1/d` for pairs with equal fiber labels and zero otherwise. -/
private def nativeFiberAverage {H F : Type} [DecidableEq F]
    (label : H → F) (d : ℕ) : Matrix H H ℂ :=
  fun p q => if label p = label q then (1/(d : ℂ)) else 0

/-- If every label fiber has the same positive size `d`, its averaging matrix is an orthogonal
projector. -/
private theorem nativeFiberAverage_projector {H F : Type} [Fintype H] [DecidableEq H]
    [DecidableEq F] (label : H → F) (d : ℕ) (hd : 0 < d)
    (hc : ∀ p, Fintype.card {q : H // label p = label q} = d) :
    IsOrthogonalProjector (nativeFiberAverage label d) := by
  have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  constructor
  · ext p q
    simp only [Matrix.mul_apply, nativeFiberAverage]
    by_cases hpq : label p = label q
    · have hcond (u : H) : label u = label q ↔ label p = label u := by rw [← hpq, eq_comm]
      rw [if_pos hpq]
      simp only [hcond]
      have hterm (u : H) :
          (if label p = label u then 1/(d : ℂ) else 0) *
            (if label p = label u then 1/(d : ℂ) else 0) =
          if label p = label u then (1/(d : ℂ))^2 else 0 := by split_ifs <;> simp [pow_two]
      simp only [hterm]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Fintype.card_subtype, hc p]
      field_simp
    · rw [if_neg hpq]
      apply Finset.sum_eq_zero
      intro u _
      by_cases hpu : label p = label u
      · have huq : label u ≠ label q := fun h => hpq (hpu.trans h)
        simp [hpu, huq]
      · simp [hpu]
  · ext p q
    by_cases hpq : label p = label q
    · simp [nativeFiberAverage, hpq]
    · simp [nativeFiberAverage, hpq, Ne.symm hpq]

/-- Reflection about the averaging projector of equally sized positive fibers is unitary. -/
private theorem nativeFiberDiffusion_unitary {H F : Type} [Fintype H] [DecidableEq H]
    [DecidableEq F] (label : H → F) (d : ℕ) (hd : 0 < d)
    (hc : ∀ p, Fintype.card {q : H // label p = label q} = d) :
    ReflectionAbout (nativeFiberAverage label d) ∈ Matrix.unitaryGroup H ℂ :=
  reflectionAbout_unitary (nativeFiberAverage_projector label d hd hc)

/-- For `r < N`, the first full Johnson diffusion matrix is unitary. -/
theorem nativeBigDiff1_unitary (N r : ℕ) (hr : r < N) :
    jwBigDiff1 N r ∈ Matrix.unitaryGroup (JRState N r) ℂ := by
  have heq : jwBigDiff1 N r = ReflectionAbout
      (nativeFiberAverage (fun p : JRState N r => p.val.1) (N-r)) := by
    ext p q
    have he : p = q ↔ p.val.1 = q.val.1 ∧ p.val.2 = q.val.2 := by
      rw [Subtype.ext_iff, Prod.ext_iff]
    by_cases hpq : p.val.1 = q.val.1
    · simp [jwBigDiff1, ReflectionAbout, nativeFiberAverage, Matrix.one_apply, he, hpq,
        div_eq_mul_inv]
    · simp [jwBigDiff1, ReflectionAbout, nativeFiberAverage, he, hpq]
  rw [heq]
  exact nativeFiberDiffusion_unitary _ _ (by omega) (jwOutsideFiber_card N r)

/-- The second full Johnson diffusion matrix is unitary. -/
theorem nativeBigDiff2_unitary (N r : ℕ) :
    jwBigDiff2 N r ∈ Matrix.unitaryGroup (JRState' N r) ℂ := by
  have heq : jwBigDiff2 N r = ReflectionAbout
      (nativeFiberAverage (fun p : JRState' N r => p.val.1) (r+1)) := by
    ext p q
    have he : p = q ↔ p.val.1 = q.val.1 ∧ p.val.2 = q.val.2 := by
      rw [Subtype.ext_iff, Prod.ext_iff]
    by_cases hpq : p.val.1 = q.val.1
    · simp [jwBigDiff2, ReflectionAbout, nativeFiberAverage, Matrix.one_apply, he, hpq,
        div_eq_mul_inv]
    · simp [jwBigDiff2, ReflectionAbout, nativeFiberAverage, he, hpq]
  rw [heq]
  exact nativeFiberDiffusion_unitary _ _ (by omega) (jwInsideFiber_card N r)

/-- The second full diffusion transported back to `JRState N r` by the adjoining and removal
matrices. -/
def nativeInnerDiffusion (N r : ℕ) : Matrix (JRState N r) (JRState N r) ℂ :=
  jwDropMat N r * jwBigDiff2 N r * jwEmbedMat N r

/-- The transported inner diffusion is unitary. -/
theorem nativeInnerDiffusion_unitary (N r : ℕ) :
    nativeInnerDiffusion N r ∈ Matrix.unitaryGroup (JRState N r) ℂ := by
  have hD : (jwBigDiff2 N r)ᴴ*jwBigDiff2 N r = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using!
        Matrix.mem_unitaryGroup_iff'.mp (nativeBigDiff2_unitary N r)
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold nativeInnerDiffusion
  rw [jwDropMat_eq_embed_adjoint]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (jwEmbedMat N r) (jwEmbedMat N r)ᴴ, ← jwDropMat_eq_embed_adjoint,
    jwEmbedMat_mul_drop, Matrix.one_mul, ← Matrix.mul_assoc (jwBigDiff2 N r)ᴴ (jwBigDiff2 N r),
    hD, Matrix.one_mul, jwDropMat_mul_embed]

/-- Conjugate the tensor extension of `K` by address routing through a fixed reference address. -/
def nativeCoupledGate {N M r : ℕ} [NeZero M] (zero : Fin N)
    (K : Matrix (JRState N r) (JRState N r) ℂ) :
    Matrix (LoadedSpace N M r) (LoadedSpace N M r) ℂ :=
  let R := permMatrix (nativeAddressRoute (M:=M) (r:=r) (fun _ => zero))
  R * TensorGate 1 (TensorGate K 1) * R

/-- The coupled gate is unitary whenever its underlying Johnson-state matrix is unitary. -/
theorem nativeCoupledGate_unitary {N M r : ℕ} [NeZero M] (zero : Fin N)
    (K : Matrix (JRState N r) (JRState N r) ℂ) (hK : K ∈ Matrix.unitaryGroup (JRState N r) ℂ) :
    nativeCoupledGate (M:=M) zero K ∈ Matrix.unitaryGroup (LoadedSpace N M r) ℂ := by
  have hR :=
      permMatrix_unitary_of_injective (nativeAddressRoute (M:=M) (r:=r) (fun _ => zero)).injective
  exact (Matrix.unitaryGroup _ ℂ).mul_mem
    ((Matrix.unitaryGroup _ ℂ).mul_mem hR (tensorGate_unitary (by simp) (tensorGate_unitary hK (by simp)))) hR

/-- Entries of the coupled gate equal entries of the tensor extension evaluated at the routed
basis labels. -/
private theorem nativeCoupledGate_entry {N M r : ℕ} [NeZero M] (zero : Fin N)
    (K : Matrix (JRState N r) (JRState N r) ℂ) (p q : LoadedSpace N M r) :
    nativeCoupledGate zero K p q =
      TensorGate (1 : Matrix (Fin N × ZMod M) (Fin N × ZMod M) ℂ) (TensorGate K 1)
        (nativeAddressRoute (fun _ => zero) p) (nativeAddressRoute (fun _ => zero) q) := by
  let R := nativeAddressRoute (M:=M) (r:=r) (fun _ => zero)
  have hR : Function.Involutive R := R.left_inv
  let D : Matrix (LoadedSpace N M r) (LoadedSpace N M r) ℂ :=
    TensorGate (1 : Matrix (Fin N × ZMod M) (Fin N × ZMod M) ℂ) (TensorGate K 1)
  change (permMatrix R * D * permMatrix R) p q = D (R p) (R q)
  rw [Matrix.mul_assoc]
  change ApplyGate (permMatrix R) (fun i => (D*permMatrix R) i q) p = _
  rw [applyGate_permMatrix hR]
  simp only [Matrix.mul_apply, permMatrix]
  rw [Finset.sum_eq_single (R q)]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

/-- The loaded-space basis label of a Johnson state with its assigned data and a zero oracle
answer. -/
def nativeDataBasis {N M r : ℕ} (data : JRState N r → Fin N → ZMod M)
    (p : JRState N r) : LoadedSpace N M r := ((p.val.2,0),(p,data p))

/-- The embedding associated with `nativeDataBasis` is supported on the assigned label and has
the original Johnson-state amplitude there. -/
private theorem nativeDataEmbedding_apply {N M r : ℕ} [NeZero M]
    (data : JRState N r → Fin N → ZMod M) (ψ : QState (JRState N r)) (q : LoadedSpace N M r) :
    nativeBasisEmbedding (nativeDataBasis data) ψ q =
      if q = nativeDataBasis data q.2.1 then ψ q.2.1 else 0 := by
  unfold nativeBasisEmbedding
  apply Finset.sum_eq_single q.2.1
  · intro p _ hp
    have hne : q ≠ nativeDataBasis data p := by
      intro h
      exact hp (congrArg (fun z => z.2.1) h).symm
    simp [hne]
  · simp

/-- If `K` only connects states with equal assigned data, the coupled gate implements `K` on
embedded basis kets. -/
theorem nativeCoupledGate_ket {N M r : ℕ} [NeZero M] (zero : Fin N)
    (K : Matrix (JRState N r) (JRState N r) ℂ)
    (data : JRState N r → Fin N → ZMod M)
    (hdata : ∀ p q, K p q ≠ 0 → data p = data q) (p : JRState N r) :
    nativeCoupledGate zero K *ᵥ Qatlib.Foundations.PureStateMath.Ket (nativeDataBasis data p) =
      nativeBasisEmbedding (nativeDataBasis data) (K *ᵥ Qatlib.Foundations.PureStateMath.Ket p) := by
  ext q
  rw [mulVec_ket_apply, nativeCoupledGate_entry, nativeDataEmbedding_apply, mulVec_ket_apply]
  rcases q with ⟨⟨addr,answer⟩,⟨label,record⟩⟩
  by_cases hk : K label p = 0
  · simp [TensorGate, Matrix.one_apply, nativeAddressRoute, nativeDataBasis, hk]
  · have hd := hdata label p hk
    have hswap : Equiv.swap label.val.2 zero addr = zero ↔ addr = label.val.2 := by
      rw [Equiv.swap_apply_eq_iff]
      simp
    simp [TensorGate, Matrix.one_apply, nativeAddressRoute, nativeDataBasis,
      Equiv.swap_apply_left, Prod.mk.injEq, hswap, hd, ite_mul, mul_ite]
    split_ifs <;> tauto

/-- The input restricted to the stored subset, extended by zero outside it. -/
def nativeSubsetData {N M r : ℕ} (x : Fin N → ZMod M) (p : JRState N r) : Fin N → ZMod M :=
  fun i => if i ∈ p.val.1 then x i else 0

/-- The input restricted to the stored subset together with its distinguished address, extended
by zero elsewhere. -/
def nativeInsertedData {N M r : ℕ} (x : Fin N → ZMod M) (p : JRState N r) : Fin N → ZMod M :=
  fun i => if i ∈ insert p.val.2 p.val.1 then x i else 0

/-- Loading the distinguished address transforms the subset-data embedding into the
inserted-data embedding. -/
theorem nativeInsertLoad_semantics {N M r : ℕ} [NeZero M]
    (x : Fin N → ZMod M) (ψ : QState (JRState N r)) :
    Run (alphabetOracle x) (nativeLoadRound (fun p => p.val.2))
      (nativeBasisEmbedding (nativeDataBasis (nativeSubsetData x)) ψ) =
      nativeBasisEmbedding (nativeDataBasis (nativeInsertedData x)) ψ := by
  have h := nativeBasisWord_semantics (nativeDataBasis (nativeSubsetData x))
    (nativeDataBasis (nativeInsertedData x)) (alphabetOracle x)
    (nativeLoadRound (fun p => p.val.2)) 1 (fun p => by
      rw [Matrix.one_mulVec, nativeBasisEmbedding_ket]
      change Run (alphabetOracle x) (nativeLoadRound (fun p => p.val.2))
        (Qatlib.Foundations.PureStateMath.Ket ((p.val.2,0),(p,nativeSubsetData x p))) = _
      rw [nativeLoadRound_run _ x _ p (by simp [nativeSubsetData, p.property.2])]
      apply congrArg (fun data => Qatlib.Foundations.PureStateMath.Ket ((p.val.2,0),(p,data)))
      funext i
      by_cases hi : i = p.val.2
      · subst i; simp [nativeInsertedData]
      · simp [nativeInsertedData, nativeSubsetData, Function.update, hi]) ψ
  simpa only [Matrix.one_mulVec] using! h

/-- The involutive permutation that negates the oracle answer register. -/
def nativeAnswerNegation (N M r : ℕ) : Equiv.Perm (LoadedSpace N M r) where
  toFun q := ((q.1.1, -q.1.2),q.2)
  invFun q := ((q.1.1, -q.1.2),q.2)
  left_inv q := by simp
  right_inv q := by simp

/-- The circuit that swaps out the distinguished stored value and uncomputes it with one negated
oracle query. -/
def nativeEraseWord (N M r : ℕ) [NeZero M] : Circuit (LoadedSpace N M r) :=
  [.gate (permMatrix (nativeDataStore (fun p => p.val.2))),
    .gate (permMatrix (nativeAnswerNegation N M r)), .query,
    .gate (permMatrix (nativeAnswerNegation N M r))]

/-- The erasure circuit is unitary and uses exactly one oracle query. -/
theorem nativeEraseWord_resources (N M r : ℕ) [NeZero M] :
    IsUnitaryCircuit (nativeEraseWord N M r) ∧ QueryCount (nativeEraseWord N M r) = 1 := by
  have hS :=
      permMatrix_unitary_of_injective
      (nativeDataStore (N:=N) (M:=M) (r:=r) (fun p => p.val.2)).injective
  have hN := permMatrix_unitary_of_injective (nativeAnswerNegation N M r).injective
  simp [nativeEraseWord, hS, hN, QueryCount]

/-- Erasing the distinguished value sends an inserted-data basis label back to the corresponding
subset-data basis label. -/
theorem nativeEraseWord_ket {N M r : ℕ} [NeZero M] (x : Fin N → ZMod M) (p : JRState N r) :
    Run (alphabetOracle x) (nativeEraseWord N M r) (Qatlib.Foundations.PureStateMath.Ket (nativeDataBasis (nativeInsertedData x) p)) =
      Qatlib.Foundations.PureStateMath.Ket (nativeDataBasis (nativeSubsetData x) p) := by
  have hins : nativeInsertedData x p p.val.2 = x p.val.2 := by simp [nativeInsertedData]
  have hclear : Function.update (nativeInsertedData x p) p.val.2 0 = nativeSubsetData x p := by
    funext i
    by_cases hi : i = p.val.2
    · subst i; simp [nativeSubsetData, p.property.2]
    · simp [nativeInsertedData, nativeSubsetData, Function.update, hi]
  simp only [nativeEraseWord, Run, ApplyGate, nativeDataBasis]
  rw [native_perm_ket]
  simp only [nativeDataStore, Equiv.coe_fn_mk, hins, hclear]
  rw [native_perm_ket]
  simp only [nativeAnswerNegation, Equiv.coe_fn_mk]
  change permMatrix (nativeAnswerNegation N M r) *ᵥ
    (permMatrix (alphabetShift x) *ᵥ Qatlib.Foundations.PureStateMath.Ket ((p.val.2,-x p.val.2),(p,nativeSubsetData x p))) = _
  rw [native_perm_ket]
  simp only [alphabetShift, Equiv.coe_fn_mk, neg_add_cancel]
  rw [native_perm_ket]
  simp [nativeAnswerNegation]

/-- Erasure transforms any inserted-data embedded state into its subset-data embedding. -/
theorem nativeEraseWord_semantics {N M r : ℕ} [NeZero M]
    (x : Fin N → ZMod M) (ψ : QState (JRState N r)) :
    Run (alphabetOracle x) (nativeEraseWord N M r)
      (nativeBasisEmbedding (nativeDataBasis (nativeInsertedData x)) ψ) =
      nativeBasisEmbedding (nativeDataBasis (nativeSubsetData x)) ψ := by
  have h := nativeBasisWord_semantics (nativeDataBasis (nativeInsertedData x))
    (nativeDataBasis (nativeSubsetData x)) (alphabetOracle x) (nativeEraseWord N M r) 1
    (fun p => by rw [Matrix.one_mulVec, nativeBasisEmbedding_ket]; exact nativeEraseWord_ket x p) ψ
  simpa only [Matrix.one_mulVec] using! h

/-- The transported inner-diffusion entry equals the second diffusion entry on the corresponding
adjoined states. -/
private theorem nativeInnerDiffusion_entry (N r : ℕ) (p q : JRState N r) :
    nativeInnerDiffusion N r p q = jwBigDiff2 N r (jwInsertEquiv N r p) (jwInsertEquiv N r q) := by
  have hE : jwEmbedMat N r *ᵥ Qatlib.Foundations.PureStateMath.Ket q = Qatlib.Foundations.PureStateMath.Ket (jwInsertEquiv N r q) := by
    ext u
    simp [jwEmbedMat_mulVec, Qatlib.Foundations.PureStateMath.Ket, Equiv.symm_apply_eq]
  have h : nativeInnerDiffusion N r *ᵥ Qatlib.Foundations.PureStateMath.Ket q =
      jwDropMat N r *ᵥ (jwBigDiff2 N r *ᵥ (jwEmbedMat N r *ᵥ Qatlib.Foundations.PureStateMath.Ket q)) := by
    simp only [Matrix.mulVec_mulVec, nativeInnerDiffusion, Matrix.mul_assoc]
  have heq := congrFun h p
  rw [hE, jwDropMat_mulVec, mulVec_ket_apply, mulVec_ket_apply] at heq
  exact heq

/-- States connected by a nonzero first-diffusion entry have identical subset data. -/
private theorem nativeOutsideData_support {N M r : ℕ} (x : Fin N → ZMod M)
    (p q : JRState N r) (hK : jwBigDiff1 N r p q ≠ 0) : nativeSubsetData x p = nativeSubsetData x q := by
  have hS : p.val.1 = q.val.1 := by
    apply Classical.byContradiction
    intro h
    exact hK (by simp [jwBigDiff1, h])
  exact congrArg (fun S : Finset (Fin N) => fun i => if i ∈ S then x i else 0) hS

/-- States connected by a nonzero inner-diffusion entry have identical inserted data. -/
private theorem nativeInsideData_support {N M r : ℕ} (x : Fin N → ZMod M)
    (p q : JRState N r) (hK : nativeInnerDiffusion N r p q ≠ 0) :
    nativeInsertedData x p = nativeInsertedData x q := by
  rw [nativeInnerDiffusion_entry] at hK
  have hS : (jwInsertEquiv N r p).val.1 = (jwInsertEquiv N r q).val.1 := by
    apply Classical.byContradiction
    intro h
    exact hK (by simp [jwBigDiff2, h])
  change insert p.val.2 p.val.1 = insert q.val.2 q.val.1 at hS
  exact congrArg (fun S : Finset (Fin N) => fun i => if i ∈ S then x i else 0) hS

/-- A single coupled gate implements `K` on embedded states when assigned data are constant
along its nonzero entries. -/
private theorem nativeCoupledWord_semantics {N M r : ℕ} [NeZero M] (zero : Fin N)
    (K : Matrix (JRState N r) (JRState N r) ℂ)
    (data : JRState N r → Fin N → ZMod M)
    (hdata : ∀ p q, K p q ≠ 0 → data p = data q)
    (x : Fin N → ZMod M) (ψ : QState (JRState N r)) :
    Run (alphabetOracle x) [.gate (nativeCoupledGate zero K)]
      (nativeBasisEmbedding (nativeDataBasis data) ψ) =
      nativeBasisEmbedding (nativeDataBasis data) (K *ᵥ ψ) := by
  apply nativeBasisWord_semantics
  intro p
  simpa only [Run, ApplyGate] using! nativeCoupledGate_ket zero K data hdata p

/-- The native walk circuit combining the first diffusion, one loading query, the inner
diffusion, and one erasure query. -/
def nativeWalkWord {N M r : ℕ} [NeZero M] (zero : Fin N) : Circuit (LoadedSpace N M r) :=
  [.gate (nativeCoupledGate zero (jwBigDiff1 N r))] ++ nativeLoadRound (fun p => p.val.2) ++
    [.gate (nativeCoupledGate zero (nativeInnerDiffusion N r))] ++ nativeEraseWord N M r

/-- For `r < N`, the native walk circuit is unitary and uses exactly two oracle queries. -/
theorem nativeWalkWord_resources {N M r : ℕ} [NeZero M] (zero : Fin N) (hr : r < N) :
    IsUnitaryCircuit (nativeWalkWord (M:=M) (r:=r) zero) ∧
      QueryCount (nativeWalkWord (M:=M) (r:=r) zero) = 2 := by
  have hD1 := nativeCoupledGate_unitary (M:=M) zero (jwBigDiff1 N r) (nativeBigDiff1_unitary N r hr)
  have hD2 :=
      nativeCoupledGate_unitary (M:=M) zero (nativeInnerDiffusion N r)
      (nativeInnerDiffusion_unitary N r)
  have hload := nativeLoadRound_unitary (N:=N) (M:=M) (r:=r) (fun p => p.val.2)
  obtain ⟨herase, hqerase⟩ := nativeEraseWord_resources N M r
  constructor
  · simp only [nativeWalkWord, isUnitaryCircuit_append, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
    exact ⟨⟨⟨hD1, hload⟩, hD2⟩, herase⟩
  · simp [nativeWalkWord, nativeLoadRound, nativeEraseWord, QueryCount]

/-- On input-loaded states, the native walk circuit implements the full Johnson-walk matrix. -/
theorem nativeWalkWord_semantics {N M r : ℕ} [NeZero M] (zero : Fin N)
    (x : Fin N → ZMod M) (ψ : QState (JRState N r)) :
    Run (alphabetOracle x) (nativeWalkWord (M:=M) (r:=r) zero) (loadedState x ψ) =
      loadedState x (jwWalkBig N r *ᵥ ψ) := by
  change Run (alphabetOracle x) (nativeWalkWord (M:=M) (r:=r) zero)
    (nativeBasisEmbedding (nativeDataBasis (nativeSubsetData x)) ψ) = _
  simp only [nativeWalkWord, run_append]
  rw [nativeCoupledWord_semantics zero _ _ (nativeOutsideData_support x),
    nativeInsertLoad_semantics, nativeCoupledWord_semantics zero _ _ (nativeInsideData_support x),
    nativeEraseWord_semantics]
  change loadedState x (nativeInnerDiffusion N r *ᵥ (jwBigDiff1 N r *ᵥ ψ)) = _
  rw [Matrix.mulVec_mulVec]
  rfl

/-- The native setup, walk, and stored phase-flip circuits satisfy `NativeJohnsonData`, with
query counts `r`, two, and zero respectively [Ambainis2007ElementDistinctness]. -/
theorem nativeJohnsonData_answer : NativeJohnsonData := by
  intro N M r k _ _ _ hr
  have hN : 0 < N := by omega
  let zero : Fin N := ⟨0,hN⟩
  obtain ⟨init, setup, hsetup, hqsetup, hsetupsem⟩ := nativeSetup_word N M r hr
  obtain ⟨hwalk, hqwalk⟩ := nativeWalkWord_resources (M:=M) (r:=r) zero hr
  exact ⟨{
    init := init
    setup := setup
    walk := nativeWalkWord zero
    flip := nativeStoredFlip N M r k
    unitarySetup := hsetup
    unitaryWalk := hwalk
    unitaryFlip := nativeStoredFlip_unitary N M r k
    setupQueries := hqsetup
    walkQueries := hqwalk
    flipQueries := nativeStoredFlip_queries N M r k
    setupSemantics := hsetupsem
    walkSemantics := nativeWalkWord_semantics zero
    flipSemantics := nativeStoredFlip_semantics
  }⟩

end Qatlib.Concepts.WalkFind.UniqueCollision
