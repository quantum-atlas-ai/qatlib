/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QtmSimulation.Phi3Compilation.QtmPhi3WireTransport
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.SearchAlgorithm

namespace Qatlib.Concepts.QtmSimulation.Phi3Compilation
open Matrix
open scoped Classical BigOperators

def qtmBlockBasisCode {C : Type} (c b : ℕ) (e : C → Reg b) (r : Fin c → C) : Reg (c*b) :=
  fun w => let i := (finProdFinEquiv (m := c) (n := b)).symm w
           e (r i.1) i.2

def qtmBlockWires {m c : ℕ} (p : Fin m ↪ Fin c) (b : ℕ) : Fin (m*b) ↪ Fin (c*b) :=
  { toFun := fun w =>
      let i := (finProdFinEquiv (m := m) (n := b)).symm w
      (finProdFinEquiv (m := c) (n := b)) (p i.1,i.2)
    inj' := by
      intro x y h
      have hh := (finProdFinEquiv (m := c) (n := b)).injective h
      apply (finProdFinEquiv (m := m) (n := b)).symm.injective
      apply Prod.ext
      · exact p.injective (congrArg Prod.fst hh)
      · exact congrArg (fun z : Fin c × Fin b => z.2) hh }

def qtmCellContextExtend {C : Type} {m c : ℕ} (p : Fin m ↪ Fin c)
    (ctx : Fin c → C) (r : Fin m → C) : Fin c → C := Function.extend p r ctx

@[simp] theorem qtmCellContextExtend_at {C : Type} {m c : ℕ} (p : Fin m ↪ Fin c)
    (ctx : Fin c → C) (r : Fin m → C) (i : Fin m) :
    qtmCellContextExtend p ctx r (p i) = r i := p.injective.extend_apply _ _ _

theorem qtmBlock_context {C : Type} {m c : ℕ} (p : Fin m ↪ Fin c) (b : ℕ)
    (e : C → Reg b) (ctx : Fin c → C) (r : Fin m → C) :
    qtmWireContextExtend (qtmBlockWires p b) (qtmBlockBasisCode c b e ctx)
      (qtmBlockBasisCode m b e r) =
      qtmBlockBasisCode c b e (qtmCellContextExtend p ctx r) := by
  funext w
  obtain ⟨⟨j,u⟩,rfl⟩ := (finProdFinEquiv (m := c) (n := b)).surjective w
  by_cases hj : ∃ i, p i = j
  · obtain ⟨i,rfl⟩ := hj
    have hw : (finProdFinEquiv (m := c) (n := b)) (p i,u) =
        qtmBlockWires p b ((finProdFinEquiv (m := m) (n := b)) (i,u)) := by
      change (finProdFinEquiv (m := c) (n := b)) (p i,u) =
        (finProdFinEquiv (m := c) (n := b))
          (p ((finProdFinEquiv (m := m) (n := b)).symm
            ((finProdFinEquiv (m := m) (n := b)) (i,u))).1,
          ((finProdFinEquiv (m := m) (n := b)).symm
            ((finProdFinEquiv (m := m) (n := b)) (i,u))).2)
      rw [Equiv.symm_apply_apply]
    conv_lhs => rw [hw, qtmWireContextExtend_at]
    simp only [qtmBlockBasisCode, Equiv.symm_apply_apply, qtmCellContextExtend_at]
  · have hw : ¬∃ i, qtmBlockWires p b i =
        (finProdFinEquiv (m := c) (n := b)) (j,u) := by
      rintro ⟨i,hi⟩
      have hh := (finProdFinEquiv (m := c) (n := b)).injective hi
      exact hj ⟨_,congrArg Prod.fst hh⟩
    rw [qtmWireContextExtend, Function.extend_apply' _ _ _ hw]
    simp only [qtmBlockBasisCode, Equiv.symm_apply_apply]
    rw [qtmCellContextExtend, Function.extend_apply' _ _ _ hj]

theorem qtmBlock_context_frame {C : Type} [Fintype C] [DecidableEq C]
    {m c : ℕ} (p : Fin m ↪ Fin c) (b : ℕ) (e : C → Reg b)
    (ctx : Fin c → C) (ψ : QState (Fin m → C)) :
    qtmWireContextEmbed (qtmBlockWires p b) (qtmBlockBasisCode c b e ctx)
      (finiteBasisPadState (qtmBlockBasisCode m b e) ψ) =
      ∑ r, ψ r • Qatlib.Foundations.PureStateMath.Ket (qtmBlockBasisCode c b e (qtmCellContextExtend p ctx r)) := by
  conv_lhs => arg 3; arg 2; rw [state_ket_expansion ψ]
  simp only [finiteBasisPadState_sum, finiteBasisPadState_smul, finiteBasisPadState_ket,
    qtmWireContextEmbed_sum, qtmWireContextEmbed_smul, qtmWireContextEmbed_ket,
    qtmBlock_context]

def qtmCellGate {C : Type} {m c : ℕ} (p : Fin m ↪ Fin c)
    (U : Matrix (Fin m → C) (Fin m → C) ℂ) : Matrix (Fin c → C) (Fin c → C) ℂ :=
  fun x y => if ∀ j, (∀ i, p i ≠ j) → x j = y j
    then U (fun i => x (p i)) (fun i => y (p i)) else 0

theorem qtmCellContextExtend_reconstruct {C : Type} {m c : ℕ} (p : Fin m ↪ Fin c)
    (x y : Fin c → C) (h : ∀ j, (∀ i, p i ≠ j) → x j = y j) :
    qtmCellContextExtend p y (fun i => x (p i)) = x := by
  funext j
  by_cases hj : ∃ i, p i = j
  · obtain ⟨i,rfl⟩ := hj
    exact qtmCellContextExtend_at p y _ i
  · rw [qtmCellContextExtend, Function.extend_apply' _ _ _ hj]
    exact (h j (fun i hi => hj ⟨i,hi⟩)).symm

theorem qtmCellGate_ket {C : Type} [Fintype C] [DecidableEq C] {m c : ℕ}
    (p : Fin m ↪ Fin c) (U : Matrix (Fin m → C) (Fin m → C) ℂ) (r : Fin c → C) :
    ApplyGate (qtmCellGate p U) (Qatlib.Foundations.PureStateMath.Ket r) =
      ∑ s, U s (fun i => r (p i)) • Qatlib.Foundations.PureStateMath.Ket (qtmCellContextExtend p r s) := by
  funext x
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single (fun i => x (p i))]
  · unfold qtmCellGate
    by_cases hoff : ∀ j, (∀ i, p i ≠ j) → x j = r j
    · rw [if_pos hoff, if_pos (qtmCellContextExtend_reconstruct p x r hoff).symm]
    · rw [if_neg hoff]
      have hx : x ≠ qtmCellContextExtend p r (fun i => x (p i)) := by
        intro hh
        apply hoff
        intro j hj
        have hn : ¬∃ i, p i = j := by rintro ⟨i,hi⟩; exact hj i hi
        rw [hh, qtmCellContextExtend, Function.extend_apply' _ _ _ hn]
      rw [if_neg hx]
  · intro s _ hs
    have hx : x ≠ qtmCellContextExtend p r s := by
      intro hh
      apply hs
      funext i
      have hi := congrFun hh (p i)
      simpa using! hi.symm
    rw [if_neg hx]
  · intro hx
    exact (hx (Finset.mem_univ _)).elim

theorem qtmBlockBasisCode_injective {C : Type} (c b : ℕ) (e : C → Reg b)
    (he : Function.Injective e) : Function.Injective (qtmBlockBasisCode c b e) := by
  intro r s h
  funext i
  apply he
  funext u
  have hh := congrFun h ((finProdFinEquiv (m := c) (n := b)) (i,u))
  simpa only [qtmBlockBasisCode, Equiv.symm_apply_apply] using! hh

theorem qtmCell_local_table {C : Type} [Fintype C] [DecidableEq C]
    {m c : ℕ} (p : Fin m ↪ Fin c) (b : ℕ) (hm : 0 < m) (hb : 0 < b)
    (e : C → Reg b) (he : Function.Injective e)
    (U : Matrix (Fin m → C) (Fin m → C) ℂ)
    (hU : U ∈ unitaryGroup (Fin m → C) ℂ) :
    ∃ gs : List (ReflectionGate (c*b)), reflectionLegal gs ∧
      gs.length ≤ phi3PaddingBudget (m*b) ∧
      ∀ ψ : QState (Fin c → C),
        Run 1 (reflectionCompile gs) (finiteBasisPadState (qtmBlockBasisCode c b e) ψ) =
          finiteBasisPadState (qtmBlockBasisCode c b e) (ApplyGate (qtmCellGate p U) ψ) := by
  let w := qtmBlockWires p b
  let code := qtmBlockBasisCode m b e
  have hcode := qtmBlockBasisCode_injective m b e he
  have hV := finiteBasisPadUnitary_unitary code hcode U hU
  obtain ⟨ts,hts,hlen,_,_,hr⟩ := known_unitary_no_work_actual_local_synthesis (m*b)
    (Nat.mul_pos hm hb) (finiteBasisPadUnitary code U) hV
  let gs := ts.map (knownWireGateMap w)
  have hket (r : Fin c → C) :
      Run 1 (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket (qtmBlockBasisCode c b e r)) =
        finiteBasisPadState (qtmBlockBasisCode c b e) (ApplyGate (qtmCellGate p U) (Qatlib.Foundations.PureStateMath.Ket r)) := by
    let rLocal : Fin m → C := fun i => r (p i)
    have hinit : qtmWireContextEmbed w (qtmBlockBasisCode c b e r)
        (finiteBasisPadState code (Qatlib.Foundations.PureStateMath.Ket rLocal)) = Qatlib.Foundations.PureStateMath.Ket (qtmBlockBasisCode c b e r) := by
      rw [finiteBasisPadState_ket, qtmWireContextEmbed_ket]
      change Qatlib.Foundations.PureStateMath.Ket (qtmWireContextExtend (qtmBlockWires p b) (qtmBlockBasisCode c b e r)
        (qtmBlockBasisCode m b e rLocal)) = _
      rw [qtmBlock_context, qtmCellContextExtend_reconstruct p r r (fun _ _ => rfl)]
    have happly : finiteBasisPadUnitary code U *ᵥ finiteBasisPadState code (Qatlib.Foundations.PureStateMath.Ket rLocal) =
        finiteBasisPadState code (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket rLocal)) :=
      finiteBasisPadUnitary_apply code hcode U (Qatlib.Foundations.PureStateMath.Ket rLocal)
    rw [← hinit, qtmWireProgram_context w _ ts hts, hr, happly]
    change qtmWireContextEmbed (qtmBlockWires p b) (qtmBlockBasisCode c b e r)
      (finiteBasisPadState (qtmBlockBasisCode m b e) (ApplyGate U (Qatlib.Foundations.PureStateMath.Ket rLocal))) = _
    rw [qtmBlock_context_frame, qtmCellGate_ket, finiteBasisPadState_sum]
    simp only [finiteBasisPadState_smul, finiteBasisPadState_ket]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    simp [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, rLocal]
  refine ⟨gs, knownWireMapList_legal w ts hts, by simpa [gs] using! hlen, ?_⟩
  intro ψ
  rw [state_ket_expansion ψ]
  simp only [finiteBasisPadState_sum, finiteBasisPadState_smul, finiteBasisPadState_ket,
    run_reflectionCompile, ApplyGate, Matrix.mulVec_sum, Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  simpa only [run_reflectionCompile, ApplyGate] using! hket r

end Qatlib.Concepts.QtmSimulation.Phi3Compilation
