/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Foundations.PureStateMath.Qubit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.CircuitImpl.ReflectionCompile
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

def reflectionSplit (n : ℕ) : Reg (n+(n-1)) ≃ Reg n × Reg (n-1) :=
  regAppendEquiv n (n-1)

noncomputable def reflectionEmbed (n : ℕ) (ψ : QState (Reg n)) :
    QState (Reg (n+(n-1))) := fun z =>
  if (reflectionSplit n z).2 = (fun _ => false) then ψ (reflectionSplit n z).1 else 0

noncomputable def reflectionLift (n : ℕ) (U : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Reg (n+(n-1))) (Reg (n+(n-1))) ℂ :=
  relabelGate (reflectionSplit n).symm (TensorGate U 1)

abbrev reflectionDataWire (n : ℕ) (i : Fin n) : Fin (n+(n-1)) := Fin.castAdd (n-1) i

abbrev reflectionWorkWire (n : ℕ) (i : Fin (n-1)) : Fin (n+(n-1)) := Fin.natAdd n i

@[simp] theorem reflectionJoin_data (n : ℕ) (x : Reg n) (w : Reg (n-1)) (i : Fin n) :
    (reflectionSplit n).symm (x,w) (reflectionDataWire n i) = x i := by
  have h := congrArg (fun p : Reg n × Reg (n-1) => p.1 i)
    ((reflectionSplit n).apply_symm_apply (x,w))
  exact h

@[simp] theorem reflectionJoin_work (n : ℕ) (x : Reg n) (w : Reg (n-1)) (i : Fin (n-1)) :
    (reflectionSplit n).symm (x,w) (reflectionWorkWire n i) = w i := by
  have h := congrArg (fun p : Reg n × Reg (n-1) => p.2 i)
    ((reflectionSplit n).apply_symm_apply (x,w))
  exact h

noncomputable def localAndStage (n : ℕ) (i : Fin (n-1)) :
    List (ReflectionGate (n+(n-1))) :=
  if h : i.val = 0 then
    toffoliLocalSteps (reflectionDataWire n ⟨0, by omega⟩)
      (reflectionDataWire n ⟨1, by omega⟩) (reflectionWorkWire n i)
  else
    toffoliLocalSteps (reflectionDataWire n ⟨i.val+1, by omega⟩)
      (reflectionWorkWire n ⟨i.val-1, by omega⟩) (reflectionWorkWire n i)

noncomputable def localAndPrefix (n : ℕ) : ℕ → List (ReflectionGate (n+(n-1)))
  | 0 => []
  | m+1 => localAndPrefix n m ++ if h : m < n-1 then localAndStage n ⟨m,h⟩ else []

noncomputable def localAndSteps (n : ℕ) : List (ReflectionGate (n+(n-1))) :=
  localAndPrefix n (n-1)

noncomputable def localAndPrefixBasis (n : ℕ) (x : Reg n) (m : ℕ) : Reg (n+(n-1)) :=
  (reflectionSplit n).symm (x, fun i =>
    if i.val < m then decide (∀ j : Fin n, j.val ≤ i.val+1 → x j = true) else false)

theorem localAndStage_length (n : ℕ) (i : Fin (n-1)) :
    (localAndStage n i).length = 15 := by
  unfold localAndStage
  split <;> exact toffoliLocalSteps_length _ _ _

theorem localAndPrefix_length (n m : ℕ) (hm : m ≤ n-1) :
    (localAndPrefix n m).length = 15*m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h : m < n-1 := by omega
    simp only [localAndPrefix, dif_pos h, List.length_append, localAndStage_length,
      ih (by omega)]
    omega

theorem localAndStage_legal (n : ℕ) (i : Fin (n-1)) : reflectionLegal (localAndStage n i) := by
  unfold localAndStage
  split
  · apply toffoliLocalSteps_legal
    all_goals
      intro h
      have hv := congrArg Fin.val h
      simp only [reflectionDataWire, reflectionWorkWire, Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
  · apply toffoliLocalSteps_legal
    all_goals
      intro h
      have hv := congrArg Fin.val h
      simp [reflectionDataWire, reflectionWorkWire] at hv
      omega

theorem localAndPrefix_legal (n m : ℕ) : reflectionLegal (localAndPrefix n m) := by
  induction m with
  | zero => intro g hg; simp [localAndPrefix] at hg
  | succ m ih =>
    intro g hg
    simp only [localAndPrefix, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ih g hg
    · split at hg
      · exact localAndStage_legal n _ g hg
      · simp at hg

private theorem prefixAnd_zero (n : ℕ) (hn : 2 ≤ n) (x : Reg n) :
    (x ⟨0, by omega⟩ && x ⟨1, by omega⟩) =
      decide (∀ j : Fin n, j.val ≤ 1 → x j = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h0,h1⟩ j hj
    have : j = ⟨0, by omega⟩ ∨ j = ⟨1, by omega⟩ := by
      by_cases h : j.val = 0
      · left; exact Fin.ext h
      · right; apply Fin.ext; change j.val = 1; omega
    rcases this with h | h
    · rw [h]; exact h0
    · rw [h]; exact h1
  · intro h
    exact ⟨h _ (by simp), h _ (by simp)⟩

private theorem prefixAnd_succ (n m : ℕ) (hm : m+1 < n) (x : Reg n) :
    (x ⟨m+1,hm⟩ && decide (∀ j : Fin n, j.val ≤ m → x j = true)) =
      decide (∀ j : Fin n, j.val ≤ m+1 → x j = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hx,h⟩ j hj
    by_cases hjm : j.val ≤ m
    · exact h j hjm
    · have he : j = ⟨m+1,hm⟩ := Fin.ext (by change j.val = m+1; omega)
      rw [he]; exact hx
  · intro h
    exact ⟨h _ (by simp), fun j hj => h j (by omega)⟩

private theorem localAndStage_action (n : ℕ) (i : Fin (n-1)) (x : Reg n) :
    Run (1 : Matrix (Reg (n+(n-1))) (Reg (n+(n-1))) ℂ)
      (reflectionCompile (localAndStage n i)) (Qatlib.Foundations.PureStateMath.Ket (localAndPrefixBasis n x i.val)) =
      Qatlib.Foundations.PureStateMath.Ket (localAndPrefixBasis n x (i.val+1)) := by
  unfold localAndStage
  split
  · rename_i hi
    have hn : 2 ≤ n := by omega
    rw [(local_toffoli_fifteen_exact _ _ _ _
      (by intro h; have := congrArg Fin.val h; simp [reflectionDataWire] at this)
      (by intro h; have := congrArg Fin.val h; simp only [reflectionDataWire, reflectionWorkWire, Fin.val_castAdd, Fin.val_natAdd] at this; omega)
      (by intro h; have := congrArg Fin.val h; simp only [reflectionDataWire, reflectionWorkWire, Fin.val_castAdd, Fin.val_natAdd] at this; omega)).2.2]
    congr 1
    funext k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · have hne : reflectionDataWire n j ≠ reflectionWorkWire n i := by
        intro h; have := congrArg Fin.val h; simp only [reflectionDataWire, reflectionWorkWire, Fin.val_castAdd, Fin.val_natAdd] at this; omega
      rw [Function.update_of_ne hne]
      simp [localAndPrefixBasis, reflectionDataWire]
    · by_cases hj : j = i
      · subst j
        rw [Function.update_self]
        simp only [localAndPrefixBasis, reflectionJoin_work, reflectionJoin_data]
        simp only [lt_self_iff_false, if_false, Bool.false_xor, hi]
        rw [if_pos (by omega), prefixAnd_zero n hn x]
      · have hne : reflectionWorkWire n j ≠ reflectionWorkWire n i := by
          intro h
          exact hj (Fin.ext (by have := congrArg Fin.val h; simp [reflectionWorkWire] at this; omega))
        rw [Function.update_of_ne hne]
        simp only [localAndPrefixBasis, reflectionJoin_work]
        have hjv : j.val ≠ i.val := fun h => hj (Fin.ext h)
        have hlt : (j.val < i.val) = (j.val < i.val+1) := propext (by omega)
        simp only [hlt]
  · rename_i hi
    have hm : i.val+1 < n := by omega
    rw [(local_toffoli_fifteen_exact _ _ _ _
      (by intro h; have := congrArg Fin.val h; simp only [reflectionDataWire, reflectionWorkWire, Fin.val_castAdd, Fin.val_natAdd] at this; omega)
      (by intro h; have := congrArg Fin.val h; simp only [reflectionDataWire, reflectionWorkWire, Fin.val_castAdd, Fin.val_natAdd] at this; omega)
      (by intro h; have := congrArg Fin.val h; simp only [reflectionWorkWire, Fin.val_natAdd] at this; omega)).2.2]
    congr 1
    funext k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · have hne : reflectionDataWire n j ≠ reflectionWorkWire n i := by
        intro h; have := congrArg Fin.val h; simp only [reflectionDataWire, reflectionWorkWire, Fin.val_castAdd, Fin.val_natAdd] at this; omega
      rw [Function.update_of_ne hne]
      simp [localAndPrefixBasis, reflectionDataWire]
    · by_cases hj : j = i
      · subst j
        rw [Function.update_self]
        simp only [localAndPrefixBasis, reflectionJoin_work, reflectionJoin_data]
        rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), Bool.false_xor]
        have hval : i.val-1+1 = i.val := by omega
        rw [hval, prefixAnd_succ n i.val hm x]
      · have hne : reflectionWorkWire n j ≠ reflectionWorkWire n i := by
          intro h
          exact hj (Fin.ext (by have := congrArg Fin.val h; simp [reflectionWorkWire] at this; omega))
        rw [Function.update_of_ne hne]
        simp only [localAndPrefixBasis, reflectionJoin_work]
        have hjv : j.val ≠ i.val := fun h => hj (Fin.ext h)
        have hlt : (j.val < i.val) = (j.val < i.val+1) := propext (by omega)
        simp only [hlt]

theorem localAndPrefix_action (n m : ℕ) (hm : m ≤ n-1) (x : Reg n) :
    Run (1 : Matrix (Reg (n+(n-1))) (Reg (n+(n-1))) ℂ)
      (reflectionCompile (localAndPrefix n m))
      (Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm (x,fun _ => false))) =
      Qatlib.Foundations.PureStateMath.Ket (localAndPrefixBasis n x m) := by
  induction m with
  | zero => simp [localAndPrefix, reflectionCompile, localAndPrefixBasis]
  | succ m ih =>
    have h : m < n-1 := by omega
    rw [localAndPrefix, dif_pos h, reflectionCompile_append, run_append, ih (by omega)]
    exact localAndStage_action n ⟨m,h⟩ x

theorem local_and_clean_prefix_action (n : ℕ) (_hn : 2 ≤ n) :
    (localAndSteps n).length = 15*(n-1) ∧ ∀ x : Reg n,
      Run (1 : Matrix (Reg (n+(n-1))) (Reg (n+(n-1))) ℂ)
        (reflectionCompile (localAndSteps n))
        (Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm (x,fun _ => false))) =
        Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm (x,fun i =>
          decide (∀ j : Fin n, j.val ≤ i.val+1 → x j=true))) := by
  refine ⟨localAndPrefix_length n (n-1) le_rfl, ?_⟩
  intro x
  rw [localAndSteps, localAndPrefix_action n (n-1) le_rfl x]
  congr 1
  simp [localAndPrefixBasis]

noncomputable def reflectionFlipPrefix (n : ℕ) : ℕ → List (ReflectionGate (n+(n-1)))
  | 0 => []
  | m+1 => reflectionFlipPrefix n m ++ if h : m < n then
      [Sum.inl (reflectionDataWire n ⟨m,h⟩,PauliX)] else []

noncomputable def reflectionDataFlips (n : ℕ) := reflectionFlipPrefix n n

noncomputable def localZeroReflectionSteps (n : ℕ) : List (ReflectionGate (n+(n-1))) :=
  if h0 : n = 0 then [] else if h1 : n = 1 then
    [.inl (reflectionDataWire n ⟨0,by omega⟩,Rz Real.pi)] else
    reflectionDataFlips n ++ localAndSteps n ++
    [.inl (reflectionWorkWire n ⟨n-2,by omega⟩,Rz Real.pi)] ++
    reflectionAdjoint (localAndSteps n) ++ reflectionDataFlips n ++
    [.inl (reflectionWorkWire n ⟨0,by omega⟩,PauliX),
     .inl (reflectionWorkWire n ⟨0,by omega⟩,Rz Real.pi),
     .inl (reflectionWorkWire n ⟨0,by omega⟩,PauliX)]

def localReflectionCost (n : ℕ) : ℕ :=
  if n = 0 then 0 else if n = 1 then 1 else 2*n+30*(n-1)+4

theorem reflectionFlipPrefix_length (n m : ℕ) (hm : m ≤ n) :
    (reflectionFlipPrefix n m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [reflectionFlipPrefix, dif_pos (show m<n by omega), List.length_append,
      List.length_cons, List.length_nil, ih (by omega)]

theorem reflectionFlipPrefix_legal (n m : ℕ) : reflectionLegal (reflectionFlipPrefix n m) := by
  induction m with
  | zero => intro g hg; simp [reflectionFlipPrefix] at hg
  | succ m ih =>
    rw [reflectionFlipPrefix, reflectionLegal_append]
    refine ⟨ih,?_⟩
    split
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst g
      exact pauliX_unitary
    · intro g hg; simp at hg

theorem localZeroReflectionSteps_legal (n : ℕ) : reflectionLegal (localZeroReflectionSteps n) := by
  unfold localZeroReflectionSteps
  split
  · intro g hg; simp at hg
  · split
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst g
      exact rz_unitary _
    · simp only [reflectionLegal_append]
      refine ⟨⟨⟨⟨⟨reflectionFlipPrefix_legal n n,localAndPrefix_legal n (n-1)⟩,
        ?_⟩,reflectionAdjoint_legal _ (localAndPrefix_legal n (n-1))⟩,
        reflectionFlipPrefix_legal n n⟩,?_⟩
      · intro g hg
        simp only [List.mem_singleton] at hg
        subst g
        exact rz_unitary _
      · intro g hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl
        · exact pauliX_unitary
        · exact rz_unitary _
        · exact pauliX_unitary

theorem localZeroReflectionSteps_length (n : ℕ) :
    (localZeroReflectionSteps n).length = localReflectionCost n := by
  unfold localZeroReflectionSteps localReflectionCost
  split
  · rfl
  · split
    · rfl
    · simp only [List.length_append, List.length_cons, List.length_nil,
        reflectionAdjoint_length, reflectionDataFlips,
        reflectionFlipPrefix_length n n le_rfl, localAndSteps,
        localAndPrefix_length n (n-1) le_rfl]
      omega

theorem reflectionEmbed_tensor (n : ℕ) (ψ : QState (Reg n)) :
    reflectionEmbed n ψ = relabelState (reflectionSplit n).symm
      (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin (n-1) => false))) := by
  funext z
  simp only [reflectionEmbed, relabelState, Function.comp_apply, TensorState,
      Qatlib.Foundations.PureStateMath.Ket, Equiv.symm_symm]
  split <;> simp_all

@[simp] theorem reflectionEmbed_ket (n : ℕ) (x : Reg n) :
    reflectionEmbed n (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm (x,fun _ => false)) := by
  rw [reflectionEmbed_tensor, tensorState_ket_ket]
  funext z
  simp only [relabelState, Function.comp_apply, Qatlib.Foundations.PureStateMath.Ket,
      Equiv.symm_symm]
  simp only [show ((reflectionSplit n) z = (x,fun _ => false)) =
    (z = (reflectionSplit n).symm (x,fun _ => false)) from
      propext (reflectionSplit n).apply_eq_iff_eq_symm_apply]

@[simp] theorem reflectionEmbed_smul (n : ℕ) (c : ℂ) (ψ : QState (Reg n)) :
    reflectionEmbed n (c • ψ) = c • reflectionEmbed n ψ := by
  funext z
  simp only [reflectionEmbed, Pi.smul_apply, smul_eq_mul]
  split <;> simp

theorem reflectionEmbed_sum {J : Type*} [Fintype J] (n : ℕ) (ψ : J → QState (Reg n)) :
    reflectionEmbed n (∑ j, ψ j) = ∑ j, reflectionEmbed n (ψ j) := by
  funext z
  simp only [reflectionEmbed, Finset.sum_apply]
  split <;> simp

theorem reflectionLift_embed (n : ℕ) (U : Matrix (Reg n) (Reg n) ℂ) (ψ : QState (Reg n)) :
    ApplyGate (reflectionLift n U) (reflectionEmbed n ψ) =
      reflectionEmbed n (ApplyGate U ψ) := by
  rw [reflectionLift, reflectionEmbed_tensor, applyGate_relabelGate, applyGate_tensorGate,
    applyGate_one, ← reflectionEmbed_tensor]

theorem reflectionEmbed_expansion (n : ℕ) (ψ : QState (Reg n)) :
    reflectionEmbed n ψ = ∑ x : Reg n,
      ψ x • Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm (x,fun _ => false)) := by
  conv_lhs => rw [state_ket_expansion ψ]
  rw [reflectionEmbed_sum]
  simp only [reflectionEmbed_smul, reflectionEmbed_ket]

theorem localAndSteps_uncompute (n : ℕ) (hn : 2 ≤ n) (x : Reg n) :
    Run (1 : Matrix (Reg (n+(n-1))) (Reg (n+(n-1))) ℂ)
      (reflectionCompile (reflectionAdjoint (localAndSteps n)))
      (Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm (x,fun i =>
        decide (∀ j : Fin n, j.val ≤ i.val+1 → x j = true)))) =
      Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm (x,fun _ => false)) := by
  rw [← (local_and_clean_prefix_action n hn).2 x, run_reflectionCompile,
    run_reflectionCompile, reflectionAdjoint_matrix (localAndSteps n) (localAndPrefix_legal n (n-1))]
  rw [ApplyGate, ApplyGate, Matrix.mulVec_mulVec]
  have hu := reflectionProgramMatrix_unitary (localAndSteps n) (localAndPrefix_legal n (n-1))
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
  rw [hu, Matrix.one_mulVec]

private theorem wireGate_diagonal_ket (n : ℕ) (w : Fin n) (d : Bool → ℂ) (x : Reg n) :
    ApplyGate (wireGate n w (Matrix.diagonal d)) (Qatlib.Foundations.PureStateMath.Ket x) = d (x w) • Qatlib.Foundations.PureStateMath.Ket x := by
  rw [applyGate_wireGate_ket]
  have hup : Function.update x w (x w) = x := Function.update_eq_self w x
  cases hx : x w <;> simp only [Matrix.diagonal_apply, if_true, if_false,
    Bool.false_eq_true, Bool.true_eq_false, zero_smul, add_zero, zero_add]
  all_goals rw [hx] at hup; rw [hup]

private theorem wireGate_X_ket (n : ℕ) (w : Fin n) (x : Reg n) :
    ApplyGate (wireGate n w PauliX) (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x w (!(x w))) := by
  rw [applyGate_wireGate_ket]
  cases hx : x w <;> simp [PauliX, permMatrix]

private theorem rz_pi_eq : Rz Real.pi = PauliZ := by
  ext a b
  simp only [Rz, PauliZ, Matrix.diagonal_apply, Complex.exp_pi_mul_I]

private theorem wireGate_Z_ket (n : ℕ) (w : Fin n) (x : Reg n) :
    ApplyGate (wireGate n w (Rz Real.pi)) (Qatlib.Foundations.PureStateMath.Ket x) =
      (if x w then (-1 : ℂ) else 1) • Qatlib.Foundations.PureStateMath.Ket x := by
  rw [rz_pi_eq]
  exact wireGate_diagonal_ket n w _ x

private theorem flipPrefix_update (n m : ℕ) (hm : m<n) (x : Reg n) (w : Reg (n-1)) :
    Function.update ((reflectionSplit n).symm
      ((fun j => if j.val < m then !(x j) else x j),w))
      (reflectionDataWire n ⟨m,hm⟩) (!(x ⟨m,hm⟩)) =
    (reflectionSplit n).symm ((fun j => if j.val < m+1 then !(x j) else x j),w) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · by_cases hj : j = ⟨m,hm⟩
    · subst j
      rw [Function.update_self]
      rw [reflectionJoin_data]
      simp only [Nat.lt_succ_self, if_true]
    · have hne : reflectionDataWire n j ≠ reflectionDataWire n ⟨m,hm⟩ := by
        intro h
        exact hj (Fin.ext (by have := congrArg Fin.val h; simpa using this))
      rw [Function.update_of_ne hne]
      simp only [reflectionJoin_data]
      have hjv : j.val ≠ m := fun h => hj (Fin.ext h)
      have he : (j.val < m) = (j.val < m+1) := propext (by omega)
      simp only [he]
  · have hne : reflectionWorkWire n j ≠ reflectionDataWire n ⟨m,hm⟩ := by
      intro h; have := congrArg Fin.val h; simp only [reflectionDataWire, reflectionWorkWire, Fin.val_castAdd, Fin.val_natAdd] at this; omega
    rw [Function.update_of_ne hne]
    simp only [reflectionJoin_work]

private theorem reflectionFlipPrefix_action (n m : ℕ) (hm : m ≤ n) (x : Reg n) (w : Reg (n-1)) :
    Run (1 : Matrix (Reg (n+(n-1))) (Reg (n+(n-1))) ℂ)
      (reflectionCompile (reflectionFlipPrefix n m)) (Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm (x,w))) =
      Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm ((fun j => if j.val < m then !(x j) else x j),w)) := by
  induction m with
  | zero => simp [reflectionFlipPrefix, reflectionCompile]
  | succ m ih =>
    have h : m<n := by omega
    rw [reflectionFlipPrefix, dif_pos h, reflectionCompile_append, run_append, ih (by omega)]
    simp only [reflectionCompile, List.map_cons, List.map_nil, Run, reflectionGateMatrix]
    rw [wireGate_X_ket]
    simp only [reflectionJoin_data, lt_self_iff_false, if_false]
    rw [flipPrefix_update n m h x w]

theorem reflectionDataFlips_action (n : ℕ) (x : Reg n) (w : Reg (n-1)) :
    Run (1 : Matrix (Reg (n+(n-1))) (Reg (n+(n-1))) ℂ)
      (reflectionCompile (reflectionDataFlips n)) (Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm (x,w))) =
      Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm ((fun j => !(x j)),w)) := by
  rw [reflectionDataFlips, reflectionFlipPrefix_action n n le_rfl]
  simp

private theorem reflectionSignCorrection (n : ℕ) (i : Fin (n-1)) (x : Reg n) :
    Run (1 : Matrix (Reg (n+(n-1))) (Reg (n+(n-1))) ℂ)
      (reflectionCompile [.inl (reflectionWorkWire n i,PauliX),
        .inl (reflectionWorkWire n i,Rz Real.pi),
        .inl (reflectionWorkWire n i,PauliX)])
      (Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm (x,fun _ => false))) =
    (-1 : ℂ) • Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm (x,fun _ => false)) := by
  simp only [reflectionCompile, List.map_cons, List.map_nil, Run, reflectionGateMatrix]
  rw [wireGate_X_ket, wireGate_Z_ket]
  simp only [Function.update_self, reflectionJoin_work, Bool.not_false, if_true]
  rw [reflectionApplyGate_smul, wireGate_X_ket]
  simp only [Function.update_self, Bool.not_true, Function.update_idem]
  have he : Function.update ((reflectionSplit n).symm (x,fun _ => false))
      (reflectionWorkWire n i) false = (reflectionSplit n).symm (x,fun _ => false) := by
    simpa only [reflectionJoin_work] using
      (Function.update_eq_self (reflectionWorkWire n i) ((reflectionSplit n).symm (x,fun _ => false)))
  rw [he]

private theorem andLast_flag_zero (n : ℕ) (hn : 2 ≤ n) (x : Reg n) :
    decide (∀ j : Fin n, j.val ≤ n-2+1 → Bool.not (x j) = true) =
      decide (x = (fun _ => false)) := by
  congr 1
  apply propext
  constructor
  · intro h
    funext j
    have := h j (by omega)
    simpa using this
  · intro h j _
    simp [h]

private theorem zeroReflection_basis_large (n : ℕ) (hn : 2 ≤ n) (x : Reg n) :
    Run (1 : Matrix (Reg (n+(n-1))) (Reg (n+(n-1))) ℂ)
      (reflectionCompile (localZeroReflectionSteps n))
      (Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm (x,fun _ => false))) =
      (if x = (fun _ => false) then (1 : ℂ) else -1) •
        Qatlib.Foundations.PureStateMath.Ket ((reflectionSplit n).symm (x,fun _ => false)) := by
  rw [localZeroReflectionSteps, dif_neg (by omega), dif_neg (by omega)]
  simp only [reflectionCompile_append, run_append]
  rw [reflectionDataFlips_action, (local_and_clean_prefix_action n hn).2]
  have hphase : ∀ z : Reg (n+(n-1)),
      Run (1 : Matrix (Reg (n+(n-1))) (Reg (n+(n-1))) ℂ)
        (reflectionCompile [.inl (reflectionWorkWire n ⟨n-2,by omega⟩,Rz Real.pi)])
        (Qatlib.Foundations.PureStateMath.Ket z) = (if z (reflectionWorkWire n ⟨n-2,by omega⟩) then (-1 : ℂ) else 1) • Qatlib.Foundations.PureStateMath.Ket z := by
    intro z
    exact wireGate_Z_ket _ _ z
  rw [hphase]
  simp only [reflectionJoin_work]
  rw [andLast_flag_zero n hn x]
  rw [run_reflectionCompile_smul, localAndSteps_uncompute n hn,
    run_reflectionCompile_smul, reflectionDataFlips_action]
  simp only [Bool.not_not]
  rw [run_reflectionCompile_smul, reflectionSignCorrection, smul_smul]
  simp only [decide_eq_true_eq]
  split_ifs <;> norm_num

private theorem zeroReflection_ket {I : Type*} [Fintype I] [DecidableEq I] (z x : I) :
    ApplyGate (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket z))) (Qatlib.Foundations.PureStateMath.Ket x) =
      (if x=z then (1 : ℂ) else -1) • Qatlib.Foundations.PureStateMath.Ket x := by
  rw [applyGate_reflectionAbout]
  change (2 : ℂ) •
      ((outerProduct (Qatlib.Foundations.PureStateMath.Ket z)) *ᵥ Qatlib.Foundations.PureStateMath.Ket x) - Qatlib.Foundations.PureStateMath.Ket x = _
  rw [outerProduct_mulVec, inner_ket_ket]
  by_cases h : x=z
  · subst x
    simp
    module
  · rw [if_neg (Ne.symm h), zero_smul, smul_zero, zero_sub, if_neg h]
    simp

private theorem zeroReflection_basis (n : ℕ) (x : Reg n) :
    Run (1 : Matrix (Reg (n+(n-1))) (Reg (n+(n-1))) ℂ)
      (reflectionCompile (localZeroReflectionSteps n)) (reflectionEmbed n (Qatlib.Foundations.PureStateMath.Ket x)) =
      reflectionEmbed n (ApplyGate (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin n => false))))
        (Qatlib.Foundations.PureStateMath.Ket x)) := by
  rw [reflectionEmbed_ket, zeroReflection_ket, reflectionEmbed_smul, reflectionEmbed_ket]
  by_cases h0 : n=0
  · subst n
    have hx : x = (fun _ => false) := Subsingleton.elim _ _
    simp [localZeroReflectionSteps, reflectionCompile, hx]
  · by_cases h1 : n=1
    · rw [localZeroReflectionSteps, dif_neg h0, dif_pos h1]
      simp only [reflectionCompile, List.map_cons, List.map_nil, Run, reflectionGateMatrix]
      rw [wireGate_Z_ket]
      simp only [reflectionJoin_data]
      have he : (x = fun _ => false) ↔ x ⟨0,by omega⟩ = false := by
        constructor
        · intro h; simp [h]
        · intro h
          funext j
          have hj : j = ⟨0,by omega⟩ := Fin.ext (by omega)
          rw [hj,h]
      cases hb : x ⟨0,by omega⟩ <;> simp [he,hb]
    · exact zeroReflection_basis_large n (by omega) x

theorem local_zero_reflection_clean_semantics_and_cost (n : ℕ) :
    reflectionLegal (localZeroReflectionSteps n) ∧
    localReflectionCost n = (if n=0 then 0 else if n=1 then 1 else 2*n+30*(n-1)+4) ∧
    (localZeroReflectionSteps n).length = localReflectionCost n ∧
    ∀ ψ : QState (Reg n),
      Run (1 : Matrix (Reg (n+(n-1))) (Reg (n+(n-1))) ℂ)
        (reflectionCompile (localZeroReflectionSteps n)) (reflectionEmbed n ψ) =
        reflectionEmbed n (ApplyGate (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin n => false)))) ψ) := by
  refine ⟨localZeroReflectionSteps_legal n,rfl,localZeroReflectionSteps_length n,?_⟩
  intro ψ
  conv_lhs => rw [state_ket_expansion ψ]
  rw [reflectionEmbed_sum, run_reflectionCompile_sum]
  simp only [reflectionEmbed_smul, run_reflectionCompile_smul, zeroReflection_basis]
  conv_rhs => arg 2; arg 2; rw [state_ket_expansion ψ]
  simp only [ApplyGate, Matrix.mulVec_sum, Matrix.mulVec_smul, reflectionEmbed_sum,
    reflectionEmbed_smul]

end Qatlib.Concepts.CircuitImpl.ReflectionCompile
