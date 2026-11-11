/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.ReflectionCompile.CleanZeroReflection
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownQubitControl

/-!
# Local synthesis of multiple-control qubit gates

This module constructs `multiKnownSteps`, a local gate list implementing a known qubit unitary
conditioned on all control bits. A chain of conjunctions computes the control flag into clean
work bits, applies the controlled qubit gate, and reverses the chain.

The construction is in the elementary gate framework of [BarencoEtAl1995], with explicit
legality, gate counts, and coherent action on the clean embedding `multiKnownEmbed`.

## Main statements

* `multiAnd_clean_prefix_action`: computes the conjunction prefixes into work bits.
* `multi_known_control_actual_local_table_and_cost`: proves exact implementation and resource
  counts.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

/-- Tests whether every bit of a control register is true. -/
def allControlTrue (n : ℕ) (x : Reg n) : Bool := (List.ofFn x).all id

/-- The matrix applying U to the target exactly when all n control bits are true, while
preserving the control register. -/
noncomputable def multiKnownGate (n : ℕ) (U : Matrix Bool Bool ℂ) :
    Matrix (Reg n × Bool) (Reg n × Bool) ℂ := fun p q =>
  if p.1 = q.1 then if allControlTrue n q.1 then U p.2 q.2
    else (1 : Matrix Bool Bool ℂ) p.2 q.2 else 0

/-- The synthesis cost: one gate for no controls and `30*(n-1)+6` gates for a positive number of
controls. -/
def multiKnownCost (n : ℕ) : ℕ := if n = 0 then 1 else 30*(n-1)+6

/-- The equivalence between a one-bit register and its Boolean value. -/
private def oneBitEquiv : Reg 1 ≃ Bool where
  toFun x := x 0
  invFun b := fun _ => b
  left_inv x := by funext i; have : i = 0 := Subsingleton.elim _ _; simp [this]
  right_inv _ := rfl

/-- Splits the physical register into n controls, one target bit, and n-1 work bits. -/
def multiKnownSplit (n : ℕ) :
    Reg (n+1+(n-1)) ≃ ((Reg n × Bool) × Reg (n-1)) :=
  (regAppendEquiv (n+1) (n-1)).trans
    (Equiv.prodCongr ((regAppendEquiv n 1).trans
      (Equiv.prodCongr (Equiv.refl _) oneBitEquiv)) (Equiv.refl _))

/-- Embeds a control-target state into the physical register with all work bits initialized to
false. -/
noncomputable def multiKnownEmbed (n : ℕ) (ψ : QState (Reg n × Bool)) :
    QState (Reg (n+1+(n-1))) :=
  relabelState (multiKnownSplit n).symm
    (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin (n-1) => false)))

/-- The physical wire occupied by the specified control bit. -/
abbrev multiKnownControlWire (n : ℕ) (i : Fin n) : Fin (n+1+(n-1)) :=
  ⟨i.val, by omega⟩
/-- The physical wire occupied by the target bit, immediately after the controls. -/
abbrev multiKnownTargetWire (n : ℕ) : Fin (n+1+(n-1)) := ⟨n, by omega⟩
/-- The physical wire occupied by the specified work bit, after the controls and target. -/
abbrev multiKnownWorkWire (n : ℕ) (i : Fin (n-1)) : Fin (n+1+(n-1)) :=
  ⟨n+1+i.val, by omega⟩

/-- Identifies the clean-state embedding and the control, target, and work coordinates of
`multiKnownSplit`. -/
theorem multi_known_control_clean_frame (n : ℕ) (ψ : QState (Reg n × Bool)) :
    multiKnownEmbed n ψ = relabelState (multiKnownSplit n).symm
      (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin (n-1) => false))) ∧
    (∀ x : Reg (n+1+(n-1)), (multiKnownSplit n x).1.1 =
      fun i : Fin n => x ⟨i.val, by omega⟩) ∧
    (∀ x : Reg (n+1+(n-1)), (multiKnownSplit n x).1.2 = x ⟨n, by omega⟩) ∧
    (∀ x : Reg (n+1+(n-1)), (multiKnownSplit n x).2 =
      fun i : Fin (n-1) => x ⟨n+1+i.val, by omega⟩) := by
  exact ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Joining the control, target, and work registers recovers each control bit at its designated
wire. -/
@[simp] theorem multiKnownJoin_control (n : ℕ) (x : Reg n) (b : Bool)
    (w : Reg (n-1)) (i : Fin n) :
    (multiKnownSplit n).symm ((x,b),w) (multiKnownControlWire n i) = x i :=
  congrArg (fun z => z.1.1 i) ((multiKnownSplit n).apply_symm_apply ((x,b),w))

/-- Joining the registers recovers the target bit at its designated wire. -/
@[simp] theorem multiKnownJoin_target (n : ℕ) (x : Reg n) (b : Bool)
    (w : Reg (n-1)) :
    (multiKnownSplit n).symm ((x,b),w) (multiKnownTargetWire n) = b :=
  congrArg (fun z => z.1.2) ((multiKnownSplit n).apply_symm_apply ((x,b),w))

/-- Joining the registers recovers each work bit at its designated wire. -/
@[simp] theorem multiKnownJoin_work (n : ℕ) (x : Reg n) (b : Bool)
    (w : Reg (n-1)) (i : Fin (n-1)) :
    (multiKnownSplit n).symm ((x,b),w) (multiKnownWorkWire n i) = w i :=
  congrArg (fun z => z.2 i) ((multiKnownSplit n).apply_symm_apply ((x,b),w))

/-- A local Toffoli gate list computing the next conjunction prefix into its work bit. -/
noncomputable def multiAndStage (n : ℕ) (i : Fin (n-1)) :
    List (ReflectionGate (n+1+(n-1))) :=
  if h : i.val = 0 then
    toffoliLocalSteps (multiKnownControlWire n ⟨0, by omega⟩)
      (multiKnownControlWire n ⟨1, by omega⟩) (multiKnownWorkWire n i)
  else
    toffoliLocalSteps (multiKnownControlWire n ⟨i.val+1, by omega⟩)
      (multiKnownWorkWire n ⟨i.val-1, by omega⟩) (multiKnownWorkWire n i)

/-- Concatenates the first m available conjunction stages, appending no further stages once the
work register is exhausted. -/
noncomputable def multiAndPrefix (n : ℕ) : ℕ → List (ReflectionGate (n+1+(n-1)))
  | 0 => []
  | m+1 => multiAndPrefix n m ++ if h : m < n-1 then multiAndStage n ⟨m,h⟩ else []

/-- The full conjunction chain with n-1 stages. -/
noncomputable def multiAndSteps (n : ℕ) : List (ReflectionGate (n+1+(n-1))) :=
  multiAndPrefix n (n-1)

/-- The basis register with the first m work bits holding the corresponding conjunction prefixes
and the remaining work bits false. -/
noncomputable def multiAndPrefixBasis (n : ℕ) (x : Reg n) (b : Bool) (m : ℕ) : Reg (n+1+(n-1)) :=
  (multiKnownSplit n).symm ((x,b), fun i =>
    if i.val < m then decide (∀ j : Fin n, j.val ≤ i.val+1 → x j = true) else false)

/-- Each conjunction stage contains exactly 15 local gates. -/
theorem multiAndStage_length (n : ℕ) (i : Fin (n-1)) :
    (multiAndStage n i).length = 15 := by
  unfold multiAndStage
  split <;> exact toffoliLocalSteps_length _ _ _

/-- A prefix of m conjunction stages contains exactly 15m gates when m ≤ n-1. -/
theorem multiAndPrefix_length (n m : ℕ) (hm : m ≤ n-1) :
    (multiAndPrefix n m).length = 15*m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h : m < n-1 := by omega
    simp only [multiAndPrefix, dif_pos h, List.length_append, multiAndStage_length,
      ih (by omega)]
    omega

/-- Every gate in a conjunction stage satisfies `reflectionLegal`. -/
theorem multiAndStage_legal (n : ℕ) (i : Fin (n-1)) : reflectionLegal (multiAndStage n i) := by
  unfold multiAndStage
  split
  · apply toffoliLocalSteps_legal
    all_goals
      intro h
      have hv := congrArg Fin.val h
      dsimp at hv
      omega
  · apply toffoliLocalSteps_legal
    all_goals
      intro h
      have hv := congrArg Fin.val h
      dsimp at hv
      omega

/-- Every conjunction prefix is a legal local gate list. -/
theorem multiAndPrefix_legal (n m : ℕ) : reflectionLegal (multiAndPrefix n m) := by
  induction m with
  | zero => intro g hg; simp [multiAndPrefix] at hg
  | succ m ih =>
    intro g hg
    simp only [multiAndPrefix, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ih g hg
    · split at hg
      · exact multiAndStage_legal n _ g hg
      · simp at hg

/-- The conjunction of the first two controls equals the test that both controls are true. -/
private theorem multiPrefixAnd_zero (n : ℕ) (hn : 2 ≤ n) (x : Reg n) :
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

/-- Conjoining the next control with a prefix conjunction gives the conjunction through that
control. -/
private theorem multiPrefixAnd_succ (n m : ℕ) (hm : m+1 < n) (x : Reg n) :
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

/-- A conjunction stage advances `multiAndPrefixBasis` from its current prefix length to the
next length. -/
private theorem multiAndStage_action (n : ℕ) (i : Fin (n-1)) (x : Reg n) (b : Bool) :
    Run (1 : Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ)
      (reflectionCompile (multiAndStage n i)) (Qatlib.Foundations.PureStateMath.Ket (multiAndPrefixBasis n x b i.val)) =
      Qatlib.Foundations.PureStateMath.Ket (multiAndPrefixBasis n x b (i.val+1)) := by
  unfold multiAndStage
  split
  · rename_i hi
    have hn : 2 ≤ n := by omega
    rw [(local_toffoli_fifteen_exact _ _ _ _
      (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
      (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
      (by intro h; have := congrArg Fin.val h; dsimp at this; omega)).2.2]
    congr 1
    funext k
    have hk : k.val < n ∨ k.val = n ∨ n+1 ≤ k.val := by omega
    rcases hk with hk | hk | hk
    · let j : Fin n := ⟨k.val,hk⟩
      have he : k = multiKnownControlWire n j := Fin.ext rfl
      rw [he]
      have hne : multiKnownControlWire n j ≠ multiKnownWorkWire n i := by
        intro h; have := congrArg Fin.val h; dsimp at this; omega
      rw [Function.update_of_ne hne]
      simp only [multiAndPrefixBasis, multiKnownJoin_control]
    · have he : k = multiKnownTargetWire n := Fin.ext hk
      rw [he]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; dsimp at this; omega)]
      simp only [multiAndPrefixBasis, multiKnownJoin_target]
    · let j : Fin (n-1) := ⟨k.val-(n+1),by omega⟩
      have he : k = multiKnownWorkWire n j := Fin.ext (by dsimp [j]; omega)
      rw [he]
      by_cases hj : j = i
      · rw [hj, Function.update_self]
        simp only [multiAndPrefixBasis, multiKnownJoin_work, multiKnownJoin_control]
        simp only [lt_self_iff_false, if_false, Bool.false_xor, hi]
        rw [if_pos (by omega), multiPrefixAnd_zero n hn x]
      · have hne : multiKnownWorkWire n j ≠ multiKnownWorkWire n i := by
          intro h
          exact hj (Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
        rw [Function.update_of_ne hne]
        simp only [multiAndPrefixBasis, multiKnownJoin_work]
        have hjv : j.val ≠ i.val := fun h => hj (Fin.ext h)
        have hlt : (j.val < i.val) = (j.val < i.val+1) := propext (by omega)
        simp only [hlt]
  · rename_i hi
    have hm : i.val+1 < n := by omega
    rw [(local_toffoli_fifteen_exact _ _ _ _
      (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
      (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
      (by intro h; have := congrArg Fin.val h; dsimp at this; omega)).2.2]
    congr 1
    funext k
    have hk : k.val < n ∨ k.val = n ∨ n+1 ≤ k.val := by omega
    rcases hk with hk | hk | hk
    · let j : Fin n := ⟨k.val,hk⟩
      have he : k = multiKnownControlWire n j := Fin.ext rfl
      rw [he]
      have hne : multiKnownControlWire n j ≠ multiKnownWorkWire n i := by
        intro h; have := congrArg Fin.val h; dsimp at this; omega
      rw [Function.update_of_ne hne]
      simp only [multiAndPrefixBasis, multiKnownJoin_control]
    · have he : k = multiKnownTargetWire n := Fin.ext hk
      rw [he]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; dsimp at this; omega)]
      simp only [multiAndPrefixBasis, multiKnownJoin_target]
    · let j : Fin (n-1) := ⟨k.val-(n+1),by omega⟩
      have he : k = multiKnownWorkWire n j := Fin.ext (by dsimp [j]; omega)
      rw [he]
      by_cases hj : j = i
      · rw [hj, Function.update_self]
        simp only [multiAndPrefixBasis, multiKnownJoin_work, multiKnownJoin_control]
        rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), Bool.false_xor]
        have hval : i.val-1+1 = i.val := by omega
        rw [hval, multiPrefixAnd_succ n i.val hm x]
      · have hne : multiKnownWorkWire n j ≠ multiKnownWorkWire n i := by
          intro h
          exact hj (Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
        rw [Function.update_of_ne hne]
        simp only [multiAndPrefixBasis, multiKnownJoin_work]
        have hjv : j.val ≠ i.val := fun h => hj (Fin.ext h)
        have hlt : (j.val < i.val) = (j.val < i.val+1) := propext (by omega)
        simp only [hlt]

/-- Running a conjunction prefix on a basis register with clean work bits produces
`multiAndPrefixBasis`. -/
theorem multiAndPrefix_action (n m : ℕ) (hm : m ≤ n-1) (x : Reg n) (b : Bool) :
    Run (1 : Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ)
      (reflectionCompile (multiAndPrefix n m))
      (Qatlib.Foundations.PureStateMath.Ket ((multiKnownSplit n).symm ((x,b),fun _ => false))) =
      Qatlib.Foundations.PureStateMath.Ket (multiAndPrefixBasis n x b m) := by
  induction m with
  | zero => simp [multiAndPrefix, reflectionCompile, multiAndPrefixBasis]
  | succ m ih =>
    have h : m < n-1 := by omega
    rw [multiAndPrefix, dif_pos h, reflectionCompile_append, run_append, ih (by omega)]
    exact multiAndStage_action n ⟨m,h⟩ x b

/-- For n ≥ 2, the full conjunction chain has length 15(n-1) and writes every conjunction prefix
into its designated work bit. -/
theorem multiAnd_clean_prefix_action (n : ℕ) (_hn : 2 ≤ n) :
    (multiAndSteps n).length = 15*(n-1) ∧ ∀ (x : Reg n) (b : Bool),
      Run (1 : Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ)
        (reflectionCompile (multiAndSteps n))
        (Qatlib.Foundations.PureStateMath.Ket ((multiKnownSplit n).symm ((x,b),fun _ => false))) =
        Qatlib.Foundations.PureStateMath.Ket ((multiKnownSplit n).symm ((x,b),fun i =>
          decide (∀ j : Fin n, j.val ≤ i.val+1 → x j=true))) := by
  refine ⟨multiAndPrefix_length n (n-1) le_rfl, ?_⟩
  intro x b
  rw [multiAndSteps, multiAndPrefix_action n (n-1) le_rfl x b]
  congr 1
  simp [multiAndPrefixBasis]

/-- Superposes the two values of one selected wire with amplitudes from a qubit state, keeping
all other wires at their specified basis values. -/
noncomputable def multiWireState {N : ℕ} (t : Fin N) (x : Reg N) (φ : QState Bool) :
    QState (Reg N) := φ false • Qatlib.Foundations.PureStateMath.Ket (Function.update x t false) +
      φ true • Qatlib.Foundations.PureStateMath.Ket (Function.update x t true)

/-- Inserting the original wire's basis state into `multiWireState` recovers the original basis
register. -/
@[simp] theorem multiWireState_ket {N : ℕ} (t : Fin N) (x : Reg N) :
    multiWireState t x (Qatlib.Foundations.PureStateMath.Ket (x t)) = Qatlib.Foundations.PureStateMath.Ket x := by
  have h := Function.update_eq_self t x
  cases hx : x t <;> simp only [multiWireState, Qatlib.Foundations.PureStateMath.Ket,
    if_true, if_false, Bool.false_eq_true, Bool.true_eq_false,
    zero_smul, one_smul, zero_add, add_zero]
  all_goals rw [hx] at h; rw [h]

/-- Scaling the qubit state scales the corresponding `multiWireState`. -/
@[simp] theorem multiWireState_smul {N : ℕ} (t : Fin N) (x : Reg N)
    (a : ℂ) (φ : QState Bool) :
    multiWireState t x (a • φ) = a • multiWireState t x φ := by
  simp [multiWireState, smul_add, smul_smul]

/-- Applying a gate at the selected wire acts on the qubit component of `multiWireState`. -/
theorem multiWireState_single {N : ℕ} (t : Fin N) (x : Reg N)
    (U : Matrix Bool Bool ℂ) (φ : QState Bool) :
    ApplyGate (wireGate N t U) (multiWireState t x φ) =
      multiWireState t x (ApplyGate U φ) := by
  simp only [multiWireState, reflectionApplyGate_add, reflectionApplyGate_smul,
    applyGate_wireGate_ket, Function.update_self, Function.update_idem]
  funext y
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ApplyGate, Matrix.mulVec,
    dotProduct, Fintype.sum_bool]
  ring

/-- A CNOT with a distinct control wire applies `PauliX` to the qubit component exactly when
that control bit is true. -/
theorem multiWireState_cnot {N : ℕ} (c t : Fin N) (hct : c ≠ t) (x : Reg N)
    (φ : QState Bool) :
    ApplyGate (cnotGate N c t) (multiWireState t x φ) =
      multiWireState t x (ApplyGate (if x c then PauliX else 1) φ) := by
  simp only [multiWireState, reflectionApplyGate_add, reflectionApplyGate_smul,
    applyGate_cnotGate_ket N c t hct, Function.update_self,
    Function.update_of_ne hct, Function.update_idem]
  cases hx : x c <;> funext y <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, PauliX, permMatrix,
      Matrix.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  all_goals ring

/-- A diagonal gate on one wire multiplies a basis register by the diagonal entry selected by
that bit. -/
private theorem multiWire_diagonal_ket (N : ℕ) (w : Fin N) (d : Bool → ℂ) (x : Reg N) :
    ApplyGate (wireGate N w (Matrix.diagonal d)) (Qatlib.Foundations.PureStateMath.Ket x) = d (x w) • Qatlib.Foundations.PureStateMath.Ket x := by
  rw [applyGate_wireGate_ket]
  have hup : Function.update x w (x w) = x := Function.update_eq_self w x
  cases hx : x w <;> simp only [Matrix.diagonal_apply, if_true, if_false,
    Bool.false_eq_true, Bool.true_eq_false, zero_smul, add_zero, zero_add]
  all_goals rw [hx] at hup; rw [hup]

/-- A diagonal gate on a distinct control wire scales `multiWireState` by the entry selected by
the fixed control bit. -/
theorem multiWireState_phase {N : ℕ} (c t : Fin N) (hct : c ≠ t) (x : Reg N)
    (d : Bool → ℂ) (φ : QState Bool) :
    ApplyGate (wireGate N c (Matrix.diagonal d)) (multiWireState t x φ) =
      d (x c) • multiWireState t x φ := by
  simp only [multiWireState, reflectionApplyGate_add, reflectionApplyGate_smul,
    multiWire_diagonal_ket, Function.update_of_ne hct, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> ring

/-- The local gate list for applying a known Euler-parameterized qubit matrix under a single
control. -/
noncomputable def multiKnownPairSteps {N : ℕ} (c t : Fin N) (p : KnownQubitAngles) :
    List (ReflectionGate N) :=
  [.inl (t,knownQubitUnitary (knownControlC p)), .inr (c,t),
   .inl (t,knownQubitUnitary (knownControlB p)), .inr (c,t),
   .inl (t,knownQubitUnitary (knownControlA p)),
   .inl (c,knownQubitUnitary (knownControlE p))]

/-- The single-control gate list is legal when the control and target wires are distinct. -/
theorem multiKnownPairSteps_legal {N : ℕ} (c t : Fin N) (hct : c ≠ t)
    (p : KnownQubitAngles) : reflectionLegal (multiKnownPairSteps c t p) := by
  intro g hg
  simp only [multiKnownPairSteps, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact knownQubitUnitary_unitary _ | exact hct

/-- The single-control gate list applies the known qubit unitary to the target component exactly
when the fixed control bit is true. -/
theorem multiKnownPairSteps_action {N : ℕ} (c t : Fin N) (hct : c ≠ t)
    (p : KnownQubitAngles) (x : Reg N) (φ : QState Bool) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (multiKnownPairSteps c t p))
      (multiWireState t x φ) =
      multiWireState t x (ApplyGate (if x c then knownQubitUnitary p else 1) φ) := by
  simp only [multiKnownPairSteps, reflectionCompile, List.map_cons, List.map_nil,
    run_gate, run_nil, reflectionGateMatrix]
  rw [multiWireState_single, multiWireState_cnot c t hct,
    multiWireState_single, multiWireState_cnot c t hct, multiWireState_single,
    (knownQubitControl_ABC_phase_factorization p).2.2]
  rw [show Rz p.delta = Matrix.diagonal (fun a =>
    if a then Complex.exp ((p.delta : ℂ) * Complex.I) else 1) from rfl,
    multiWireState_phase c t hct]
  cases hx : x c
  · simp only [Bool.false_eq_true, if_false, one_smul,
      ← applyGate_mul, Matrix.one_mul]
    rw [← Matrix.mul_assoc, (knownQubitControl_ABC_phase_factorization p).1]
  · simp only [if_true]
    rw [← multiWireState_smul]
    simp only [← applyGate_mul]
    rw [← applyGate_smul]
    congr 2
    simpa only [Matrix.mul_assoc] using!
      (knownQubitControl_ABC_phase_factorization p).2.1

/-- Selects the sole control wire for one control, or the final conjunction work wire for more
controls. -/
def multiKnownFlagWire (n : ℕ) (hn : n ≠ 0) : Fin (n+1+(n-1)) :=
  if h : n = 1 then multiKnownControlWire n ⟨0,by omega⟩
  else multiKnownWorkWire n ⟨n-2,by omega⟩

/-- For a positive number of controls, the control-flag wire differs from the target wire. -/
theorem multiKnownFlagWire_ne_target (n : ℕ) (hn : n ≠ 0) :
    multiKnownFlagWire n hn ≠ multiKnownTargetWire n := by
  unfold multiKnownFlagWire
  split <;> intro he <;> have hv := congrArg Fin.val he <;> dsimp at hv <;> omega

/-- The local gate list that computes the all-true flag, applies the known controlled qubit
unitary, and uncomputes the work bits. -/
noncomputable def multiKnownSteps (n : ℕ) (p : KnownQubitAngles) :
    List (ReflectionGate (n+1+(n-1))) :=
  if hn : n = 0 then [.inl (multiKnownTargetWire n,knownQubitUnitary p)]
  else multiAndSteps n ++ multiKnownPairSteps (multiKnownFlagWire n hn)
    (multiKnownTargetWire n) p ++ reflectionAdjoint (multiAndSteps n)

/-- The synthesized multiple-control gate list is legal for every number of controls and every
Euler parameter tuple. -/
theorem multiKnownSteps_legal (n : ℕ) (p : KnownQubitAngles) :
    reflectionLegal (multiKnownSteps n p) := by
  unfold multiKnownSteps
  split
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    exact knownQubitUnitary_unitary p
  · rename_i hn
    rw [reflectionLegal_append, reflectionLegal_append]
    exact ⟨⟨multiAndPrefix_legal n (n-1), multiKnownPairSteps_legal _ _
      (multiKnownFlagWire_ne_target n hn) p⟩,
      reflectionAdjoint_legal _ (multiAndPrefix_legal n (n-1))⟩

/-- The synthesized multiple-control gate list has exactly `multiKnownCost n` gates. -/
theorem multiKnownSteps_length (n : ℕ) (p : KnownQubitAngles) :
    (multiKnownSteps n p).length = multiKnownCost n := by
  unfold multiKnownSteps multiKnownCost
  split
  · simp_all
  · rename_i hn
    simp only [List.length_append, reflectionAdjoint_length,
      multiAndSteps, multiAndPrefix_length n (n-1) le_rfl,
      multiKnownPairSteps, List.length_cons, List.length_nil]
    omega

/-- The clean embedding of a basis state is the joined basis register with every work bit false. -/
@[simp] theorem multiKnownEmbed_ket (n : ℕ) (x : Reg n × Bool) :
    multiKnownEmbed n (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket ((multiKnownSplit n).symm (x,fun _ => false)) := by
  rw [multiKnownEmbed, tensorState_ket_ket]
  funext z
  simp only [relabelState, Function.comp_apply, Qatlib.Foundations.PureStateMath.Ket,
      Equiv.symm_symm]
  simp only [show (multiKnownSplit n z = (x,fun _ => false)) =
      (z = (multiKnownSplit n).symm (x,fun _ => false)) from
    propext (multiKnownSplit n).apply_eq_iff_eq_symm_apply]

/-- The clean embedding commutes with scalar multiplication. -/
@[simp] theorem multiKnownEmbed_smul (n : ℕ) (c : ℂ) (ψ : QState (Reg n × Bool)) :
    multiKnownEmbed n (c • ψ) = c • multiKnownEmbed n ψ := by
  funext z
  simp [multiKnownEmbed, relabelState, TensorState, mul_assoc]

/-- The clean embedding commutes with finite sums of states. -/
theorem multiKnownEmbed_sum {J : Type*} [Fintype J] (n : ℕ)
    (ψ : J → QState (Reg n × Bool)) :
    multiKnownEmbed n (∑ j,ψ j) = ∑ j,multiKnownEmbed n (ψ j) := by
  funext z
  simp [multiKnownEmbed, relabelState, TensorState, Finset.sum_mul]

/-- Updating the target wire of a joined register changes only the target component. -/
theorem multiKnownJoin_update_target (n : ℕ) (x : Reg n) (b b' : Bool)
    (w : Reg (n-1)) :
    Function.update ((multiKnownSplit n).symm ((x,b),w)) (multiKnownTargetWire n) b' =
      (multiKnownSplit n).symm ((x,b'),w) := by
  funext k
  have hk : k.val < n ∨ k.val = n ∨ n+1 ≤ k.val := by omega
  rcases hk with hk | hk | hk
  · let j : Fin n := ⟨k.val,hk⟩
    have he : k = multiKnownControlWire n j := Fin.ext rfl
    rw [he, Function.update_of_ne (by intro h; have := congrArg Fin.val h; dsimp at this; omega)]
    simp only [multiKnownJoin_control]
  · have he : k = multiKnownTargetWire n := Fin.ext hk
    rw [he, Function.update_self, multiKnownJoin_target]
  · let j : Fin (n-1) := ⟨k.val-(n+1),by omega⟩
    have he : k = multiKnownWorkWire n j := Fin.ext (by dsimp [j]; omega)
    rw [he, Function.update_of_ne (by intro h; have := congrArg Fin.val h; dsimp at this; omega)]
    simp only [multiKnownJoin_work]

/-- Expands the target-wire superposition of a joined register as the sum of the two joined
target basis states. -/
theorem multiKnownJoin_wireState (n : ℕ) (x : Reg n) (b : Bool)
    (w : Reg (n-1)) (φ : QState Bool) :
    multiWireState (multiKnownTargetWire n) ((multiKnownSplit n).symm ((x,b),w)) φ =
      ∑ b' : Bool, φ b' • Qatlib.Foundations.PureStateMath.Ket ((multiKnownSplit n).symm ((x,b'),w)) := by
  simp only [multiWireState, multiKnownJoin_update_target, Fintype.sum_bool]
  exact add_comm _ _

/-- Reversing the conjunction chain restores all work bits to false on a fully computed prefix
basis state. -/
theorem multiAnd_uncompute (n : ℕ) (x : Reg n) (b : Bool) :
    Run (1 : Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ)
      (reflectionCompile (reflectionAdjoint (multiAndSteps n)))
      (Qatlib.Foundations.PureStateMath.Ket (multiAndPrefixBasis n x b (n-1))) =
      Qatlib.Foundations.PureStateMath.Ket ((multiKnownSplit n).symm ((x,b),fun _ => false)) := by
  simp only [multiAndSteps]
  rw [← multiAndPrefix_action n (n-1) le_rfl x b, run_reflectionCompile,
    run_reflectionCompile, reflectionAdjoint_matrix _ (multiAndPrefix_legal n (n-1))]
  rw [ApplyGate, ApplyGate, Matrix.mulVec_mulVec]
  have hu := reflectionProgramMatrix_unitary (multiAndSteps n) (multiAndPrefix_legal n (n-1))
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
  simp only [multiAndSteps] at hu
  rw [hu, Matrix.one_mulVec]

/-- The all-control test equals the decision procedure for every control bit being true. -/
theorem allControlTrue_eq_decide (n : ℕ) (x : Reg n) :
    allControlTrue n x = decide (∀ i, x i = true) := by
  apply Bool.eq_iff_iff.mpr
  simp [allControlTrue, List.all_eq_true, List.mem_ofFn]

/-- After the conjunction chain, the selected flag wire equals the all-true control test. -/
theorem multiKnownFlag_value (n : ℕ) (hn : n ≠ 0) (x : Reg n) (b : Bool) :
    multiAndPrefixBasis n x b (n-1) (multiKnownFlagWire n hn) = allControlTrue n x := by
  unfold multiKnownFlagWire
  split
  · rename_i h
    simp only [multiAndPrefixBasis, multiKnownJoin_control]
    rw [allControlTrue_eq_decide]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro hx i
      have hi : i = ⟨0,by omega⟩ := Fin.ext (by omega)
      simpa only [hi] using! hx
    · intro hx; exact hx _
  · rename_i h
    simp only [multiAndPrefixBasis, multiKnownJoin_work]
    rw [if_pos (by omega), allControlTrue_eq_decide]
    congr 1
    apply propext
    constructor
    · intro hx i; exact hx i (by omega)
    · intro hx i _; exact hx i

/-- Expands the action of `multiKnownGate` on a control-target basis state, preserving the
controls. -/
theorem multiKnownGate_ket (n : ℕ) (U : Matrix Bool Bool ℂ) (x : Reg n) (b : Bool) :
    ApplyGate (multiKnownGate n U) (Qatlib.Foundations.PureStateMath.Ket (x,b)) =
      ∑ a : Bool, (if allControlTrue n x then U else 1) a b • Qatlib.Foundations.PureStateMath.Ket (x,a) := by
  funext ⟨y,a⟩
  by_cases hf : allControlTrue n x = true <;>
    by_cases hy : y = x <;> cases a <;> cases b <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, multiKnownGate, hy, hf,
      Finset.sum_apply, Matrix.one_apply]

/-- The local gate list implements the all-true controlled qubit matrix on each basis state and
restores every work bit to false. -/
theorem multiKnown_basis_action (n : ℕ) (p : KnownQubitAngles) (x : Reg n) (b : Bool) :
    Run (1 : Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ)
      (reflectionCompile (multiKnownSteps n p))
      (Qatlib.Foundations.PureStateMath.Ket ((multiKnownSplit n).symm ((x,b),fun _ => false))) =
      ∑ a : Bool, (if allControlTrue n x then knownQubitUnitary p else 1) a b •
        Qatlib.Foundations.PureStateMath.Ket ((multiKnownSplit n).symm ((x,a),fun _ => false)) := by
  by_cases hn : n = 0
  · subst n
    rw [multiKnownSteps, dif_pos rfl]
    simp only [reflectionCompile, List.map_cons,
      List.map_nil, run_gate, run_nil, reflectionGateMatrix]
    rw [applyGate_wireGate_ket, multiKnownJoin_target,
      multiKnownJoin_update_target, multiKnownJoin_update_target]
    simp only [allControlTrue, List.ofFn_zero, List.all_nil, if_true, Fintype.sum_bool]
    exact add_comm _ _
  · rw [multiKnownSteps, dif_neg hn, reflectionCompile_append,
      reflectionCompile_append, run_append, run_append]
    rw [show Run (1 : Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ)
      (reflectionCompile (multiAndSteps n))
      (Qatlib.Foundations.PureStateMath.Ket ((multiKnownSplit n).symm ((x,b),fun _ => false))) =
      Qatlib.Foundations.PureStateMath.Ket (multiAndPrefixBasis n x b (n-1)) from
        multiAndPrefix_action n (n-1) le_rfl x b]
    have hk : multiWireState (multiKnownTargetWire n) (multiAndPrefixBasis n x b (n-1))
        (Qatlib.Foundations.PureStateMath.Ket b) = Qatlib.Foundations.PureStateMath.Ket (multiAndPrefixBasis n x b (n-1)) := by
      simpa only [multiAndPrefixBasis, multiKnownJoin_target] using!
        multiWireState_ket (multiKnownTargetWire n) (multiAndPrefixBasis n x b (n-1))
    rw [← hk, multiKnownPairSteps_action _ _ (multiKnownFlagWire_ne_target n hn),
      multiKnownFlag_value]
    rw [multiAndPrefixBasis, multiKnownJoin_wireState, run_reflectionCompile_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [run_reflectionCompile_smul]
    change _ • Run _ _
        (Qatlib.Foundations.PureStateMath.Ket (multiAndPrefixBasis n x a (n-1))) = _
    rw [multiAnd_uncompute]
    congr 1
    simp [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]

/-- The local synthesis is legal, has exactly `multiKnownCost n` gates and no queries, and
implements the controlled qubit unitary on every cleanly embedded state; compare
[BarencoEtAl1995]. -/
theorem multi_known_control_actual_local_table_and_cost (n : ℕ) (p : KnownQubitAngles) :
    reflectionLegal (multiKnownSteps n p) ∧
    (multiKnownSteps n p).length = multiKnownCost n ∧
    QueryCount (reflectionCompile (multiKnownSteps n p)) = 0 ∧
    GateCount (reflectionCompile (multiKnownSteps n p)) = multiKnownCost n ∧
    ∀ ψ : QState (Reg n × Bool),
      Run (1 : Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ)
        (reflectionCompile (multiKnownSteps n p)) (multiKnownEmbed n ψ) =
        multiKnownEmbed n (multiKnownGate n (knownQubitUnitary p) *ᵥ ψ) := by
  refine ⟨multiKnownSteps_legal n p, multiKnownSteps_length n p,
    queryCount_reflectionCompile _, ?_, ?_⟩
  · rw [gateCount_reflectionCompile, multiKnownSteps_length]
  · intro ψ
    conv_lhs => rw [state_ket_expansion ψ]
    rw [multiKnownEmbed_sum, run_reflectionCompile_sum]
    change _ = multiKnownEmbed n (ApplyGate (multiKnownGate n (knownQubitUnitary p)) ψ)
    conv_rhs => rw [state_ket_expansion ψ]
    rw [ApplyGate, Matrix.mulVec_sum, multiKnownEmbed_sum]
    refine Finset.sum_congr rfl fun ⟨x,b⟩ _ => ?_
    rw [Matrix.mulVec_smul, multiKnownEmbed_smul, multiKnownEmbed_smul,
      multiKnownEmbed_ket, run_reflectionCompile_smul, multiKnown_basis_action]
    change _ = _ • multiKnownEmbed n
        (ApplyGate (multiKnownGate n (knownQubitUnitary p)) (Qatlib.Foundations.PureStateMath.Ket (x,b)))
    rw [multiKnownGate_ket, multiKnownEmbed_sum]
    simp only [multiKnownEmbed_smul, multiKnownEmbed_ket]

end Qatlib.Concepts.MatrixAccess.KnownFrameSynth
