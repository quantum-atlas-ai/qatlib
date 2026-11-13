/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Foundations.PureStateMath.Tensor
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary

/-!
# Synthesis without work qubits

This module constructs exact local gate tables for controlled one-qubit unitaries and two-level
instructions, using the elementary-gate synthesis framework of [BarencoEtAl1995]. It develops
Boolean prefix computations with borrowed bits and derives explicit gate bounds for
implementations without work qubits and with one clean ancillary qubit.

The instruction tables combine into exact synthesis of arbitrary unitaries on nonempty qubit
registers. The final comparison theorem supplies implementations of the same unitary both
without work qubits and in a clean frame.

## Main statements

* `no_work_multi_unitary_control_local_table_and_cost`: quadratic gate bound for a controlled
  one-qubit unitary without work qubits.
* `single_ancilla_known_control_local_table_and_cost`: linear gate bound using one clean
  ancillary qubit.
* `known_two_level_no_work_local_implementation`: cubic gate bound for a legal two-level
  instruction.
* `known_unitary_no_work_actual_local_synthesis`: exact synthesis with at most `768*(n+1)^3*4^n`
  gates for `1 ≤ n`.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The equivalence identifying a one-qubit register with its Boolean value. -/
def noWorkOneBitEquiv : Reg 1 ≃ Bool where
  toFun x := x 0
  invFun b := fun _ => b
  left_inv x := by funext i; have : i = 0 := Subsingleton.elim _ _; simp [this]
  right_inv _ := rfl

/-- Splits an `(n+1)`-qubit register into `n` control bits and a target bit. -/
def noWorkControlSplit (n : ℕ) : Reg (n+1) ≃ (Reg n × Bool) :=
  (regAppendEquiv n 1).trans (Equiv.prodCongr (Equiv.refl _) noWorkOneBitEquiv)

/-- Splits the register into control bits, a target bit, and a one-qubit ancillary register. -/
def singleAncillaSplit (n : ℕ) : Reg (n+1+1) ≃ ((Reg n × Bool) × Reg 1) :=
  (regAppendEquiv (n+1) 1).trans
    (Equiv.prodCongr (noWorkControlSplit n) (Equiv.refl _))

/-- Embeds a control-target state by adjoining an ancillary qubit in the false basis state. -/
noncomputable def singleAncillaEmbed (n : ℕ) (ψ : QState (Reg n × Bool)) :
    QState (Reg (n+1+1)) :=
  relabelState (singleAncillaSplit n).symm
    (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket (fun _ : Fin 1 => false)))

/-- The inverse control-target splitting is the data-register equivalence `knownDataEquiv`. -/
theorem noWorkControlSplit_symm_data (n : ℕ) :
    (noWorkControlSplit n).symm = knownDataEquiv n := by
  apply Equiv.ext
  intro ⟨x,b⟩
  apply (noWorkControlSplit n).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · funext i
    exact (knownDataEquiv_control n x b i).symm
  · exact (knownDataEquiv_target n x b).symm

/-- Every unitary matrix on a finite nonempty index type possesses a unitary square root. -/
theorem noWork_unitary_square_root {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (U : Matrix I I ℂ) (hU : U ∈ unitaryGroup I ℂ) :
    ∃ V : Matrix I I ℂ, V ∈ unitaryGroup I ℂ ∧ V * V = U := by
  letI : CStarAlgebra (Matrix I I ℂ) := {}
  letI : ContinuousFunctionalCalculus ℂ (Matrix I I ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  have hu : U ∈ unitary (Matrix I I ℂ) := hU
  have hn : IsStarNormal U := isStarNormal_of_mem_unitary hu
  let f : ℂ → ℂ := fun z => Complex.exp (((z.arg / 2 : ℝ) : ℂ) * Complex.I)
  have hf : ContinuousOn f (spectrum ℂ U) := U.finite_spectrum.continuousOn f
  refine ⟨cfc f U, ?_, ?_⟩
  · apply (cfc_unitary_iff f U hn hf).mpr
    intro z _
    have hnorm : ‖f z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    calc
      star (f z) * f z = (Complex.normSq (f z) : ℂ) :=
        (Complex.normSq_eq_conj_mul_self (z := f z)).symm
      _ = 1 := by rw [Complex.normSq_eq_norm_sq, hnorm]; norm_num
  · rw [← cfc_mul f f U hf hf]
    calc
      cfc (fun z => f z * f z) U = cfc (id : ℂ → ℂ) U := by
        apply cfc_congr
        intro z hz
        have hnorm : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary hu hz
        change Complex.exp _ * Complex.exp _ = z
        rw [← Complex.exp_add]
        have he : (((z.arg / 2 : ℝ) : ℂ) * Complex.I +
            ((z.arg / 2 : ℝ) : ℂ) * Complex.I) = (z.arg : ℂ) * Complex.I := by
          push_cast
          ring
        rw [he]
        simpa only [hnorm, Complex.ofReal_one, one_mul] using!
          Complex.norm_mul_exp_arg_mul_I z
      _ = U := cfc_id ℂ U hn

/-- A gate on the unique wire equals the Boolean gate transported along `noWorkOneBitEquiv`. -/
theorem noWork_one_wire_matrix (U : Matrix Bool Bool ℂ) :
    wireGate 1 0 U = relabelGate noWorkOneBitEquiv.symm U := by
  ext x y
  rw [wireGate_apply, if_pos]
  · rfl
  · intro k hk
    exact (hk (Subsingleton.elim _ _)).elim

/-- Every one-qubit unitary has an exact legal one-gate table with no oracle queries. -/
theorem noWork_one_bit_unitary_table (U : Matrix (Reg 1) (Reg 1) ℂ)
    (hU : U ∈ unitaryGroup (Reg 1) ℂ) :
    ∃ gs : List (ReflectionGate 1), reflectionLegal gs ∧ gs.length = 1 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = 1 ∧
      ∀ ψ : QState (Reg 1), Run 1 (reflectionCompile gs) ψ = U *ᵥ ψ := by
  let B := relabelGate noWorkOneBitEquiv U
  refine ⟨[.inl (0,B)], ?_, rfl, queryCount_reflectionCompile _, rfl, ?_⟩
  · intro g hg
    obtain rfl := List.mem_singleton.mp hg
    exact (relabelGate_mem_unitaryGroup noWorkOneBitEquiv U).2 hU
  · intro ψ
    simp only [reflectionCompile, List.map_cons, List.map_nil, run_gate, run_nil,
      reflectionGateMatrix, noWork_one_wire_matrix, B, relabelGate_relabelGate]
    rfl

/-- Every legal two-level instruction on one qubit has an exact legal one-gate table with no
oracle queries. -/
theorem noWork_one_bit_two_level_table (g : TwoLevelInstruction (Reg 1))
    (hg : twoLevelLegal g) :
    ∃ gs : List (ReflectionGate 1), reflectionLegal gs ∧ gs.length = 1 ∧
      QueryCount (reflectionCompile gs) = 0 ∧ GateCount (reflectionCompile gs) = 1 ∧
      ∀ ψ : QState (Reg 1), Run 1 (reflectionCompile gs) ψ = twoLevelMatrix g *ᵥ ψ :=
  noWork_one_bit_unitary_table _ (twoLevelMatrix_unitary g hg)

/-- The four-Toffoli gate sequence used for a three-control toggle with a borrowed wire. -/
noncomputable def noWorkDirtyTripleSteps {N : ℕ} (a b c t w : Fin N) :
    List (ReflectionGate N) :=
  toffoliLocalSteps a b w ++ toffoliLocalSteps w c t ++
    toffoliLocalSteps a b w ++ toffoliLocalSteps w c t

/-- The borrowed-wire three-control toggle sequence has length `60`. -/
theorem noWorkDirtyTriple_length {N : ℕ} (a b c t w : Fin N) :
    (noWorkDirtyTripleSteps a b c t w).length = 60 := by
  simp [noWorkDirtyTripleSteps, toffoliLocalSteps_length]

/-- The three-control toggle sequence is legal when its five wires are pairwise distinct. -/
theorem noWorkDirtyTriple_legal {N : ℕ} (a b c t w : Fin N)
    (h : List.Pairwise (· ≠ ·) [a,b,c,t,w]) :
    reflectionLegal (noWorkDirtyTripleSteps a b c t w) := by
  have hab : a ≠ b := (List.pairwise_cons.mp h).1 b (by simp)
  have haw : a ≠ w := (List.pairwise_cons.mp h).1 w (by simp)
  have hbw : b ≠ w := (List.pairwise_cons.mp (List.pairwise_cons.mp h).2).1 w (by simp)
  have hcw : c ≠ w :=
      (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp h).2).2).1 w (by simp)
  have hct : c ≠ t :=
      (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp h).2).2).1 t (by simp)
  have htw : t ≠ w :=
      (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp h).2).2).2).1 w (by simp)
  simp only [noWorkDirtyTripleSteps, reflectionLegal_append]
  exact ⟨⟨⟨toffoliLocalSteps_legal a b w hab haw hbw,
    toffoliLocalSteps_legal w c t hcw.symm htw.symm hct⟩,
    toffoliLocalSteps_legal a b w hab haw hbw⟩,
    toffoliLocalSteps_legal w c t hcw.symm htw.symm hct⟩

/-- On distinct wires, the sequence toggles the target by the conjunction of three controls and
restores all other basis bits. -/
theorem noWorkDirtyTriple_ket {N : ℕ} (a b c t w : Fin N)
    (h : List.Pairwise (· ≠ ·) [a,b,c,t,w]) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (noWorkDirtyTripleSteps a b c t w)) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (x a && x b && x c))) := by
  have hab : a ≠ b := (List.pairwise_cons.mp h).1 b (by simp)
  have hat : a ≠ t := (List.pairwise_cons.mp h).1 t (by simp)
  have haw : a ≠ w := (List.pairwise_cons.mp h).1 w (by simp)
  have hbt : b ≠ t := (List.pairwise_cons.mp (List.pairwise_cons.mp h).2).1 t (by simp)
  have hbw : b ≠ w := (List.pairwise_cons.mp (List.pairwise_cons.mp h).2).1 w (by simp)
  have hct : c ≠ t :=
      (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp h).2).2).1 t (by simp)
  have hcw : c ≠ w :=
      (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp h).2).2).1 w (by simp)
  have htw : t ≠ w :=
      (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp h).2).2).2).1 w (by simp)
  have ha := (local_toffoli_fifteen_exact N a b w hab haw hbw).2.2
  have hb := (local_toffoli_fifteen_exact N w c t hcw.symm htw.symm hct).2.2
  simp only [noWorkDirtyTripleSteps, reflectionCompile_append, run_append]
  rw [ha, hb, ha, hb]
  congr 1
  funext k
  by_cases hkt : k = t
  · subst k
    simp only [Function.update_self, Function.update_of_ne haw,
      Function.update_of_ne hbw, Function.update_of_ne hat,
      Function.update_of_ne hbt, Function.update_of_ne hcw,
      Function.update_of_ne hct, Function.update_of_ne htw,
      Function.update_of_ne htw.symm]
    cases x a <;> cases x b <;> cases x c <;> cases x w <;> cases x t <;> rfl
  · by_cases hkw : k = w
    · subst k
      simp [Function.update_of_ne hkt, Function.update_of_ne haw,
        Function.update_of_ne hbw, Function.update_of_ne hat,
        Function.update_of_ne hbt]
    · simp [Function.update_of_ne hkt, Function.update_of_ne hkw]

/-- The three-control sequence acts on any state by linearly extending its target-toggle action
on basis registers, assuming distinct wires. -/
theorem noWorkDirtyTriple_state {N : ℕ} (a b c t w : Fin N)
    (h : List.Pairwise (· ≠ ·) [a,b,c,t,w]) (ψ : QState (Reg N)) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (noWorkDirtyTripleSteps a b c t w)) ψ =
      ∑ x, ψ x • Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (x a && x b && x c))) := by
  conv_lhs => arg 3; rw [state_ket_expansion ψ]
  rw [run_reflectionCompile_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [run_reflectionCompile_smul, noWorkDirtyTriple_ket a b c t w h x]

/-- An uncontrolled known one-qubit unitary has an exact legal one-gate, query-free
implementation under the control-target relabeling. -/
theorem noWork_zero_control_table (p : KnownQubitAngles) :
    ∃ gs : List (ReflectionGate 1), reflectionLegal gs ∧ gs.length = 1 ∧
      QueryCount (reflectionCompile gs) = 0 ∧ GateCount (reflectionCompile gs) = 1 ∧
      ∀ ψ : QState (Reg 0 × Bool),
        Run 1 (reflectionCompile gs) (relabelState (noWorkControlSplit 0).symm ψ) =
          relabelState (noWorkControlSplit 0).symm (multiKnownGate 0 (knownQubitUnitary p) *ᵥ ψ) := by
  let U := knownQubitUnitary p
  have hmat : wireGate 1 0 U = relabelGate (noWorkControlSplit 0).symm (multiKnownGate 0 U) := by
    ext x y
    rw [wireGate_apply, if_pos (by intro k hk; exact (hk (Subsingleton.elim _ _)).elim)]
    change U (x 0) (y 0) = if (noWorkControlSplit 0 x).1 = (noWorkControlSplit 0 y).1 then
      if allControlTrue 0 (noWorkControlSplit 0 y).1 then U (x 0) (y 0) else (1 : Matrix Bool Bool ℂ) (x 0) (y 0) else 0
    rw [if_pos (Subsingleton.elim _ _)]
    simp [allControlTrue]
  refine ⟨[.inl (0,U)], ?_, rfl, queryCount_reflectionCompile _, rfl, ?_⟩
  · intro g hg
    obtain rfl := List.mem_singleton.mp hg
    exact knownQubitUnitary_unitary p
  · intro ψ
    simp only [reflectionCompile, List.map_cons, List.map_nil, run_gate, run_nil,
      reflectionGateMatrix, hmat]
    exact applyGate_relabelGate _ _ _

/-- Relabeling a basis ket gives the ket at the relabeled index. -/
private theorem noWork_relabel_ket {I J : Type} [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (x : I) : relabelState e (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (e x) := by
  funext y
  simp [relabelState, Qatlib.Foundations.PureStateMath.Ket, Equiv.symm_apply_eq]

/-- Relabeling states commutes with finite sums. -/
private theorem noWork_relabel_sum {I J K : Type} [Fintype K]
    (e : I ≃ J) (φ : K → QState I) :
    relabelState e (∑ k, φ k) = ∑ k, relabelState e (φ k) := by
  funext y
  simp [relabelState]

/-- Relabeling states commutes with complex scalar multiplication. -/
private theorem noWork_relabel_smul {I J : Type} (e : I ≃ J)
    (z : ℂ) (ψ : QState I) : relabelState e (z • ψ) = z • relabelState e ψ := rfl

/-- Updating the final wire of a joined control-target register changes only its target
component. -/
theorem noWorkControlJoin_update (n : ℕ) (x : Reg n) (b a : Bool) :
    Function.update ((noWorkControlSplit n).symm (x,b)) (Fin.last n) a =
      (noWorkControlSplit n).symm (x,a) := by
  rw [noWorkControlSplit_symm_data]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [knownDataEquiv_target]
  · rw [Function.update_of_ne (by simp), knownDataEquiv_control,
      knownDataEquiv_control]

/-- A superposition on the target wire of a joined register expands as the corresponding two
basis kets. -/
theorem noWorkControlJoin_wireState (n : ℕ) (x : Reg n) (b : Bool)
    (φ : QState Bool) :
    multiWireState (Fin.last n) ((noWorkControlSplit n).symm (x,b)) φ =
      ∑ a : Bool, φ a • Qatlib.Foundations.PureStateMath.Ket ((noWorkControlSplit n).symm (x,a)) := by
  simp only [multiWireState, noWorkControlJoin_update, Fintype.sum_bool]
  exact add_comm _ _

/-- A singly controlled known one-qubit unitary has an exact legal six-gate, query-free
implementation. -/
theorem noWork_one_control_table (p : KnownQubitAngles) :
    ∃ gs : List (ReflectionGate 2), reflectionLegal gs ∧ gs.length = 6 ∧
      QueryCount (reflectionCompile gs) = 0 ∧ GateCount (reflectionCompile gs) = 6 ∧
      ∀ ψ : QState (Reg 1 × Bool),
        Run 1 (reflectionCompile gs) (relabelState (noWorkControlSplit 1).symm ψ) =
          relabelState (noWorkControlSplit 1).symm
            (multiKnownGate 1 (knownQubitUnitary p) *ᵥ ψ) := by
  let gs := multiKnownPairSteps (0 : Fin 2) (1 : Fin 2) p
  have hb (x : Reg 1) (b : Bool) :
      Run 1 (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket ((noWorkControlSplit 1).symm (x,b))) =
        ∑ a : Bool, (if allControlTrue 1 x then knownQubitUnitary p else 1) a b •
          Qatlib.Foundations.PureStateMath.Ket ((noWorkControlSplit 1).symm (x,a)) := by
    let q := (noWorkControlSplit 1).symm (x,b)
    have ht : q (1 : Fin 2) = b := by
      change (knownDataEquiv 1 (x,b)) (Fin.last 1) = b
      exact knownDataEquiv_target 1 x b
    have hc : q (0 : Fin 2) = allControlTrue 1 x := by
      change (knownDataEquiv 1 (x,b)) (Fin.castSucc (0 : Fin 1)) = allControlTrue 1 x
      rw [knownDataEquiv_control]
      simp [allControlTrue, List.ofFn_succ]
    have hk := multiWireState_ket (1 : Fin 2) q
    rw [ht] at hk
    rw [← hk, multiKnownPairSteps_action _ _ (by decide), hc]
    rw [show (1 : Fin 2) = Fin.last 1 from rfl, noWorkControlJoin_wireState]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    simp [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
  refine ⟨gs, multiKnownPairSteps_legal _ _ (by decide) p, rfl,
    queryCount_reflectionCompile _, rfl, ?_⟩
  intro ψ
  conv_lhs => arg 3; arg 2; rw [state_ket_expansion ψ]
  rw [noWork_relabel_sum, run_reflectionCompile_sum]
  conv_rhs => arg 2; arg 2; rw [state_ket_expansion ψ]
  rw [Matrix.mulVec_sum, noWork_relabel_sum]
  apply Finset.sum_congr rfl
  intro ⟨x,b⟩ _
  rw [noWork_relabel_smul, noWork_relabel_ket, run_reflectionCompile_smul, hb,
    Matrix.mulVec_smul, noWork_relabel_smul]
  change _ = _ • relabelState _ (ApplyGate _ (Qatlib.Foundations.PureStateMath.Ket (x,b)))
  rw [multiKnownGate_ket, noWork_relabel_sum]
  simp only [noWork_relabel_smul, noWork_relabel_ket]

/-- The conjunction of the first `r` values of a Boolean sequence, with empty conjunction true. -/
def noWorkPrefixAnd (c : ℕ → Bool) (r : ℕ) : Bool := (List.range r).all c

/-- Extending a Boolean prefix by one bit conjoins the previous prefix value with that bit. -/
@[simp] theorem noWorkPrefixAnd_succ (c : ℕ → Bool) (r : ℕ) :
    noWorkPrefixAnd c (r+1) = (noWorkPrefixAnd c r && c r) := by
  simp [noWorkPrefixAnd, List.range_succ]

/-- Toggles dirty bit `r` by the conjunction of control bit `r+1` and dirty bit `r-1`. -/
def noWorkDirtyPrefixStage (c : ℕ → Bool) (r : ℕ) (d : ℕ → Bool) : ℕ → Bool :=
  Function.update d r (d r ^^ (c (r+1) && d (r-1)))

/-- The recursive Boolean transformation for accumulating control-prefix conjunctions in dirty
bits. -/
def noWorkDirtyPrefixBits (c : ℕ → Bool) : ℕ → (ℕ → Bool) → ℕ → Bool
  | 0, d => d
  | 1, d => Function.update d 0 (d 0 ^^ (c 0 && c 1))
  | r+2, d => noWorkDirtyPrefixStage c (r+1) (noWorkDirtyPrefixBits c (r+1) (noWorkDirtyPrefixStage c (r+1) d))

/-- The prefix transformation toggles dirty bit `i < r` by the first `i+2` controls and leaves
later dirty bits unchanged. -/
theorem noWorkDirtyPrefixBits_spec (c d : ℕ → Bool) (r i : ℕ) :
    noWorkDirtyPrefixBits c r d i = if i < r then d i ^^ noWorkPrefixAnd c (i+2) else d i := by
  induction r using Nat.twoStepInduction generalizing d i with
  | zero => simp [noWorkDirtyPrefixBits]
  | one =>
    by_cases hi : i = 0
    · subst i
      simp [noWorkDirtyPrefixBits, noWorkPrefixAnd, List.range_succ]
    · have hlt : ¬ i < 1 := by omega
      simp [noWorkDirtyPrefixBits, Function.update_of_ne hi, hlt]
  | more r ih _ =>
    simp only [noWorkDirtyPrefixBits]
    rename_i ih_next
    by_cases hi : i = r+1
    · subst i
      simp only [noWorkDirtyPrefixStage, Function.update_self]
      rw [ih_next, ih_next]
      simp only [lt_self_iff_false, if_false, Nat.add_sub_cancel_right,
        show r < r+1 from by omega, if_true, Function.update_self]
      simp only [show r+1 < r+2 from by omega, if_true]
      rw [noWorkPrefixAnd_succ c (r+2)]
      cases h0 : c (r+2) <;> cases h1 : d r <;>
        cases h2 : noWorkPrefixAnd c (r+2) <;> cases h3 : d (r+1) <;>
        simp [h1, Function.update, show r+1-1 = r from by omega]
    · simp only [noWorkDirtyPrefixStage, Function.update_of_ne hi]
      rw [ih_next]
      simp only [Function.update_of_ne hi]
      have he : (i < r+1) = (i < r+1+1) := propext (by omega)
      simp only [he, show r+1+1 = r+2 from by omega]

/-- Applying the dirty-prefix Boolean transformation twice restores the original dirty bits. -/
theorem noWorkDirtyPrefixBits_involutive (c : ℕ → Bool) (r : ℕ) :
    Function.Involutive (noWorkDirtyPrefixBits c r) := by
  intro d
  funext i
  rw [noWorkDirtyPrefixBits_spec, noWorkDirtyPrefixBits_spec]
  by_cases hi : i < r <;> simp [hi]

/-- The recursive Toffoli gate sequence realizing the dirty-prefix transformation. -/
noncomputable def noWorkDirtyPrefixSteps {N : ℕ} (c w : ℕ → Fin N) :
    ℕ → List (ReflectionGate N)
  | 0 => []
  | 1 => toffoliLocalSteps (c 0) (c 1) (w 0)
  | r+2 => toffoliLocalSteps (c (r+2)) (w r) (w (r+1)) ++
      noWorkDirtyPrefixSteps c w (r+1) ++
      toffoliLocalSteps (c (r+2)) (w r) (w (r+1))

/-- The dirty-prefix sequence has length `15*(2*r-1)`, with subtraction in the natural numbers. -/
theorem noWorkDirtyPrefixSteps_length {N : ℕ} (c w : ℕ → Fin N) (r : ℕ) :
    (noWorkDirtyPrefixSteps c w r).length = 15*(2*r-1) := by
  induction r using Nat.twoStepInduction with
  | zero => rfl
  | one => exact toffoliLocalSteps_length _ _ _
  | more r _ ih =>
    simp only [noWorkDirtyPrefixSteps, List.length_append, toffoliLocalSteps_length, ih]
    have h : 1 ≤ 2*(r+1) := by omega
    omega

/-- Toggles target wire `t` by the conjunction of wires `a` and `b` in a basis register. -/
def noWorkToffoliUpdate {N : ℕ} (a b t : Fin N) (x : Reg N) : Reg N :=
  Function.update x t (x t ^^ (x a && x b))

/-- The basis-register transformation induced by the recursive dirty-prefix Toffoli sequence. -/
def noWorkDirtyPrefixTransform {N : ℕ} (c w : ℕ → Fin N) : ℕ → Reg N → Reg N
  | 0, x => x
  | 1, x => noWorkToffoliUpdate (c 0) (c 1) (w 0) x
  | r+2, x => noWorkToffoliUpdate (c (r+2)) (w r) (w (r+1))
      (noWorkDirtyPrefixTransform c w (r+1)
        (noWorkToffoliUpdate (c (r+2)) (w r) (w (r+1)) x))

/-- Requires the used control wires and dirty wires to be separately injective and mutually
disjoint. -/
def noWorkDirtyPrefixLayout {N : ℕ} (c w : ℕ → Fin N) (r : ℕ) : Prop :=
  Set.InjOn c (Set.Iio (r+1)) ∧ Set.InjOn w (Set.Iio r) ∧
    ∀ i < r+1, ∀ j < r, c i ≠ w j

/-- A valid dirty-prefix layout remains valid when the prefix length is decreased. -/
private theorem noWorkDirtyPrefixLayout_mono {N : ℕ} {c w : ℕ → Fin N} {r s : ℕ}
    (h : noWorkDirtyPrefixLayout c w r) (hs : s ≤ r) : noWorkDirtyPrefixLayout c w s := by
  refine ⟨?_,?_,?_⟩
  · intro i hi j hj hij
    exact h.1 (by change i < r+1; change i < s+1 at hi; omega)
      (by change j < r+1; change j < s+1 at hj; omega) hij
  · intro i hi j hj hij
    exact h.2.1 (by change i < r; change i < s at hi; omega)
      (by change j < r; change j < s at hj; omega) hij
  · intro i hi j hj
    exact h.2.2 i (by omega) j (by omega)

/-- A valid dirty-prefix layout makes every gate in its sequence legal. -/
theorem noWorkDirtyPrefixSteps_legal {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r) : reflectionLegal (noWorkDirtyPrefixSteps c w r) := by
  induction r using Nat.twoStepInduction with
  | zero => simp [noWorkDirtyPrefixSteps,reflectionLegal]
  | one =>
    exact toffoliLocalSteps_legal _ _ _
      (fun he => by have hv := h.1 (by simp) (by simp) he; omega)
      (h.2.2 0 (by omega) 0 (by omega)) (h.2.2 1 (by omega) 0 (by omega))
  | more r _ ih =>
    have ht : reflectionLegal (toffoliLocalSteps (c (r+2)) (w r) (w (r+1))) :=
      toffoliLocalSteps_legal _ _ _ (h.2.2 _ (by omega) _ (by omega))
        (h.2.2 _ (by omega) _ (by omega))
        (fun he => by have hv := h.2.1 (by simp) (by simp) he; omega)
    simp only [noWorkDirtyPrefixSteps,reflectionLegal_append]
    exact ⟨⟨ht,ih (noWorkDirtyPrefixLayout_mono h (by omega))⟩,ht⟩

/-- Under the layout condition, the compiled dirty-prefix sequence maps each basis ket to the
ket of `noWorkDirtyPrefixTransform`. -/
theorem noWorkDirtyPrefixSteps_ket {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (noWorkDirtyPrefixSteps c w r)) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (noWorkDirtyPrefixTransform c w r x) := by
  induction r using Nat.twoStepInduction generalizing x with
  | zero => rfl
  | one =>
    exact (local_toffoli_fifteen_exact N _ _ _
      (fun he => by have hv := h.1 (by simp) (by simp) he; omega)
      (h.2.2 0 (by omega) 0 (by omega)) (h.2.2 1 (by omega) 0 (by omega))).2.2 x
  | more r _ ih =>
    have ht := (local_toffoli_fifteen_exact N (c (r+2)) (w r) (w (r+1))
      (h.2.2 _ (by omega) _ (by omega)) (h.2.2 _ (by omega) _ (by omega))
      (fun he => by have hv := h.2.1 (by simp) (by simp) he; omega)).2.2
    simp only [noWorkDirtyPrefixSteps,reflectionCompile_append,run_append]
    rw [ht,ih (noWorkDirtyPrefixLayout_mono h (by omega)),ht]
    rfl

/-- Boolean sequences agreeing on a prefix have equal conjunctions over that prefix. -/
private theorem noWorkPrefixAnd_congr (c d : ℕ → Bool) (r : ℕ)
    (h : ∀ i < r, c i = d i) : noWorkPrefixAnd c r = noWorkPrefixAnd d r := by
  apply Bool.eq_iff_iff.mpr
  simp only [noWorkPrefixAnd,List.all_eq_true,List.mem_range]
  constructor
  · intro hall i hi
    rw [← h i hi]
    exact hall i hi
  · intro hall i hi
    rw [h i hi]
    exact hall i hi

/-- The dirty-prefix register transformation leaves every wire outside its used dirty wires
unchanged. -/
theorem noWorkDirtyPrefixTransform_outside {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (x : Reg N) (k : Fin N) (hk : ∀ j < r, k ≠ w j) :
    noWorkDirtyPrefixTransform c w r x k = x k := by
  induction r using Nat.twoStepInduction generalizing x with
  | zero => rfl
  | one => exact Function.update_of_ne (hk 0 (by omega)) _ _
  | more r _ ih =>
    simp only [noWorkDirtyPrefixTransform,noWorkToffoliUpdate,
      Function.update_of_ne (hk (r+1) (by omega))]
    rw [ih _ (fun j hj => hk j (by omega))]
    exact Function.update_of_ne (hk (r+1) (by omega)) _ _

/-- Under the layout condition, dirty wire `i < r` is toggled by the conjunction of the first
`i+2` control bits. -/
theorem noWorkDirtyPrefixTransform_flag {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r) (x : Reg N) (i : ℕ) (hi : i < r) :
    noWorkDirtyPrefixTransform c w r x (w i) =
      (x (w i) ^^ noWorkPrefixAnd (fun j => x (c j)) (i+2)) := by
  induction r using Nat.twoStepInduction generalizing x i with
  | zero => omega
  | one =>
    have he : i = 0 := by omega
    subst i
    simp [noWorkDirtyPrefixTransform,noWorkToffoliUpdate,noWorkPrefixAnd,List.range_succ]
  | more r _ ih =>
    let q := noWorkToffoliUpdate (c (r+2)) (w r) (w (r+1)) x
    have hprefix := noWorkDirtyPrefixLayout_mono h (show r+1 ≤ r+2 from by omega)
    have hctrl (j : ℕ) (hj : j < r+3) : q (c j) = x (c j) :=
      Function.update_of_ne (h.2.2 j (by omega) (r+1) (by omega)) _ _
    have hwr : q (w r) = x (w r) :=
      Function.update_of_ne (fun he => by
        have hv := h.2.1 (show r < r+2 from by omega) (show r+1 < r+2 from by omega) he
        omega) _ _
    by_cases hie : i = r+1
    · subst i
      simp only [noWorkDirtyPrefixTransform,noWorkToffoliUpdate,Function.update_self]
      change (noWorkDirtyPrefixTransform c w (r+1) q (w (r+1)) ^^
        (noWorkDirtyPrefixTransform c w (r+1) q (c (r+2)) &&
          noWorkDirtyPrefixTransform c w (r+1) q (w r))) = _
      rw [noWorkDirtyPrefixTransform_outside c w (r+1) q (w (r+1))
        (fun j hj he => by
          have hv : r+1 = j := h.2.1 (show r+1 < r+2 from by omega)
            (show j < r+2 from by omega) he
          omega),
        noWorkDirtyPrefixTransform_outside c w (r+1) q (c (r+2))
          (fun j hj => h.2.2 _ (by omega) _ (by omega)),
        ih hprefix q r (by omega),hwr,hctrl (r+2) (by omega)]
      have hp : noWorkPrefixAnd (fun j => q (c j)) (r+2) =
          noWorkPrefixAnd (fun j => x (c j)) (r+2) :=
        noWorkPrefixAnd_congr _ _ _ (fun j hj => hctrl j (by omega))
      rw [hp, noWorkPrefixAnd_succ (fun j => x (c j)) (r+2)]
      simp only [q,noWorkToffoliUpdate,Function.update_self]
      cases x (w (r+1)) <;> cases x (c (r+2)) <;> cases x (w r) <;>
        cases noWorkPrefixAnd (fun j => x (c j)) (r+2) <;> rfl
    · have hil : i < r+1 := by omega
      have hiw : w i ≠ w (r+1) := fun he => by
        have hv := h.2.1 (show i < r+2 from by omega) (show r+1 < r+2 from by omega) he
        omega
      simp only [noWorkDirtyPrefixTransform,noWorkToffoliUpdate,Function.update_of_ne hiw]
      change noWorkDirtyPrefixTransform c w (r+1) q (w i) = _
      rw [ih hprefix q i hil]
      have hp : noWorkPrefixAnd (fun j => q (c j)) (i+2) =
          noWorkPrefixAnd (fun j => x (c j)) (i+2) :=
        noWorkPrefixAnd_congr _ _ _ (fun j hj => hctrl j (by omega))
      rw [hp]
      congr 1
      exact Function.update_of_ne hiw _ _

/-- Under the layout condition, the dirty-prefix register transformation is an involution. -/
theorem noWorkDirtyPrefixTransform_involutive {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r) :
    Function.Involutive (noWorkDirtyPrefixTransform c w r) := by
  intro x
  funext k
  by_cases hk : ∃ j < r, w j = k
  · obtain ⟨j,hj,rfl⟩ := hk
    rw [noWorkDirtyPrefixTransform_flag c w r h _ j hj,
      noWorkDirtyPrefixTransform_flag c w r h x j hj]
    have hp : noWorkPrefixAnd (fun i => noWorkDirtyPrefixTransform c w r x (c i)) (j+2) =
        noWorkPrefixAnd (fun i => x (c i)) (j+2) :=
      noWorkPrefixAnd_congr _ _ _ (fun i hi =>
        noWorkDirtyPrefixTransform_outside c w r x (c i)
          (fun l hl => h.2.2 i (by omega) l hl))
    rw [hp]
    simp
  · have hout : ∀ j < r, k ≠ w j := by
      intro j hj he
      exact hk ⟨j,hj,he.symm⟩
    rw [noWorkDirtyPrefixTransform_outside c w r _ k hout,
      noWorkDirtyPrefixTransform_outside c w r x k hout]

/-- Under the layout condition, the dirty-prefix transformation commutes with updates to a wire
outside all used controls and dirty wires. -/
theorem noWorkDirtyPrefixTransform_update {N : ℕ} (c w : ℕ → Fin N) (r : ℕ)
    (h : noWorkDirtyPrefixLayout c w r) (t : Fin N)
    (hct : ∀ i < r+1, c i ≠ t) (hwt : ∀ j < r, w j ≠ t)
    (x : Reg N) (b : Bool) :
    noWorkDirtyPrefixTransform c w r (Function.update x t b) =
      Function.update (noWorkDirtyPrefixTransform c w r x) t b := by
  funext k
  by_cases hkt : k = t
  · subst k
    rw [noWorkDirtyPrefixTransform_outside c w r _ t (fun j hj => (hwt j hj).symm)]
    simp
  · rw [Function.update_of_ne hkt]
    by_cases hk : ∃ j < r, w j = k
    · obtain ⟨j,hj,rfl⟩ := hk
      rw [noWorkDirtyPrefixTransform_flag c w r h _ j hj,
        noWorkDirtyPrefixTransform_flag c w r h x j hj,
        Function.update_of_ne hkt]
      congr 1
      exact noWorkPrefixAnd_congr _ _ _ (fun i hi => Function.update_of_ne (hct i (by omega)) _ _)
    · have hout : ∀ j < r, k ≠ w j := by
        intro j hj he
        exact hk ⟨j,hj,he.symm⟩
      rw [noWorkDirtyPrefixTransform_outside c w r _ k hout,
        noWorkDirtyPrefixTransform_outside c w r x k hout,
        Function.update_of_ne hkt]

/-- The gate sequence computing a controlled target toggle using a dirty-prefix computation and
its repeated use. -/
noncomputable def noWorkBorrowedAndSteps {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ) :
    List (ReflectionGate N) :=
  toffoliLocalSteps (c (r+1)) (w (r-1)) t ++ noWorkDirtyPrefixSteps c w r ++
    toffoliLocalSteps (c (r+1)) (w (r-1)) t ++ noWorkDirtyPrefixSteps c w r

/-- For `1 ≤ r`, the borrowed-AND sequence has exactly `60*r` gates. -/
theorem noWorkBorrowedAndSteps_length {N : ℕ} (c w : ℕ → Fin N) (t : Fin N)
    (r : ℕ) (hr : 1 ≤ r) : (noWorkBorrowedAndSteps c w t r).length = 60*r := by
  simp only [noWorkBorrowedAndSteps,List.length_append,toffoliLocalSteps_length,
    noWorkDirtyPrefixSteps_length]
  omega

/-- The borrowed-AND sequence is legal under the stated prefix-layout and wire-separation
conditions with `1 ≤ r`. -/
theorem noWorkBorrowedAndSteps_legal {N : ℕ} (c w : ℕ → Fin N) (t : Fin N)
    (r : ℕ) (hr : 1 ≤ r) (h : noWorkDirtyPrefixLayout c w r)
    (hlast : ∀ j < r, c (r+1) ≠ w j)
    (hct : ∀ i < r+2, c i ≠ t) (hwt : ∀ j < r, w j ≠ t) :
    reflectionLegal (noWorkBorrowedAndSteps c w t r) := by
  have ht := toffoliLocalSteps_legal (c (r+1)) (w (r-1)) t
    (hlast _ (by omega)) (hct _ (by omega)) (hwt _ (by omega))
  have hp := noWorkDirtyPrefixSteps_legal c w r h
  simp only [noWorkBorrowedAndSteps,reflectionLegal_append]
  exact ⟨⟨⟨ht,hp⟩,ht⟩,hp⟩

/-- Under the stated layout and separation conditions, the borrowed-AND sequence toggles the
target by the first `r+2` controls and restores the remaining basis bits. -/
theorem noWorkBorrowedAndSteps_ket {N : ℕ} (c w : ℕ → Fin N) (t : Fin N)
    (r : ℕ) (hr : 1 ≤ r) (h : noWorkDirtyPrefixLayout c w r)
    (hlast : ∀ j < r, c (r+1) ≠ w j)
    (hct : ∀ i < r+2, c i ≠ t) (hwt : ∀ j < r, w j ≠ t) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (noWorkBorrowedAndSteps c w t r)) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) (r+2))) := by
  have ht := (local_toffoli_fifteen_exact N (c (r+1)) (w (r-1)) t
    (hlast _ (by omega)) (hct _ (by omega)) (hwt _ (by omega))).2.2
  have hp := noWorkDirtyPrefixSteps_ket c w r h
  simp only [noWorkBorrowedAndSteps,reflectionCompile_append,run_append]
  rw [ht,hp,ht,hp]
  let F := noWorkDirtyPrefixTransform c w r
  let a := c (r+1)
  let b := w (r-1)
  let q := Function.update x t (x t ^^ (x a && x b))
  change Qatlib.Foundations.PureStateMath.Ket
      (F (Function.update (F q) t ((F q) t ^^ ((F q) a && (F q) b)))) = _
  have hc : ∀ i < r+1, c i ≠ t := fun i hi => hct i (by omega)
  rw [show F (Function.update (F q) t ((F q) t ^^ ((F q) a && (F q) b))) =
      Function.update (F (F q)) t ((F q) t ^^ ((F q) a && (F q) b)) from
    noWorkDirtyPrefixTransform_update c w r h t hc hwt (F q) _]
  change Qatlib.Foundations.PureStateMath.Ket
      (Function.update (F (F q)) t ((F q) t ^^ ((F q) a && (F q) b))) = _
  rw [show F (F q) = q from noWorkDirtyPrefixTransform_involutive c w r h q]
  have hqt : F q t = q t := noWorkDirtyPrefixTransform_outside c w r q t
    (fun j hj => (hwt j hj).symm)
  have hqa : F q a = x a := by
    change noWorkDirtyPrefixTransform c w r q a = x a
    rw [noWorkDirtyPrefixTransform_outside c w r q a hlast]
    exact Function.update_of_ne (hct (r+1) (by omega)) _ _
  have hqb : F q b = (x b ^^ noWorkPrefixAnd (fun i => x (c i)) (r+1)) := by
    change noWorkDirtyPrefixTransform c w r q (w (r-1)) = _
    rw [noWorkDirtyPrefixTransform_flag c w r h q (r-1) (by omega)]
    have hlen : r-1+2 = r+1 := by omega
    rw [hlen, show q (w (r-1)) = x (w (r-1)) from
      Function.update_of_ne (hwt (r-1) (by omega)) _ _]
    congr 1
    exact noWorkPrefixAnd_congr _ _ _ (fun i hi => Function.update_of_ne (hct i (by omega)) _ _)
  rw [hqt,hqa,hqb]
  simp only [q,Function.update_self,Function.update_idem]
  rw [noWorkPrefixAnd_succ (fun i => x (c i)) (r+1)]
  congr 2
  cases x t <;> cases x a <;> cases x b <;>
    cases noWorkPrefixAnd (fun i => x (c i)) (r+1) <;> rfl

/-- Distinct control wires and `m-2` disjoint borrowed wires give a legal `m`-control
target-toggle table of length at most `60*m+1`. -/
theorem noWork_many_borrowed_and_table {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (m : ℕ)
    (hc : Set.InjOn c (Set.Iio m)) (hw : Set.InjOn w (Set.Iio (m-2)))
    (hcw : ∀ i < m, ∀ j < m-2, c i ≠ w j)
    (hct : ∀ i < m, c i ≠ t) (hwt : ∀ j < m-2, w j ≠ t) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧ gs.length ≤ 60*m+1 ∧
      ∀ x : Reg N, Run 1 (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) m)) := by
  rcases m with _ | m
  · refine ⟨knownFlipSteps [t],knownFlipSteps_legal _,by simp [knownFlipSteps],?_⟩
    intro x
    rw [knownFlipSteps_action [t] (by simp)]
    congr 1
    funext k
    by_cases hk : k = t
    · subst k
      simp [noWorkPrefixAnd]
    · simp [hk,noWorkPrefixAnd]
  rcases m with _ | m
  · refine ⟨[.inr (c 0,t)],?_,by simp,?_⟩
    · intro g hg
      obtain rfl := List.mem_singleton.mp hg
      exact hct 0 (by omega)
    · intro x
      simp only [reflectionCompile,List.map_cons,List.map_nil,run_gate,run_nil,reflectionGateMatrix]
      simpa [noWorkPrefixAnd,List.range_succ] using!
          applyGate_cnotGate_ket N (c 0) t (hct 0 (by omega)) x
  rcases m with _ | m
  · have h01 : c 0 ≠ c 1 := fun he => by
      have hh : 0 = 1 := hc (by simp) (by simp) he
      omega
    refine ⟨toffoliLocalSteps (c 0) (c 1) t,
      toffoliLocalSteps_legal _ _ _ h01 (hct 0 (by omega)) (hct 1 (by omega)),?_,?_⟩
    · rw [toffoliLocalSteps_length]
      norm_num
    · intro x
      simpa [noWorkPrefixAnd,List.range_succ] using!
        (local_toffoli_fifteen_exact N _ _ _ h01 (hct 0 (by omega)) (hct 1 (by omega))).2.2 x
  · have hm : m+1+1+1 = (m+1)+2 := by omega
    have hsub : m+1+1+1-2 = m+1 := by omega
    have hprefix : noWorkDirtyPrefixLayout c w (m+1) := by
      refine ⟨?_,?_,?_⟩
      · intro i hi j hj he
        exact hc (show i < m+1+1+1 from by change i < m+1+1 at hi; omega)
          (show j < m+1+1+1 from by change j < m+1+1 at hj; omega) he
      · simpa only [hsub] using! hw
      · intro i hi j hj
        exact hcw i (by omega) j (by omega)
    have hlast : ∀ j < m+1, c (m+1+1) ≠ w j := fun j hj => hcw _ (by omega) j (by omega)
    have htarget : ∀ i < m+1+2, c i ≠ t := fun i hi => hct i (by omega)
    have hwork : ∀ j < m+1, w j ≠ t := fun j hj => hwt j (by omega)
    refine ⟨noWorkBorrowedAndSteps c w t (m+1),
      noWorkBorrowedAndSteps_legal c w t (m+1) (by omega) hprefix hlast htarget hwork,?_,?_⟩
    · rw [noWorkBorrowedAndSteps_length _ _ _ _ (by omega)]
      omega
    · intro x
      simpa only [hm] using!
        noWorkBorrowedAndSteps_ket c w t (m+1) (by omega) hprefix hlast htarget hwork x

/-- A conjunction over a concatenated prefix factors into the conjunctions over its two
consecutive parts. -/
private theorem noWorkPrefixAnd_add (c : ℕ → Bool) (a b : ℕ) :
    noWorkPrefixAnd c (a+b) = (noWorkPrefixAnd c a && noWorkPrefixAnd (fun i => c (a+i)) b) := by
  simp [noWorkPrefixAnd,List.range_add,List.all_map,Function.comp_def]

/-- Updating a wire outside the control prefix leaves the prefix conjunction unchanged. -/
private theorem noWorkPrefixAnd_update {N : ℕ} (c : ℕ → Fin N) (m : ℕ)
    (t : Fin N) (hct : ∀ i < m, c i ≠ t) (x : Reg N) (b : Bool) :
    noWorkPrefixAnd (fun i => Function.update x t b (c i)) m =
      noWorkPrefixAnd (fun i => x (c i)) m :=
  noWorkPrefixAnd_congr _ _ _ (fun i hi => Function.update_of_ne (hct i hi) _ _)

/-- Alternating the specified toggle tables as `as ++ bs ++ as ++ bs` toggles the target by `A x
&& B x` and restores the borrowed wire, under the stated update-invariance assumptions. -/
theorem noWork_dirty_and_combine {N : ℕ} (s t : Fin N) (hst : s ≠ t)
    (A B : Reg N → Bool)
    (ha : ∀ (x : Reg N) (v : Bool), A (Function.update x s v) = A x ∧
      A (Function.update x t v) = A x)
    (hb : ∀ (x : Reg N) (v : Bool), B (Function.update x s v) = B x ∧
      B (Function.update x t v) = B x)
    (as bs : List (ReflectionGate N))
    (has : ∀ x : Reg N, Run 1 (reflectionCompile as) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x s (x s ^^ A x)))
    (hbs : ∀ x : Reg N, Run 1 (reflectionCompile bs) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (B x && x s)))) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (as ++ bs ++ as ++ bs)) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (A x && B x))) := by
  simp only [reflectionCompile_append,run_append]
  rw [has,hbs,has,hbs]
  simp only [(ha _ _).1,(ha _ _).2,(hb _ _).1,(hb _ _).2,
    Function.update_self,Function.update_of_ne hst,Function.update_of_ne hst.symm]
  congr 1
  funext k
  by_cases hkt : k = t
  · subst k
    simp only [Function.update_self]
    cases A x <;> cases B x <;> cases x s <;> cases x t <;> rfl
  · by_cases hks : k = s
    · subst k
      simp [Function.update_of_ne hkt]
    · simp [Function.update_of_ne hkt,Function.update_of_ne hks]

/-- With one borrowed wire disjoint from the controls and target, an `m`-control toggle has a
legal table of length at most `120*(m+1)+4`. -/
theorem noWork_single_dirty_and_table {N : ℕ} (c : ℕ → Fin N) (s t : Fin N) (m : ℕ)
    (hc : Set.InjOn c (Set.Iio m)) (hcs : ∀ i < m, c i ≠ s)
    (hct : ∀ i < m, c i ≠ t) (hst : s ≠ t) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧ gs.length ≤ 120*(m+1)+4 ∧
      ∀ x : Reg N, Run 1 (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) m)) := by
  by_cases hm : m ≤ 2
  · obtain ⟨gs,hgs,hlen,hrun⟩ := noWork_many_borrowed_and_table c (fun _ => s) t m hc
      (by intro i hi; change i < m-2 at hi; omega)
      (by intro i hi j hj; omega) hct (by intro j hj; omega)
    exact ⟨gs,hgs,hlen.trans (by omega),hrun⟩
  · let a := (m+1)/2
    let b := m/2
    have hab : a+b = m := by dsimp [a,b]; omega
    have ha : 2 ≤ a := by dsimp [a]; omega
    have hb : 1 ≤ b := by dsimp [b]; omega
    have hbal : b ≤ a ∧ a ≤ b+1 := by dsimp [a,b]; omega
    have hne (i j : ℕ) (hi : i < m) (hj : j < m) (hij : i ≠ j) : c i ≠ c j :=
      fun he => hij (hc hi hj he)
    let ca : ℕ → Fin N := c
    let wa : ℕ → Fin N := fun j => c (a+j)
    have hca : Set.InjOn ca (Set.Iio a) := by
      intro i hi j hj he
      exact hc (show i < m from by change i < a at hi; omega)
        (show j < m from by change j < a at hj; omega) he
    have hwa : Set.InjOn wa (Set.Iio (a-2)) := by
      intro i hi j hj he
      have hv : a+i = a+j := hc
        (show a+i < m from by change i < a-2 at hi; omega)
        (show a+j < m from by change j < a-2 at hj; omega) he
      omega
    have hcawa : ∀ i < a, ∀ j < a-2, ca i ≠ wa j := by
      intro i hi j hj
      exact hne i (a+j) (by omega) (by omega) (by omega)
    obtain ⟨as,has,halen,hrA⟩ := noWork_many_borrowed_and_table ca wa s a hca hwa hcawa
      (fun i hi => hcs i (by omega)) (fun j hj => hcs (a+j) (by omega))
    let cb : ℕ → Fin N := fun i => if i < b then c (a+i) else s
    let wb : ℕ → Fin N := c
    have hcb : Set.InjOn cb (Set.Iio (b+1)) := by
      intro i hi j hj he
      change i < b+1 at hi
      change j < b+1 at hj
      by_cases hib : i < b <;> by_cases hjb : j < b
      · simp only [cb,if_pos hib,if_pos hjb] at he
        have hv : a+i = a+j := hc (show a+i < m from by omega) (show a+j < m from by omega) he
        omega
      · simp only [cb,if_pos hib,if_neg hjb] at he
        exact (hcs (a+i) (by omega) he).elim
      · simp only [cb,if_neg hib,if_pos hjb] at he
        exact (hcs (a+j) (by omega) he.symm).elim
      · omega
    have hwb : Set.InjOn wb (Set.Iio (b+1-2)) := by
      intro i hi j hj he
      exact hc (show i < m from by change i < b+1-2 at hi; omega)
        (show j < m from by change j < b+1-2 at hj; omega) he
    have hcbwb : ∀ i < b+1, ∀ j < b+1-2, cb i ≠ wb j := by
      intro i hi j hj
      by_cases hib : i < b
      · simp only [cb,if_pos hib,wb]
        exact hne (a+i) j (by omega) (by omega) (by omega)
      · simp only [cb,if_neg hib,wb]
        exact (hcs j (by omega)).symm
    have hcbt : ∀ i < b+1, cb i ≠ t := by
      intro i hi
      by_cases hib : i < b
      · simpa only [cb,if_pos hib] using! hct (a+i) (by omega)
      · simpa only [cb,if_neg hib] using! hst
    obtain ⟨bs,hbs,hblen,hrB⟩ := noWork_many_borrowed_and_table cb wb t (b+1)
      hcb hwb hcbwb hcbt (fun j hj => hct j (by omega))
    let A : Reg N → Bool := fun x => noWorkPrefixAnd (fun i => x (c i)) a
    let B : Reg N → Bool := fun x => noWorkPrefixAnd (fun i => x (c (a+i))) b
    have hA (x : Reg N) (v : Bool) : A (Function.update x s v) = A x ∧
        A (Function.update x t v) = A x :=
      ⟨noWorkPrefixAnd_update c a s (fun i hi => hcs i (by omega)) x v,
        noWorkPrefixAnd_update c a t (fun i hi => hct i (by omega)) x v⟩
    have hB (x : Reg N) (v : Bool) : B (Function.update x s v) = B x ∧
        B (Function.update x t v) = B x :=
      ⟨noWorkPrefixAnd_update (fun i => c (a+i)) b s (fun i hi => hcs (a+i) (by omega)) x v,
        noWorkPrefixAnd_update (fun i => c (a+i)) b t (fun i hi => hct (a+i) (by omega)) x v⟩
    have hBtable (x : Reg N) : Run 1 (reflectionCompile bs) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (B x && x s))) := by
      rw [hrB]
      congr 2
      rw [noWorkPrefixAnd_succ]
      have hp : noWorkPrefixAnd (fun i => x (cb i)) b = B x :=
        noWorkPrefixAnd_congr _ _ _ (fun i hi => by simp only [cb,if_pos hi])
      rw [hp]
      simp [cb]
    refine ⟨as ++ bs ++ as ++ bs,?_,?_,?_⟩
    · simp only [reflectionLegal_append]
      exact ⟨⟨⟨has,hbs⟩,has⟩,hbs⟩
    · simp only [List.length_append]
      omega
    · intro x
      rw [noWork_dirty_and_combine s t hst A B hA hB as bs hrA hBtable x]
      congr 2
      rw [← hab,noWorkPrefixAnd_add]

/-- Running a compiled reflection-gate list commutes with addition of states. -/
private theorem noWork_run_add {N : ℕ} (gs : List (ReflectionGate N))
    (ψ φ : QState (Reg N)) : Run 1 (reflectionCompile gs) (ψ+φ) =
      Run 1 (reflectionCompile gs) ψ + Run 1 (reflectionCompile gs) φ := by
  simp only [run_reflectionCompile,ApplyGate,Matrix.mulVec_add]

/-- A basis-correct AND-toggle table preserves an arbitrary superposition on a separate wire
outside the controls. -/
theorem noWork_and_table_wireState {N : ℕ} (c : ℕ → Fin N) (m : ℕ)
    (s t : Fin N) (hst : s ≠ t) (hct : ∀ i < m, c i ≠ t)
    (gs : List (ReflectionGate N))
    (hgs : ∀ x : Reg N, Run 1 (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x s (x s ^^ noWorkPrefixAnd (fun i => x (c i)) m)))
    (x : Reg N) (φ : QState Bool) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs) (multiWireState t x φ) =
      multiWireState t (Function.update x s (x s ^^ noWorkPrefixAnd (fun i => x (c i)) m)) φ := by
  have he (v : Bool) :
      Function.update (Function.update x t v) s
        ((Function.update x t v) s ^^ noWorkPrefixAnd (fun i => Function.update x t v (c i)) m) =
      Function.update (Function.update x s (x s ^^ noWorkPrefixAnd (fun i => x (c i)) m)) t v := by
    rw [Function.update_of_ne hst,noWorkPrefixAnd_update c m t hct]
    exact Function.update_comm hst.symm _ _ x
  simp only [multiWireState,noWork_run_add,run_reflectionCompile_smul,hgs,he]

/-- A unitary on a target wire controlled by `m` distinct other wires has an exact legal table
of length at most `256*(m+1)^2`. -/
theorem noWork_multi_control_wire_table {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (hc : Set.InjOn c (Set.Iio m)) (hct : ∀ i < m, c i ≠ t)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧ gs.length ≤ 256*(m+1)^2 ∧
      ∀ (x : Reg N) (φ : QState Bool),
        Run 1 (reflectionCompile gs) (multiWireState t x φ) =
          multiWireState t x (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then U else 1) φ) := by
  induction m generalizing U with
  | zero =>
    refine ⟨[.inl (t,U)],?_,by simp,?_⟩
    · intro g hg
      obtain rfl := List.mem_singleton.mp hg
      exact hU
    · intro x φ
      simp only [reflectionCompile,List.map_cons,List.map_nil,run_gate,run_nil,reflectionGateMatrix]
      simpa [noWorkPrefixAnd] using! multiWireState_single t x U φ
  | succ m ih =>
    obtain ⟨V,hV,hVV⟩ := noWork_unitary_square_root U hU
    let p := knownQubitAnglesOfUnitary V
    have hp : knownQubitUnitary p = V := (knownQubitEuler_explicit_angles_cover_unitaries V hV).1
    let padj := knownQubitAngleAdjoint p
    have hpadj : knownQubitUnitary padj = Vᴴ := by rw [knownQubitUnitary_adjoint,hp]
    have hcm : Set.InjOn c (Set.Iio m) := by
      intro i hi j hj he
      exact hc (show i < m+1 from by change i < m at hi; omega)
        (show j < m+1 from by change j < m at hj; omega) he
    have hctm : ∀ i < m, c i ≠ t := fun i hi => hct i (by omega)
    have hccl : ∀ i < m, c i ≠ c m := fun i hi he => by
      have hv : i = m := hc (show i < m+1 from by omega) (show m < m+1 from by omega) he
      omega
    have hlast : c m ≠ t := hct m (by omega)
    obtain ⟨xs,hxs,hxlen,hx⟩ := noWork_single_dirty_and_table c t (c m) m
      hcm hctm hccl hlast.symm
    obtain ⟨rs,hrs,hrlen,hr⟩ := ih hcm hctm V hV
    let vs := multiKnownPairSteps (c m) t p
    let ds := multiKnownPairSteps (c m) t padj
    have hvs : reflectionLegal vs := multiKnownPairSteps_legal _ _ hlast p
    have hds : reflectionLegal ds := multiKnownPairSteps_legal _ _ hlast padj
    have hvlen : vs.length = 6 := rfl
    have hdlen : ds.length = 6 := rfl
    refine ⟨vs ++ xs ++ ds ++ xs ++ rs,?_,?_,?_⟩
    · simp only [reflectionLegal_append]
      exact ⟨⟨⟨⟨hvs,hxs⟩,hds⟩,hxs⟩,hrs⟩
    · simp only [List.length_append,hvlen,hdlen]
      nlinarith
    · intro x φ
      let a := noWorkPrefixAnd (fun i => x (c i)) m
      let q := Function.update x (c m) (x (c m) ^^ a)
      have hA : noWorkPrefixAnd (fun i => q (c i)) m = a :=
        noWorkPrefixAnd_update c m (c m) hccl x _
      have hq : q (c m) = (x (c m) ^^ a) := Function.update_self _ _ _
      have hrestore : Function.update q (c m)
          (q (c m) ^^ noWorkPrefixAnd (fun i => q (c i)) m) = x := by
        rw [hA,hq]
        simp [q]
      simp only [reflectionCompile_append,run_append]
      rw [multiKnownPairSteps_action (c m) t hlast p,hp,
        noWork_and_table_wireState c m (c m) t hlast hctm xs hx,
        multiKnownPairSteps_action (c m) t hlast padj,hpadj]
      change Run 1 (reflectionCompile rs)
        (Run 1 (reflectionCompile xs)
          (multiWireState t q (ApplyGate (if q (c m) then Vᴴ else 1)
            (ApplyGate (if x (c m) then V else 1) φ)))) = _
      rw [noWork_and_table_wireState c m (c m) t hlast hctm xs hx,hrestore,hr,hq]
      rw [noWorkPrefixAnd_succ]
      change multiWireState t x (ApplyGate (if a then V else 1)
        (ApplyGate (if x (c m) ^^ a then Vᴴ else 1)
          (ApplyGate (if x (c m) then V else 1) φ))) =
        multiWireState t x (ApplyGate (if (a && x (c m)) then U else 1) φ)
      cases a <;> cases x (c m) <;> simp [applyGate_one]
      · rw [← applyGate_mul,show Vᴴ * V = 1 from hV.1,applyGate_one]
      · rw [← applyGate_mul,show V * Vᴴ = 1 from hV.2,applyGate_one]
      · rw [← applyGate_mul,hVV]

/-- Selects the initial control wires in a register containing controls, a target, and `k`
additional wires. -/
noncomputable def noWorkControlWires (n k : ℕ) : ℕ → Fin (n+1+k) :=
  fun i => if h : i < n then ⟨i,by omega⟩ else ⟨n,by omega⟩

/-- The selected control wires are injective on indices below `n`. -/
private theorem noWorkControlWires_inj (n k : ℕ) :
    Set.InjOn (noWorkControlWires n k) (Set.Iio n) := by
  intro i hi j hj he
  change i < n at hi
  change j < n at hj
  simpa only [noWorkControlWires,dif_pos hi,dif_pos hj] using! congrArg Fin.val he

/-- Every selected control wire with index below `n` differs from the target wire. -/
private theorem noWorkControlWires_ne_target (n k : ℕ) (i : ℕ) (hi : i < n) :
    noWorkControlWires n k i ≠ (⟨n,by omega⟩ : Fin (n+1+k)) := by
  intro he
  have hv := congrArg Fin.val he
  simp only [noWorkControlWires,dif_pos hi] at hv
  omega

/-- The conjunction on the selected wires of a joined register equals `allControlTrue` on its
control register. -/
private theorem noWork_prefix_allControl (n : ℕ) (x : Reg n) (b : Bool) :
    noWorkPrefixAnd (fun i => (noWorkControlSplit n).symm (x,b) (noWorkControlWires n 0 i)) n =
      allControlTrue n x := by
  have hcoord (i : ℕ) (hi : i < n) :
      (noWorkControlSplit n).symm (x,b) (noWorkControlWires n 0 i) = x ⟨i,hi⟩ := by
    rw [noWorkControlSplit_symm_data]
    simp only [noWorkControlWires,dif_pos hi]
    exact knownDataEquiv_control n x b ⟨i,hi⟩
  rw [allControlTrue_eq_decide]
  apply Bool.eq_iff_iff.mpr
  simp only [noWorkPrefixAnd,List.all_eq_true,List.mem_range,decide_eq_true_eq]
  constructor
  · intro hall i
    have hh := hall i.val i.isLt
    simpa only [hcoord i.val i.isLt] using! hh
  · intro hall i hi
    rw [hcoord i hi]
    exact hall _

/-- An `n`-controlled one-qubit unitary has an exact legal implementation without work qubits
using at most `256*(n+1)^2` gates and no queries; the gate count equals the table length.
See [BarencoEtAl1995] for elementary controlled-gate synthesis. -/
theorem no_work_multi_unitary_control_local_table_and_cost (n : ℕ)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate (n+1)), reflectionLegal gs ∧ gs.length ≤ 256*(n+1)^2 ∧
      QueryCount (reflectionCompile gs) = 0 ∧ GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n × Bool),
        Run 1 (reflectionCompile gs) (relabelState (noWorkControlSplit n).symm ψ) =
          relabelState (noWorkControlSplit n).symm (multiKnownGate n U *ᵥ ψ) := by
  obtain ⟨gs,hgs,hlen,hr⟩ := noWork_multi_control_wire_table n (noWorkControlWires n 0)
    (Fin.last n) (noWorkControlWires_inj n 0)
    (fun i hi => noWorkControlWires_ne_target n 0 i hi)
    U hU
  have hb (x : Reg n) (b : Bool) :
      Run 1 (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket ((noWorkControlSplit n).symm (x,b))) =
        ∑ a : Bool, (if allControlTrue n x then U else 1) a b •
          Qatlib.Foundations.PureStateMath.Ket ((noWorkControlSplit n).symm (x,a)) := by
    let q := (noWorkControlSplit n).symm (x,b)
    have ht : q (Fin.last n) = b := by
      change (noWorkControlSplit n).symm (x,b) (Fin.last n) = b
      rw [noWorkControlSplit_symm_data]
      exact knownDataEquiv_target n x b
    have hk := multiWireState_ket (Fin.last n) q
    rw [ht] at hk
    rw [← hk,hr,noWork_prefix_allControl,noWorkControlJoin_wireState]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    simp [ApplyGate,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket]
  refine ⟨gs,hgs,hlen,queryCount_reflectionCompile _,gateCount_reflectionCompile _,?_⟩
  intro ψ
  conv_lhs => arg 3; arg 2; rw [state_ket_expansion ψ]
  rw [noWork_relabel_sum,run_reflectionCompile_sum]
  conv_rhs => arg 2; arg 2; rw [state_ket_expansion ψ]
  rw [Matrix.mulVec_sum,noWork_relabel_sum]
  apply Finset.sum_congr rfl
  intro ⟨x,b⟩ _
  rw [noWork_relabel_smul,noWork_relabel_ket,run_reflectionCompile_smul,hb,
    Matrix.mulVec_smul,noWork_relabel_smul]
  change _ = _ • relabelState _ (ApplyGate _ (Qatlib.Foundations.PureStateMath.Ket (x,b)))
  rw [multiKnownGate_ket,noWork_relabel_sum]
  simp only [noWork_relabel_smul,noWork_relabel_ket]

/-- An `n`-controlled known one-qubit unitary has an exact legal implementation without work
qubits, with at most `256*(n+1)^2` gates, no queries, and gate count equal to table length. -/
theorem no_work_multi_known_control_local_table_and_cost (n : ℕ) (p : KnownQubitAngles) :
    ∃ gs : List (ReflectionGate (n+1)), reflectionLegal gs ∧ gs.length ≤ 256*(n+1)^2 ∧
      QueryCount (reflectionCompile gs) = 0 ∧ GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n × Bool),
        Run 1 (reflectionCompile gs) (relabelState (noWorkControlSplit n).symm ψ) =
          relabelState (noWorkControlSplit n).symm (multiKnownGate n (knownQubitUnitary p) *ᵥ ψ) := by
  exact no_work_multi_unitary_control_local_table_and_cost n
    (knownQubitUnitary p) (knownQubitUnitary_unitary p)

/-- A known unitary controlled by `m` distinct wires has an exact legal table of length at most
`720*(m+1)+6` on states whose separate ancillary wire is false, preserving that wire. -/
private theorem noWork_single_clean_wire_table {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (s t : Fin N)
    (hc : Set.InjOn c (Set.Iio m)) (hcs : ∀ i < m, c i ≠ s)
    (hct : ∀ i < m, c i ≠ t) (hst : s ≠ t) (p : KnownQubitAngles) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧ gs.length ≤ 720*(m+1)+6 ∧
      ∀ (x : Reg N), x s = false → ∀ φ : QState Bool,
        Run 1 (reflectionCompile gs) (multiWireState t x φ) =
          multiWireState t x (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then
            knownQubitUnitary p else 1) φ) := by
  obtain ⟨as,has,halen,ha⟩ := noWork_single_dirty_and_table c t s m hc hct hcs hst.symm
  let bs := multiKnownPairSteps s t p
  have hbs := multiKnownPairSteps_legal s t hst p
  refine ⟨as ++ bs ++ as,?_,?_,?_⟩
  · simp only [reflectionLegal_append]
    exact ⟨⟨has,hbs⟩,has⟩
  · have hblen : bs.length = 6 := rfl
    simp only [List.length_append,hblen]
    omega
  · intro x hxs φ
    let a := noWorkPrefixAnd (fun i => x (c i)) m
    let q := Function.update x s (x s ^^ a)
    have hq : q s = a := by simp [q,hxs]
    have hA : noWorkPrefixAnd (fun i => q (c i)) m = a :=
      noWorkPrefixAnd_update c m s hcs x _
    have hrestore : Function.update q s (q s ^^ noWorkPrefixAnd (fun i => q (c i)) m) = x := by
      rw [hA,hq]
      simp only [Bool.xor_self]
      dsimp only [q]
      rw [Function.update_idem]
      rw [← hxs]
      exact Function.update_eq_self s x
    simp only [reflectionCompile_append,run_append]
    rw [noWork_and_table_wireState c m s t hst hct as ha,
      multiKnownPairSteps_action s t hst p]
    change Run 1 (reflectionCompile as)
      (multiWireState t q (ApplyGate (if q s then knownQubitUnitary p else 1) φ)) = _
    rw [noWork_and_table_wireState c m s t hst hct as ha,hrestore,hq]

/-- Joining controls, target, and ancillary register recovers each control bit on its designated
wire. -/
@[simp] theorem singleAncillaJoin_control (n : ℕ) (x : Reg n) (b : Bool)
    (v : Reg 1) (i : Fin n) :
    (singleAncillaSplit n).symm ((x,b),v) ⟨i.val,by omega⟩ = x i :=
  congrArg (fun z => z.1.1 i) ((singleAncillaSplit n).apply_symm_apply ((x,b),v))

/-- Joining controls, target, and ancillary register places the target bit on wire `n`. -/
@[simp] theorem singleAncillaJoin_target (n : ℕ) (x : Reg n) (b : Bool) (v : Reg 1) :
    (singleAncillaSplit n).symm ((x,b),v) ⟨n,by omega⟩ = b :=
  congrArg (fun z => z.1.2) ((singleAncillaSplit n).apply_symm_apply ((x,b),v))

/-- Joining controls, target, and ancillary register places the ancillary bit on wire `n+1`. -/
@[simp] theorem singleAncillaJoin_ancilla (n : ℕ) (x : Reg n) (b : Bool) (v : Reg 1) :
    (singleAncillaSplit n).symm ((x,b),v) ⟨n+1,by omega⟩ = v 0 :=
  congrArg (fun z => z.2 (0 : Fin 1)) ((singleAncillaSplit n).apply_symm_apply ((x,b),v))

/-- Updating the target wire of a joined register changes only the target component. -/
private theorem singleAncillaJoin_update_target (n : ℕ) (x : Reg n) (b a : Bool) (v : Reg 1) :
    Function.update ((singleAncillaSplit n).symm ((x,b),v)) (⟨n,by omega⟩ : Fin (n+1+1)) a =
      (singleAncillaSplit n).symm ((x,a),v) := by
  funext k
  have hk : k.val < n ∨ k.val = n ∨ k.val = n+1 := by omega
  rcases hk with hk | hk | hk
  · let i : Fin n := ⟨k.val,hk⟩
    have he : k = (⟨i.val,by omega⟩ : Fin (n+1+1)) := Fin.ext rfl
    rw [he,Function.update_of_ne (by intro h; have hv := congrArg Fin.val h; dsimp at hv; omega)]
    simp
  · have he : k = (⟨n,by omega⟩ : Fin (n+1+1)) := Fin.ext hk
    rw [he,Function.update_self,singleAncillaJoin_target]
  · have he : k = (⟨n+1,by omega⟩ : Fin (n+1+1)) := Fin.ext hk
    rw [he,Function.update_of_ne (by intro h; have hv := congrArg Fin.val h; dsimp at hv; omega)]
    simp

/-- A target-wire superposition in the joined register expands over the two possible target bits
with fixed controls and ancillary register. -/
private theorem singleAncillaJoin_wireState (n : ℕ) (x : Reg n) (b : Bool) (v : Reg 1)
    (φ : QState Bool) :
    multiWireState (⟨n,by omega⟩ : Fin (n+1+1)) ((singleAncillaSplit n).symm ((x,b),v)) φ =
      ∑ a : Bool, φ a • Qatlib.Foundations.PureStateMath.Ket ((singleAncillaSplit n).symm ((x,a),v)) := by
  simp only [multiWireState,singleAncillaJoin_update_target,Fintype.sum_bool]
  exact add_comm _ _

/-- Embedding a basis ket appends a false ancillary bit under `singleAncillaSplit`. -/
@[simp] theorem singleAncillaEmbed_ket (n : ℕ) (x : Reg n × Bool) :
    singleAncillaEmbed n (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket ((singleAncillaSplit n).symm (x,fun _ => false)) := by
  rw [singleAncillaEmbed,tensorState_ket_ket,noWork_relabel_ket]

/-- Embedding with one false ancillary bit commutes with scalar multiplication. -/
@[simp] theorem singleAncillaEmbed_smul (n : ℕ) (z : ℂ) (ψ : QState (Reg n × Bool)) :
    singleAncillaEmbed n (z • ψ) = z • singleAncillaEmbed n ψ := by
  funext x
  simp [singleAncillaEmbed,relabelState,TensorState,mul_assoc]

/-- Embedding with one false ancillary bit commutes with finite sums. -/
private theorem singleAncillaEmbed_sum {J : Type} [Fintype J] (n : ℕ)
    (φ : J → QState (Reg n × Bool)) : singleAncillaEmbed n (∑ j,φ j) = ∑ j,singleAncillaEmbed n (φ j) := by
  funext x
  simp [singleAncillaEmbed,relabelState,TensorState,Finset.sum_mul]

/-- The one-ancillary-qubit embedding equals the prefix-wire embedding after control-target
relabeling. -/
private theorem singleAncillaEmbed_wire (n : ℕ) (ψ : QState (Reg n × Bool)) :
    singleAncillaEmbed n ψ = knownWireEmbed (knownPrefixWires (n+1) 1)
      (relabelState (noWorkControlSplit n).symm ψ) := by
  conv_lhs => arg 2; rw [state_ket_expansion ψ]
  rw [singleAncillaEmbed_sum]
  conv_rhs => arg 2; arg 2; rw [state_ket_expansion ψ]
  rw [noWork_relabel_sum,knownWireEmbed_sum]
  simp only [singleAncillaEmbed_smul,singleAncillaEmbed_ket,noWork_relabel_smul,
    noWork_relabel_ket,knownWireEmbed_smul,knownWireEmbed_ket,knownWireExtend_prefix]
  rfl

/-- A legal control-target implementation with the stated linear bound lifts to a query-free
implementation on the one-ancillary-qubit embedding with the same bound and exact action. -/
private theorem singleAncilla_small_table (n : ℕ) (p : KnownQubitAngles)
    (gs : List (ReflectionGate (n+1))) (hgs : reflectionLegal gs)
    (hlen : gs.length ≤ 720*(n+1)+6)
    (hr : ∀ ψ : QState (Reg n × Bool), Run 1 (reflectionCompile gs)
      (relabelState (noWorkControlSplit n).symm ψ) =
        relabelState (noWorkControlSplit n).symm (multiKnownGate n (knownQubitUnitary p) *ᵥ ψ)) :
    ∃ fs : List (ReflectionGate (n+1+1)), reflectionLegal fs ∧ fs.length ≤ 720*(n+1)+6 ∧
      QueryCount (reflectionCompile fs) = 0 ∧ GateCount (reflectionCompile fs) = fs.length ∧
      ∀ ψ : QState (Reg n × Bool), Run 1 (reflectionCompile fs) (singleAncillaEmbed n ψ) =
        singleAncillaEmbed n (multiKnownGate n (knownQubitUnitary p) *ᵥ ψ) := by
  let e := knownPrefixWires (n+1) 1
  let fs := gs.map (knownWireGateMap e)
  refine ⟨fs,knownWireMapList_legal e gs hgs,?_,queryCount_reflectionCompile _,
    gateCount_reflectionCompile _,?_⟩
  · simpa only [fs,List.length_map] using! hlen
  · intro ψ
    rw [singleAncillaEmbed_wire,knownWireProgram_embed e gs hgs,hr,← singleAncillaEmbed_wire]

/-- An `n`-controlled known one-qubit unitary has an exact legal implementation using one false
ancillary qubit, at most `720*(n+1)+6` gates, and no queries, restoring the ancillary qubit. -/
theorem single_ancilla_known_control_local_table_and_cost (n : ℕ) (p : KnownQubitAngles) :
    ∃ gs : List (ReflectionGate (n+1+1)), reflectionLegal gs ∧ gs.length ≤ 720*(n+1)+6 ∧
      QueryCount (reflectionCompile gs) = 0 ∧ GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n × Bool), Run 1 (reflectionCompile gs) (singleAncillaEmbed n ψ) =
        singleAncillaEmbed n (multiKnownGate n (knownQubitUnitary p) *ᵥ ψ) := by
  by_cases hn0 : n = 0
  · subst n
    obtain ⟨gs,hgs,hlen,_,_,hr⟩ := noWork_zero_control_table p
    exact singleAncilla_small_table 0 p gs hgs (by omega) hr
  by_cases hn1 : n = 1
  · subst n
    obtain ⟨gs,hgs,hlen,_,_,hr⟩ := noWork_one_control_table p
    exact singleAncilla_small_table 1 p gs hgs (by omega) hr
  let c := noWorkControlWires n 1
  let s : Fin (n+1+1) := ⟨n+1,by omega⟩
  let t : Fin (n+1+1) := ⟨n,by omega⟩
  have hcs : ∀ i < n, c i ≠ s := by
    intro i hi he
    have hv := congrArg Fin.val he
    simp only [c,noWorkControlWires,dif_pos hi,s] at hv
    omega
  have hst : s ≠ t := by intro he; have hv := congrArg Fin.val he; dsimp [s,t] at hv; omega
  obtain ⟨gs,hgs,hlen,hr⟩ := noWork_single_clean_wire_table n c s t
    (noWorkControlWires_inj n 1) hcs (noWorkControlWires_ne_target n 1) hst p
  have hb (x : Reg n) (b : Bool) :
      Run 1 (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket ((singleAncillaSplit n).symm ((x,b),fun _ => false))) =
        ∑ a : Bool, (if allControlTrue n x then knownQubitUnitary p else 1) a b •
          Qatlib.Foundations.PureStateMath.Ket ((singleAncillaSplit n).symm ((x,a),fun _ => false)) := by
    let q := (singleAncillaSplit n).symm ((x,b),fun _ => false)
    have ht : q t = b := singleAncillaJoin_target n x b _
    have hs : q s = false := singleAncillaJoin_ancilla n x b _
    have hA : noWorkPrefixAnd (fun i => q (c i)) n = allControlTrue n x := by
      rw [allControlTrue_eq_decide]
      apply Bool.eq_iff_iff.mpr
      simp only [noWorkPrefixAnd,List.all_eq_true,List.mem_range,decide_eq_true_eq]
      have hcoord (i : ℕ) (hi : i < n) : q (c i) = x ⟨i,hi⟩ := by
        simp only [q,c,noWorkControlWires,dif_pos hi]
        exact singleAncillaJoin_control n x b _ ⟨i,hi⟩
      constructor
      · intro hall i
        have hh := hall i.val i.isLt
        simpa only [hcoord i.val i.isLt] using! hh
      · intro hall i hi
        rw [hcoord i hi]
        exact hall _
    have hk := multiWireState_ket t q
    rw [ht] at hk
    rw [← hk,hr q hs,hA,singleAncillaJoin_wireState]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    simp [ApplyGate,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket]
  refine ⟨gs,hgs,hlen,queryCount_reflectionCompile _,gateCount_reflectionCompile _,?_⟩
  intro ψ
  conv_lhs => arg 3; arg 2; rw [state_ket_expansion ψ]
  rw [singleAncillaEmbed_sum,run_reflectionCompile_sum]
  conv_rhs => arg 2; arg 2; rw [state_ket_expansion ψ]
  rw [Matrix.mulVec_sum,singleAncillaEmbed_sum]
  apply Finset.sum_congr rfl
  intro ⟨x,b⟩ _
  rw [singleAncillaEmbed_smul,singleAncillaEmbed_ket,run_reflectionCompile_smul,hb,
    Matrix.mulVec_smul,singleAncillaEmbed_smul]
  change _ = _ • singleAncillaEmbed n
      (ApplyGate _ (Qatlib.Foundations.PureStateMath.Ket (x,b)))
  rw [multiKnownGate_ket,singleAncillaEmbed_sum]
  simp only [singleAncillaEmbed_smul,singleAncillaEmbed_ket]

/-- A two-level unitary on the canonical controlled pair has an exact legal table of length at
most `256*(k+1)^2` without extra wires. -/
private theorem noWorkCanonicalPair_table (k : ℕ) (B : Matrix Bool Bool ℂ)
    (hB : B ∈ unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧ gs.length ≤ 256*(k+1)^2 ∧
      ∀ ψ : QState (Reg (k+1)), Run 1 (reflectionCompile gs) ψ =
        twoLevelMatrix (.pair (knownControlAddress k false) (knownControlAddress k true) B) *ᵥ ψ := by
  obtain ⟨gs,hgs,hlen,_,_,hr⟩ :=
    no_work_multi_unitary_control_local_table_and_cost k B hB
  refine ⟨gs,hgs,hlen,?_⟩
  intro ψ
  let φ := relabelState (knownDataEquiv k).symm ψ
  have hφ : relabelState (knownDataEquiv k) φ = ψ := by
    funext u
    simp [φ,relabelState]
  rw [noWorkControlSplit_symm_data] at hr
  rw [← hφ,hr,knownCanonicalPair_action]

/-- A unitary two-level block on distinct `(k+1)`-bit addresses has an exact legal table of
length at most `768*(k+2)^3`. -/
private theorem noWorkPair_table (k : ℕ) (x y : Reg (k+1)) (hxy : x ≠ y)
    (B : Matrix Bool Bool ℂ) (hB : B ∈ unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧ gs.length ≤ 768*(k+2)^3 ∧
      ∀ ψ : QState (Reg (k+1)), Run 1 (reflectionCompile gs) ψ = twoLevelMatrix (.pair x y B) *ᵥ ψ := by
  obtain ⟨t,ht⟩ : ∃ t, x t ≠ y t := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  obtain ⟨as,has,halen,hax,hay⟩ := knownPairAddress_program k x y t ht
  obtain ⟨bs,hbs,hblen,hb⟩ := noWorkCanonicalPair_table k B hB
  let rs := reflectionAdjoint as
  have hrs : reflectionLegal rs := reflectionAdjoint_legal as has
  let A := reflectionProgramMatrix as
  have hA : A ∈ unitaryGroup (Reg (k+1)) ℂ := reflectionProgramMatrix_unitary as has
  have hpq : knownControlAddress k false ≠ knownControlAddress k true := by
    intro he
    have hh := congrFun he (Fin.last k)
    simp [knownControlAddress] at hh
  have hx : A *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket (knownControlAddress k false) := by
    simpa only [run_reflectionCompile,ApplyGate] using! hax
  have hy : A *ᵥ Qatlib.Foundations.PureStateMath.Ket y = Qatlib.Foundations.PureStateMath.Ket (knownControlAddress k true) := by
    simpa only [run_reflectionCompile,ApplyGate] using! hay
  refine ⟨as ++ bs ++ rs,?_,?_,?_⟩
  · simp only [reflectionLegal_append]
    exact ⟨⟨has,hbs⟩,hrs⟩
  · have hrlen : rs.length = as.length := reflectionAdjoint_length as
    simp only [List.length_append,hrlen]
    nlinarith
  · intro ψ
    rw [reflectionCompile_append,reflectionCompile_append,run_append,run_append,
      run_reflectionCompile,hb,run_reflectionCompile,reflectionAdjoint_matrix as has]
    exact known_two_level_unitary_conjugate A hA x y _ _ hxy hpq hx hy B ψ

/-- A unit-modulus phase at the all-true address has an exact legal table of length at most
`256*(k+1)^2`. -/
private theorem noWorkCanonicalPhase_table (k : ℕ) (z : ℂ) (hz : star z*z=1) :
    ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧ gs.length ≤ 256*(k+1)^2 ∧
      ∀ ψ : QState (Reg (k+1)), Run 1 (reflectionCompile gs) ψ =
        twoLevelMatrix (.phase (fun _ => true) z) *ᵥ ψ := by
  let B := Matrix.diagonal (fun b : Bool => if b then z else 1)
  have hB : B ∈ unitaryGroup Bool ℂ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
    change (starRingEnd ℂ) z*z=1 at hz
    ext a b
    cases a <;> cases b <;> simp [B,Matrix.mul_apply,hz]
  obtain ⟨gs,hgs,hlen,hr⟩ := noWorkCanonicalPair_table k B hB
  have hpq : knownControlAddress k false ≠ knownControlAddress k true := by
    intro he
    have hh := congrFun he (Fin.last k)
    simp [knownControlAddress] at hh
  have hq : knownControlAddress k true = fun _ => true := by
    funext i
    simp [knownControlAddress]
  have hmat : twoLevelMatrix (.pair (knownControlAddress k false) (knownControlAddress k true) B) =
      twoLevelMatrix (.phase (fun _ => true) z) := by
    rw [← hq]
    ext u v
    by_cases hux : u = knownControlAddress k false <;>
      by_cases huy : u = knownControlAddress k true <;>
      by_cases hvx : v = knownControlAddress k false <;>
      by_cases hvy : v = knownControlAddress k true <;>
      by_cases huv : u = v <;> simp_all [twoLevelMatrix,B]
  refine ⟨gs,hgs,hlen,?_⟩
  intro ψ
  rw [hr,hmat]

/-- A unit-modulus phase at any `(k+1)`-bit address has an exact legal table of length at most
`768*(k+2)^3`. -/
private theorem noWorkPhase_table (k : ℕ) (x : Reg (k+1)) (z : ℂ) (hz : star z*z=1) :
    ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧ gs.length ≤ 768*(k+2)^3 ∧
      ∀ ψ : QState (Reg (k+1)), Run 1 (reflectionCompile gs) ψ = twoLevelMatrix (.phase x z) *ᵥ ψ := by
  let as := knownAddressFlips x (fun _ => true)
  obtain ⟨has,halen,hax⟩ := knownAddressFlips_spec x (fun _ => true)
  obtain ⟨bs,hbs,hblen,hb⟩ := noWorkCanonicalPhase_table k z hz
  let rs := reflectionAdjoint as
  have hrs := reflectionAdjoint_legal as has
  let A := reflectionProgramMatrix as
  have hA : A ∈ unitaryGroup (Reg (k+1)) ℂ := reflectionProgramMatrix_unitary as has
  have hx : A *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket (fun _ => true) := by
    simpa only [run_reflectionCompile,ApplyGate] using! hax
  refine ⟨as ++ bs ++ rs,?_,?_,?_⟩
  · simp only [reflectionLegal_append]
    exact ⟨⟨has,hbs⟩,hrs⟩
  · have hrlen : rs.length = as.length := reflectionAdjoint_length as
    simp only [List.length_append,hrlen]
    nlinarith
  · intro ψ
    rw [reflectionCompile_append,reflectionCompile_append,run_append,run_append,
      run_reflectionCompile,hb,run_reflectionCompile,reflectionAdjoint_matrix as has]
    exact known_two_level_phase_conjugate A hA x _ hx z ψ

/-- For `1 ≤ n`, every legal two-level instruction on `n` qubits has an exact legal
implementation without work qubits, using at most `768*(n+1)^3` gates and no queries. -/
theorem known_two_level_no_work_local_implementation (n : ℕ) (hn : 1 ≤ n)
    (g : TwoLevelInstruction (Reg n)) (hg : twoLevelLegal g) :
    ∃ gs : List (ReflectionGate n), reflectionLegal gs ∧ gs.length ≤ 768*(n+1)^3 ∧
      QueryCount (reflectionCompile gs) = 0 ∧ GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) ψ = twoLevelMatrix g *ᵥ ψ := by
  cases n with
  | zero => omega
  | succ k =>
    have hlocal : ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧
        gs.length ≤ 768*(k+2)^3 ∧
        ∀ ψ : QState (Reg (k+1)), Run 1 (reflectionCompile gs) ψ = twoLevelMatrix g *ᵥ ψ := by
      cases g with
      | pair x y B => exact noWorkPair_table k x y hg.1 B hg.2
      | phase x z => exact noWorkPhase_table k x z hg
    obtain ⟨gs,hgs,hlen,hr⟩ := hlocal
    exact ⟨gs,hgs,hlen,queryCount_reflectionCompile _,gateCount_reflectionCompile _,hr⟩

/-- Legal instruction tables of length at most `C` combine into an exact legal table for a
two-level program with length at most `C*ts.length`. -/
theorem noWork_program_table_of_instruction_tables (n C : ℕ)
    (ts : List (TwoLevelInstruction (Reg n)))
    (hts : ∀ g ∈ ts, twoLevelLegal g)
    (hlocal : ∀ g ∈ ts, twoLevelLegal g →
      ∃ gs : List (ReflectionGate n), reflectionLegal gs ∧ gs.length ≤ C ∧
        ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) ψ = twoLevelMatrix g *ᵥ ψ) :
    ∃ gs : List (ReflectionGate n), reflectionLegal gs ∧ gs.length ≤ C*ts.length ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) ψ = twoLevelProgram ts *ᵥ ψ := by
  exact twoLevel_program_table_of_instruction_tables n n C (fun ψ => ψ) ts hts hlocal

/-- Exact legal tables of length at most `768*(n+1)^3` for all legal two-level instructions
yield an exact, query-free table for any unitary with at most `768*(n+1)^3*4^n` gates. -/
theorem noWork_unitary_table_of_instruction_tables (n : ℕ)
    (hlocal : ∀ (g : TwoLevelInstruction (Reg n)), twoLevelLegal g →
      ∃ gs : List (ReflectionGate n), reflectionLegal gs ∧ gs.length ≤ 768*(n+1)^3 ∧
        ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) ψ = twoLevelMatrix g *ᵥ ψ)
    (U : Matrix (Reg n) (Reg n) ℂ) (hU : U ∈ unitaryGroup (Reg n) ℂ) :
    ∃ gs : List (ReflectionGate n), reflectionLegal gs ∧ gs.length ≤ 768*(n+1)^3*4^n ∧
      QueryCount (reflectionCompile gs) = 0 ∧ GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) ψ = U *ᵥ ψ := by
  exact known_unitary_table_of_instruction_tables n n (768*(n+1)^3)
    (fun ψ => ψ) hlocal U hU

/-- A given exact no-work unitary table with the stated bound can be paired with an exact
clean-frame table bounded by `128*(n+1)^2*4^n`, both using no queries. -/
theorem noWork_clean_frame_comparison_of_table (n : ℕ)
    (U : Matrix (Reg n) (Reg n) ℂ) (hU : U ∈ unitaryGroup (Reg n) ℂ)
    (gs_nw : List (ReflectionGate n)) (hnw : reflectionLegal gs_nw)
    (hlen : gs_nw.length ≤ 768*(n+1)^3*4^n)
    (hrun : ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs_nw) ψ = U *ᵥ ψ) :
    ∃ gs_fr : List (ReflectionGate (n+(n+1))),
      reflectionLegal gs_nw ∧ reflectionLegal gs_fr ∧
      gs_nw.length ≤ 768*(n+1)^3*4^n ∧ gs_fr.length ≤ 128*(n+1)^2*4^n ∧
      QueryCount (reflectionCompile gs_nw) = 0 ∧ QueryCount (reflectionCompile gs_fr) = 0 ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs_nw) ψ = U *ᵥ ψ ∧
        Run 1 (reflectionCompile gs_fr) (knownFrameEmbed n ψ) = knownFrameEmbed n (U *ᵥ ψ) := by
  obtain ⟨gs_fr,hfr,hflen,_,_,hf⟩ := known_unitary_actual_clean_local_synthesis n U hU
  exact ⟨gs_fr,hnw,hfr,hlen,hflen,queryCount_reflectionCompile _,
    queryCount_reflectionCompile _,fun ψ => ⟨hrun ψ,hf ψ⟩⟩

/-- For `1 ≤ n`, every `n`-qubit unitary has an exact legal implementation without work qubits,
with at most `768*(n+1)^3*4^n` gates and no queries. The construction uses two-level
synthesis as in [BarencoEtAl1995]. -/
theorem known_unitary_no_work_actual_local_synthesis (n : ℕ) (hn : 1 ≤ n)
    (U : Matrix (Reg n) (Reg n) ℂ) (hU : U ∈ unitaryGroup (Reg n) ℂ) :
    ∃ gs : List (ReflectionGate n), reflectionLegal gs ∧ gs.length ≤ 768*(n+1)^3*4^n ∧
      QueryCount (reflectionCompile gs) = 0 ∧ GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) ψ = U *ᵥ ψ := by
  apply noWork_unitary_table_of_instruction_tables n _ U hU
  intro g hg
  obtain ⟨gs,hgs,hlen,_,_,hr⟩ := known_two_level_no_work_local_implementation n hn g hg
  exact ⟨gs,hgs,hlen,hr⟩

/-- For `1 ≤ n`, every unitary has query-free legal no-work and clean-frame implementations of
the same action, with respective bounds `768*(n+1)^3*4^n` and `128*(n+1)^2*4^n`. -/
theorem no_work_and_clean_frame_same_unitary_consumer (n : ℕ) (hn : 1 ≤ n)
    (U : Matrix (Reg n) (Reg n) ℂ) (hU : U ∈ unitaryGroup (Reg n) ℂ) :
    ∃ gs_nw : List (ReflectionGate n), ∃ gs_fr : List (ReflectionGate (n+(n+1))),
      reflectionLegal gs_nw ∧ reflectionLegal gs_fr ∧
      gs_nw.length ≤ 768*(n+1)^3*4^n ∧ gs_fr.length ≤ 128*(n+1)^2*4^n ∧
      QueryCount (reflectionCompile gs_nw) = 0 ∧ QueryCount (reflectionCompile gs_fr) = 0 ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs_nw) ψ = U *ᵥ ψ ∧
        Run 1 (reflectionCompile gs_fr) (knownFrameEmbed n ψ) = knownFrameEmbed n (U *ᵥ ψ) := by
  obtain ⟨gs,hgs,hlen,_,_,hr⟩ := known_unitary_no_work_actual_local_synthesis n hn U hU
  obtain ⟨fs,hf⟩ := noWork_clean_frame_comparison_of_table n U hU gs hgs hlen hr
  exact ⟨gs,fs,hf⟩

end Qatlib.Concepts.CircuitImpl.MultiControl
