/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.WireComposition.ClusterWireInstrument
import Qatlib.Concepts.InstrumentSeq.SeqAssoc.InstrumentCoarseGrainLaws
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ClusterPatterns.WireComposition

namespace Qatlib.Concepts.ClusterPatterns.AdaptiveEuler

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable def clusterSequenceUnitary : List ℂ → Operator 2
  | [] => 1
  | z :: zs => clusterSequenceUnitary zs * clusterJ z

def clusterSequenceOutcomeEquiv (n : ℕ) : Bool × Reg n ≃ Reg (n + 1) :=
  Fin.consEquiv (fun _ : Fin (n + 1) => Bool)

theorem reg_zero_subsingleton (x : Reg 0) : x = ZeroStr 0 := by
  funext i
  exact i.elim0

theorem finset_univ_reg_zero : (Finset.univ : Finset (Reg 0)) = {ZeroStr 0} := by
  ext x
  simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
  exact reg_zero_subsingleton x

noncomputable def clusterSequenceEmptyInstrument : Instrument (Reg 0) 2 2 :=
  Instrument.ofKraus (fun _ : Reg 0 => (1 : Operator 2)) (by
    rw [finset_univ_reg_zero, Finset.sum_singleton]
    simp)

noncomputable def clusterSequenceInstrument :
    (zs : List ℂ) → (∀ z ∈ zs, ‖z‖ = 1) → Instrument (Reg zs.length) 2 2
  | [], _ => clusterSequenceEmptyInstrument
  | z :: zs, hzs =>
      ((clusterWireInstrument z (hzs z List.mem_cons_self)).seq
        (clusterSequenceInstrument zs (fun w hw => hzs w (List.mem_cons_of_mem z hw)))).coarsen
        (clusterSequenceOutcomeEquiv zs.length)

theorem cluster_sequence_unitary_word_laws :
    clusterSequenceUnitary [] = 1 ∧
      (∀ (z : ℂ) (zs : List ℂ), clusterSequenceUnitary (z :: zs) =
        clusterSequenceUnitary zs * clusterJ z) ∧
      (∀ zs : List ℂ, (∀ z ∈ zs, ‖z‖ = 1) →
        clusterSequenceUnitary zs ∈ Matrix.unitaryGroup (Fin 2) ℂ) := by
  refine ⟨rfl, fun z zs => rfl, fun zs hzs => ?_⟩
  induction zs with
  | nil => exact Submonoid.one_mem _
  | cons z zs ih =>
    show clusterSequenceUnitary zs * clusterJ z ∈ Matrix.unitaryGroup (Fin 2) ℂ
    exact Submonoid.mul_mem _ (ih (fun w hw => hzs w (List.mem_cons_of_mem z hw)))
      (clusterJ_unitary (hzs z List.mem_cons_self))

theorem half_pow_cast (n : ℕ) : (1 / 2 : ℂ) ^ n = (((1 / 2 : ℝ) ^ n : ℝ) : ℂ) := by
  push_cast
  norm_num

theorem clusterSequenceEmptyInstrument_branch (ω : Reg 0) (ρ : Operator 2) :
    clusterSequenceEmptyInstrument.branch ω ρ = ρ := by
  show (1 : Operator 2) * ρ * (1 : Operator 2).conjTranspose = ρ
  simp

theorem cluster_sequence_instrument_probability_conditioning :
    ∀ (zs : List ℂ) (hzs : ∀ z ∈ zs, ‖z‖ = 1) (ρ : Operator 2) (ω : Reg zs.length),
      (clusterSequenceInstrument zs hzs).branch ω ρ =
        (1 / 2 : ℂ) ^ zs.length • conjBranch (clusterSequenceUnitary zs) ρ ∧
      instrumentProb (clusterSequenceInstrument zs hzs) ρ ω =
        (1 / 2 : ℝ) ^ zs.length * (Matrix.trace ρ).re ∧
      (clusterSequenceInstrument zs hzs).forget.map ρ =
        conjBranch (clusterSequenceUnitary zs) ρ ∧
      (IsDensityOperator ρ → ∀ h : 0 < instrumentProb (clusterSequenceInstrument zs hzs) ρ ω,
        (clusterSequenceInstrument zs hzs).conditionalState ρ ω h =
          conjBranch (clusterSequenceUnitary zs) ρ) := by
  intro zs
  induction zs with
  | nil =>
    intro hzs ρ ω
    have hω : ω = ZeroStr 0 := reg_zero_subsingleton ω
    subst hω
    have hbranch : (clusterSequenceInstrument [] hzs).branch (ZeroStr 0) ρ = ρ :=
      clusterSequenceEmptyInstrument_branch (ZeroStr 0) ρ
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hbranch]
      show ρ = (1 / 2 : ℂ) ^ 0 • conjBranch (clusterSequenceUnitary []) ρ
      rw [pow_zero, one_smul]
      show ρ = conjBranch 1 ρ
      simp
    · show (Matrix.trace ((clusterSequenceInstrument [] hzs).branch (ZeroStr 0) ρ)).re = _
      rw [hbranch]
      simp
    · show (clusterSequenceInstrument [] hzs).forget.map ρ = conjBranch 1 ρ
      rw [Instrument.forget_apply, finset_univ_reg_zero, Finset.sum_singleton, hbranch]
      simp
    · intro hρ h
      show ((instrumentProb (clusterSequenceInstrument [] hzs) ρ (ZeroStr 0) : ℝ) : ℂ)⁻¹ •
          ((clusterSequenceInstrument [] hzs).branch (ZeroStr 0) ρ) = conjBranch 1 ρ
      rw [hbranch]
      simp only [conjBranch_apply, Matrix.one_mul, Matrix.mul_one, conjTranspose_one]
      have htr : Matrix.trace ρ = 1 := hρ.2
      have hprob : instrumentProb (clusterSequenceInstrument [] hzs) ρ (ZeroStr 0) = 1 := by
        show (Matrix.trace ((clusterSequenceInstrument [] hzs).branch (ZeroStr 0) ρ)).re = 1
        rw [hbranch, htr]
        norm_num
      rw [hprob]
      simp
  | cons z zs ih =>
    intro hzs ρ ω
    have hzh : ‖z‖ = 1 := hzs z List.mem_cons_self
    have hU : clusterSequenceUnitary (z :: zs) = clusterSequenceUnitary zs * clusterJ z := rfl
    have hUn : clusterSequenceUnitary zs ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
      cluster_sequence_unitary_word_laws.2.2 zs (fun w hw => hzs w (List.mem_cons_of_mem z hw))
    have hcomp : conjBranch (clusterSequenceUnitary zs) (conjBranch (clusterJ z) ρ) =
        conjBranch (clusterSequenceUnitary zs * clusterJ z) ρ := by
      show ((conjBranch (clusterSequenceUnitary zs)).comp (conjBranch (clusterJ z))) ρ = _
      rw [conjBranch_comp]

    have hbranch : (clusterSequenceInstrument (z :: zs) hzs).branch ω ρ =
        (1 / 2 : ℂ) ^ (z :: zs).length •
          conjBranch (clusterSequenceUnitary (z :: zs)) ρ := by
      show (((clusterWireInstrument z (hzs z List.mem_cons_self)).seq
            (clusterSequenceInstrument zs (fun w hw => hzs w (List.mem_cons_of_mem z hw)))).coarsen
            (clusterSequenceOutcomeEquiv zs.length)).branch ω ρ = _
      rw [Instrument.coarsen_branch_equiv_apply]
      show ((clusterSequenceInstrument zs (fun w hw => hzs w (List.mem_cons_of_mem z hw))).branch
            ((clusterSequenceOutcomeEquiv zs.length).symm ω).2).comp
          ((clusterWireInstrument z (hzs z List.mem_cons_self)).branch
            ((clusterSequenceOutcomeEquiv zs.length).symm ω).1) ρ = _
      rw [LinearMap.comp_apply, clusterWireInstrument_branch_apply,
        (ih (fun w hw => hzs w (List.mem_cons_of_mem z hw)) _ _).1, map_smul, hcomp,
        smul_smul, ← pow_succ]
      rfl
    refine ⟨hbranch, ?_, ?_, ?_⟩
    · show (Matrix.trace ((clusterSequenceInstrument (z :: zs) hzs).branch ω ρ)).re = _
      rw [hbranch, Matrix.trace_smul, smul_eq_mul,
        trace_conjBranch_unitary _ (by
          rw [hU]
          exact Submonoid.mul_mem _ hUn (clusterJ_unitary hzh)), half_pow_cast,
        Complex.re_ofReal_mul]
    · show (((clusterWireInstrument z (hzs z List.mem_cons_self)).seq
            (clusterSequenceInstrument zs (fun w hw => hzs w (List.mem_cons_of_mem z hw)))).coarsen
            (clusterSequenceOutcomeEquiv zs.length)).forget.map ρ = _
      rw [Instrument.forget_coarsen_apply, Instrument.forget_apply]
      have hseqbranch : ∀ op : Bool × Reg zs.length,
          ((clusterWireInstrument z (hzs z List.mem_cons_self)).seq
            (clusterSequenceInstrument zs
              (fun w hw => hzs w (List.mem_cons_of_mem z hw)))).branch op ρ
          = (clusterSequenceInstrument zs
              (fun w hw => hzs w (List.mem_cons_of_mem z hw))).branch op.2
            ((clusterWireInstrument z (hzs z List.mem_cons_self)).branch op.1 ρ) :=
        fun op => rfl
      rw [Finset.sum_congr rfl (fun op _ => hseqbranch op), Fintype.sum_prod_type]
      have hinner : ∀ b : Bool,
          (∑ w : Reg zs.length,
            (clusterSequenceInstrument zs
              (fun w hw => hzs w (List.mem_cons_of_mem z hw))).branch w
              ((clusterWireInstrument z (hzs z List.mem_cons_self)).branch b ρ))
          = conjBranch (clusterSequenceUnitary zs)
              ((clusterWireInstrument z (hzs z List.mem_cons_self)).branch b ρ) := by
        intro b
        rw [← Instrument.forget_apply,
          (ih (fun w hw => hzs w (List.mem_cons_of_mem z hw)) _ (ZeroStr _)).2.2.1]
      rw [Finset.sum_congr rfl (fun b _ => hinner b), ← map_sum, ← Instrument.forget_apply]
      have hJforget := (cluster_wire_instrument_probability z hzh ρ false).2.2
      rw [hJforget, hU]
      exact hcomp
    · intro hρ h
      have htr : Matrix.trace ρ = 1 := hρ.2
      have hprob : instrumentProb (clusterSequenceInstrument (z :: zs) hzs) ρ ω =
          (1 / 2 : ℝ) ^ (z :: zs).length := by
        show (Matrix.trace ((clusterSequenceInstrument (z :: zs) hzs).branch ω ρ)).re = _
        rw [hbranch, Matrix.trace_smul, smul_eq_mul,
          trace_conjBranch_unitary _ (by
            rw [hU]
            exact Submonoid.mul_mem _ hUn (clusterJ_unitary hzh)), htr, mul_one, half_pow_cast,
          Complex.ofReal_re]
      show ((instrumentProb (clusterSequenceInstrument (z :: zs) hzs) ρ ω : ℝ) : ℂ)⁻¹ •
          ((clusterSequenceInstrument (z :: zs) hzs).branch ω ρ) = _
      rw [hprob, hbranch, hU, smul_smul]
      have hsc : ((((1 / 2 : ℝ) ^ (z :: zs).length : ℝ) : ℂ))⁻¹ *
          (1 / 2 : ℂ) ^ (z :: zs).length = 1 := by
        rw [← half_pow_cast, inv_mul_cancel₀]
        exact pow_ne_zero _ (by norm_num)
      rw [hsc, one_smul]

end Qatlib.Concepts.ClusterPatterns.AdaptiveEuler
