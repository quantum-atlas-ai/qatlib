/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.OracleAmplify.StandardOracleTidyAmplificationStat
import Qatlib.Concepts.UniformBqp.OracleAmplify.StandardOracleMajorityAmpStre
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel

/-!
# Tidy amplification for a standard bit oracle

`standardOracleTidyAmplification` combines majority amplification with coherent output copying
and uncomputation. Hermiticity and product-basis reassociation keep the resulting circuit in the
standard workspace-oracle model, with the resource bounds required by the specification. The
background is described in [BennettEtAl1997].

## Main statements

* `workspace_oracle_hermitian`: self-adjointness of the bit oracle.
* `standardOracleTidyAmplification`: amplified success with restored seed registers.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option autoImplicit false
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.Amplification
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.CircuitReversal.ReversalAlgebra
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.UniformBqp.OracleAmplify
open Matrix
open scoped Classical

/-- The standard workspace bit oracle equals its conjugate transpose. -/
private theorem workspace_oracle_hermitian {n : ℕ} {W : Type}
    [Fintype W] [DecidableEq W] (x : Fin n → Bool) :
    (workspaceBitOracle (W := W) x)ᴴ = workspaceBitOracle x := by
  rw [workspaceBitOracle, tensorGate_conjTranspose, Matrix.conjTranspose_one,
    show (BitOracleOn x)ᴴ = BitOracleOn x from permMatrix_conjTranspose (bitFlip_involutive x)]

/-- Reassociating the product basis identifies the lifted workspace oracle with the standard
oracle on a workspace enlarged by one Boolean factor. -/
private theorem oracle_reassociate {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (x : Fin n → Bool) :
    relabelGate (Equiv.prodAssoc (Fin n × Bool) W Bool)
      (LiftGate (workspaceBitOracle (W := W) x)) =
      workspaceBitOracle (W := W × Bool) x := by
  ext z z'
  rcases z with ⟨p, w, c⟩
  rcases z' with ⟨p', w', c'⟩
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.prodAssoc_symm_apply, LiftGate, workspaceBitOracle, TensorGate,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- Every unitary standard bit-oracle circuit with success at least `2/3` satisfies the tidy
amplification specification, with probability at least `1 - ε` on the restored-seed state
carrying the correct answer bit [BennettEtAl1997]. -/
theorem standardOracleTidyAmplification : StandardOracleTidyAmplification := by
  intro n hn W X _ _ _ _ _ C seed v input b ε hC hb hε
  obtain ⟨r, C₁, hprecision, hu, hq, hg, hmass⟩ :=
    standardOracleMajorityAmplification n hn W X C seed v input b (ε / 2) hC hb (by positivity)
  let verdict := fun z : (Fin n × Bool) × (Fin (2 * r + 1) → (Fin n × Bool) × W) =>
    MajorityBit (fun j => v (z.2 j))
  let E := LiftCircuit C₁ ++ [Step.gate (AnswerCopyGate verdict)] ++
    LiftCircuit (ReverseCircuit C₁)
  let e := Equiv.prodAssoc (Fin n × Bool) (Fin (2 * r + 1) → (Fin n × Bool) × W) Bool
  have hEu : IsUnitaryCircuit E := by
    exact (isUnitaryCircuit_append _ _).mpr
      ⟨(isUnitaryCircuit_append _ _).mpr ⟨hu.lift,
        (isUnitaryCircuit_gate _ _).mpr ⟨answerCopyGate_unitary _, isUnitaryCircuit_nil⟩⟩,
        (isUnitaryCircuit_reverseCircuit hu).lift⟩
  obtain ⟨hlegal, hEq, hEg, _⟩ := relabelCircuit_legality_resources e E
  refine ⟨r, relabelCircuit e E, ?_, hlegal.mpr hEu, ?_, ?_, ?_⟩
  · convert hprecision using 2
    congr 2
    field_simp
  · rw [hEq]
    simp only [E, queryCount_append, queryCount_liftCircuit, queryCount_reverseCircuit, hq,
      QueryCount]
    ring
  · rw [hEg]
    simp only [E, gateCount_append, gateCount_liftCircuit, gateCount_reverseCircuit, hg, GateCount]
    omega
  · intro x
    have hclean := subroutine_cleaning_mass (workspaceBitOracle (input x))
      (workspaceBitOracle_unitary (input x)) (workspace_oracle_hermitian (input x))
      C₁ hu ((⟨0, hn⟩, false), fun _ => seed) verdict (b x)
    have htransport := (run_relabelCircuit_readout e
      (LiftGate (workspaceBitOracle (W := Fin (2 * r + 1) → (Fin n × Bool) × W) (input x)))
      E (Ket (((⟨0, hn⟩, false), fun _ => seed), false))
      {(((⟨0, hn⟩, false), fun _ => seed), b x)}).2
    have hseed : relabelState e (Ket (((⟨0, hn⟩, false), fun _ => seed), false)) =
        Ket ((⟨0, hn⟩, false), (fun _ => seed, false)) := by
      funext z
      simp [relabelState, Ket, e, Prod.ext_iff, and_assoc]
    rw [oracle_reassociate, hseed] at htransport
    simp only [Finset.map_singleton, Equiv.toEmbedding_apply, e,
        Equiv.prodAssoc_apply] at htransport
    rw [htransport]
    simp only [MeasureProb, Finset.sum_singleton]
    change 1 - ε ≤ BornProb (Run (LiftGate (workspaceBitOracle (input x))) E
      (Ket (((⟨0, hn⟩, false), fun _ => seed), false)))
      (((⟨0, hn⟩, false), fun _ => seed), b x)
    rw [hclean]
    have hm := hmass x
    have hp := measureProb_nonneg (Run (workspaceBitOracle (input x)) C₁
      (Ket ((⟨0, hn⟩, false), fun _ => seed))) (Finset.univ.filter fun z => verdict z = b x)
    change 1 - ε / 2 ≤ MeasureProb (Run (workspaceBitOracle (input x)) C₁
      (Ket ((⟨0, hn⟩, false), fun _ => seed))) (Finset.univ.filter fun z => verdict z = b x) at hm
    by_cases hlarge : 1 ≤ ε
    · nlinarith [sq_nonneg (MeasureProb (Run (workspaceBitOracle (input x)) C₁
        (Ket ((⟨0, hn⟩, false), fun _ => seed))) (Finset.univ.filter fun z => verdict z = b x))]
    · nlinarith [sq_nonneg (ε / 2)]

end Qatlib.Concepts.UniformBqp.OracleAmplify
