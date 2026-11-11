/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.ChainFeedback.ClusterWireParityFeedback
import Qatlib.Concepts.ClusterPatterns.AdaptiveEuler.CountedClusterSequence

/-!
# Adaptive Euler patterns on cluster chains

This module defines adaptive phase selection and Pauli frame tracking for cluster-chain
measurement patterns, following the setting of [RaussendorfBriegel2000]. The functions
`adaptiveRealizedWord` and `adaptiveFinalFrame` describe the realized phase word and its final
correction, while `clusterAdaptiveProgram` gives an observed circuit with explicit Kraus leaves.

The transport identities relate each realized sequence to its nominal sequence through a scalar
Pauli frame. The instrument results remove this frame and identify the resulting channel,
including its action on a finite reference system. The four-step word `clusterAdaptiveEulerWord`
specializes these results to three real phase parameters.

## Main statements

* `cluster_adaptive_word_transport`: the final scalar Pauli frame relates realized and nominal
  sequence operators.
* `cluster_adaptive_euler_corrected_channel`: corrected Euler branches sum to nominal unitary
  conjugation on a system with a reference.
* `cluster_adaptive_program_leaves_and_cost`: exact leaf enumeration and gate, measurement, and
  query counts.
* `cluster_adaptive_euler_pattern`: four measurements, sixteen gates, and the explicit
  corrected-frame amplitude formula.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.ClusterPatterns.ChainFeedback
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ClusterPatterns.WireComposition

namespace Qatlib.Concepts.ClusterPatterns.AdaptiveEuler

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped ComplexOrder

set_option linter.unusedSectionVars false

/-- Choose a phase or its complex conjugate according to the current X-frame bit. -/
noncomputable def adaptivePhase (x : Bool) (z : ℂ) : ℂ := if x then star z else z

/-- Update the two Pauli feedback bits and accumulated scalar phase after one nominal phase and
measurement outcome. -/
noncomputable def adaptiveFrameStep (F : Bool × Bool × ℂ) (ζ : ℂ) (s : Bool) : Bool × Bool × ℂ :=
  let p := wireFeedbackStep (F.1, F.2.1) s
  (p.1, (p.2, F.2.2 * (if F.1 then (if F.2.1 then (-1 : ℂ) else 1) * star ζ else 1)))

/-- Process paired nominal phases and outcomes, returning the final feedback frame and the
realized phase word. -/
noncomputable def adaptiveRunFold : Bool × Bool × ℂ → List (ℂ × Bool) → (Bool × Bool × ℂ) × List ℂ
  | F, [] => (F, [])
  | F, p :: ps =>
      let out := adaptiveRunFold (adaptiveFrameStep F p.1 p.2) ps
      (out.1, (if p.2 then (-1 : ℂ) else 1) * adaptivePhase F.1 p.1 :: out.2)

/-- Run adaptive feedback from the trivial frame on the zipped phase and outcome lists. -/
noncomputable def adaptiveRun (zs : List ℂ) (msg : List Bool) : (Bool × Bool × ℂ) × List ℂ :=
  adaptiveRunFold (false, false, 1) (zs.zip msg)

/-- The phase word realized by adaptive feedback on the given nominal word and measurement
record. -/
noncomputable def adaptiveRealizedWord (zs : List ℂ) (msg : List Bool) : List ℂ :=
    (adaptiveRun zs msg).2

/-- The final Pauli feedback bits and accumulated scalar phase produced by an adaptive run. -/
noncomputable def adaptiveFinalFrame (zs : List ℂ) (msg : List Bool) : Bool × Bool × ℂ :=
  (adaptiveRun zs msg).1

/-- The product of the Boolean-selected Pauli X and Pauli Z operators determined by a feedback
frame. -/
noncomputable def adaptiveFrameGate (F : Bool × Bool × ℂ) : Operator 2 :=
  pauliXChoice F.1 * pauliZChoice F.2.1

/-- The four-phase word consisting of one followed by the complex exponentials of the three real
Euler parameters. -/
noncomputable def clusterAdaptiveEulerWord (ξ η ζ : ℝ) : List ℂ :=
  [1, Complex.exp ((ξ : ℂ) * Complex.I), Complex.exp ((η : ℂ) * Complex.I),
    Complex.exp ((ζ : ℂ) * Complex.I)]

/-- The observed circuit that adaptively applies a phase gate, a Hadamard gate, and a
measurement at each site of a cluster chain. -/
noncomputable def clusterAdaptiveLoopFin :
    (zs : List ℂ) → (Bool × Bool × ℂ) → ObservedCircuit (Fin (2 ^ (zs.length + 1)))
  | [], _ => .halt true
  | [z], F =>
      .step (.gate (clusterSeqPhaseFin 1 (adaptivePhase F.1 z))) (.step (.gate (clusterSeqHFin 1))
        (.measure 2 (clusterSeqLabelFin 1)
          (fun _ => .halt true)))
  | z :: w :: ws, F =>
      .step (.gate (clusterSeqPhaseFin _ (adaptivePhase F.1 z))) (.step (.gate (clusterSeqHFin _))
        (.measure 2 (clusterSeqLabelFin _)
          (fun k => clusterSeqShiftObservedFin _
            (clusterAdaptiveLoopFin (w :: ws)
              (adaptiveFrameStep F z (boolEquivFin2.symm k))))))

/-- The Kraus leaf, acceptance flag, resource counts, and outcome record of the adaptive
measurement loop for a specified Boolean history. -/
noncomputable def clusterAdaptiveLoopLeafGen :
    (zs : List ℂ) → (Bool × Bool × ℂ) → (ω : Reg zs.length) →
      ObservedKrausLeaf (2 ^ (zs.length + 1))
  | [], _, _ => ⟨1, true, 0, 0, 0, []⟩
  | [z], F, ω =>
      ⟨Projector (Finset.univ.filter
          (fun r : Fin (2 ^ (1 + 1)) => clusterSeqLabelFin 1 r = boolEquivFin2 (ω 0)))
          * clusterSeqHFin 1 * clusterSeqPhaseFin 1 (adaptivePhase F.1 z),
        true, 0, 2, 1, [(2, (boolEquivFin2 (ω 0)).val)]⟩
  | z :: w :: ws, F, ω =>
      ⟨clusterSeqShiftGateFin _ ((clusterAdaptiveLoopLeafGen (w :: ws)
            (adaptiveFrameStep F z (ω 0)) (Fin.tail ω)).operator)
          * Projector (Finset.univ.filter
              (fun r : Fin (2 ^ ((z :: w :: ws).length + 1)) =>
                clusterSeqLabelFin (z :: w :: ws).length r = boolEquivFin2 (ω 0)))
          * clusterSeqHFin (z :: w :: ws).length
          * clusterSeqPhaseFin (z :: w :: ws).length (adaptivePhase F.1 z),
        true, 0,
        (clusterAdaptiveLoopLeafGen (w :: ws) (adaptiveFrameStep F z (ω 0)) (Fin.tail ω)).gates + 2,
        (clusterAdaptiveLoopLeafGen (w :: ws) (adaptiveFrameStep F z (ω 0)) (Fin.tail ω)).measurements + 1,
        (2, (boolEquivFin2 (ω 0)).val) ::
          (clusterAdaptiveLoopLeafGen (w :: ws) (adaptiveFrameStep F z (ω 0)) (Fin.tail ω)).outcomes⟩

/-- Prepare the cluster resource and execute the adaptive loop from the trivial feedback frame. -/
noncomputable def clusterAdaptiveProgram (zs : List ℂ) :
    ObservedCircuit (Fin (2 ^ (zs.length + 1))) :=
  clusterSeqPrependSteps 1 (clusterSequenceResourceCircuit zs.length)
    (clusterAdaptiveLoopFin zs (false, false, 1))

/-- The explicit Kraus leaf of the resource preparation followed by the adaptive loop for a
specified outcome history. -/
noncomputable def clusterAdaptiveProgramLeafGen (zs : List ℂ) (ω : Reg zs.length) :
    ObservedKrausLeaf (2 ^ (zs.length + 1)) :=
  ObservedKrausLeaf.prepend (clusterSequenceResourceGate zs.length) 0 (2 * zs.length) 0 []
    (clusterAdaptiveLoopLeafGen zs (false, false, 1) ω)

set_option autoImplicit false
noncomputable section AdaptiveProofs
open scoped Classical BigOperators

/-- A complex number of unit norm multiplied by its conjugate equals one. -/
private theorem adaptive_unit_phase (z : ℂ) (hz : ‖z‖=1) : z*star z=1 := by
  have h := Complex.normSq_eq_conj_mul_self (z := z)
  rw [Complex.normSq_eq_norm_sq,hz,one_pow] at h
  simpa only [mul_comm,Complex.star_def] using! h.symm

/-- Unit-modulus phases satisfy the stated Pauli transport identities for `clusterJ`. Complex
conjugation and negation preserve their unit norm. -/
theorem cluster_adaptive_pauli_j_laws :
    (∀ z : ℂ, ‖z‖ = 1 →
      pauliXChoice true * clusterJ z = clusterJ (-(1 : ℂ) * z) ∧
      clusterJ z * pauliZChoice true = pauliXChoice true * clusterJ z ∧
      clusterJ z * pauliXChoice true = z • (pauliZChoice true * clusterJ (star z)) ∧
      pauliZChoice true * clusterJ z = z • (clusterJ (star z) * pauliXChoice true) ∧
      ∀ b : Bool, pauliXChoice b * clusterJ z =
        clusterJ ((if b then (-1 : ℂ) else 1) * z)) ∧
    (∀ z : ℂ, ‖z‖ = 1 → ‖star z‖ = 1 ∧ ‖(-1 : ℂ) * z‖ = 1) := by
  constructor
  · intro z hz
    have hs := adaptive_unit_phase z hz
    change z*(starRingEnd ℂ) z=1 at hs
    have hx : pauliXChoice true*clusterJ z=clusterJ (-1*z) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [pauliXChoice,relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,
          Matrix.mul_apply,Fin.sum_univ_two,PauliX,permMatrix,boolEquivFin2,clusterJ_entry]
    refine ⟨hx,?_,?_,?_,?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [pauliXChoice,pauliZChoice,relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,
          Matrix.mul_apply,Fin.sum_univ_two,PauliX,PauliZ,permMatrix,boolEquivFin2,clusterJ_entry]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [pauliXChoice,pauliZChoice,relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,
          Matrix.mul_apply,Matrix.smul_apply,Fin.sum_univ_two,PauliX,PauliZ,permMatrix,
          boolEquivFin2,clusterJ_entry,smul_eq_mul] <;>
        solve | ring | linear_combination ((Real.sqrt 2 : ℂ)⁻¹)*hs |
          linear_combination -((Real.sqrt 2 : ℂ)⁻¹)*hs
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [pauliXChoice,pauliZChoice,relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,
          Matrix.mul_apply,Matrix.smul_apply,Fin.sum_univ_two,PauliX,PauliZ,permMatrix,
          boolEquivFin2,clusterJ_entry,smul_eq_mul] <;>
        solve | ring | linear_combination ((Real.sqrt 2 : ℂ)⁻¹)*hs |
          linear_combination -((Real.sqrt 2 : ℂ)⁻¹)*hs
    · intro b
      cases b
      · simp [pauliXChoice]
      · exact hx
  · intro z hz
    simp [hz]

/-- One adaptive measurement step transports the current scalar Pauli frame through `clusterJ z`
to the updated frame. -/
private theorem adaptive_step_transport (F : Bool × Bool × ℂ) (z : ℂ) (hz : ‖z‖=1)
    (s : Bool) :
    clusterJ ((if s then (-1 : ℂ) else 1)*adaptivePhase F.1 z)*
      (F.2.2 • adaptiveFrameGate F)=
      (adaptiveFrameStep F z s).2.2 •
        (adaptiveFrameGate (adaptiveFrameStep F z s)*clusterJ z) := by
  have hs := adaptive_unit_phase z hz
  change z*(starRingEnd ℂ) z=1 at hs
  obtain ⟨x,b,c⟩ := F
  ext i j
  cases x <;> cases b <;> cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [adaptivePhase,adaptiveFrameGate,adaptiveFrameStep,wireFeedbackStep,
      pauliXChoice,pauliZChoice,relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,
      Matrix.mul_apply,Matrix.smul_apply,Fin.sum_univ_two,PauliX,PauliZ,permMatrix,
      boolEquivFin2,clusterJ_entry,smul_eq_mul] <;>
    solve | ring | linear_combination (((Real.sqrt 2 : ℂ)⁻¹)*c)*hs |
      linear_combination -(((Real.sqrt 2 : ℂ)⁻¹)*c)*hs

/-- An adaptive frame step preserves unit norm of the accumulated scalar phase when the nominal
phase has unit norm. -/
private theorem adaptive_step_norm (F : Bool × Bool × ℂ) (hF : ‖F.2.2‖=1)
    (z : ℂ) (hz : ‖z‖=1) (s : Bool) : ‖(adaptiveFrameStep F z s).2.2‖=1 := by
  obtain ⟨x,b,c⟩ := F
  cases x <;> cases b <;> simp [adaptiveFrameStep,hF,hz]

/-- The realized phase of one adaptive step has unit norm when the nominal phase does. -/
private theorem adaptive_realized_norm (F : Bool × Bool × ℂ) (z : ℂ) (hz : ‖z‖=1)
    (s : Bool) : ‖(if s then (-1 : ℂ) else 1)*adaptivePhase F.1 z‖=1 := by
  cases F.1 <;> cases s <;> simp [adaptivePhase,hz]

/-- Folding adaptive feedback preserves word length and unit-modulus phases and agrees with
Boolean wire feedback. The realized sequence transports the initial scalar Pauli frame to
the final frame times the nominal sequence. -/
private theorem adaptive_fold_transport (ps : List (ℂ × Bool))
    (hps : ∀ p ∈ ps, ‖p.1‖=1) (F : Bool × Bool × ℂ) (hF : ‖F.2.2‖=1) :
    (adaptiveRunFold F ps).2.length=ps.length ∧
    ((adaptiveRunFold F ps).1.1,(adaptiveRunFold F ps).1.2.1)=
      (ps.map Prod.snd).foldl wireFeedbackStep (F.1,F.2.1) ∧
    ‖(adaptiveRunFold F ps).1.2.2‖=1 ∧
    (∀ w ∈ (adaptiveRunFold F ps).2, ‖w‖=1) ∧
    clusterSequenceUnitary (adaptiveRunFold F ps).2*(F.2.2 • adaptiveFrameGate F)=
      (adaptiveRunFold F ps).1.2.2 •
        (adaptiveFrameGate (adaptiveRunFold F ps).1*clusterSequenceUnitary (ps.map Prod.fst)) := by
  induction ps generalizing F with
  | nil => simp [adaptiveRunFold,clusterSequenceUnitary,hF]
  | cons p ps ih =>
    have hz := hps p List.mem_cons_self
    have hi := ih (fun q hq => hps q (List.mem_cons_of_mem p hq))
      (adaptiveFrameStep F p.1 p.2) (adaptive_step_norm F hF p.1 hz p.2)
    rcases hi with ⟨hlen,hbits,hnorm,hword,hmat⟩
    refine ⟨by simpa [adaptiveRunFold] using! hlen,?_,hnorm,?_,?_⟩
    · simpa only [adaptiveRunFold,List.map_cons,List.foldl_cons,adaptiveFrameStep] using! hbits
    · intro w hw
      simp only [adaptiveRunFold,List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact adaptive_realized_norm F p.1 hz p.2
      · exact hword w hw
    · simp only [adaptiveRunFold,clusterSequenceUnitary,List.map_cons]
      rw [Matrix.mul_assoc,adaptive_step_transport F p.1 hz p.2,
        ← Matrix.smul_mul,← Matrix.mul_assoc,hmat,Matrix.smul_mul,Matrix.mul_assoc]

/-- For a unit-modulus word and an equally long outcome record, adaptive execution preserves
length, produces the wire feedback bits and a unit-modulus scalar, and realizes the nominal
sequence up to its final scalar Pauli frame. -/
theorem cluster_adaptive_word_transport :
    ∀ (zs : List ℂ) (_hzs : ∀ z ∈ zs, ‖z‖ = 1) (msg : List Bool)
      (_hmsg : msg.length = zs.length),
      (adaptiveRealizedWord zs msg).length = zs.length ∧
      (adaptiveFinalFrame zs msg).1 = (wireFeedbackBits msg).1 ∧
      (adaptiveFinalFrame zs msg).2.1 = (wireFeedbackBits msg).2 ∧
      ‖(adaptiveFinalFrame zs msg).2.2‖ = 1 ∧
      (∀ w ∈ adaptiveRealizedWord zs msg, ‖w‖ = 1) ∧
      clusterSequenceUnitary (adaptiveRealizedWord zs msg) =
        (adaptiveFinalFrame zs msg).2.2 •
          (adaptiveFrameGate (adaptiveFinalFrame zs msg) * clusterSequenceUnitary zs) := by
  intro zs hzs msg hmsg
  have hps : ∀ p ∈ zs.zip msg, ‖p.1‖=1 := by
    intro p hp
    exact hzs p.1 (List.of_mem_zip hp).1
  have hi := adaptive_fold_transport (zs.zip msg) hps (false,false,1) (by simp)
  have hz : (zs.zip msg).map Prod.fst=zs := List.map_fst_zip (by omega)
  have hm : (zs.zip msg).map Prod.snd=msg := List.map_snd_zip (by omega)
  rw [hz,hm] at hi
  have hlen : (zs.zip msg).length=zs.length := by simp [List.length_zip,hmsg]
  rcases hi with ⟨hl,hbits,hn,hw,hmat⟩
  refine ⟨hl.trans hlen,congrArg Prod.fst hbits,congrArg Prod.snd hbits,hn,hw,?_⟩
  simpa [adaptiveFrameGate,pauliXChoice,pauliZChoice] using! hmat

/-- Multiplying an operator by a unit-modulus scalar leaves its conjugation action unchanged. -/
private theorem adaptive_conj_phase (c : ℂ) (hc : ‖c‖=1) (U ρ : Operator 2) :
    (c • U)*ρ*(c • U)ᴴ=U*ρ*Uᴴ := by
  have hs : star c*c=1 := by simpa only [mul_comm] using! adaptive_unit_phase c hc
  simp only [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hs,one_smul]

/-- The sum of the constant weight `(1 / 2 : ℂ)^L` over all `L`-bit registers equals one. -/
private theorem adaptive_uniform_sum (L : ℕ) : (∑ _ω : Reg L, (1/2 : ℂ)^L)=1 := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

/-- A unit-modulus word possesses an instrument with uniform outcome probabilities and branches
given by the nominal sequence followed by the outcome-dependent Pauli frame. A corrected
instrument has every branch equal to one half to the word length times nominal unitary
conjugation, and forgetting outcomes gives that conjugation. -/
theorem cluster_adaptive_instrument_branches :
    ∀ (zs : List ℂ) (_hzs : ∀ z ∈ zs, ‖z‖ = 1),
      ∃ I : Instrument (Reg zs.length) 2 2,
        (∀ (ω : Reg zs.length) (ρ : Operator 2), I.branch ω ρ =
          (1 / 2 : ℂ)^zs.length •
            conjBranch (adaptiveFrameGate (adaptiveFinalFrame zs (List.ofFn ω)) *
              clusterSequenceUnitary zs) ρ) ∧
        (∀ (ρ : Operator 2) (_hρ : IsDensityOperator ρ) (ω : Reg zs.length),
          instrumentProb I ρ ω = (1 / 2 : ℝ)^zs.length) ∧
        ∃ J : Instrument (Reg zs.length) 2 2,
          (∀ (ω : Reg zs.length) (ρ : Operator 2), J.branch ω ρ =
            (1 / 2 : ℂ)^zs.length • conjBranch (clusterSequenceUnitary zs) ρ) ∧
          (∀ ρ : Operator 2, J.forget.map ρ = conjBranch (clusterSequenceUnitary zs) ρ) := by
  intro zs hzs
  let U : Reg zs.length → Operator 2 := fun ω =>
    clusterSequenceUnitary (adaptiveRealizedWord zs (List.ofFn ω))
  let a : ℂ := ((Real.sqrt 2 : ℂ)⁻¹)^zs.length
  let K : Reg zs.length → Operator 2 := fun ω => a • U ω
  have ht (ω : Reg zs.length) := cluster_adaptive_word_transport zs hzs
    (List.ofFn ω) List.length_ofFn
  have hunit (ω : Reg zs.length) : U ω ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    cluster_sequence_unitary_word_laws.2.2 _ (ht ω).2.2.2.2.1
  have ha : star a*a=(1/2 : ℂ)^zs.length := by
    simpa only [a,star_pow,star_inv,Complex.star_def,map_inv₀,Complex.conj_ofReal] using!
      clusterSeqSqrtPow zs.length
  have hcomplete : ∑ ω : Reg zs.length, (K ω)ᴴ*K ω=1 := by
    have he (ω : Reg zs.length) : (K ω)ᴴ*K ω=(1/2 : ℂ)^zs.length • (1 : Operator 2) := by
      have hh : (U ω)ᴴ*U ω=1 := by
        simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff').mp (hunit ω)
      simp only [K,Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hh]
      rw [mul_comm a (star a),ha]
    simp_rw [he]
    rw [← Finset.sum_smul,adaptive_uniform_sum,one_smul]
  let I := Instrument.ofKraus K hcomplete
  have hb (ω : Reg zs.length) (ρ : Operator 2) :
      I.branch ω ρ=(1/2 : ℂ)^zs.length • conjBranch (U ω) ρ := by
    simp only [I,Instrument.ofKraus_branch,K,conjBranch_apply,
      Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,ha]
  refine ⟨I,?_,?_,clusterSequenceInstrument zs hzs,?_,?_⟩
  · intro ω ρ
    rw [hb]
    dsimp only [U]
    rw [(ht ω).2.2.2.2.2]
    change _ • ((_*ρ)*_ᴴ)=_
    rw [adaptive_conj_phase _ (ht ω).2.2.2.1]
    rfl
  · intro ρ hρ ω
    unfold instrumentProb
    rw [hb,Matrix.trace_smul,trace_conjBranch_unitary _ (hunit ω),hρ.2,smul_eq_mul,mul_one,
      half_pow_cast,Complex.ofReal_re]
  · intro ω ρ
    exact (cluster_sequence_instrument_probability_conditioning zs hzs ρ ω).1
  · intro ρ
    exact (cluster_sequence_instrument_probability_conditioning zs hzs ρ (ZeroStr _)).2.2.1

/-- Every phase in the four-step adaptive Euler word has unit norm. -/
private theorem adaptive_euler_norm (ξ η ζ : ℝ) :
    ∀ z ∈ clusterAdaptiveEulerWord ξ η ζ, ‖z‖=1 := by
  intro z hz
  simp only [clusterAdaptiveEulerWord,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp [Complex.norm_exp]

/-- The four-step Euler word possesses a corrected instrument whose branches are one sixteenth
of nominal unitary conjugation. Summing the branches tensored with the identity on any
finite reference system gives conjugation by the nominal unitary tensored with that identity
[RaussendorfBriegel2000]. -/
theorem cluster_adaptive_euler_corrected_channel :
    ∀ (ξ η ζ : ℝ) (r : ℕ) (X : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ),
      ∃ J : Instrument (Reg (clusterAdaptiveEulerWord ξ η ζ).length) 2 2,
        (∀ (ω : Reg (clusterAdaptiveEulerWord ξ η ζ).length) (ρ : Operator 2),
          J.branch ω ρ = (1 / 2 : ℂ)^4 •
            conjBranch (clusterSequenceUnitary (clusterAdaptiveEulerWord ξ η ζ)) ρ) ∧
        (∑ ω : Reg (clusterAdaptiveEulerWord ξ η ζ).length, tensorLeft (J.branch ω) X) =
          TensorGate (clusterSequenceUnitary (clusterAdaptiveEulerWord ξ η ζ)) (1 : Operator r) * X *
            (TensorGate (clusterSequenceUnitary (clusterAdaptiveEulerWord ξ η ζ)) (1 : Operator r))ᴴ := by
  intro ξ η ζ r X
  obtain ⟨_,_,_,J,hb,hf⟩ := cluster_adaptive_instrument_branches
    (clusterAdaptiveEulerWord ξ η ζ) (adaptive_euler_norm ξ η ζ)
  refine ⟨J,hb,?_⟩
  rw [← tensorLeft_conjBranch]
  ext x y
  have hs (ρ : Operator 2) : ∑ ω, J.branch ω ρ=
      conjBranch (clusterSequenceUnitary (clusterAdaptiveEulerWord ξ η ζ)) ρ := by
    rw [← Instrument.forget_apply]
    exact hf ρ
  simpa only [Matrix.sum_apply,tensorLeft] using!
    congrArg (fun M => M x.1 y.1) (hs (fun i j => X (i,x.2) (j,y.2)))

/-- Every explicit adaptive loop leaf is accepted, makes no queries, uses two gates and one
measurement per phase, and records one outcome per phase. -/
private theorem adaptive_loop_fields (zs : List ℂ) (F : Bool × Bool × ℂ) (ω : Reg zs.length) :
    (clusterAdaptiveLoopLeafGen zs F ω).accepted=true ∧
    (clusterAdaptiveLoopLeafGen zs F ω).queries=0 ∧
    (clusterAdaptiveLoopLeafGen zs F ω).gates=2*zs.length ∧
    (clusterAdaptiveLoopLeafGen zs F ω).measurements=zs.length ∧
    (clusterAdaptiveLoopLeafGen zs F ω).outcomes.length=zs.length := by
  induction zs generalizing F with
  | nil => simp [clusterAdaptiveLoopLeafGen]
  | cons z zs ih =>
    cases zs with
    | nil => simp [clusterAdaptiveLoopLeafGen]
    | cons w ws =>
      obtain ⟨_,_,hg,hm,ho⟩ := ih (adaptiveFrameStep F z (ω 0)) (Fin.tail ω)
      simp only [clusterAdaptiveLoopLeafGen,List.length_cons,hg,hm,ho]
      exact ⟨trivial,trivial,by omega,trivial,trivial⟩

/-- The adaptive loop for a word of length `n` has exactly `2^n` observed leaves. -/
private theorem adaptive_loop_count (zs : List ℂ) (F : Bool × Bool × ℂ) :
    observedLeafCount (clusterAdaptiveLoopFin zs F)=2^zs.length := by
  induction zs generalizing F with
  | nil => rfl
  | cons z zs ih =>
    cases zs with
    | nil => simp [clusterAdaptiveLoopFin,observedLeafCount]
    | cons w ws =>
      simp only [clusterAdaptiveLoopFin,observedLeafCount,observedLeafCount_shiftObservedFin,ih]
      simp [pow_succ,Nat.mul_comm]

/-- Prepending the first phase gate, Hadamard, and measurement projector to a shifted
continuation leaf gives the explicit loop leaf for the extended outcome history. -/
private theorem adaptive_loop_elem (z w : ℂ) (ws : List ℂ) (F : Bool × Bool × ℂ)
    (b : Bool) (j : Fin (2^(w::ws).length)) :
    ObservedKrausLeaf.prepend (clusterSeqPhaseFin (z::w::ws).length (adaptivePhase F.1 z)) 0 1 0 []
      (ObservedKrausLeaf.prepend (clusterSeqHFin (z::w::ws).length) 0 1 0 []
        (ObservedKrausLeaf.prepend (Projector (Finset.univ.filter
          (fun r => clusterSeqLabelFin (z::w::ws).length r=boolEquivFin2 b)))
          0 0 1 [(2,(boolEquivFin2 b).val)]
          (clusterSeqShiftLeaf (w::ws).length
            (clusterAdaptiveLoopLeafGen (w::ws) (adaptiveFrameStep F z b)
              ((bitVecEquiv (w::ws).length).symm j)))))=
      clusterAdaptiveLoopLeafGen (z::w::ws) F
        (Fin.cons b ((bitVecEquiv (w::ws).length).symm j)) := by
  have ha := (adaptive_loop_fields (w::ws) (adaptiveFrameStep F z b)
    ((bitVecEquiv (w::ws).length).symm j)).1
  have hq := (adaptive_loop_fields (w::ws) (adaptiveFrameStep F z b)
    ((bitVecEquiv (w::ws).length).symm j)).2.1
  simp only [clusterAdaptiveLoopLeafGen,Fin.tail_cons,Fin.cons_zero,
    ObservedKrausLeaf.prepend,clusterSeqShiftLeaf,ha,hq,List.nil_append,Nat.add_zero]
  simp [Nat.add_assoc]

set_option maxHeartbeats 1000000 in

/-- The observed Kraus leaves of the adaptive loop are exactly its explicit leaves enumerated by
Boolean histories. -/
private theorem adaptive_loop_leaves (zs : List ℂ) (F : Bool × Bool × ℂ) :
    observedKrausLeaves 1 (clusterAdaptiveLoopFin zs F)=
      List.ofFn (fun i : Fin (2^zs.length) =>
        clusterAdaptiveLoopLeafGen zs F ((bitVecEquiv zs.length).symm i)) := by
  induction zs generalizing F with
  | nil =>
    rw [show clusterAdaptiveLoopFin [] F=ObservedCircuit.halt true from rfl,
      observedKrausLeaves,clusterSeqOfFn_fin1]
    rfl
  | cons z zs ih =>
    cases zs with
    | nil =>
      simp only [clusterAdaptiveLoopFin,observedKrausLeaves]
      rw [List.map_flatten,List.map_ofFn,List.map_flatten,List.map_ofFn,Function.comp_def]
      change _=List.ofFn
          (fun i : Fin 2 => clusterAdaptiveLoopLeafGen [z] F ((bitVecEquiv 1).symm i))
      simp only [clusterAdaptiveLoopLeafGen,clusterSeqBitVec_one_label,clusterSeqOfFn_fin2,
        List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.nil_append,
        List.cons_append,ObservedKrausLeaf.prepend,Matrix.one_mul,Function.comp_apply]
      rfl
    | cons w ws =>
      have hlen : (observedKrausLeaves 1 (clusterAdaptiveLoopFin (z::w::ws) F)).length=
          2^(z::w::ws).length := by rw [observedKrausLeaves_length,adaptive_loop_count]
      apply List.ext_getElem?'
      intro v hv
      rw [hlen,List.length_ofFn] at hv
      have hv' : v < 2^(z::w::ws).length := by omega
      have hvL : v < (observedKrausLeaves 1 (clusterAdaptiveLoopFin (z::w::ws) F)).length := by
        rw [hlen]; exact hv'
      rw [List.getElem?_eq_getElem hvL,List.getElem?_eq_getElem (by simp; exact hv')]
      simp only [Option.some.injEq]
      rw [List.getElem_ofFn (by rw [List.length_ofFn]; exact hv')]
      simp only [clusterAdaptiveLoopFin,observedKrausLeaves,observedKrausLeaves_shiftObservedFin,ih,
        List.map_ofFn,Function.comp_def,clusterSeqOfFn_fin2,List.flatten_cons,List.flatten_nil,
        List.append_nil]
      have hpow : 2^(z::w::ws).length=2^(w::ws).length+2^(w::ws).length := by
        simp only [List.length_cons,pow_succ]
        omega
      by_cases h : v < 2^(w::ws).length
      · rw [List.getElem_map,List.getElem_map,
          List.getElem_append_left (by rw [List.length_ofFn]; exact h),
          List.getElem_ofFn (by rw [List.length_ofFn]; exact h)]
        change _=clusterAdaptiveLoopLeafGen (z::w::ws) F
            ((bitVecEquiv (z::w::ws).length).symm ⟨v,hv'⟩)
        rw [show (0 : Fin 2)=boolEquivFin2 false from rfl,
          show boolEquivFin2.symm (boolEquivFin2 false)=false from rfl,adaptive_loop_elem]
        exact congrArg (clusterAdaptiveLoopLeafGen (z::w::ws) F)
          (clusterSeqBitVec_symm_low (w::ws).length v hv' h).symm
      · rw [List.getElem_map,List.getElem_map,
          List.getElem_append_right (by rw [List.length_ofFn]; omega)]
        simp only [List.length_ofFn]
        rw [List.getElem_ofFn (by rw [List.length_ofFn]; omega)]
        rw [show (1 : Fin 2)=boolEquivFin2 true from rfl,
          show boolEquivFin2.symm (boolEquivFin2 true)=true from rfl,adaptive_loop_elem]
        exact congrArg (clusterAdaptiveLoopLeafGen (z::w::ws) F)
          (clusterSeqBitVec_symm_high (w::ws).length v hv' (by omega)).symm

/-- The adaptive program has one accepted leaf per Boolean history, with no queries, one
measurement per phase, four gates per phase, and one recorded outcome per phase
[RaussendorfBriegel2000]. -/
theorem cluster_adaptive_program_leaves_and_cost :
    ∀ (zs : List ℂ), observedLeafCount (clusterAdaptiveProgram zs)=2^zs.length ∧
      observedKrausLeaves 1 (clusterAdaptiveProgram zs)=
        List.ofFn (fun i : Fin (2^zs.length) =>
          clusterAdaptiveProgramLeafGen zs ((bitVecEquiv zs.length).symm i)) ∧
      (∀ ω : Reg zs.length, (clusterAdaptiveProgramLeafGen zs ω).accepted=true ∧
        (clusterAdaptiveProgramLeafGen zs ω).queries=0 ∧
        (clusterAdaptiveProgramLeafGen zs ω).measurements=zs.length ∧
        (clusterAdaptiveProgramLeafGen zs ω).gates=4*zs.length ∧
        (clusterAdaptiveProgramLeafGen zs ω).outcomes.length=zs.length) := by
  intro zs
  refine ⟨?_,?_,?_⟩
  · rw [clusterAdaptiveProgram,observedLeafCount_prependSteps,adaptive_loop_count]
  · rw [clusterAdaptiveProgram,observedKrausLeaves_prependSteps,adaptive_loop_leaves,
      clusterSeqFullGate_one,List.map_ofFn]
    have hq : QueryCount (clusterSequenceResourceCircuit zs.length)=0 := by
      rw [clusterSequenceResourceCircuit,(relabelCircuit_legality_resources _ _).2.1,
        queryCount_resourceCircuitB]
    have hg : GateCount (clusterSequenceResourceCircuit zs.length)=2*zs.length := by
      rw [clusterSequenceResourceCircuit,(relabelCircuit_legality_resources _ _).2.2.1,
        gateCount_resourceCircuitB]
    apply clusterSeqOfFn_congr
    intro i
    simp only [clusterAdaptiveProgramLeafGen,hq,hg,
      show clusterSeqCircuitGate (clusterSequenceResourceCircuit zs.length)=
        clusterSequenceResourceGate zs.length from rfl,Function.comp_apply]
  · intro ω
    obtain ⟨ha,hq,hg,hm,ho⟩ := adaptive_loop_fields zs (false,false,1) ω
    simp only [clusterAdaptiveProgramLeafGen,ObservedKrausLeaf.prepend,ha,hq,hg,hm,ho,
      List.nil_append,Nat.add_zero]
    exact ⟨trivial,trivial,trivial,by omega,trivial⟩

/-- The realized adaptive phase word from a specified initial frame and Boolean outcome history. -/
private def adaptiveHistoryWord (zs : List ℂ) (F : Bool × Bool × ℂ) (ω : Reg zs.length) : List ℂ :=
  (adaptiveRunFold F (zs.zip (List.ofFn ω))).2

/-- The realized history word splits into the first outcome-adjusted phase and the tail word
computed from the updated frame. -/
private theorem adaptive_history_cons (z : ℂ) (zs : List ℂ) (F : Bool × Bool × ℂ)
    (ω : Reg (z::zs).length) : adaptiveHistoryWord (z::zs) F ω=
      ((if ω 0 then (-1 : ℂ) else 1)*adaptivePhase F.1 z)::
        adaptiveHistoryWord zs (adaptiveFrameStep F z (ω 0)) (Fin.tail ω) := by
  simp only [adaptiveHistoryWord,List.ofFn_succ,List.zip_cons_cons,adaptiveRunFold]
  rfl

/-- The adaptive loop branch operator on Boolean registers, formed recursively from phase gates,
Hadamards, measurement projectors, and shifted continuation operators. -/
private def adaptiveLoopB : (zs : List ℂ) → (Bool × Bool × ℂ) → Reg zs.length →
    Matrix (Reg (zs.length+1)) (Reg (zs.length+1)) ℂ
  | [], _, _ => 1
  | z::zs, F, ω =>
      clusterSeqShiftOp zs.length (adaptiveLoopB zs (adaptiveFrameStep F z (ω 0)) (Fin.tail ω))*
        Projector (Finset.univ.filter (fun x : Reg ((z::zs).length+1) => x 0=ω 0))*
        clusterSeqOneBitB (z::zs).length 0 Hadamard*
        clusterSeqOneBitB (z::zs).length 0 (clusterSeqPhaseB (adaptivePhase F.1 z))

/-- Relabeling the Boolean-register adaptive branch operator gives the operator of the explicit
finite-index loop leaf. -/
private theorem adaptive_loop_operator (zs : List ℂ) (F : Bool × Bool × ℂ) (ω : Reg zs.length) :
    (clusterAdaptiveLoopLeafGen zs F ω).operator=
      relabelGate (bitVecEquiv (zs.length+1)) (adaptiveLoopB zs F ω) := by
  induction zs generalizing F with
  | nil => simp [clusterAdaptiveLoopLeafGen,adaptiveLoopB,CircuitRelabel.relabelGate_one]
  | cons z zs ih =>
    cases zs with
    | nil =>
      simp only [clusterAdaptiveLoopLeafGen,adaptiveLoopB,clusterSeqShiftOp_one,
        Matrix.one_mul,clusterSeqHFin,clusterSeqPhaseFin,clusterSeqOneBitFin]
      rw [clusterSeqProjectorFin_eq 1 (ω 0),← CircuitRelabel.relabelGate_mul,
        ← CircuitRelabel.relabelGate_mul]
      rfl
    | cons w ws =>
      rw [clusterAdaptiveLoopLeafGen]
      conv_rhs => rw [adaptiveLoopB]
      simp only [clusterSeqHFin,clusterSeqPhaseFin,clusterSeqOneBitFin]
      rw [ih,clusterSeqShiftGateFin_relabel,clusterSeqProjectorFin_eq _ (ω 0)]
      have hE : ∀ M : Matrix (Reg ((z::w::ws).length+1)) (Reg ((z::w::ws).length+1)) ℂ,
          relabelGate (bitVecEquiv ((w::ws).length+2)) M=
            relabelGate (bitVecEquiv ((z::w::ws).length+1)) M := fun _ => rfl
      rw [hE _]
      rw [← CircuitRelabel.relabelGate_mul,← CircuitRelabel.relabelGate_mul,
        ← CircuitRelabel.relabelGate_mul]

/-- The explicit adaptive program leaf operator is the relabeling of the Boolean-register loop
operator composed with resource preparation. -/
private theorem adaptive_program_operator (zs : List ℂ) (ω : Reg zs.length) :
    (clusterAdaptiveProgramLeafGen zs ω).operator=
      relabelGate (bitVecEquiv (zs.length+1)) (adaptiveLoopB zs (false,false,1) ω*
        clusterSeqResourceGateB zs.length) := by
  change (clusterAdaptiveLoopLeafGen zs (false,false,1) ω).operator*
    clusterSequenceResourceGate zs.length=_
  rw [adaptive_loop_operator,clusterSequenceResourceGate_eq_relabel,
    ← CircuitRelabel.relabelGate_mul]

/-- Left multiplication of `clusterJ z` by the Boolean-selected Pauli X changes the sign of its
phase when the bit is true. -/
private theorem adaptive_XJ (z : ℂ) (b : Bool) :
    relabelGate boolEquivFin2 (if b then PauliX else 1)*clusterJ z=
      clusterJ ((if b then (-1 : ℂ) else 1)*z) := by
  cases b
  · simp [CircuitRelabel.relabelGate_one]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.mul_apply,
        Fin.sum_univ_two,PauliX,permMatrix,boolEquivFin2,clusterJ_entry]

/-- The first adaptive raw step factors off the measured basis state and continues on the
remaining chain with the updated frame and a `1 / √2`-scaled `clusterJ` output. -/
private theorem adaptive_raw_step (zs : List ℂ) (z : ℂ) (F : Bool × Bool × ℂ)
    (a : Bool) (ω : Reg zs.length) (φ : QState (Fin 2)) :
    (adaptiveLoopB (z::zs) F (Fin.cons a ω)*clusterSeqResourceGateB (zs.length+1))*ᵥ
      (clusterSeqInitialFrameB (zs.length+1)*ᵥ φ)=
      relabelState (Fin.consEquiv (fun _ : Fin (zs.length+2) => Bool))
        (TensorState (Qatlib.Foundations.PureStateMath.Ket a)
          ((adaptiveLoopB zs (adaptiveFrameStep F z a) ω*clusterSeqResourceGateB zs.length)*ᵥ
            (clusterSeqInitialFrameB zs.length*ᵥ
              ((Real.sqrt 2 : ℂ)⁻¹ •
                (clusterJ ((if a then (-1 : ℂ) else 1)*adaptivePhase F.1 z)*ᵥ φ))))) := by
  rw [adaptiveLoopB]
  simp only [Fin.cons_zero,Fin.tail_cons,List.length_cons]
  rw [clusterSeqResourceGateB_succ]
  conv_lhs => repeat rw [clusterSeqMulVecAssoc]
  rw [Fin.succ_zero_eq_one,clusterSeqMeasureQ0,clusterSeqShiftOp_mulVec_tensor,
    Matrix.mulVec_mulVec φ (relabelGate boolEquivFin2 (if a then PauliX else 1))
      (clusterJ (adaptivePhase F.1 z)),adaptive_XJ]
  simp only [clusterSeqMulVecAssoc]

/-- A register prefix equals a Boolean cons exactly when its first bit and remaining prefix
equal the specified head and tail. -/
private theorem adaptive_front_cons {m : ℕ} (x : Reg (m+2)) (a : Bool) (ω : Reg m) :
    (fun j => x (Fin.castSucc j))=Fin.cons a ω ↔
      x 0=a ∧ (fun j => Fin.tail x (Fin.castSucc j))=ω := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · simpa using! congrFun h 0
    · funext j
      simpa using! congrFun h j.succ
  · rintro ⟨h0,ht⟩
    funext j
    cases j using Fin.cases with
    | zero => simpa using! h0
    | succ j => simpa using! congrFun ht j

/-- An adaptive Boolean-register leaf is supported on its specified measurement history. On that
history its output amplitude is `1 / √2` to the word length times the realized sequence
applied to the input state. -/
private theorem adaptive_leaf_physics (zs : List ℂ) (F : Bool × Bool × ℂ)
    (ω : Reg zs.length) (φ : QState (Fin 2)) :
    (adaptiveLoopB zs F ω*clusterSeqResourceGateB zs.length)*ᵥ
      (clusterSeqInitialFrameB zs.length*ᵥ φ)=
      (fun x : Reg (zs.length+1) => if (fun j => x (Fin.castSucc j))=ω then
        ((Real.sqrt 2 : ℂ)⁻¹)^zs.length*
          (clusterSequenceUnitary (adaptiveHistoryWord zs F ω)*ᵥ φ)
            (boolEquivFin2 (x (Fin.last zs.length))) else 0) := by
  induction zs generalizing F φ with
  | nil =>
    simpa only [adaptiveLoopB,adaptiveHistoryWord,List.zip_nil_left,adaptiveRunFold] using!
      clusterSeqLeafPhysics [] (by simp) ω φ
  | cons z zs ih =>
    have hω : ω=Fin.cons (ω 0) (Fin.tail ω) := (Fin.cons_self_tail ω).symm
    rw [hω]
    simp only [List.length_cons]
    rw [adaptive_raw_step]
    rw [ih]
    funext x
    change Qatlib.Foundations.PureStateMath.Ket (ω 0) (x 0)*
      (if (fun j => Fin.tail x (Fin.castSucc j))=Fin.tail ω then
        ((Real.sqrt 2 : ℂ)⁻¹)^zs.length*
          (clusterSequenceUnitary (adaptiveHistoryWord zs (adaptiveFrameStep F z (ω 0)) (Fin.tail ω))*ᵥ
            ((Real.sqrt 2 : ℂ)⁻¹ •
              (clusterJ ((if ω 0 then (-1 : ℂ) else 1)*adaptivePhase F.1 z)*ᵥ φ)))
                (boolEquivFin2 (Fin.tail x (Fin.last zs.length))) else 0)=_
    have hlast : Fin.tail x (Fin.last zs.length)=x (Fin.last (zs.length+1)) := rfl
    rw [hlast,adaptive_history_cons]
    simp only [Fin.cons_zero,Fin.tail_cons,clusterSequenceUnitary,applyGate_smul',pow_succ,
      Pi.smul_apply,smul_eq_mul,← Matrix.mulVec_mulVec]
    have hf := adaptive_front_cons x (ω 0) (Fin.tail ω)
    simp only [hf,Qatlib.Foundations.PureStateMath.Ket]
    by_cases h0 : x 0=ω 0 <;>
      by_cases ht : (fun j => Fin.tail x (Fin.castSucc j))=Fin.tail ω <;>
        simp only [h0,ht,if_true,if_false,and_true,and_false,
          one_mul,zero_mul]
    ring

/-- For unit-modulus nominal phases, a raw adaptive leaf has zero amplitude on other outcome
histories and amplitude `1 / √2` to the word length times the realized sequence on its own
history [RaussendorfBriegel2000]. -/
theorem cluster_adaptive_raw_leaf_amplitude :
    ∀ (zs : List ℂ) (_hzs : ∀ z ∈ zs, ‖z‖ = 1) (ω v : Reg zs.length) (c i : Fin 2),
      ((clusterAdaptiveProgramLeafGen zs ω).operator*clusterSequenceInitialFrame zs.length)
        (clusterSequenceRegisterEquiv zs.length (v,boolEquivFin2.symm c)) i=
        if v=ω then ((Real.sqrt 2 : ℂ)⁻¹)^zs.length*
          (clusterSequenceUnitary (adaptiveRealizedWord zs (List.ofFn ω))*ᵥ
            (fun j => if i=j then (1 : ℂ) else 0)) c else 0 := by
  intro zs _ ω v c i
  let φ : QState (Fin 2) := fun j => if i=j then 1 else 0
  let r := clusterSequenceRegisterEquiv zs.length (v,boolEquivFin2.symm c)
  have hcol : ((clusterAdaptiveProgramLeafGen zs ω).operator*clusterSequenceInitialFrame zs.length) r i=
      (((clusterAdaptiveProgramLeafGen zs ω).operator*clusterSequenceInitialFrame zs.length)*ᵥ φ) r := by
    exact (clusterSeqSum_col _ i).symm
  rw [hcol,adaptive_program_operator,clusterSeqMulVecAssoc,clusterSequenceInitialFrame_mulVec]
  rw [show relabelGate (bitVecEquiv (zs.length+1))
        (adaptiveLoopB zs (false,false,1) ω*clusterSeqResourceGateB zs.length)*ᵥ
      relabelState (bitVecEquiv (zs.length+1)) (clusterSeqInitialFrameB zs.length*ᵥ φ)=
      relabelState (bitVecEquiv (zs.length+1))
        ((adaptiveLoopB zs (false,false,1) ω*clusterSeqResourceGateB zs.length)*ᵥ
          (clusterSeqInitialFrameB zs.length*ᵥ φ)) from applyGate_relabelGate _ _ _,
    adaptive_leaf_physics,relabelState_apply]
  have hr : (bitVecEquiv (zs.length+1)).symm r=
      (regSuccEquiv zs.length).symm (v,boolEquivFin2.symm c) := by
    simp [r,clusterSequenceRegisterEquiv]
  rw [hr]
  have hf : (fun j => (regSuccEquiv zs.length).symm (v,boolEquivFin2.symm c)
      (Fin.castSucc j))=v := funext (clusterSeqRegSucc_symm_front zs.length v _)
  rw [hf,clusterSeqRegSucc_symm_last,Equiv.apply_symm_apply]
  rfl

/-- Every leaf of the four-step adaptive Euler program uses four measurements, sixteen gates,
and no queries. Its realized sequence equals the nominal sequence with the final scalar
Pauli frame, and its amplitudes satisfy the stated history-supported branch formula
[RaussendorfBriegel2000]. -/
theorem cluster_adaptive_euler_pattern :
    ∀ (ξ η ζ : ℝ) (ω : Reg (clusterAdaptiveEulerWord ξ η ζ).length),
      (clusterAdaptiveProgramLeafGen (clusterAdaptiveEulerWord ξ η ζ) ω).measurements=4 ∧
      (clusterAdaptiveProgramLeafGen (clusterAdaptiveEulerWord ξ η ζ) ω).gates=16 ∧
      (clusterAdaptiveProgramLeafGen (clusterAdaptiveEulerWord ξ η ζ) ω).queries=0 ∧
      clusterSequenceUnitary (adaptiveRealizedWord (clusterAdaptiveEulerWord ξ η ζ) (List.ofFn ω))=
        (adaptiveFinalFrame (clusterAdaptiveEulerWord ξ η ζ) (List.ofFn ω)).2.2 •
          (adaptiveFrameGate (adaptiveFinalFrame (clusterAdaptiveEulerWord ξ η ζ) (List.ofFn ω))*
            clusterSequenceUnitary (clusterAdaptiveEulerWord ξ η ζ)) ∧
      ∀ (v : Reg (clusterAdaptiveEulerWord ξ η ζ).length) (c i : Fin 2),
        ((clusterAdaptiveProgramLeafGen (clusterAdaptiveEulerWord ξ η ζ) ω).operator*
          clusterSequenceInitialFrame (clusterAdaptiveEulerWord ξ η ζ).length)
          (clusterSequenceRegisterEquiv (clusterAdaptiveEulerWord ξ η ζ).length
            (v,boolEquivFin2.symm c)) i=
          if v=ω then ((Real.sqrt 2 : ℂ)⁻¹)^4*
            ((adaptiveFinalFrame (clusterAdaptiveEulerWord ξ η ζ) (List.ofFn ω)).2.2 •
              (adaptiveFrameGate (adaptiveFinalFrame (clusterAdaptiveEulerWord ξ η ζ) (List.ofFn ω))*
                clusterSequenceUnitary (clusterAdaptiveEulerWord ξ η ζ))*ᵥ
                  (fun j => if i=j then (1 : ℂ) else 0)) c else 0 := by
  intro ξ η ζ ω
  have hc := (cluster_adaptive_program_leaves_and_cost (clusterAdaptiveEulerWord ξ η ζ)).2.2 ω
  have ht := cluster_adaptive_word_transport (clusterAdaptiveEulerWord ξ η ζ)
    (adaptive_euler_norm ξ η ζ) (List.ofFn ω) List.length_ofFn
  refine ⟨hc.2.2.1,hc.2.2.2.1,hc.2.1,ht.2.2.2.2.2,?_⟩
  intro v c i
  rw [cluster_adaptive_raw_leaf_amplitude _ (adaptive_euler_norm ξ η ζ),ht.2.2.2.2.2]
  simp only [show (clusterAdaptiveEulerWord ξ η ζ).length=4 from rfl,Matrix.smul_mulVec]

end AdaptiveProofs
end Qatlib.Concepts.ClusterPatterns.AdaptiveEuler
