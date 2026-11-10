/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompletenessRefinedDefs
import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompletenessEnergy
import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompletenessVerifier
import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompletenessCounterexamples
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Concepts.QmaCompleteness.HistoryHam

open scoped Classical BigOperators
open Qatlib
open Matrix

theorem mwGoodProjector_offdiag (p : WitnessVerifierProgram)
    (u u' : Reg (programQubits p)) (hne : u ≠ u') : mwGoodProjector p u u' = 0 := by
  simp [mwGoodProjector, hne]

theorem mwGoodProjector_diag (p : WitnessVerifierProgram) (u : Reg (programQubits p)) :
    mwGoodProjector p u u = if u ∈ programOutputEvent p then 1 else 0 := by
  by_cases ho : u ∈ programOutputEvent p
  · simp [mwGoodProjector, ho]
  · simp [mwGoodProjector, ho]

theorem mwRound_offdiag (p : WitnessVerifierProgram)
    (u u' : Reg (programQubits p)) (hne : u ≠ u') : mwRound p u u' = 0 := by
  simp [mwRound, hne]

theorem mwRound_diag (p : WitnessVerifierProgram) (u : Reg (programQubits p)) :
    mwRound p u u = if u ∈ programOutputEvent p then 0 else 1 := by
  by_cases ho : u ∈ programOutputEvent p
  · simp [mwRound, ho]
  · simp [mwRound, ho]

theorem mwTwoProjectionsOrthogonal (p : WitnessVerifierProgram) :
    MwTwoProjectionsOrthogonal p := by
  refine ⟨?_, ?_⟩
  · intro u
    exact mwGoodProjector_diag p u
  · intro u u' hne
    exact mwGoodProjector_offdiag p u u' hne

theorem mwRound_preserves_witness (p : WitnessVerifierProgram) :
    MwWitnessPreserving p (mwRound p) := by
  intro u u' h
  by_cases hd : u = u'
  · rw [hd]
  · have hz := mwRound_offdiag p u u' hd
    rw [hz] at h
    exact (h rfl).elim

theorem mwGoodProjector_preserves_witness (p : WitnessVerifierProgram) :
    MwWitnessPreserving p (mwGoodProjector p) := by
  intro u u' h
  by_cases hd : u = u'
  · rw [hd]
  · have hz := mwGoodProjector_offdiag p u u' hd
    rw [hz] at h
    exact (h rfl).elim

theorem mwVerificationWires_le (p : WitnessVerifierProgram) :
    mwVerificationWires p ≤ programQubits p := by
  unfold mwVerificationWires
  have h : p.witnessBits ≤ programQubits p := by
    unfold programQubits
    omega
  omega

section Clause2Helpers

theorem clause2Aux_mulVec_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (c : ℂ) (v : ι → ℂ) :
    A *ᵥ (fun y => c * v y) = fun y => c * (A *ᵥ v) y := by
  have h := Matrix.mulVec_smul A c v
  simpa only [Pi.smul_def, smul_eq_mul] using h

theorem clause2Aux_qmaGateAt_getElem (gs : List FiniteGateCode) (t : ℕ) (h : t < gs.length) :
    qmaGateAt gs t = gs[t] := by
  unfold qmaGateAt
  rw [List.drop_eq_getElem_cons h]

theorem clause2Aux_finiteWordMatrix_append (n : ℕ) (l : List FiniteGateCode) (g : FiniteGateCode) :
    finiteWordMatrix n (l ++ [g]) = finiteCodeMatrix n g * finiteWordMatrix n l := by
  induction l with
  | nil => simp [finiteWordMatrix]
  | cons a as ih =>
    show finiteWordMatrix n (a :: (as ++ [g]))
        = finiteCodeMatrix n g * finiteWordMatrix n (a :: as)
    rw [show finiteWordMatrix n (a :: (as ++ [g]))
        = finiteWordMatrix n (as ++ [g]) * finiteCodeMatrix n a from rfl]
    rw [show finiteWordMatrix n (a :: as)
        = finiteWordMatrix n as * finiteCodeMatrix n a from rfl]
    rw [ih, Matrix.mul_assoc]

end Clause2Helpers

theorem clause2Aux_history_slice (C : QmaHistoryCircuit) (φ : QState (Reg C.qubits))
    (t : Fin (C.gates.length + 1)) (y : Reg C.qubits) :
    sl (qmaHistoryState C φ) t y
      = (((Real.sqrt (C.gates.length + 1))⁻¹ : ℝ) : ℂ) * qmaExactHistory C φ t y := rfl

theorem clause2Aux_exact_history_step (C : QmaHistoryCircuit) (φ : QState (Reg C.qubits))
    (i : Fin C.gates.length) :
    qmaExactHistory C φ i.succ
      = (qmaExactGates C i) *ᵥ qmaExactHistory C φ i.castSucc := by
  have hi : i.val < C.gates.length := i.isLt
  have hget : qmaGateAt C.gates i.val = C.gates[i.val] :=
    clause2Aux_qmaGateAt_getElem C.gates i.val hi
  have htake : C.gates.take (i.val + 1) = C.gates.take i.val ++ [C.gates[i.val]] :=
    List.take_succ_eq_append_getElem hi
  have hL : qmaExactHistory C φ i.succ
      = (finiteWordMatrix C.qubits (C.gates.take (i.val + 1))).mulVec φ := by
    show (finiteWordMatrix C.qubits (C.gates.take (i.succ.val))).mulVec φ = _
    rfl
  have hR : qmaExactHistory C φ i.castSucc
      = (finiteWordMatrix C.qubits (C.gates.take i.val)).mulVec φ := by
    show (finiteWordMatrix C.qubits (C.gates.take (i.castSucc.val))).mulVec φ = _
    rfl
  have hG : qmaExactGates C i = finiteCodeMatrix C.qubits (C.gates[i.val]) := by
    show finiteCodeMatrix C.qubits (qmaGateAt C.gates i.val) = _
    rw [hget]
  rw [hL, hR, hG, htake, clause2Aux_finiteWordMatrix_append, Matrix.mulVec_mulVec]

theorem clause2Aux_mulVec_sub_neg {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v : ι → ℂ) :
    (A - B) *ᵥ v = -((B - A) *ᵥ v) := by
  have h1 : (A - B) *ᵥ v = A *ᵥ v - B *ᵥ v := by
    simp only [sub_eq_add_neg, Matrix.add_mulVec, Matrix.neg_mulVec]
  have h2 : (B - A) *ᵥ v = B *ᵥ v - A *ᵥ v := by
    simp only [sub_eq_add_neg, Matrix.add_mulVec, Matrix.neg_mulVec]
  rw [h1, h2]
  ring

theorem clause2Aux_nm_sub_neg {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v : ι → ℂ) :
    nm ((A - B) *ᵥ v) = nm ((B - A) *ᵥ v) := by
  have h1 : (A - B) *ᵥ v = -((B - A) *ᵥ v) := clause2Aux_mulVec_sub_neg A B v
  rw [h1]
  have h2 : nm (-((B - A) *ᵥ v)) = nm ((B - A) *ᵥ v) := by
    unfold nm
    congr 1
    unfold vn
    apply Finset.sum_congr rfl
    intro y _
    rw [Pi.neg_apply, norm_neg]
  exact h2

theorem clause2Aux_rounded_gate_vn_lower (n b : ℕ) (g : FiniteGateCode)
    (hg : finiteCodeLegal n g = true) (v : QState (Reg n))
    (hκ : g13n2_kappa n b ≤ 1) :
    (1 - g13n2_kappa n b) ^ 2 * vn v ≤ vn (qmaRoundedGate n b g *ᵥ v) := by
  have hU : finiteCodeMatrix n g ∈ Matrix.unitaryGroup (Reg n) ℂ :=
    finiteCodeMatrix_unitary n g hg
  have hUnm : nm (finiteCodeMatrix n g *ᵥ v) = nm v := g13n2_unitary_nm hU v
  have hD := g13n2_round_gate_vec n b g v
  have hneg : nm ((finiteCodeMatrix n g - qmaRoundedGate n b g) *ᵥ v)
      = nm ((qmaRoundedGate n b g - finiteCodeMatrix n g) *ᵥ v) :=
    clause2Aux_nm_sub_neg _ _ _
  have hsplit : finiteCodeMatrix n g *ᵥ v
      = fun y => (qmaRoundedGate n b g *ᵥ v) y
          + ((finiteCodeMatrix n g - qmaRoundedGate n b g) *ᵥ v) y :=
    g13n2_split_mulVec (finiteCodeMatrix n g) (qmaRoundedGate n b g) v
  have htri := g13n2_nm_add (qmaRoundedGate n b g *ᵥ v)
    ((finiteCodeMatrix n g - qmaRoundedGate n b g) *ᵥ v)
  have hnm : nm (finiteCodeMatrix n g *ᵥ v)
      ≤ nm (qmaRoundedGate n b g *ᵥ v)
        + nm ((finiteCodeMatrix n g - qmaRoundedGate n b g) *ᵥ v) := by
    rw [hsplit]
    exact htri
  have hD' : nm ((finiteCodeMatrix n g - qmaRoundedGate n b g) *ᵥ v)
      ≤ g13n2_kappa n b * nm v := by
    rw [hneg]
    exact hD
  have hκ0 : 0 ≤ g13n2_kappa n b := g13n2_kappa_nonneg n b
  have h1κ : 0 ≤ 1 - g13n2_kappa n b := by linarith
  have h2 : (1 - g13n2_kappa n b) * nm v ≤ nm (qmaRoundedGate n b g *ᵥ v) := by
    rw [hUnm] at hnm
    linarith
  have hsq : (1 - g13n2_kappa n b) ^ 2 * nm v ^ 2
      ≤ nm (qmaRoundedGate n b g *ᵥ v) ^ 2 := by
    have hnonneg : 0 ≤ (1 - g13n2_kappa n b) * nm v :=
      mul_nonneg h1κ (nm_nonneg v)
    have hnonneg2 : 0 ≤ nm (qmaRoundedGate n b g *ᵥ v) := nm_nonneg _
    nlinarith
  rw [nm_sq, nm_sq] at hsq
  exact hsq

theorem clause2Aux_kappa_le_one (C : QmaHistoryCircuit) :
    g13n2_kappa C.qubits (qmaClause2Bits C) ≤ 1 := by
  have h := g2c2_tiny_absorb C.qubits C.gates.length
  have ht : qmaTiny (C.qubits + C.gates.length + 2) ≤ 1 := by
    unfold qmaTiny
    have hone : 1 ≤ (2 : ℝ) ^ (C.qubits + C.gates.length + 2) :=
      one_le_pow₀ (by norm_num)
    have hpos : 0 < (2 : ℝ) ^ (C.qubits + C.gates.length + 2) := by positivity
    rw [inv_pow]
    exact (inv_le_one₀ hpos).mpr hone
  show g13n2_kappa C.qubits (3 * (C.qubits + C.gates.length) + 64) ≤ 1
  have hsq0 : 0 ≤ g13n2_kappa C.qubits (3 * (C.qubits + C.gates.length) + 64) ^ 2 / 2 := by
    positivity
  linarith

theorem clause2Aux_prop_energy_le (C : QmaHistoryCircuit) (φ : QState (Reg C.qubits))
    (hφ : Normalized φ) (b : ℕ) (i : Fin C.gates.length)
    (hκ : g13n2_kappa C.qubits b ≤ 1) :
    qmaEnergy (qmaPropTerm C.qubits C.gates.length (qmaRoundedGates C b) i)
        (qmaHistoryState C φ)
      ≤ g13n2_kappa C.qubits b / (C.gates.length + 1) := by
  set κ : ℝ := g13n2_kappa C.qubits b with hκdef
  set c : ℂ := (((Real.sqrt (C.gates.length + 1))⁻¹ : ℝ) : ℂ) with hc
  have hcsq : ‖c‖ ^ 2 = 1 / (C.gates.length + 1 : ℝ) := by
    have h1 : ‖c‖ = (Real.sqrt (C.gates.length + 1))⁻¹ := by
      rw [hc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    have h2 : ((Real.sqrt (C.gates.length + 1))⁻¹ : ℝ) ^ 2
        = 1 / (C.gates.length + 1 : ℝ) := by
      rw [inv_pow, Real.sq_sqrt (by positivity), one_div]
    rw [h1, h2]
  have hψnorm : ∀ t : Fin (C.gates.length + 1), vn (qmaExactHistory C φ t) = 1 := by
    intro t
    exact normalized_qmaExactHistory hφ t
  have hsl_cast_fn : sl (qmaHistoryState C φ) i.castSucc
      = fun y => c * qmaExactHistory C φ i.castSucc y := by
    funext y
    exact clause2Aux_history_slice C φ i.castSucc y
  have hsl_succ_pt : ∀ y : Reg C.qubits,
      sl (qmaHistoryState C φ) i.succ y = c * qmaExactHistory C φ i.succ y := by
    intro y
    exact clause2Aux_history_slice C φ i.succ y
  have hstep := clause2Aux_exact_history_step C φ i
  have hleg : finiteCodeLegal C.qubits (qmaGateAt C.gates i.val) = true :=
    g13n2_hist_gateAt_legal C i.isLt
  have hvn_cast : vn (sl (qmaHistoryState C φ) i.castSucc)
      = 1 / (C.gates.length + 1 : ℝ) := by
    rw [hsl_cast_fn, vn_smul, hcsq, hψnorm]
    ring
  have hlow0 := clause2Aux_rounded_gate_vn_lower C.qubits b (qmaGateAt C.gates i.val) hleg
    (qmaExactHistory C φ i.castSucc) hκ
  have hlow : (1 - g13n2_kappa C.qubits b) ^ 2 * vn (qmaExactHistory C φ i.castSucc)
      ≤ vn (qmaRoundedGates C b i *ᵥ qmaExactHistory C φ i.castSucc) := by
    simpa only [qmaRoundedGates] using hlow0
  have hlinR : ∀ y : Reg C.qubits,
      (qmaRoundedGates C b i *ᵥ sl (qmaHistoryState C φ) i.castSucc) y
        = c * ((qmaRoundedGates C b i) *ᵥ qmaExactHistory C φ i.castSucc) y := by
    intro y
    have htmp : qmaRoundedGates C b i *ᵥ sl (qmaHistoryState C φ) i.castSucc
        = qmaRoundedGates C b i *ᵥ (fun y => c * qmaExactHistory C φ i.castSucc y) := by
      rw [hsl_cast_fn]
    rw [htmp]
    have h := congrFun (clause2Aux_mulVec_smul (qmaRoundedGates C b i) c
      (qmaExactHistory C φ i.castSucc)) y
    rw [h]
  have hvnR : vn (qmaRoundedGates C b i *ᵥ sl (qmaHistoryState C φ) i.castSucc)
      ≥ (1 - κ) ^ 2 / (C.gates.length + 1 : ℝ) := by
    calc vn (qmaRoundedGates C b i *ᵥ sl (qmaHistoryState C φ) i.castSucc)
        = ‖c‖ ^ 2 * vn (qmaRoundedGates C b i *ᵥ qmaExactHistory C φ i.castSucc) := by
          have hfun : qmaRoundedGates C b i *ᵥ sl (qmaHistoryState C φ) i.castSucc
              = fun y => c * ((qmaRoundedGates C b i)
                  *ᵥ qmaExactHistory C φ i.castSucc) y := by
            rw [hsl_cast_fn]
            exact clause2Aux_mulVec_smul (qmaRoundedGates C b i) c
              (qmaExactHistory C φ i.castSucc)
          rw [hfun, vn_smul]
        _ ≥ ‖c‖ ^ 2 * ((1 - g13n2_kappa C.qubits b) ^ 2
            * vn (qmaExactHistory C φ i.castSucc)) :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
        _ = (1 - κ) ^ 2 / (C.gates.length + 1 : ℝ) := by
          rw [hcsq, hψnorm i.castSucc]
          ring
  have hpoint : ∀ y : Reg C.qubits,
      sl (qmaHistoryState C φ) i.succ y
        - (qmaRoundedGates C b i *ᵥ sl (qmaHistoryState C φ) i.castSucc) y
      = c * ((qmaExactGates C i - qmaRoundedGates C b i)
          *ᵥ qmaExactHistory C φ i.castSucc) y := by
    intro y
    rw [hsl_succ_pt y, hlinR y]
    have hs := congrFun hstep y
    have hsub := congrFun (Matrix.sub_mulVec (qmaExactGates C i) (qmaRoundedGates C b i)
      (qmaExactHistory C φ i.castSucc)) y
    rw [hs, hsub, Pi.sub_apply]
    ring
  have hfun : (fun y => sl (qmaHistoryState C φ) i.succ y
        - (qmaRoundedGates C b i *ᵥ sl (qmaHistoryState C φ) i.castSucc) y)
      = fun y => c * ((qmaExactGates C i - qmaRoundedGates C b i)
          *ᵥ qmaExactHistory C φ i.castSucc) y := by
    funext y
    exact hpoint y
  have hnmerr : nm ((qmaExactGates C i - qmaRoundedGates C b i)
        *ᵥ qmaExactHistory C φ i.castSucc)
      ≤ g13n2_kappa C.qubits b * nm (qmaExactHistory C φ i.castSucc) := by
    have hD := g13n2_round_gate_vec C.qubits b (qmaGateAt C.gates i.val)
      (qmaExactHistory C φ i.castSucc)
    have hneg := clause2Aux_nm_sub_neg (qmaExactGates C i) (qmaRoundedGates C b i)
      (qmaExactHistory C φ i.castSucc)
    rw [hneg]
    simpa only [qmaRoundedGates, qmaExactGates] using hD
  have hvnerr : vn ((qmaExactGates C i - qmaRoundedGates C b i)
        *ᵥ qmaExactHistory C φ i.castSucc)
      ≤ g13n2_kappa C.qubits b ^ 2 * vn (qmaExactHistory C φ i.castSucc) := by
    have h1 : nm ((qmaExactGates C i - qmaRoundedGates C b i)
          *ᵥ qmaExactHistory C φ i.castSucc) ^ 2
        ≤ (g13n2_kappa C.qubits b * nm (qmaExactHistory C φ i.castSucc)) ^ 2 :=
      pow_le_pow_left₀ (nm_nonneg _) hnmerr 2
    calc vn ((qmaExactGates C i - qmaRoundedGates C b i)
          *ᵥ qmaExactHistory C φ i.castSucc)
        = nm ((qmaExactGates C i - qmaRoundedGates C b i)
          *ᵥ qmaExactHistory C φ i.castSucc) ^ 2 := (nm_sq _).symm
        _ ≤ (g13n2_kappa C.qubits b * nm (qmaExactHistory C φ i.castSucc)) ^ 2 := h1
        _ = g13n2_kappa C.qubits b ^ 2
            * nm (qmaExactHistory C φ i.castSucc) ^ 2 := by ring
        _ = g13n2_kappa C.qubits b ^ 2 * vn (qmaExactHistory C φ i.castSucc) := by
          rw [nm_sq]
  have hvnres : vn (fun y => sl (qmaHistoryState C φ) i.succ y
        - (qmaRoundedGates C b i *ᵥ sl (qmaHistoryState C φ) i.castSucc) y)
      ≤ g13n2_kappa C.qubits b ^ 2 / (C.gates.length + 1 : ℝ) := by
    rw [hfun, vn_smul, hcsq]
    have hvnψ : vn (qmaExactHistory C φ i.castSucc) = 1 := hψnorm i.castSucc
    calc (1 / (C.gates.length + 1 : ℝ))
          * vn ((qmaExactGates C i - qmaRoundedGates C b i)
            *ᵥ qmaExactHistory C φ i.castSucc)
        ≤ (1 / (C.gates.length + 1 : ℝ))
            * (g13n2_kappa C.qubits b ^ 2
              * vn (qmaExactHistory C φ i.castSucc)) :=
          mul_le_mul_of_nonneg_left hvnerr (by positivity)
        _ = g13n2_kappa C.qubits b ^ 2 / (C.gates.length + 1 : ℝ) := by
          rw [hvnψ]
          ring
  rw [g13n_prop_energy_residual]
  have h1 : (1 / 2 : ℝ) * vn (fun y => sl (qmaHistoryState C φ) i.succ y
      - (qmaRoundedGates C b i *ᵥ sl (qmaHistoryState C φ) i.castSucc) y)
      ≤ (1 / 2 : ℝ) * (g13n2_kappa C.qubits b ^ 2 / (C.gates.length + 1 : ℝ)) := by
    have h := hvnres
    nlinarith
  have h2 : vn (sl (qmaHistoryState C φ) i.castSucc)
      - vn (qmaRoundedGates C b i *ᵥ sl (qmaHistoryState C φ) i.castSucc)
      ≤ 1 / (C.gates.length + 1 : ℝ) - (1 - κ) ^ 2 / (C.gates.length + 1 : ℝ) := by
    have hvnR' := hvnR
    have hvn_cast' := hvn_cast
    nlinarith
  have hκ0 : 0 ≤ g13n2_kappa C.qubits b := g13n2_kappa_nonneg C.qubits b
  calc (1 / 2 : ℝ) * vn (fun y => sl (qmaHistoryState C φ) i.succ y
          - (qmaRoundedGates C b i *ᵥ sl (qmaHistoryState C φ) i.castSucc) y)
        + (1 / 2 : ℝ) * (vn (sl (qmaHistoryState C φ) i.castSucc)
            - vn (qmaRoundedGates C b i *ᵥ sl (qmaHistoryState C φ) i.castSucc))
      ≤ (1 / 2 : ℝ) * (g13n2_kappa C.qubits b ^ 2 / (C.gates.length + 1 : ℝ))
          + (1 / 2 : ℝ) * (1 / (C.gates.length + 1 : ℝ)
              - (1 - κ) ^ 2 / (C.gates.length + 1 : ℝ)) := by linarith
      _ = g13n2_kappa C.qubits b / (C.gates.length + 1) := by ring

theorem clause2Aux_in_energy_zero (C : QmaHistoryCircuit) (φ : QState (Reg C.qubits))
    (hlegal : QmaInitLegal C φ) (j : Fin C.qubits) (hj : j ∈ C.initZeroWires) :
    qmaEnergy (qmaInTerm C.qubits C.gates.length j) (qmaHistoryState C φ) = 0 := by
  rw [g13n_in_energy]
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : y j
  · have hφ0 : φ y = 0 := by
      by_contra hne
      have h1 := hlegal y hne j hj
      simp [hy] at h1
    have hhist : qmaHistoryState C φ ((0 : Fin (C.gates.length + 1)), y) = 0 := by
      show (((Real.sqrt (C.gates.length + 1))⁻¹ : ℝ) : ℂ)
        * qmaExactHistory C φ (0 : Fin (C.gates.length + 1)) y = 0
      have h0 : qmaExactHistory C φ (0 : Fin (C.gates.length + 1)) y = φ y := by
        show (finiteWordMatrix C.qubits (C.gates.take 0)).mulVec φ y = _
        simp only [List.take_zero, finiteWordMatrix, Matrix.one_mulVec]
      rw [h0, hφ0]
      norm_num
    rw [if_pos hy, hhist]
    norm_num
  · rw [if_neg hy]

theorem clause2Aux_out_energy_eq (C : QmaHistoryCircuit) (φ : QState (Reg C.qubits))
    (hφ : Normalized φ) :
    qmaEnergy (qmaOutTerm C.qubits C.gates.length C.outputWire) (qmaHistoryState C φ)
      = (1 - qmaHistoryAcceptProb C φ) / (C.gates.length + 1) := by
  rw [g13n_out_energy_sub]
  set c : ℂ := (((Real.sqrt (C.gates.length + 1))⁻¹ : ℝ) : ℂ) with hc
  have hcsq : ‖c‖ ^ 2 = 1 / (C.gates.length + 1 : ℝ) := by
    have h1 : ‖c‖ = (Real.sqrt (C.gates.length + 1))⁻¹ := by
      rw [hc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    have h2 : ((Real.sqrt (C.gates.length + 1))⁻¹ : ℝ) ^ 2
        = 1 / (C.gates.length + 1 : ℝ) := by
      rw [inv_pow, Real.sq_sqrt (by positivity), one_div]
    rw [h1, h2]
  have hlast : qmaExactHistory C φ (Fin.last C.gates.length)
      = (finiteWordMatrix C.qubits C.gates).mulVec φ := by
    show (finiteWordMatrix C.qubits (C.gates.take (Fin.last C.gates.length).val)).mulVec φ = _
    rw [show (Fin.last C.gates.length).val = C.gates.length from rfl, List.take_length]
  have hslast : ∀ y : Reg C.qubits,
      qmaHistoryState C φ (Fin.last C.gates.length, y)
        = c * qmaExactHistory C φ (Fin.last C.gates.length) y := by
    intro y
    exact clause2Aux_history_slice C φ (Fin.last C.gates.length) y
  have hlastpt : ∀ y : Reg C.qubits,
      qmaExactHistory C φ (Fin.last C.gates.length) y
        = (finiteWordMatrix C.qubits C.gates).mulVec φ y := by
    intro y
    rw [hlast]
  have hsq : ∀ y : Reg C.qubits,
      ‖c * qmaExactHistory C φ (Fin.last C.gates.length) y‖ ^ 2
        = ‖c‖ ^ 2 * ‖qmaExactHistory C φ (Fin.last C.gates.length) y‖ ^ 2 := by
    intro y
    calc ‖c * qmaExactHistory C φ (Fin.last C.gates.length) y‖ ^ 2
        = Complex.normSq (c * qmaExactHistory C φ (Fin.last C.gates.length) y) :=
          (Complex.normSq_eq_norm_sq _).symm
        _ = Complex.normSq c
            * Complex.normSq (qmaExactHistory C φ (Fin.last C.gates.length) y) :=
          Complex.normSq_mul _ _
        _ = ‖c‖ ^ 2 * ‖qmaExactHistory C φ (Fin.last C.gates.length) y‖ ^ 2 := by
          rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have htot : (∑ y : Reg C.qubits,
        ‖qmaHistoryState C φ (Fin.last C.gates.length, y)‖ ^ 2)
      = 1 / (C.gates.length + 1 : ℝ) := by
    have hstep : ∀ y : Reg C.qubits,
        ‖qmaHistoryState C φ (Fin.last C.gates.length, y)‖ ^ 2
          = ‖c‖ ^ 2 * ‖qmaExactHistory C φ (Fin.last C.gates.length) y‖ ^ 2 := by
      intro y
      rw [hslast y, hsq y]
    have hsum : (∑ y : Reg C.qubits,
          ‖qmaExactHistory C φ (Fin.last C.gates.length) y‖ ^ 2)
        = vn (qmaExactHistory C φ (Fin.last C.gates.length)) := rfl
    rw [Finset.sum_congr rfl (fun y _ => hstep y), ← Finset.mul_sum, hsum]
    have hnorm : vn (qmaExactHistory C φ (Fin.last C.gates.length)) = 1 :=
      normalized_qmaExactHistory hφ (Fin.last C.gates.length)
    rw [hnorm, hcsq]
    ring
  have hacc : (∑ y : Reg C.qubits, if y C.outputWire then
        ‖qmaHistoryState C φ (Fin.last C.gates.length, y)‖ ^ 2 else (0 : ℝ))
      = qmaHistoryAcceptProb C φ / (C.gates.length + 1 : ℝ) := by
    have hstep : ∀ y : Reg C.qubits,
        (if y C.outputWire then
            ‖qmaHistoryState C φ (Fin.last C.gates.length, y)‖ ^ 2 else (0 : ℝ))
          = ‖c‖ ^ 2 * (if y C.outputWire then
              ‖(finiteWordMatrix C.qubits C.gates).mulVec φ y‖ ^ 2 else (0 : ℝ)) := by
      intro y
      by_cases hy : y C.outputWire
      · rw [if_pos hy, if_pos hy, hslast y, hsq y, hlastpt y]
      · rw [if_neg hy, if_neg hy]
        ring
    rw [Finset.sum_congr rfl (fun y _ => hstep y), ← Finset.mul_sum]
    have happ := g13n_accept_eq C φ
    rw [happ, hcsq]
    ring
  rw [htot, hacc]
  ring

theorem clause2Aux_history_state_energy_le (C : QmaHistoryCircuit) (φ : QState (Reg C.qubits))
    (hφ : Normalized φ) (hlegal : QmaInitLegal C φ) :
    qmaEnergy (qmaHistoryHamiltonian C (qmaRoundedGates C (qmaClause2Bits C)))
      (qmaHistoryState C φ)
      ≤ qmaClause2YesBound C (qmaHistoryAcceptProb C φ) := by
  have hκ : g13n2_kappa C.qubits (qmaClause2Bits C) ≤ 1 := clause2Aux_kappa_le_one C
  rw [g13n_energy_split]
  have hprop : (∑ i : Fin C.gates.length,
        qmaEnergy (qmaPropTerm C.qubits C.gates.length
          (qmaRoundedGates C (qmaClause2Bits C)) i) (qmaHistoryState C φ))
      ≤ g13n2_kappa C.qubits (qmaClause2Bits C) := by
    have hle : ∀ i : Fin C.gates.length,
        qmaEnergy (qmaPropTerm C.qubits C.gates.length
          (qmaRoundedGates C (qmaClause2Bits C)) i) (qmaHistoryState C φ)
        ≤ g13n2_kappa C.qubits (qmaClause2Bits C) / (C.gates.length + 1) :=
      fun i => clause2Aux_prop_energy_le C φ hφ (qmaClause2Bits C) i hκ
    calc (∑ i : Fin C.gates.length,
          qmaEnergy (qmaPropTerm C.qubits C.gates.length
            (qmaRoundedGates C (qmaClause2Bits C)) i) (qmaHistoryState C φ))
        ≤ ∑ i : Fin C.gates.length,
            (g13n2_kappa C.qubits (qmaClause2Bits C) / (C.gates.length + 1)) :=
          Finset.sum_le_sum (fun i _ => hle i)
        _ = (C.gates.length : ℝ)
            * (g13n2_kappa C.qubits (qmaClause2Bits C) / (C.gates.length + 1)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp
        _ ≤ g13n2_kappa C.qubits (qmaClause2Bits C) := by
          have hκ0 : 0 ≤ g13n2_kappa C.qubits (qmaClause2Bits C) :=
            g13n2_kappa_nonneg C.qubits (qmaClause2Bits C)
          have h2 : 0 < (C.gates.length + 1 : ℝ) := by positivity
          rw [← mul_div_assoc]
          exact (div_le_iff₀ h2).mpr (by nlinarith)
  have hin : (∑ j ∈ C.initZeroWires,
        qmaEnergy (qmaInTerm C.qubits C.gates.length j) (qmaHistoryState C φ)) = 0 := by
    rw [Finset.sum_eq_zero]
    intro j hj
    exact clause2Aux_in_energy_zero C φ hlegal j hj
  have hout : qmaEnergy (qmaOutTerm C.qubits C.gates.length C.outputWire)
      (qmaHistoryState C φ)
      = (1 - qmaHistoryAcceptProb C φ) / (C.gates.length + 1) :=
    clause2Aux_out_energy_eq C φ hφ
  have ht : g13n2_kappa C.qubits (qmaClause2Bits C)
      ≤ qmaTiny (C.qubits + C.gates.length + 2) := by
    have h := g2c2_tiny_absorb C.qubits C.gates.length
    have hκ0 : 0 ≤ g13n2_kappa C.qubits (qmaClause2Bits C) :=
      g13n2_kappa_nonneg C.qubits (qmaClause2Bits C)
    show g13n2_kappa C.qubits (3 * (C.qubits + C.gates.length) + 64)
        ≤ qmaTiny (C.qubits + C.gates.length + 2)
    have hsq0 : 0 ≤ g13n2_kappa C.qubits (3 * (C.qubits + C.gates.length) + 64) ^ 2 / 2 := by
      positivity
    linarith
  have h1 := hprop
  rw [hin, hout, qmaClause2YesBound]
  nlinarith [h1, ht]

theorem clause2Aux_star_neg (x : ℂ) : star (-x) = -star x := by
  have h : star (x + -x) = star x + star (-x) := by rw [star_add]
  have h2 : star (x + -x) = star (0 : ℂ) := by rw [add_neg_cancel]
  have h3 : (star (0 : ℂ)) = 0 := star_zero ℂ
  rw [h2, h3] at h
  calc star (-x) = star (-x) + 0 := by ring
    _ = (star x + star (-x)) - star x := by ring
    _ = (0 - star x) := by rw [h]
    _ = -star x := by ring

theorem clause2Aux_star_intCast (a : ℤ) : star (a : ℂ) = a := by
  cases a with
  | ofNat n =>
    rw [show (Int.ofNat n : ℂ) = ((n : ℕ) : ℂ) by simp, RCLike.star_def]
    exact Complex.conj_natCast n
  | negSucc n =>
    have hcast : ((Int.negSucc n : ℤ) : ℂ) = -((n + 1 : ℕ) : ℂ) := by simp
    rw [hcast, clause2Aux_star_neg, RCLike.star_def, Complex.conj_natCast]

theorem clause2Aux_star_pow_two (w : ℕ) : star ((2 : ℂ) ^ w) = (2 : ℂ) ^ w := by
  have e : ((2 : ℂ) ^ w) = ((2 ^ w : ℕ) : ℂ) := (Nat.cast_pow 2 w).symm
  rw [e, RCLike.star_def, Complex.conj_natCast, ← e]

theorem clause2Aux_isDyadicC_zero (w : ℕ) : qmaIsDyadicC w (0 : ℂ) := by
  refine ⟨0, 0, ?_⟩
  simp

theorem clause2Aux_isDyadicC_one (w : ℕ) : qmaIsDyadicC w (1 : ℂ) := by
  refine ⟨(2 ^ w : ℕ), 0, ?_⟩
  rw [Nat.cast_pow, mul_one]
  simp

theorem clause2Aux_isDyadicC_of_zero_one {b : ℕ} {z : ℂ} (hz : z = 0 ∨ z = 1) :
    qmaIsDyadicC b z := by
  rcases hz with h | h
  · rw [h]
    exact clause2Aux_isDyadicC_zero b
  · rw [h]
    exact clause2Aux_isDyadicC_one b

theorem clause2Aux_isDyadicC_mul_zero_one {b : ℕ} {x y z : ℂ}
    (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (hz : z = 0 ∨ z = 1) :
    qmaIsDyadicC b (x * y * z) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz
  · rw [hx, hy, hz]
    ring_nf
    exact clause2Aux_isDyadicC_zero b
  · rw [hx, hy, hz]
    ring_nf
    exact clause2Aux_isDyadicC_zero b
  · rw [hx, hy, hz]
    ring_nf
    exact clause2Aux_isDyadicC_zero b
  · rw [hx, hy, hz]
    ring_nf
    exact clause2Aux_isDyadicC_zero b
  · rw [hx, hy, hz]
    ring_nf
    exact clause2Aux_isDyadicC_zero b
  · rw [hx, hy, hz]
    ring_nf
    exact clause2Aux_isDyadicC_zero b
  · rw [hx, hy, hz]
    ring_nf
    exact clause2Aux_isDyadicC_zero b
  · rw [hx, hy, hz]
    ring_nf
    exact clause2Aux_isDyadicC_one b

theorem clause2Aux_isDyadicC_neg {w : ℕ} {z : ℂ} (hz : qmaIsDyadicC w z) :
    qmaIsDyadicC w (-z) := by
  obtain ⟨a, c, h⟩ := hz
  refine ⟨-a, -c, ?_⟩
  have hn : -((a : ℂ) + Complex.I * (c : ℂ))
      = ((-a : ℤ) : ℂ) + Complex.I * ((-c : ℤ) : ℂ) := by
    rw [Int.cast_neg, Int.cast_neg]
    ring
  rw [mul_neg, ← hn, ← h]

theorem clause2Aux_isDyadicC_star {w : ℕ} {z : ℂ} (hz : qmaIsDyadicC w z) :
    qmaIsDyadicC w (star z) := by
  obtain ⟨a, c, h⟩ := hz
  refine ⟨a, -c, ?_⟩
  have hstar : star ((a : ℂ) + Complex.I * (c : ℂ))
      = (a : ℂ) + Complex.I * ((-c : ℤ) : ℂ) := by
    rw [star_add, star_mul', clause2Aux_star_intCast, clause2Aux_star_intCast]
    rw [show star (Complex.I : ℂ) = -Complex.I by
      rw [RCLike.star_def]; exact Complex.conj_I]
    rw [Int.cast_neg]
    ring
  have hsm : star (((2 : ℂ) ^ w) * z) = ((2 : ℂ) ^ w) * star z := by
    rw [star_mul', clause2Aux_star_pow_two]
  rw [← hsm, h, hstar]

theorem clause2Aux_isDyadicC_half {w : ℕ} {z : ℂ} (hz : qmaIsDyadicC w z) :
    qmaIsDyadicC (w + 1) ((1 / 2 : ℂ) * z) := by
  obtain ⟨a, c, h⟩ := hz
  refine ⟨a, c, ?_⟩
  calc ((2 : ℂ) ^ (w + 1)) * ((1 / 2 : ℂ) * z)
      = ((2 : ℂ) ^ w * 2) * ((1 / 2 : ℂ) * z) := by
        rw [pow_add, pow_one]
      _ = (2 : ℂ) ^ w * z := by ring
      _ = (a : ℂ) + Complex.I * (c : ℂ) := h

theorem clause2Aux_roundC_isDyadicC (b : ℕ) (z : ℂ) : qmaIsDyadicC b (qmaRoundC b z) := by
  refine ⟨Int.floor (z.re * 2 ^ b + 1 / 2), Int.floor (z.im * 2 ^ b + 1 / 2), ?_⟩
  show ((2 : ℂ) ^ b) * qmaRoundC b z
      = ((Int.floor (z.re * 2 ^ b + 1 / 2) : ℤ) : ℂ)
        + Complex.I * ((Int.floor (z.im * 2 ^ b + 1 / 2) : ℤ) : ℂ)
  unfold qmaRoundC
  have hpow : ((2 : ℂ) ^ b) = ((2 ^ b : ℕ) : ℂ) := (Nat.cast_pow 2 b).symm
  rw [hpow]
  have hne : ((2 ^ b : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero b (by norm_num : (2 : ℕ) ≠ 0)
  field_simp

theorem clause2Aux_roundedGate_isDyadicC (n b : ℕ) (g : FiniteGateCode) (x y : Reg n) :
    qmaIsDyadicC b (qmaRoundedGate n b g x y) := by
  show qmaIsDyadicC b (qmaRoundC b (finiteCodeMatrix n g x y))
  exact clause2Aux_roundC_isDyadicC b (finiteCodeMatrix n g x y)

theorem clause2Aux_roundedGates_isDyadicC (C : QmaHistoryCircuit) (b : ℕ)
    (j : Fin C.gates.length) (x y : Reg C.qubits) :
    qmaIsDyadicC b (qmaRoundedGates C b j x y) := by
  show qmaIsDyadicC b (qmaRoundedGate C.qubits b (qmaGateAt C.gates j.val) x y)
  exact clause2Aux_roundedGate_isDyadicC C.qubits b (qmaGateAt C.gates j.val) x y

theorem clause2Aux_propTerm_isDyadicC (n m b : ℕ) (U : Fin m → Matrix (Reg n) (Reg n) ℂ)
    (i : Fin m) (p q : Fin (m + 1) × Reg n)
    (hU : ∀ j : Fin m, ∀ x y : Reg n, qmaIsDyadicC b (U j x y)) :
    qmaIsDyadicC (b + 1) (qmaPropTerm n m U i p q) := by
  rw [qmaPropTerm_entry]
  by_cases c1 : p.1 = i.succ ∧ q.1 = i.succ
  · rw [if_pos c1, Matrix.one_apply]
    by_cases h : p.2 = q.2
    · rw [if_pos h]
      exact clause2Aux_isDyadicC_half (clause2Aux_isDyadicC_one b)
    · rw [if_neg h]
      exact clause2Aux_isDyadicC_half (clause2Aux_isDyadicC_zero b)
  by_cases c2 : p.1 = i.castSucc ∧ q.1 = i.castSucc
  · rw [if_neg c1, if_pos c2, Matrix.one_apply]
    by_cases h : p.2 = q.2
    · rw [if_pos h]
      exact clause2Aux_isDyadicC_half (clause2Aux_isDyadicC_one b)
    · rw [if_neg h]
      exact clause2Aux_isDyadicC_half (clause2Aux_isDyadicC_zero b)
  by_cases c3 : p.1 = i.succ ∧ q.1 = i.castSucc
  · rw [if_neg c1, if_neg c2, if_pos c3]
    exact clause2Aux_isDyadicC_neg (clause2Aux_isDyadicC_half (hU i p.2 q.2))
  by_cases c4 : p.1 = i.castSucc ∧ q.1 = i.succ
  · rw [if_neg c1, if_neg c2, if_neg c3, if_pos c4]
    exact clause2Aux_isDyadicC_neg
        (clause2Aux_isDyadicC_half (clause2Aux_isDyadicC_star (hU i q.2 p.2)))
  rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4]
  exact clause2Aux_isDyadicC_zero (b + 1)

theorem clause2Aux_inTerm_isDyadicC (n m b : ℕ) (j : Fin n) (p q : Fin (m + 1) × Reg n) :
    qmaIsDyadicC b (qmaInTerm n m j p q) := by
  rw [qmaInTerm_entry]
  have h1 : Ket 0 p.1 = 0 ∨ Ket 0 p.1 = 1 := by
    by_cases h : p.1 = 0
    · right
      rw [ket_apply, if_pos h]
    · left
      rw [ket_apply, if_neg h]
  have h2 : Ket 0 q.1 = 0 ∨ Ket 0 q.1 = 1 := by
    by_cases h : q.1 = 0
    · right
      rw [ket_apply, if_pos h]
    · left
      rw [ket_apply, if_neg h]
  have h3 : (if p.2 = q.2 then (if p.2 j then (1 : ℂ) else 0) else 0) = 0
      ∨ (if p.2 = q.2 then (if p.2 j then (1 : ℂ) else 0) else 0) = 1 := by
    by_cases h : p.2 = q.2
    · by_cases h' : p.2 j
      · right
        rw [if_pos h, if_pos h']
      · left
        rw [if_pos h, if_neg h']
    · left
      rw [if_neg h]
  exact clause2Aux_isDyadicC_mul_zero_one h1 h2 h3

theorem clause2Aux_outTerm_isDyadicC (n m b : ℕ) (out : Fin n) (p q : Fin (m + 1) × Reg n) :
    qmaIsDyadicC b (qmaOutTerm n m out p q) := by
  rw [qmaOutTerm_entry]
  have h1 : Ket (Fin.last m) p.1 = 0 ∨ Ket (Fin.last m) p.1 = 1 := by
    by_cases h : p.1 = Fin.last m
    · right
      rw [ket_apply, if_pos h]
    · left
      rw [ket_apply, if_neg h]
  have h2 : Ket (Fin.last m) q.1 = 0 ∨ Ket (Fin.last m) q.1 = 1 := by
    by_cases h : q.1 = Fin.last m
    · right
      rw [ket_apply, if_pos h]
    · left
      rw [ket_apply, if_neg h]
  have h3 : (if p.2 = q.2 then (if p.2 out then (0 : ℂ) else 1) else 0) = 0
      ∨ (if p.2 = q.2 then (if p.2 out then (0 : ℂ) else 1) else 0) = 1 := by
    by_cases h : p.2 = q.2
    · by_cases h' : p.2 out
      · left
        rw [if_pos h, if_pos h']
      · right
        rw [if_pos h, if_neg h']
    · left
      rw [if_neg h]
  exact clause2Aux_isDyadicC_mul_zero_one h1 h2 h3

theorem clause2Aux_terms_isDyadicC (C : QmaHistoryCircuit) (b : ℕ)
    (hU : ∀ j : Fin C.gates.length, ∀ x y : Reg C.qubits,
      qmaIsDyadicC b (qmaRoundedGates C b j x y)) :
    ∀ t ∈ qmaHistoryTerms C (qmaRoundedGates C b),
      ∀ p q : Fin (C.gates.length + 1) × Reg C.qubits,
        qmaIsDyadicC (b + 1) (t.matrix p q) := by
  intro t ht p q
  have hsplit : qmaHistoryTerms C (qmaRoundedGates C b)
      = qmaHistoryPropTerms C (qmaRoundedGates C b)
        ++ qmaHistoryInTerms C ++ qmaHistoryOutTerm C := rfl
  have hmem : t ∈ qmaHistoryPropTerms C (qmaRoundedGates C b)
      ∨ t ∈ qmaHistoryInTerms C ∨ t ∈ qmaHistoryOutTerm C := by
    have h := ht
    rw [hsplit, List.mem_append, List.mem_append, or_assoc] at h
    exact h
  rcases hmem with hprop | hin | hout
  · rw [qmaHistoryPropTerms, List.mem_map] at hprop
    obtain ⟨i, _, heq⟩ := hprop
    rw [← heq]
    exact clause2Aux_propTerm_isDyadicC C.qubits C.gates.length b (qmaRoundedGates C b) i p q hU
  · rw [qmaHistoryInTerms, List.mem_map] at hin
    obtain ⟨j, _, heq⟩ := hin
    rw [← heq]
    exact clause2Aux_inTerm_isDyadicC C.qubits C.gates.length (b + 1) j p q
  · rw [qmaHistoryOutTerm, List.mem_singleton] at hout
    cases hout
    exact clause2Aux_outTerm_isDyadicC C.qubits C.gates.length (b + 1) C.outputWire p q

theorem clause2Aux_yesBound_mono (C : QmaHistoryCircuit) {a a' : ℝ} (h : a ≤ a') :
    qmaClause2YesBound C a' ≤ qmaClause2YesBound C a := by
  unfold qmaClause2YesBound
  have h2 : 0 ≤ (C.gates.length + 1 : ℝ) := by positivity
  have h3 : 1 - a' ≤ 1 - a := by linarith
  have h4 : (1 - a') / (C.gates.length + 1) ≤ (1 - a) / (C.gates.length + 1) := by
    exact mul_le_mul_of_nonneg_right h3 (by positivity)
  linarith

theorem clause2Aux_yes_clause (C : QmaHistoryCircuit) (a : ℝ)
    (h : ∃ φ : QState (Reg C.qubits), QmaInitLegal C φ ∧ Normalized φ ∧
      a ≤ qmaHistoryAcceptProb C φ) :
    ∃ η : QState (Fin (C.gates.length + 1) × Reg C.qubits), Normalized η ∧
      qmaEnergy (qmaHistoryHamiltonian C (qmaRoundedGates C (qmaClause2Bits C))) η
        ≤ qmaClause2YesBound C a := by
  obtain ⟨φ, hlegal, hφ, hacc⟩ := h
  refine ⟨qmaHistoryState C φ, normalized_qmaHistoryState hφ, ?_⟩
  have hE := clause2Aux_history_state_energy_le C φ hφ hlegal
  have hmono := clause2Aux_yesBound_mono C hacc
  linarith

theorem clause2Aux_no_clause (C : QmaHistoryCircuit) (ε : ℝ)
    (hsnd : ∀ φ : QState (Reg C.qubits), QmaInitLegal C φ → Normalized φ →
      qmaHistoryAcceptProb C φ ≤ ε) :
    ∀ η : QState (Fin (C.gates.length + 1) × Reg C.qubits), Normalized η →
      qmaClause2NoBound C ε
        ≤ qmaEnergy (qmaHistoryHamiltonian C (qmaRoundedGates C (qmaClause2Bits C))) η := by
  intro η hη
  have h := g2c2_clause2 C ε hsnd η hη
  unfold qmaClause2NoBound
  exact h

theorem clause2Aux_locality_clause (C : QmaHistoryCircuit)
    (t : QmaHistoryTerm C.qubits C.gates.length)
    (ht : t ∈ qmaHistoryTerms C (qmaRoundedGates C (qmaClause2Bits C))) :
    qmaActsOn C.qubits C.gates.length t.matrix t.clockSupport t.workSupport
      ∧ t.clockSupport.card ≤ 2 ∧ t.workSupport.card ≤ 2 := by
  have ht' : t ∈ qmaHistoryTerms C
      (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64)) := by
    rw [qmaClause2Bits] at ht
    exact ht
  exact clause2_clause3 C t ht'

theorem clause2Aux_norm_clause (C : QmaHistoryCircuit)
    (t : QmaHistoryTerm C.qubits C.gates.length)
    (ht : t ∈ qmaHistoryTerms C (qmaRoundedGates C (qmaClause2Bits C)))
    (p q : Fin (C.gates.length + 1) × Reg C.qubits) :
    ‖t.matrix p q‖ ≤ 1 := by
  have ht' : t ∈ qmaHistoryTerms C
      (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64)) := by
    rw [qmaClause2Bits] at ht
    exact ht
  exact clause2_clause4 C t ht' p q

theorem clause2Aux_dyadic_clause (C : QmaHistoryCircuit)
    (t : QmaHistoryTerm C.qubits C.gates.length)
    (ht : t ∈ qmaHistoryTerms C (qmaRoundedGates C (qmaClause2Bits C)))
    (p q : Fin (C.gates.length + 1) × Reg C.qubits) :
    qmaIsDyadicC (qmaClause2Bits C + 1) (t.matrix p q) := by
  exact clause2Aux_terms_isDyadicC C (qmaClause2Bits C)
    (fun j x y => clause2Aux_roundedGates_isDyadicC C (qmaClause2Bits C) j x y) t ht p q

theorem clause2Aux_term_count_clause (C : QmaHistoryCircuit) :
    (qmaHistoryTerms C (qmaRoundedGates C (qmaClause2Bits C))).length
      ≤ C.gates.length + C.qubits + 1 := by
  have h := clause2_clause6 C
  show (qmaHistoryTerms C
      (qmaRoundedGates C (3 * (C.qubits + C.gates.length) + 64))).length
      ≤ C.gates.length + C.qubits + 1
  exact h

theorem clause2Aux_twoWay (C : QmaHistoryCircuit) : qmaClause2TwoWay C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a h
    exact clause2Aux_yes_clause C a h
  · intro ε hsnd η hη
    exact clause2Aux_no_clause C ε hsnd η hη
  · intro t ht
    exact clause2Aux_locality_clause C t ht
  · intro t ht p q
    exact clause2Aux_norm_clause C t ht p q
  · intro t ht p q
    exact clause2Aux_dyadic_clause C t ht p q
  · exact clause2Aux_term_count_clause C

@[simp] theorem qmaClause3GammaBits_zero : qmaClause3GammaBits 0 = [false] := rfl

@[simp] theorem qmaClause3GammaBits_succ (v : ℕ) :
    qmaClause3GammaBits (v + 1) = true :: qmaClause3GammaBits v := by
  simp [qmaClause3GammaBits, List.replicate_succ]

theorem clause3Aux_gammaBits_injective (a b : ℕ) (s t : List Bool)
    (h : qmaClause3GammaBits a ++ s = qmaClause3GammaBits b ++ t) : a = b := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => rfl
      | succ b =>
          simp only [qmaClause3GammaBits_zero, qmaClause3GammaBits_succ] at h
          exact absurd h (by simp)
  | succ a ih =>
      cases b with
      | zero =>
          simp only [qmaClause3GammaBits_zero, qmaClause3GammaBits_succ] at h
          exact absurd h (by simp)
      | succ b =>
          simp only [qmaClause3GammaBits_succ] at h
          have h' : qmaClause3GammaBits a ++ s = qmaClause3GammaBits b ++ t := (List.cons.inj h).2
          have := ih b h'
          omega

theorem clause3Aux_natBits_length : ∀ (w v : ℕ), (qmaClause3NatBits w v).length = w := by
  intro w
  induction w with
  | zero => intro v; rfl
  | succ w ih => intro v; simp [qmaClause3NatBits, ih]

theorem clause3Aux_natBits_injective : ∀ (w : ℕ) {v v' : ℕ}, v < 2 ^ w → v' < 2 ^ w →
    qmaClause3NatBits w v = qmaClause3NatBits w v' → v = v' := by
  intro w
  induction w with
  | zero =>
      intro v v' hv hv' h
      have h1 : v = 0 := by omega
      have h2 : v' = 0 := by omega
      omega
  | succ w ih =>
      intro v v' hv hv' h
      have hhead : decide (v % 2 = 1) = decide (v' % 2 = 1) := (List.cons.inj h).1
      have htail : qmaClause3NatBits w (v / 2) = qmaClause3NatBits w (v' / 2) := (List.cons.inj h).2
      have hv2 : v / 2 < 2 ^ w := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        have hp : 2 ^ w * 2 = 2 ^ (w + 1) := by rw [pow_succ]
        omega
      have hv2' : v' / 2 < 2 ^ w := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        have hp : 2 ^ w * 2 = 2 ^ (w + 1) := by rw [pow_succ]
        omega
      have hdiv : v / 2 = v' / 2 := ih hv2 hv2' htail
      have hmod : v % 2 = v' % 2 := by
        by_cases hp : v % 2 = 1
        · have hd : decide (v % 2 = 1) = true := by simp [hp]
          rw [hd] at hhead
          have hd' : decide (v' % 2 = 1) = true := hhead.symm
          have hx := (decide_eq_true_eq).mp hd'
          omega
        · have hd : decide (v % 2 = 1) = false := by simp [hp]
          rw [hd] at hhead
          have hd' : decide (v' % 2 = 1) = false := hhead.symm
          have hn : ¬ (v' % 2 = 1) := (decide_eq_false_iff_not).mp hd'
          omega
      have h1 := Nat.mod_add_div v 2
      have h2 := Nat.mod_add_div v' 2
      omega

theorem clause3Aux_encNat_width_lt (v : ℕ) : v < 2 ^ (v.log2 + 1) := Nat.lt_log2_self

theorem clause3Aux_encNat_injective (v v' : ℕ) (h : qmaClause3EncNat v = qmaClause3EncNat v') : v = v' := by
  have h' : qmaClause3GammaBits (v.log2 + 1) ++ qmaClause3NatBits (v.log2 + 1) v
      = qmaClause3GammaBits (v'.log2 + 1) ++ qmaClause3NatBits (v'.log2 + 1) v' := h
  have hw : v.log2 + 1 = v'.log2 + 1 := by
    apply clause3Aux_gammaBits_injective (v.log2 + 1) (v'.log2 + 1)
      (qmaClause3NatBits (v.log2 + 1) v) (qmaClause3NatBits (v'.log2 + 1) v')
    exact h'
  have hbits : qmaClause3NatBits (v.log2 + 1) v = qmaClause3NatBits (v.log2 + 1) v' := by
    have h2 := h'
    rw [← hw] at h2
    exact List.append_cancel_left h2
  have h3 : v' < 2 ^ (v.log2 + 1) := by rw [hw]; exact clause3Aux_encNat_width_lt v'
  have h4 := clause3Aux_natBits_injective (v.log2 + 1) (clause3Aux_encNat_width_lt v) h3 hbits
  omega

theorem clause3Aux_append_inj_of_length_eq {α : Type} {l₁ l₂ : List α} {s t : List α}
    (hlen : l₁.length = l₂.length) (h : l₁ ++ s = l₂ ++ t) : l₁ = l₂ ∧ s = t := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => exact ⟨rfl, by simpa using h⟩
      | cons b l₂ => simp at hlen
  | cons a l₁ ih =>
      cases l₂ with
      | nil => simp at hlen
      | cons b l₂ =>
          have h' : a :: (l₁ ++ s) = b :: (l₂ ++ t) := h
          have hab : a = b := (List.cons.inj h').1
          have htail : l₁ ++ s = l₂ ++ t := (List.cons.inj h').2
          have hlen' : l₁.length = l₂.length := by simp at hlen; omega
          obtain ⟨heq, hst⟩ := ih hlen' htail
          exact ⟨by simp [heq, hab], hst⟩

theorem clause3Aux_encNat_selfDelimiting (v v' : ℕ) (s t : List Bool)
    (h : qmaClause3EncNat v ++ s = qmaClause3EncNat v' ++ t) : v = v' ∧ s = t := by
  have h' : qmaClause3GammaBits (v.log2 + 1) ++ (qmaClause3NatBits (v.log2 + 1) v ++ s)
      = qmaClause3GammaBits (v'.log2 + 1) ++ (qmaClause3NatBits (v'.log2 + 1) v' ++ t) := by
    simpa only [qmaClause3EncNat, List.append_assoc] using h
  have hw : v.log2 + 1 = v'.log2 + 1 := by
    apply clause3Aux_gammaBits_injective (v.log2 + 1) (v'.log2 + 1)
      (qmaClause3NatBits (v.log2 + 1) v ++ s) (qmaClause3NatBits (v'.log2 + 1) v' ++ t)
    exact h'
  have hbits : qmaClause3NatBits (v.log2 + 1) v ++ s
      = qmaClause3NatBits (v.log2 + 1) v' ++ t := by
    have h2 := h'
    rw [← hw] at h2
    exact List.append_cancel_left h2
  obtain ⟨hb, hst⟩ := clause3Aux_append_inj_of_length_eq
    (l₁ := qmaClause3NatBits (v.log2 + 1) v) (l₂ := qmaClause3NatBits (v.log2 + 1) v')
    (s := s) (t := t) (by rw [clause3Aux_natBits_length, clause3Aux_natBits_length]) hbits
  have hv : v = v' := clause3Aux_natBits_injective (v.log2 + 1)
    (clause3Aux_encNat_width_lt v) (by rw [hw]; exact clause3Aux_encNat_width_lt v') hb
  exact ⟨hv, hst⟩

theorem clause3Aux_flatten_pieces {α : Type} {f : α → List Bool}
    (hf : ∀ a b (s t : List Bool), f a ++ s = f b ++ t → a = b ∧ s = t) :
    ∀ (xs ys : List α) (s t : List Bool), xs.length = ys.length →
    (xs.map f).flatten ++ s = (ys.map f).flatten ++ t → xs = ys ∧ s = t := by
  intro xs
  induction xs with
  | nil =>
      intro ys s t hlen h
      cases ys with
      | nil => exact ⟨rfl, by simpa using h⟩
      | cons y ys' => simp at hlen
  | cons x xs ih =>
      intro ys s t hlen h
      cases ys with
      | nil => simp at hlen
      | cons y ys' =>
          have hlen' : xs.length = ys'.length := by
            simp only [List.length_cons] at hlen
            omega
          have h' : f x ++ ((xs.map f).flatten ++ s)
              = f y ++ ((ys'.map f).flatten ++ t) := by
            have hh := h
            simp only [List.map_cons, List.flatten_cons, List.append_assoc] at hh
            exact hh
          obtain ⟨hxy, hrest⟩ := hf x y ((xs.map f).flatten ++ s) ((ys'.map f).flatten ++ t) h'
          obtain ⟨hlist, hst⟩ := ih ys' s t hlen' hrest
          refine ⟨by simp [hxy, hlist], hst⟩

theorem clause3Aux_encList_selfDelimiting {α : Type} {f : α → List Bool}
    (hf : ∀ a b (s t : List Bool), f a ++ s = f b ++ t → a = b ∧ s = t) :
    ∀ (xs ys : List α) (s t : List Bool),
    qmaClause3EncList f xs ++ s = qmaClause3EncList f ys ++ t → xs = ys ∧ s = t := by
  intro xs ys s t h
  have h' : qmaClause3GammaBits xs.length ++ ((xs.map f).flatten ++ s)
      = qmaClause3GammaBits ys.length ++ ((ys.map f).flatten ++ t) := by
    simpa only [qmaClause3EncList, List.append_assoc] using h
  have hlen : xs.length = ys.length := by
    apply clause3Aux_gammaBits_injective xs.length ys.length
      ((xs.map f).flatten ++ s) ((ys.map f).flatten ++ t)
    exact h'
  have hrest : (xs.map f).flatten ++ s = (ys.map f).flatten ++ t := by
    have h2 := h'
    rw [hlen] at h2
    exact List.append_cancel_left h2
  exact clause3Aux_flatten_pieces hf xs ys s t hlen hrest

theorem clause3Aux_encList_injective {α : Type} {f : α → List Bool}
    (hf : ∀ a b (s t : List Bool), f a ++ s = f b ++ t → a = b ∧ s = t) :
    ∀ (xs ys : List α), qmaClause3EncList f xs = qmaClause3EncList f ys → xs = ys := by
  intro xs ys h
  obtain ⟨rfl, _⟩ := clause3Aux_encList_selfDelimiting hf xs ys [] [] (by simpa using h)
  exact rfl

theorem clause3Aux_int_eq_of_natAbs_eq {v v' : ℤ} (hsign : decide (0 ≤ v) = decide (0 ≤ v'))
    (hab : v.natAbs = v'.natAbs) : v = v' := by
  by_cases h : 0 ≤ v
  · have h' : 0 ≤ v' := by
      have hd : decide (0 ≤ v') = true := by rw [← hsign]; simp [h]
      simpa using (decide_eq_true_eq).mp hd
    calc v = (v.natAbs : ℤ) := (Int.natAbs_of_nonneg h).symm
      _ = (v'.natAbs : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hab
      _ = v' := Int.natAbs_of_nonneg h'
  · have hn : ¬ (0 ≤ v') := by
      have hd : decide (0 ≤ v') = false := by rw [← hsign]; simp [h]
      simpa using (decide_eq_false_iff_not).mp hd
    have hneg : v = -(v.natAbs : ℤ) := by
      have h0 : 0 ≤ -v := by omega
      have hh : (((-v).natAbs : ℕ) : ℤ) = -v := Int.natAbs_of_nonneg h0
      have hh' : (-v).natAbs = v.natAbs := Int.natAbs_neg v
      have hcast : ((v.natAbs : ℕ) : ℤ) = -v := by
        rw [← hh']
        exact hh
      simpa using congrArg Neg.neg hcast.symm
    have hneg' : v' = -(v'.natAbs : ℤ) := by
      have h0 : 0 ≤ -v' := by omega
      have hh : (((-v').natAbs : ℕ) : ℤ) = -v' := Int.natAbs_of_nonneg h0
      have hh' : (-v').natAbs = v'.natAbs := Int.natAbs_neg v'
      have hcast : ((v'.natAbs : ℕ) : ℤ) = -v' := by
        rw [← hh']
        exact hh
      simpa using congrArg Neg.neg hcast.symm
    rw [hneg, hneg']
    exact congrArg Neg.neg (congrArg (fun n : ℕ => (n : ℤ)) hab)

theorem clause3Aux_encInt_selfDelimiting (v v' : ℤ) (s t : List Bool)
    (h : qmaClause3EncInt v ++ s = qmaClause3EncInt v' ++ t) : v = v' ∧ s = t := by
  have h' : decide (0 ≤ v) :: qmaClause3EncNat v.natAbs ++ s
      = decide (0 ≤ v') :: qmaClause3EncNat v'.natAbs ++ t := h
  have hsign : decide (0 ≤ v) = decide (0 ≤ v') := (List.cons.inj h').1
  have hnat : qmaClause3EncNat v.natAbs ++ s = qmaClause3EncNat v'.natAbs ++ t :=
      (List.cons.inj h').2
  obtain ⟨hab, hst⟩ := clause3Aux_encNat_selfDelimiting v.natAbs v'.natAbs s t hnat
  exact ⟨clause3Aux_int_eq_of_natAbs_eq hsign hab, hst⟩

theorem clause3Aux_encInt_injective (v v' : ℤ) (h : qmaClause3EncInt v = qmaClause3EncInt v') : v = v' := by
  obtain ⟨rfl, _⟩ := clause3Aux_encInt_selfDelimiting v v' [] [] (by simpa using h)
  exact rfl

theorem clause3Aux_lhIndexPairs_mem (d : ℕ) (p q : Fin d) : (p, q) ∈ lhIndexPairs d := by
  simp only [lhIndexPairs, List.mem_flatMap]
  refine ⟨⟨p.val, p.isLt⟩, ?_, ?_⟩
  · exact List.mem_finRange p
  · simp only [List.mem_map]
    exact ⟨⟨q.val, q.isLt⟩, List.mem_finRange q, rfl⟩

theorem clause3Aux_encTerm_split {N : ℕ} {t t' : LhTerm N} (s u : List Bool)
    (h : qmaClause3EncTerm t ++ s = qmaClause3EncTerm t' ++ u) :
    (t.wires.length = t'.wires.length) ∧ (t.wires = t'.wires) ∧
    (qmaClause3TermEntries t = qmaClause3TermEntries t') ∧ (s = u) := by
  have h' := h
  simp only [qmaClause3EncTerm, List.append_assoc] at h'
  obtain ⟨hlen, hrest⟩ := clause3Aux_encNat_selfDelimiting t.wires.length t'.wires.length _ _ h'
  obtain ⟨hwires, hrest2⟩ := clause3Aux_encList_selfDelimiting
    (fun a b (s u : List Bool) => by
      intro hx
      obtain ⟨hv, hs⟩ := clause3Aux_encNat_selfDelimiting a.val b.val s u hx
      exact ⟨Fin.ext hv, hs⟩)
    t.wires t'.wires _ _ hrest
  obtain ⟨hentries, hsu⟩ := clause3Aux_encList_selfDelimiting
    (fun a b (s u : List Bool) => clause3Aux_encInt_selfDelimiting a b s u)
    (qmaClause3TermEntries t) (qmaClause3TermEntries t') _ _ hrest2
  exact ⟨hlen, hwires, hentries, hsu⟩

theorem clause3Aux_encTerm_eq_of_split {N : ℕ} {t t' : LhTerm N}
    (hwires : t.wires = t'.wires)
    (hentries : qmaClause3TermEntries t = qmaClause3TermEntries t') : t = t' := by
  cases t with
  | mk wires re im =>
      cases t' with
      | mk wires' re' im' =>
          change wires = wires' at hwires
          subst wires'
          have hsplit : (lhIndexPairs (2 ^ wires.length)).map (fun q => re q.1 q.2)
                ++ (lhIndexPairs (2 ^ wires.length)).map (fun q => im q.1 q.2)
              = (lhIndexPairs (2 ^ wires.length)).map (fun q => re' q.1 q.2)
                ++ (lhIndexPairs (2 ^ wires.length)).map (fun q => im' q.1 q.2) := by
            simpa only [qmaClause3TermEntries] using hentries
          obtain ⟨hre, him⟩ := clause3Aux_append_inj_of_length_eq
            (by rw [List.length_map, List.length_map]) hsplit
          have hre' : re = re' := by
            apply Matrix.ext
            intro p q
            have hpq : (p, q) ∈ lhIndexPairs (2 ^ wires.length) := clause3Aux_lhIndexPairs_mem _ p q
            have hmem := (List.map_inj_left).mp hre
            exact hmem (p, q) hpq
          have him' : im = im' := by
            apply Matrix.ext
            intro p q
            have hpq : (p, q) ∈ lhIndexPairs (2 ^ wires.length) := clause3Aux_lhIndexPairs_mem _ p q
            have hmem := (List.map_inj_left).mp him
            exact hmem (p, q) hpq
          subst hre'
          subst him'
          rfl

theorem clause3Aux_encTerm_injective {N : ℕ} {t t' : LhTerm N}
    (h : qmaClause3EncTerm t = qmaClause3EncTerm t') : t = t' := by
  obtain ⟨-, hwires, hentries, -⟩ := clause3Aux_encTerm_split [] [] (by simpa using h)
  exact clause3Aux_encTerm_eq_of_split hwires hentries

theorem clause3Aux_encTerm_selfDelimiting {N : ℕ} {t t' : LhTerm N} (s u : List Bool)
    (h : qmaClause3EncTerm t ++ s = qmaClause3EncTerm t' ++ u) : t = t' ∧ s = u := by
  obtain ⟨-, hwires, hentries, hsu⟩ := clause3Aux_encTerm_split s u h
  exact ⟨clause3Aux_encTerm_eq_of_split hwires hentries, hsu⟩

theorem clause3Aux_toBits_injective {E E' : LhEncoding}
    (h : qmaClause3ToBits E = qmaClause3ToBits E') : E = E' := by
  cases E with
  | mk qc w terms =>
      cases E' with
      | mk qc' w' terms' =>
          have h' : qmaClause3EncNat qc
                ++ (qmaClause3EncNat w ++ qmaClause3EncList (fun t : LhTerm qc => qmaClause3EncTerm t) terms)
              = qmaClause3EncNat qc'
                ++ (qmaClause3EncNat w' ++ qmaClause3EncList (fun t : LhTerm qc' => qmaClause3EncTerm t) terms') := by
            simpa only [qmaClause3ToBits, List.append_assoc] using h
          obtain ⟨hq, hrest⟩ := clause3Aux_encNat_selfDelimiting qc qc' _ _ h'
          subst qc'
          obtain ⟨hw, hrest2⟩ := clause3Aux_encNat_selfDelimiting w w' _ _ hrest
          obtain ⟨hterms, hsu⟩ := clause3Aux_encList_selfDelimiting
            (fun a b (s u : List Bool) => clause3Aux_encTerm_selfDelimiting s u)
            terms terms' [] [] (by simpa using hrest2)
          subst terms'
          subst w'
          rfl

theorem clause3Aux_yes_no_disjoint (k : ℕ) (x : List Bool) :
    ¬ (qmaClause3YesBits k x ∧ qmaClause3NoBits k x) := by
  rintro ⟨⟨E, hx, hloc, hherm, hyes⟩, ⟨E', hx', hloc', hherm', hno⟩⟩
  have hEq : E = E' := clause3Aux_toBits_injective (hx.trans hx'.symm)
  subst hEq
  obtain ⟨η, hnorm, hle⟩ := hyes
  have hge := hno η hnorm
  have hle0 : qmaEnergy (lhHamiltonian E) η ≤ 0 := by
    simpa [qmaClause3YesBound] using hle
  have hpos : 0 < qmaClause3NoBound E := by
    unfold qmaClause3NoBound
    positivity
  have hge0 : 0 < qmaEnergy (lhHamiltonian E) η := by
    linarith
  linarith

theorem clause3Aux_frozen_collision_separated : qmaClause3ToBits clause3E1 ≠ qmaClause3ToBits clause3E2 := by
  decide

theorem clause3Aux_outputBit_index (w a : ℕ) (p : Reg (w + a + 1)) :
    qmaOutputBit w a p = p (Fin.natAdd (w + a) 0) := rfl

theorem clause3Aux_ancillaBit_index (w a : ℕ) (p : Reg (w + a + 1)) (j : Fin a) :
    qmaAncillaBits w a p j = p (Fin.castAdd 1 (Fin.natAdd w j)) := rfl

theorem clause3Aux_regSplit (w a : ℕ) (p : Reg (w + a + 1)) :
    qmaRegSplit w a p
      = ((qmaWitnessBits w a p, qmaAncillaBits w a p), fun _ : Fin 1 => qmaOutputBit w a p) := by
  apply Prod.ext
  · apply Prod.ext
    · funext i
      rfl
    · funext j
      rfl
  · funext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    rw [hj]
    rfl

theorem clause3Aux_outWire_eq (V : QmaVerifier) (x : List Bool) :
    (qmaClause3OutWire V x : Fin (qmaRegisterSize V x.length))
      = Fin.natAdd (V.witnessQubits x.length + V.auxQubits x.length) 0 := by
  apply Fin.ext
  show V.witnessQubits x.length + V.auxQubits x.length
    = (V.witnessQubits x.length + V.auxQubits x.length) + 0
  omega

theorem clause3Aux_initState_shape (w a : ℕ) (ψ : QState (Reg w)) (p : Reg (w + a + 1)) :
    qmaInitialState w a ψ p
      = ψ (qmaWitnessBits w a p)
        * (if qmaAncillaBits w a p = ZeroStr a then (1 : ℂ) else 0)
        * (if qmaOutputBit w a p = false then (1 : ℂ) else 0) := by
  have hket1 : (Ket (ZeroStr a) (qmaAncillaBits w a p) : ℂ)
      = if qmaAncillaBits w a p = ZeroStr a then 1 else 0 := cnotAux_ket_zero _
  have hket2 : (Ket (ZeroStr 1) (fun _ : Fin 1 => qmaOutputBit w a p) : ℂ)
      = if qmaOutputBit w a p = false then 1 else 0 := by
    rw [cnotAux_ket_zero]
    by_cases h : qmaOutputBit w a p = false
    · have heq : (fun _ : Fin 1 => qmaOutputBit w a p) = ZeroStr 1 := by
        funext j
        show qmaOutputBit w a p = false
        exact h
      rw [if_pos heq, if_pos h]
    · have hne : ¬ (fun _ : Fin 1 => qmaOutputBit w a p) = ZeroStr 1 := by
        intro heq
        exact h (congrFun heq 0)
      rw [if_neg hne, if_neg h]
  rw [qmaInitialState, clause3Aux_regSplit w a p]
  simp only [tensorState_apply]
  rw [hket1, hket2]

theorem clause3Aux_initState_zero_ancilla (w a : ℕ) (ψ : QState (Reg w)) (p : Reg (w + a + 1))
    (h : qmaAncillaBits w a p ≠ ZeroStr a) : qmaInitialState w a ψ p = 0 := by
  rw [clause3Aux_initState_shape]
  rw [if_neg h]
  ring

theorem clause3Aux_initState_zero_output (w a : ℕ) (ψ : QState (Reg w)) (p : Reg (w + a + 1))
    (h : qmaOutputBit w a p = true) : qmaInitialState w a ψ p = 0 := by
  rw [clause3Aux_initState_shape]
  have hne : qmaOutputBit w a p ≠ false := by
    rw [h]
    simp
  by_cases h1 : qmaAncillaBits w a p = ZeroStr a
  · rw [if_pos h1, if_neg hne]
    ring
  · rw [if_neg h1, if_neg hne]
    ring

theorem clause3Aux_initState_support_aux (w a : ℕ) (ψ : QState (Reg w)) (p : Reg (w + a + 1))
    (j : Fin (w + a + 1)) (hjaux : w ≤ j.val ∧ j.val < w + a)
    (hp : qmaInitialState w a ψ p ≠ 0) : p j = false := by
  have hanc : qmaAncillaBits w a p = ZeroStr a := by
    by_contra h
    have hz := clause3Aux_initState_zero_ancilla w a ψ p h
    exact hp hz
  obtain ⟨j', hj'⟩ : ∃ j' : Fin a, j = Fin.castAdd 1 (Fin.natAdd w j') := by
    refine ⟨⟨j.val - w, by omega⟩, ?_⟩
    apply Fin.ext
    simp
    omega
  rw [hj']
  have hz : ∀ k : Fin a, qmaAncillaBits w a p k = false := (cnotAux_zeroStr_iff _).mp hanc
  have hzz := hz j'
  rwa [clause3Aux_ancillaBit_index] at hzz

theorem clause3Aux_initState_support_out (w a : ℕ) (ψ : QState (Reg w)) (p : Reg (w + a + 1))
    (j : Fin (w + a + 1)) (hjout : j.val = w + a)
    (hp : qmaInitialState w a ψ p ≠ 0) : p j = false := by
  have hout : qmaOutputBit w a p = false := by
    by_cases h : qmaOutputBit w a p = false
    · exact h
    · have hz := clause3Aux_initState_zero_output w a ψ p (by simpa using h)
      exact (hp hz).elim
  have hj' : j = Fin.natAdd (w + a) 0 := by
    apply Fin.ext
    show j.val = (w + a) + 0
    omega
  rw [hj']
  rw [← (clause3Aux_outputBit_index w a p)]
  exact hout

theorem clause3Aux_initLegal_verifierInitial (V : QmaVerifier) (x : List Bool)
    (ψ : QState (Reg (V.witnessQubits x.length))) :
    QmaInitLegal (qmaClause3VerifierCircuit V x)
      (qmaInitialState (V.witnessQubits x.length) (V.auxQubits x.length) ψ) := by
  intro p hp j hj
  rcases Finset.mem_union.mp hj with hjaux | hjout
  · exact clause3Aux_initState_support_aux (V.witnessQubits x.length) (V.auxQubits x.length) ψ p j
      (Finset.mem_filter.mp hjaux).2 hp
  · have hj'' : j = qmaClause3OutWire V x := by
      simpa [qmaClause3OutWire] using (Finset.mem_singleton.mp hjout)
    have hjval : j.val = V.witnessQubits x.length + V.auxQubits x.length := by
      rw [hj'']
      rfl
    exact clause3Aux_initState_support_out (V.witnessQubits x.length) (V.auxQubits x.length) ψ p j
      hjval hp

theorem clause3Aux_historyAcceptProb_eq (V : QmaVerifier) (x : List Bool)
    (ψ : QState (Reg (V.witnessQubits x.length))) :
    qmaHistoryAcceptProb (qmaClause3VerifierCircuit V x)
        (qmaInitialState (V.witnessQubits x.length) (V.auxQubits x.length) ψ)
      = qmaAcceptProb V x ψ := by
  have hev : (Finset.univ.filter fun z : Reg (qmaRegisterSize V x.length) =>
      z (qmaClause3OutWire V x))
      = qmaAcceptEvent (V.witnessQubits x.length) (V.auxQubits x.length) := by
    ext z
    constructor
    · intro hz
      have hz' := (Finset.mem_filter.mp hz).2
      rw [clause3Aux_outWire_eq] at hz'
      rw [← (clause3Aux_outputBit_index (V.witnessQubits x.length) (V.auxQubits x.length) z)] at hz'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz'⟩
    · intro hz
      have hz' := (Finset.mem_filter.mp hz).2
      rw [(clause3Aux_outputBit_index (V.witnessQubits x.length) (V.auxQubits x.length) z)] at hz'
      rw [← clause3Aux_outWire_eq] at hz'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz'⟩
  unfold qmaHistoryAcceptProb qmaAcceptProb
  have h1 : (Finset.univ.filter fun z : Reg (qmaRegisterSize V x.length) =>
      z (qmaClause3OutWire V x))
      = qmaAcceptEvent (V.witnessQubits x.length) (V.auxQubits x.length) := hev
  simp only [qmaClause3VerifierCircuit]
  exact congrArg (fun S : Finset (Reg (qmaRegisterSize V x.length)) =>
    MeasureProb
      (Run (1 : Matrix (Reg (qmaRegisterSize V x.length)) (Reg (qmaRegisterSize V x.length)) ℂ)
        (finiteCodeCircuit (qmaRegisterSize V x.length) (V.program x))
        (qmaInitialState (V.witnessQubits x.length) (V.auxQubits x.length) ψ)) S) h1

theorem clause3Aux_verifierCircuit_gates_le (V : QmaVerifier) (x : List Bool) :
    ∃ c k : ℕ, (qmaClause3VerifierCircuit V x).gates.length ≤ c * x.length ^ k + c := by
  obtain ⟨c, k, hk⟩ := V.sizeBound
  exact ⟨c, k, hk x⟩

end Qatlib.Concepts.QmaCompleteness.HistoryHam
