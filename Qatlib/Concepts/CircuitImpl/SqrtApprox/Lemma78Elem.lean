/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.SqrtApprox.Lemma78Stat
import Qatlib.Concepts.CircuitImpl.SqrtApprox.UnitarySqrtChain
import Qatlib.Concepts.CircuitImpl.SqrtApprox.Lemma78
import Qatlib.Concepts.CircuitImpl.SqrtApprox.TruncatedMultiControl
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation

/-!
# Elementary synthesis for approximate multi-controlled gates

This module proves `lemma7_8`, the full-matrix approximation statement for multi-controlled
single-qubit gates associated with Lemma 7.8 of [BarencoEtAl1995]. Auxiliary results cover zero
truncation levels, exact synthesis within the available budget, small control counts, and the
action of a recursive step when its last control is false.

`lemma7_8_readout` uses the same legal query-free gate program to bound measurement-probability
error on every normalized input state.

## Main statements

* `lemma7_8`: full-register operator-norm approximation with the prescribed gate bound.
* `lemma7_8_readout`: measurement-probability error at most `2 * (π / 2^k)`.

## References

* [Barenco et al., 1995, Section 7][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.SqrtApprox

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The residual-unitary approximation predicate for a fixed gate and control layout, including
legality, gate counts, and the bound `‖V - 1‖ ≤ π / 2^k`. -/
def elementaryApproxTable {N : ℕ} (m k : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (U : Matrix Bool Bool ℂ) : Prop :=
  ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
    gs.length ≤ (240 * (m + 1) + 20) * k ∧
    QueryCount (reflectionCompile gs) = 0 ∧
    GateCount (reflectionCompile gs) = gs.length ∧
    ∃ V : Matrix Bool Bool ℂ, V ∈ unitaryGroup Bool ℂ ∧
      ‖(V - 1 : Matrix Bool Bool ℂ)‖ ≤ Real.pi / (2 ^ k : ℝ) ∧
      ∀ x φ, Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs)
        (multiWireState t x φ) = multiWireState t x
          (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then U * V else 1) φ)

/-- At zero truncation levels, every unitary target satisfies the residual-unitary approximation
predicate. -/
theorem lemma7_8_zero_levels {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    elementaryApproxTable m 0 c t U := by
  have hUa : Uᴴ ∈ unitaryGroup Bool ℂ := by
    simpa only [Matrix.star_eq_conjTranspose] using! Unitary.star_mem hU
  obtain ⟨seq, hzero, _, _, hnorm⟩ := unitary_sqrt_chain_spec Bool Uᴴ hUa
  have hb : ‖Uᴴ - 1‖ ≤ Real.pi := by simpa only [hzero, pow_zero, div_one] using! hnorm 0
  refine ⟨[], by simp [reflectionLegal], by simp, queryCount_reflectionCompile _,
    gateCount_reflectionCompile _, Uᴴ, hUa, by simpa only [pow_zero, div_one] using! hb, ?_⟩
  intro x φ
  rw [show U * Uᴴ = 1 from hU.2]
  simp [reflectionCompile]

/-- Distinct controls avoiding the target permit the residual-unitary approximation whenever the
stated gate budget covers the quadratic exact-synthesis bound. -/
theorem lemma7_8_of_exact_budget {N : ℕ} (m k : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (hc : Set.InjOn c (Set.Iio m)) (hct : ∀ i < m, c i ≠ t)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ)
    (hbudget : 256 * (m + 1) ^ 2 ≤ (240 * (m + 1) + 20) * k) :
    elementaryApproxTable m k c t U := by
  obtain ⟨gs, hgs, hlen, hrun⟩ := noWork_multi_control_wire_table m c t hc hct U hU
  refine ⟨gs, hgs, hlen.trans hbudget, queryCount_reflectionCompile _,
    gateCount_reflectionCompile _, 1, by simp, ?_, ?_⟩
  · simp only [sub_self, norm_zero]
    positivity
  · simpa only [Matrix.mul_one] using! hrun

/-- With distinct controls avoiding the target, `k ≥ 2 * (m + 1)` suffices for the
residual-unitary approximation predicate. -/
theorem lemma7_8_large_levels {N : ℕ} (m k : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (hc : Set.InjOn c (Set.Iio m)) (hct : ∀ i < m, c i ≠ t)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) (hk : 2 * (m + 1) ≤ k) :
    elementaryApproxTable m k c t U := by
  apply lemma7_8_of_exact_budget m k c t hc hct U hU
  nlinarith [Nat.mul_le_mul_left (240 * (m + 1) + 20) hk]

/-- A unitary gate with no controls satisfies the residual-unitary approximation predicate at
every positive truncation level. -/
theorem lemma7_8_no_controls {N : ℕ} (k : ℕ) (hk : 0 < k) (c : ℕ → Fin N) (t : Fin N)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    elementaryApproxTable 0 k c t U := by
  refine ⟨[.inl (t, U)], ?_, by simp; omega, queryCount_reflectionCompile _,
    gateCount_reflectionCompile _, 1, by simp, ?_, ?_⟩
  · intro g hg
    obtain rfl := List.mem_singleton.mp hg
    exact hU
  · simp only [sub_self, norm_zero]
    positivity
  · intro x φ
    simp only [reflectionCompile, List.map_cons, List.map_nil, run_gate, run_nil,
      reflectionGateMatrix, Matrix.mul_one]
    simpa [noWorkPrefixAnd] using! multiWireState_single t x U φ

/-- A unitary gate with one control distinct from its target satisfies the residual-unitary
approximation predicate at every positive truncation level. -/
theorem lemma7_8_one_control {N : ℕ} (k : ℕ) (hk : 0 < k) (c : ℕ → Fin N) (t : Fin N)
    (hct : c 0 ≠ t) (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    elementaryApproxTable 1 k c t U := by
  let p := knownQubitAnglesOfUnitary U
  have hp : knownQubitUnitary p = U := (knownQubitEuler_explicit_angles_cover_unitaries U hU).1
  refine ⟨multiKnownPairSteps (c 0) t p, multiKnownPairSteps_legal _ _ hct _,
    ?_, queryCount_reflectionCompile _, gateCount_reflectionCompile _, 1, by simp, ?_, ?_⟩
  · have hlen : (multiKnownPairSteps (c 0) t p).length = 6 := rfl
    rw [hlen]
    omega
  · simp only [sub_self, norm_zero]
    positivity
  · intro x φ
    rw [multiKnownPairSteps_action _ _ hct, hp, Matrix.mul_one]
    simp [noWorkPrefixAnd]

/-- Boolean sequences agreeing on their first `m` entries have the same prefix conjunction. -/
private theorem elementary_truncation_prefix_congr (a b : ℕ → Bool) (m : ℕ)
    (h : ∀ i < m, a i = b i) : noWorkPrefixAnd a m = noWorkPrefixAnd b m := by
  apply Bool.eq_iff_iff.mpr
  simp only [noWorkPrefixAnd, List.all_eq_true, List.mem_range]
  constructor
  · intro ha i hi
    rw [← h i hi]
    exact ha i hi
  · intro hb i hi
    rw [h i hi]
    exact hb i hi

/-- When the prefix controls are true and the last control is false, the specified two-toggle
gate sequence applies `Vᴴ` to the target-wire state. -/
theorem elementary_truncated_step_false_control {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (hct : ∀ i < m, c i ≠ t) (hccl : ∀ i < m, c i ≠ c m) (hlast : c m ≠ t)
    (V : Matrix Bool Bool ℂ) (hV : V ∈ unitaryGroup Bool ℂ)
    (xs : List (ReflectionGate N))
    (hx : ∀ x : Reg N, Run 1 (reflectionCompile xs) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x (c m) (x (c m) ^^ noWorkPrefixAnd (fun i => x (c i)) m)))
    (x : Reg N) (ha : noWorkPrefixAnd (fun i => x (c i)) m = true)
    (hb : x (c m) = false) (φ : QState Bool) :
    let p := knownQubitAnglesOfUnitary V
    Run (1 : Matrix (Reg N) (Reg N) ℂ)
      (reflectionCompile (multiKnownPairSteps (c m) t p ++ xs ++
        multiKnownPairSteps (c m) t (knownQubitAngleAdjoint p) ++ xs))
      (multiWireState t x φ) = multiWireState t x (ApplyGate Vᴴ φ) := by
  (try dsimp only)
  let p := knownQubitAnglesOfUnitary V
  have hp : knownQubitUnitary p = V := (knownQubitEuler_explicit_angles_cover_unitaries V hV).1
  have hpadj : knownQubitUnitary (knownQubitAngleAdjoint p) = Vᴴ := by
    rw [knownQubitUnitary_adjoint, hp]
  let q := Function.update x (c m) (x (c m) ^^ noWorkPrefixAnd (fun i => x (c i)) m)
  have hA : noWorkPrefixAnd (fun i => q (c i)) m = true := by
    change noWorkPrefixAnd (fun i => Function.update x (c m) _ (c i)) m = true
    rw [elementary_truncation_prefix_congr _ (fun i => x (c i)) m
      (fun i hi => Function.update_of_ne (hccl i hi) _ _), ha]
  have hq : q (c m) = true := by simp [q, ha, hb]
  have hrestore : Function.update q (c m)
      (q (c m) ^^ noWorkPrefixAnd (fun i => q (c i)) m) = x := by
    rw [hA, hq]
    have hid : Function.update x (c m) false = x := by
      rw [← hb]
      exact Function.update_eq_self _ _
    simp [q, ha, hb]
  simp only [reflectionCompile_append, run_append]
  rw [multiKnownPairSteps_action (c m) t hlast p, hp,
    noWork_and_table_wireState c m (c m) t hlast hct xs hx,
    multiKnownPairSteps_action (c m) t hlast (knownQubitAngleAdjoint p), hpadj]
  change Run 1 (reflectionCompile xs)
    (multiWireState t q (ApplyGate (if q (c m) then Vᴴ else 1)
      (ApplyGate (if x (c m) then V else 1) φ))) = _
  rw [noWork_and_table_wireState c m (c m) t hlast hct xs hx, hrestore, hq, hb]
  simp [applyGate_one]

/-- The full-matrix multi-controlled synthesis statement `Lemma7_8`, corresponding to [Barenco
et al., Lemma 7.8][BarencoEtAl1995]. -/
theorem lemma7_8 : Lemma7_8 := by
  intro N m k c t hc hct U hU
  obtain ⟨seq,hzero,hu,hs,hbound⟩ := unitary_sqrt_chain_spec Bool U hU
  obtain ⟨gs,hgs,hlen,G,hG,herr,hsem⟩ := elementary_truncated_chain seq hu hs m k 0 c t hc hct
  refine ⟨gs,hgs,hlen,queryCount_reflectionCompile _,gateCount_reflectionCompile _,G,hG,?_,?_⟩
  · have herr' : ‖reflectionProgramMatrix gs-G‖≤‖seq k-1‖ := by
      simpa only [Nat.zero_add] using! herr
    exact herr'.trans (hbound k)
  · simpa only [hzero] using! hsem

/-- A legal query-free program with the prescribed gate bound approximates the ideal
multi-controlled gate so that every measurement event on a normalized input has probability
error at most `2 * (π / 2^k)`. -/
theorem lemma7_8_readout (N m k : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (hc : Set.InjOn c (Set.Iio m)) (hct : ∀ i < m,c i≠t)
    (U : Matrix Bool Bool ℂ) (hU : U∈unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
      gs.length≤(240*(m+1)+20)*k ∧ QueryCount (reflectionCompile gs)=0 ∧
      GateCount (reflectionCompile gs)=gs.length ∧
      ∃ G : Matrix (Reg N) (Reg N) ℂ, G∈unitaryGroup (Reg N) ℂ ∧
        (∀ x φ,ApplyGate G (multiWireState t x φ)=multiWireState t x
          (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then U else 1) φ)) ∧
        ∀ ψ : QState (Reg N), Normalized ψ → ∀ E : Finset (Reg N),
          |MeasureProb (Run 1 (reflectionCompile gs) ψ) E-MeasureProb (ApplyGate G ψ) E|
            ≤2*(Real.pi/(2^k : ℝ)) := by
  obtain ⟨gs,hgs,hlen,hq,hg,G,hG,herr,hsem⟩ := lemma7_8 N m k c t hc hct U hU
  refine ⟨gs,hgs,hlen,hq,hg,G,hG,hsem,?_⟩
  intro ψ hψ E
  rw [run_reflectionCompile]
  let S := reflectionProgramMatrix gs
  have hS : S∈unitaryGroup (Reg N) ℂ := reflectionProgramMatrix_unitary gs hgs
  have hp := measureProb_sub_le_two_mul_l2 (ApplyGate S ψ) (ApplyGate G ψ) E
    (normalized_applyGate hS hψ) (normalized_applyGate hG hψ)
  have hd : ApplyGate S ψ-ApplyGate G ψ=ApplyGate (S-G) ψ := by
    simp only [ApplyGate,Matrix.sub_mulVec]
  have hv : ‖toEuclidean_fromVec (ApplyGate S ψ-ApplyGate G ψ)‖≤Real.pi/(2^k : ℝ) := by
    rw [hd,← toEuclideanCLM_applyGate]
    have h := ((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix (Reg N) (Reg N) ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Reg N) →L[ℂ] EuclideanSpace ℂ (Reg N))) (S-G)).le_opNorm (toEuclidean_fromVec ψ)
    rw [← Matrix.cstar_norm_def, (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ,mul_one] at h
    exact h.trans herr
  exact hp.trans (mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ)≤2))

end Qatlib.Concepts.CircuitImpl.SqrtApprox
