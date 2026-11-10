/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemGates95.BorrowedAnd.Section7.BorrowedNetworks
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Qatlib.Papers.ElemGates95.ThreeQubit
import Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharp
import Qatlib.Concepts.CircuitImpl.MultiControl.Corollary710Elem
import Qatlib.Concepts.CircuitImpl.SqrtApprox.Lemma78Elem
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped Matrix.Norms.L2Operator
open Qatlib.Papers.ElemGates95.QubitControl.Section4
open Qatlib.Papers.ElemGates95.QubitControl.Section5
open Qatlib.Papers.ElemGates95.ThreeQubit

namespace Qatlib.Papers.ElemGates95.MultiControl.Section7

theorem corollary7_4_paper (N n : ℕ) (c : ℕ → Fin N) (s t : Fin N)
    (hn : 7 ≤ n) (hc : Set.InjOn c (Set.Iio (n - 2)))
    (hcs : ∀ i < n - 2, c i ≠ s) (hct : ∀ i < n - 2, c i ≠ t) (hst : s ≠ t) :
    ∃ gs : List (ReflectionGate N),
      reflectionLegal gs ∧
      toffCount (cor74Blocks (n - 2) c s t) = 8 * (n - 5) ∧
      exactCount (cor74Blocks (n - 2) c s t) = 4 ∧
      gs.length ≤ 48 * n - 204 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ x : Reg N,
        Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs) (Ket x) =
          Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) (n - 2))) := by
  obtain ⟨htoff, hexact, hlen, hlegal, hq, hg, hrun⟩ :=
    corollary7_4_two_layer_ledger (N := N) (n := n) c s t hn hc hcs hct hst
  exact ⟨cor74Word (n - 2) c s t, hlegal, htoff, hexact, hlen, hq, hg, hrun⟩

theorem corollary7_6 (n : ℕ) (_hn : 2 ≤ n) (p : KnownQubitAngles) :
    ∃ gs : List (ReflectionGate ((n - 1) + 1)),
      reflectionLegal gs ∧ gs.length ≤ 256 * ((n - 1) + 1) ^ 2 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg (n - 1) × Bool),
        Run 1 (reflectionCompile gs)
            (relabelState (noWorkControlSplit (n - 1)).symm ψ) =
          relabelState (noWorkControlSplit (n - 1)).symm
            (multiKnownGate (n - 1) (knownQubitUnitary p) *ᵥ ψ) := by
  obtain ⟨gs, hlegal, hle, hq, hg, hrun⟩ :=
    no_work_multi_known_control_local_table_and_cost (n - 1) p
  exact ⟨gs, hlegal, hle, hq, hg, hrun⟩

theorem lemma7_8_approx (N m k : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (hc : Set.InjOn c (Set.Iio m)) (hct : ∀ i < m, c i ≠ t)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
      gs.length ≤ (240 * (m + 1) + 20) * k ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∃ G : Matrix (Reg N) (Reg N) ℂ, G ∈ Matrix.unitaryGroup (Reg N) ℂ ∧
        ‖reflectionProgramMatrix gs - G‖ ≤ Real.pi / (2 ^ k : ℝ) ∧
        ∀ (x : Reg N) (φ : QState Bool), ApplyGate G (multiWireState t x φ) =
          multiWireState t x
            (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then U else 1) φ) :=
  Qatlib.Concepts.CircuitImpl.SqrtApprox.lemma7_8 N m k c t hc hct U hU

def approximationDepth (ε : ℝ) : ℕ := Nat.ceil (Real.logb 2 (Real.pi / ε))

theorem approximationDepth_error_bound (ε : ℝ) (hε : 0 < ε) :
    Real.pi / (2 ^ approximationDepth ε : ℝ) ≤ ε := by
  have hx : 0 < Real.pi / ε := div_pos Real.pi_pos hε
  have hp : Real.pi / ε ≤ (2 : ℝ) ^ approximationDepth ε := by
    have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hx).mp
      (Nat.le_ceil (Real.logb 2 (Real.pi / ε)))
    simpa only [approximationDepth, Real.rpow_natCast] using! h
  have hpow : (0 : ℝ) < 2 ^ approximationDepth ε := by positivity
  apply (div_le_iff₀ hpow).mpr
  exact (div_le_iff₀ hε).mp hp |>.trans_eq (mul_comm _ _)

theorem lemma7_8_with_tolerance (N m : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (hc : Set.InjOn c (Set.Iio m)) (hct : ∀ i < m, c i ≠ t)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
      gs.length ≤ (240 * (m + 1) + 20) * approximationDepth ε ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∃ G : Matrix (Reg N) (Reg N) ℂ, G ∈ Matrix.unitaryGroup (Reg N) ℂ ∧
        ‖reflectionProgramMatrix gs - G‖ ≤ ε ∧
        ∀ (x : Reg N) (φ : QState Bool), ApplyGate G (multiWireState t x φ) =
          multiWireState t x
            (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then U else 1) φ) := by
  obtain ⟨gs, hl, hn, hq, hg, G, hG, he, hs⟩ :=
    lemma7_8_approx N m (approximationDepth ε) c t hc hct U hU
  exact ⟨gs, hl, hn, hq, hg, G, hG, he.trans (approximationDepth_error_bound ε hε), hs⟩

theorem lemma7_9_five_block (W : Matrix Bool Bool ℂ)
    (hW : W ∈ Matrix.unitaryGroup Bool ℂ) (hdet : W.det = 1) :
    ∃ A B C : Matrix Bool Bool ℂ, SU2 A ∧ SU2 B ∧ SU2 C ∧
      ∀ last otherControls : Bool,
        (if last then A else 1) * (if otherControls then PauliX else 1) *
          (if last then B else 1) * (if otherControls then PauliX else 1) *
          (if last then C else 1) = if last && otherControls then W else 1 := by
  obtain ⟨A, B, C, hAu, hBu, hCu, hAd, hBd, hCd, hABC, hprod⟩ := lemma4_3 W hW hdet
  refine ⟨A, B, C, ⟨hAu, hAd⟩, ⟨hBu, hBd⟩, ⟨hCu, hCd⟩, ?_⟩
  intro last otherControls
  cases last <;> cases otherControls <;> simp [hABC, hprod, pauliX_mul_self]

theorem lemma7_9 (N m : ℕ) (c : ℕ → Fin N) (t : Fin N) (W : Matrix Bool Bool ℂ)
    (hW : W ∈ Matrix.unitaryGroup Bool ℂ) (hdet : W.det = 1)
    (hc : Set.InjOn c (Set.Iio m)) (hct : ∀ i < m, c i ≠ t) :
    (∃ A B C : Matrix Bool Bool ℂ,
        SU2 A ∧ SU2 B ∧ SU2 C ∧ A * B * C = 1 ∧ A * PauliX * B * PauliX * C = W) ∧
      ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
        QueryCount (reflectionCompile gs) = 0 ∧
        GateCount (reflectionCompile gs) = gs.length ∧
        ∀ (x : Reg N) (φ : QState Bool),
          Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs)
              (multiWireState t x φ) =
            multiWireState t x
              (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then W else 1) φ) := by

  have hfac := lemma4_3 W hW hdet
  refine ⟨?_, ?_⟩
  · obtain ⟨A, B, C, hAu, hBu, hCu, hAd, hBd, hCd, hABC, hprod⟩ := hfac
    exact ⟨A, B, C, ⟨hAu, hAd⟩, ⟨hBu, hBd⟩, ⟨hCu, hCd⟩, hABC, hprod⟩
  · obtain ⟨gs, hlegal, _, hrun⟩ :=
      noWork_multi_control_wire_table m c t hc hct W hW
    exact ⟨gs, hlegal, queryCount_reflectionCompile _,
      gateCount_reflectionCompile _, hrun⟩

theorem corollary7_10_paper (N m : ℕ) (c : ℕ → Fin N) (s t : Fin N)
    (hc : Set.InjOn c (Set.Iio m)) (hcs : ∀ i < m, c i ≠ s) (hct : ∀ i < m, c i ≠ t)
    (hst : s ≠ t) (W : Matrix Bool Bool ℂ) (hW : W ∈ Matrix.unitaryGroup Bool ℂ)
    (hdet : W.det = 1) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
      gs.length ≤ 240 * (m + 2) ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ (x : Reg N) (φ : QState Bool),
        Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs)
            (multiWireState t x φ) =
          multiWireState t x
            (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then W else 1) φ) :=
  Qatlib.Concepts.CircuitImpl.MultiControl.corollary7_10
    N m c s t hc hcs hct hst W hW hdet

theorem lemma7_11 (N m : ℕ) (c : ℕ → Fin N) (s t : Fin N) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (hc : Set.InjOn c (Set.Iio m)) (hcs : ∀ i < m, c i ≠ s)
    (hct : ∀ i < m, c i ≠ t) (hst : s ≠ t) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ (x : Reg N), x s = false → ∀ φ : QState Bool,
        Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs)
            (multiWireState t x φ) =
          multiWireState t x
            (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then U else 1) φ) := by

  let p := knownQubitAnglesOfUnitary U
  have hp : knownQubitUnitary p = U :=
    (knownQubitEuler_explicit_angles_cover_unitaries U hU).1
  obtain ⟨as, has, -, ha⟩ := noWork_single_dirty_and_table c t s m hc hct hcs hst.symm
  let bs := multiKnownPairSteps s t p
  have hbs : reflectionLegal bs := multiKnownPairSteps_legal s t hst p
  refine ⟨as ++ bs ++ as, ?_, queryCount_reflectionCompile _, gateCount_reflectionCompile _, ?_⟩
  · simp only [reflectionLegal_append]
    exact ⟨⟨has, hbs⟩, has⟩
  · intro x hxs φ
    let a := noWorkPrefixAnd (fun i => x (c i)) m
    let q := Function.update x s (x s ^^ a)
    have hPrefix (v : Bool) :
        noWorkPrefixAnd (fun i => Function.update x s v (c i)) m = a := by
      apply Bool.eq_iff_iff.mpr
      simp only [a, noWorkPrefixAnd, List.all_eq_true, List.mem_range]
      constructor <;> intro h i hi
      · simpa [Function.update_of_ne (hcs i hi)] using! h i hi
      · simpa [Function.update_of_ne (hcs i hi)] using! h i hi
    have hq : q s = a := by simp [q, hxs]
    have hA : noWorkPrefixAnd (fun i => q (c i)) m = a := by
      simpa only [q] using! hPrefix (x s ^^ a)
    have hrestore :
        Function.update q s (q s ^^ noWorkPrefixAnd (fun i => q (c i)) m) = x := by
      rw [hA, hq]
      simp only [Bool.xor_self]
      dsimp only [q]
      rw [Function.update_idem]
      rw [← hxs]
      exact Function.update_eq_self s x
    simp only [reflectionCompile_append, run_append]
    rw [noWork_and_table_wireState c m s t hst hct as ha,
      multiKnownPairSteps_action s t hst p]
    change Run 1 (reflectionCompile as)
      (multiWireState t q (ApplyGate (if q s then knownQubitUnitary p else 1) φ)) = _
    rw [noWork_and_table_wireState c m s t hst hct as ha, hrestore, hq, hp]

theorem corollary7_12_paper (n : ℕ) (_hn : 3 ≤ n) (p : KnownQubitAngles) :
    ∃ gs : List (ReflectionGate ((n - 2) + 1 + 1)), reflectionLegal gs ∧
      gs.length ≤ 720 * ((n - 2) + 1) + 6 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg (n - 2) × Bool),
        Run 1 (reflectionCompile gs) (singleAncillaEmbed (n - 2) ψ) =
          singleAncillaEmbed (n - 2) (multiKnownGate (n - 2) (knownQubitUnitary p) *ᵥ ψ) :=
  single_ancilla_known_control_local_table_and_cost (n - 2) p

end Qatlib.Papers.ElemGates95.MultiControl.Section7
