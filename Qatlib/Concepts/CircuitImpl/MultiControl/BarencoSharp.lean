/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharpDefs
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.MultiKnownQubitControl
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Qatlib.Concepts.GateTables.GrayUniversal.GrayCodeSynthesis
import Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharpCount
import Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharpDimension

/-!
# Sharp multi-control synthesis and circuit dimension

`cor74Word_semantics` and `cor76_control_table` give exact conjunction toggles and controlled
qubit unitaries with explicit elementary-gate bounds. Gray-path constructions extend these words
to arbitrary two-level instructions and then to all unitaries on a nonempty qubit register,
following the synthesis framework of [BarencoEtAl1995].

The module also defines Euler and canonical two-qubit parameter families. It proves smoothness
and Hausdorff-dimension bounds for fixed wire lists, and derives omitted-target results under an
explicit dimension hypothesis on the target set.

## Main statements

* `corollary7_4_two_layer_ledger`: Block counts, elementary-gate bounds, legality, and basis
  semantics for the conjunction toggle.
* `cor76_section8_gray_universality`: Exact unitary synthesis with an explicit gate bound.
* `barenco_kakForm_dimH_le`: Hausdorff-dimension bound for the nine-parameter circuit family.
* `barenco_kakFullForm_dimH_le`: Hausdorff-dimension bound for the fifteen-parameter circuit
  family.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharpCount
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl

open Matrix
open scoped Classical BigOperators
open Qatlib
open Qatlib.Concepts.CircuitImpl.MultiControl.CountPackedCommutator
open Qatlib.Concepts.GateTables.GrayUniversal

/-- For at least five distinct controls, `cor74Word` toggles the target by their conjunction on
each computational basis state and preserves all other wires. -/
theorem cor74Word_semantics {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (s t : Fin N)
    (hm : 5 ≤ m) (hc : Set.InjOn c (Set.Iio m))
    (hcs : ∀ i < m, c i ≠ s) (hct : ∀ i < m, c i ≠ t) (hst : s ≠ t) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (cor74Word m c s t)) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) m)) :=
  (cor74_word_package m c s t hm hc hcs hct hst).2.2.2 x

/-- For `n ≥ 7`, the Corollary 7.4 construction has `8 * (n - 5)` Toffoli blocks, four exact
blocks, and at most `48 * n - 204` elementary gates. It is legal, uses no queries, and
toggles the target by the conjunction of its `n - 2` controls [Barenco et al., Corollary
7.4][BarencoEtAl1995]. -/
theorem corollary7_4_two_layer_ledger {N n : ℕ} (c : ℕ → Fin N) (s t : Fin N)
    (hn : 7 ≤ n) (hc : Set.InjOn c (Set.Iio (n-2)))
    (hcs : ∀ i < n-2, c i ≠ s) (hct : ∀ i < n-2, c i ≠ t) (hst : s ≠ t) :
    toffCount (cor74Blocks (n-2) c s t) = 8*(n-5) ∧
    exactCount (cor74Blocks (n-2) c s t) = 4 ∧
    (cor74Word (n-2) c s t).length ≤ 48*n-204 ∧
    reflectionLegal (cor74Word (n-2) c s t) ∧
    QueryCount (reflectionCompile (cor74Word (n-2) c s t)) = 0 ∧
    GateCount (reflectionCompile (cor74Word (n-2) c s t)) = (cor74Word (n-2) c s t).length ∧
    ∀ x : Reg N,
      Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (cor74Word (n-2) c s t)) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) (n-2))) := by
  have hm : 5 ≤ n-2 := by omega
  have hpack := cor74_word_package (n-2) c s t hm hc hcs hct hst
  obtain ⟨hc1, hc2, hc3⟩ := cor74Blocks_census (n-2) c s t hm
  have hlen := cor74Word_length (n-2) c s t hm
  refine ⟨?_, hc2, ?_, hpack.1, hpack.2.1, hpack.2.2.1, hpack.2.2.2⟩ <;> omega

/-- Constructs a legal conjunction-controlled target toggle with a separate spectator wire,
using at most `48 * m - 109` gates for `m ≥ 5` and at most `120 * (m + 1) + 4` gates
otherwise. -/
private theorem cor76_and_word {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (s t : Fin N)
    (hc : Set.InjOn c (Set.Iio m)) (hcs : ∀ i < m, c i ≠ s)
    (hct : ∀ i < m, c i ≠ t) (hst : s ≠ t) :
    ∃ xs : List (ReflectionGate N), reflectionLegal xs ∧
      xs.length ≤ (if 5 ≤ m then 48*m-109 else 120*(m+1)+4) ∧
      ∀ x : Reg N, Run 1 (reflectionCompile xs) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) m)) := by
  by_cases hm : 5 ≤ m
  · refine ⟨cor74Word m c s t, cor74Word_legal m c s t hm hc hcs hct hst, ?_,
      cor74Word_semantics m c s t hm hc hcs hct hst⟩
    rw [if_pos hm]
    exact (cor74Word_length m c s t hm).le
  · obtain ⟨gs, hgs, hlen, hr⟩ := noWork_single_dirty_and_table c s t m hc hcs hct hst
    refine ⟨gs, hgs, ?_, hr⟩
    rw [if_neg hm]
    exact hlen

/-- Given `V * V = U`, a legal conjunction toggle, and an `m`-controlled implementation of `V`,
constructs an `(m + 1)`-controlled implementation of `U`. The resulting length is `12 + 2 *
xs.length + rs.length`. -/
private theorem cor76_step {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (hctm : ∀ i < m, c i ≠ t) (hclast : ∀ i < m, c i ≠ c m) (hlast : c m ≠ t)
    (U V : Matrix Bool Bool ℂ) (hV : V ∈ unitaryGroup Bool ℂ) (hVV : V*V = U)
    (xs : List (ReflectionGate N)) (hxs : reflectionLegal xs)
    (hxsrun : ∀ x : Reg N, Run 1 (reflectionCompile xs) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x (c m) (x (c m) ^^ noWorkPrefixAnd (fun i => x (c i)) m)))
    (rs : List (ReflectionGate N)) (hrs : reflectionLegal rs)
    (hrsrun : ∀ (x : Reg N) (φ : QState Bool),
      Run 1 (reflectionCompile rs) (multiWireState t x φ) =
        multiWireState t x (ApplyGate
          (if noWorkPrefixAnd (fun i => x (c i)) m then V else 1) φ)) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
      gs.length = 12 + 2*xs.length + rs.length ∧
      ∀ (x : Reg N) (φ : QState Bool),
        Run 1 (reflectionCompile gs) (multiWireState t x φ) =
          multiWireState t x (ApplyGate
            (if noWorkPrefixAnd (fun i => x (c i)) (m+1) then U else 1) φ) := by
  let p := knownQubitAnglesOfUnitary V
  have hp : knownQubitUnitary p = V := (knownQubitEuler_explicit_angles_cover_unitaries V hV).1
  let padj := knownQubitAngleAdjoint p
  have hpadj : knownQubitUnitary padj = Vᴴ := by rw [knownQubitUnitary_adjoint, hp]
  let vs := multiKnownPairSteps (c m) t p
  let ds := multiKnownPairSteps (c m) t padj
  have hvs : reflectionLegal vs := multiKnownPairSteps_legal _ _ hlast p
  have hds : reflectionLegal ds := multiKnownPairSteps_legal _ _ hlast padj
  have hvlen : vs.length = 6 := rfl
  have hdlen : ds.length = 6 := rfl
  refine ⟨vs ++ xs ++ ds ++ xs ++ rs, ?_, ?_, ?_⟩
  · simp only [reflectionLegal_append]
    exact ⟨⟨⟨⟨hvs, hxs⟩, hds⟩,hxs⟩, hrs⟩
  · simp only [List.length_append, hvlen, hdlen]
    omega
  · intro x φ
    let a := noWorkPrefixAnd (fun i => x (c i)) m
    let q := Function.update x (c m) (x (c m) ^^ a)
    have hA : noWorkPrefixAnd (fun i => q (c i)) m = a :=
      and_update c m (c m) hclast x _
    have hq : q (c m) = (x (c m) ^^ a) := Function.update_self _ _ _
    have hrestore : Function.update q (c m)
        (q (c m) ^^ noWorkPrefixAnd (fun i => q (c i)) m) = x := by
      rw [hA, hq]
      simp [q]
    simp only [reflectionCompile_append, run_append]
    rw [multiKnownPairSteps_action (c m) t hlast p, hp,
      noWork_and_table_wireState c m (c m) t hlast hctm xs hxsrun,
      multiKnownPairSteps_action (c m) t hlast padj, hpadj]
    change Run 1 (reflectionCompile rs)
      (Run 1 (reflectionCompile xs)
        (multiWireState t q (ApplyGate (if q (c m) then Vᴴ else 1)
          (ApplyGate (if x (c m) then V else 1) φ)))) = _
    rw [noWork_and_table_wireState c m (c m) t hlast hctm xs hxsrun, hrestore, hrsrun, hq]
    rw [noWorkPrefixAnd_succ]
    change multiWireState t x (ApplyGate (if a then V else 1)
      (ApplyGate (if x (c m) ^^ a then Vᴴ else 1)
        (ApplyGate (if x (c m) then V else 1) φ))) =
      multiWireState t x (ApplyGate (if (a && x (c m)) then U else 1) φ)
    cases a <;> cases x (c m) <;> simp [applyGate_one]
    · rw [← applyGate_mul, show Vᴴ * V = 1 from hV.1, applyGate_one]
    · rw [← applyGate_mul, show V * Vᴴ = 1 from hV.2, applyGate_one]
    · rw [← applyGate_mul, hVV]

/-- For at most five distinct controls disjoint from the target, constructs a legal controlled
implementation of any qubit unitary using at most `120 * k * k + 140 * k + 1` gates. -/
private theorem cor76_small_table {N : ℕ} : ∀ (k : ℕ), k ≤ 5 →
    ∀ (c : ℕ → Fin N) (t : Fin N), Set.InjOn c (Set.Iio k) → (∀ i < k, c i ≠ t) →
    ∀ (U : Matrix Bool Bool ℂ), U ∈ unitaryGroup Bool ℂ →
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
      gs.length ≤ 120*k*k+140*k+1 ∧
      ∀ (x : Reg N) (φ : QState Bool),
        Run 1 (reflectionCompile gs) (multiWireState t x φ) =
          multiWireState t x (ApplyGate
            (if noWorkPrefixAnd (fun i => x (c i)) k then U else 1) φ) := by
  intro k
  induction k with
  | zero =>
    intro _ c t _ _ U hU
    refine ⟨[.inl (t, U)], ?_, by simp, ?_⟩
    · intro g hg
      obtain rfl := List.mem_singleton.mp hg
      exact hU
    · intro x φ
      simp only [reflectionCompile, List.map_cons, List.map_nil, run_gate, run_nil,
        reflectionGateMatrix]
      simpa [noWorkPrefixAnd] using! multiWireState_single t x U φ
  | succ k ih =>
    intro hk c t hc hct U hU
    obtain ⟨V, hV, hVV⟩ := noWork_unitary_square_root U hU
    have hcm : Set.InjOn c (Set.Iio k) := by
      intro i hi j hj he
      exact hc (show i < k+1 from by change i < k at hi; omega)
        (show j < k+1 from by change j < k at hj; omega) he
    have hctm : ∀ i < k, c i ≠ t := fun i hi => hct i (by omega)
    have hccl : ∀ i < k, c i ≠ c k := fun i hi he => by
      have hv : i = k := hc (show i < k+1 from by omega) (show k < k+1 from by omega) he
      omega
    have hlast : c k ≠ t := hct k (by omega)
    obtain ⟨xs, hxs, hxslen, hxsrun⟩ :=
      cor76_and_word k c t (c k) hcm hctm hccl hlast.symm
    have hxslen' : xs.length ≤ 120*(k+1)+4 := by
      rw [show (if 5 ≤ k then 48*k-109 else 120*(k+1)+4) = 120*(k+1)+4 from
        if_neg (by omega)] at hxslen
      exact hxslen
    obtain ⟨rs, hrs, hrslen, hrsrun⟩ :=
      ih (by omega) c t hcm hctm V hV
    obtain ⟨gs, hgs, hlen, hrun⟩ :=
      cor76_step k c t hctm hccl hlast U V hV hVV xs hxs hxsrun rs hrs hrsrun
    refine ⟨gs, hgs, ?_, hrun⟩
    rw [hlen]
    calc 12 + 2*xs.length + rs.length
        ≤ 12 + 2*(120*(k+1)+4) + (120*k*k+140*k+1) := by omega
      _ = 120*(k+1)*(k+1)+140*(k+1)+1 := by ring

/-- For `k ≥ 5` distinct controls disjoint from the target, constructs a legal controlled qubit
unitary with `gs.length + 254 * k ≤ 48 * k * k + 3771`. -/
private theorem cor76_sharp_table {N : ℕ} : ∀ (k : ℕ), 5 ≤ k →
    ∀ (c : ℕ → Fin N) (t : Fin N), Set.InjOn c (Set.Iio k) → (∀ i < k, c i ≠ t) →
    ∀ (U : Matrix Bool Bool ℂ), U ∈ unitaryGroup Bool ℂ →
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
      gs.length + 254*k ≤ 48*k*k + 3771 ∧
      ∀ (x : Reg N) (φ : QState Bool),
        Run 1 (reflectionCompile gs) (multiWireState t x φ) =
          multiWireState t x (ApplyGate
            (if noWorkPrefixAnd (fun i => x (c i)) k then U else 1) φ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk c t hc hct U hU
    by_cases hk5 : k = 5
    · subst hk5
      obtain ⟨gs, hgs, hlen, hrun⟩ :=
        cor76_small_table 5 (by omega) c t hc hct U hU
      exact ⟨gs, hgs, by omega, hrun⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, k = j+1 := ⟨k-1, by omega⟩
    subst hj
    have hkm : 5 ≤ j := by omega
    have hcm : Set.InjOn c (Set.Iio j) := by
      intro i hi j' hj' he
      exact hc (show i < j+1 from by change i < j at hi; omega)
        (show j' < j+1 from by change j' < j at hj'; omega) he
    have hctm : ∀ i < j, c i ≠ t := fun i hi => hct i (by omega)
    have hccl : ∀ i < j, c i ≠ c j := fun i hi he => by
      have hv : i = j := hc (show i < j+1 from by omega) (show j < j+1 from by omega) he
      omega
    have hlast : c j ≠ t := hct j (by omega)
    obtain ⟨V, hV, hVV⟩ := noWork_unitary_square_root U hU
    obtain ⟨xs, hxs, hxslen, hxsrun⟩ :=
      cor76_and_word j c t (c j) hcm hctm hccl hlast.symm
    rw [if_pos hkm] at hxslen
    obtain ⟨rs, hrs, hrslen, hrsrun⟩ :=
      ih j (by omega) hkm c t hcm hctm V hV
    obtain ⟨gs, hgs, hlen, hrun⟩ :=
      cor76_step j c t hctm hccl hlast U V hV hVV xs hxs hxsrun rs hrs hrsrun
    refine ⟨gs, hgs, ?_, hrun⟩
    rw [hlen]
    calc 12 + 2*xs.length + rs.length + 254*(j+1)
        ≤ 12 + 2*(48*j-109) + rs.length + 254*(j+1) := by omega
      _ ≤ 48*j*j + 3771 + (96*j+48) := by omega
      _ = 48*(j+1)*(j+1) + 3771 := by ring

/-- For `k ≥ 5`, constructs a legal, query-free `k`-controlled qubit unitary with `gs.length +
350 * (k + 1) ≤ 48 * (k + 1) * (k + 1) + 4073`. Its compiled gate count equals the word
length [BarencoEtAl1995]. -/
theorem cor76_sharp_control_table {N : ℕ} (k : ℕ) (hk : 5 ≤ k)
    (c : ℕ → Fin N) (t : Fin N) (hc : Set.InjOn c (Set.Iio k))
    (hct : ∀ i < k, c i ≠ t) (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
      gs.length + 350*(k+1) ≤ 48*(k+1)*(k+1) + 4073 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ (x : Reg N) (φ : QState Bool),
        Run 1 (reflectionCompile gs) (multiWireState t x φ) =
          multiWireState t x (ApplyGate
            (if noWorkPrefixAnd (fun i => x (c i)) k then U else 1) φ) := by
  obtain ⟨gs, hgs, hlen, hrun⟩ := cor76_sharp_table k hk c t hc hct U hU
  refine ⟨gs, hgs, ?_, queryCount_reflectionCompile _, gateCount_reflectionCompile _, hrun⟩
  calc gs.length + 350*(k+1)
      = gs.length + 254*k + (96*k+350) := by omega
    _ ≤ 48*k*k + 3771 + (96*k+350) := by omega
    _ = 48*(k+1)*(k+1) + 4073 := by ring

/-- Constructs a legal, query-free `k`-controlled qubit unitary using at most `48 * (k + 1) * (k
+ 1) + 3701` gates, with compiled gate count equal to word length [BarencoEtAl1995]. -/
theorem cor76_control_table {N : ℕ} (k : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (hc : Set.InjOn c (Set.Iio k)) (hct : ∀ i < k, c i ≠ t)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
      gs.length ≤ 48*(k+1)*(k+1) + 3701 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ (x : Reg N) (φ : QState Bool),
        Run 1 (reflectionCompile gs) (multiWireState t x φ) =
          multiWireState t x (ApplyGate
            (if noWorkPrefixAnd (fun i => x (c i)) k then U else 1) φ) := by
  by_cases hk : 5 ≤ k
  · obtain ⟨gs, hgs, hlen, hq, hg, hrun⟩ :=
      cor76_sharp_control_table k hk c t hc hct U hU
    refine ⟨gs, hgs, ?_, hq, hg, hrun⟩
    set q := 48*(k+1)*(k+1) with hqdef
    omega
  · obtain ⟨gs, hgs, hlen, hrun⟩ :=
      cor76_small_table k (by omega) c t hc hct U hU
    refine ⟨gs, hgs, ?_, queryCount_reflectionCompile _, gateCount_reflectionCompile _, hrun⟩
    have hk5 : k ≤ 5 := by omega
    have h1 : k*k ≤ 25 := Nat.mul_le_mul hk5 hk5
    have h2 : 120*k*k ≤ 3000 := by
      calc 120*k*k = 120*(k*k) := by ring
        _ ≤ 120*25 := Nat.mul_le_mul_left _ h1
        _ = 3000 := by norm_num
    have h3 : 140*k ≤ 700 := Nat.mul_le_mul_left _ hk5
    omega

/-- The first `k` entries of `grayControlWires t` are pairwise distinct. -/
private theorem grayControlWires_inj' {k : ℕ} (t : Fin (k+1)) :
    Set.InjOn (grayControlWires t) (Set.Iio k) := by
  intro i hi j hj he
  change i < k at hi
  change j < k at hj
  simp only [grayControlWires, dif_pos hi, dif_pos hj] at he
  exact congrArg Fin.val (Fin.succAbove_right_injective he)

/-- Each of the first `k` Gray control wires differs from the target wire. -/
private theorem grayControlWires_ne' {k : ℕ} (t : Fin (k+1)) (i : ℕ) (hi : i < k) :
    grayControlWires t i ≠ t := by
  simp only [grayControlWires, dif_pos hi]
  exact Fin.succAbove_ne t _

/-- The conjunction over the Gray control wires is true exactly when every wire other than the
target is true. -/
private theorem grayControls_true_iff' {k : ℕ} (t : Fin (k+1)) (x : Reg (k+1)) :
    noWorkPrefixAnd (fun i => x (grayControlWires t i)) k = true ↔
      ∀ w, w ≠ t → x w = true := by
  simp only [noWorkPrefixAnd, List.all_eq_true, List.mem_range]
  constructor
  · intro h w hw
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hw
    have hh := h i.val i.isLt
    simpa only [grayControlWires, dif_pos i.isLt] using! hh
  · intro h i hi
    simp only [grayControlWires, dif_pos hi]
    exact h _ (Fin.succAbove_ne t _)

/-- The two canonical Gray control addresses with opposite target bits are distinct. -/
private theorem grayControlAddress_ne' {k : ℕ} (t : Fin (k+1)) :
    grayControlAddress t false ≠ grayControlAddress t true := by
  intro h
  have hh := congrFun h t
  simp [grayControlAddress] at hh

/-- Updating the target bit of a canonical Gray control address produces the canonical address
with the new bit. -/
private theorem grayControlAddress_update' {k : ℕ} (t : Fin (k+1)) (b c : Bool) :
    Function.update (grayControlAddress t b) t c = grayControlAddress t c := by
  funext w
  by_cases hw : w = t
  · subst w
    simp [grayControlAddress]
  · simp [hw, grayControlAddress]

/-- Constructs a legal implementation of a unitary two-level block on the two canonical Gray
control addresses, using at most `48 * (k + 1) * (k + 1) + 3701` gates. -/
private theorem cor76_canonical_pair_table {k : ℕ} (t : Fin (k+1))
    (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧
      gs.length ≤ 48*(k+1)*(k+1) + 3701 ∧ ∀ ψ : QState (Reg (k+1)),
        Run 1 (reflectionCompile gs) ψ =
          twoLevelMatrix (.pair (grayControlAddress t false) (grayControlAddress t true) U) *ᵥ ψ := by
  obtain ⟨gs, hgs, hlen, _, _, hr⟩ :=
    cor76_control_table k (grayControlWires t) t (grayControlWires_inj' t)
      (fun i hi => grayControlWires_ne' t i hi) U hU
  have hk (q : Reg (k+1)) : Run 1 (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket q) =
      twoLevelMatrix (.pair (grayControlAddress t false) (grayControlAddress t true) U) *ᵥ Qatlib.Foundations.PureStateMath.Ket q := by
    have hrun := hr q (Qatlib.Foundations.PureStateMath.Ket (q t))
    rw [multiWireState_ket] at hrun
    rw [hrun, known_two_level_pair_update _ _ U (grayControlAddress_ne' t)]
    by_cases hc : noWorkPrefixAnd (fun i => q (grayControlWires t i)) k = true
    · have hq : q = grayControlAddress t (q t) := by
        funext w
        by_cases hw : w = t
        · simp [hw, grayControlAddress]
        · simp [hw, grayControlAddress, (grayControls_true_iff' t q).mp hc w hw]
      cases hb : q t
      · have hqe : q = grayControlAddress t false := by simpa only [hb] using! hq
        subst q
        rw [if_pos hc]
        simp [grayControlAddress_update', multiWireState, ApplyGate, Matrix.mulVec,
          dotProduct, Qatlib.Foundations.PureStateMath.Ket, (grayControlAddress_ne' t).symm]
        module
      · have hqe : q = grayControlAddress t true := by simpa only [hb] using! hq
        subst q
        rw [if_pos hc]
        simp [grayControlAddress_update', multiWireState, ApplyGate, Matrix.mulVec,
          dotProduct, Qatlib.Foundations.PureStateMath.Ket, grayControlAddress_ne' t]
        module
    · have hfalse : noWorkPrefixAnd (fun i => q (grayControlWires t i)) k = false :=
        Bool.eq_false_iff.mpr hc
      have hqf : q ≠ grayControlAddress t false := by
        intro he
        subst q
        apply hc
        apply (grayControls_true_iff' t _).mpr
        intro w hw
        simp [grayControlAddress, hw]
      have hqt : q ≠ grayControlAddress t true := by
        intro he
        subst q
        apply hc
        apply (grayControls_true_iff' t _).mpr
        intro w hw
        simp [grayControlAddress, hw]
      simp [hfalse, applyGate_one, Qatlib.Foundations.PureStateMath.Ket, hqf.symm, hqt.symm]
  refine ⟨gs, hgs, hlen, ?_⟩
  intro ψ
  conv_lhs => arg 3; rw [state_ket_expansion ψ]
  rw [run_reflectionCompile_sum]
  simp only [run_reflectionCompile_smul, hk]
  conv_rhs => arg 2; rw [state_ket_expansion ψ]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]

/-- Conjugating a Boolean-indexed matrix by `PauliX` negates both entry indices. -/
private theorem grayReverseBlock' (B : Matrix Bool Bool ℂ) :
    PauliX * B * PauliX = fun a b => B (!a) (!b) := by
  ext a b
  cases a <;> cases b <;> simp [PauliX, permMatrix, Matrix.mul_apply]

/-- Reversing the two selected addresses and conjugating the block by `PauliX` leaves the
two-level matrix unchanged. -/
private theorem grayPairReverse' {k : ℕ} (x y : Reg (k+1)) (hxy : x ≠ y)
    (B : Matrix Bool Bool ℂ) :
    twoLevelMatrix (.pair y x (PauliX*B*PauliX)) = twoLevelMatrix (.pair x y B) := by
  rw [grayReverseBlock']
  ext u v
  by_cases hux : u = x <;> by_cases huy : u = y <;>
    by_cases hvx : v = x <;> by_cases hvy : v = y <;>
    by_cases huv : u = v <;> simp_all [twoLevelMatrix]

/-- Constructs a legal two-level unitary on two addresses differing only at one wire, with
length at most `48 * (k + 1) * (k + 1) + 2 * k + 3701`. -/
private theorem cor76_adjacent_pair_table {k : ℕ} (x y : Reg (k+1)) (t : Fin (k+1))
    (ht : x t ≠ y t) (hother : ∀ w, w ≠ t → x w = y w)
    (B : Matrix Bool Bool ℂ) (hB : B ∈ unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧
      gs.length ≤ 48*(k+1)*(k+1) + 2*k + 3701 ∧ ∀ ψ : QState (Reg (k+1)),
        Run 1 (reflectionCompile gs) ψ = twoLevelMatrix (.pair x y B) *ᵥ ψ := by
  have hxy : x ≠ y := fun he => ht (congrFun he t)
  let as := knownAddressFlips x (grayControlAddress t (x t))
  have has : reflectionLegal as := (knownAddressFlips_spec x _).1
  have halen : as.length ≤ k := by
    simp only [as, knownAddressFlips, knownFlipSteps, List.length_map, Finset.length_toList]
    calc
      _ ≤ ((Finset.univ : Finset (Fin (k+1))).erase t).card := by
        apply Finset.card_le_card
        intro w hw
        have hne := (Finset.mem_filter.mp hw).2
        apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_univ _⟩
        intro he
        subst w
        simp [grayControlAddress] at hne
      _ = k := by simp
  let A := reflectionProgramMatrix as
  have hA : A ∈ unitaryGroup (Reg (k+1)) ℂ := reflectionProgramMatrix_unitary as has
  have hx : A *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket (grayControlAddress t (x t)) := by
    simpa only [A, run_reflectionCompile, ApplyGate] using! (knownAddressFlips_spec x _).2.2
  have hy : A *ᵥ Qatlib.Foundations.PureStateMath.Ket y = Qatlib.Foundations.PureStateMath.Ket (grayControlAddress t (y t)) := by
    change ApplyGate (reflectionProgramMatrix as) (Qatlib.Foundations.PureStateMath.Ket y) = _
    rw [← run_reflectionCompile]
    dsimp only [as]
    rw [knownAddressFlips, knownFlipSteps_action _ (Finset.nodup_toList _)]
    congr 1
    funext w
    by_cases hw : w = t
    · subst w
      simp [Finset.mem_toList, grayControlAddress]
    · simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and,
        grayControlAddress, if_neg hw, hother w hw]
      cases y w <;> simp
  let rs := reflectionAdjoint as
  have hrs : reflectionLegal rs := reflectionAdjoint_legal as has
  have hrlen : rs.length = as.length := reflectionAdjoint_length as
  have hlocal (U : Matrix Bool Bool ℂ) (hU : U ∈ unitaryGroup Bool ℂ) :
      ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧
        gs.length ≤ 48*(k+1)*(k+1) + 2*k + 3701 ∧ ∀ ψ : QState (Reg (k+1)),
          Run 1 (reflectionCompile gs) ψ =
            Aᴴ *ᵥ (twoLevelMatrix (.pair (grayControlAddress t false)
              (grayControlAddress t true) U) *ᵥ (A *ᵥ ψ)) := by
    obtain ⟨bs, hbs, hblen, hb⟩ := cor76_canonical_pair_table t U hU
    refine ⟨as ++ bs ++ rs, ?_, ?_, ?_⟩
    · simp only [reflectionLegal_append]
      exact ⟨⟨has, hbs⟩, hrs⟩
    · simp only [List.length_append, hrlen]
      omega
    · intro ψ
      rw [reflectionCompile_append, reflectionCompile_append, run_append, run_append,
        run_reflectionCompile, hb, run_reflectionCompile, reflectionAdjoint_matrix as has]
      rfl
  cases hb : x t
  · have hyb : y t = true := by cases he : y t <;> simp_all
    obtain ⟨gs, hgs, hlen, hr⟩ := hlocal B hB
    refine ⟨gs, hgs, hlen, ?_⟩
    intro ψ
    rw [hr]
    apply known_two_level_unitary_conjugate A hA x y _ _ hxy (grayControlAddress_ne' t)
    · simpa only [hb] using! hx
    · simpa only [hyb] using! hy
  · have hyb : y t = false := by cases he : y t <;> simp_all
    have hU : PauliX*B*PauliX ∈ unitaryGroup Bool ℂ :=
      (unitaryGroup Bool ℂ).mul_mem ((unitaryGroup Bool ℂ).mul_mem pauliX_unitary hB) pauliX_unitary
    obtain ⟨gs, hgs, hlen, hr⟩ := hlocal (PauliX*B*PauliX) hU
    refine ⟨gs, hgs, hlen, ?_⟩
    intro ψ
    rw [hr]
    have he := known_two_level_unitary_conjugate A hA y x _ _ hxy.symm
      (grayControlAddress_ne' t) (by simpa only [hyb] using! hy)
      (by simpa only [hb] using! hx) (PauliX*B*PauliX) ψ
    rw [he, grayPairReverse' x y hxy B]

/-- The set of differing wires of two register addresses is empty exactly when the addresses are
equal. -/
private theorem grayDifference_empty' {n : ℕ} (x y : Reg n) :
    grayDifference x y = ∅ ↔ x = y := by
  constructor
  · intro h
    funext w
    by_contra hw
    have hm : w ∈ grayDifference x y := by simp [grayDifference, hw]
    rw [h] at hm
    simp at hm
  · rintro rfl
    simp [grayDifference]

/-- A two-level `PauliX` block sends the basis vector at its first selected address to the
second. -/
private theorem graySwap_ket' {n : ℕ} (x z : Reg n) (hxz : x ≠ z) :
    twoLevelMatrix (.pair x z PauliX) *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket z := by
  rw [known_two_level_pair_update x z PauliX hxz]
  simp [Qatlib.Foundations.PureStateMath.Ket, hxz.symm, PauliX, permMatrix]

/-- A two-level `PauliX` block fixes a basis vector whose address is neither selected address. -/
private theorem graySwap_other_ket' {n : ℕ} (x z q : Reg n)
    (hxz : x ≠ z) (hqx : q ≠ x) (hqz : q ≠ z) :
    twoLevelMatrix (.pair x z PauliX) *ᵥ Qatlib.Foundations.PureStateMath.Ket q = Qatlib.Foundations.PureStateMath.Ket q := by
  rw [known_two_level_pair_update x z PauliX hxz]
  simp [Qatlib.Foundations.PureStateMath.Ket, hqx.symm, hqz.symm]

/-- Constructs a legal implementation of a unitary block on any two distinct addresses. Its
length is bounded by `2 * (grayDifference x y).card - 1` times `48 * (k + 1) * (k + 1) + 2 *
k + 3701` [BarencoEtAl1995]. -/
theorem cor76_gray_pair_table {k : ℕ} (x y : Reg (k+1)) (hxy : x ≠ y)
    (B : Matrix Bool Bool ℂ) (hB : B ∈ unitaryGroup Bool ℂ) :
    ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧
      gs.length ≤ (2*(grayDifference x y).card-1) * (48*(k+1)*(k+1)+2*k+3701) ∧
      ∀ ψ : QState (Reg (k+1)), Run 1 (reflectionCompile gs) ψ =
        twoLevelMatrix (.pair x y B) *ᵥ ψ := by
  classical
  have hgeneral (d : ℕ) : ∀ (x y : Reg (k+1)), (grayDifference x y).card = d → x ≠ y →
      ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧
        gs.length ≤ (2*d-1) * (48*(k+1)*(k+1)+2*k+3701) ∧
        ∀ ψ : QState (Reg (k+1)), Run 1 (reflectionCompile gs) ψ =
          twoLevelMatrix (.pair x y B) *ᵥ ψ := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro x y hd hxy
      have hdpos : 0 < d := by
        rw [← hd, Finset.card_pos]
        by_contra he
        apply hxy
        apply (grayDifference_empty' x y).mp
        exact Finset.not_nonempty_iff_eq_empty.mp he
      obtain ⟨t, ht⟩ : ∃ t, x t ≠ y t := by
        by_contra he
        push Not at he
        exact hxy (funext he)
      have htm : t ∈ grayDifference x y := by simp [grayDifference, ht]
      by_cases hd1 : d = 1
      · have hsingle : grayDifference x y = {t} := by
          obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (hd.trans hd1)
          have htw : t = w := by simpa only [hw, Finset.mem_singleton] using! htm
          simpa only [← htw] using! hw
        have hother : ∀ w, w ≠ t → x w = y w := by
          intro w hw
          by_contra he
          have hm : w ∈ grayDifference x y := by simp [grayDifference, he]
          rw [hsingle] at hm
          exact hw (Finset.mem_singleton.mp hm)
        obtain ⟨gs, hgs, hlen, hr⟩ := cor76_adjacent_pair_table x y t ht hother B hB
        refine ⟨gs, hgs, ?_, hr⟩
        simpa only [hd1, Nat.reduceMul, Nat.reduceSub, one_mul] using! hlen
      · let z := Function.update x t (y t)
        have hzcard : (grayDifference z y).card = d-1 := by
          rw [grayDifference_update, Finset.card_erase_of_mem htm, hd]
        have hzy : z ≠ y := by
          intro he
          have hempty := (grayDifference_empty' z y).mpr he
          rw [hempty, Finset.card_empty] at hzcard
          omega
        have hxz : x ≠ z := by
          intro he
          have het := congrFun he t
          simp only [z, Function.update_self] at het
          exact ht het
        obtain ⟨as, has, halen, ha⟩ := cor76_adjacent_pair_table x z t
          (by simpa only [z, Function.update_self] using! ht)
          (fun w hw => by simp [z, hw]) PauliX pauliX_unitary
        obtain ⟨bs, hbs, hblen, hb⟩ := ih (d-1) (by omega) z y hzcard hzy
        let rs := reflectionAdjoint as
        have hrs : reflectionLegal rs := reflectionAdjoint_legal as has
        have hrlen : rs.length = as.length := reflectionAdjoint_length as
        let A := reflectionProgramMatrix as
        have hA : A ∈ unitaryGroup (Reg (k+1)) ℂ := reflectionProgramMatrix_unitary as has
        have hx : A *ᵥ Qatlib.Foundations.PureStateMath.Ket x = Qatlib.Foundations.PureStateMath.Ket z := by
          have hh :=
              (ha (Qatlib.Foundations.PureStateMath.Ket x)).trans (graySwap_ket' x z hxz)
          simpa only [A, run_reflectionCompile, ApplyGate] using! hh
        have hy : A *ᵥ Qatlib.Foundations.PureStateMath.Ket y = Qatlib.Foundations.PureStateMath.Ket y := by
          have hh :=
              (ha (Qatlib.Foundations.PureStateMath.Ket y)).trans
              (graySwap_other_ket' x z y hxz hxy.symm hzy.symm)
          simpa only [A, run_reflectionCompile, ApplyGate] using! hh
        refine ⟨as ++ bs ++ rs, ?_, ?_, ?_⟩
        · simp only [reflectionLegal_append]
          exact ⟨⟨has, hbs⟩, hrs⟩
        · simp only [List.length_append, hrlen]
          calc
            _ ≤ (48*(k+1)*(k+1)+2*k+3701) + (2*(d-1)-1)*(48*(k+1)*(k+1)+2*k+3701) +
                (48*(k+1)*(k+1)+2*k+3701) := add_le_add (add_le_add halen hblen) halen
            _ = ((2*(d-1)-1)+2)*(48*(k+1)*(k+1)+2*k+3701) := by ring
            _ = _ := by congr 1; omega
        · intro ψ
          rw [reflectionCompile_append, reflectionCompile_append, run_append, run_append,
            run_reflectionCompile, hb, run_reflectionCompile, reflectionAdjoint_matrix as has]
          exact known_two_level_unitary_conjugate A hA x y z y hxy hzy hx hy B ψ
  exact hgeneral _ x y rfl hxy

/-- Constructs a legal phase operation at one register address, using at most `48 * (k + 1) * (k
+ 1) + 2 * k + 3701` gates. -/
theorem cor76_gray_phase_table {k : ℕ} (x : Reg (k+1)) (z : ℂ) (hz : star z*z = 1) :
    ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧
      gs.length ≤ 48*(k+1)*(k+1) + 2*k + 3701 ∧ ∀ ψ : QState (Reg (k+1)),
        Run 1 (reflectionCompile gs) ψ = twoLevelMatrix (.phase x z) *ᵥ ψ := by
  let t := Fin.last k
  let y := Function.update x t (!(x t))
  have ht : x t ≠ y t := by simp [y]
  have hother : ∀ w, w ≠ t → x w = y w := by
    intro w hw
    simp [y, hw]
  have hxy : x ≠ y := fun he => ht (congrFun he t)
  let B : Matrix Bool Bool ℂ := Matrix.diagonal (fun b => if b then 1 else z)
  have hB : B ∈ unitaryGroup Bool ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    change (starRingEnd ℂ) z*z = 1 at hz
    ext a b
    cases a <;> cases b <;> simp [B, Matrix.mul_apply, hz]
  obtain ⟨gs, hgs, hlen, hr⟩ := cor76_adjacent_pair_table x y t ht hother B hB
  have hmat : twoLevelMatrix (.pair x y B) = twoLevelMatrix (.phase x z) := by
    ext u v
    by_cases hux : u = x <;> by_cases huy : u = y <;>
      by_cases hvx : v = x <;> by_cases hvy : v = y <;>
      by_cases huv : u = v <;> simp_all [twoLevelMatrix, B]
  exact ⟨gs, hgs, hlen, fun ψ => (hr ψ).trans (congrArg (fun A => A *ᵥ ψ) hmat)⟩

/-- For `n ≥ 1`, every legal two-level instruction has a legal, query-free implementation with
at most `(2 * n - 1) * (48 * n * n + 2 * n + 3699)` gates [Barenco et al., Section
8][BarencoEtAl1995]. -/
theorem cor76_section8_gray_two_level (n : ℕ) (hn : 1 ≤ n)
    (g : TwoLevelInstruction (Reg n)) (hg : twoLevelLegal g) :
    ∃ gs : List (ReflectionGate n), reflectionLegal gs ∧
      gs.length ≤ (2*n-1) * (48*n*n+2*n+3699) ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n), Run 1 (reflectionCompile gs) ψ = twoLevelMatrix g *ᵥ ψ := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k+1 := ⟨n-1, by omega⟩
  have hcost : 48*(k+1)*(k+1) + 2*k + 3701 = 48*(k+1)*(k+1)+2*(k+1)+3699 := by omega
  have hlocal : ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧
      gs.length ≤ (2*(k+1)-1)*(48*(k+1)*(k+1)+2*(k+1)+3699) ∧
      ∀ ψ : QState (Reg (k+1)), Run 1 (reflectionCompile gs) ψ = twoLevelMatrix g *ᵥ ψ := by
    cases g with
    | pair x y B =>
      obtain ⟨gs, hgs, hlen, hr⟩ := cor76_gray_pair_table x y hg.1 B hg.2
      refine ⟨gs, hgs, hlen.trans ?_, hr⟩
      rw [hcost]
      apply Nat.mul_le_mul_right
      apply Nat.sub_le_sub_right
      apply Nat.mul_le_mul_left
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
    | phase x z =>
      obtain ⟨gs, hgs, hlen, hr⟩ := cor76_gray_phase_table x z hg
      refine ⟨gs, hgs, hlen.trans ?_, hr⟩
      rw [hcost]
      exact Nat.le_mul_of_pos_left _ (by omega : 1 ≤ 2*(k+1)-1)
  obtain ⟨gs, hgs, hlen, hr⟩ := hlocal
  exact ⟨gs, hgs, hlen, queryCount_reflectionCompile _, gateCount_reflectionCompile _, hr⟩

/-- For `n ≥ 1`, every `n`-qubit unitary has an exact legal, query-free implementation with at
most `2 ^ (n - 1) * (2 ^ n + 1) * ((2 * n - 1) * (48 * n * n + 2 * n + 3699))` gates
[Barenco et al., Section 8][BarencoEtAl1995]. -/
theorem cor76_section8_gray_universality (n : ℕ) (hn : 1 ≤ n)
    (U : Matrix (Reg n) (Reg n) ℂ) (hU : U ∈ unitaryGroup (Reg n) ℂ) :
    ∃ gs : List (ReflectionGate n), reflectionLegal gs ∧
      gs.length ≤ 2^(n-1)*(2^n+1)*((2*n-1)*(48*n*n+2*n+3699)) ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n),
        Run 1 (reflectionCompile gs) ψ = U *ᵥ ψ := by
  let C := (2*n-1)*(48*n*n+2*n+3699)
  obtain ⟨ts, hts, hlen, hprog⟩ := known_unitary_two_level_factorization (Reg n) U hU
  have hcount : ts.length ≤ 2^(n-1)*(2^n+1) := by
    have hc : Fintype.card (Reg n) = 2^n := by simp [Reg]
    rw [hc] at hlen
    have hp : 2^n = 2^(n-1)*2 := by
      conv_lhs => rw [show n = (n-1)+1 by omega, pow_succ]
    have he : 2^n*(2^n+1)/2 = 2^(n-1)*(2^n+1) := by
      calc
        _ = (2^(n-1)*(2^n+1)*2)/2 := by congr 1; rw [hp]; ring
        _ = _ := Nat.mul_div_cancel _ (by decide : 0 < 2)
    exact hlen.trans_eq he
  obtain ⟨gs, hgs, hglen, hr⟩ := noWork_program_table_of_instruction_tables n C ts hts (by
    intro g _ hg
    obtain ⟨as, has, halen, _, _, ha⟩ := cor76_section8_gray_two_level n hn g hg
    exact ⟨as, has, halen, ha⟩)
  refine ⟨gs, hgs, ?_, queryCount_reflectionCompile _, gateCount_reflectionCompile _, ?_⟩
  · exact hglen.trans ((Nat.mul_le_mul_left C hcount).trans_eq (Nat.mul_comm _ _))
  · intro ψ
    rw [hr, hprog]

/-- For `n ≥ 2`, rewrites `4 ^ n ≤ 9 * r + 3 * n + 1` as the integer lower bound `(4 ^ n - 3 * n
- 1 + 8) / 9 ≤ r`. -/
theorem barenco_generic_length_threshold (n r : ℕ) (hn : 2 ≤ n) :
    4^n ≤ 9*r + 3*n + 1 ↔ (4^n - 3*n - 1 + 8) / 9 ≤ r := by
  have h4 : 16 ≤ 4^n := by
    calc 16 = 4^2 := by norm_num
      _ ≤ 4^n := Nat.pow_le_pow_right (by norm_num) hn
  omega

/-- For `n ≤ 1`, the integer threshold `(4 ^ n - 3 * n - 1 + 8) / 9` is at most one. -/
theorem barenco_dimension_threshold_degenerate (n : ℕ) (hn : n ≤ 1) :
    (4^n - 3*n - 1 + 8) / 9 ≤ 1 := by
  have : n = 0 ∨ n = 1 := by omega
  rcases this with rfl | rfl <;> norm_num

section B2Smooth

open scoped ComplexConjugate ENNReal

/-- The Pauli X matrix indexed by `Fin 2`. -/
def b2X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli Y matrix indexed by `Fin 2`. -/
def b2Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli Z matrix indexed by `Fin 2`. -/
def b2Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The matrix `b2X` is Hermitian. -/
theorem b2X_herm : b2Xᴴ = b2X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b2X, Matrix.conjTranspose_apply]

/-- The matrix `b2Y` is Hermitian. -/
theorem b2Y_herm : b2Yᴴ = b2Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b2Y, Matrix.conjTranspose_apply]

/-- The matrix `b2Z` is Hermitian. -/
theorem b2Z_herm : b2Zᴴ = b2Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b2Z, Matrix.conjTranspose_apply]

/-- The square of `b2X` is the identity matrix. -/
theorem b2X_sq : b2X * b2X = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, b2X, Fin.sum_univ_two, Matrix.of_apply]

/-- The square of `b2Y` is the identity matrix. -/
theorem b2Y_sq : b2Y * b2Y = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, b2Y, Fin.sum_univ_two, Matrix.of_apply]

/-- The square of `b2Z` is the identity matrix. -/
theorem b2Z_sq : b2Z * b2Z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, b2Z, Fin.sum_univ_two, Matrix.of_apply]

/-- The tensor product of two `Fin 2` matrices, indexed by pairs of qubit indices. -/
def b2Tensor (u v : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => u p.1 q.1 * v p.2 q.2

/-- The tensor product of two matrices that square to the identity also squares to the identity. -/
theorem b2Tensor_sq (u v : Matrix (Fin 2) (Fin 2) ℂ) (hu : u * u = 1) (hv : v * v = 1) :
    b2Tensor u v * b2Tensor u v = 1 := by
  ext p q
  simp only [Matrix.mul_apply, b2Tensor, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  show (∑ x : Fin 2, ∑ y : Fin 2, (u p.1 x * v p.2 y) * (u x q.1 * v y q.2))
      = if p = q then 1 else 0
  have hreg : ∀ x y : Fin 2,
      (u p.1 x * v p.2 y) * (u x q.1 * v y q.2) = (u p.1 x * u x q.1) * (v p.2 y * v y q.2) :=
    fun x y => by ring
  simp only [hreg]
  have hu' : ∀ x y : Fin 2, (∑ k, u x k * u k y) = if x = y then 1 else 0 := fun x y => by
    have h := congrFun (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M x) hu) y
    simpa [Matrix.mul_apply, Matrix.one_apply] using! h
  have hv' : ∀ x y : Fin 2, (∑ k, v x k * v k y) = if x = y then 1 else 0 := fun x y => by
    have h := congrFun (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M x) hv) y
    simpa [Matrix.mul_apply, Matrix.one_apply] using! h
  rw [← Finset.sum_mul_sum, hu', hv']
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
    simp [h1, h2, Prod.ext_iff]

/-- The tensor product of two Hermitian matrices is Hermitian. -/
theorem b2Tensor_herm (u v : Matrix (Fin 2) (Fin 2) ℂ) (hu : uᴴ = u) (hv : vᴴ = v) :
    (b2Tensor u v)ᴴ = b2Tensor u v := by
  ext p q
  have huS : ∀ i j : Fin 2, star (u i j) = u j i := by
    intro i j
    rw [show star (u i j) = uᴴ j i from (Matrix.conjTranspose_apply u i j).symm, hu]
  have hvS : ∀ i j : Fin 2, star (v i j) = v j i := by
    intro i j
    rw [show star (v i j) = vᴴ j i from (Matrix.conjTranspose_apply v i j).symm, hv]
  simp only [b2Tensor, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul, huS, hvS]
  ring

/-- Complex conjugation sends `exp (I * t)` to `exp (-I * t)` for real `t`. -/
private theorem conj_exp_I (t : ℝ) :
    conj (Complex.exp (Complex.I * (t : ℂ))) = Complex.exp (-Complex.I * (t : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_I, Complex.conj_ofReal]

/-- The product of the complex exponentials of `x` and `-x` is one. -/
private theorem exp_add_neg (x : ℂ) : Complex.exp x * Complex.exp (-x) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- The product of two copies of the norm of `exp (I * t)` is one for real `t`. -/
private theorem norm_exp_I_sq (t : ℝ) :
    ‖Complex.exp (Complex.I * (t : ℂ))‖ * ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
  have h1 : Complex.exp (Complex.I * (t : ℂ)) * conj (Complex.exp (Complex.I * (t : ℂ))) = 1 := by
    rw [conj_exp_I, show -Complex.I * (t : ℂ) = -(Complex.I * (t : ℂ)) from by ring,
      ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h3 : Complex.normSq (Complex.exp (Complex.I * (t : ℂ))) = 1 := by
    have h2 : ((Complex.normSq (Complex.exp (Complex.I * (t : ℂ))) : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self, mul_comm]
      exact h1
    simpa using! Complex.ofReal_inj.mp h2
  rw [← pow_two, ← Complex.normSq_eq_norm_sq]
  exact h3

/-- If the squared norms of `w` and `x` sum to one, the matrix with rows `(w, x)` and `(-conj x,
conj w)` belongs to the special unitary group. -/
private theorem su2_form_mem {w x : ℂ} (h : ‖w‖ * ‖w‖ + ‖x‖ * ‖x‖ = 1) :
    !![w, x; -conj x, conj w] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  have hz : ∀ z : ℂ, z * conj z = ((‖z‖ * ‖z‖ : ℝ) : ℂ) := fun z => by
    rw [mul_comm z (conj z), ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, pow_two]
  have hz' : ∀ z : ℂ, conj z * z = ((‖z‖ * ‖z‖ : ℝ) : ℂ) := fun z => by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, pow_two]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Matrix.one_apply, Matrix.of_apply, map_mul, map_neg,
        starRingEnd_self_apply, Matrix.cons_val_zero', Matrix.cons_val_one,
        Matrix.cons_val_succ', Matrix.head_cons]
    · norm_num
      simp only [hz]
      push_cast
      exact_mod_cast h
    · norm_num
      ring
    · norm_num
      ring
    · norm_num
      simp only [hz']
      push_cast
      exact_mod_cast (by linarith [h])
  · rw [Matrix.det_fin_two_of,
      show w * conj w - x * -(conj x) = w * conj w + x * conj x from by ring, hz w, hz x]
    push_cast
    exact_mod_cast (by linarith [h])

/-- The three-angle parametrization of a special unitary qubit matrix using complex phases and
real sine and cosine. -/
def su2Euler (α β γ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (Complex.I*(α+γ)) * Real.cos β,
     Complex.exp (Complex.I*(α-γ)) * Real.sin β;
     -Complex.exp (Complex.I*(γ-α)) * Real.sin β,
     Complex.exp (-Complex.I*(α+γ)) * Real.cos β]

/-- Every matrix `su2Euler α β γ` belongs to the special unitary group. -/
theorem su2Euler_mem_specialUnitary (α β γ : ℝ) :
    su2Euler α β γ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hnorm1 : ∀ t : ℝ, ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
    intro t
    have hn2 := norm_exp_I_sq t
    have hnn := norm_nonneg (Complex.exp (Complex.I * (t : ℂ)))
    nlinarith [hnn, hn2]
  have habs2 : ∀ r : ℝ, |r| * |r| = r * r := fun r => by rw [← abs_mul, abs_mul_self]
  have hform : su2Euler α β γ =
      !![Complex.exp (Complex.I * ((α : ℂ) + (γ : ℂ))) * ((Real.cos β : ℂ)),
         Complex.exp (Complex.I * ((α : ℂ) - (γ : ℂ))) * ((Real.sin β : ℂ));
         -conj (Complex.exp (Complex.I * ((α : ℂ) - (γ : ℂ))) * ((Real.sin β : ℂ))),
         conj (Complex.exp (Complex.I * ((α : ℂ) + (γ : ℂ))) * ((Real.cos β : ℂ)))] := by
    have hAG : Complex.I * ((α : ℂ) + (γ : ℂ)) = Complex.I * (((α + γ : ℝ) : ℂ)) := by
      push_cast
      ring
    have hSG : Complex.I * ((α : ℂ) - (γ : ℂ)) = Complex.I * (((α - γ : ℝ) : ℂ)) := by
      push_cast
      ring
    have hGS : Complex.I * ((γ : ℂ) - (α : ℂ)) = -Complex.I * (((α - γ : ℝ) : ℂ)) := by
      push_cast
      ring
    have hNA2 : Complex.exp (-Complex.I * ((α : ℂ) + (γ : ℂ)))
        = Complex.exp (-Complex.I * (((α + γ : ℝ) : ℂ))) := by
      congr 1
      push_cast
      ring
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [su2Euler, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_one,
        Matrix.cons_val_succ', Matrix.head_cons]
    all_goals
      first
      | rfl
      | rw [hSG, map_mul, conj_exp_I, Complex.conj_ofReal, hGS]
      | rw [hAG, map_mul, conj_exp_I, Complex.conj_ofReal, hNA2]
    all_goals try ring
  rw [hform]
  refine su2_form_mem (w := Complex.exp (Complex.I * ((α : ℂ) + (γ : ℂ))) * ((Real.cos β : ℂ)))
    (x := Complex.exp (Complex.I * ((α : ℂ) - (γ : ℂ))) * ((Real.sin β : ℂ))) ?_
  rw [show Complex.I * ((α : ℂ) + (γ : ℂ)) = Complex.I * (((α + γ : ℝ) : ℂ)) from by
        push_cast; ring,
    show Complex.I * ((α : ℂ) - (γ : ℂ)) = Complex.I * (((α - γ : ℝ) : ℂ)) from by
        push_cast; ring,
    Complex.norm_mul, Complex.norm_mul, hnorm1 (α + γ), hnorm1 (α - γ), one_mul, one_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, habs2, habs2]
  rw [← pow_two (Real.cos β), ← pow_two (Real.sin β)]
  linarith [Real.sin_sq_add_cos_sq β]

/-- The matrix `cos t • 1 + (I * sin t) • W`. -/
def trigM (t : ℝ) (W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((Real.cos t : ℂ)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    + (Complex.I * ((Real.sin t : ℂ))) • W

/-- The trigonometric matrix `trigM t W` is unitary whenever `W` is Hermitian and squares to the
identity. -/
private theorem trigM_mem_unitary (t : ℝ) (W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hW2 : W * W = 1) (hWh : Wᴴ = W) :
    trigM t W ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have hstar : (trigM t W)ᴴ
      = ((Real.cos t : ℂ)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
        - (Complex.I * ((Real.sin t : ℂ))) • W := by
    rw [trigM, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hWh, star_mul,
      show Star.star ((Real.cos t : ℂ)) = starRingEnd ℂ ((Real.cos t : ℂ)) from rfl,
      show Star.star ((Real.sin t : ℂ)) = starRingEnd ℂ ((Real.sin t : ℂ)) from rfl,
      show Star.star Complex.I = starRingEnd ℂ Complex.I from rfl,
      Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
      show ((Real.sin t : ℂ)) * (-Complex.I) = -(Complex.I * ((Real.sin t : ℂ))) from by ring,
      neg_smul, sub_eq_add_neg]
  have h11 : ((Real.cos t : ℂ)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
        * ((Real.cos t : ℂ)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      = (((Real.cos t : ℂ)) * ((Real.cos t : ℂ))) •
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  have h1W : ((Real.cos t : ℂ)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
        * (Complex.I * ((Real.sin t : ℂ))) • W
      = (((Real.cos t : ℂ)) * (Complex.I * ((Real.sin t : ℂ)))) • W := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  have hW1 : (Complex.I * ((Real.sin t : ℂ))) • W
        * ((Real.cos t : ℂ)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      = ((Complex.I * ((Real.sin t : ℂ))) * ((Real.cos t : ℂ))) • W := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  have hWW : (Complex.I * ((Real.sin t : ℂ))) • W * (Complex.I * ((Real.sin t : ℂ))) • W
      = ((Complex.I * ((Real.sin t : ℂ))) * (Complex.I * ((Real.sin t : ℂ)))) •
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hW2, smul_smul]
  have hcs : ((Real.cos t : ℂ)) * ((Real.cos t : ℂ))
      - (Complex.I * ((Real.sin t : ℂ))) * (Complex.I * ((Real.sin t : ℂ))) = 1 := by
    have hII : (Complex.I * ((Real.sin t : ℂ))) * (Complex.I * ((Real.sin t : ℂ)))
        = -(((Real.sin t : ℂ)) * ((Real.sin t : ℂ))) := by
      rw [show (Complex.I * ((Real.sin t : ℂ))) * (Complex.I * ((Real.sin t : ℂ)))
            = (Complex.I * Complex.I) * (((Real.sin t : ℂ)) * ((Real.sin t : ℂ))) from by
          ring,
        Complex.I_mul_I, neg_one_mul]
    rw [hII, sub_neg_eq_add]
    push_cast
    rw [show Complex.cos (t : ℂ) * Complex.cos (t : ℂ) + Complex.sin (t : ℂ) * Complex.sin (t : ℂ)
          = ((Real.cos t * Real.cos t + Real.sin t * Real.sin t : ℝ) : ℂ) from by
        push_cast
        ring,
      show Real.cos t * Real.cos t + Real.sin t * Real.sin t = 1 from by
        rw [← pow_two, ← pow_two]; linarith [Real.sin_sq_add_cos_sq t]]
    norm_num
  rw [hstar, trigM, mul_sub, add_mul, add_mul, h11, h1W, hW1, hWW,
    sub_add_eq_sub_sub,
    mul_comm (Complex.I * ((Real.sin t : ℂ))) ((Real.cos t : ℂ)),
    add_sub_cancel_right, ← sub_smul, hcs, one_smul]

/-- The product of the three trigonometric factors generated by the tensor squares of Pauli X,
Y, and Z. -/
def canonicalPair (a b c : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  trigM a (b2Tensor b2X b2X) * trigM b (b2Tensor b2Y b2Y) * trigM c (b2Tensor b2Z b2Z)

/-- Every matrix in the three-parameter family `canonicalPair` is unitary. -/
theorem canonicalPair_mem_unitary (a b c : ℝ) :
    canonicalPair a b c ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  have h1 := trigM_mem_unitary a (b2Tensor b2X b2X)
    (b2Tensor_sq b2X b2X b2X_sq b2X_sq) (b2Tensor_herm b2X b2X b2X_herm b2X_herm)
  have h2 := trigM_mem_unitary b (b2Tensor b2Y b2Y)
    (b2Tensor_sq b2Y b2Y b2Y_sq b2Y_sq) (b2Tensor_herm b2Y b2Y b2Y_herm b2Y_herm)
  have h3 := trigM_mem_unitary c (b2Tensor b2Z b2Z)
    (b2Tensor_sq b2Z b2Z b2Z_sq b2Z_sq) (b2Tensor_herm b2Z b2Z b2Z_herm b2Z_herm)
  have h12 := (Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ).mul_mem h1 h2
  exact (Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ).mul_mem h12 h3

/-- Matrix multiplication expressed as a finite sum on functions of two indices. -/
noncomputable def matMulFn {I : Type*} [Fintype I] (f g : I → I → ℂ) : I → I → ℂ :=
  fun x y => ∑ z, f x z * g z y

/-- The identity matrix entry function, equal to one on equal indices and zero otherwise. -/
def oneFn {I : Type*} [DecidableEq I] (x y : I) : ℂ := if x = y then 1 else 0

/-- The entry function of `su2Euler` with its three real angles bundled into a tuple. -/
def su2EulerFn (p : ℝ × ℝ × ℝ) : Fin 2 → Fin 2 → ℂ :=
  fun i j => su2Euler p.1 p.2.1 p.2.2 i j

/-- Evaluating a smooth function with values in a finite doubly indexed function space at fixed
indices preserves smoothness. -/
private theorem contDiff_apply2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α β : Type*} [Fintype α] [Fintype β] (f : E → α → β → ℂ)
    (hf : ContDiff ℝ ⊤ f) (x : α) (y : β) :
    ContDiff ℝ ⊤ fun p => f p x y :=
  contDiff_pi.1 ((contDiff_pi.1 hf) x) y

/-- Multiplying two smooth families of finite matrix entry functions yields a smooth family. -/
private theorem contDiff_matmul_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type*} [Fintype I] {f g : E → I → I → ℂ}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) :
    ContDiff ℝ ⊤ fun p => matMulFn (f p) (g p) := by
  refine contDiff_pi' fun x => contDiff_pi' fun y => ?_
  exact ContDiff.sum fun z _ =>
    ContDiff.mul (contDiff_apply2 f hf x z) (contDiff_apply2 g hg z y)

/-- The complex-valued coercion of a smooth real function is smooth. -/
private theorem contDiff_ofReal_real (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ fun t => ((f t : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

/-- The Euler matrix entry function depends smoothly on its three real parameters. -/
theorem su2EulerFn_contDiff :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ => su2EulerFn p) := by
  have hα : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ => p.1) := contDiff_fst
  have hβ : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ => p.2.1) := contDiff_fst.comp contDiff_snd
  have hγ : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ => p.2.2) := contDiff_snd.comp contDiff_snd
  have hcos : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ => ((Real.cos p.2.1 : ℂ))) :=
    (contDiff_ofReal_real Real.cos Real.contDiff_cos).comp hβ
  have hsin : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ => ((Real.sin p.2.1 : ℂ))) :=
    (contDiff_ofReal_real Real.sin Real.contDiff_sin).comp hβ
  have hαC : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ => ((p.1 : ℂ))) :=
    Complex.ofRealCLM.contDiff.comp hα
  have hγC : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ => ((p.2.2 : ℂ))) :=
    Complex.ofRealCLM.contDiff.comp hγ
  refine contDiff_pi' fun i => contDiff_pi' fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [su2EulerFn, su2Euler, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.head_cons]
  all_goals
    first
    | exact (ContDiff.cexp (contDiff_const.mul (hαC.add hγC))).mul hcos
    | exact (ContDiff.cexp (contDiff_const.mul (hαC.sub hγC))).mul hsin
    | exact ((ContDiff.cexp (contDiff_const.mul (hγC.sub hαC))).neg).mul hsin
    | exact (ContDiff.cexp (contDiff_const.neg.mul (hαC.add hγC))).mul hcos

/-- Embeds a qubit matrix entry function on one register wire, with entries zero unless all
other wires agree. -/
def singleWireGateFn {n : ℕ} (a : Fin n) (u : Fin 2 → Fin 2 → ℂ) :
    (Fin n → Fin 2) → (Fin n → Fin 2) → ℂ :=
  fun x y => if (∀ i, i ≠ a → y i = x i) then u (x a) (y a) else 0

/-- Embeds a matrix entry function on a pair of wires, with entries zero unless all wires
outside the pair agree. -/
def wirePairGateFn {n : ℕ} (a b : Fin n) (U : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → ℂ) :
    (Fin n → Fin 2) → (Fin n → Fin 2) → ℂ :=
  fun x y => if (∀ i, i ≠ a → i ≠ b → y i = x i) then U (x a, x b) (y a, y b) else 0

/-- The entry function of the scalar matrix with global phase `exp (I * φ)`. -/
def phaseGateFn {n : ℕ} (φ : ℝ) : (Fin n → Fin 2) → (Fin n → Fin 2) → ℂ :=
  fun x y => if x = y then Complex.exp (Complex.I * φ) else 0

/-- The entry-function form of the product defining `canonicalPair`, using `matMulFn`. -/
def canonicalPairFn (a b c : ℝ) : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → ℂ :=
  matMulFn (matMulFn (fun x y => trigM a (b2Tensor b2X b2X) x y)
      (fun x y => trigM b (b2Tensor b2Y b2Y) x y))
    (fun x y => trigM c (b2Tensor b2Z b2Z) x y)

/-- The entry-function and matrix definitions of `canonicalPair` agree at every pair of indices. -/
theorem canonicalPairFn_eq (a b c : ℝ) (x y : Fin 2 × Fin 2) :
    canonicalPairFn a b c x y = canonicalPair a b c x y := by
  simp [canonicalPairFn, canonicalPair, matMulFn, Matrix.mul_apply]

/-- The nine-parameter two-qubit block formed by a tensor product of two Euler matrices followed
by `canonicalPair`. -/
def gateBlockFn (t : Fin 9 → ℝ) : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → ℂ :=
  matMulFn
    (fun x y => su2EulerFn (t ⟨0, by decide⟩, (t ⟨1, by decide⟩, t ⟨2, by decide⟩)) x.1 y.1
      * su2EulerFn (t ⟨3, by decide⟩, (t ⟨4, by decide⟩, t ⟨5, by decide⟩)) x.2 y.2)
    (canonicalPairFn (t ⟨6, by decide⟩) (t ⟨7, by decide⟩) (t ⟨8, by decide⟩))

/-- The product of one Euler gate on each wire, with a separate triple of angles for each wire. -/
def localLayerFn {n : ℕ} (θ : Fin n → ℝ × ℝ × ℝ) :
    (Fin n → Fin 2) → (Fin n → Fin 2) → ℂ :=
  (List.finRange n).foldl
    (fun acc i => matMulFn acc (singleWireGateFn i (su2EulerFn (θ i)))) oneFn

/-- The circuit entry function formed from a global phase, a local Euler layer, and
nine-parameter blocks on the listed wire pairs. -/
def kakCircuitFn {n : ℕ} (wires : List (Fin n × Fin n))
    (p : ℝ × (Fin n → ℝ × ℝ × ℝ) × (Fin wires.length → Fin 9 → ℝ)) :
    (Fin n → Fin 2) → (Fin n → Fin 2) → ℂ :=
  matMulFn (phaseGateFn p.1)
    (matMulFn (localLayerFn p.2.1)
      ((List.finRange wires.length).foldl (fun acc k =>
        matMulFn acc (wirePairGateFn (wires.get k).1 (wires.get k).2
          (gateBlockFn (p.2.2 k)))) oneFn))

/-- Each entry of the global phase gate is smooth when its real phase parameter varies smoothly. -/
private theorem contDiff_phaseGate {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ ⊤ f) (x y : Fin n → Fin 2) :
    ContDiff ℝ ⊤ (fun p => phaseGateFn (f p) x y) := by
  by_cases hxy : x = y
  · simp only [phaseGateFn, if_pos hxy]
    exact ContDiff.cexp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hf))
  · simp only [phaseGateFn, if_neg hxy]
    exact contDiff_const

/-- Each entry of an embedded single-wire gate varies smoothly with a smooth family of qubit
matrices. -/
private theorem contDiff_singleWire {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Fin n) (g : E → Fin 2 → Fin 2 → ℂ) (hg : ContDiff ℝ ⊤ g)
    (x y : Fin n → Fin 2) :
    ContDiff ℝ ⊤ (fun p => singleWireGateFn a (g p) x y) := by
  by_cases hcond : ∀ i, i ≠ a → y i = x i
  · simp only [singleWireGateFn, if_pos hcond]
    exact contDiff_apply2 g hg _ _
  · simp only [singleWireGateFn, if_neg hcond]
    exact contDiff_const

/-- Each entry of an embedded two-wire gate varies smoothly with a smooth family of two-qubit
matrices. -/
private theorem contDiff_wirePair {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : Fin n) (G : E → (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → ℂ)
    (hG : ContDiff ℝ ⊤ G) (x y : Fin n → Fin 2) :
    ContDiff ℝ ⊤ (fun p => wirePairGateFn a b (G p) x y) := by
  by_cases hcond : ∀ i, i ≠ a → i ≠ b → y i = x i
  · simp only [wirePairGateFn, if_pos hcond]
    exact contDiff_apply2 G hG _ _
  · simp only [wirePairGateFn, if_neg hcond]
    exact contDiff_const

/-- Each entry of `trigM` varies smoothly when its real angle varies smoothly. -/
private theorem trigM_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ ⊤ f)
    (W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (x y : Fin 2 × Fin 2) :
    ContDiff ℝ ⊤ (fun p => trigM (f p) W x y) := by
  simp only [trigM, smul_eq_mul, Matrix.one_apply]
  exact (((contDiff_ofReal_real Real.cos Real.contDiff_cos).comp hf).mul
      contDiff_const).add
    ((contDiff_const.mul
        ((contDiff_ofReal_real Real.sin Real.contDiff_sin).comp hf)).mul contDiff_const)

/-- The family `canonicalPairFn` varies smoothly with three smooth real parameter functions. -/
private theorem canonicalPairFn_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (fa fb fc : E → ℝ) (ha : ContDiff ℝ ⊤ fa) (hb : ContDiff ℝ ⊤ fb)
    (hc : ContDiff ℝ ⊤ fc) :
    ContDiff ℝ ⊤ (fun p : E => canonicalPairFn (fa p) (fb p) (fc p)) := by
  have hgate : ∀ (f : E → ℝ) (hf : ContDiff ℝ ⊤ f)
      (W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
      ContDiff ℝ ⊤ (fun p : E => (fun x y => trigM (f p) W x y)) :=
    fun f hf W => contDiff_pi' fun x => contDiff_pi' fun y => trigM_contDiff f hf W x y
  exact contDiff_matmul_entry (contDiff_matmul_entry (hgate fa ha _) (hgate fb hb _))
    (hgate fc hc _)

/-- The nine-parameter block entry function varies smoothly with any smooth choice of its
parameters. -/
private theorem gateBlockFn_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : E → Fin 9 → ℝ) (ht : ContDiff ℝ ⊤ t) :
    ContDiff ℝ ⊤ (fun p : E => gateBlockFn (t p)) := by
  have htk : ∀ k : Fin 9, ContDiff ℝ ⊤ (fun p : E => t p k) := fun k =>
    contDiff_pi.1 ht k
  have hE1 : ContDiff ℝ ⊤ (fun p : E => su2EulerFn
      (t p ⟨0, by decide⟩, (t p ⟨1, by decide⟩, t p ⟨2, by decide⟩))) :=
    su2EulerFn_contDiff.comp
      ((htk ⟨0, by decide⟩).prodMk ((htk ⟨1, by decide⟩).prodMk (htk ⟨2, by decide⟩)))
  have hE2 : ContDiff ℝ ⊤ (fun p : E => su2EulerFn
      (t p ⟨3, by decide⟩, (t p ⟨4, by decide⟩, t p ⟨5, by decide⟩))) :=
    su2EulerFn_contDiff.comp
      ((htk ⟨3, by decide⟩).prodMk ((htk ⟨4, by decide⟩).prodMk (htk ⟨5, by decide⟩)))
  have htens : ContDiff ℝ ⊤ (fun p : E => (fun x y : Fin 2 × Fin 2 =>
      su2EulerFn (t p ⟨0, by decide⟩, (t p ⟨1, by decide⟩, t p ⟨2, by decide⟩)) x.1 y.1
      * su2EulerFn (t p ⟨3, by decide⟩, (t p ⟨4, by decide⟩, t p ⟨5, by decide⟩)) x.2 y.2)) := by
    refine contDiff_pi' fun x => contDiff_pi' fun y => ?_
    exact (contDiff_apply2 _ hE1 x.1 y.1).mul (contDiff_apply2 _ hE2 x.2 y.2)
  have hcan : ContDiff ℝ ⊤ (fun p : E =>
      canonicalPairFn (t p ⟨6, by decide⟩) (t p ⟨7, by decide⟩) (t p ⟨8, by decide⟩)) :=
    canonicalPairFn_contDiff _ _ _ (htk ⟨6, by decide⟩) (htk ⟨7, by decide⟩)
      (htk ⟨8, by decide⟩)
  exact contDiff_matmul_entry htens hcan

/-- A finite ordered product of smooth matrix families, starting from a smooth initial matrix,
is smooth. -/
private theorem contDiff_gateChainFin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type*} [Fintype I] {r : ℕ}
    (gate : E → Fin r → I → I → ℂ) (hgate : ContDiff ℝ ⊤ gate)
    (B : E → I → I → ℂ) (hB : ContDiff ℝ ⊤ B) :
    ContDiff ℝ ⊤ (fun p => (List.finRange r).foldl
      (fun acc k => matMulFn acc (gate p k)) (B p)) := by
  have hind : ∀ (l : List (Fin r)) (B : E → I → I → ℂ) (hB : ContDiff ℝ ⊤ B),
      ContDiff ℝ ⊤ (fun p => l.foldl (fun acc k => matMulFn acc (gate p k)) (B p)) := by
    intro l
    induction l with
    | nil => intro B hB; exact hB
    | cons k rest ih =>
        intro C hC
        show ContDiff ℝ ⊤ (fun p => rest.foldl (fun acc k => matMulFn acc (gate p k))
          (matMulFn (C p) (gate p k)))
        exact ih (fun p => matMulFn (C p) (gate p k))
          (contDiff_matmul_entry hC (contDiff_pi.1 hgate k))
  exact hind (List.finRange r) B hB

/-- The local Euler layer varies smoothly with a smooth family of wire-angle triples. -/
private theorem localLayerFn_contDiff {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (θ : E → Fin n → ℝ × ℝ × ℝ) (hθ : ContDiff ℝ ⊤ θ) :
    ContDiff ℝ ⊤ (fun p => localLayerFn (θ p)) := by
  refine contDiff_gateChainFin
    (fun p i => singleWireGateFn i (su2EulerFn (θ p i))) ?_ (fun _ => oneFn) contDiff_const
  refine contDiff_pi' fun i => contDiff_pi' fun x => contDiff_pi' fun y => ?_
  exact contDiff_singleWire (n := n) (E := E) i (fun p => su2EulerFn (θ p i))
    (su2EulerFn_contDiff.comp (contDiff_pi.1 hθ i)) x y

/-- The circuit expression with nine-parameter blocks is smooth when its global phase, local
angles, and block parameters vary smoothly. -/
private theorem kakCircuitFn_contDiff_aux {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (wires : List (Fin n × Fin n))
    (φ : E → ℝ) (hφ' : ContDiff ℝ ⊤ φ)
    (θ : E → Fin n → ℝ × ℝ × ℝ) (hθ : ContDiff ℝ ⊤ θ)
    (t : E → Fin wires.length → Fin 9 → ℝ) (ht : ContDiff ℝ ⊤ t) :
    ContDiff ℝ ⊤ (fun p : E => matMulFn (phaseGateFn (n := n) (φ p))
      (matMulFn (localLayerFn (θ p))
        ((List.finRange wires.length).foldl (fun acc k =>
          matMulFn acc (wirePairGateFn (wires.get k).1 (wires.get k).2
            (gateBlockFn (t p k)))) oneFn))) := by
  have hφ : ContDiff ℝ ⊤ (fun p : E => phaseGateFn (n := n) (φ p)) := by
    refine contDiff_pi' fun x => contDiff_pi' fun y => ?_
    exact contDiff_phaseGate φ hφ' x y
  have hL : ContDiff ℝ ⊤ (fun p : E => localLayerFn (θ p)) := localLayerFn_contDiff θ hθ
  have hR : ContDiff ℝ ⊤ (fun p : E => (List.finRange wires.length).foldl
      (fun acc k => matMulFn acc (wirePairGateFn (wires.get k).1 (wires.get k).2
        (gateBlockFn (t p k)))) oneFn) := by
    have hB1 : ContDiff ℝ ⊤ (fun _ : E =>
        (oneFn : (Fin n → Fin 2) → (Fin n → Fin 2) → ℂ)) := contDiff_const
    refine contDiff_gateChainFin
      (fun p k => wirePairGateFn (wires.get k).1 (wires.get k).2 (gateBlockFn (t p k))) ?_
      (fun _ => (oneFn : (Fin n → Fin 2) → (Fin n → Fin 2) → ℂ)) hB1
    refine contDiff_pi' fun k => contDiff_pi' fun x => contDiff_pi' fun y => ?_
    exact contDiff_wirePair (n := n) (E := E) _ _
      (fun p => gateBlockFn (t p k)) (gateBlockFn_contDiff _ (contDiff_pi.1 ht k)) x y
  exact contDiff_matmul_entry hφ (contDiff_matmul_entry hL hR)

set_option maxHeartbeats 2000000 in

/-- For a fixed list of wire pairs, the entry function `kakCircuitFn` is smooth in all its real
parameters. -/
theorem kakCircuitFn_contDiff {n : ℕ} (wires : List (Fin n × Fin n)) :
    ContDiff ℝ ⊤ (fun p : ℝ × (Fin n → ℝ × ℝ × ℝ) × (Fin wires.length → Fin 9 → ℝ) =>
      kakCircuitFn wires p) :=
  kakCircuitFn_contDiff_aux wires _ contDiff_fst _
    (contDiff_fst.comp contDiff_snd) _ (contDiff_snd.comp contDiff_snd)

/-- The real parameter space for `r` nine-parameter blocks and an `n`-wire local layer with
global phase has dimension `9 * r + 3 * n + 1`. -/
private theorem finrank_kakParam {n : ℕ} (r : ℕ) :
    Module.finrank ℝ (ℝ × (Fin n → ℝ × ℝ × ℝ) × (Fin r → Fin 9 → ℝ))
      = 9 * r + 3 * n + 1 := by
  simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self,
    Fintype.card_fin, Finset.card_univ, Finset.sum_const, smul_eq_mul]
  omega

/-- The range of the nine-parameter circuit family for a fixed wire list has Hausdorff dimension
at most `9 * wires.length + 3 * n + 1`. -/
theorem barenco_kakForm_dimH_le {n : ℕ} (wires : List (Fin n × Fin n)) :
    dimH (Set.range (kakCircuitFn wires)) ≤ ((9 * wires.length + 3 * n + 1 : ℕ) : ℝ≥0∞) := by
  have h1 := ((kakCircuitFn_contDiff wires).of_le le_top).dimH_range_le
  rw [finrank_kakParam] at h1
  exact h1

/-- If a target set has Hausdorff dimension at least `4 ^ n` and the nine-parameter circuit
bound is smaller, some target lies outside the range of `kakCircuitFn`. -/
theorem barenco_existential_target_outside {n : ℕ} (wires : List (Fin n × Fin n))
    (A : Set ((Fin n → Fin 2) → (Fin n → Fin 2) → ℂ))
    (hA : ((4 ^ n : ℕ) : ℝ≥0∞) ≤ dimH A)
    (hcard : ((9 * wires.length + 3 * n + 1 : ℕ) : ℝ≥0∞) < ((4 ^ n : ℕ) : ℝ≥0∞)) :
    ∃ V, V ∈ A ∧ V ∉ Set.range (kakCircuitFn wires) := by
  by_contra hcon
  push_neg at hcon
  have h1 := barenco_kakForm_dimH_le wires
  have h2 : ((4 ^ n : ℕ) : ℝ≥0∞) ≤ ((9 * wires.length + 3 * n + 1 : ℕ) : ℝ≥0∞) :=
    hA.trans ((dimH_mono fun v hv => hcon v hv).trans h1)
  exact (lt_irrefl _ (lt_of_le_of_lt h2 hcard)).elim

/-- For `n ≥ 2`, a fixed wire list below the integer nine-parameter threshold misses some
element of any target set with Hausdorff dimension at least `4 ^ n`. -/
theorem barenco_existential_target_outside_of_threshold {n : ℕ} (hn : 2 ≤ n)
    (wires : List (Fin n × Fin n))
    (hlen : wires.length < (4 ^ n - 3 * n - 1 + 8) / 9)
    (A : Set ((Fin n → Fin 2) → (Fin n → Fin 2) → ℂ))
    (hA : ((4 ^ n : ℕ) : ℝ≥0∞) ≤ dimH A) :
    ∃ V, V ∈ A ∧ V ∉ Set.range (kakCircuitFn wires) :=
  barenco_existential_target_outside wires A hA (by
    exact_mod_cast (barenco_dimension_threshold n wires.length hn).2 hlen)

/-- A nonzero complex number is its norm times the complex exponential of its argument. -/
private theorem exp_I_mul_arg_mul_norm (z : ℂ) (hz : z ≠ 0) :
    Complex.exp (Complex.I * ((Complex.arg z : ℂ))) * ((‖z‖ : ℂ)) = z := by
  have h1 : Complex.exp (Complex.I * ((Complex.arg z : ℂ)))
      = Complex.exp (((Complex.arg z : ℂ)) * Complex.I) := by
    congr 1
    ring
  rw [h1, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- The conjugate of a nonzero complex number is its norm times the complex exponential of the
negative of its argument. -/
private theorem exp_negI_mul_arg_mul_norm (z : ℂ) (hz : z ≠ 0) :
    Complex.exp (-Complex.I * ((Complex.arg z : ℂ))) * ((‖z‖ : ℂ)) = conj z := by
  have h0 := exp_I_mul_arg_mul_norm z hz
  have hc : conj (Complex.exp (Complex.I * ((Complex.arg z : ℂ))))
      = Complex.exp (-Complex.I * ((Complex.arg z : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [starRingEnd_apply, star_mul]
    rw [show Star.star (Complex.I : ℂ) = -Complex.I from Complex.conj_I,
      show Star.star (((z.arg : ℝ) : ℂ)) = ((z.arg : ℝ) : ℂ) from Complex.conj_ofReal z.arg]
    ring
  rw [← hc]
  calc conj (Complex.exp (Complex.I * ((Complex.arg z : ℂ)))) * ((‖z‖ : ℂ))
      = conj (Complex.exp (Complex.I * ((Complex.arg z : ℂ))) * ((‖z‖ : ℝ) : ℂ)) := by
        rw [map_mul, Complex.conj_ofReal]
    _ = conj z := congrArg conj h0

/-- Every special unitary qubit matrix equals `su2Euler α β γ` for some real angles. -/
theorem su2Euler_surjective (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ α β γ : ℝ, su2Euler α β γ = U := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff,
    Matrix.star_eq_conjTranspose] at hU
  obtain ⟨hUU, hdet⟩ := hU
  have hdetne : IsUnit U.det := by rw [hdet]; exact isUnit_one
  have hinvmul := Matrix.nonsing_inv_mul U hdetne
  have hUH : Uᴴ = U⁻¹ := by
    calc Uᴴ = (U⁻¹ * U) * Uᴴ := by rw [hinvmul, Matrix.one_mul]
      _ = U⁻¹ * (U * Uᴴ) := Matrix.mul_assoc U⁻¹ U Uᴴ
      _ = U⁻¹ := by rw [hUU, Matrix.mul_one]
  have hadj : U⁻¹ = U.adjugate := by
    rw [Matrix.inv_def, hdet]
    simp
  have h11 : U 1 1 = conj (U 0 0) := by
    have h1 : star (U 1 1) = U 0 0 := by
      have h2 : Uᴴ 1 1 = U.adjugate 1 1 := by rw [hUH, hadj]
      rw [Matrix.conjTranspose_apply] at h2
      simp only [Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val_zero',
        Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.head_cons] at h2
      exact h2
    calc U 1 1 = star (star (U 1 1)) := (star_star _).symm
      _ = star (U 0 0) := by rw [h1]
      _ = conj (U 0 0) := rfl
  have h01 : U 0 1 = -conj (U 1 0) := by
    have h1 : conj (U 1 0) = -U 0 1 := by
      have h2 : Uᴴ 0 1 = U.adjugate 0 1 := by rw [hUH, hadj]
      rw [Matrix.conjTranspose_apply] at h2
      simp only [Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val_zero',
        Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.head_cons] at h2
      exact h2
    rw [h1]
    ring
  have h10 : U 1 0 = -conj (U 0 1) := by
    have hs := congrArg conj h01
    rw [map_neg, Complex.conj_conj] at hs
    calc U 1 0 = -(-(U 1 0)) := (neg_neg _).symm
      _ = -conj (U 0 1) := by rw [← hs]
  have hdet2 : (U 0 0) * (U 1 1) - (U 0 1) * (U 1 0) = 1 := by
    rw [← Matrix.det_fin_two U, hdet]
  have hsqR : Complex.normSq (U 0 0) + Complex.normSq (U 0 1) = 1 := by
    have h9 : U 0 0 * conj (U 0 0) + U 0 1 * conj (U 0 1) = (1 : ℂ) := by
      have h8 := hdet2
      rw [h11, h10,
        show U 0 1 * (-(conj (U 0 1))) = -((U 0 1) * conj (U 0 1)) from by ring,
        sub_neg_eq_add] at h8
      exact h8
    have h9' : ((Complex.normSq (U 0 0) + Complex.normSq (U 0 1) : ℝ) : ℂ) = (1 : ℂ) := by
      push_cast
      rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self,
        mul_comm (conj (U 0 0)) (U 0 0), mul_comm (conj (U 0 1)) (U 0 1)]
      exact h9
    exact_mod_cast h9'
  have hnale1 : (‖U 0 0‖ : ℝ) ≤ 1 := by
    have h9 := hsqR
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h9
    nlinarith [norm_nonneg (U 0 0)]
  set β : ℝ := Real.arccos (‖U 0 0‖) with hβdef
  have hcosβ : Real.cos β = ‖U 0 0‖ :=
    Real.cos_arccos (le_trans (by norm_num : (-1 : ℝ) ≤ 0) (norm_nonneg _)) hnale1
  have hsinβ : Real.sin β = ‖U 0 1‖ := by
    have h1 := Real.sin_arccos (‖U 0 0‖)
    rw [h1]
    have h2 : (‖U 0 1‖ : ℝ) * ‖U 0 1‖ = 1 - (‖U 0 0‖) * (‖U 0 0‖) := by
      have h3 := hsqR
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h3
      linarith
    rw [← pow_two, ← pow_two] at h2
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  rcases eq_or_ne (U 0 1) 0 with hb0 | hb0
  · have hane : (U 0 0) ≠ 0 := by
      intro h0
      have hnb0 : Complex.normSq (U 0 1) = 0 := by rw [hb0]; simp
      have hna0 : Complex.normSq (U 0 0) = 0 := by rw [h0]; simp
      rw [hna0, hnb0] at hsqR
      simp at hsqR
    have hnb0' : (‖U 0 1‖ : ℝ) = 0 := by rw [hb0]; simp
    have hna1 : (‖U 0 0‖ : ℝ) = 1 := by
      have h3 := hsqR
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h3
      have h4 : Complex.normSq (U 0 1) = 0 := by rw [hb0]; simp
      rw [Complex.normSq_eq_norm_sq] at h4
      nlinarith [h3, h4, norm_nonneg (U 0 0)]
    have hsin0 : Real.sin β = 0 := by rw [hsinβ, hnb0']
    have h10' : U 1 0 = 0 := by rw [h10, hb0]; simp
    have hA : ((Complex.arg (U 0 0) : ℝ) : ℂ) + ((0 : ℝ) : ℂ)
        = ((Complex.arg (U 0 0) : ℝ) : ℂ) := by push_cast; ring
    have hB : ((Complex.arg (U 0 0) : ℝ) : ℂ) - ((0 : ℝ) : ℂ)
        = ((Complex.arg (U 0 0) : ℝ) : ℂ) := by push_cast; ring
    have hC : ((0 : ℝ) : ℂ) - ((Complex.arg (U 0 0) : ℝ) : ℂ)
        = -((Complex.arg (U 0 0) : ℝ) : ℂ) := by push_cast; ring
    refine ⟨Complex.arg (U 0 0), β, 0, ?_⟩
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · simp only [su2Euler, Matrix.of_apply, Matrix.cons_val_zero',
        Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.head_cons]
      rw [hA, hcosβ]
      exact exp_I_mul_arg_mul_norm (U 0 0) hane
    · simp only [su2Euler, Matrix.of_apply, Matrix.cons_val_zero',
        Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.head_cons]
      rw [hB, hsin0]
      simp
      exact hb0.symm
    · simp only [su2Euler, Matrix.of_apply, Matrix.cons_val_zero',
        Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.head_cons]
      rw [hC, hsin0]
      simp
      exact h10'.symm
    · simp only [su2Euler, Matrix.of_apply, Matrix.cons_val_zero',
        Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.head_cons]
      show Complex.exp (-Complex.I * (((Complex.arg (U 0 0) : ℝ) : ℂ)
          + ((0 : ℝ) : ℂ))) * ((Real.cos β : ℝ) : ℂ) = U 1 1
      rw [hA, hcosβ, hna1]
      have he : Complex.exp (-Complex.I * ((Complex.arg (U 0 0) : ℝ) : ℂ)) * ((1 : ℝ) : ℂ)
          = conj (U 0 0) := by
        have hz := exp_negI_mul_arg_mul_norm (U 0 0) hane
        rw [hna1] at hz
        exact hz
      rw [he, h11]
  · rcases eq_or_ne (U 0 0) 0 with ha0 | ha0
    · have hnb1 : (‖U 0 1‖ : ℝ) = 1 := by
        have h3 := hsqR
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h3
        have h4 : Complex.normSq (U 0 0) = 0 := by rw [ha0]; simp
        rw [Complex.normSq_eq_norm_sq] at h4
        nlinarith [h3, h4, norm_nonneg (U 0 1)]
      have hcos0 : Real.cos β = 0 := by rw [hcosβ, ha0]; simp
      have h11' : U 1 1 = 0 := by rw [h11, ha0]; simp
      have hA : ((Complex.arg (U 0 1) : ℝ) : ℂ) + ((0 : ℝ) : ℂ)
          = ((Complex.arg (U 0 1) : ℝ) : ℂ) := by push_cast; ring
      have hB : ((Complex.arg (U 0 1) : ℝ) : ℂ) - ((0 : ℝ) : ℂ)
          = ((Complex.arg (U 0 1) : ℝ) : ℂ) := by push_cast; ring
      have hC : ((0 : ℝ) : ℂ) - ((Complex.arg (U 0 1) : ℝ) : ℂ)
          = -((Complex.arg (U 0 1) : ℝ) : ℂ) := by push_cast; ring
      have hD : Complex.I * (-((Complex.arg (U 0 1) : ℝ) : ℂ))
          = -Complex.I * ((Complex.arg (U 0 1) : ℝ) : ℂ) := by ring
      refine ⟨Complex.arg (U 0 1), β, 0, ?_⟩
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j
      · simp only [su2Euler, Matrix.of_apply, Matrix.cons_val_zero',
          Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.head_cons]
        rw [hA, hcos0]
        simp
        exact ha0.symm
      · simp only [su2Euler, Matrix.of_apply, Matrix.cons_val_zero',
          Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.head_cons]
        rw [hB, hsinβ]
        exact exp_I_mul_arg_mul_norm (U 0 1) hb0
      · simp only [su2Euler, Matrix.of_apply, Matrix.cons_val_zero',
          Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.head_cons]
        rw [hC, hD, hsinβ]
        show -Complex.exp (-Complex.I * ((Complex.arg (U 0 1) : ℝ) : ℂ))
            * ((‖U 0 1‖ : ℝ) : ℂ) = U 1 0
        rw [h10, neg_mul]
        exact congrArg Neg.neg (exp_negI_mul_arg_mul_norm (U 0 1) hb0)
      · simp only [su2Euler, Matrix.of_apply, Matrix.cons_val_zero',
          Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.head_cons]
        rw [hA, hcos0]
        simp
        exact h11'.symm
    · refine ⟨(Complex.arg (U 0 0) + Complex.arg (U 0 1)) / 2, β,
        (Complex.arg (U 0 0) - Complex.arg (U 0 1)) / 2, ?_⟩
      have hAC : (((Complex.arg (U 0 0) + Complex.arg (U 0 1)) / 2 : ℝ) : ℂ)
          + (((Complex.arg (U 0 0) - Complex.arg (U 0 1)) / 2 : ℝ) : ℂ)
          = ((Complex.arg (U 0 0) : ℝ) : ℂ) := by
        push_cast
        ring
      have hBC : (((Complex.arg (U 0 0) + Complex.arg (U 0 1)) / 2 : ℝ) : ℂ)
          - (((Complex.arg (U 0 0) - Complex.arg (U 0 1)) / 2 : ℝ) : ℂ)
          = ((Complex.arg (U 0 1) : ℝ) : ℂ) := by
        push_cast
        ring
      have hNC : (((Complex.arg (U 0 0) - Complex.arg (U 0 1)) / 2 : ℝ) : ℂ)
          - (((Complex.arg (U 0 0) + Complex.arg (U 0 1)) / 2 : ℝ) : ℂ)
          = -((Complex.arg (U 0 1) : ℝ) : ℂ) := by
        push_cast
        ring
      have hD : Complex.I * (-((Complex.arg (U 0 1) : ℝ) : ℂ))
          = -Complex.I * ((Complex.arg (U 0 1) : ℝ) : ℂ) := by ring
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j
      · simp only [su2Euler, Matrix.of_apply, Matrix.cons_val_zero',
          Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.head_cons]
        rw [hAC, hcosβ]
        exact exp_I_mul_arg_mul_norm (U 0 0) ha0
      · simp only [su2Euler, Matrix.of_apply, Matrix.cons_val_zero',
          Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.head_cons]
        rw [hBC, hsinβ]
        exact exp_I_mul_arg_mul_norm (U 0 1) hb0
      · simp only [su2Euler, Matrix.of_apply, Matrix.cons_val_zero',
          Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.head_cons]
        rw [hNC, hD, hsinβ]
        show -Complex.exp (-Complex.I * ((Complex.arg (U 0 1) : ℝ) : ℂ))
            * ((‖U 0 1‖ : ℝ) : ℂ) = U 1 0
        rw [h10, neg_mul]
        exact congrArg Neg.neg (exp_negI_mul_arg_mul_norm (U 0 1) hb0)
      · simp only [su2Euler, Matrix.of_apply, Matrix.cons_val_zero',
          Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.head_cons]
        show Complex.exp (-Complex.I * ((((Complex.arg (U 0 0) + Complex.arg (U 0 1)) / 2 : ℝ) : ℂ)
            + (((Complex.arg (U 0 0) - Complex.arg (U 0 1)) / 2 : ℝ) : ℂ)))
            * ((Real.cos β : ℝ) : ℂ) = U 1 1
        rw [hAC, hcosβ, h11]
        exact exp_negI_mul_arg_mul_norm (U 0 0) ha0

/-- Every Euler qubit matrix is unitary. -/
theorem su2Euler_mem_unitary (α β γ : ℝ) :
    su2Euler α β γ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have h := su2Euler_mem_specialUnitary α β γ
  have h2 : su2Euler α β γ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ (su2Euler α β γ).det = 1 :=
    Matrix.mem_specialUnitaryGroup_iff.mp h
  exact h2.1

/-- The Euler matrix at three zero angles is the identity. -/
theorem su2Euler_zero : su2Euler 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [su2Euler, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.one_apply]
  all_goals norm_num

/-- The canonical two-qubit matrix at three zero parameters is the identity. -/
theorem canonicalPair_zero : canonicalPair 0 0 0 = 1 := by
  have h0 : ∀ W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, trigM 0 W = 1 := by
    intro W
    simp [trigM]
  rw [canonicalPair, h0, h0, h0, Matrix.one_mul, Matrix.mul_one]

/-- The tensor product of two qubit identity matrices is the two-qubit identity. -/
theorem b2Tensor_one : b2Tensor (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 = 1 := by
  ext p q
  simp only [b2Tensor, Matrix.of_apply, Matrix.one_apply]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
    simp [h1, h2, Prod.ext_iff]

/-- The tensor product of two unitary qubit matrices is unitary. -/
theorem b2Tensor_mem_unitary {u v : Matrix (Fin 2) (Fin 2) ℂ}
    (hu : u ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hv : v ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    b2Tensor u v ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker_mem_unitary hu hv

/-- The fifteen-parameter two-qubit block formed by a canonical Pauli interaction between two
local Euler tensor factors. -/
def gateBlockFull (t : Fin 15 → ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  b2Tensor (su2Euler (t ⟨0, by decide⟩) (t ⟨1, by decide⟩) (t ⟨2, by decide⟩))
      (su2Euler (t ⟨3, by decide⟩) (t ⟨4, by decide⟩) (t ⟨5, by decide⟩))
    * canonicalPair (t ⟨6, by decide⟩) (t ⟨7, by decide⟩) (t ⟨8, by decide⟩)
    * b2Tensor (su2Euler (t ⟨9, by decide⟩) (t ⟨10, by decide⟩) (t ⟨11, by decide⟩))
      (su2Euler (t ⟨12, by decide⟩) (t ⟨13, by decide⟩) (t ⟨14, by decide⟩))

/-- Every fifteen-parameter block `gateBlockFull t` is unitary. -/
theorem gateBlockFull_mem_unitary (t : Fin 15 → ℝ) :
    gateBlockFull t ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  have hAB := b2Tensor_mem_unitary
    (su2Euler_mem_unitary (t ⟨0, by decide⟩) (t ⟨1, by decide⟩) (t ⟨2, by decide⟩))
    (su2Euler_mem_unitary (t ⟨3, by decide⟩) (t ⟨4, by decide⟩) (t ⟨5, by decide⟩))
  have hDE := b2Tensor_mem_unitary
    (su2Euler_mem_unitary (t ⟨9, by decide⟩) (t ⟨10, by decide⟩) (t ⟨11, by decide⟩))
    (su2Euler_mem_unitary (t ⟨12, by decide⟩) (t ⟨13, by decide⟩) (t ⟨14, by decide⟩))
  have hC := canonicalPair_mem_unitary (t ⟨6, by decide⟩) (t ⟨7, by decide⟩) (t ⟨8, by decide⟩)
  exact (Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ).mul_mem hAB hC) hDE

/-- The fifteen-parameter block with all parameters zero is the identity. -/
theorem gateBlockFull_zero : gateBlockFull (fun _ => 0) = 1 := by
  show b2Tensor (su2Euler 0 0 0) (su2Euler 0 0 0) * canonicalPair 0 0 0
      * b2Tensor (su2Euler 0 0 0) (su2Euler 0 0 0) = 1
  rw [su2Euler_zero, canonicalPair_zero, b2Tensor_one, Matrix.one_mul, Matrix.mul_one]

/-- The entry-function form of the fifteen-parameter block, expressed with `matMulFn`. -/
def gateBlockFullFn (t : Fin 15 → ℝ) : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → ℂ :=
  matMulFn
    (matMulFn
      (fun x y => su2EulerFn (t ⟨0, by decide⟩, (t ⟨1, by decide⟩, t ⟨2, by decide⟩)) x.1 y.1
        * su2EulerFn (t ⟨3, by decide⟩, (t ⟨4, by decide⟩, t ⟨5, by decide⟩)) x.2 y.2)
      (canonicalPairFn (t ⟨6, by decide⟩) (t ⟨7, by decide⟩) (t ⟨8, by decide⟩)))
    (fun x y => su2EulerFn (t ⟨9, by decide⟩, (t ⟨10, by decide⟩, t ⟨11, by decide⟩)) x.1 y.1
      * su2EulerFn (t ⟨12, by decide⟩, (t ⟨13, by decide⟩, t ⟨14, by decide⟩)) x.2 y.2)

/-- The entry-function and matrix definitions of the fifteen-parameter block agree at every pair
of indices. -/
theorem gateBlockFullFn_eq (t : Fin 15 → ℝ) (x y : Fin 2 × Fin 2) :
    gateBlockFullFn t x y = gateBlockFull t x y := by
  simp only [gateBlockFullFn, gateBlockFull, matMulFn, Matrix.mul_apply, canonicalPairFn_eq,
    b2Tensor, Matrix.of_apply, su2EulerFn]

/-- The fifteen-parameter block entry function varies smoothly with any smooth choice of
parameters. -/
private theorem gateBlockFullFn_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : E → Fin 15 → ℝ) (ht : ContDiff ℝ ⊤ t) :
    ContDiff ℝ ⊤ (fun p : E => gateBlockFullFn (t p)) := by
  have htk : ∀ k : Fin 15, ContDiff ℝ ⊤ (fun p : E => t p k) := fun k =>
    contDiff_pi.1 ht k
  have hE1 : ContDiff ℝ ⊤ (fun p : E => su2EulerFn
      (t p ⟨0, by decide⟩, (t p ⟨1, by decide⟩, t p ⟨2, by decide⟩))) :=
    su2EulerFn_contDiff.comp
      ((htk ⟨0, by decide⟩).prodMk ((htk ⟨1, by decide⟩).prodMk (htk ⟨2, by decide⟩)))
  have hE2 : ContDiff ℝ ⊤ (fun p : E => su2EulerFn
      (t p ⟨3, by decide⟩, (t p ⟨4, by decide⟩, t p ⟨5, by decide⟩))) :=
    su2EulerFn_contDiff.comp
      ((htk ⟨3, by decide⟩).prodMk ((htk ⟨4, by decide⟩).prodMk (htk ⟨5, by decide⟩)))
  have hE3 : ContDiff ℝ ⊤ (fun p : E => su2EulerFn
      (t p ⟨9, by decide⟩, (t p ⟨10, by decide⟩, t p ⟨11, by decide⟩))) :=
    su2EulerFn_contDiff.comp
      ((htk ⟨9, by decide⟩).prodMk ((htk ⟨10, by decide⟩).prodMk (htk ⟨11, by decide⟩)))
  have hE4 : ContDiff ℝ ⊤ (fun p : E => su2EulerFn
      (t p ⟨12, by decide⟩, (t p ⟨13, by decide⟩, t p ⟨14, by decide⟩))) :=
    su2EulerFn_contDiff.comp
      ((htk ⟨12, by decide⟩).prodMk ((htk ⟨13, by decide⟩).prodMk (htk ⟨14, by decide⟩)))
  have htens1 : ContDiff ℝ ⊤ (fun p : E => (fun x y : Fin 2 × Fin 2 =>
      su2EulerFn (t p ⟨0, by decide⟩, (t p ⟨1, by decide⟩, t p ⟨2, by decide⟩)) x.1 y.1
      * su2EulerFn (t p ⟨3, by decide⟩, (t p ⟨4, by decide⟩, t p ⟨5, by decide⟩)) x.2 y.2)) := by
    refine contDiff_pi' fun x => contDiff_pi' fun y => ?_
    exact (contDiff_apply2 _ hE1 x.1 y.1).mul (contDiff_apply2 _ hE2 x.2 y.2)
  have htens2 : ContDiff ℝ ⊤ (fun p : E => (fun x y : Fin 2 × Fin 2 =>
      su2EulerFn (t p ⟨9, by decide⟩, (t p ⟨10, by decide⟩, t p ⟨11, by decide⟩)) x.1 y.1
      * su2EulerFn (t p ⟨12, by decide⟩, (t p ⟨13, by decide⟩, t p ⟨14, by decide⟩)) x.2 y.2)) := by
    refine contDiff_pi' fun x => contDiff_pi' fun y => ?_
    exact (contDiff_apply2 _ hE3 x.1 y.1).mul (contDiff_apply2 _ hE4 x.2 y.2)
  have hcan : ContDiff ℝ ⊤ (fun p : E =>
      canonicalPairFn (t p ⟨6, by decide⟩) (t p ⟨7, by decide⟩) (t p ⟨8, by decide⟩)) :=
    canonicalPairFn_contDiff _ _ _ (htk ⟨6, by decide⟩) (htk ⟨7, by decide⟩)
      (htk ⟨8, by decide⟩)
  exact contDiff_matmul_entry (contDiff_matmul_entry htens1 hcan) htens2

/-- The circuit entry function formed from a global phase, a local Euler layer, and
fifteen-parameter blocks on the listed wire pairs. -/
def kakCircuitFullFn {n : ℕ} (wires : List (Fin n × Fin n))
    (p : ℝ × (Fin n → ℝ × ℝ × ℝ) × (Fin wires.length → Fin 15 → ℝ)) :
    (Fin n → Fin 2) → (Fin n → Fin 2) → ℂ :=
  matMulFn (phaseGateFn p.1)
    (matMulFn (localLayerFn p.2.1)
      ((List.finRange wires.length).foldl (fun acc k =>
        matMulFn acc (wirePairGateFn (wires.get k).1 (wires.get k).2
          (gateBlockFullFn (p.2.2 k)))) oneFn))

/-- The circuit expression with fifteen-parameter blocks is smooth when its global phase, local
angles, and block parameters vary smoothly. -/
private theorem kakCircuitFullFn_contDiff_aux {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (wires : List (Fin n × Fin n))
    (φ : E → ℝ) (hφ' : ContDiff ℝ ⊤ φ)
    (θ : E → Fin n → ℝ × ℝ × ℝ) (hθ : ContDiff ℝ ⊤ θ)
    (t : E → Fin wires.length → Fin 15 → ℝ) (ht : ContDiff ℝ ⊤ t) :
    ContDiff ℝ ⊤ (fun p : E => matMulFn (phaseGateFn (n := n) (φ p))
      (matMulFn (localLayerFn (θ p))
        ((List.finRange wires.length).foldl (fun acc k =>
          matMulFn acc (wirePairGateFn (wires.get k).1 (wires.get k).2
            (gateBlockFullFn (t p k)))) oneFn))) := by
  have hφ : ContDiff ℝ ⊤ (fun p : E => phaseGateFn (n := n) (φ p)) := by
    refine contDiff_pi' fun x => contDiff_pi' fun y => ?_
    exact contDiff_phaseGate φ hφ' x y
  have hL : ContDiff ℝ ⊤ (fun p : E => localLayerFn (θ p)) := localLayerFn_contDiff θ hθ
  have hR : ContDiff ℝ ⊤ (fun p : E => (List.finRange wires.length).foldl
      (fun acc k => matMulFn acc (wirePairGateFn (wires.get k).1 (wires.get k).2
        (gateBlockFullFn (t p k)))) oneFn) := by
    have hB1 : ContDiff ℝ ⊤ (fun _ : E =>
        (oneFn : (Fin n → Fin 2) → (Fin n → Fin 2) → ℂ)) := contDiff_const
    refine contDiff_gateChainFin
      (fun p k => wirePairGateFn (wires.get k).1 (wires.get k).2 (gateBlockFullFn (t p k))) ?_
      (fun _ => (oneFn : (Fin n → Fin 2) → (Fin n → Fin 2) → ℂ)) hB1
    refine contDiff_pi' fun k => contDiff_pi' fun x => contDiff_pi' fun y => ?_
    exact contDiff_wirePair (n := n) (E := E) _ _
      (fun p => gateBlockFullFn (t p k)) (gateBlockFullFn_contDiff _ (contDiff_pi.1 ht k)) x y
  exact contDiff_matmul_entry hφ (contDiff_matmul_entry hL hR)

set_option maxHeartbeats 2000000 in

/-- For a fixed list of wire pairs, the entry function `kakCircuitFullFn` is smooth in all its
real parameters. -/
theorem kakCircuitFullFn_contDiff {n : ℕ} (wires : List (Fin n × Fin n)) :
    ContDiff ℝ ⊤ (fun p : ℝ × (Fin n → ℝ × ℝ × ℝ) × (Fin wires.length → Fin 15 → ℝ) =>
      kakCircuitFullFn wires p) :=
  kakCircuitFullFn_contDiff_aux wires _ contDiff_fst _
    (contDiff_fst.comp contDiff_snd) _ (contDiff_snd.comp contDiff_snd)

/-- The real parameter space for `r` fifteen-parameter blocks and an `n`-wire local layer with
global phase has dimension `15 * r + 3 * n + 1`. -/
private theorem finrank_kakFullParam {n : ℕ} (r : ℕ) :
    Module.finrank ℝ (ℝ × (Fin n → ℝ × ℝ × ℝ) × (Fin r → Fin 15 → ℝ))
      = 15 * r + 3 * n + 1 := by
  simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self,
    Fintype.card_fin, Finset.card_univ, Finset.sum_const, smul_eq_mul]
  omega

/-- The range of the fifteen-parameter circuit family for a fixed wire list has Hausdorff
dimension at most `15 * wires.length + 3 * n + 1`. -/
theorem barenco_kakFullForm_dimH_le {n : ℕ} (wires : List (Fin n × Fin n)) :
    dimH (Set.range (kakCircuitFullFn wires))
      ≤ ((15 * wires.length + 3 * n + 1 : ℕ) : ℝ≥0∞) := by
  have h1 := ((kakCircuitFullFn_contDiff wires).of_le le_top).dimH_range_le
  rw [finrank_kakFullParam] at h1
  exact h1

/-- For natural numbers `r` and `s`, the quantity `3 * (2 * r - s)` is at most `15 * r`. -/
theorem gauge_dim_le_full_param (r s : ℕ) : 3 * (2 * r - s) ≤ 15 * r := by omega

/-- If `s ≤ 2 * r`, subtracting `3 * (2 * r - s)` from `15 * r` leaves `9 * r + 3 * s`. -/
theorem gauge_contraction_count {r s : ℕ} (hs : s ≤ 2 * r) :
    15 * r - 3 * (2 * r - s) = 9 * r + 3 * s := by omega

/-- If `s ≤ n` and `s ≤ 2 * r`, the contracted parameter count `15 * r - 3 * (2 * r - s)` is at
most `9 * r + 3 * n`. -/
theorem gauge_contracted_count_le {r s n : ℕ} (hsn : s ≤ n) (hs2r : s ≤ 2 * r) :
    15 * r - 3 * (2 * r - s) ≤ 9 * r + 3 * n := by omega

/-- When `r = 0` and `s ≤ 2 * 0`, the parameter-count identity reduces to `15 * 0 - 3 * (2 * 0 -
s) = 9 * 0 + 3 * s`. -/
theorem gauge_contraction_count_zero {s : ℕ} (hs : s ≤ 2 * 0) :
    15 * 0 - 3 * (2 * 0 - s) = 9 * 0 + 3 * s := by omega

/-- If a target set has Hausdorff dimension at least `4 ^ n` and the fifteen-parameter circuit
bound is smaller, some target lies outside the range of `kakCircuitFullFn`. -/
theorem barenco_existential_target_outside_full {n : ℕ} (wires : List (Fin n × Fin n))
    (A : Set ((Fin n → Fin 2) → (Fin n → Fin 2) → ℂ))
    (hA : ((4 ^ n : ℕ) : ℝ≥0∞) ≤ dimH A)
    (hcard : ((15 * wires.length + 3 * n + 1 : ℕ) : ℝ≥0∞) < ((4 ^ n : ℕ) : ℝ≥0∞)) :
    ∃ V, V ∈ A ∧ V ∉ Set.range (kakCircuitFullFn wires) := by
  by_contra hcon
  push_neg at hcon
  have h1 := barenco_kakFullForm_dimH_le wires
  have h2 : ((4 ^ n : ℕ) : ℝ≥0∞) ≤ ((15 * wires.length + 3 * n + 1 : ℕ) : ℝ≥0∞) :=
    hA.trans ((dimH_mono fun v hv => hcon v hv).trans h1)
  exact (lt_irrefl _ (lt_of_le_of_lt h2 hcard)).elim

end B2Smooth

end Qatlib.Concepts.CircuitImpl.MultiControl
