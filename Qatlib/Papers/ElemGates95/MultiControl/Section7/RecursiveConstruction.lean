/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemGates95.MultiControl.Section7.MultibitNetworks

/-!
# Recursive construction of multicontrolled gates

This module realizes the five-block recursion of Lemma 7.5 of [BarencoEtAl1995] as an equality
between actual local gate lists. A unitary square root `V` of `U`, a controlled prefix-AND
toggle, and a smaller circuit with target operation `V` combine to implement `U` with one
additional control.

The theorem `lemma7_5_step` accepts the two smaller circuits as hypotheses. The existence
theorem `lemma7_5_actual` supplies them and records the exact concatenation and length formula;
`noWorkPrefixAnd_update_ne` ensures that changing a distinct wire leaves the control predicate
unchanged.

## Main statements

* `lemma7_5_step`: the list `vs ++ xs ++ ds ++ xs ++ rs` implements the additional control and
  has length `12 + 2 * xs.length + rs.length`.
* `lemma7_5_actual`: a unitary square root and all five legal component lists exist.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Papers.ElemGates95.MultiControl.Section7

/-- Updating a wire distinct from each of the first `r` control wires leaves their prefix
conjunction unchanged. -/
theorem noWorkPrefixAnd_update_ne {N : ℕ} (c : ℕ → Fin N) (r : ℕ) (s : Fin N)
    (h : ∀ i < r, c i ≠ s) (x : Reg N) (v : Bool) :
    noWorkPrefixAnd (fun i => Function.update x s v (c i)) r =
      noWorkPrefixAnd (fun i => x (c i)) r := by
  apply Bool.eq_iff_iff.mpr
  simp only [noWorkPrefixAnd, List.all_eq_true, List.mem_range]
  exact ⟨fun hh i hi => by simpa [Function.update_of_ne (h i hi)] using! hh i hi,
    fun hh i hi => by simpa [Function.update_of_ne (h i hi)] using! hh i hi⟩

/-- Implements the five-block recursion of Lemma 7.5 of [BarencoEtAl1995] from a unitary square
root, a prefix-AND toggle circuit, and a smaller controlled-root circuit. The constructed
list has the exact form `vs ++ xs ++ ds ++ xs ++ rs` and length `12 + 2 * xs.length +
rs.length`. -/
theorem lemma7_5_step {N m : ℕ} (c : ℕ → Fin N) (t : Fin N)
    (hctm : ∀ i < m, c i ≠ t) (hclast : ∀ i < m, c i ≠ c m) (hlast : c m ≠ t)
    (U V : Matrix Bool Bool ℂ) (hV : V ∈ Matrix.unitaryGroup Bool ℂ) (hVV : V * V = U)
    (xs : List (ReflectionGate N)) (hxs : reflectionLegal xs)
    (hxsrun : ∀ x : Reg N, Run 1 (reflectionCompile xs)
      (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket
        (Function.update x (c m) (x (c m) ^^ noWorkPrefixAnd (fun i => x (c i)) m)))
    (rs : List (ReflectionGate N)) (hrs : reflectionLegal rs)
    (hrsrun : ∀ (x : Reg N) (φ : QState Bool),
      Run 1 (reflectionCompile rs) (multiWireState t x φ) =
        multiWireState t x (ApplyGate
          (if noWorkPrefixAnd (fun i => x (c i)) m then V else 1) φ)) :
    ∃ gs vs ds : List (ReflectionGate N),
      reflectionLegal vs ∧ reflectionLegal ds ∧
      vs.length = 6 ∧ ds.length = 6 ∧
      gs = vs ++ xs ++ ds ++ xs ++ rs ∧
      reflectionLegal gs ∧
      gs.length = 12 + 2 * xs.length + rs.length ∧
      ∀ (x : Reg N) (φ : QState Bool),
        Run 1 (reflectionCompile gs) (multiWireState t x φ) =
          multiWireState t x (ApplyGate
            (if noWorkPrefixAnd (fun i => x (c i)) (m + 1) then U else 1) φ) := by
  let p := knownQubitAnglesOfUnitary V
  have hp : knownQubitUnitary p = V :=
    (knownQubitEuler_explicit_angles_cover_unitaries V hV).1
  let padj := knownQubitAngleAdjoint p
  have hpadj : knownQubitUnitary padj = Vᴴ := by rw [knownQubitUnitary_adjoint, hp]
  let vs := multiKnownPairSteps (c m) t p
  let ds := multiKnownPairSteps (c m) t padj
  have hvs : reflectionLegal vs := multiKnownPairSteps_legal _ _ hlast p
  have hds : reflectionLegal ds := multiKnownPairSteps_legal _ _ hlast padj
  have hvlen : vs.length = 6 := rfl
  have hdlen : ds.length = 6 := rfl
  refine ⟨vs ++ xs ++ ds ++ xs ++ rs, vs, ds, hvs, hds, hvlen, hdlen, rfl, ?_, ?_, ?_⟩
  · simp only [reflectionLegal_append]
    exact ⟨⟨⟨⟨hvs, hxs⟩, hds⟩, hxs⟩, hrs⟩
  · simp only [List.length_append, hvlen, hdlen]
    omega
  · intro x φ
    let a := noWorkPrefixAnd (fun i => x (c i)) m
    let q := Function.update x (c m) (x (c m) ^^ a)
    have hA : noWorkPrefixAnd (fun i => q (c i)) m = a :=
      noWorkPrefixAnd_update_ne c m (c m) hclast x (x (c m) ^^ a)
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

/-- Supplies the unitary square root and actual legal component lists for Lemma 7.5 of
[BarencoEtAl1995]. It records the two six-gate controlled-root blocks, the prefix toggle and
smaller controlled-root actions, the exact concatenation, and its multicontrolled-`U`
semantics. -/
theorem lemma7_5_actual (N m : ℕ) (c : ℕ → Fin N) (t : Fin N)
    (hc : Set.InjOn c (Set.Iio (m + 1))) (hct : ∀ i < m + 1, c i ≠ t)
    (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    ∃ V : Matrix Bool Bool ℂ, V ∈ Matrix.unitaryGroup Bool ℂ ∧ V * V = U ∧
      ∃ (gs vs ds xs rs : List (ReflectionGate N)),
        reflectionLegal vs ∧ reflectionLegal ds ∧
        vs.length = 6 ∧ ds.length = 6 ∧
        gs = vs ++ xs ++ ds ++ xs ++ rs ∧
        reflectionLegal gs ∧
        gs.length = 12 + 2 * xs.length + rs.length ∧
        (∀ x : Reg N, Run 1 (reflectionCompile xs)
          (Qatlib.Foundations.PureStateMath.Ket x) =
          Qatlib.Foundations.PureStateMath.Ket
            (Function.update x (c m) (x (c m) ^^ noWorkPrefixAnd (fun i => x (c i)) m))) ∧
        (∀ (x : Reg N) (φ : QState Bool),
          Run 1 (reflectionCompile rs) (multiWireState t x φ) =
            multiWireState t x (ApplyGate
              (if noWorkPrefixAnd (fun i => x (c i)) m then V else 1) φ)) ∧
        ∀ (x : Reg N) (φ : QState Bool),
          Run 1 (reflectionCompile gs) (multiWireState t x φ) =
            multiWireState t x (ApplyGate
              (if noWorkPrefixAnd (fun i => x (c i)) (m + 1) then U else 1) φ) := by
  obtain ⟨V, hV, hVV⟩ := noWork_unitary_square_root U hU
  have hcm : Set.InjOn c (Set.Iio m) := by
    intro i hi j hj he
    exact hc (show i < m + 1 from by change i < m at hi; omega)
      (show j < m + 1 from by change j < m at hj; omega) he
  have hctm : ∀ i < m, c i ≠ t := fun i hi => hct i (by omega)
  have hccl : ∀ i < m, c i ≠ c m := by
    intro i hi he
    have := hc (show i < m + 1 by omega) (show m < m + 1 by omega) he
    omega
  have hlast : c m ≠ t := hct m (by omega)
  obtain ⟨xs, hxs, _, hxsrun⟩ :=
    noWork_single_dirty_and_table c t (c m) m hcm hctm hccl hlast.symm
  obtain ⟨rs, hrs, _, hrsrun⟩ :=
    noWork_multi_control_wire_table m c t hcm hctm V hV
  obtain ⟨gs, vs, ds, hvs, hds, hvlen, hdlen, hgs, hgl, hglen, hrun⟩ :=
    lemma7_5_step c t hctm hccl hlast U V hV hVV xs hxs hxsrun rs hrs hrsrun
  exact ⟨V, hV, hVV, gs, vs, ds, xs, rs, hvs, hds, hvlen, hdlen, hgs, hgl, hglen,
    hxsrun, hrsrun, hrun⟩

end Qatlib.Papers.ElemGates95.MultiControl.Section7
