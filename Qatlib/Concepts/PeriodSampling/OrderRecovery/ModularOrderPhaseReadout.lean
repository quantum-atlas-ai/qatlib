/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.HspRecovery.RecordExtract.ExecutionSemantics
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.EncodingCore

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Qatlib.Concepts.PeriodSampling.OrderRecovery

open Matrix
open scoped Classical

theorem modularMulPerm_injective (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) :
    Function.Injective fun x : ZMod N => (a : ZMod N) * x := by
  intro x y h
  have h2 := congrArg (fun z : ZMod N => ((a⁻¹ : (ZMod N)ˣ) : ZMod N) * z) h
  dsimp only at h2
  rwa [← mul_assoc, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    one_mul, one_mul] at h2

def modularOrderMatrix (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) : Matrix (ZMod N) (ZMod N) ℂ :=
  permMatrix fun x : ZMod N => (a : ZMod N) * x

theorem modularOrderMatrix_unitary (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) :
    modularOrderMatrix N a ∈ Matrix.unitaryGroup (ZMod N) ℂ :=
  permMatrix_unitary_of_injective (modularMulPerm_injective N a)

theorem applyGate_modularOrderMatrix_ket (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (x : ZMod N) :
    ApplyGate (modularOrderMatrix N a) (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket ((a : ZMod N) * x) := by
  funext i
  simp only [modularOrderMatrix, ApplyGate, permMatrix, Matrix.mulVec, dotProduct,
    Matrix.of_apply, Qatlib.Foundations.PureStateMath.Ket]
  rw [Finset.sum_eq_single x]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

theorem applyGate_modularOrderMatrix (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (φ : QState (ZMod N)) (x : ZMod N) :
    ApplyGate (modularOrderMatrix N a) φ x = φ (((a⁻¹ : (ZMod N)ˣ) : ZMod N) * x) := by
  simp only [modularOrderMatrix, ApplyGate, permMatrix, Matrix.mulVec, dotProduct,
    Matrix.of_apply]
  rw [Finset.sum_eq_single (((a⁻¹ : (ZMod N)ˣ) : ZMod N) * x)]
  · have hmul : (a : ZMod N) * (((a⁻¹ : (ZMod N)ˣ) : ZMod N) * x) = x := by
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [if_pos hmul.symm, one_mul]
  · intro v _ hv
    have hne : x ≠ (a : ZMod N) * v := by
      intro h
      apply hv
      have h2 := congrArg (fun z : ZMod N => ((a⁻¹ : (ZMod N)ˣ) : ZMod N) * z) h

      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at h2
      exact h2.symm
    rw [if_neg hne]
    simp
  · simp

theorem applyGate_modularOrderMatrix_pow_ket (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) (k : ℕ)
    (x : ZMod N) :
    ApplyGate ((modularOrderMatrix N a) ^ k) (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (((a ^ k : (ZMod N)ˣ) : ZMod N) * x) := by
  induction k generalizing x with
  | zero =>
    simp [pow_zero, applyGate_one]
  | succ k ih =>
    rw [pow_succ, applyGate_mul, applyGate_modularOrderMatrix_ket, ih]
    congr 1
    rw [← mul_assoc, ← Units.val_mul, ← pow_succ]

theorem inv_pow_mul_eq_one_iff (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) (k : ℕ) (x : ZMod N) :
    ((((a⁻¹ : (ZMod N)ˣ) ^ k : (ZMod N)ˣ) : ZMod N) * x = 1) ↔
      x = ((a ^ k : (ZMod N)ˣ) : ZMod N) := by
  constructor
  · intro h
    have h2 := congrArg (fun z : ZMod N => (((a ^ k : (ZMod N)ˣ)) : ZMod N) * z) h

    rw [← mul_assoc, ← Units.val_mul,
      show (a ^ k : (ZMod N)ˣ) * (a⁻¹ : (ZMod N)ˣ) ^ k = 1 from by
        rw [inv_pow, mul_inv_cancel], Units.val_one, one_mul, mul_one] at h2
    exact h2
  · intro h
    rw [h, ← Units.val_mul, show (a⁻¹ : (ZMod N)ˣ) ^ k * a ^ k = 1 from by
      rw [inv_pow, inv_mul_cancel], Units.val_one]

noncomputable def modularOrderOracle (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) :
    Matrix (Fin M × ZMod N) (Fin M × ZMod N) ℂ :=
  BlockDiag fun y : Fin M => if y.val + 1 = M then modularOrderMatrix N a else 1

theorem modularOrderOracle_unitary (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) :
    modularOrderOracle N M a ∈ Matrix.unitaryGroup (Fin M × ZMod N) ℂ := by
  apply blockDiag_unitary
  intro y
  split
  · exact modularOrderMatrix_unitary N a
  · exact Submonoid.one_mem _

theorem applyGate_modularOrderOracle (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (Ψ : QState (Fin M × ZMod N)) (w : Fin M) (x : ZMod N) :
    ApplyGate (modularOrderOracle N M a) Ψ (w, x) =
      ApplyGate (if w.val + 1 = M then modularOrderMatrix N a else 1)
        (fun v => Ψ (w, v)) x := by
  simp only [modularOrderOracle, ApplyGate, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single w]
  · simp only [BlockDiag, Matrix.of_apply, if_true]
  · intro u _ hu
    apply Finset.sum_eq_zero
    intro v _
    simp only [BlockDiag, Matrix.of_apply, if_neg (Ne.symm hu), zero_mul]
  · simp

theorem applyGate_modularOrderOracle_fiber (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (Ψ : QState (Fin M × ZMod N)) (w : Fin M) (x : ZMod N) :
    ApplyGate (modularOrderOracle N M a) Ψ (w, x) =
      if w.val + 1 = M then Ψ (w, (((a⁻¹ : (ZMod N)ˣ) : ZMod N) * x)) else Ψ (w, x) := by
  rw [applyGate_modularOrderOracle]
  by_cases hw : w.val + 1 = M
  · rw [if_pos hw, if_pos hw]
    exact applyGate_modularOrderMatrix N a _ x
  · rw [if_neg hw, if_neg hw]
    exact congrFun (applyGate_one _) x

def modularOrderSwapPerm (N M : ℕ) (y last : Fin M) : Fin M × ZMod N → Fin M × ZMod N :=
  fun p => (Equiv.swap y last p.1, p.2)

theorem modularOrderSwapPerm_involutive (N M : ℕ) (y last : Fin M) :
    Function.Involutive (modularOrderSwapPerm N M y last) := by
  rintro ⟨z, x⟩
  simp only [modularOrderSwapPerm, Prod.mk.injEq]
  refine ⟨?_, trivial⟩
  show Equiv.swap y last (Equiv.swap y last z) = z
  rw [← Equiv.trans_apply, Equiv.swap_swap, Equiv.refl_apply]

theorem modularOrderSwapPerm_last_iff (M : ℕ) (y last z : Fin M)
    (hlast : last.val + 1 = M) :
    (Equiv.swap y last z).val + 1 = M ↔ z = y := by
  constructor
  · intro h
    have hsz : Equiv.swap y last z = last := by
      apply Fin.ext
      omega
    have h2 := congrArg (Equiv.swap y last) hsz
    rw [show Equiv.swap y last (Equiv.swap y last z) = z from by
      rw [← Equiv.trans_apply, Equiv.swap_swap, Equiv.refl_apply],
      Equiv.swap_apply_right] at h2
    exact h2
  · intro h
    subst h
    rw [Equiv.swap_apply_left]
    exact hlast

def modularOrderSwapBlock (N M : ℕ) [NeZero N] (y last : Fin M) :
    Circuit (Fin M × ZMod N) :=
  [Step.gate (permMatrix (modularOrderSwapPerm N M y last)), Step.query,
    Step.gate (permMatrix (modularOrderSwapPerm N M y last))]

theorem modularOrderSwapGate_unitary (N M : ℕ) [NeZero N] (y last : Fin M) :
    permMatrix (modularOrderSwapPerm N M y last) ∈
      Matrix.unitaryGroup (Fin M × ZMod N) ℂ :=
  permMatrix_unitary (modularOrderSwapPerm_involutive N M y last)

theorem isUnitaryCircuit_modularOrderSwapBlock (N M : ℕ) [NeZero N] (y last : Fin M) :
    IsUnitaryCircuit (modularOrderSwapBlock N M y last) := by
  intro U hU
  simp only [modularOrderSwapBlock, List.mem_cons, List.not_mem_nil, or_false] at hU
  rcases hU with hU | hU | hU
  · obtain rfl := Step.gate.inj hU
    exact modularOrderSwapGate_unitary N M y last
  · cases hU
  · obtain rfl := Step.gate.inj hU
    exact modularOrderSwapGate_unitary N M y last

theorem modularOrderSwapBlock_counts (N M : ℕ) [NeZero N] (y last : Fin M) :
    QueryCount (modularOrderSwapBlock N M y last) = 1 ∧
      GateCount (modularOrderSwapBlock N M y last) = 2 :=
  ⟨rfl, rfl⟩

theorem run_modularOrderSwapBlock (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (y last : Fin M)
    (hlast : last.val + 1 = M) (Φ : QState (Fin M × ZMod N)) :
    Run (modularOrderOracle N M a) (modularOrderSwapBlock N M y last) Φ =
      fun p => if p.1 = y then Φ (p.1, (((a⁻¹ : (ZMod N)ˣ) : ZMod N) * p.2))
        else Φ p := by
  funext p
  obtain ⟨z, x⟩ := p
  show ApplyGate (permMatrix (modularOrderSwapPerm N M y last))
      (ApplyGate (modularOrderOracle N M a)
        (ApplyGate (permMatrix (modularOrderSwapPerm N M y last)) Φ)) (z, x) = _
  rw [applyGate_permMatrix (modularOrderSwapPerm_involutive N M y last),
    applyGate_modularOrderOracle_fiber,
    applyGate_permMatrix (modularOrderSwapPerm_involutive N M y last)]
  simp only [modularOrderSwapPerm,
      applyGate_permMatrix (modularOrderSwapPerm_involutive N M y last)]
  show (if (Equiv.swap y last z).val + 1 = M then
      Φ (Equiv.swap y last (Equiv.swap y last z), (((a⁻¹ : (ZMod N)ˣ) : ZMod N) * x))
    else Φ (Equiv.swap y last (Equiv.swap y last z), x)) = _
  rw [show Equiv.swap y last (Equiv.swap y last z) = z from by
    rw [← Equiv.trans_apply, Equiv.swap_swap, Equiv.refl_apply]]
  by_cases hz : z = y
  · rw [if_pos ((modularOrderSwapPerm_last_iff M y last z hlast).mpr hz), if_pos hz]
  · rw [if_neg (fun h => hz ((modularOrderSwapPerm_last_iff M y last z hlast).mp h)),
      if_neg hz]

theorem run_modularOrderSwapBlock_repeat (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (y last : Fin M) (hlast : last.val + 1 = M) (k : ℕ) (Φ : QState (Fin M × ZMod N)) :
    Run (modularOrderOracle N M a)
        (RepeatCircuit (modularOrderSwapBlock N M y last) k) Φ =
      fun p => if p.1 = y then
        Φ (p.1, ((((a⁻¹ : (ZMod N)ˣ) ^ k : (ZMod N)ˣ) : ZMod N) * p.2)) else Φ p := by
  induction k generalizing Φ with
  | zero =>
    funext p
    obtain ⟨z, x⟩ := p
    simp [RepeatCircuit, run_nil]
  | succ k ih =>
    rw [RepeatCircuit, run_append, ih]
    rw [run_modularOrderSwapBlock N M a y last hlast]
    funext p
    obtain ⟨z, x⟩ := p
    by_cases hz : z = y
    · simp only [hz, if_true]
      congr 2
      rw [← mul_assoc, ← Units.val_mul, ← pow_succ']
    · simp only [hz, if_false]

def modularOrderLabels (M : ℕ) : List (Fin M) :=
  (List.range' 1 (M - 1)).attach.map fun y =>
    ⟨y.val, by
      have hy := (List.mem_range'_1).mp y.property
      omega⟩

theorem modularOrderLabels_map_val (M : ℕ) :
    (modularOrderLabels M).map Fin.val = List.range' 1 (M - 1) := by
  simp only [modularOrderLabels, List.map_map]
  change (List.range' 1 (M - 1)).attach.map Subtype.val = _
  simp

theorem modularOrderLabels_nodup (M : ℕ) : (modularOrderLabels M).Nodup := by
  apply List.Nodup.map _ (List.nodup_attach.mpr _)
  · intro a b hab
    exact Subtype.ext (Fin.ext_iff.mp hab)
  · rw [List.range'_eq_map_range]
    exact List.Nodup.map (fun a b h => Nat.add_left_cancel h) (List.nodup_range)

theorem mem_modularOrderLabels {M : ℕ} {y : Fin M} :
    y ∈ modularOrderLabels M ↔ y.val ≠ 0 := by
  simp only [modularOrderLabels, List.mem_map, List.mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨v, hv, heq⟩
    have hv' := (List.mem_range'_1).mp hv
    have hval : y.val = v := (congrArg Fin.val heq).symm
    omega
  · intro hy
    exact ⟨y.val, (List.mem_range'_1).mpr ⟨by omega, by omega⟩, Fin.ext rfl⟩

theorem sum_range'_one_mul_two (n : ℕ) : (List.range' 1 n).sum * 2 = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hsplit : List.range' 1 (n + 1) = List.range' 1 n ++ [n + 1] := by
      rw [← List.range'_append_1 (s := 1) (m := n) (n := 1)]
      congr 1
      show List.range' (1 + n) 1 = [n + 1]
      rw [show 1 + n = n + 1 from Nat.add_comm 1 n]
      rfl
    rw [hsplit, List.sum_append, List.sum_singleton]
    calc ((List.range' 1 n).sum + (n + 1)) * 2
        = (List.range' 1 n).sum * 2 + (n + 1) * 2 := by ring
      _ = n * (n + 1) + (n + 1) * 2 := by rw [ih]
      _ = (n + 1) * (n + 2) := by ring

theorem sum_modularOrderLabels_val_mul_two (M : ℕ) :
    ((modularOrderLabels M).map Fin.val).sum * 2 = M * (M - 1) := by
  rw [modularOrderLabels_map_val]
  have h2 := sum_range'_one_mul_two (M - 1)
  have h3 : (M - 1) * (M - 1 + 1) = M * (M - 1) := by
    rcases M with _ | M'
    · rfl
    · rw [Nat.succ_sub_one, Nat.mul_comm]
  rw [h3] at h2
  exact h2

theorem sum_modularOrderLabels_val (M : ℕ) :
    ((modularOrderLabels M).map Fin.val).sum = M * (M - 1) / 2 := by
  have h2 := sum_modularOrderLabels_val_mul_two M
  calc ((modularOrderLabels M).map Fin.val).sum
      = ((modularOrderLabels M).map Fin.val).sum * 2 / 2 :=
        by omega
    _ = M * (M - 1) / 2 := by rw [h2]

def modularOrderLoop (N M : ℕ) [NeZero N] (last : Fin M) : Circuit (Fin M × ZMod N) :=
  (modularOrderLabels M).flatMap fun y =>
    RepeatCircuit (modularOrderSwapBlock N M y last) y.val

theorem queryCount_flatMap {I : Type} [Fintype I] [DecidableEq I] {α : Type}
    (l : List α) (f : α → Circuit I) :
    QueryCount (l.flatMap f) = (l.map fun x => QueryCount (f x)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, queryCount_append, ih]

theorem gateCount_flatMap {I : Type} [Fintype I] [DecidableEq I] {α : Type}
    (l : List α) (f : α → Circuit I) :
    GateCount (l.flatMap f) = (l.map fun x => GateCount (f x)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, gateCount_append, ih]

theorem isUnitaryCircuit_flatMap {I : Type} [Fintype I] [DecidableEq I] {α : Type}
    (l : List α) (f : α → Circuit I) (h : ∀ x ∈ l, IsUnitaryCircuit (f x)) :
    IsUnitaryCircuit (l.flatMap f) := by
  induction l with
  | nil => exact isUnitaryCircuit_nil
  | cons x xs ih =>
    rw [List.flatMap_cons, isUnitaryCircuit_append]
    exact ⟨h x (List.mem_cons_self), ih (fun y hy => h y (List.mem_cons_of_mem x hy))⟩

theorem list_sum_two_mul_val {M : ℕ} (l : List (Fin M)) :
    (l.map fun y => 2 * y.val).sum = 2 * (l.map Fin.val).sum := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem modularOrderLoop_counts (N M : ℕ) [NeZero N] (last : Fin M) :
    QueryCount (modularOrderLoop N M last) = M * (M - 1) / 2 ∧
      GateCount (modularOrderLoop N M last) = M * (M - 1) := by
  refine ⟨?_, ?_⟩
  · rw [modularOrderLoop, queryCount_flatMap]
    rw [show ((modularOrderLabels M).map fun y =>
          QueryCount (RepeatCircuit (modularOrderSwapBlock N M y last) y.val))
        = (modularOrderLabels M).map Fin.val from by
      apply List.map_congr_left
      intro y _
      rw [queryCount_repeatCircuit, (modularOrderSwapBlock_counts N M y last).1, mul_one]]
    exact sum_modularOrderLabels_val M
  · rw [modularOrderLoop, gateCount_flatMap]
    rw [show ((modularOrderLabels M).map fun y =>
          GateCount (RepeatCircuit (modularOrderSwapBlock N M y last) y.val))
        = (modularOrderLabels M).map (fun y => 2 * y.val) from by
      apply List.map_congr_left
      intro y _
      rw [gateCount_repeatCircuit, (modularOrderSwapBlock_counts N M y last).2]
      exact Nat.mul_comm _ _]
    rw [list_sum_two_mul_val]
    have h2 := sum_modularOrderLabels_val_mul_two M
    rw [mul_comm 2, h2]

theorem isUnitaryCircuit_modularOrderLoop (N M : ℕ) [NeZero N] (last : Fin M) :
    IsUnitaryCircuit (modularOrderLoop N M last) := by
  rw [modularOrderLoop]
  apply isUnitaryCircuit_flatMap
  intro y _
  apply IsUnitaryCircuit.repeatCircuit
  exact isUnitaryCircuit_modularOrderSwapBlock N M y last

def fiberPowShift (N : ℕ) [NeZero N] {M : ℕ} (a : (ZMod N)ˣ) (L : List (Fin M))
    (Φ : QState (Fin M × ZMod N)) : QState (Fin M × ZMod N) :=
  fun p => if p.1 ∈ L then
    Φ (p.1, ((((a⁻¹ : (ZMod N)ˣ) ^ p.1.val : (ZMod N)ˣ) : ZMod N) * p.2))
    else Φ p

theorem fiberPowShift_cons (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (y : Fin M)
    (ys : List (Fin M)) (hny : y ∉ ys) (Φ : QState (Fin M × ZMod N)) :
    fiberPowShift N a (y :: ys) Φ =
      fiberPowShift N a ys (fun p => if p.1 = y then
        Φ (p.1, ((((a⁻¹ : (ZMod N)ˣ) ^ y.val : (ZMod N)ˣ) : ZMod N) * p.2))
        else Φ p) := by
  funext p
  obtain ⟨z, x⟩ := p
  simp only [fiberPowShift, List.mem_cons]
  by_cases hzy : z = y
  · subst hzy
    rw [if_pos (Or.inl rfl), if_neg hny, if_pos rfl]
  · by_cases hzys : z ∈ ys
    · rw [if_pos (Or.inr hzys), if_pos hzys, if_neg hzy]
    · rw [if_neg (not_or.mpr ⟨hzy, hzys⟩), if_neg hzys, if_neg hzy]

theorem run_modularOrderLoop_list (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (last : Fin M)
    (hlast : last.val + 1 = M) :
    ∀ (L : List (Fin M)), L.Nodup → ∀ (Φ : QState (Fin M × ZMod N)),
    Run (modularOrderOracle N M a)
        (L.flatMap fun y => RepeatCircuit (modularOrderSwapBlock N M y last) y.val) Φ =
      fiberPowShift N a L Φ := by
  intro L hL
  induction L with
  | nil =>
    intro Φ
    funext p
    obtain ⟨z, x⟩ := p
    simp [fiberPowShift]
  | cons y ys ih =>
    intro Φ
    have hny : y ∉ ys := (List.nodup_cons.mp hL).1
    have hys : ys.Nodup := (List.nodup_cons.mp hL).2
    rw [List.flatMap_cons, run_append,
      run_modularOrderSwapBlock_repeat N M a y last hlast, ih hys]
    exact (fiberPowShift_cons N M a y ys hny Φ).symm

theorem run_modularOrderLoop (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (last : Fin M)
    (hlast : last.val + 1 = M) (Φ : QState (Fin M × ZMod N)) :
    Run (modularOrderOracle N M a) (modularOrderLoop N M last) Φ =
      fiberPowShift N a (modularOrderLabels M) Φ := by
  show Run (modularOrderOracle N M a)
      ((modularOrderLabels M).flatMap fun y =>
        RepeatCircuit (modularOrderSwapBlock N M y last) y.val) Φ = _
  exact run_modularOrderLoop_list N M a last hlast _ (modularOrderLabels_nodup M) Φ

theorem fiberPowShift_tensorState_uniform_ket_one (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (z : Fin M) (x : ZMod N) :
    fiberPowShift N a (modularOrderLabels M)
        (TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) (Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N)))
        (z, x) =
      (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
        (if x = ((a ^ z.val : (ZMod N)ˣ) : ZMod N) then 1 else 0) := by
  by_cases hz : z ∈ modularOrderLabels M
  · simp only [fiberPowShift, if_pos hz]
    simp only [TensorState, Qatlib.Foundations.PureStateMath.Ket]
    congr 1
    simp only [inv_pow_mul_eq_one_iff N a z.val x]
  · simp only [fiberPowShift, if_neg hz]
    have hzv : z.val = 0 := by
      by_contra h
      exact hz (mem_modularOrderLabels.mpr h)
    simp only [TensorState, Qatlib.Foundations.PureStateMath.Ket]
    congr 1
    rw [hzv, pow_zero, Units.val_one]

theorem controlledPowers_modularOrderMatrix_tensorState_ket_one_apply (N M : ℕ)
    [NeZero N] (a : (ZMod N)ˣ) (z : Fin M) (x : ZMod N) :
    (ControlledPowers (modularOrderMatrix N a) M *ᵥ
      TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) (Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N)))
        (z, x) =
      (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
        (if x = ((a ^ z.val : (ZMod N)ˣ) : ZMod N) then 1 else 0) := by
  simp only [ControlledPowers, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single z]
  · simp only [if_true]
    have hfactor : (∑ x' : ZMod N, (modularOrderMatrix N a ^ z.val) x x' *
          TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) (Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N))
            (z, x'))
        = (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
          ((modularOrderMatrix N a ^ z.val) *ᵥ Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N)) x := by
      simp only [TensorState, Qatlib.Foundations.PureStateMath.Ket, Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x' _ => by ring
    rw [hfactor]
    rw [show ((modularOrderMatrix N a ^ z.val) *ᵥ Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N)) =
        Qatlib.Foundations.PureStateMath.Ket (((a ^ z.val : (ZMod N)ˣ) : ZMod N) * 1) from
      applyGate_modularOrderMatrix_pow_ket N a z.val 1]
    rw [mul_one]
    rfl
  · intro w _ hw
    apply Finset.sum_eq_zero
    intro x' _
    rw [if_neg hw.symm]
    simp
  · simp

def modularLast (M : ℕ) (hM : 0 < M) : Fin M := ⟨M - 1, Nat.sub_lt hM Nat.one_pos⟩

theorem modularLast_val_add_one (M : ℕ) (hM : 0 < M) :
    (modularLast M hM).val + 1 = M :=
  Nat.sub_add_cancel hM

noncomputable def modularOrderCircuit (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) :
    Circuit (Fin M × ZMod N) :=
  if hM : 0 < M then
    [Step.gate (TensorGate (Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare
        (fun _ : Fin M => (Real.sqrt (M : ℝ))⁻¹) ⟨0, hM⟩)
        (1 : Matrix (ZMod N) (ZMod N) ℂ))] ++
    modularOrderLoop N M (modularLast M hM) ++
    [Step.gate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix (ZMod N) (ZMod N) ℂ))]
  else []

theorem uniformVector_nonneg (M : ℕ) : ∀ _ : Fin M, 0 ≤ (Real.sqrt (M : ℝ))⁻¹ :=
  fun _ => by positivity

theorem uniformVector_sum_sq (M : ℕ) (hM : 0 < M) :
    ∑ _j : Fin M, ((Real.sqrt (M : ℝ))⁻¹) ^ 2 = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, inv_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (M : ℝ))]
  exact mul_inv_cancel₀ (by exact_mod_cast hM.ne' : (M : ℝ) ≠ 0)

theorem prepGate_unitary (N M : ℕ) [NeZero N] (hM : 0 < M) :
    TensorGate (Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare (fun _ : Fin M => (Real.sqrt (M : ℝ))⁻¹)
        ⟨0, hM⟩) (1 : Matrix (ZMod N) (ZMod N) ℂ) ∈
      Matrix.unitaryGroup (Fin M × ZMod N) ℂ :=
  tensorGate_unitary
    (Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare_unitary _ _ (uniformVector_nonneg M)
      (uniformVector_sum_sq M hM))
    (Submonoid.one_mem _)

theorem invQFTGate_unitary (N M : ℕ) [NeZero N] (hM : 0 < M) :
    TensorGate (QFTMatrix M)ᴴ (1 : Matrix (ZMod N) (ZMod N) ℂ) ∈
      Matrix.unitaryGroup (Fin M × ZMod N) ℂ :=
  tensorGate_unitary (conjTranspose_mem_unitaryGroup (qftMatrix_unitary hM))
    (Submonoid.one_mem _)

noncomputable def orderClockState (M : ℕ) : QState (Fin M) :=
  fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹

theorem applyGate_prepGate_ket_zero (N M : ℕ) [NeZero N] (hM : 0 < M) :
    ApplyGate (TensorGate (Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare
        (fun _ : Fin M => (Real.sqrt (M : ℝ))⁻¹) ⟨0, hM⟩)
        (1 : Matrix (ZMod N) (ZMod N) ℂ))
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M)) (Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N))) =
      TensorState (orderClockState M) (Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N)) := by
  rw [applyGate_tensorGate, applyGate_one]
  congr 1
  show ApplyGate (Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare (fun _ : Fin M => (Real.sqrt (M : ℝ))⁻¹)
      ⟨0, hM⟩) (Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M)) = orderClockState M
  show Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare (fun _ : Fin M => (Real.sqrt (M : ℝ))⁻¹) ⟨0, hM⟩ *ᵥ
      Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M) = orderClockState M
  rw [Qatlib.Concepts.BlockEncoding.EncodingCore.nonnegativePrepare_mulVec_ket _ _ (uniformVector_nonneg M)]
  funext j
  dsimp only [orderClockState]
  rw [Complex.ofReal_inv]

theorem run_modularOrderCircuit_loop (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M) :
    Run (modularOrderOracle N M a) (modularOrderLoop N M (modularLast M hM))
        (TensorState (orderClockState M) (Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N))) =
      ControlledPowers (modularOrderMatrix N a) M *ᵥ
        TensorState (orderClockState M) (Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N)) := by
  rw [run_modularOrderLoop N M a (modularLast M hM) (modularLast_val_add_one M hM)]
  funext p
  obtain ⟨z, x⟩ := p
  unfold orderClockState
  rw [fiberPowShift_tensorState_uniform_ket_one N M a z x,
    controlledPowers_modularOrderMatrix_tensorState_ket_one_apply N M a z x]

theorem run_modularOrderCircuit (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M) :
    Run (modularOrderOracle N M a) (modularOrderCircuit N M a)
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M)) (Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N))) =
      qpeOutput M (modularOrderMatrix N a) (Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N)) := by
  unfold modularOrderCircuit
  rw [dif_pos hM, run_append, run_append]
  simp only [run_gate, run_nil]
  rw [applyGate_prepGate_ket_zero N M hM, run_modularOrderCircuit_loop N M a hM]
  rfl

theorem modular_order_actual_unitary_and_controlled_power_run :
    ∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M),
      modularOrderMatrix N a ∈ Matrix.unitaryGroup (ZMod N) ℂ ∧
        modularOrderOracle N M a ∈ Matrix.unitaryGroup (Fin M × ZMod N) ℂ ∧
        Run (modularOrderOracle N M a) (modularOrderCircuit N M a)
            (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M)) (Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N))) =
          qpeOutput M (modularOrderMatrix N a) (Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N)) := by
  intro N M _ a hM
  exact ⟨modularOrderMatrix_unitary N a, modularOrderOracle_unitary N M a,
    run_modularOrderCircuit N M a hM⟩

theorem modular_order_exact_query_macro_ledger :
    ∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ), 0 < M →
      IsUnitaryCircuit (modularOrderCircuit N M a) ∧
        QueryCount (modularOrderCircuit N M a) = M * (M - 1) / 2 ∧
        GateCount (modularOrderCircuit N M a) = M * (M - 1) + 2 := by
  intro N M _ a hM
  unfold modularOrderCircuit
  rw [dif_pos hM]
  refine ⟨?_, ?_, ?_⟩
  · rw [isUnitaryCircuit_append, isUnitaryCircuit_append]
    refine ⟨⟨?_, isUnitaryCircuit_modularOrderLoop N M (modularLast M hM)⟩, ?_⟩
    · intro U hU
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hU
      obtain rfl := Step.gate.inj hU
      exact prepGate_unitary N M hM
    · intro U hU
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hU
      obtain rfl := Step.gate.inj hU
      exact invQFTGate_unitary N M hM
  · rw [queryCount_append, queryCount_append,
      (modularOrderLoop_counts N M (modularLast M hM)).1]
    simp [QueryCount]
  · rw [gateCount_append, gateCount_append,
      (modularOrderLoop_counts N M (modularLast M hM)).2]
    simp [GateCount]
    omega

noncomputable def modularOrderLaw (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M) :
    FinDist (Fin M) where
  prob y := MarginalProbLeft (Run (modularOrderOracle N M a) (modularOrderCircuit N M a)
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M)) (Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N)))) {y}
  nonneg _ := measureProb_nonneg _ _
  sum_one := by
    have hnorm : Normalized (Run (modularOrderOracle N M a) (modularOrderCircuit N M a)
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M)) (Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N)))) :=
      ((modular_order_exact_query_macro_ledger N M a hM).1).normalized_run
        (modularOrderOracle_unitary N M a)
        (normalized_tensorState (normalized_ket _) (normalized_ket _))
    simp only [MarginalProbLeft, MeasureProb, Finset.sum_product, Finset.sum_singleton]
    rw [← Fintype.sum_prod_type]
    exact hnorm

theorem modularOrderLaw_prob (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M)
    (y : Fin M) :
    (modularOrderLaw N M a hM).prob y =
      MarginalProbLeft (Run (modularOrderOracle N M a) (modularOrderCircuit N M a)
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M)) (Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N)))) {y} := rfl

theorem modular_order_pos (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) : 0 < orderOf a :=
  (isOfFinOrder_of_finite a).orderOf_pos

def modularOrbit (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) (j : Fin (orderOf a)) : ZMod N :=
  ((a ^ j.val : (ZMod N)ˣ) : ZMod N)

theorem modularOrbit_injective (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) :
    Function.Injective (modularOrbit N a) := by
  intro j k h
  apply Fin.ext
  apply pow_injOn_Iio_orderOf j.isLt k.isLt
  exact Units.ext h

noncomputable def modularOrbitLift (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (f : QState (Fin (orderOf a))) : QState (ZMod N) :=
  ∑ j, f j • Qatlib.Foundations.PureStateMath.Ket (modularOrbit N a j)

theorem inner_modularOrbitLift (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (f g : QState (Fin (orderOf a))) :
    Qatlib.Foundations.PureStateMath.Inner (modularOrbitLift N a f) (modularOrbitLift N a g) = Qatlib.Foundations.PureStateMath.Inner f g := by
  unfold modularOrbitLift
  simp only [Qatlib.Foundations.PureStateMath.Inner, star_sum, star_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, Finset.smul_sum]
  simp only [smul_eq_mul]
  change (∑ k, ∑ j, g k * (star (f j) * Qatlib.Foundations.PureStateMath.Inner (Qatlib.Foundations.PureStateMath.Ket (modularOrbit N a j))
    (Qatlib.Foundations.PureStateMath.Ket (modularOrbit N a k)))) = _
  simp_rw [inner_ket_ket, (modularOrbit_injective N a).eq_iff]
  simp [dotProduct, mul_ite, mul_comm]

noncomputable def modularOrbitFourier (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (s : Fin (orderOf a)) : QState (ZMod N) :=
  modularOrbitLift N a (fun j => star (QFTMatrix (orderOf a) j s))

theorem modularOrbitFourier_orthonormal (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (s t : Fin (orderOf a)) :
    Qatlib.Foundations.PureStateMath.Inner (modularOrbitFourier N a s) (modularOrbitFourier N a t) =
      if s = t then 1 else 0 := by
  rw [modularOrbitFourier, modularOrbitFourier, inner_modularOrbitLift]
  have hU := qftMatrix_unitary (modular_order_pos N a)
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
  have he := congrArg (fun A : Matrix (Fin (orderOf a)) (Fin (orderOf a)) ℂ => A t s) hU
  simpa [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, mul_comm, eq_comm] using! he

theorem modularOrbitLift_ket_zero (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) :
    modularOrbitLift N a (Qatlib.Foundations.PureStateMath.Ket (⟨0, modular_order_pos N a⟩ : Fin (orderOf a))) =
      Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N) := by
  simp [modularOrbitLift, Qatlib.Foundations.PureStateMath.Ket, modularOrbit]

theorem modularOrbitFourier_decomposition (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) :
    (∑ s : Fin (orderOf a), (Real.sqrt (orderOf a : ℝ) : ℂ)⁻¹ •
      modularOrbitFourier N a s) = Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N) := by
  let z : Fin (orderOf a) := ⟨0, modular_order_pos N a⟩
  have hU := qftMatrix_unitary (modular_order_pos N a)
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hU
  have hc : ∀ j : Fin (orderOf a),
      (∑ s : Fin (orderOf a), (Real.sqrt (orderOf a : ℝ) : ℂ)⁻¹ *
        star (QFTMatrix (orderOf a) j s)) = Qatlib.Foundations.PureStateMath.Ket z j := by
    intro j
    have he := congrArg (fun A : Matrix (Fin (orderOf a)) (Fin (orderOf a)) ℂ => A z j) hU
    have hz : ∀ s : Fin (orderOf a), QFTMatrix (orderOf a) z s =
        (Real.sqrt (orderOf a : ℝ) : ℂ)⁻¹ := by
      intro s
      simp [QFTMatrix, z]
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, hz, Matrix.one_apply,
      Qatlib.Foundations.PureStateMath.Ket, eq_comm] using! he
  rw [← modularOrbitLift_ket_zero N a]
  unfold modularOrbitFourier modularOrbitLift
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hc]
  rfl

theorem orbitFourier_coeff_rotate (r : ℕ) (hr : 0 < r) (s j : Fin r) :
    star (QFTMatrix r j s) = primRoot r ^ s.val *
      star (QFTMatrix r (finRotate r j) s) := by
  have hc : ∀ k : Fin r, star (QFTMatrix r k s) =
      (Real.sqrt (r : ℝ) : ℂ)⁻¹ * primRoot r ^ (-((k.val : ℤ) * s.val)) := by
    intro k
    simp only [QFTMatrix, Matrix.of_apply, RCLike.star_def, map_mul, map_inv₀,
      Complex.conj_ofReal, primRoot_conj_zpow]
  simp only [hc]
  rw [← zpow_natCast]
  have hp : primRoot r ^ (-((r : ℤ) * s.val)) = 1 := by
    rw [_root_.zpow_neg, _root_.zpow_mul, primRoot_zpow_natCast_eq_one hr, _root_.one_zpow, inv_one]
  cases r with
  | zero => omega
  | succ n =>
    rw [coe_finRotate]
    by_cases hj : j = Fin.last n
    · rw [if_pos hj]
      subst j
      simp only [Fin.val_last, Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one]
      have he : -((n : ℤ) * s.val) = (s.val : ℤ) + -(((n + 1 : ℕ) : ℤ) * s.val) := by
        push_cast
        ring
      rw [he, zpow_add₀ (primRoot_ne_zero _), hp, mul_one, mul_comm]
    · rw [if_neg hj]
      push_cast
      rw [mul_left_comm, ← zpow_add₀ (primRoot_ne_zero _)]
      congr 1
      congr 1
      ring

theorem modularOrbit_rotate (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (j : Fin (orderOf a)) :
    (a : ZMod N) * modularOrbit N a j = modularOrbit N a (finRotate (orderOf a) j) := by
  unfold modularOrbit
  have hr := modular_order_pos N a
  generalize he : orderOf a = r at j ⊢
  cases r with
  | zero => omega
  | succ n =>
    rw [coe_finRotate]
    by_cases hj : j = Fin.last n
    · rw [if_pos hj]
      subst j
      simp only [Fin.val_last, pow_zero, Units.val_one]
      rw [← Units.val_mul, ← pow_succ', ← he, pow_orderOf_eq_one, Units.val_one]
    · rw [if_neg hj, ← Units.val_mul, ← pow_succ']

theorem modularOrbitFourier_eigen_root (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (s : Fin (orderOf a)) :
    ApplyGate (modularOrderMatrix N a) (modularOrbitFourier N a s) =
      primRoot (orderOf a) ^ s.val • modularOrbitFourier N a s := by
  unfold modularOrbitFourier modularOrbitLift ApplyGate
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul]
  change (∑ j, star (QFTMatrix (orderOf a) j s) •
      ApplyGate (modularOrderMatrix N a) (Qatlib.Foundations.PureStateMath.Ket (modularOrbit N a j))) = _
  simp_rw [applyGate_modularOrderMatrix_ket, modularOrbit_rotate]
  conv_lhs =>
    arg 2
    ext j
    rw [orbitFourier_coeff_rotate (orderOf a) (modular_order_pos N a) s j]
  rw [Finset.smul_sum]
  simp_rw [← smul_smul]
  exact Equiv.sum_comp (finRotate (orderOf a)) (fun j =>
    primRoot (orderOf a) ^ s.val •
      (star (QFTMatrix (orderOf a) j s) • Qatlib.Foundations.PureStateMath.Ket (modularOrbit N a j)))

theorem modularOrbitFourier_eigen (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (s : Fin (orderOf a)) :
    ApplyGate (modularOrderMatrix N a) (modularOrbitFourier N a s) =
      Complex.exp (2 * Real.pi * Complex.I * (((s.val : ℝ) / (orderOf a : ℝ)) : ℂ)) •
        modularOrbitFourier N a s := by
  rw [modularOrbitFourier_eigen_root, primRoot, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem modularOrbitFourier_weight (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) :
    ‖(Real.sqrt (orderOf a : ℝ) : ℂ)⁻¹‖ ^ 2 = 1 / (orderOf a : ℝ) := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (by positivity), one_div]

theorem modular_order_born_uniform_orbit_spectrum :
    ∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M) (y : Fin M),
      1 < N → (modularOrderLaw N M a hM).prob y =
        1 / (orderOf a : ℝ) * ∑ s : Fin (orderOf a),
          ‖qpeKernel M ((s.val : ℝ) / (orderOf a : ℝ)) y‖ ^ 2 := by
  intro N M _ a hM y _hN
  rw [modularOrderLaw_prob, run_modularOrderCircuit,
    ← modularOrbitFourier_decomposition N a]
  rw [(offgrid_qpe_eigen_and_spectral_law M (modularOrderMatrix N a)
    (Qatlib.Foundations.PureStateMath.Ket (1 : ZMod N)) 0 hM).2 (Fin (orderOf a)) (modularOrbitFourier N a)
    (fun _ => (Real.sqrt (orderOf a : ℝ) : ℂ)⁻¹)
    (fun s => (s.val : ℝ) / (orderOf a : ℝ))
    (fun j k => by
      by_cases hj : j = k
      · simpa only [if_pos hj] using! modularOrbitFourier_orthonormal N a j k
      · simpa only [if_neg hj] using! modularOrbitFourier_orthonormal N a j k)
    (fun j => by simpa only [Complex.ofReal_div] using! modularOrbitFourier_eigen N a j)]
  simp_rw [modularOrbitFourier_weight]
  exact (Finset.mul_sum _ _ _).symm

end Qatlib.Concepts.PeriodSampling.OrderRecovery
