/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.InterruptBridge.StoppingDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.StoppingCore.InterruptBridge

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal BigOperators Classical Matrix

variable {I R : Type} [Fintype I] [DecidableEq I]

theorem microStep_cons (O : Matrix I I ℂ) (s : Step I) (cs : List (Step I))
    (ψ : QState I) (r : R) (lg : List (Step I)) :
    microStep O ⟨s :: cs, ψ, r, lg⟩ =
      match s with
      | .gate U => ⟨cs, ApplyGate U ψ, r, .gate U :: lg⟩
      | .query => ⟨cs, ApplyGate O ψ, r, .query :: lg⟩ := by
  cases s <;> rfl

theorem microStep_nil (O : Matrix I I ℂ) (ψ : QState I) (r : R) (lg : List (Step I)) :
    microStep O ⟨[], ψ, r, lg⟩ = ⟨[], ψ, r, lg⟩ := rfl

theorem microAfter_succ (O : Matrix I I ℂ) (k : ℕ) (cfg : InterruptConfig I R) :
    microAfter O (k + 1) cfg = microAfter O k (microStep O cfg) := rfl

theorem microAfter_zero (O : Matrix I I ℂ) (cfg : InterruptConfig I R) :
    microAfter O 0 cfg = cfg := rfl

theorem microAfter_spec (O : Matrix I I ℂ) (k : ℕ) (cfg : InterruptConfig I R) :
    microAfter O k cfg =
      ⟨cfg.word.drop k, Run O (cfg.word.take k) cfg.mem, cfg.ref,
        (cfg.word.take k).reverse ++ cfg.log⟩ := by
  have hd : ∀ n : ℕ, List.drop n ([] : List (Step I)) = [] := by intro n; cases n <;> rfl
  have ht : ∀ n : ℕ, List.take n ([] : List (Step I)) = [] := by intro n; cases n <;> rfl
  induction k generalizing cfg with
  | zero =>
    rcases cfg with ⟨w, ψ, r, lg⟩
    rfl
  | succ k ih =>
    rcases cfg with ⟨w, ψ, r, lg⟩
    cases w with
    | nil =>
      rw [microAfter_succ, microStep_nil, ih]
      simp [hd, ht, Run]
    | cons s cs =>
      cases s with
      | gate U =>
        have hstep : microStep O ⟨Step.gate U :: cs, ψ, r, lg⟩ =
            ⟨cs, ApplyGate U ψ, r, Step.gate U :: lg⟩ := rfl
        rw [microAfter_succ, hstep, ih]
        simp [List.reverse_cons, List.append_assoc]
      | query =>
        have hstep : microStep O ⟨Step.query :: cs, ψ, r, lg⟩ =
            ⟨cs, ApplyGate O ψ, r, Step.query :: lg⟩ := rfl
        rw [microAfter_succ, hstep, ih]
        simp [List.reverse_cons, List.append_assoc]

theorem microAfter_add (O : Matrix I I ℂ) (m n : ℕ) (cfg : InterruptConfig I R) :
    microAfter O (m + n) cfg = microAfter O n (microAfter O m cfg) := by
  induction m generalizing cfg with
  | zero => rw [Nat.zero_add, microAfter_zero]
  | succ m ih =>
    rw [show m + 1 + n = m + n + 1 from by omega, microAfter_succ, ih, microAfter_succ]

theorem microAfter_empty (O : Matrix I I ℂ) (k : ℕ) (cfg : InterruptConfig I R)
    (h : cfg.word = []) : microAfter O k cfg = cfg := by
  have hd : ∀ n : ℕ, List.drop n ([] : List (Step I)) = [] := by intro n; cases n <;> rfl
  have ht : ∀ n : ℕ, List.take n ([] : List (Step I)) = [] := by intro n; cases n <;> rfl
  rcases cfg with ⟨w, ψ, r, lg⟩
  simp only at h
  subst h
  rw [microAfter_spec]
  simp [hd, ht, Run]

theorem microLaunch_nil (cfg : InterruptConfig I R) (h : cfg.word = []) :
    microLaunch cfg = Sum.inl (cfg.mem, cfg.ref, cfg.log) := by
  simp [microLaunch, h]

theorem microLaunch_cons (cfg : InterruptConfig I R) (h : cfg.word ≠ []) :
    microLaunch cfg = Sum.inr cfg := by
  simp [microLaunch, h]

theorem microNext_nil (O : Matrix I I ℂ) (ψ : QState I) (r : R) (lg : List (Step I)) :
    microNext O ⟨[], ψ, r, lg⟩ = PMF.pure (Sum.inl (ψ, r, lg)) := rfl

theorem microNext_cons (O : Matrix I I ℂ) (s : Step I) (cs : List (Step I))
    (ψ : QState I) (r : R) (lg : List (Step I)) :
    microNext O ⟨s :: cs, ψ, r, lg⟩ =
      if cs = [] then
        PMF.pure
          (Sum.inl ((microStep O ⟨s :: cs, ψ, r, lg⟩).mem,
            (microStep O ⟨s :: cs, ψ, r, lg⟩).ref, (microStep O ⟨s :: cs, ψ, r, lg⟩).log))
      else PMF.pure (Sum.inr (microStep O ⟨s :: cs, ψ, r, lg⟩)) := rfl

theorem microResult_nil (O : Matrix I I ℂ) (k : ℕ) (cfg : InterruptConfig I R)
    (h : cfg.word = []) :
    microResult O k cfg = Sum.inl ((microAfter O k cfg).mem, (microAfter O k cfg).ref,
      (microAfter O k cfg).log) := by
  simp [microResult, h]

theorem microResult_cons (O : Matrix I I ℂ) (k : ℕ) (cfg : InterruptConfig I R)
    (h : cfg.word ≠ []) (hk : cfg.word.length ≤ k) :
    microResult O k cfg = Sum.inl ((microAfter O k cfg).mem, (microAfter O k cfg).ref,
      (microAfter O k cfg).log) := by
  simp [microResult, hk]

theorem microResult_running (O : Matrix I I ℂ) (k : ℕ) (cfg : InterruptConfig I R)
    (hk : k < cfg.word.length) :
    microResult O k cfg = Sum.inr (microAfter O k cfg) := by
  simp [microResult, Nat.not_le.mpr hk]

theorem micro_runFor_point (O : Matrix I I ℂ) (k : ℕ) (cfg : InterruptConfig I R) :
    runFor (microNext O) k (microLaunch cfg) =
      PMF.pure (microResult O k cfg, min k cfg.word.length) := by
  induction k generalizing cfg with
  | zero =>
    rcases cfg with ⟨w, ψ, r, lg⟩
    cases w with
    | nil => rfl
    | cons s cs => rfl
  | succ k ih =>
    rcases cfg with ⟨w, ψ, r, lg⟩
    cases w with
    | nil =>
      rw [microLaunch_nil _ rfl, runFor_halted,
        microResult_nil O (k + 1) ⟨[], ψ, r, lg⟩ rfl,
        microAfter_empty O (k + 1) ⟨[], ψ, r, lg⟩ rfl]
      rfl
    | cons s cs =>
      rw [microLaunch_cons _ (by simp)]
      show
        CostedLaw.bind (tick (microNext O) (Sum.inr ⟨s :: cs, ψ, r, lg⟩))
          (runFor (microNext O) k) = _
      simp only [tick]
      rw [microNext_cons O s cs ψ r lg]
      cases hc : cs with
      | nil =>
        rw [if_pos rfl, PMF.pure_map, CostedLaw.bind, PMF.pure_bind, runFor_halted,
          CostedLaw.charge_ret]
        have hstep : (microStep O ⟨s :: [], ψ, r, lg⟩).word = [] := by
          rw [microStep_cons]; cases s <;> rfl
        rw [microResult_cons O (k + 1) ⟨s :: [], ψ, r, lg⟩ (by simp) (by simp),
          microAfter_succ, microAfter_empty O k (microStep O ⟨s :: [], ψ, r, lg⟩) hstep]
        rw [show min (k + 1) (List.length [s]) = 1 from by simp [List.length]]
      | cons s2 cs2 =>
        rw [if_neg (by simp [hc]), PMF.pure_map, CostedLaw.bind, PMF.pure_bind]
        have ih' := ih (microStep O ⟨s :: s2 :: cs2, ψ, r, lg⟩)
        have hstep : (microStep O ⟨s :: s2 :: cs2, ψ, r, lg⟩).word = s2 :: cs2 := by
          rw [microStep_cons]; cases s <;> rfl
        have hlaunch' : microLaunch (microStep O ⟨s :: s2 :: cs2, ψ, r, lg⟩) =
            Sum.inr (microStep O ⟨s :: s2 :: cs2, ψ, r, lg⟩) :=
          microLaunch_cons _ (by simp [hstep])
        rw [hlaunch'] at ih'
        rw [ih', CostedLaw.charge, PMF.pure_map, hstep]
        show PMF.pure (microResult O k (microStep O ⟨s :: s2 :: cs2, ψ, r, lg⟩),
            1 + min k (List.length (s2 :: cs2))) =
          PMF.pure (microResult O (k + 1) ⟨s :: s2 :: cs2, ψ, r, lg⟩,
            min (k + 1) (List.length (s :: s2 :: cs2)))
        have hlen : (s :: s2 :: cs2).length ≤ k + 1 ↔
            (microStep O ⟨s :: s2 :: cs2, ψ, r, lg⟩).word.length ≤ k := by
          simp [List.length, hstep]
        apply congrArg PMF.pure
        apply Prod.ext
        · by_cases hle : (s :: s2 :: cs2).length ≤ k + 1
          · rw [microResult_cons O (k + 1) ⟨s :: s2 :: cs2, ψ, r, lg⟩ (by simp) hle,
              microResult_cons O k (microStep O ⟨s :: s2 :: cs2, ψ, r, lg⟩) (by simp [hstep])
                (hlen.mp hle), microAfter_succ]
          · rw [microResult_running O (k + 1) ⟨s :: s2 :: cs2, ψ, r, lg⟩
                (by simpa using! Nat.not_le.mp hle),
              microResult_running O k (microStep O ⟨s :: s2 :: cs2, ψ, r, lg⟩) (by
                rw [hstep]
                exact Nat.lt_of_succ_lt_succ (Nat.not_le.mp hle)),
              microAfter_succ]
        · simp [List.length, hstep]
          omega

theorem prefix_resume : InterruptPrefixResume := by
  intro I R _ _ O m n cfg
  refine ⟨runFor_add (microNext O) m n (microLaunch cfg),
    (microAfter_add O m n cfg).symm, ?_⟩
  have h := congrArg (fun p : CostedLaw (InterruptOutput I R ⊕ InterruptConfig I R) =>
    p.map Prod.fst) (runFor_add (microNext O) m n (microLaunch cfg))

  rw [h, CostedLaw.bind, PMF.map_bind]
  congr 1
  funext x
  rw [CostedLaw.charge, PMF.map_comp]
  have hf : (Prod.fst ∘ fun x_1 : (InterruptOutput I R ⊕ InterruptConfig I R) × ℕ =>
    (x_1.1, x.2 + x_1.2)) = Prod.fst := by
    funext y
    rfl
  rw [hf]

theorem prefix_state : InterruptPrefixState := by
  intro I R _ _ O k cfg
  refine ⟨microAfter_spec O k cfg, fun hk => ?_⟩
  rw [micro_runFor_point, min_eq_left hk]

theorem cut_degenerate : InterruptCutDegenerate := by
  intro I R _ _ O cfg
  refine ⟨microAfter_zero O cfg, ?_, ?_⟩
  · intro n
    exact runFor_halted (microNext O) n (cfg.mem, cfg.ref, cfg.log)
  · intro k hk
    have hlen : ¬ cfg.word.length ≤ k := by omega
    refine ⟨microResult_running O k cfg hk, ?_, ?_⟩
    · rw [microAfter_spec]
    · intro hnil
      rw [microAfter_spec] at hnil
      have hdrop := congrArg List.length hnil
      simp [List.length_drop] at hdrop
      omega

theorem cut_kinds : InterruptCutKinds := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I w k
    unfold cutKind
    by_cases ha : optAtomic (w.drop k).head? = true <;>
      by_cases hb : optAtomic (w.take k).getLast? = true
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]
  · intro I w k
    rfl
  · intro I w hw k hk
    subst hw
    have hk' : k ≤ 1 := by simpa using! hk
    interval_cases k <;> rfl
  · intro U V
    rfl

theorem sum_bool (f : Bool → ℂ) : ∑ i, f i = f false + f true := by
  have h : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [h]
  simp [Finset.sum_insert, Finset.sum_singleton]

theorem pauliXZ_ne : PauliX * PauliZ ≠ PauliZ * PauliX := by
  intro h
  have h2 := congrFun (congrFun h false) true
  simp [PauliX, PauliZ, permMatrix, Matrix.mul_apply, Matrix.diagonal, sum_bool] at h2
  norm_num at h2

theorem applyGate_pauliX_ket_false : ApplyGate PauliX (Qatlib.Foundations.PureStateMath.Ket false) = Qatlib.Foundations.PureStateMath.Ket true := by
  funext i
  cases i with
  | false => simp [ApplyGate, Matrix.mulVec_eq_sum, PauliX, permMatrix, Qatlib.Foundations.PureStateMath.Ket, sum_bool]
  | true => simp [ApplyGate, Matrix.mulVec_eq_sum, PauliX, permMatrix, Qatlib.Foundations.PureStateMath.Ket, sum_bool]

theorem applyGate_pauliZ_ket_false : ApplyGate PauliZ (Qatlib.Foundations.PureStateMath.Ket false) = Qatlib.Foundations.PureStateMath.Ket false := by
  funext i
  cases i with
  | false => simp [ApplyGate, Matrix.mulVec_eq_sum, PauliZ, Matrix.diagonal, Qatlib.Foundations.PureStateMath.Ket, sum_bool]
  | true => simp [ApplyGate, Matrix.mulVec_eq_sum, PauliZ, Matrix.diagonal, Qatlib.Foundations.PureStateMath.Ket, sum_bool]

theorem applyGate_pauliZ_ket_true : ApplyGate PauliZ (Qatlib.Foundations.PureStateMath.Ket true) = (-1 : ℂ) • Qatlib.Foundations.PureStateMath.Ket true := by
  funext i
  cases i with
  | false => simp [ApplyGate, Matrix.mulVec_eq_sum, PauliZ, Matrix.diagonal, Qatlib.Foundations.PureStateMath.Ket, sum_bool]
  | true => simp [ApplyGate, Matrix.mulVec_eq_sum, PauliZ, Matrix.diagonal, Qatlib.Foundations.PureStateMath.Ket, sum_bool]

theorem run_xz_ne_run_zx (O : Matrix Bool Bool ℂ) :
    Run O [Step.gate PauliX, Step.gate PauliZ] (Qatlib.Foundations.PureStateMath.Ket false) ≠
      Run O [Step.gate PauliZ, Step.gate PauliX] (Qatlib.Foundations.PureStateMath.Ket false) := by
  intro h
  have h2 : ApplyGate PauliZ (ApplyGate PauliX (Qatlib.Foundations.PureStateMath.Ket false)) =
      ApplyGate PauliX (ApplyGate PauliZ (Qatlib.Foundations.PureStateMath.Ket false)) := by
    simpa [Run] using! h
  simp only [applyGate_pauliX_ket_false, applyGate_pauliZ_ket_false,
    applyGate_pauliZ_ket_true] at h2
  have h3 := congrFun h2 true
  simp [Qatlib.Foundations.PureStateMath.Ket] at h3
  norm_num at h3

theorem consumers : InterruptConsumers := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro O
    exact ⟨pauliXZ_ne, run_xz_ne_run_zx O⟩
  · intro O
    simp [microAfter_succ, microAfter_zero, microStep_cons, applyGate_pauliX_ket_false]
  · intro O
    rw [microAfter_spec]
    simp [Run, applyGate_pauliX_ket_false]
  · intro O
    have h := runFor_add (microNext O) 1 1
      (microLaunch ⟨[Step.gate PauliX, Step.gate PauliZ], Qatlib.Foundations.PureStateMath.Ket false, (), []⟩)
    simpa using! h
  · refine ⟨teleportBellResource_normalized, ?_⟩
    intro hex
    obtain ⟨a, b, hEq⟩ := hex
    have hff := congrFun hEq (false, false)
    have hft := congrFun hEq (false, true)
    have htt := congrFun hEq (true, true)
    simp only [TensorState] at hff hft htt
    rw [teleportBellResource_apply'] at hff hft htt
    rw [if_pos rfl] at hff htt
    rw [if_neg (by decide : (false : Bool) ≠ true)] at hft
    have hb : (Real.sqrt 2 : ℂ)⁻¹ ≠ 0 :=
      inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num)))
    rw [eq_comm, mul_eq_zero] at hft
    rcases hft with h0 | h0
    · rw [h0, zero_mul] at hff
      exact hb hff
    · rw [h0, mul_zero] at htt
      exact hb htt
  · intro Rt r k
    constructor
    · rw [microAfter_spec]
    · rw [microAfter_spec]

theorem clause13 : Clause13Claim :=
  ⟨prefix_resume, prefix_state, cut_degenerate, cut_kinds, consumers⟩

end Qatlib.Concepts.StoppingCore.InterruptBridge
