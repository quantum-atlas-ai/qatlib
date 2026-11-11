/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# FermEigState17 — elementary cost-model toolkit

Fixed paper version: arXiv:1711.10460,
"Improved Techniques for Preparing Eigenstates of Fermionic Hamiltonians".

This file holds the small asymptotic bookkeeping vocabulary shared by the
paper-layer complexity claims.  The paper states every resource bound in
`O(·)` form.  At the paper layer we encode the same asymptotic classes with
*positive* representatives: `log x` is replaced by `1 + log x` (and
`log log x` by `1 + log (1 + log x)`), which is the standard way to make the
`O`-statements total and monotone on the whole domain without changing the
asymptotic class.  The predicates below are explicit-constant upper bounds,
i.e. the elementary definition of `f = O(g)`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FermEigState17.MainResults.CostModel

/-- `1 + log x`, the positive representative of the asymptotic class `log x`. -/
def onePlusLog (x : ℝ) : ℝ := 1 + Real.log x

/-- `1 + log (1 + log x)`, the positive representative of `log log x`. -/
def onePlusLogLog (x : ℝ) : ℝ := onePlusLog (onePlusLog x)

/-- Gate reference `η (1 + log η)`, same asymptotic class as `η log η`. -/
def etaGate (η : ℝ) : ℝ := η * onePlusLog η

/-- Gate target `η (1 + log η) (1 + log N)`, same class as `η log η log N`
(Claim c001). -/
def sortGateTarget (η N : ℝ) : ℝ := etaGate η * onePlusLog N

/-- Depth target `(1 + log η) (1 + log (1 + log N))`, same class as
`log η · log log N` (Claim c001). -/
def sortDepthTarget (η N : ℝ) : ℝ := onePlusLog η * onePlusLogLog N

/-- Gate/depth target `η² (1 + log N)`, same class as `η² log N` (Claim c002). -/
def etaSqTarget (η N : ℝ) : ℝ := η ^ 2 * onePlusLog N

/-- Explicit-constant form of `f = O(g)`. -/
def IsO (f g : ℝ) : Prop := ∃ K : ℝ, 0 ≤ K ∧ f ≤ K * g

/-- `1 + log x` is nonnegative for `x ≥ 1`. -/
lemma onePlusLog_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ onePlusLog x := by
  unfold onePlusLog
  have := Real.log_nonneg hx
  linarith

/-- `1 + log x` is monotone on `x ≥ 1`. -/
lemma onePlusLog_le_onePlusLog {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    onePlusLog x ≤ onePlusLog y := by
  unfold onePlusLog
  have hxpos : 0 < x := by linarith
  have := Real.log_le_log hxpos hxy
  linarith

/-- `1 + log (1 + log x)` is nonnegative for `x ≥ 1`. -/
lemma onePlusLogLog_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ onePlusLogLog x := by
  have h1 : 1 ≤ onePlusLog x := by
    unfold onePlusLog
    have := Real.log_nonneg hx
    linarith
  have hdef : onePlusLogLog x = 1 + Real.log (onePlusLog x) := rfl
  rw [hdef]
  have := Real.log_nonneg h1
  linarith

/-- `1 + log (1 + log x)` is monotone on `x ≥ 1`. -/
lemma onePlusLogLog_le_of_le {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    onePlusLogLog x ≤ onePlusLogLog y := by
  have hx1 : 1 ≤ onePlusLog x := by
    unfold onePlusLog
    have := Real.log_nonneg hx
    linarith
  exact onePlusLog_le_onePlusLog hx1 (onePlusLog_le_onePlusLog hx hxy)

/-- `1 + log log N ≤ 1 + log N` for `N ≥ 1`; used to fold the Step-6 depth
`η² (log log N + log η)` into the final `O(η² log N)`. -/
lemma onePlusLogLog_le_onePlusLog {N : ℝ} (hN : 1 ≤ N) :
    onePlusLogLog N ≤ onePlusLog N := by
  have hdef : onePlusLogLog N = onePlusLog (onePlusLog N) := rfl
  rw [hdef]
  unfold onePlusLog
  have hNpos : 0 < N := by linarith
  have h1 : 1 + Real.log N ≤ N := by
    have := Real.log_le_sub_one_of_pos hNpos
    linarith
  have h2 : 0 < 1 + Real.log N := by
    have := Real.log_nonneg hN
    linarith
  have := Real.log_le_log h2 h1
  linarith

/-- `η (1 + log η)` is nonnegative for `η ≥ 1`. -/
lemma etaGate_nonneg {η : ℝ} (hη : 1 ≤ η) : 0 ≤ etaGate η := by
  unfold etaGate
  exact mul_nonneg (by linarith) (onePlusLog_nonneg hη)

/-- `η (1 + log η) ≤ η (1 + log η)(1 + log N)` for `1 ≤ η ≤ N`. -/
lemma etaGate_le_sortGateTarget {η N : ℝ} (hη : 1 ≤ η) (hηN : η ≤ N) :
    etaGate η ≤ sortGateTarget η N := by
  unfold sortGateTarget
  have hfac : 1 ≤ onePlusLog N := by
    unfold onePlusLog
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by linarith)
    linarith
  calc etaGate η = etaGate η * 1 := by ring
    _ ≤ etaGate η * onePlusLog N :=
        mul_le_mul_of_nonneg_left hfac (etaGate_nonneg hη)
    _ = etaGate η * onePlusLog N := rfl

/-- `η (1 + log η) ≤ η² (1 + log N)` for `2 ≤ η ≤ N`. -/
lemma etaGate_le_etaSqTarget {η N : ℝ} (hη : 2 ≤ η) (hηN : η ≤ N) :
    etaGate η ≤ etaSqTarget η N := by
  unfold etaGate etaSqTarget
  have hηpos : 0 < η := by linarith
  have hlogN1 : 0 ≤ 1 + Real.log N := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by linarith)
    linarith
  have h1log : 1 + Real.log η ≤ 1 + Real.log N := by
    have := Real.log_le_log (by linarith : (0 : ℝ) < η) hηN
    linarith
  have hfac : 1 + Real.log η ≤ η * (1 + Real.log N) := by
    have h2 : 1 + Real.log N ≤ η * (1 + Real.log N) := by
      calc 1 + Real.log N = 1 * (1 + Real.log N) := by ring
        _ ≤ η * (1 + Real.log N) :=
            mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ η) hlogN1
    linarith
  calc η * (1 + Real.log η) = η * (1 + Real.log η) := rfl
    _ ≤ η * (η * (1 + Real.log N)) :=
        mul_le_mul_of_nonneg_left hfac (le_of_lt hηpos)
    _ = η ^ 2 * (1 + Real.log N) := by ring

/-- `1 + log η ≤ (1 + log η)(1 + log(1 + log N))`. -/
lemma onePlusLog_le_sortDepthTarget {η N : ℝ} (hη : 1 ≤ η) (hN : 1 ≤ N) :
    onePlusLog η ≤ sortDepthTarget η N := by
  unfold sortDepthTarget
  have hfac : 1 ≤ onePlusLogLog N := by
    have hlog : 1 ≤ onePlusLog N := by
      unfold onePlusLog
      have := Real.log_nonneg hN
      linarith
    have hdef : onePlusLogLog N = 1 + Real.log (onePlusLog N) := rfl
    rw [hdef]
    have := Real.log_nonneg hlog
    linarith
  calc onePlusLog η = onePlusLog η * 1 := by ring
    _ ≤ onePlusLog η * onePlusLogLog N :=
        mul_le_mul_of_nonneg_left hfac (onePlusLog_nonneg hη)

/-- `(1 + log η)(1 + log(1 + log N)) ≥ 1`. -/
lemma one_le_sortDepthTarget {η N : ℝ} (hη : 1 ≤ η) (hN : 1 ≤ N) :
    (1 : ℝ) ≤ sortDepthTarget η N := by
  unfold sortDepthTarget
  have h1 : 1 ≤ onePlusLog η := by
    unfold onePlusLog
    have := Real.log_nonneg hη
    linarith
  have h2 : 1 ≤ onePlusLogLog N := by
    have hlog : 1 ≤ onePlusLog N := by
      unfold onePlusLog
      have := Real.log_nonneg hN
      linarith
    have hdef : onePlusLogLog N = 1 + Real.log (onePlusLog N) := rfl
    rw [hdef]
    have := Real.log_nonneg hlog
    linarith
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ onePlusLog η * onePlusLogLog N :=
        mul_le_mul h1 h2 (by norm_num) (by linarith)

/-- `η² (1 + log N) ≥ 1`. -/
lemma one_le_etaSqTarget {η N : ℝ} (hη : 1 ≤ η) (hN : 1 ≤ N) :
    (1 : ℝ) ≤ etaSqTarget η N := by
  unfold etaSqTarget
  have h1 : 1 ≤ η ^ 2 := by nlinarith
  have h2 : 1 ≤ 1 + Real.log N := by
    have := Real.log_nonneg hN
    linarith
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ η ^ 2 * (1 + Real.log N) :=
        mul_le_mul h1 h2 (by norm_num) (by positivity)

end Qatlib.Papers.FermEigState17.MainResults.CostModel
