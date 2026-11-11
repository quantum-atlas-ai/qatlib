/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.CopyExponent.CommutingCopyExactTightnessQuan
import Qatlib.Concepts.CopyEvolution.CopyExponent.SupNormTightCopyBudgetQuan

/-!
# Upper and lower copy bounds for density evolution

This module gives explicit upper and lower copy bounds for the fresh-copy partial-swap
procedure. A commuting two-dimensional family yields error at least t²s/(4n), while a
state-dependent ceiling budget achieves trace-norm error at most ε for arbitrary density
operators.

The bounds quantify the copy dependence of density-matrix exponentiation
[LloydMohseniRebentrost2014] for this procedure.

## Main statements

* `copyComplexityLower`: derives n ≥ t²s/(4ε) from the commuting-family error bound.
* `copyComplexityUpper`: gives a sufficient budget with n ≤ 16t²/ε + 1 and exact resource
  counts.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.CopyEvolution.CopyExponent

open Matrix

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CopyEvolution.CopyExponent
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

/-- The two-dimensional diagonal operator with diagonal entries one and zero used in the
commuting example. -/
private noncomputable def rho2 : Operator 2 :=
  Matrix.diagonal fun b => if b = 0 then (1 : ℂ) else 0

/-- The two-dimensional diagonal operator with diagonal entries `1 - s` and `s` used in the
commuting example. -/
private noncomputable def sigma2 (s : ℝ) : Operator 2 :=
  Matrix.diagonal fun b => if b = 0 then ((1 - s : ℝ) : ℂ) else (s : ℂ)

/-- For the stated commuting family and parameter bounds, `n` fresh-copy steps have trace-norm
error at least `t²s/(4n)`. This gives a concrete lower estimate for the procedure of
[LloydMohseniRebentrost2014]. -/
theorem commutingFamilyCopyLower (t : ℝ) (n : ℕ) (s : ℝ) (ht : 0 ≤ t) (hn : 0 < n)
    (hsq : t ^ 2 ≤ (n : ℝ)) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    t ^ 2 * s / (4 * (n : ℝ)) ≤
      Matrix.traceNorm (freshCopyReferenceRun rho2 (List.replicate n (t / (n : ℝ))) 1
        (TensorGate (sigma2 s) (1 : Operator 1)) - TensorGate (sigma2 s) (1 : Operator 1)) := by
  have htight := commutingCopyExactTightness t n s ht hn hsq hs0 hs1
  dsimp only [rho2, sigma2]
  rw [htight.2.1]
  have hcos := htight.2.2
  have hs2 : (0 : ℝ) ≤ 2 * s := by positivity
  have hstep : t ^ 2 / (8 * (n : ℝ)) * (2 * s) ≤
      (1 - (Real.cos (t / (n : ℝ))) ^ (2 * n)) * (2 * s) :=
    mul_le_mul_of_nonneg_right hcos hs2
  have hnr : (n : ℝ) ≠ 0 := by positivity
  calc t ^ 2 * s / (4 * (n : ℝ))
      = t ^ 2 / (8 * (n : ℝ)) * (2 * s) := by field_simp; ring
    _ ≤ (1 - (Real.cos (t / (n : ℝ))) ^ (2 * n)) * (2 * s) := hstep
    _ = (1 - (Real.cos (t / (n : ℝ))) ^ (2 * n)) * 2 * s := by ring

/-- If the commuting-family fresh-copy error is at most positive `ε`, the stated parameter
bounds imply `n ≥ t²s/(4ε)`. This is a lower bound for this simulation procedure in the
setting of [LloydMohseniRebentrost2014]. -/
theorem copyComplexityLower (t : ℝ) (n : ℕ) (s ε : ℝ) (ht : 0 ≤ t) (hn : 0 < n)
    (hsq : t ^ 2 ≤ (n : ℝ)) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 < ε)
    (herr : Matrix.traceNorm (freshCopyReferenceRun rho2 (List.replicate n (t / (n : ℝ))) 1
        (TensorGate (sigma2 s) (1 : Operator 1)) - TensorGate (sigma2 s) (1 : Operator 1)) ≤ ε) :
    t ^ 2 * s / (4 * ε) ≤ (n : ℝ) := by
  have hlow := commutingFamilyCopyLower t n s ht hn hsq hs0 hs1
  have h1 : t ^ 2 * s / (4 * (n : ℝ)) ≤ ε := hlow.trans herr
  have hnr : (0 : ℝ) < n := by positivity
  have hden : (0 : ℝ) < 4 * (n : ℝ) := by positivity
  have h2 : t ^ 2 * s ≤ ε * (4 * (n : ℝ)) := (div_le_iff₀ hden).mp h1
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ε)]
  nlinarith [h2]

/-- The budget `max 1 (Nat.ceil (8 * t² * Matrix.traceNorm (ρ - σ) / ε))` achieves trace-norm
error at most `ε`, has resource tuple `(n, n, n, 0)`, and satisfies `n ≤ 16t²/ε + 1` for
density inputs. This provides explicit copy bounds for [LloydMohseniRebentrost2014]. -/
theorem copyComplexityUpper {D : ℕ} (ρ σ : Operator D) (t ε : ℝ)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) (hε : 0 < ε) :
    let n : ℕ := max 1 (Nat.ceil (8 * t ^ 2 * Matrix.traceNorm (ρ - σ) / ε))
    Matrix.traceNorm (freshCopyReferenceRun ρ (List.replicate n (t / (n : ℝ))) 1
        (TensorGate σ (1 : Operator 1)) -
      TensorGate (HamiltonianEvolution ρ t) (1 : Operator 1) * TensorGate σ (1 : Operator 1) *
        (TensorGate (HamiltonianEvolution ρ t) (1 : Operator 1))ᴴ) ≤ ε ∧
    freshCopyResourceCounts D (List.replicate n (t / (n : ℝ))) = (n, n, n, 0) ∧
    (n : ℝ) ≤ 16 * t ^ 2 / ε + 1 :=
  supNormTightCopyBudget D ρ σ t ε hρ hσ hε

end Qatlib.Concepts.CopyEvolution.CopyExponent
