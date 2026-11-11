/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.ReflectionsPhaseBridge
import Qatlib.Papers.SpanProgSt12.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Source Theorem 13 — span-program evaluation by phase estimation

Fixed paper: Belovs & Reichardt, *Span programs and quantum algorithms for
st-connectivity and claw detection*, arXiv:1203.2603v1 (12 Mar 2012),
`assets/1203.2603.pdf`.  Section 5, Theorem 13 (paper p. 13).

Paper statement: "Assume `C₁W ≥ 1`. Then the above algorithm is correct and requires
`O(W)` controlled applications of `U`. In each of these applications, `R_Λ` requires
no access to the input oracle, whereas `R_Π` can be implemented in one oracle
query."

This file *proves* the theorem by bridging the corrected, machine-checked reflection
theory of the Frozen library (`reflections_true_zero_witness`,
`reflections_false_root_inverse`, `reflections_false_root_phase`,
`twoReflectionConstruction`) and a small arithmetic ledger.  The four content
conjuncts are:

1. existence of the kernel projector `Δ` with the exact kernel characterization
   (`A_G z = 0 ↔ Δ z = z`), fixed before the input `x`;
2. true-input correctness: a nonzero eigenvalue-one eigenvector of
   `U = R_Λ R_Π` with root overlap at least `9/10` (paper's "large overlap with
   `|0⟩` tuned by `C₁`);
3. false-input correctness: a genuine inverse image `η` of the root under `1 − U`
   with `‖η‖² ≤ (5/2)W²`, and the resulting low-phase mass bound
   `(2√(6ΘW) + Θ/2)²` at precision `Θ` (the paper's Lemma 11 route);
4. the resource ledger: with precision `Θ = 1/W` the algorithm uses at most `2W`
   controlled applications of `U`, and `R_Π = 2Π_x − 1` is exactly a single phase
   query to the complement marker.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QueryComplexity.Reflections
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SpanProgSt12.MainResults.SpanProgramEval

/-- Number of controlled applications of `U` required by phase estimation at
precision `Θ`: the inverse precision, rounded up (paper: "the number of
applications of `U` is equal to the inverse of the precision, up to a constant
factor"). -/
def phaseEstimationApplications (Θ : ℝ) : ℕ := ⌈1 / Θ⌉₊

/-- At the paper's precision `Θ = 1/W` with `W ≥ 1`, phase estimation uses at most
`2W` controlled applications of `U` (the `O(W)` ledger of Theorem 13). -/
theorem phaseEstimationApplications_bound {W : ℝ} (hW : 1 ≤ W) :
    (phaseEstimationApplications (1 / W) : ℝ) ≤ 2 * W := by
  have hWpos : 0 < W := by linarith
  unfold phaseEstimationApplications
  rw [one_div_one_div]
  have hle : (⌈W⌉₊ : ℝ) ≤ W + 1 := by
    have h := Nat.ceil_lt_add_one hWpos.le
    linarith
  linarith

/-- **Theorem 13 (arXiv:1203.2603v1, Section 5, p. 13).**  Assume a span program
`P` with a dual witness `v` of value `W ≥ 1`.  Then, writing `U = R_Λ R_Π` for the
two-reflection unitary of `P`:

* `R_Λ = 2Δ − I` for a fixed kernel projector `Δ` with the exact kernel
  characterization, and `R_Π = 2Π_x − I` is exactly a single phase query;
* on true inputs, `U` has a nonzero eigenvalue-one eigenvector with overlap at
  least `9/10` on the root `|0⟩`;
* on false inputs, the root has an exact inverse image under `1 − U` of squared
  norm at most `(5/2)W²`, so the low-phase mass at precision `Θ` is at most
  `(2√(6ΘW) + Θ/2)²`;
* phase estimation at precision `Θ = 1/W` uses at most `2W` controlled
  applications of `U`. -/
theorem source_theorem13
    {X : Type} [Fintype X] [DecidableEq X] {n m : ℕ}
    (input : X → Fin n → Bool) (f : X → Bool)
    (v : X → Fin n → Fin m → ℂ) (W : ℝ)
    (hd : SourceDualFeasible input f v W) (hW : 1 ≤ W) :
    ∃ Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ,
      IsOrthogonalProjector Δ ∧
      (∀ z : QState (Vertex X f n m),
        adjacency input f v W *ᵥ z = 0 ↔ Δ *ᵥ z = z) ∧
      (∀ x : X, f x = true →
        ∃ ψ : QState (Vertex X f n m), ψ ≠ 0 ∧
          twoReflectionUnitary input f x Δ *ᵥ ψ = ψ ∧
          (9 / 10 : ℝ) * (∑ z, ‖ψ z‖ ^ 2) ≤ ‖ψ (Sum.inr (Sum.inl ()))‖ ^ 2) ∧
      (∀ x : X, f x = false →
        ∃ η : QState (Vertex X f n m),
          (1 - twoReflectionUnitary input f x Δ) *ᵥ η =
            Ket (Sum.inr (Sum.inl ())) ∧
          (∑ z, ‖η z‖ ^ 2) ≤ (5 / 2 : ℝ) * W ^ 2) ∧
      (∀ x : X, f x = false → ∀ (J : Type) [Fintype J] [DecidableEq J]
        (V : Matrix (Vertex X f n m) J ℂ) (θ : J → ℝ),
        Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry V → V * Vᴴ = 1 →
        twoReflectionUnitary input f x Δ * V =
          V * Matrix.diagonal (fun i => Complex.exp (Complex.I * θ i)) →
        ∀ Θ : ℝ, 0 ≤ Θ →
          (∑ i ∈ Finset.univ.filter (fun i => |θ i| ≤ Θ),
            ‖(Vᴴ *ᵥ Ket (Sum.inr (Sum.inl ()))) i‖ ^ 2) ≤
            (2 * Real.sqrt (6 * Θ * W) + Θ / 2) ^ 2) ∧
      (phaseEstimationApplications (1 / W) : ℝ) ≤ 2 * W ∧
      (∀ x : X,
        (2 : ℂ) • pixProj (m := m) input f x -
            (1 : Matrix (Vertex X f n m) (Vertex X f n m) ℂ) =
          PhaseOracle (fun l => match l with
            | Sum.inl _ => false
            | Sum.inr c => complementMark input f x c)) := by
  obtain ⟨-, _, hPix, Δ, hΔ, hk⟩ := twoReflectionConstruction X n m input f v W
  refine ⟨Δ, hΔ, hk, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact reflections_true_zero_witness input f v W hd hW Δ hk x hx
  · intro x hx
    exact reflections_false_root_inverse input f v W hd hW Δ hΔ hk x hx
  · intro x hx J _ _ V θ hV hfull hEV Θ hΘ
    exact reflections_false_root_phase input f v W hd hW Δ hΔ hk x hx J V θ
      hV hfull hEV Θ hΘ
  · exact phaseEstimationApplications_bound hW
  · intro x
    exact hPix x

end Qatlib.Papers.SpanProgSt12.MainResults.SpanProgramEval
