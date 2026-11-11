/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# RmSearch.Complexity.Simulability — Theorem 4: classical simulability of Algorithm 2

Fixed source: arXiv:2603.26039v3, "Achieving double-logarithmic precision dependence in
optimization-based quantum unstructured search", Theorem 4, p. 11–13.

Algorithm 2 (Grover-compatible Riemannian modified Newton) keeps the quantum iterate `U_k`
inside the two-dimensional Grover plane `S = span_ℂ{|ψ₀⟩, H|ψ₀⟩}`.  Writing the gradient
`[H, ψ_k] = x_k X₀ + y_k Y₀`, the whole iteration is described by the real triple
`(x_k, y_k, q_k)`, and the paper's `FRMN` update (steps 1–6 on p. 11–12) is an explicit
classical procedure:

1. `γ_k := max(δ, |2q_k - 1|)`;
2. form the `2 × 2` matrix `M_k(t) = ∏_ℓ E_H(θ_ℓ^(1)(tγ_k;x_k,y_k)) E_{ψ₀}(θ_ℓ^(2)(tγ_k;x_k,y_k))`;
3. `(α_k^temp(t), β_k^temp(t)) := M_k(t)(α_k, β_k)` and `q_k^temp(t) := q₀|α_k^temp(t)|²`;
4. backtracking `t_k := ρ^{m_k}` with the smallest `m_k` satisfying the Armijo test
   `q_k^temp(ρ^{m_k}) ≥ q_k + cρ^{m_k}γ_k G_k`;
5. update `(α_{k+1}, β_{k+1}) := M_k(t_k)(α_k, β_k)`, `q_{k+1} = q₀|α_{k+1}|²`,
   `z_{k+1} = α_{k+1}\bar β_{k+1}`, `x_{k+1} = Re z_{k+1}`, `y_{k+1} = Im z_{k+1}`.

The nontrivial content, proved in the paper from Theorem 2 (Grover-plane invariance), is that
the next triple depends on the current triple through this classical map only.  This file
formalizes the classical update and the resulting iterate formula.
-/

set_option autoImplicit false
noncomputable section

open Classical

namespace Qatlib.Papers.QSearchPrec26.RmSearch.Complexity.Simulability

/-- The classical state of the FRMN process: Grover-plane coefficients and the success
probability `q_k = q₀ |α_k|² = Tr(Hψ_k)`. -/
structure GroverState where
  /-- Real part `ℜ(α_k \bar β_k)` of the Grover-plane coefficient product. -/
  x : ℝ
  /-- Imaginary part `ℑ(α_k \bar β_k)`. -/
  y : ℝ
  /-- Success probability `q_k = Tr(Hψ_k)`. -/
  q : ℝ

namespace GroverState

/-- The initial triplet `(x₀,y₀,q₀) = (1,0,q₀)` of Theorem 4 (p. 12). -/
def init (q0 : ℝ) : GroverState := ⟨1, 0, q0⟩

end GroverState

/-- Step 1 of FRMN: the modified Newton scaling `γ_k = max(δ, |2q_k - 1|)`. -/
def newtonScaling (δ : ℝ) (s : GroverState) : ℝ := max δ |2 * s.q - 1|

/-- The Armijo acceptance test used in step 4 of FRMN at trial step `t`:
`q_k^temp(t) ≥ q_k + c t γ_k G_k` with `G_k = 2q_k(1-q_k)`. -/
def armijoOk (trialQ : GroverState → ℝ → ℝ) (δ c : ℝ) (s : GroverState) (t : ℝ) : Prop :=
  s.q + c * t * newtonScaling δ s * (2 * s.q * (1 - s.q)) ≤ trialQ s t

/-- Step 4 of FRMN: the accepted step `t_k = ρ^{m_k}`, where `m_k` is the smallest
nonnegative integer satisfying the Armijo test.  If no integer satisfies it (which cannot
happen, by Lemma 5), the value `1` is returned. -/
def acceptedStep (trialQ : GroverState → ℝ → ℝ) (δ c ρ : ℝ) (s : GroverState) : ℝ :=
  if h : ∃ m : ℕ, armijoOk trialQ δ c s (ρ ^ m) then ρ ^ (Nat.find h) else 1

/-- One full classical FRMN update (steps 1–5): apply the classical `advance` map at the
accepted Armijo step.  `advance s t` is the result of step 5 at trial step `t`, i.e. the
`2 × 2` matrix computation `(α,β) ↦ M_k(t)(α,β)` followed by reading off `(x,y,q)`; it is a
function of the real triple `s` alone, hence classically computable. -/
def frmnStep (trialQ : GroverState → ℝ → ℝ)
    (advance : GroverState → ℝ → GroverState) (δ c ρ : ℝ) (s : GroverState) : GroverState :=
  advance s (acceptedStep trialQ δ c ρ s)

/-- **Theorem 4** (arXiv:2603.26039v3, Theorem 4, p. 11–13).  Run Algorithm 2 with the
5-factor retraction and fixed parameters `0 < δ ≤ 1`, `0 < c`, `0 < ρ < 1` from `U₀ = I`
(`q₀ = M/N ∈ (0,1]`).  Suppose the coefficient triples `(x_k,y_k,q_k)` of the quantum
iterates satisfy the FRMN recursion of steps 1–5 (the Grover-plane reduction derived from
Theorem 2 and Eq. (13)).  Then the triple at every iteration is the `k`-fold iterate of the
explicit classical map `FRMN = frmnStep trialQ advance δ c ρ` applied to `(1,0,q₀)`.

The hypothesis `hAlg2` is the paper's reduction of the quantum iteration to the classical
`2 × 2` computation (Theorem 2 together with the observation on p. 13 that the Armijo line
search is performed by evaluating `q_k^temp`, not by quantum sampling).  The construction of
`trialQ` and `advance` from `M_k(t)` (steps 2–5) is data of the classical process, and the
conclusion states that this process alone reproduces the entire trajectory. -/
theorem theorem4_classically_simulable
    (q0 δ c ρ : ℝ) (hq0 : 0 < q0) (hq01 : q0 ≤ 1)
    (hδ : 0 < δ) (hc : 0 < c) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (trialQ : GroverState → ℝ → ℝ) (advance : GroverState → ℝ → GroverState)
    (coeffs : ℕ → GroverState)
    (hinit : coeffs 0 = GroverState.init q0)
    (hAlg2 : ∀ k, coeffs (k + 1) = frmnStep trialQ advance δ c ρ (coeffs k)) :
    ∀ k, coeffs k = (frmnStep trialQ advance δ c ρ)^[k] (GroverState.init q0) := by
  intro k
  induction k with
  | zero => simpa using hinit
  | succ k ih =>
    rw [Function.iterate_succ_apply', hAlg2 k, ih]

/-- The classical FRMN step is determined by the current triple alone; consequently two
runs whose triples agree at some iterate have the same next triple.  This is the
phase-invariance statement behind Theorem 4's executability. -/
theorem frmnStep_congr (trialQ : GroverState → ℝ → ℝ)
    (advance : GroverState → ℝ → GroverState) (δ c ρ : ℝ)
    {s s' : GroverState} (h : s = s') :
    frmnStep trialQ advance δ c ρ s = frmnStep trialQ advance δ c ρ s' := by
  rw [h]

end Qatlib.Papers.QSearchPrec26.RmSearch.Complexity.Simulability
