/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Element Distinctness Revisited — the reduced `(2k+1)`-dimensional subspace

Source: R. Portugal, *Element Distinctness Revisited*, fixed preprint
**arXiv:1711.11336v3 (13 Jun 2018)**.  Section 3 "Main Result",
Theorem 3.1 and its proof, pp. 6–10 of the PDF.

The paper analyses the staggered quantum walk for element `k`-distinctness in
the `(2k+1)`-dimensional invariant subspace spanned by the vectors `|η_ℓ^j⟩`
of Eq. (7).  This file records faithfully the *reduced model quantities* that
Theorem 3.1 refers to:

* the class cardinalities `|η_ℓ^j|` (p. 6);
* the eigenangles `φ_n` of the reduced evolution `u = u_β u_α`, Eq. (19), p. 9;
* the squared overlaps `⟨k,0|ψ_n⟩²`, Eqs. (20)–(22), p. 9;
* the spectral parameter `b`, Eq. (18), p. 9;
* the detuning `λ = ⟨k,0|ψ_0⟩ / √b`, Eq. (17), p. 9;
* the optimal parameters `t₂ = π/φ_k`, `t₁ = π/(2λ)` (Eqs. (26), (28)) and the
  maximal success probability `p_succ = 1/(4b)` (Eq. (25), p. 10).

The asymptotic content of Theorem 3.1 is stated in `Theorem31.lean`; the exact
optimality steps of the proof are proved in `Optimality.lean`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ElemDistinct17.MainResults

open scoped BigOperators

/-- Cardinality of the reduced class `η_ℓ^j` (Theorem 3.1 proof, p. 6):
`C(k,ℓ) · C(N-k, r-ℓ) · (N-r-k+ℓ)` for `j = 0` (the last element is unmarked)
and `C(k,ℓ) · C(N-k, r-ℓ) · (k-ℓ)` for `j = 1` (the last element is marked). -/
def etaCard (k N r ℓ j : ℕ) : ℕ :=
  Nat.choose k ℓ * Nat.choose (N - k) (r - ℓ) *
    (if j = 0 then N - r - k + ℓ else k - ℓ)

/-- `cos φ_n = 1 - 2n(N-n+1)/((r+1)(N-r))`, Eq. (19), p. 9. -/
noncomputable def cosPhi (N r n : ℕ) : ℝ :=
  1 - (2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1)) /
    (((r : ℝ) + 1) * ((N : ℝ) - (r : ℝ)))

/-- The eigenangle `φ_n` of the reduced evolution, Eq. (19), p. 9. -/
noncomputable def phi (N r n : ℕ) : ℝ := Real.arccos (cosPhi N r n)

/-- Squared overlap `⟨k,0|ψ_n⟩²`, Eqs. (20)–(22), p. 9.  The three cases
`n = 0`, `0 < n < k` and `n = k` are the paper's three displayed formulas. -/
noncomputable def overlapSq (k N r n : ℕ) : ℝ :=
  if n = 0 then
    ∏ i ∈ Finset.range k, (((r : ℝ) - (i : ℝ)) / ((N : ℝ) - (i : ℝ)))
  else if n < k then
    (1 / 2) * (Nat.choose k n : ℝ) *
      ((∏ i ∈ Finset.range n, ((N : ℝ) - (r : ℝ) - (i : ℝ))) *
       (∏ i ∈ Finset.range (k - n), ((r : ℝ) - (n : ℝ) - (i : ℝ)))) /
      ((∏ i ∈ Finset.range n, ((N : ℝ) - ((n : ℝ) - 1) - (i : ℝ))) *
       (∏ i ∈ Finset.range (k - n), ((N : ℝ) - 2 * (n : ℝ) - (i : ℝ))))
  else
    (1 / 2) * (∏ i ∈ Finset.range k, ((N : ℝ) - (r : ℝ) - (i : ℝ))) /
      (∏ i ∈ Finset.range k, ((N : ℝ) - ((k : ℝ) - 1) - (i : ℝ)))

/-- The spectral parameter `b = Σ_{n=1}^k ⟨k,0|ψ_n⟩² / (1 - cos(t₂ φ_n))`,
Eq. (18), p. 9. -/
noncomputable def bParam (k N r : ℕ) (t2 : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 k, overlapSq k N r n / (1 - Real.cos (t2 * phi N r n))

/-- The detuning `λ = ⟨k,0|ψ_0⟩ / √b`, Eq. (17), p. 9, using that
`overlapSq` stores the *squared* overlap `⟨k,0|ψ_0⟩²`. -/
noncomputable def lambdaParam (k N r : ℕ) (t2 : ℝ) : ℝ :=
  Real.sqrt (overlapSq k N r 0 / bParam k N r t2)

/-- The optimal number of walk steps `t₂ = π/φ_k`, Eq. (26), p. 10. -/
noncomputable def t2Opt (k N r : ℕ) : ℝ := Real.pi / phi N r k

/-- The optimal number of main-block repetitions `t₁ = π/(2λ)`, Eq. (28),
p. 10, evaluated at the optimal `t₂`. -/
noncomputable def t1Opt (k N r : ℕ) : ℝ :=
  Real.pi / (2 * lambdaParam k N r (t2Opt k N r))

/-- The maximal success probability `p_succ = 1/(4b)`, Eq. (25) of p. 10
(maximum of `(1/(4b)) sin²(λt)` at `t = π/(2λ)`). -/
noncomputable def pSucc (k N r : ℕ) : ℝ :=
  1 / (4 * bParam k N r (t2Opt k N r))

/-! ## Structural facts about the eigenangles -/

/-- Under `r < N`, the cosine of Eq. (19) is at most one. -/
theorem cosPhi_le_one (N r n : ℕ) (hrN : r < N) (hnN : n ≤ N) :
    cosPhi N r n ≤ 1 := by
  unfold cosPhi
  have hNr : (0 : ℝ) < (N : ℝ) - (r : ℝ) := by
    have h : (r : ℝ) < (N : ℝ) := by exact_mod_cast hrN
    linarith
  have hden : (0 : ℝ) < ((r : ℝ) + 1) * ((N : ℝ) - (r : ℝ)) := by positivity
  have hnN' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hnum : (0 : ℝ) ≤ 2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) := by nlinarith
  have hq : (0 : ℝ) ≤
      (2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1)) /
        (((r : ℝ) + 1) * ((N : ℝ) - (r : ℝ))) := div_nonneg hnum hden.le
  linarith

/-- Under the model hypotheses `0 ≤ n ≤ r`, `r < N`, `2r ≤ N`, the cosine of
Eq. (19) lies in `[-1, 1]`; hence `φ_n = arccos (cos φ_n)` is defined. -/
theorem cosPhi_mem_Icc (N r n : ℕ) (hnN : n ≤ N) (hnr : n ≤ r) (hrN : r < N)
    (h2r : 2 * r ≤ N) : cosPhi N r n ∈ Set.Icc (-1) 1 := by
  constructor
  · -- lower bound: `2n(N-n+1) ≤ 2(r+1)(N-r)` since the difference is
    -- `(r-n+1)(N-r-n)`.
    unfold cosPhi
    have hNr : (0 : ℝ) < (N : ℝ) - (r : ℝ) := by
      have h : (r : ℝ) < (N : ℝ) := by exact_mod_cast hrN
      linarith
    have hden : (0 : ℝ) < ((r : ℝ) + 1) * ((N : ℝ) - (r : ℝ)) := by positivity
    have hnr' : (n : ℝ) ≤ (r : ℝ) := by exact_mod_cast hnr
    have h2r' : 2 * (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2r
    have hfactor : ((r : ℝ) + 1) * ((N : ℝ) - (r : ℝ)) -
        (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) =
        (((r : ℝ) - (n : ℝ)) + 1) * ((N : ℝ) - (r : ℝ) - (n : ℝ)) := by ring
    have hnonneg : (0 : ℝ) ≤
        (((r : ℝ) - (n : ℝ)) + 1) * ((N : ℝ) - (r : ℝ) - (n : ℝ)) := by
      apply mul_nonneg
      · linarith
      · linarith
    have hkey : 2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) ≤
        2 * (((r : ℝ) + 1) * ((N : ℝ) - (r : ℝ))) := by
      nlinarith [hfactor, hnonneg]
    have hq : (2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1)) /
        (((r : ℝ) + 1) * ((N : ℝ) - (r : ℝ))) ≤ 2 := by
      rw [div_le_iff₀ hden]
      linarith
    linarith
  · exact cosPhi_le_one N r n hrN hnN

/-- With `r < N`, `n ≤ N`, `0 < n` the cosine of Eq. (19) is strictly below one,
so the eigenangle is strictly positive. -/
theorem phi_pos (N r n : ℕ) (hrN : r < N) (hnN : n ≤ N) (hn0 : 0 < n) :
    0 < phi N r n := by
  unfold phi
  apply Real.arccos_pos.mpr
  unfold cosPhi
  have hNr : (0 : ℝ) < (N : ℝ) - (r : ℝ) := by
    have h : (r : ℝ) < (N : ℝ) := by exact_mod_cast hrN
    linarith
  have hden : (0 : ℝ) < ((r : ℝ) + 1) * ((N : ℝ) - (r : ℝ)) := by positivity
  have hnN' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnum : (0 : ℝ) < 2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) := by nlinarith
  have hq : (0 : ℝ) <
      (2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1)) /
        (((r : ℝ) + 1) * ((N : ℝ) - (r : ℝ))) := div_pos hnum hden
  linarith

/-- With `-1 < cos φ_n`, the eigenangle is strictly below `π`. -/
theorem phi_lt_pi (N r n : ℕ) (h : -1 < cosPhi N r n) : phi N r n < Real.pi := by
  unfold phi
  exact Real.arccos_lt_pi.mpr h

/-- Under the non-degeneracy hypothesis `n < N - r`, the cosine of Eq. (19)
is strictly above `-1` (the difference `(r+1)(N-r) - n(N-n+1)` factors as
`(r-n+1)(N-r-n) > 0`). -/
theorem cosPhi_gt_neg_one (N r n : ℕ) (_hnN : n ≤ N) (hnr : n ≤ r) (hrN : r < N)
    (_h2r : 2 * r ≤ N) (hns : n < N - r) : -1 < cosPhi N r n := by
  unfold cosPhi
  have hNr : (0 : ℝ) < (N : ℝ) - (r : ℝ) := by
    have h : (r : ℝ) < (N : ℝ) := by exact_mod_cast hrN
    linarith
  have hden : (0 : ℝ) < ((r : ℝ) + 1) * ((N : ℝ) - (r : ℝ)) := by positivity
  have hns' : (n : ℝ) < (N : ℝ) - (r : ℝ) := by
    have hcast : ((N - r : ℕ) : ℝ) = (N : ℝ) - (r : ℝ) :=
      Nat.cast_sub (le_of_lt hrN)
    have hlt : (n : ℝ) < ((N - r : ℕ) : ℝ) := by exact_mod_cast hns
    rw [hcast] at hlt
    exact hlt
  have hnr' : (n : ℝ) ≤ (r : ℝ) := by exact_mod_cast hnr
  have hfactor : ((r : ℝ) + 1) * ((N : ℝ) - (r : ℝ)) -
      (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) =
      (((r : ℝ) - (n : ℝ)) + 1) * ((N : ℝ) - (r : ℝ) - (n : ℝ)) := by ring
  have hpos : (0 : ℝ) <
      (((r : ℝ) - (n : ℝ)) + 1) * ((N : ℝ) - (r : ℝ) - (n : ℝ)) := by
    apply mul_pos
    · linarith
    · linarith
  have hkey : (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) <
      ((r : ℝ) + 1) * ((N : ℝ) - (r : ℝ)) := by
    nlinarith [hfactor, hpos]
  have hq : (2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1)) /
      (((r : ℝ) + 1) * ((N : ℝ) - (r : ℝ))) < 2 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  linarith

/-- Under the model hypotheses the eigenangle lies in `(0, π)`. -/
theorem phi_mem_Ioo (N r n : ℕ) (hnN : n ≤ N) (hnr : n ≤ r) (hrN : r < N)
    (h2r : 2 * r ≤ N) (hn0 : 0 < n) (hns : n < N - r) :
    phi N r n ∈ Set.Ioo 0 Real.pi :=
  ⟨phi_pos N r n hrN hnN hn0,
   phi_lt_pi N r n (cosPhi_gt_neg_one N r n hnN hnr hrN h2r hns)⟩

/-- Under `0 < φ_k`, the exact optimal walk length `t₂ = π/φ_k` is positive. -/
theorem t2Opt_pos (k N r : ℕ) (hphi : 0 < phi N r k) : 0 < t2Opt k N r := by
  unfold t2Opt
  exact div_pos Real.pi_pos hphi

/-! ## The optimal `t₂` is the exact phase `π/φ_k` -/

/-- Definitional unfolding: `t₂ = π/φ_k`, Eq. (26). -/
theorem t2Opt_eq (k N r : ℕ) : t2Opt k N r = Real.pi / phi N r k := rfl

/-- `t₂ · φ_k = π` when the eigenangle does not vanish. -/
theorem t2Opt_mul_phi (k N r : ℕ) (hphi : phi N r k ≠ 0) :
    t2Opt k N r * phi N r k = Real.pi := by
  unfold t2Opt
  exact div_mul_cancel₀ Real.pi hphi

/-- At the optimal `t₂` the phase factor `cos (t₂ φ_k)` equals `-1`. -/
theorem cos_t2Opt_phase (k N r : ℕ) (hphi : phi N r k ≠ 0) :
    Real.cos (t2Opt k N r * phi N r k) = -1 := by
  rw [t2Opt_mul_phi k N r hphi, Real.cos_pi]

/-- The maximal success probability of Eq. (25)/(27): `p_succ = 1/(4b)`. -/
theorem pSucc_eq (k N r : ℕ) :
    pSucc k N r = 1 / (4 * bParam k N r (t2Opt k N r)) := rfl

/-! ## The asymptotic statement of Theorem 3.1 -/

/-- **Theorem 3.1 conclusion (p. 6), in asymptotic form.**

`r : ℕ → ℕ` is a sequence of Johnson-graph radii satisfying `r_N / N^{k/(k+1)} → 1`
(the paper takes `r` to be the integer nearest to `N^{k/(k+1)}`, Section 2.1,
p. 3).  The three components are Eqs. (26), (28), (27) of pp. 9–10:

* `t₂ = π/φ_k = π√r/(2√k) + O(1)`;
* `t₁ = π/(2λ) = (π/4)√r + O(r^{(k-2)/(2k)})`;
* `p_succ = 1 - O(r^{-1/k})`.
-/
def AsymptoticOptimal (k : ℕ) (r : ℕ → ℕ) : Prop :=
  (∃ C : ℝ, ∀ᶠ N in Filter.atTop,
    |t2Opt k N (r N) - Real.pi * Real.sqrt (r N) / (2 * Real.sqrt (k : ℝ))| ≤ C) ∧
  (∃ C : ℝ, ∀ᶠ N in Filter.atTop,
    |t1Opt k N (r N) - Real.pi / 4 * Real.sqrt (r N)| ≤
      C * (r N : ℝ) ^ (((k : ℝ) - 2) / (2 * (k : ℝ)))) ∧
  (∃ C : ℝ, ∀ᶠ N in Filter.atTop,
    |1 - pSucc k N (r N)| ≤ C * (r N : ℝ) ^ (-(1 / (k : ℝ))))

end Qatlib.Papers.ElemDistinct17.MainResults
