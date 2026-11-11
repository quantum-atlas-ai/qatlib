/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZeroSumGames19.MainResults.GameModel.SourceGameModel

set_option backward.isDefEq.respectTransparency false

/-!
# ZeroSumGames19 — Lemma 12 (LP reduction tolerance)

Fixed source: arXiv:1904.03180v1, Lemma 12, pp.13–14.

Paper statement: finding the optimal value `λ*` of the game (6) up to additive
error `ε''' = ε/(6R(r+1))` suffices to correctly conclude either `OPT < α` or
`OPT ≥ α − ε` for the corresponding LP (4).

What is proved here:

* `epsilon_tolerance_eq` — the algebraic identity `6R(r+1)·ε''' = ε` from the
  paper's choice `ε''' = ε/(6R(r+1))`; proved.
* `lemma12_second_case_arithmetic` — the second half of the proof (p.14,
  equations (7)–(8)): the game strategy gives `bᵀy ≥ α − 6Rε'''` and weak duality
  with the dual optimum (`Σx* ≤ r`) gives `bᵀy ≤ OPT + 6Rrε'''`, hence
  `OPT ≥ α − ε`; proved.
* `source_lemma12` — the full two-case decision claim over `LPGameReduction`.
  The case-yields (`λ* > 0 ⇒ OPT < α` and the (7)–(8) strategy) are taken as
  hypotheses because the reduced matrices `A⁰⁰⁰` of game (6) are not
  constructed in this library; the accuracy arithmetic turning
  `|λ̂ − λ*| ≤ ε'''` into both case antecedents is proved.

Suggested continuation: define game (6) as a `Fin (n+3) × Fin (m+2)` matrix,
formalise `min_{y∈Δ} max_i (A⁰⁰⁰y)_i` by finite max/min over `Finset.univ`, and
prove the row-wise implications `A⁰⁰⁰y* ≤ λ*e`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ZeroSumGames19.MainResults.SdpDuality

open Qatlib.Papers.ZeroSumGames19.MainResults.GameModel

/-- Lemma 12, p.14: `ε''' = ε/(6R(r+1))` is exactly the tolerance with
    `6R(r+1)ε''' = ε`. -/
theorem epsilon_tolerance_eq {R r ε ε''' : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hεdef : ε''' = ε / (6 * R * (r + 1))) :
    6 * R * (r + 1) * ε''' = ε := by
  have hden : (6 : ℝ) * R * (r + 1) ≠ 0 := by positivity
  rw [hεdef]
  field_simp

/-- Lemma 12, p.14, second case, equations (7)–(8): if the game strategy gives
    `bᵀy ≥ α − 6Rε'''` and weak duality with a dual optimum of `Σx* ≤ r` gives
    `bᵀy ≤ OPT + 6Rrε'''`, then `OPT ≥ α − ε` for `ε''' = ε/(6R(r+1))`. -/
theorem lemma12_second_case_arithmetic {OPT α R r ε ε''' bTy : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r)
    (hεdef : ε''' = ε / (6 * R * (r + 1)))
    (hb : α - 6 * R * ε''' ≤ bTy)
    (hweak : bTy ≤ OPT + 6 * R * r * ε''') :
    α - ε ≤ OPT := by
  have hεeq : 6 * R * (r + 1) * ε''' = ε := epsilon_tolerance_eq hR hr hεdef
  have h : α - 6 * R * (r + 1) * ε''' ≤ OPT := by linarith
  rwa [hεeq] at h

/-- Lemma 12, pp.13-14 (decision logic).  The paper's two-case argument:
    with `epsT = eps/(6R(r+1))` and `|lamHat - lambdaStar| <= epsT`,
    * if `epsT < lamHat` then `lambdaStar > 0`, and the Gordan-alternative
      construction (`A'''y <= 0` impossible, built explicitly on p.14)
      gives `OPT < alpha`;
    * if `lamHat <= epsT` then `lambdaStar < 2 epsT`, and the approximate
      strategy of equations (7)-(8) gives `b^T y >= alpha - 6R epsT` together
      with weak duality `b^T y <= OPT + 6R r epsT`, hence `OPT >= alpha - eps`
      (`lemma12_second_case_arithmetic`, proved above).

    The two case-yields are taken as hypotheses here: the Gordan alternative
    and the (7)-(8) derivation require the explicit game (6) built from the
    LP (4), which is not constructed in this library (the `LPGameReduction`
    record only carries the numbers).  The decision arithmetic is proved. -/
theorem source_lemma12
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (data : LPGameReduction n m) (lamHat ε : ℝ)
    (hε : 0 < ε) (hR : 0 < data.R) (hr : 0 ≤ data.r)
    (hacc : |lamHat - data.lambdaStar| ≤ ε / (6 * data.R * (data.r + 1)))
    (hcase1 : 0 < data.lambdaStar → data.OPT < data.α)
    (hcase2 : data.lambdaStar ≤ 2 * (ε / (6 * data.R * (data.r + 1))) →
      ∃ bTy : ℝ, data.α - 6 * data.R * (ε / (6 * data.R * (data.r + 1))) ≤ bTy ∧
        bTy ≤ data.OPT + 6 * data.R * data.r * (ε / (6 * data.R * (data.r + 1)))) :
    (ε / (6 * data.R * (data.r + 1)) < lamHat → data.OPT < data.α) ∧
    (lamHat ≤ ε / (6 * data.R * (data.r + 1)) → data.α - ε ≤ data.OPT) := by
  constructor
  · intro hlarge
    apply hcase1
    have h := (abs_le.mp hacc).2
    linarith
  · intro hsmall
    have hstar : data.lambdaStar ≤ 2 * (ε / (6 * data.R * (data.r + 1))) := by
      have h := (abs_le.mp hacc).1
      linarith
    obtain ⟨bTy, hb, hweak⟩ := hcase2 hstar
    exact lemma12_second_case_arithmetic hR hr rfl hb hweak

end Qatlib.Papers.ZeroSumGames19.MainResults.SdpDuality
