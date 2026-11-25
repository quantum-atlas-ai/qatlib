/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampling25.MainResults.Mcmi.McmiDecay

@[expose] public section

/-!
# Theorem 2.3 from Lemma D.1

`Qatlib.Papers.GibbsSampling25.MainResults.Mcmi.uniform_mcmi_decay` records
Theorem 2.3 of arXiv:2412.01732v1 (p.4, eq. (3)) as a predicate: the
matrix-valued conditional mutual information decays like
`K |Λ| exp (-dist (A, C) / ξ)`. The source derives it from Lemma D.1
(arXiv:2412.01732v1, p.46, eq. (73)), which bounds the same quantity by
`4 min {|A|, |C|} Δ exp (-μ dist (A, C))` for a strong local effective
Hamiltonian with interaction-norm bound `Δ` and decay `μ`.

This file discharges that final step: since `min {|A|, |C|} ≤ |A| ≤ |Λ|`, the
Lemma D.1 estimate implies the uniform bound with prefactor `K = max (4Δ) 1`
and decay length `ξ = 1 / μ`, so it yields the predicate
`uniform_mcmi_decay` of the published model.

The Lemma D.1 estimate itself is an explicit hypothesis `hD1`, stated in the
form of `Qatlib.Papers.GibbsSampling25.MainResults.Mcmi.mcmi_decay_from_effective_hamiltonian`
with the effective Hamiltonian and its constants universally quantified. What
is proved here is the reduction of Theorem 2.3 to Lemma D.1; a proof of
Lemma D.1 from the locality of the effective Hamiltonian is not part of this
file, and the matrix-level MCMI remains an interface datum of the source model.

## Main statements

* `mcmi_decay_prefactor_bound`: the arithmetic core, `4 min |A| |C| Δ ≤ K |Λ|`.
* `uniform_mcmi_decay_of_lemmaD1`: Theorem 2.3 follows from the Lemma D.1
  estimate.

## References

* arXiv:2412.01732v1, Theorem 2.3 (p.4, eq. (3)) and Lemma D.1 (p.46, eq. (73)).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.GibbsSampling25.MainResults.Mcmi

open Qatlib.Papers.GibbsSampling25.MainResults.Model
open Qatlib.Papers.GibbsSampling25.MainResults.Mcmi

variable {Λ : Type} [Fintype Λ] [DecidableEq Λ]

omit [DecidableEq Λ] in
/-- The arithmetic core of the derivation of Theorem 2.3 from Lemma D.1: the
prefactor `4 * min {|A|, |C|} * Δ` of the Lemma D.1 estimate is dominated by
`max (4Δ) 1 * |Λ|`, because `min {|A|, |C|} ≤ |A| ≤ |Λ|` and both factors are
non-negative. -/
theorem mcmi_decay_prefactor_bound (Δ : ℝ) (hΔ : 0 ≤ Δ) (A C : Finset Λ) :
    4 * (min A.card C.card : ℝ) * Δ ≤ max (4 * Δ) 1 * (Fintype.card Λ : ℝ) := by
  have hcard : (min A.card C.card : ℝ) ≤ (Fintype.card Λ : ℝ) := by
    have h : min A.card C.card ≤ Fintype.card Λ :=
      le_trans (min_le_left _ _) (Finset.card_le_univ A)
    exact_mod_cast h
  have hK : (4 * Δ : ℝ) ≤ max (4 * Δ) 1 := le_max_left _ _
  calc 4 * (min A.card C.card : ℝ) * Δ = (min A.card C.card : ℝ) * (4 * Δ) := by ring
    _ ≤ (Fintype.card Λ : ℝ) * max (4 * Δ) 1 :=
        mul_le_mul hcard hK (by linarith) (by positivity)
    _ = max (4 * Δ) 1 * (Fintype.card Λ : ℝ) := by ring

/-- **Theorem 2.3** of arXiv:2412.01732v1 (p.4, eq. (3)), derived from
Lemma D.1 as in `Qatlib.Papers.GibbsSampling25.MainResults.Mcmi.uniform_mcmi_decay`.
If `H_Λ` admits a strong local effective Hamiltonian with interaction-norm bound
`Δ` and decay `μ` (`hEff`), and Lemma D.1 applies in the form
`‖H_σ(A:C|D)‖∞ ≤ 4 min {|A|, |C|} Δ exp (-μ dist (A, C))` for every such choice
(`hD1`), then the MCMI decays uniformly,

`‖H_σ(A:C|D)‖∞ ≤ K |Λ| exp (-dist (A, C) / ξ)` with `K = max (4Δ) 1`,
`ξ = 1 / μ`.

The `(κ, r)`-locality, `J`-boundedness and growth constant `g` enter only
through the existence of the strong local effective Hamiltonian, exactly as in
the published predicate `uniform_mcmi_decay`, and are unused here. -/
theorem uniform_mcmi_decay_of_lemmaD1 (dist : Λ → Λ → ℝ) (J r κ g β : ℝ)
    (hJ : 0 ≤ J) (hr : 0 < r) (hκ : 0 ≤ κ) (hg : 0 < g) (mcmi : McmiNorm Λ)
    (hEff : ∃ (hterm : Finset Λ → Finset Λ → ℝ) (Δ μ : ℝ), 0 ≤ Δ ∧ 0 < μ ∧
      IsStrongLocalEffectiveHamiltonian mcmi hterm Δ μ)
    (hD1 : ∀ (hterm : Finset Λ → Finset Λ → ℝ) (Δ μ : ℝ), 0 ≤ Δ → 0 < μ →
      IsStrongLocalEffectiveHamiltonian mcmi hterm Δ μ →
      ∀ A C Dd : Finset Λ,
        mcmi A C Dd ≤ 4 * (min A.card C.card : ℝ) * Δ *
          Real.exp (- μ * setDistOf dist A C)) :
    uniform_mcmi_decay dist J r κ g β hJ hr hκ hg mcmi hEff := by
  obtain ⟨hterm, Δ, μ, hΔ, hμ, hSL⟩ := hEff
  refine ⟨max (4 * Δ) 1, 1 / μ, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    one_div_pos.mpr hμ, ?_⟩
  intro A C Dd
  have hb := hD1 hterm Δ μ hΔ hμ hSL A C Dd
  have hpre := mcmi_decay_prefactor_bound Δ hΔ A C
  have hexp : Real.exp (- μ * setDistOf dist A C)
      = Real.exp (- setDistOf dist A C / (1 / μ)) := by
    have h1 : (1 : ℝ) / μ = μ⁻¹ := one_div μ
    congr 1
    rw [h1, div_inv_eq_mul]
    ring
  calc mcmi A C Dd
      ≤ 4 * (min A.card C.card : ℝ) * Δ * Real.exp (- μ * setDistOf dist A C) := hb
    _ ≤ (max (4 * Δ) 1 * (Fintype.card Λ : ℝ)) *
          Real.exp (- μ * setDistOf dist A C) :=
        mul_le_mul_of_nonneg_right hpre (Real.exp_pos _).le
    _ = max (4 * Δ) 1 * (Fintype.card Λ : ℝ) *
          Real.exp (- setDistOf dist A C / (1 / μ)) := by
        rw [hexp]

end Qatlib.Papers.GibbsSampling25.MainResults.Mcmi
