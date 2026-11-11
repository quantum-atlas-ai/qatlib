/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# VariationalNegativeMass — Proposition 4 tachyonic-mass bounds

Source: Jordan–Lee–Preskill, *Quantum Algorithms for Quantum Field Theories*,
fixed arXiv:1111.3633v1 (2011).

Proposition 4 (pp.25–27): let `H` be the lattice scalar-field Hamiltonian of Eq. 15,
`H = Σ_{x∈Ω} aᵈ [ ½π(x)² + ½(∇ₐφ)²(x) + (m₀²/2)φ(x)² + (λ₀/4!)φ(x)⁴ ]`.
If `m₀² ≤ 0` and `λ₀ > 0`, and `|ψ⟩` is any field state with `⟨ψ|H|ψ⟩ ≤ E`, then for
every lattice site `x`,

`⟨φ(x)²⟩ ≤ −24m₀²/λ₀ + √(36m₀⁴/λ₀² + 24/(λ₀aᵈ)(E + 3(V−aᵈ)m₀⁴/(2λ₀)))`   (Eq.51),

`⟨π(x)²⟩ ≤ (2/aᵈ)(E + 3V m₀⁴/(2λ₀))`                                         (Eq.52),

with `V` the physical volume (`V = aᵈ·|Ω|`).

The paper's proof computes the minimum `U_min = −3m₀⁴/(2λ₀)` of the local potential
`U(x) = (m₀²/2)φ² + (λ₀/4!)φ⁴` (Eqs.53–54), drops the positive terms of the energy
(Eqs.55–59) to isolate one site, applies Proposition 2 to get `⟨φ⁴⟩ ≥ ⟨φ²⟩²`
(Eq.61), and solves the resulting quadratic. The formalization keeps all these steps;
`quadratic_min` is Eq.54 (completing the square) and `sq_shift_le` is the algebraic
core of the quadratic formula (completing the square after scaling).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QFieldTheory11.MainResults.VariationalNegativeMass

/-- Fixed arXiv:1111.3633v1, Eq.54 (p.26): for `λ > 0`, the quadratic
`m s/2 + λ s²/24` is bounded below by `−3m²/(2λ)`, the minimum of the local potential
`U = (m₀²/2)φ² + (λ₀/4!)φ⁴` at `s = φ²`. Proved by completing the square
`m s/2 + λ s²/24 = (λ/24)(s + 6m/λ)² − 3m²/(2λ)`. -/
lemma quadratic_min {m lam : ℝ} (hl : 0 < lam) (s : ℝ) :
    -(3 * m ^ 2) / (2 * lam) ≤ m * s / 2 + lam * s ^ 2 / 24 := by
  have hlam : lam ≠ 0 := ne_of_gt hl
  have hkey : m * s / 2 + lam * s ^ 2 / 24
      = lam / 24 * (s + 6 * m / lam) ^ 2 - 3 * m ^ 2 / (2 * lam) := by
    field_simp [hlam]
    ring
  have hnonneg : 0 ≤ lam / 24 * (s + 6 * m / lam) ^ 2 := by positivity
  rw [hkey, neg_div]
  linarith

/-- Fixed arXiv:1111.3633v1, Eqs.60–61 (p.27): completing the square. If
`m s/2 + λ s²/24 ≤ e` with `λ > 0`, then
`(s + 6m/λ)² ≤ 36m²/λ² + 24e/λ`. This is the scaled quadratic that yields the
radicand of Eq.51. -/
lemma sq_shift_le {m lam s e : ℝ} (hl : 0 < lam)
    (hquad : m * s / 2 + lam * s ^ 2 / 24 ≤ e) :
    (s + 6 * m / lam) ^ 2 ≤ 36 * m ^ 2 / lam ^ 2 + 24 * e / lam := by
  have hlam : lam ≠ 0 := ne_of_gt hl
  have hlam2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam
  -- Scale the hypothesis by `24`.
  have h24 : 12 * m * s + lam * s ^ 2 ≤ 24 * e := by
    have hmul := mul_le_mul_of_nonneg_left hquad (show (0 : ℝ) ≤ 24 by norm_num)
    linarith [hmul]
  -- Divide by `lam`.
  have hdiv : (12 * m * s + lam * s ^ 2) / lam ≤ 24 * e / lam :=
    div_le_div_of_nonneg_right h24 hl.le
  have hkey : (s + 6 * m / lam) ^ 2
      = (12 * m * s + lam * s ^ 2) / lam + 36 * m ^ 2 / lam ^ 2 := by
    field_simp [hlam]
    ring
  rw [hkey]
  linarith

/-- Fixed arXiv:1111.3633v1, Proposition 4 (pp.25–27, Eqs.51–52). For a lattice
scalar-field Hamiltonian of Eq.15 with `m₀² ≤ 0` and `λ₀ > 0`, any state whose energy
expectation `⟨H⟩` (finite sum over sites of `aᵈ(½π² + ½(∇ₐφ)² + (m₀²/2)φ² + (λ₀/4!)φ⁴)`)
is at most `E` satisfies, at every site `x`, the Eq.51 bound on `⟨φ(x)²⟩` and the Eq.52
bound on `⟨π(x)²⟩`, with `V = aᵈ·|Ω|` the physical volume and `m₀⁴ = (m₀²)²`.

Hypotheses `hφ4sq` and `hCS` encode Prop.2 (`⟨φ(x)²⟩² ≤ ⟨φ(x)⁴⟩`), `hV` the volume
identity, and `hH` the energy cap. These are exactly the data used in the paper's
proof; no additional physical assumption is added. -/
theorem prop4_negative_mass_bounds
    {ι : Type*} [Fintype ι]
    (E a m0sq lam0 V : ℝ) (d : ℕ)
    (φ2 π2 grad2 φ4 : ι → ℝ)
    (ha : 0 < a) (hm : m0sq ≤ 0) (hl : 0 < lam0)
    (hφ2 : ∀ i, 0 ≤ φ2 i) (hπ2 : ∀ i, 0 ≤ π2 i)
    (hgrad2 : ∀ i, 0 ≤ grad2 i)
    (hCS : ∀ i, φ2 i ^ 2 ≤ φ4 i)
    (hV : V = (Fintype.card ι : ℝ) * a ^ d)
    (hH : ∑ i, a ^ d *
        (π2 i / 2 + grad2 i / 2 + m0sq * φ2 i / 2 + lam0 * φ4 i / 24) ≤ E)
    (x : ι) :
    φ2 x ≤ -24 * m0sq / lam0 +
        Real.sqrt (36 * m0sq ^ 2 / lam0 ^ 2 +
          24 * (E + 3 * (V - a ^ d) * m0sq ^ 2 / (2 * lam0)) / (lam0 * a ^ d)) ∧
    π2 x ≤ 2 / a ^ d * (E + 3 * V * m0sq ^ 2 / (2 * lam0)) := by
  classical
  set Umin : ℝ := -(3 * m0sq ^ 2) / (2 * lam0) with hUmin_def
  set U : ι → ℝ := fun i => m0sq * φ2 i / 2 + lam0 * φ4 i / 24 with hU_def
  set term : ι → ℝ := fun i =>
    a ^ d * (π2 i / 2 + grad2 i / 2 + U i) with hterm_def
  have hapos : 0 < a ^ d := pow_pos ha d
  have hπ2half : ∀ i, 0 ≤ π2 i / 2 := fun i => by linarith [hπ2 i]
  have hgrad2half : ∀ i, 0 ≤ grad2 i / 2 := fun i => by linarith [hgrad2 i]
  -- `∑ term i ≤ E` holds by hypothesis.
  have hsum_le : ∑ i, term i ≤ E := by
    simpa [hterm_def, hU_def, add_assoc] using hH
  -- Eq.54: each local potential is bounded below by `Umin`.
  have hUmin : ∀ i, Umin ≤ U i := by
    intro i
    have hs : 0 ≤ φ2 i := hφ2 i
    -- `φ⁴ ≥ (φ²)²` (Prop.2, Eq.61) so the potential dominates the quadratic in `s = φ²`.
    have hdom : m0sq * φ2 i / 2 + lam0 * (φ2 i) ^ 2 / 24 ≤ U i := by
      have h1 : lam0 * (φ2 i) ^ 2 / 24 ≤ lam0 * φ4 i / 24 := by
        apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 24)
        exact mul_le_mul_of_nonneg_left (hCS i) hl.le
      simp only [hU_def]
      linarith [h1]
    have hmin : Umin ≤ m0sq * φ2 i / 2 + lam0 * (φ2 i) ^ 2 / 24 := by
      have := quadratic_min (m := m0sq) (lam := lam0) hl (φ2 i)
      simpa only [hUmin_def] using this
    exact le_trans hmin hdom
  -- Every term dominates `aᵈ·Umin` (kinetic pieces are nonnegative).
  have hterm_Umin : ∀ i, a ^ d * Umin ≤ term i := by
    intro i
    have hUi : Umin ≤ U i := hUmin i
    have hkin : 0 ≤ π2 i / 2 + grad2 i / 2 := by linarith [hπ2half i, hgrad2half i]
    have h1 : a ^ d * Umin ≤ a ^ d * (π2 i / 2 + grad2 i / 2 + U i) := by
      apply mul_le_mul_of_nonneg_left _ hapos.le
      linarith
    simpa only [hterm_def] using h1
  -- The erased-site sum of `aᵈ·Umin`.
  have hcpos : 1 ≤ Fintype.card ι := by
    have := Fintype.card_pos_iff.2 ⟨x⟩
    omega
  have hcard : ((Finset.univ.erase x).card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Nat.cast_sub hcpos]
    norm_num
  have hsum_erase_const : ∑ i ∈ Finset.univ.erase x, (a ^ d * Umin)
      = ((Finset.univ.erase x).card : ℝ) * (a ^ d * Umin) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hsum_erase : ((Finset.univ.erase x).card : ℝ) * (a ^ d * Umin)
      ≤ ∑ i ∈ Finset.univ.erase x, term i := by
    rw [← hsum_erase_const]
    exact Finset.sum_le_sum (fun i _ => hterm_Umin i)
  -- `(card − 1)·aᵈ·Umin = (V − aᵈ)·Umin`.
  have herase_eq : ((Finset.univ.erase x).card : ℝ) * (a ^ d * Umin)
      = (V - a ^ d) * Umin := by
    rw [hcard, hV]
    ring
  have hsplit : term x + ∑ i ∈ Finset.univ.erase x, term i = ∑ i, term i :=
    Finset.add_sum_erase _ term (Finset.mem_univ x)
  -- Bound on `⟨π(x)²⟩` (Eq.52).
  have hπterm_x : a ^ d * (π2 x / 2 + Umin) ≤ term x := by
    have h1 : π2 x / 2 + Umin ≤ π2 x / 2 + grad2 x / 2 + U x := by
      linarith [hgrad2half x, hUmin x]
    have h2 := mul_le_mul_of_nonneg_left h1 hapos.le
    simpa only [hterm_def] using h2
  have hπ_energy : a ^ d * π2 x / 2 + V * Umin ≤ E := by
    have hcombine : a ^ d * (π2 x / 2 + Umin)
        + ((Finset.univ.erase x).card : ℝ) * (a ^ d * Umin) ≤ E := by
      calc a ^ d * (π2 x / 2 + Umin)
            + ((Finset.univ.erase x).card : ℝ) * (a ^ d * Umin)
          ≤ term x + ∑ i ∈ Finset.univ.erase x, term i := by
            exact add_le_add hπterm_x hsum_erase
        _ = ∑ i, term i := hsplit
        _ ≤ E := hsum_le
    have hrewrite : a ^ d * (π2 x / 2 + Umin)
        + ((Finset.univ.erase x).card : ℝ) * (a ^ d * Umin)
        = a ^ d * π2 x / 2 + V * Umin := by
      rw [herase_eq]; ring
    rwa [hrewrite] at hcombine
  have hπ_bound : π2 x ≤ 2 / a ^ d * (E + 3 * V * m0sq ^ 2 / (2 * lam0)) := by
    have hUmin_val : Umin = -(3 * m0sq ^ 2) / (2 * lam0) := hUmin_def
    have hkey : a ^ d * π2 x / 2 ≤ E - V * Umin := by linarith [hπ_energy]
    have hEval : E - V * Umin = E + 3 * V * m0sq ^ 2 / (2 * lam0) := by
      rw [hUmin_val]; ring
    rw [hEval] at hkey
    rw [div_mul_eq_mul_div, le_div_iff₀ hapos]
    nlinarith [hkey]
  -- Bound on `⟨φ(x)²⟩` (Eq.51).
  have hφterm_x : a ^ d * U x ≤ term x := by
    have hkin : 0 ≤ π2 x / 2 + grad2 x / 2 := by linarith [hπ2half x, hgrad2half x]
    have h1 : U x ≤ π2 x / 2 + grad2 x / 2 + U x := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hapos.le
    simpa only [hterm_def] using h2
  have hφ_energy : a ^ d * U x ≤ E + 3 * (V - a ^ d) * m0sq ^ 2 / (2 * lam0) := by
    have hcombine : a ^ d * U x + (V - a ^ d) * Umin ≤ E := by
      have h2 : a ^ d * U x + ((Finset.univ.erase x).card : ℝ) * (a ^ d * Umin) ≤ E := by
        calc a ^ d * U x + ((Finset.univ.erase x).card : ℝ) * (a ^ d * Umin)
            ≤ term x + ∑ i ∈ Finset.univ.erase x, term i := by
              exact add_le_add hφterm_x hsum_erase
          _ = ∑ i, term i := hsplit
          _ ≤ E := hsum_le
      rwa [herase_eq] at h2
    have hUmin_val : Umin = -(3 * m0sq ^ 2) / (2 * lam0) := hUmin_def
    have hEval : E - (V - a ^ d) * Umin = E + 3 * (V - a ^ d) * m0sq ^ 2 / (2 * lam0) := by
      rw [hUmin_val]; ring
    have : a ^ d * U x ≤ E - (V - a ^ d) * Umin := by linarith [hcombine]
    rwa [hEval] at this
  -- `U x` dominates the quadratic in `s = ⟨φ(x)²⟩` because `φ⁴ ≥ (φ²)²`.
  have hU_quad : m0sq * φ2 x / 2 + lam0 * (φ2 x) ^ 2 / 24 ≤ U x := by
    have h1 : lam0 * (φ2 x) ^ 2 / 24 ≤ lam0 * φ4 x / 24 := by
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 24)
      exact mul_le_mul_of_nonneg_left (hCS x) hl.le
    simp only [hU_def]
    linarith [h1]
  have hquad : m0sq * φ2 x / 2 + lam0 * (φ2 x) ^ 2 / 24
      ≤ (E + 3 * (V - a ^ d) * m0sq ^ 2 / (2 * lam0)) / a ^ d := by
    rw [le_div_iff₀ hapos]
    nlinarith [hU_quad, hφ_energy]
  -- Quadratic formula (Eqs.60–61).
  have hsq : (φ2 x + 6 * m0sq / lam0) ^ 2
      ≤ 36 * m0sq ^ 2 / lam0 ^ 2 +
        24 * ((E + 3 * (V - a ^ d) * m0sq ^ 2 / (2 * lam0)) / a ^ d) / lam0 :=
    sq_shift_le hl hquad
  have htight : φ2 x ≤ -6 * m0sq / lam0 +
      Real.sqrt (36 * m0sq ^ 2 / lam0 ^ 2 +
        24 * (E + 3 * (V - a ^ d) * m0sq ^ 2 / (2 * lam0)) / (lam0 * a ^ d)) := by
    have hσ : φ2 x + 6 * m0sq / lam0
        ≤ Real.sqrt (36 * m0sq ^ 2 / lam0 ^ 2 +
          24 * ((E + 3 * (V - a ^ d) * m0sq ^ 2 / (2 * lam0)) / a ^ d) / lam0) := by
      have h1 : φ2 x + 6 * m0sq / lam0 ≤ |φ2 x + 6 * m0sq / lam0| := le_abs_self _
      have h2 : |φ2 x + 6 * m0sq / lam0|
          = Real.sqrt ((φ2 x + 6 * m0sq / lam0) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      have h3 : Real.sqrt ((φ2 x + 6 * m0sq / lam0) ^ 2)
          ≤ Real.sqrt (36 * m0sq ^ 2 / lam0 ^ 2 +
            24 * ((E + 3 * (V - a ^ d) * m0sq ^ 2 / (2 * lam0)) / a ^ d) / lam0) :=
        Real.sqrt_le_sqrt hsq
      linarith
    -- Reassociate the factor `24·/aᵈ` into `24·/(λ₀ aᵈ)`.
    have harg : 24 * ((E + 3 * (V - a ^ d) * m0sq ^ 2 / (2 * lam0)) / a ^ d) / lam0
        = 24 * (E + 3 * (V - a ^ d) * m0sq ^ 2 / (2 * lam0)) / (lam0 * a ^ d) := by
      field_simp
    rw [harg] at hσ
    simp only [neg_mul, neg_div]
    linarith only [hσ]
  -- Paper's looser constant `−24m₀²/λ₀` (obtained by `−6m₀²/λ₀ ≤ −24m₀²/λ₀` since `m₀² ≤ 0`).
  have hweaken : -6 * m0sq / lam0
      ≤ -24 * m0sq / lam0 := by
    have : m0sq / lam0 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hm hl.le
    simp only [mul_div_assoc]
    linarith only [this]
  exact ⟨le_trans htight (add_le_add hweaken (le_refl _)), hπ_bound⟩

end Qatlib.Papers.QFieldTheory11.MainResults.VariationalNegativeMass
