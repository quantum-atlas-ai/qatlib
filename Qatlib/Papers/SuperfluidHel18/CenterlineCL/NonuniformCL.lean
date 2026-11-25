/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.GaussLinking
public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.WritheGeometry
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Non-uniform circulation normalization and geometric writhe suppression

[Kedia2018SuperfluidHelicity], Section V, Eqs. (7)–(8),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
This module extends the equal-circulation classical-limit theorem of
`Qatlib.Papers.SuperfluidHel18.CenterlineCL.ClassicalLimit` in two directions.

First, the self term is no longer an abstract real input: the writhe of each filament is
the actual self Gauss integral `gaussLinking (γ i) (γ i)` of the given centerline, with an
explicit integrability hypothesis (dischargeable for simple regular `C²` curves by
`writheKernel_integrable_of_regular` in `KernelBounds`) so that the integral is genuine
rather than a junk value of the Bochner extension.

Second, the circulations `κ i` may vary in size and sign. If the total circulation is
nonzero, the rescaled self term is controlled by the *inverse effective bundle size*
`(∑ i, κ i²) / (∑ i, κ i)²`. If `|κ i| ≤ K`, this factor is at most
`K * (∑ i, |κ i|) / (∑ i, κ i)²`. For nonnegative circulations it is at most
`K / (∑ i, κ i)`, and for comparable positive circulations in `[c, C]` at most `C / (n c)`.
Equal nonzero circulations recover exactly `1/n`, the `O(1/N)` suppression of Eq. (7).

The main limit theorem keeps the convergence of the rescaled off-diagonal pairing as an
explicit hypothesis: it is *not* assumed proved, and no Euler helicity value is fed in as
a limit. The suppression strength enters through a sequence `s n → 0` dominating the
stage-`n` inverse effective bundle size. Vortex dynamics, reconnection and the
identification of the pairing limit with a Biot–Savart helicity remain outside.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.SuperfluidHel18.VanishCharge
open MeasureTheory
open Filter
open scoped BigOperators Topology

/-- The writhe of a closed centerline as the actual self Gauss integral. The integral is
a genuine writhe whenever the self kernel is integrable, e.g. for simple regular `C²`
curves; without integrability the Bochner integral evaluates to `0` by convention, which
the explicit integrability hypotheses of the results below exclude. -/
noncomputable def gaussWrithe (γ : ℝ → (Fin 3 → ℝ)) : ℝ :=
  gaussLinking γ γ

/-- The self (writhe) part of centerline helicity built from actual self Gauss integrals
of the centerlines, weighted by squared circulations. -/
noncomputable def writheGaussPart {ι : Type*} [Fintype ι] (κ : ι → ℝ)
    (γ : ι → ℝ → (Fin 3 → ℝ)) : ℝ :=
  ∑ i, κ i ^ 2 * gaussWrithe (γ i)

/-- The centerline helicity of a geometric bundle whose self term is the actual self Gauss
integral of each centerline: no real-number writhe input remains. -/
noncomputable def centerlineHelicityGaussSelf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → ℝ) (γ : ι → ℝ → (Fin 3 → ℝ)) : ℝ :=
  centerlineHelicityGauss κ γ (fun i => gaussWrithe (γ i))

/-- The geometric self-term assembly splits into the off-diagonal Gauss pairing sum plus
the actual writhe sum, the non-uniform-circulation form of Eq. (6) of the paper. -/
theorem centerlineHelicityGaussSelf_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → ℝ) (γ : ι → ℝ → (Fin 3 → ℝ)) :
    centerlineHelicityGaussSelf κ γ
      = pairLinkingGauss κ γ + writheGaussPart κ γ := by
  simp [centerlineHelicityGaussSelf, centerlineHelicityGauss_eq, writheGaussPart,
    writhePart]

/-- Uniform writhe bound for actual self Gauss integrals: the self part is at most `W`
times the sum of squared circulations. Non-uniform circulations are allowed; the bound
is pure summation algebra once each actual writhe is bounded in absolute value. -/
theorem abs_writheGaussPart_le {ι : Type*} [Fintype ι] (κ : ι → ℝ)
    (γ : ι → ℝ → (Fin 3 → ℝ)) {W : ℝ}
    (hwr : ∀ i, |gaussWrithe (γ i)| ≤ W) :
    |writheGaussPart κ γ| ≤ W * ∑ i, κ i ^ 2 := by
  have h1 : |∑ i, κ i ^ 2 * gaussWrithe (γ i)| ≤ ∑ i, |κ i ^ 2 * gaussWrithe (γ i)| :=
    Finset.abs_sum_le_sum_abs _ Finset.univ
  have h2 : ∑ i, |κ i ^ 2 * gaussWrithe (γ i)| ≤ ∑ i, κ i ^ 2 * W := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg (κ i))]
    exact mul_le_mul_of_nonneg_left (hwr i) (sq_nonneg (κ i))
  have h3 : ∑ i, κ i ^ 2 * W = W * ∑ i, κ i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm (κ i ^ 2) W
  exact h1.trans (h2.trans h3.le)

/-- Rescaled writhe suppression with actual Gauss geometry and non-uniform circulations:
after division by the squared total circulation, the self part is at most `W` times the
inverse effective bundle size `(∑ κ i²) / (∑ κ i)²`. -/
theorem rescaled_writheGaussPart_le {ι : Type*} [Fintype ι] (κ : ι → ℝ)
    (γ : ι → ℝ → (Fin 3 → ℝ)) {W : ℝ} (hκ : ∑ i, κ i ≠ 0)
    (hwr : ∀ i, |gaussWrithe (γ i)| ≤ W) :
    |writheGaussPart κ γ| / (∑ i, κ i) ^ 2
      ≤ W * ((∑ i, κ i ^ 2) / (∑ i, κ i) ^ 2) := by
  have hpos : (0 : ℝ) < (∑ i, κ i) ^ 2 := sq_pos_of_ne_zero hκ
  have h := abs_writheGaussPart_le κ γ hwr
  rw [show W * ((∑ i, κ i ^ 2) / (∑ i, κ i) ^ 2)
      = (W * ∑ i, κ i ^ 2) / (∑ i, κ i) ^ 2 from by ring,
    div_le_div_iff₀ hpos hpos]
  exact mul_le_mul_of_nonneg_right h (sq_nonneg _)

/-- The sum of squared circulations is at most a uniform circulation modulus bound `K`
times the sum of moduli. For signed circulations, divide by the squared nonzero total
without replacing that total by the sum of moduli. -/
theorem sum_sq_le_of_abs_le {ι : Type*} [Fintype ι] (κ : ι → ℝ) {K : ℝ}
    (hK : ∀ i, |κ i| ≤ K) :
    ∑ i, κ i ^ 2 ≤ K * ∑ i, |κ i| := by
  have hmono : ∀ i, κ i ^ 2 ≤ K * |κ i| := by
    intro i
    have hsq : κ i ^ 2 = |κ i| * |κ i| := by
      rw [← sq_abs (κ i), pow_two]
    rw [hsq]
    exact mul_le_mul_of_nonneg_right (hK i) (abs_nonneg _)
  calc ∑ i, κ i ^ 2 ≤ ∑ i, K * |κ i| := Finset.sum_le_sum fun i _ => hmono i
    _ = K * ∑ i, |κ i| := by rw [Finset.mul_sum]

/-- For nonnegative circulations bounded above by `K`, the inverse effective bundle size
is at most `K` divided by the total circulation: the suppression factor is small exactly
when no single vortex carries a positive fraction of the total circulation. -/
theorem selfWeight_le_of_le {ι : Type*} [Fintype ι] (κ : ι → ℝ) {K : ℝ}
    (hk : ∀ i, 0 ≤ κ i) (hK : ∀ i, κ i ≤ K) (hκ : ∑ i, κ i ≠ 0) :
    (∑ i, κ i ^ 2) / (∑ i, κ i) ^ 2 ≤ K / (∑ i, κ i) := by
  have hpos : (0 : ℝ) < ∑ i, κ i :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => hk i) fun h => hκ h.symm
  have habs : ∀ i, |κ i| ≤ K := by
    intro i
    rw [abs_of_nonneg (hk i)]
    exact hK i
  have hsumabs : ∑ i, |κ i| = ∑ i, κ i :=
    Finset.sum_congr rfl fun i _ => abs_of_nonneg (hk i)
  have h1 : ∑ i, κ i ^ 2 ≤ K * ∑ i, κ i := by
    calc ∑ i, κ i ^ 2 ≤ K * ∑ i, |κ i| := sum_sq_le_of_abs_le κ habs
      _ = K * ∑ i, κ i := by rw [hsumabs]
  rw [div_le_div_iff₀ (sq_pos_of_ne_zero hκ) hpos]
  calc (∑ i, κ i ^ 2) * ∑ i, κ i ≤ (K * ∑ i, κ i) * ∑ i, κ i :=
        mul_le_mul_of_nonneg_right h1 hpos.le
    _ = K * (∑ i, κ i) ^ 2 := by ring

/-- Comparable positive circulations: if every circulation of an `n`-filament bundle lies
in `[c, C]` with `0 < c`, the inverse effective bundle size is at most `C / (n c)`, the
quantitative `O(1/N)` suppression for non-uniform but comparable bundles. -/
theorem selfWeight_le_of_comparable {n : ℕ} (κ : Fin n → ℝ) {c C : ℝ} (hc : 0 < c)
    (hlow : ∀ i, c ≤ κ i) (hhigh : ∀ i, κ i ≤ C) (hκ : ∑ i, κ i ≠ 0) :
    (∑ i, κ i ^ 2) / (∑ i, κ i) ^ 2 ≤ C / ((n : ℝ) * c) := by
  have hnn : ∀ i, 0 ≤ κ i := fun i => hc.le.trans (hlow i)
  have hsumpos : (0 : ℝ) < ∑ i, κ i :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => hnn i) fun h => hκ h.symm
  have hn : n ≠ 0 := by
    intro hn0
    subst hn0
    simp at hκ
  have h1 := selfWeight_le_of_le κ hnn hhigh hκ
  have hC : (0 : ℝ) ≤ C := by
    have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    exact hc.le.trans ((hlow i0).trans (hhigh i0))
  have hsum : (n : ℝ) * c ≤ ∑ i, κ i := by
    calc (n : ℝ) * c = ∑ i : Fin n, c := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i, κ i := Finset.sum_le_sum fun i _ => hlow i
  have hnc : (0 : ℝ) < (n : ℝ) * c := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hc
  refine le_trans h1 ?_
  rw [div_le_div_iff₀ hsumpos hnc]
  exact mul_le_mul_of_nonneg_left hsum hC

/-- Equal circulations recover exactly the inverse bundle size: the inverse effective
bundle size of `n` equal filaments is `1/n`, the `O(1/N)` power of Eq. (7) of the
paper. -/
theorem selfWeight_const_eq_inv_card {n : ℕ} (hn : n ≠ 0) (κ₀ : ℝ) (hκ₀ : κ₀ ≠ 0) :
    (∑ _ : Fin n, κ₀ ^ 2) / (∑ _ : Fin n, κ₀) ^ 2 = 1 / (n : ℝ) := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow]
  field_simp

/-- The rescaled geometric centerline helicity differs from the rescaled off-diagonal
pairing by the suppressed actual writhe term; the strength is the inverse effective
bundle size. Integrability of each self kernel makes the writhes genuine. -/
theorem rescaled_centerlineGaussSelf_near_linking {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → ℝ) (γ : ι → ℝ → (Fin 3 → ℝ)) {W : ℝ} (hκ : ∑ i, κ i ≠ 0)
    (_hint : ∀ i, Integrable (fun p : ℝ × ℝ => writheKernel (γ i) p.1 p.2) gaussMeasure)
    (hwr : ∀ i, |gaussWrithe (γ i)| ≤ W) :
    |centerlineHelicityGaussSelf κ γ / (∑ i, κ i) ^ 2
        - pairLinkingGauss κ γ / (∑ i, κ i) ^ 2|
      ≤ W * ((∑ i, κ i ^ 2) / (∑ i, κ i) ^ 2) := by
  rw [centerlineHelicityGaussSelf_eq, add_div, add_sub_cancel_left, abs_div,
    abs_of_pos (sq_pos_of_ne_zero hκ)]
  exact rescaled_writheGaussPart_le κ γ hκ hwr

/-- The non-uniform geometric classical limit (Eq. (8) of the paper, non-uniform form).
Suppose each stage of a bundle sequence (a bundle of `n + 1` filaments at stage `n`)
carries genuine (integrable) self Gauss writhes bounded by `W`, and the stage-`n`
inverse effective bundle size is dominated by a sequence `s n → 0` (e.g. `2 / (n + 1)`
for circulations comparable within a factor two). If the rescaled off-diagonal Gauss
pairings converge to `H`, then the rescaled centerline helicities converge to the same
`H`.

The convergence of the pairing to `H` is a *hypothesis*: this theorem does not prove it,
does not identify `H` with any Euler or Biot–Savart helicity, and uses no vortex
dynamics. The suppression strength is exactly the effective-size sequence, separating
what is proved (writhe suppression, abstract convergence transfer) from what is assumed
(off-diagonal pairing convergence). -/
theorem classical_limit_nonuniform {W : ℝ} (hW : 0 ≤ W)
    (s h ch : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0))
    (H : ℝ) (hh : Tendsto h atTop (𝓝 H))
    (hch : ∀ n : ℕ, ∃ (κ : Fin (n + 1) → ℝ) (γ : Fin (n + 1) → ℝ → (Fin 3 → ℝ)),
      (∑ i, κ i ≠ 0) ∧
        (∀ i, Integrable (fun p : ℝ × ℝ => writheKernel (γ i) p.1 p.2) gaussMeasure) ∧
        (∀ i, |gaussWrithe (γ i)| ≤ W) ∧
        ((∑ i, κ i ^ 2) / (∑ i, κ i) ^ 2 ≤ s n) ∧
        (ch n = centerlineHelicityGaussSelf κ γ / (∑ i, κ i) ^ 2) ∧
        (h n = pairLinkingGauss κ γ / (∑ i, κ i) ^ 2)) :
    Tendsto ch atTop (𝓝 H) := by
  have hWs : Tendsto (fun n : ℕ => W * s n) atTop (𝓝 0) := by
    have hmul : Tendsto (fun n : ℕ => W * s n) atTop (𝓝 (W * 0)) :=
      Tendsto.mul tendsto_const_nhds hs
    simpa using hmul
  have habs : Tendsto (fun n => |ch n - h n|) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) hWs
    obtain ⟨κ, γ, hκ, _hint, hwr, hsize, hchn, hhn⟩ := hch n
    have hsplit := rescaled_centerlineGaussSelf_near_linking κ γ hκ _hint hwr
    rw [← hchn, ← hhn] at hsplit
    calc |ch n - h n| ≤ W * ((∑ i, κ i ^ 2) / (∑ i, κ i) ^ 2) := hsplit
      _ ≤ W * s n := mul_le_mul_of_nonneg_left hsize hW
  have hdiff : Tendsto (fun n => ch n - h n) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero fun n => ch n - h n).mpr habs
  have hgoaleq : ch = fun n => (ch n - h n) + h n := by funext n; ring
  have hfin : Tendsto (fun n : ℕ => (ch n - h n) + h n) atTop (𝓝 (0 + H)) := hdiff.add hh
  rw [hgoaleq]
  simpa using hfin

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
