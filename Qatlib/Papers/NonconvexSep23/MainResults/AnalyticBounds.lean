/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Tactic

@[expose] public section


/-!
# Conditional adiabatic tracking and analytic estimates

The closed analytic content of arXiv:2311.00811 as recorded in the legacy source.
Tracking estimates retain their explicit adiabatic and tensor hypotheses. They do
not establish the Schrödinger dynamics, ground-state construction or algorithm costs.
The inconsistent legacy double-well data are replaced by an unrestricted scalar
tracking constant wherever only that scalar was used by a closed proof.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Qatlib.Papers.NonconvexSep23.MainResults

/-- Model of the adiabatic evolution of §2.3: Hamiltonian `H(t)`, unit ground
family `|φ(t)⟩`, true propagator `U^ε`, adiabatic intertwiner `Ua^ε`, and the
rank-one ground projector `P(t)` together with eq. (2.13). -/
structure AdiabaticFamily (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- `H(t)` (bounded on the simulation domain `Ω`). -/
  H : ℝ → E →L[ℂ] E
  /-- the unit ground state `|φ(t)⟩`. -/
  phi : ℝ → E
  phi_unit : ∀ t, ‖phi t‖ = 1
  /-- the exact propagator `U^ε` (eq. 2.9). -/
  U : ℝ → E →L[ℂ] E
  /-- the adiabatic intertwiner `Ua^ε` (eq. 2.12). -/
  Ua : ℝ → E →L[ℂ] E
  /-- `Ua` is norm-preserving. -/
  Ua_norm : ∀ t x, ‖Ua t x‖ = ‖x‖
  /-- the ground projector `P(t)`. -/
  P : ℝ → E →L[ℂ] E
  /-- `P(t)` projects onto `ℂ · φ(t)`. -/
  P_apply : ∀ t x, P t x = inner (𝕜 := ℂ) (phi t) x • phi t
  /-- the intertwining identity (eq. 2.13). -/
  intertwine : ∀ t, (Ua t).comp (P 0) = (P t).comp (Ua t)

/-- eq. (3.8): every unit complex number is a global phase `e^{iα}`. -/
lemma unit_complex_eq_cexp (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ α : ℝ, Complex.exp (α * Complex.I) = z := by
  refine ⟨Complex.arg z, ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I z
  rw [hz] at h
  simpa using h

/-- If `x = c • φ` with `‖φ‖ = 1` and `‖x‖ = 1`, then `‖c‖ = 1`. -/
lemma coeff_norm_eq_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (φ x : E) (c : ℂ) (hφ : ‖φ‖ = 1) (hx : ‖x‖ = 1) (hc : x = c • φ) :
    ‖c‖ = 1 := by
  rw [hc, norm_smul, hφ, mul_one] at hx
  exact hx

/-- The intertwining identity (2.13) sends the initial ground state into the
ground line at every time: `P(t) (Ua(t) φ(0)) = Ua(t) φ(0)`. -/
lemma intertwine_ground {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (F : AdiabaticFamily E) (t : ℝ) :
    F.P t (F.Ua t (F.phi 0)) = F.Ua t (F.phi 0) := by
  have hcomp : (F.Ua t) (F.P 0 (F.phi 0)) = (F.P t) (F.Ua t (F.phi 0)) :=
    DFunLike.congr_fun (F.intertwine t) (F.phi 0)
  rw [← hcomp]
  have hP0 : F.P 0 (F.phi 0) = F.phi 0 := by
    rw [F.P_apply]
    have h1 : inner (𝕜 := ℂ) (F.phi 0) (F.phi 0) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, F.phi_unit 0]
      simp
    rw [h1, one_smul]
  rw [hP0]

/-! ## Lemma 5 (1D adiabatic tracking, eq. 3.7–3.8) -/

/-- Fixed arXiv:2311.00811, **Lemma 5** (§3.2, p.12), eqs. (3.7)–(3.8).
Let `w` be a well-formed asymmetric double well and `H(t) = Ĥ(λ(t))` on
`0 ≤ t ≤ log λ_f`. Let `ψ^ε(t) = U^ε(t) φ(0)` solve (2.9) from `|φ(0)⟩`, and let
`φ̃(t) = Ua^ε(t) φ(0)`. Then for all `0 ≤ t ≤ log λ_f`,
`‖ψ^ε(t) − φ̃(t)‖ ≤ ε θ t`, where `φ̃(t) = e^{i α(t)} φ(t)` differs from the
ground state by a global phase.

The adiabatic estimate `‖(U^ε − Ua^ε)φ(0)‖ ≤ εθt` is Theorem 3 of [16] (eq. 2.15),
supplied as `hAdiab` exactly as in the paper. The phase bookkeeping is proved. -/
theorem lemma5_adiabatic_tracking
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (θ : ℝ) (F : AdiabaticFamily E) (lamF ε : ℝ)
    (hAdiab : ∀ t ∈ Set.Icc 0 (Real.log lamF),
      ‖(F.U t - F.Ua t) (F.phi 0)‖ ≤ ε * θ * t) :
    ∀ t ∈ Set.Icc 0 (Real.log lamF),
      ∃ α : ℝ, F.Ua t (F.phi 0) = Complex.exp (α * Complex.I) • F.phi t ∧
        ‖F.U t (F.phi 0) - Complex.exp (α * Complex.I) • F.phi t‖ ≤ ε * θ * t := by
  intro t ht
  have hmem : F.Ua t (F.phi 0)
      = inner (𝕜 := ℂ) (F.phi t) (F.Ua t (F.phi 0)) • F.phi t := by
    have := F.P_apply t (F.Ua t (F.phi 0))
    rw [intertwine_ground F t] at this
    exact this
  have hphiNorm : ‖F.Ua t (F.phi 0)‖ = 1 := by rw [F.Ua_norm, F.phi_unit 0]
  have hc : ‖inner (𝕜 := ℂ) (F.phi t) (F.Ua t (F.phi 0))‖ = 1 :=
    coeff_norm_eq_one (F.phi t) (F.Ua t (F.phi 0)) _ (F.phi_unit t) hphiNorm hmem
  obtain ⟨α, hα⟩ := unit_complex_eq_cexp _ hc
  refine ⟨α, ?_, ?_⟩
  · rw [hα]; exact hmem
  · have hb := hAdiab t ht
    have hsub : (F.U t - F.Ua t) (F.phi 0) = F.U t (F.phi 0) - F.Ua t (F.phi 0) := by
      simp
    rw [hsub] at hb
    rw [hα, ← hmem]
    exact hb

/-! ## Proposition 6 (high-dimensional tracking, eq. 3.18) -/

/-- Fixed arXiv:2311.00811, **Proposition 6** (§3.3, p.14), eq. (3.18).
For `0 ≤ t ≤ log λ_f`, the solution `|Ψ^ε(t)⟩` of (2.9) governed by the separable
`H(t)` of (3.17) from `|Φ(0)⟩` satisfies `‖Ψ^ε(t) − Φ̃(t)‖ ≤ ε θ d t`, where
`Φ̃(t)` differs from the ground state `|Φ(t)⟩` by a global phase.

Proof route of the source: the `d`-dimensional dynamics factorises as a product
state (3.24)–(3.27); Lemma 5 applied to each of the `d` coordinates (3.26) followed
by the `d`-fold triangle inequality (3.28) gives the `εθdt` bound.

Lemmas `5` is applied coordinatewise (`hcoord`, the (3.26) input); the product-state
telescoping inequality (3.28) is carried as `hTensor` because Mathlib has no tensor
product of Hilbert spaces here. The `d`-fold summation step is proved. -/
theorem proposition6_adiabatic_tracking_highdim
    {E : Type*} [NormedAddCommGroup E]
    (θ : ℝ) (d : ℕ)
    (Ψ Φ : ℝ → E) (ψ φ : Fin d → ℝ → E) (ε lamF : ℝ)
    (hcoord : ∀ (k : Fin d) (t : ℝ), t ∈ Set.Icc 0 (Real.log lamF) →
      ‖ψ k t - φ k t‖ ≤ ε * θ * t)
    (hTensor : ∀ t, t ∈ Set.Icc 0 (Real.log lamF) →
      ‖Ψ t - Φ t‖ ≤ ∑ k : Fin d, ‖ψ k t - φ k t‖) :
    ∀ t ∈ Set.Icc 0 (Real.log lamF),
      ‖Ψ t - Φ t‖ ≤ ε * θ * (d : ℝ) * t := by
  intro t ht
  calc ‖Ψ t - Φ t‖ ≤ ∑ k : Fin d, ‖ψ k t - φ k t‖ := hTensor t ht
    _ ≤ ∑ _k : Fin d, ε * θ * t := Finset.sum_le_sum (fun k _ => hcoord k t ht)
    _ = (d : ℝ) * (ε * θ * t) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ε * θ * (d : ℝ) * t := by ring

/-- Lemma 9, eq. (4.5): the rescaled potential factor
`φ(s) = 1/(−εs + λ_f + 1/λ_f)²`. -/
def phiRescale (ε lamF s : ℝ) : ℝ := 1 / (-ε * s + lamF + 1 / lamF) ^ 2

/-- Fixed arXiv:2311.00811, **Lemma 9** (§4.3, p.17; proof Appendix C), eq. (4.5):
the effective potential factor satisfies `φ(s) ∈ [1/λ_f², λ_f²]` for
`s ∈ [1/(ελ_f), λ_f/ε]`.

This is the concrete, fully-verified content of (4.5); the operator-level identity
that `s ↦ Ψ(t(s))` solves (4.4) is `lemma9_time_rescaling` below. -/
lemma lemma9_effective_potential_range
    (lamF ε : ℝ) (hlamF : 0 < lamF) (hε : 0 < ε) :
    ∀ s ∈ Set.Icc (1 / (ε * lamF)) (lamF / ε),
      phiRescale ε lamF s ∈ Set.Icc (1 / lamF ^ 2) (lamF ^ 2) := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  rw [phiRescale]
  set A : ℝ := -ε * s + lamF + 1 / lamF with hA
  have hA1 : 1 / lamF ≤ A := by
    have h : ε * s ≤ lamF := by
      calc ε * s ≤ ε * (lamF / ε) := mul_le_mul_of_nonneg_left hs2 (le_of_lt hε)
        _ = lamF := by field_simp
    rw [hA]; linarith
  have hA2 : A ≤ lamF := by
    have h : 1 / lamF ≤ ε * s := by
      calc 1 / lamF = ε * (1 / (ε * lamF)) := by field_simp
        _ ≤ ε * s := mul_le_mul_of_nonneg_left hs1 (le_of_lt hε)
    rw [hA]; linarith
  have hApos : 0 < A := lt_of_lt_of_le (by positivity) hA1
  constructor
  · apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < A ^ 2)
    exact pow_le_pow_left₀ hApos.le hA2 2
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < A ^ 2)]
    have hsq : (1 / lamF) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (by positivity) hA1 2
    have heq : lamF ^ 2 * (1 / lamF) ^ 2 = 1 := by field_simp
    calc (1 : ℝ) = lamF ^ 2 * (1 / lamF) ^ 2 := heq.symm
      _ ≤ lamF ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)

/-- App. A, eq. (A.7): the tail of a geometric series with ratio `r ∈ (0, 1/2)` is
bounded by `2 r^{m+1}`. -/
lemma geometric_tail_bound (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1 / 2) (m : ℕ) :
    (∑' k : ℕ, r ^ (k + m + 1)) ≤ 2 * r ^ (m + 1) := by
  have hsum : (∑' k : ℕ, r ^ (k + m + 1)) = r ^ (m + 1) * (∑' k : ℕ, r ^ k) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    have hk : k + m + 1 = (m + 1) + k := by omega
    rw [hk, pow_add]
  rw [hsum, tsum_geometric_of_lt_one hr0 (by linarith : r < 1)]
  have hpos : 0 < 1 - r := by linarith
  have hdiv : r ^ (m + 1) * (1 - r)⁻¹ = r ^ (m + 1) / (1 - r) := by
    rw [div_eq_mul_inv]
  rw [hdiv, div_le_iff₀ hpos]
  have ha : 0 ≤ r ^ (m + 1) := pow_nonneg hr0 _
  have hfac : 0 ≤ 1 - 2 * r := by linarith
  nlinarith [mul_nonneg ha hfac]

/-- Fixed arXiv:2311.00811, **Lemma 10** (Appendix A, p.29), eq. (A.1).
Let `Ψ` be the exact solution of (2.16) and `Ψ̃` its truncation to Fourier
frequencies `≤ n/2`. From the periodic-analytic initial data the exact Fourier
coefficients satisfy `‖c_k(t)‖ ≤ r^k` with `0 < r < min(1/2, 1/(At))` (eq. A.6–A.7,
Cauchy's integral formula on the analyticity strip). Then
`max_{x,t} |Ψ(x,t) − Ψ̃(x,t)| ≤ 2 r^{n/2+1}` for every integer `n ≥ 1`.

`hcoef` is exactly the source's (A.7) coefficient bound (the periodic-analytic
input); `hΨ`, `hΨt` record the exact/truncated Fourier expansions (A.4). The
analyticity → coefficient-decay step (A.2)–(A.6) (Cauchy integral on the strip)
is carried by `hcoef`. The truncation-error step (A.5)–(A.7) is proved here by
splitting the summable Fourier series at `n/2+1`
(`Summable.sum_add_tsum_nat_add`), bounding the tail with
`norm_tsum_le_tsum_norm` and `‖exp(k x i)‖ = 1`, then applying the scalar
estimate `geometric_tail_bound`. -/
theorem lemma10_fourier_truncation
    (Ψ Ψt : ℝ → ℝ → ℂ) (c : ℝ → ℕ → ℂ) (n : ℕ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr : r < 1 / 2)
    (hΨ : ∀ x t, Ψ x t = ∑' k : ℕ, c t k * Complex.exp (k * x * Complex.I))
    (hcoef : ∀ t k, ‖c t k‖ ≤ r ^ k)
    (hΨt : ∀ x t, Ψt x t = ∑ k ∈ Finset.range (n / 2 + 1), c t k * Complex.exp (k * x * Complex.I)) :
    ∀ x t, ‖Ψ x t - Ψt x t‖ ≤ 2 * r ^ (n / 2 + 1) := by
  intro x t
  set m : ℕ := n / 2 + 1 with hm
  set e : ℕ → ℂ := fun k => c t k * Complex.exp (k * x * Complex.I) with he
  have hgeom : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_lt_one hr0 (by linarith)
  have hcoefnorm : ∀ k, ‖e k‖ ≤ r ^ k := by
    intro k
    rw [he]
    rw [norm_mul]
    have hexp : ‖Complex.exp ((k : ℂ) * (x : ℂ) * Complex.I)‖ = 1 := by
      rw [show ((k : ℂ) * (x : ℂ) * Complex.I)
          = (((k : ℝ) * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I ((k : ℝ) * x)
    rw [hexp, mul_one]
    exact hcoef t k
  have hsum : Summable e := hgeom.of_norm_bounded hcoefnorm
  have hsplit := hsum.sum_add_tsum_nat_add m
  have hdiff : (∑' k, e k) - (∑ k ∈ Finset.range m, e k) = ∑' k, e (k + m) := by
    rw [sub_eq_iff_eq_add, add_comm]
    exact hsplit.symm
  have hΨeq : Ψ x t = ∑' k, e k := by simpa [he] using hΨ x t
  have hΨteq : Ψt x t = ∑ k ∈ Finset.range m, e k := by
    rw [hΨt x t]
  rw [hΨeq, hΨteq, hdiff]
  have hgeom_shift : Summable (fun k : ℕ => r ^ (k + m)) :=
    (summable_nat_add_iff (f := fun k : ℕ => r ^ k) m).mpr hgeom
  have hbound_shift : ∀ k, ‖e (k + m)‖ ≤ r ^ (k + m) := fun k => hcoefnorm (k + m)
  have hbound_shift_abs : ∀ k, ‖(‖e (k + m)‖ : ℝ)‖ ≤ r ^ (k + m) := by
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hbound_shift k
  have hnorm_shift : Summable (fun k : ℕ => ‖e (k + m)‖) :=
    hgeom_shift.of_norm_bounded hbound_shift_abs
  calc ‖∑' k, e (k + m)‖
      ≤ ∑' k, ‖e (k + m)‖ := norm_tsum_le_tsum_norm hnorm_shift
    _ ≤ ∑' k, r ^ (k + m) := hnorm_shift.tsum_le_tsum hbound_shift hgeom_shift
    _ ≤ 2 * r ^ m := by
        simpa [m, Nat.add_assoc] using geometric_tail_bound r hr0 hr (n / 2)

/-- Fixed arXiv:2311.00811, **Lemma 14** (Appendix C, p.32), eqs. (C.1)–(C.2).
If `ψ₁, ψ₂` are unit vectors with `‖ψ₁ − ψ₂‖ ≤ δ` and `O` is a bounded operator
with `‖O‖ ≤ 1`, then `|⟨ψ₁|O|ψ₁⟩ − ⟨ψ₂|O|ψ₂⟩| ≤ 2δ`.

Fully proved by the paper's triangle-inequality split
`⟨ψ₁|O|ψ₁⟩ − ⟨ψ₂|O|ψ₂⟩ = ⟨ψ₁−ψ₂|O|ψ₁⟩ + ⟨ψ₂|O(ψ₁−ψ₂)⟩` followed by
Cauchy–Schwarz and `‖O‖ ≤ 1`. -/
theorem lemma14_observable_perturbation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ₁ ψ₂ : E) (h1 : ‖ψ₁‖ = 1) (h2 : ‖ψ₂‖ = 1) (δ : ℝ)
    (hδ : ‖ψ₁ - ψ₂‖ ≤ δ)
    (O : E →L[ℂ] E) (hO : ‖O‖ ≤ 1) :
    ‖inner (𝕜 := ℂ) ψ₁ (O ψ₁) - inner (𝕜 := ℂ) ψ₂ (O ψ₂)‖ ≤ 2 * δ := by
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hδ
  have hOψ1 : ‖O ψ₁‖ ≤ 1 := by
    calc ‖O ψ₁‖ ≤ ‖O‖ * ‖ψ₁‖ := O.le_opNorm _
      _ = ‖O‖ := by rw [h1, mul_one]
      _ ≤ 1 := hO
  have hOψd : ‖O (ψ₁ - ψ₂)‖ ≤ δ := by
    calc ‖O (ψ₁ - ψ₂)‖ ≤ ‖O‖ * ‖ψ₁ - ψ₂‖ := O.le_opNorm _
      _ ≤ 1 * δ := mul_le_mul hO hδ (norm_nonneg _) (by linarith [norm_nonneg O])
      _ = δ := one_mul δ
  have hsplit : inner (𝕜 := ℂ) ψ₁ (O ψ₁) - inner (𝕜 := ℂ) ψ₂ (O ψ₂)
      = inner (𝕜 := ℂ) (ψ₁ - ψ₂) (O ψ₁) + inner (𝕜 := ℂ) ψ₂ (O (ψ₁ - ψ₂)) := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  rw [hsplit]
  have hA : ‖inner (𝕜 := ℂ) (ψ₁ - ψ₂) (O ψ₁)‖ ≤ δ := by
    calc ‖inner (𝕜 := ℂ) (ψ₁ - ψ₂) (O ψ₁)‖ ≤ ‖ψ₁ - ψ₂‖ * ‖O ψ₁‖ := norm_inner_le_norm _ _
      _ ≤ δ * 1 := mul_le_mul hδ hOψ1 (norm_nonneg _) hδ0
      _ = δ := mul_one δ
  have hB : ‖inner (𝕜 := ℂ) ψ₂ (O (ψ₁ - ψ₂))‖ ≤ δ := by
    calc ‖inner (𝕜 := ℂ) ψ₂ (O (ψ₁ - ψ₂))‖ ≤ ‖ψ₂‖ * ‖O (ψ₁ - ψ₂)‖ := norm_inner_le_norm _ _
      _ = ‖O (ψ₁ - ψ₂)‖ := by rw [h2, one_mul]
      _ ≤ δ := hOψd
  calc ‖inner (𝕜 := ℂ) (ψ₁ - ψ₂) (O ψ₁) + inner (𝕜 := ℂ) ψ₂ (O (ψ₁ - ψ₂))‖
      ≤ ‖inner (𝕜 := ℂ) (ψ₁ - ψ₂) (O ψ₁)‖ + ‖inner (𝕜 := ℂ) ψ₂ (O (ψ₁ - ψ₂))‖ :=
        norm_add_le _ _
    _ ≤ δ + δ := add_le_add hA hB
    _ = 2 * δ := by ring


end Qatlib.Papers.NonconvexSep23.MainResults
