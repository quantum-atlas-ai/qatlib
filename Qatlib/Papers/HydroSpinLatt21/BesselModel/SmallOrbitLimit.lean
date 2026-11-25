/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.BesselModel.GkTrajectory
public import Qatlib.Papers.HydroSpinLatt21.BesselModel.SmallOrbitMemory
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Joint small-orbit and low-memory limit

[Saenz2021HydroSpinLattices], Methods equations (12)–(26),
[DOI](https://doi.org/10.1038/s41586-021-03682-1).
At fixed mass, spacing, wavenumber, force prefactor, and Rayleigh
parameters, the target generalized Kuramoto field is independent of
radius. A family of Bessel-history trajectories with common speed
bounds and convergent initial data converges uniformly to a generalized
Kuramoto trajectory on a fixed time interval as radius and memory time
both tend to zero. The comparison assumes the trajectories exist.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.HydroSpinLatt21.BesselModel

open Set Filter
open scoped NNReal Topology

/-- A Bessel-history trajectory has differentiable emission phases on the
whole time axis, bounded emission and comparison speeds, and satisfies the
kinematics and tangential balance on the comparison interval. -/
structure BesselHistoryOn {ι : Type*} [Fintype ι] (F k r L m D u₀ T Ω R a b : ℝ)
    (left right : ι → ι) (q q' : ℝ → AngularState ι) : Prop where
  continuousOn : ContinuousOn q (Icc a b)
  hasDeriv : ∀ t ∈ Ico a b, HasDerivWithinAt q (q' t) (Ici t) t
  differentiablePhase : ∀ i, Differentiable ℝ (fun t => (q t).1 i)
  emissionSpeed : ∀ i s, ‖deriv (fun t => (q t).1 i) s‖ ≤ Ω
  comparisonSpeed : ∀ t ∈ Ico a b, ∀ i, |(q t).2 i| ≤ R
  kinematics : ∀ t ∈ Ico a b, (q' t).1 = (q t).2
  balance : ∀ t ∈ Ico a b, ∀ i, m * (r * (q' t).2 i) =
    D * (1 - (r * (q t).2 i) ^ 2 / u₀ ^ 2) * (r * (q t).2 i) +
      twoNeighborBesselForce F k r L ((q t).1 i) t T
        (fun s => (q s).1 (left i)) (fun s => (q s).1 (right i))

/-- On a bounded time interval, the Bessel-to-Kuramoto trajectory error is
uniformly controlled by the initial error and a linear combination of
memory time and orbital radius. All constants are chosen independently of
the positive radius and memory time. The preferred speed is scaled as
`u₀ = r * ω₀` to preserve the angular Rayleigh drift. -/
theorem dist_small_orbit_trajectories {ι : Type*} [Fintype ι] (left right : ι → ι)
    (F k L m D τ ω₀ Ω R : ℝ) (hL : 0 < L) (hk : 0 < k) (hm : 0 < m)
    (hΩ : 0 ≤ Ω) (hτ : τ = m / D) :
    ∃ A ≥ 0, ∃ B ≥ 0, ∃ K : ℝ≥0, ∀ (r T a b δ : ℝ) (q q' g : ℝ → AngularState ι),
      0 < r → r ≤ L / 4 → 0 < T →
      BesselHistoryOn F k r L m D (r * ω₀) T Ω R a b left right q q' →
      ContinuousOn g (Icc a b) →
      (∀ t ∈ Ico a b, HasDerivWithinAt g (gkLatticeRhs F k 1 L m τ ω₀ left right (g t))
        (Ici t) t) →
      (∀ t ∈ Ico a b, ∀ i, |(g t).2 i| ≤ R) →
      dist (q a) (g a) ≤ δ →
      ∀ t ∈ Icc a b, dist (q t) (g t) ≤ gronwallBound δ K (A * (Ω + Ω) * T + B * r) (b - a) := by
  obtain ⟨A, hA, B, hB, hAcc⟩ := gk_acceleration_error_small_orbit F k L m hk hL hm
  obtain ⟨K, hK⟩ := gkLatticeRhs_lipschitz F k 1 L m τ ω₀ R left right
  refine ⟨A, hA, B, hB, K, ?_⟩
  intro r T a b δ q q' g hr hrL hT hModel hg hg' hgvel hinit t ht
  let v := gkLatticeRhs F k 1 L m τ ω₀ left right
  let ε := A * (Ω + Ω) * T + B * r
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hRadius := gk_lattice_rhs_eq_unit_radius F k r L m τ ω₀ left right hr.ne' hL.ne' hm.ne'
  have hω₀ : ω₀ = (r * ω₀) / r := by
    rw [mul_comm, mul_div_cancel_right₀ _ hr.ne']
  have hResidual (s : ℝ) (hs : s ∈ Ico a b) : dist (q' s) (v (q s)) ≤ ε := by
    change dist (q' s) (gkLatticeRhs F k 1 L m τ ω₀ left right (q s)) ≤ ε
    rw [← hRadius]
    apply gk_state_residual_le F k r L m τ ω₀ left right (q s) (q' s) hε (hModel.kinematics s hs)
    intro i
    exact hAcc r hr hrL (fun u => (q u).1 (left i)) (fun u => (q u).1 (right i)) Ω Ω
      (hModel.differentiablePhase (left i)) (hModel.differentiablePhase (right i))
      (hModel.emissionSpeed (left i)) (hModel.emissionSpeed (right i))
      ((q s).1 i) s T ((q s).2 i) ((q' s).2 i) D τ (r * ω₀) ω₀ hT hτ hω₀ (hModel.balance s hs i)
  have hExact (s : ℝ) (_ : s ∈ Ico a b) : dist (v (g s)) (v (g s)) ≤ 0 := by simp
  have hBound : dist (q t) (g t) ≤ gronwallBound δ K ε (t - a) := by
    simpa only [add_zero] using
      dist_le_of_approx_trajectories_ODE_of_mem
        (v := fun _ => v) (s := fun _ => {x | ∀ i, |x.2 i| ≤ R})
        (fun _ _ => hK) hModel.continuousOn hModel.hasDeriv hResidual hModel.comparisonSpeed
        hg hg' hExact hgvel hinit t ht
  exact hBound.trans (gronwallBound_mono (dist_nonneg.trans hinit) hε K.coe_nonneg (sub_le_sub_right ht.2 a))

/-- Fixed-horizon Grönwall bounds vanish when the initial error and the
residual vanish. -/
theorem tendsto_gronwall_zero {γ : Type*} {p : Filter γ} {δ ε : γ → ℝ}
    (K H : ℝ) (hδ : Tendsto δ p (𝓝 0)) (hε : Tendsto ε p (𝓝 0)) :
    Tendsto (fun n => gronwallBound (δ n) K (ε n) H) p (𝓝 0) := by
  by_cases hK : K = 0
  · simpa [hK, gronwallBound_K0] using hδ.add (hε.mul_const H)
  · simpa [gronwallBound_of_K_ne_0 hK] using
      (hδ.mul_const (Real.exp (K * H))).add
        ((hε.div_const K).mul_const (Real.exp (K * H) - 1))

/-- For a family with common speed bounds and convergent initial values,
the Bessel-history solutions approach the generalized Kuramoto solution
uniformly on the fixed comparison interval in the joint small-radius and
low-memory limit. No relation between the two vanishing scales is needed. -/
theorem tendsto_uniformly_on_small_orbit {ι γ : Type*} [Fintype ι] {p : Filter γ}
    (left right : ι → ι) (F k L m D τ ω₀ Ω R a b : ℝ)
    (hL : 0 < L) (hk : 0 < k) (hm : 0 < m) (hΩ : 0 ≤ Ω) (hτ : τ = m / D)
    (r T : γ → ℝ) (q q' : γ → ℝ → AngularState ι) (g : ℝ → AngularState ι)
    (hr : Tendsto r p (𝓝 0)) (hT : Tendsto T p (𝓝 0))
    (hinit : Tendsto (fun n => dist (q n a) (g a)) p (𝓝 0))
    (hFamily : ∀ᶠ n in p, 0 < r n ∧ r n ≤ L / 4 ∧ 0 < T n ∧
      BesselHistoryOn F k (r n) L m D (r n * ω₀) (T n) Ω R a b left right (q n) (q' n))
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (gkLatticeRhs F k 1 L m τ ω₀ left right (g t))
      (Ici t) t)
    (hgvel : ∀ t ∈ Ico a b, ∀ i, |(g t).2 i| ≤ R) :
    TendstoUniformlyOn q g p (Icc a b) := by
  obtain ⟨A, _, B, _, K, hBound⟩ :=
    dist_small_orbit_trajectories left right F k L m D τ ω₀ Ω R hL hk hm hΩ hτ
  have hResidual : Tendsto (fun n => A * (Ω + Ω) * T n + B * r n) p (𝓝 0) := by
    simpa using (hT.const_mul (A * (Ω + Ω))).add (hr.const_mul B)
  have hLimit := tendsto_gronwall_zero (K : ℝ) (b - a) hinit hResidual
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [hFamily, (tendsto_order.1 hLimit).2 η hη] with n hn hε t ht
  obtain ⟨hrn, hsep, hTn, hq⟩ := hn
  rw [dist_comm]
  exact (hBound (r n) (T n) a b (dist (q n a) (g a)) (q n) (q' n) g hrn hsep hTn
    hq hg hg' hgvel le_rfl t ht).trans_lt hε

end Qatlib.Papers.HydroSpinLatt21.BesselModel
