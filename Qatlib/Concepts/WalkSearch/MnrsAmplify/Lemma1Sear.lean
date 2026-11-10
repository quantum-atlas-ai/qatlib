/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma1Stat
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MnrsAmplify
open scoped Real ComplexConjugate

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

theorem mnrs_mark_projection_eq (M : Submodule ℂ W) : markProj M = M.starProjection := rfl

omit [FiniteDimensional ℂ W] in

theorem mnrs_line_projection_eq (u : W) :
    lineProj u = (Submodule.span ℂ {u}).starProjection := rfl

omit [FiniteDimensional ℂ W] in

theorem mnrs_frozen_reflection_exact_on_orthogonal (u : W) (Rs : Submodule ℂ W)
    (R : W ≃ₗᵢ[ℂ] W) (β : ℝ)
    (hbound : ∀ ψ ∈ Rs, ψ ∈ (Submodule.span ℂ {u})ᗮ →
      ‖R ψ+ψ-(2 : ℂ) • lineProj u ψ‖ ≤ β)
    (ψ : W) (hψ : ψ ∈ Rs) (ho : ψ ∈ (Submodule.span ℂ {u})ᗮ) : R ψ = -ψ := by
  have hp : lineProj u ψ = 0 := by
    rw [mnrs_line_projection_eq]
    exact (Submodule.starProjection_apply_eq_zero_iff _).mpr ho
  have hβ : 0 ≤ β := by simpa using hbound 0 Rs.zero_mem (Submodule.zero_mem _)
  have hz : R ψ+ψ = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    by_contra hn
    have hd : 0 < ‖R ψ+ψ‖ := lt_of_not_ge hn
    let r : ℝ := (β+1)/‖R ψ+ψ‖
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hb := hbound ((r : ℂ) • ψ) (Rs.smul_mem _ hψ) ((Submodule.span ℂ {u})ᗮ.smul_mem _ ho)
    simp only [map_smul, hp, smul_zero, sub_zero, ← smul_add, norm_smul,
      Complex.norm_real] at hb
    rw [Real.norm_of_nonneg hr] at hb
    have he : r*‖R ψ+ψ‖ = β+1 := by dsimp [r]; field_simp
    rw [he] at hb
    linarith
  exact eq_neg_of_add_eq_zero_left hz

omit [FiniteDimensional ℂ W] in

theorem mnrs_frozen_reflection_exact (u : W) (Rs : Submodule ℂ W)
    (R : W ≃ₗᵢ[ℂ] W) (β : ℝ) (hu : u ∈ Rs) (hfix : R u = u)
    (hbound : ∀ ψ ∈ Rs, ψ ∈ (Submodule.span ℂ {u})ᗮ →
      ‖R ψ+ψ-(2 : ℂ) • lineProj u ψ‖ ≤ β)
    (z : W) (hz : z ∈ Rs) : R z = (2 : ℂ) • lineProj u z-z := by
  have hspan : lineProj u z ∈ Submodule.span ℂ {u} :=
    (Submodule.orthogonalProjection (Submodule.span ℂ {u}) z).property
  have hline : lineProj u z ∈ Rs :=
    (Submodule.span_le.mpr (by simpa using hu)) hspan
  have horth : z-lineProj u z ∈ (Submodule.span ℂ {u})ᗮ := by
    rw [mnrs_line_projection_eq]
    exact Submodule.sub_starProjection_mem_orthogonal z
  have hneg := mnrs_frozen_reflection_exact_on_orthogonal u Rs R β hbound
    (z-lineProj u z) (Rs.sub_mem hz hline) horth
  have hfixed : R (lineProj u z) = lineProj u z := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hspan
    rw [← ha, map_smul, hfix]
  have hsplit : z = lineProj u z+(z-lineProj u z) := by abel
  calc
    R z = R (lineProj u z)+R (z-lineProj u z) := by rw [← map_add, ← hsplit]
    _ = (2 : ℂ) • lineProj u z-z := by rw [hfixed, hneg]; module

omit [FiniteDimensional ℂ W] in

theorem mnrs_raa_state_norm (unmarkRefl : W ≃ₗᵢ[ℂ] W) (R : ℕ → W ≃ₗᵢ[ℂ] W)
    (x₀ : W) (i : ℕ) : ‖raaState unmarkRefl R x₀ i‖ = ‖x₀‖ :=
  (raaUnitary unmarkRefl R i).norm_map x₀

private theorem mnrs_log_schedule_constant : Real.log (4*Real.pi^3/18) ≤ 2 := by
  have hp : Real.pi^3 ≤ (3.15 : ℝ)^3 :=
    pow_le_pow_left₀ Real.pi_pos.le (Real.pi_lt_d2).le 3
  have hc : 4*Real.pi^3/18 ≤ 7 := by nlinarith only [hp]
  have he : (7 : ℝ) ≤ Real.exp 2 := by
    have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 5
    norm_num [Finset.sum_range_succ] at hs
    exact hs
  exact (Real.log_le_iff_le_exp (by positivity : 0 < 4*Real.pi^3/18)).mpr (hc.trans he)

theorem mnrs_schedule_log_bound (γ : ℝ) (hγ : 0 < γ) (i : ℕ) (hi : 1 ≤ i) :
    Real.log (1/betaAt γ i) ≤ Real.log (1/γ)+2*(i : ℝ) := by
  have hiR : (0 : ℝ) < i := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hi)
  have he : 1/betaAt γ i = (4*Real.pi^3/18)*(i : ℝ)^2*(1/γ) := by
    unfold betaAt
    field_simp
  rw [he, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hl := Real.log_le_sub_one_of_pos hiR
  linarith only [hl, mnrs_log_schedule_constant]

theorem mnrs_raa_cost_bound (γ c₁ c₂ : ℝ) (hγ : 0 < γ) (hc₁ : 0 ≤ c₁)
    (costR : ℕ → ℝ) (costMark : ℝ) (t : ℕ)
    (hcost : ∀ i, 1 ≤ i → i ≤ t → costR i ≤ c₁*Real.log (1/betaAt γ i))
    (hmark : costMark ≤ c₂) :
    raaCost costR costMark t ≤
      ((3 : ℝ)^t-1)*(c₁*(Real.log (1/γ)+3)+c₂)/2-c₁*(t : ℝ) := by
  have hrec (n : ℕ) (hn : n ≤ t) : raaCost costR costMark n ≤
      ((3 : ℝ)^n-1)*(c₁*(Real.log (1/γ)+3)+c₂)/2-c₁*(n : ℝ) := by
    induction n with
    | zero => simp [raaCost]
    | succ n ih =>
      have hprev := ih (by omega)
      have hlevel := (hcost (n+1) (by omega) hn).trans
        (mul_le_mul_of_nonneg_left (mnrs_schedule_log_bound γ hγ (n+1) (by omega)) hc₁)
      simp only [Nat.cast_add, Nat.cast_one] at hlevel
      simp only [raaCost, pow_succ, Nat.cast_add, Nat.cast_one]
      nlinarith only [hprev, hlevel, hmark]
  exact hrec t le_rfl

omit [FiniteDimensional ℂ W] in

theorem mnrs_triple_angle_step (g v : W) (hg : ‖g‖ = 1) (hv : ‖v‖ = 1)
    (ho : inner ℂ g v = 0) (U : W ≃ₗᵢ[ℂ] W) (hUg : U g = -g) (hUv : U v = v)
    (a : ℝ) (hn : ‖(Real.sin a : ℂ) • g+(Real.cos a : ℂ) • v‖ = 1) :
    (2 : ℂ) • lineProj ((Real.sin a : ℂ) • g+(Real.cos a : ℂ) • v)
      (U ((Real.sin a : ℂ) • g+(Real.cos a : ℂ) • v))-
        U ((Real.sin a : ℂ) • g+(Real.cos a : ℂ) • v) =
      (Real.sin (3*a) : ℂ) • g+(Real.cos (3*a) : ℂ) • v := by
  have hgg : inner ℂ g g = 1 := inner_self_eq_one_of_norm_eq_one hg
  have hvv : inner ℂ v v = 1 := inner_self_eq_one_of_norm_eq_one hv
  have hvg : inner ℂ v g = 0 := by rw [← inner_conj_symm, ho, map_zero]
  have hUs : U ((Real.sin a : ℂ) • g+(Real.cos a : ℂ) • v) =
      -(Real.sin a : ℂ) • g+(Real.cos a : ℂ) • v := by
    rw [map_add, map_smul, map_smul, hUg, hUv, smul_neg, neg_smul]
  rw [mnrs_line_projection_eq, Submodule.starProjection_singleton, hn]
  simp only [one_pow]
  have hi : inner ℂ ((Real.sin a : ℂ) • g+(Real.cos a : ℂ) • v)
      (U ((Real.sin a : ℂ) • g+(Real.cos a : ℂ) • v)) =
        ((Real.cos a)^2-(Real.sin a)^2 : ℝ) := by
    rw [hUs]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      hgg, hvv, ho, hvg, Complex.conj_ofReal, mul_zero, add_zero,
      zero_add, mul_one, Complex.ofReal_sub, Complex.ofReal_pow]
    ring
  rw [hi, hUs, Real.sin_three_mul, Real.cos_three_mul]
  have hs := Real.sin_sq_add_cos_sq a
  have hsin : (2 : ℂ)*((Real.cos a)^2-(Real.sin a)^2 : ℝ)*(Real.sin a : ℂ)+Real.sin a =
      (3*Real.sin a-4*(Real.sin a)^3 : ℝ) := by
    have he : 2*((Real.cos a)^2-(Real.sin a)^2)*Real.sin a+Real.sin a =
        3*Real.sin a-4*(Real.sin a)^3 := by linear_combination 2*(Real.sin a)*hs
    exact_mod_cast he
  have hcos : (2 : ℂ)*((Real.cos a)^2-(Real.sin a)^2 : ℝ)*(Real.cos a : ℂ)-Real.cos a =
      (4*(Real.cos a)^3-3*Real.cos a : ℝ) := by
    have he : 2*((Real.cos a)^2-(Real.sin a)^2)*Real.cos a-Real.cos a =
        4*(Real.cos a)^3-3*Real.cos a := by linear_combination -2*(Real.cos a)*hs
    exact_mod_cast he
  rw [← hsin, ← hcos]
  module

omit [FiniteDimensional ℂ W] in

theorem mnrs_raa_plane_state (g v : W) (hg : ‖g‖ = 1) (hv : ‖v‖ = 1)
    (ho : inner ℂ g v = 0) (U : W ≃ₗᵢ[ℂ] W) (hUg : U g = -g) (hUv : U v = v)
    (Rs : Submodule ℂ W) (hgRs : g ∈ Rs) (hvRs : v ∈ Rs)
    (x₀ : W) (hn : ‖x₀‖ = 1) (θ γ : ℝ)
    (hx : x₀ = (Real.sin θ : ℂ) • g+(Real.cos θ : ℂ) • v)
    (R : ℕ → W ≃ₗᵢ[ℂ] W) (t : ℕ)
    (hfix : ∀ i, 1 ≤ i → i ≤ t → R i (raaState U R x₀ (i-1)) = raaState U R x₀ (i-1))
    (hbound : ∀ i, 1 ≤ i → i ≤ t → ∀ ψ ∈ Rs,
      ψ ∈ (Submodule.span ℂ {raaState U R x₀ (i-1)})ᗮ →
        ‖R i ψ+ψ-(2 : ℂ) • lineProj (raaState U R x₀ (i-1)) ψ‖ ≤ betaAt γ i) :
    ∀ i, i ≤ t → raaState U R x₀ i =
      (Real.sin ((3 : ℝ)^i*θ) : ℂ) • g+(Real.cos ((3 : ℝ)^i*θ) : ℂ) • v := by
  intro i
  induction i with
  | zero => intro _; simpa [raaState, raaUnitary] using hx
  | succ i ih =>
    intro hi
    have hstate := ih (by omega)
    have hφRs : raaState U R x₀ i ∈ Rs := by
      rw [hstate]; exact Rs.add_mem (Rs.smul_mem _ hgRs) (Rs.smul_mem _ hvRs)
    have hURs : U (raaState U R x₀ i) ∈ Rs := by
      rw [hstate, map_add, map_smul, map_smul, hUg, hUv]
      exact Rs.add_mem (Rs.smul_mem _ (Rs.neg_mem hgRs)) (Rs.smul_mem _ hvRs)
    have hfixi : R (i+1) (raaState U R x₀ i) = raaState U R x₀ i := by
      simpa using hfix (i+1) (by omega) hi
    have hb : ∀ ψ ∈ Rs, ψ ∈ (Submodule.span ℂ {raaState U R x₀ i})ᗮ →
        ‖R (i+1) ψ+ψ-(2 : ℂ) • lineProj (raaState U R x₀ i) ψ‖ ≤ betaAt γ (i+1) := by
      simpa using hbound (i+1) (by omega) hi
    have he := mnrs_frozen_reflection_exact (raaState U R x₀ i) Rs (R (i+1))
      (betaAt γ (i+1)) hφRs hfixi hb (U (raaState U R x₀ i)) hURs
    have hφn : ‖(Real.sin ((3 : ℝ)^i*θ) : ℂ) • g+
        (Real.cos ((3 : ℝ)^i*θ) : ℂ) • v‖ = 1 := by
      rw [← hstate, mnrs_raa_state_norm, hn]
    change R (i+1) (U (raaState U R x₀ i)) = _
    rw [he, hstate, mnrs_triple_angle_step g v hg hv ho U hUg hUv _ hφn]
    have hangle : 3*((3 : ℝ)^i*θ) = (3 : ℝ)^(i+1)*θ := by rw [pow_succ]; ring
    rw [hangle]

private theorem mnrs_sin_final_window (a : ℝ) (ha : a ∈ Set.Icc (π/4) (3*π/4)) :
    1/Real.sqrt 2 ≤ Real.sin a := by
  have hs : Real.sin (π/4) ≤ Real.sin a := by
    by_cases h : a ≤ π/2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h ha.1
    · have h' := Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos] : -(π/2) ≤ π/4)
        (by linarith : π-a ≤ π/2) (by linarith [ha.2] : π/4 ≤ π-a)
      simpa only [Real.sin_pi_sub] using h'
  rw [Real.sin_pi_div_four] at hs
  have he : Real.sqrt 2/2 = 1/Real.sqrt 2 := by
    have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp; nlinarith only [hsq]
  rwa [he] at hs

theorem mnrs_initial_good_bad_plane (M Rs : Submodule ℂ W) (x : W) (hn : ‖x‖ = 1)
    (hxRs : x ∈ Rs) (hclosed : ∀ z ∈ Rs, markProj M z ∈ Rs)
    (hy : markProj M x ≠ 0) (hz : x-markProj M x ≠ 0) :
    ∃ g v : W, ‖g‖ = 1 ∧ ‖v‖ = 1 ∧ g ∈ M ∧ v ∈ Mᗮ ∧
      g ∈ Rs ∧ v ∈ Rs ∧ inner ℂ g v = 0 ∧
      x = (Real.sin (Real.arcsin ‖markProj M x‖) : ℂ) • g+
        (Real.cos (Real.arcsin ‖markProj M x‖) : ℂ) • v := by
  let y := markProj M x
  let z := x-y
  let g := NormedSpace.normalize y
  let v := NormedSpace.normalize z
  have hyM : y ∈ M := (M.orthogonalProjection x).property
  have hzM : z ∈ Mᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hyRs : y ∈ Rs := hclosed x hxRs
  have hzRs : z ∈ Rs := Rs.sub_mem hxRs hyRs
  have hgn : ‖g‖ = 1 := NormedSpace.norm_normalize hy
  have hvn : ‖v‖ = 1 := NormedSpace.norm_normalize hz
  have hgM : g ∈ M := by
    simpa only [g, NormedSpace.normalize, Complex.coe_smul] using M.smul_mem ((‖y‖⁻¹ : ℝ) : ℂ) hyM
  have hvM : v ∈ Mᗮ := by
    simpa only [v, NormedSpace.normalize, Complex.coe_smul] using Mᗮ.smul_mem ((‖z‖⁻¹ : ℝ) : ℂ) hzM
  have hgRs : g ∈ Rs := by
    simpa only [g, NormedSpace.normalize, Complex.coe_smul] using Rs.smul_mem ((‖y‖⁻¹ : ℝ) : ℂ) hyRs
  have hvRs : v ∈ Rs := by
    simpa only [v, NormedSpace.normalize, Complex.coe_smul] using Rs.smul_mem ((‖z‖⁻¹ : ℝ) : ℂ) hzRs
  have hgv : inner ℂ g v = 0 := (M.mem_orthogonal v).mp hvM g hgM
  have hyz : inner ℂ y z = 0 := (M.mem_orthogonal z).mp hzM y hyM
  have hzy : inner ℂ z y = 0 := by rw [← inner_conj_symm, hyz, map_zero]
  have hsplit : x = y+z := by dsimp [z]; abel
  have hsq : ‖x‖^2 = ‖y‖^2+‖z‖^2 := by
    have he : inner ℂ x x = inner ℂ y y+inner ℂ z z := by
      rw [hsplit, inner_add_add_self, hyz, hzy]; ring
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at he
    exact_mod_cast he
  have hyn : ‖y‖ ≤ 1 := by simpa only [hn] using! M.norm_starProjection_apply_le x
  have hsin : Real.sin (Real.arcsin ‖y‖) = ‖y‖ := Real.sin_arcsin (by linarith [norm_nonneg y]) hyn
  have hcos0 : 0 ≤ Real.cos (Real.arcsin ‖y‖) :=
    Real.cos_nonneg_of_mem_Icc (Real.arcsin_mem_Icc _)
  have hcos : Real.cos (Real.arcsin ‖y‖) = ‖z‖ := by
    apply (sq_eq_sq₀ hcos0 (norm_nonneg z)).mp
    have ht := Real.sin_sq_add_cos_sq (Real.arcsin ‖y‖)
    rw [hsin] at ht
    rw [hn] at hsq
    nlinarith only [hsq, ht]
  refine ⟨g, v, hgn, hvn, hgM, hvM, hgRs, hvRs, hgv, ?_⟩
  rw [hsin, hcos, Complex.coe_smul, Complex.coe_smul]
  simpa only [g, v, NormedSpace.norm_smul_normalize] using hsplit

omit [FiniteDimensional ℂ W] in

theorem mnrs_raa_invariant_subspace (K Rs : Submodule ℂ W) (hKR : K ≤ Rs)
    (U : W ≃ₗᵢ[ℂ] W) (hU : ∀ z ∈ K, U z ∈ K) (x₀ : W) (hx : x₀ ∈ K)
    (R : ℕ → W ≃ₗᵢ[ℂ] W) (γ : ℝ) (t : ℕ)
    (hfix : ∀ i, 1 ≤ i → i ≤ t → R i (raaState U R x₀ (i-1)) = raaState U R x₀ (i-1))
    (hbound : ∀ i, 1 ≤ i → i ≤ t → ∀ ψ ∈ Rs,
      ψ ∈ (Submodule.span ℂ {raaState U R x₀ (i-1)})ᗮ →
        ‖R i ψ+ψ-(2 : ℂ) • lineProj (raaState U R x₀ (i-1)) ψ‖ ≤ betaAt γ i) :
    ∀ i, i ≤ t → ∀ z ∈ K, (raaUnitary U R i) z ∈ K := by
  intro i
  induction i with
  | zero => intro _ z hz; exact hz
  | succ i ih =>
    intro hi z hz
    have hn : i ≤ t := by omega
    have hφ : raaState U R x₀ i ∈ K := ih hn x₀ hx
    have hw : U ((raaUnitary U R i) z) ∈ K := hU _ (ih hn z hz)
    have hfi : R (i+1) (raaState U R x₀ i) = raaState U R x₀ i := by
      simpa using hfix (i+1) (by omega) hi
    have hbi : ∀ ψ ∈ Rs, ψ ∈ (Submodule.span ℂ {raaState U R x₀ i})ᗮ →
        ‖R (i+1) ψ+ψ-(2 : ℂ) • lineProj (raaState U R x₀ i) ψ‖ ≤ betaAt γ (i+1) := by
      simpa using hbound (i+1) (by omega) hi
    have he := mnrs_frozen_reflection_exact (raaState U R x₀ i) Rs (R (i+1))
      (betaAt γ (i+1)) (hKR hφ) hfi hbi (U ((raaUnitary U R i) z)) (hKR hw)
    change R (i+1) (U ((raaUnitary U R i) z)) ∈ K
    rw [he]
    apply K.sub_mem _ hw
    apply K.smul_mem
    exact (Submodule.span_le.mpr (by simpa using hφ))
      (Submodule.orthogonalProjection (Submodule.span ℂ {raaState U R x₀ i}) _).property

theorem mnrs_sin_three_sub (A B : ℝ) :
    Real.sin (3 * A) - Real.sin (3 * B) =
      (Real.sin A - Real.sin B) *
        (3 - 4 * (Real.sin A ^ 2 + Real.sin A * Real.sin B + Real.sin B ^ 2)) := by
  rw [Real.sin_three_mul, Real.sin_three_mul]
  ring

theorem mnrs_sum_inv_sq_le_two (n : ℕ) :
    ∑ l ∈ Finset.Icc 1 n, (1 : ℝ) / (l : ℝ) ^ 2 ≤ 2 := by
  have hstep : ∀ m : ℕ, 1 ≤ m →
      ∑ l ∈ Finset.Icc 1 m, (1 : ℝ) / (l : ℝ) ^ 2 ≤ 2 - 1 / (m : ℝ) := by
    intro m
    induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        norm_num [Finset.Icc_self]
      · have h := ih (by omega)
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
        have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm0
        have hm1pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have hkey : (1 : ℝ) / ((m : ℝ) + 1) ^ 2 ≤ 1 / (m : ℝ) - 1 / ((m : ℝ) + 1) := by
          have h1 : (1 : ℝ) / (m : ℝ) - 1 / ((m : ℝ) + 1) = 1 / ((m : ℝ) * ((m : ℝ) + 1)) := by
            field_simp
            ring
          rw [h1]
          apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
            (by positivity : (0 : ℝ) < (m : ℝ) * ((m : ℝ) + 1))
          nlinarith [hm1pos]
        linarith [h, hkey]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have h := hstep n hn
    have h1 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith [h, h1]

private theorem mnrs_sqrt_two_div_two : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  field_simp
  nlinarith only [hsq]

private theorem mnrs_sqrt_two_le : Real.sqrt 2 ≤ 99 / 70 := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg 2) (by norm_num : (0 : ℝ) ≤ 99 / 70)).mp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem mnrs_one_div_sqrt_two_le : 1 / Real.sqrt 2 ≤ 99 / 140 := by
  rw [← mnrs_sqrt_two_div_two]
  linarith [mnrs_sqrt_two_le]

theorem mnrs_arcsin_le_pi_div_three {x : ℝ} (hx0 : 0 ≤ x) (hx : x ^ 2 ≤ 3 / 4) :
    Real.arcsin x ≤ π / 3 := by
  have h1 : x ≤ Real.sqrt 3 / 2 := by
    have h2 : (Real.sqrt 3 / 2 : ℝ) ^ 2 = 3 / 4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    have h4 : x ^ 2 ≤ (Real.sqrt 3 / 2 : ℝ) ^ 2 := by rw [h2]; exact hx
    exact (sq_le_sq₀ hx0 (by positivity : (0 : ℝ) ≤ Real.sqrt 3 / 2)).mp h4
  calc Real.arcsin x ≤ Real.arcsin (Real.sqrt 3 / 2) := Real.arcsin_le_arcsin h1
    _ = Real.arcsin (Real.sin (π / 3)) := by rw [Real.sin_pi_div_three]
    _ = π / 3 := Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

private theorem mnrs_ofReal_eq (r : ℝ) : (RCLike.ofReal r : ℂ) = Complex.ofReal r := rfl

theorem mnrs_raa_step
    (Mr Rs : Submodule ℂ W) (unmarkRefl : W ≃ₗᵢ[ℂ] W)
    (hMneg : ∀ z ∈ Mr, unmarkRefl z = -z)
    (hMid : ∀ z ∈ Mrᗮ, unmarkRefl z = z)
    (x₀ : W) (hx₀ : ‖x₀‖ = 1) (γ : ℝ) (hγ0 : 0 < γ)
    (R : ℕ → W ≃ₗᵢ[ℂ] W) (t : ℕ)
    (hclose : ∀ z ∈ Rs, markProj Mr z ∈ Rs)
    (hRRs : ∀ i, 1 ≤ i → i ≤ t → ∀ z ∈ Rs, R i z ∈ Rs)
    (hfix : ∀ i, 1 ≤ i → i ≤ t →
      R i (raaState unmarkRefl R x₀ (i - 1)) = raaState unmarkRefl R x₀ (i - 1))
    (hbound : ∀ i, 1 ≤ i → i ≤ t → ∀ ψ ∈ Rs,
      ψ ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ (i - 1)})ᗮ →
      ‖R i ψ + ψ - (2 : ℂ) • lineProj (raaState unmarkRefl R x₀ (i - 1)) ψ‖
        ≤ betaAt γ i * ‖ψ‖)
    (j : ℕ) (hjt : j + 1 ≤ t)
    (hφRs : raaState unmarkRefl R x₀ j ∈ Rs)
    (hϕ : Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ≤ π / 3) :
    |‖markProj Mr (raaState unmarkRefl R x₀ (j + 1))‖ -
        Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)| ≤
      betaAt γ (j + 1) * |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)|
    ∧ raaState unmarkRefl R x₀ (j + 1) ∈ Rs := by
  let y := markProj Mr (raaState unmarkRefl R x₀ j)
  let z := raaState unmarkRefl R x₀ j - y
  let μ := NormedSpace.normalize y
  let ν := NormedSpace.normalize z
  let ϕ := Real.arcsin ‖y‖
  have hϕle : ϕ ≤ π / 3 := hϕ
  have hϕnn : 0 ≤ ϕ := Real.arcsin_nonneg.mpr (norm_nonneg y)
  have hφn : ‖raaState unmarkRefl R x₀ j‖ = 1 := by rw [mnrs_raa_state_norm, hx₀]
  have hyM : y ∈ Mr := (Mr.orthogonalProjection (raaState unmarkRefl R x₀ j)).property
  have hzM : z ∈ Mrᗮ := Submodule.sub_starProjection_mem_orthogonal _
  have hyRs : y ∈ Rs := hclose _ hφRs
  have hzRs : z ∈ Rs := Rs.sub_mem hφRs hyRs
  have hsy1 : ‖y‖ ≤ 1 := by
    have h := Submodule.norm_starProjection_apply_le Mr (raaState unmarkRefl R x₀ j)
    exact h.trans_eq hφn
  have hsinϕ : Real.sin ϕ = ‖y‖ := Real.sin_arcsin (by linarith [norm_nonneg y]) hsy1
  have hyz0 : inner ℂ y z = 0 := (Mr.mem_orthogonal z).mp hzM y hyM
  have hzy0 : inner ℂ z y = 0 := by rw [← inner_conj_symm, hyz0, map_zero]
  have hsplit : raaState unmarkRefl R x₀ j = y + z := (add_sub_cancel y _).symm
  have hnormsq : ‖y‖ ^ 2 + ‖z‖ ^ 2 = 1 := by
    have he : inner ℂ (raaState unmarkRefl R x₀ j) (raaState unmarkRefl R x₀ j) =
        inner ℂ y y + inner ℂ z z := by
      rw [hsplit, inner_add_add_self, hyz0, hzy0]
      ring
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K] at he
    have he' : ‖raaState unmarkRefl R x₀ j‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by exact_mod_cast he
    rw [hφn] at he'
    linarith [he']
  have hcosϕ : Real.cos ϕ = ‖z‖ := by
    have h1 : (1 : ℝ) - ‖y‖ ^ 2 = ‖z‖ ^ 2 := by linarith [hnormsq]
    show Real.cos (Real.arcsin ‖y‖) = ‖z‖
    rw [Real.cos_arcsin, h1, Real.sqrt_sq (norm_nonneg z)]
  have hμM : μ ∈ Mr := by
    simpa only [μ, NormedSpace.normalize, Complex.coe_smul] using
      Mr.smul_mem ((‖y‖⁻¹ : ℝ) : ℂ) hyM
  have hνM : ν ∈ Mrᗮ := by
    simpa only [ν, NormedSpace.normalize, Complex.coe_smul] using
      Mrᗮ.smul_mem ((‖z‖⁻¹ : ℝ) : ℂ) hzM
  have hμRs : μ ∈ Rs := by
    simpa only [μ, NormedSpace.normalize, Complex.coe_smul] using
      Rs.smul_mem ((‖y‖⁻¹ : ℝ) : ℂ) hyRs
  have hνRs : ν ∈ Rs := by
    simpa only [ν, NormedSpace.normalize, Complex.coe_smul] using
      Rs.smul_mem ((‖z‖⁻¹ : ℝ) : ℂ) hzRs
  have hμν : inner ℂ μ ν = 0 := (Mr.mem_orthogonal ν).mp hνM μ hμM
  have hνμ : inner ℂ ν μ = 0 := by rw [← inner_conj_symm, hμν, map_zero]
  have hμn : ‖μ‖ ≤ 1 := by
    rcases eq_or_ne y 0 with hy0 | hy0
    · have h0 : μ = 0 := by
        show NormedSpace.normalize y = 0
        rw [hy0]
        simp [NormedSpace.normalize]
      rw [h0, norm_zero]
      norm_num
    · rw [NormedSpace.norm_normalize hy0]
  have hνn : ‖ν‖ ≤ 1 := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · have h0 : ν = 0 := by
        show NormedSpace.normalize z = 0
        rw [hz0]
        simp [NormedSpace.normalize]
      rw [h0, norm_zero]
      norm_num
    · rw [NormedSpace.norm_normalize hz0]
  have hμ2 : Real.sin ϕ * ‖μ‖ ^ 2 = Real.sin ϕ := by
    rcases eq_or_ne y 0 with hy0 | hy0
    · have hs0 : Real.sin ϕ = 0 := by rw [hsinϕ, hy0, norm_zero]
      rw [hs0, zero_mul]
    · rw [NormedSpace.norm_normalize hy0]
      simp
  have hν2 : Real.cos ϕ * ‖ν‖ ^ 2 = Real.cos ϕ := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · have hc0 : Real.cos ϕ = 0 := by rw [hcosϕ, hz0, norm_zero]
      rw [hc0, zero_mul]
    · rw [NormedSpace.norm_normalize hz0]
      simp
  have hdecomp : raaState unmarkRefl R x₀ j = (Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν := by
    have hy' : (‖y‖ : ℂ) • μ = y := by
      rw [Complex.coe_smul]
      exact NormedSpace.norm_smul_normalize y
    have hz' : (‖z‖ : ℂ) • ν = z := by
      rw [Complex.coe_smul]
      exact NormedSpace.norm_smul_normalize z
    rw [hsinϕ, hcosϕ, hy', hz']
    exact hsplit
  have hUφ : unmarkRefl (raaState unmarkRefl R x₀ j) =
      -(Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν := by
    rw [hdecomp, map_add, map_smul, map_smul, hMneg μ hμM, hMid ν hνM, smul_neg, ← neg_smul]
  let φp := (Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν
  have hφpRs : φp ∈ Rs := Rs.sub_mem (Rs.smul_mem _ hμRs) (Rs.smul_mem _ hνRs)
  have hUdecomp : unmarkRefl (raaState unmarkRefl R x₀ j) =
      (Real.cos (2 * ϕ) : ℂ) • raaState unmarkRefl R x₀ j - (Real.sin (2 * ϕ) : ℂ) • φp := by
    have hc3 : Real.cos (2 * ϕ) * Real.sin ϕ - Real.sin (2 * ϕ) * Real.cos ϕ =
        -Real.sin ϕ := by
      have h1 : Real.sin (2 * ϕ - ϕ) = Real.sin ϕ := by congr 1; ring
      rw [Real.sin_sub] at h1
      linarith [h1]
    have hc4 : Real.cos (2 * ϕ) * Real.cos ϕ + Real.sin (2 * ϕ) * Real.sin ϕ =
        Real.cos ϕ := by
      have h1 : Real.cos (2 * ϕ - ϕ) = Real.cos ϕ := by congr 1; ring
      rwa [Real.cos_sub] at h1
    rw [hUφ, hdecomp]
    show -(Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν =
      (Real.cos (2 * ϕ) : ℂ) • ((Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν) -
        (Real.sin (2 * ϕ) : ℂ) • ((Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν)
    have hvec : (Real.cos (2 * ϕ) : ℂ) • ((Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν) -
        (Real.sin (2 * ϕ) : ℂ) • ((Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν) =
        ((Real.cos (2 * ϕ) * Real.sin ϕ - Real.sin (2 * ϕ) * Real.cos ϕ : ℝ) : ℂ) • μ +
          ((Real.cos (2 * ϕ) * Real.cos ϕ + Real.sin (2 * ϕ) * Real.sin ϕ : ℝ) : ℂ) • ν := by
      push_cast
      module
    rw [hvec, hc3, hc4, Complex.ofReal_neg, neg_smul]
  have hideal : (Real.cos (2 * ϕ) : ℂ) • raaState unmarkRefl R x₀ j +
        (Real.sin (2 * ϕ) : ℂ) • φp =
      (Real.sin (3 * ϕ) : ℂ) • μ + (Real.cos (3 * ϕ) : ℂ) • ν := by
    have hc1 : Real.cos (2 * ϕ) * Real.sin ϕ + Real.sin (2 * ϕ) * Real.cos ϕ =
        Real.sin (3 * ϕ) := by
      have h1 : Real.sin (2 * ϕ + ϕ) = Real.sin (3 * ϕ) := by congr 1; ring
      rw [Real.sin_add] at h1
      linarith [h1]
    have hc2 : Real.cos (2 * ϕ) * Real.cos ϕ - Real.sin (2 * ϕ) * Real.sin ϕ =
        Real.cos (3 * ϕ) := by
      have h1 : Real.cos (2 * ϕ + ϕ) = Real.cos (3 * ϕ) := by congr 1; ring
      rwa [Real.cos_add] at h1
    rw [hdecomp]
    show (Real.cos (2 * ϕ) : ℂ) • ((Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν) +
        (Real.sin (2 * ϕ) : ℂ) • ((Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν) =
      (Real.sin (3 * ϕ) : ℂ) • μ + (Real.cos (3 * ϕ) : ℂ) • ν
    have hvec : (Real.cos (2 * ϕ) : ℂ) • ((Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν) +
        (Real.sin (2 * ϕ) : ℂ) • ((Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν) =
        ((Real.cos (2 * ϕ) * Real.sin ϕ + Real.sin (2 * ϕ) * Real.cos ϕ : ℝ) : ℂ) • μ +
          ((Real.cos (2 * ϕ) * Real.cos ϕ - Real.sin (2 * ϕ) * Real.sin ϕ : ℝ) : ℂ) • ν := by
      push_cast
      module
    rw [hvec, hc1, hc2]
  have hφporth0 : φp ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ j})ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hcomp : inner ℂ φp (raaState unmarkRefl R x₀ j) =
        ((Real.cos ϕ * Real.sin ϕ * ‖μ‖ ^ 2 - Real.sin ϕ * Real.cos ϕ * ‖ν‖ ^ 2 : ℝ) : ℂ) := by
      rw [hdecomp]
      show inner ℂ ((Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν)
          ((Real.sin ϕ : ℂ) • μ + (Real.cos ϕ : ℂ) • ν) = _
      simp only [inner_sub_left, inner_add_right, inner_smul_left, inner_smul_right,
        hμν, hνμ, inner_self_eq_norm_sq_to_K, Complex.conj_ofReal, mnrs_ofReal_eq]
      push_cast
      ring
    rw [hcomp]
    have hzero : Real.cos ϕ * Real.sin ϕ * ‖μ‖ ^ 2 - Real.sin ϕ * Real.cos ϕ * ‖ν‖ ^ 2 = 0 := by
      linear_combination Real.cos ϕ * hμ2 - Real.sin ϕ * hν2
    exact_mod_cast hzero
  have hφpnorm : ‖φp‖ ≤ 1 := by
    have hcomp : inner ℂ φp φp =
        ((Real.cos ϕ ^ 2 * ‖μ‖ ^ 2 + Real.sin ϕ ^ 2 * ‖ν‖ ^ 2 : ℝ) : ℂ) := by
      show inner ℂ ((Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν)
          ((Real.cos ϕ : ℂ) • μ - (Real.sin ϕ : ℂ) • ν) = _
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        hμν, hνμ, Complex.conj_ofReal, mul_zero, add_zero, zero_add, sub_zero, mnrs_ofReal_eq]
      simp only [inner_self_eq_norm_sq_to_K, mnrs_ofReal_eq]
      push_cast
      ring
    have hsq1 : ‖φp‖ ^ 2 = Real.cos ϕ ^ 2 * ‖μ‖ ^ 2 + Real.sin ϕ ^ 2 * ‖ν‖ ^ 2 := by
      have h1 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) φp
      rw [hcomp] at h1
      simp only [mnrs_ofReal_eq] at h1
      have h2 : (↑‖φp‖ : ℂ) ^ 2 = ↑(‖φp‖ ^ 2) := by simp
      rw [h2] at h1
      exact (Complex.ofReal_inj.mp h1).symm
    have hsqle : ‖φp‖ ^ 2 ≤ 1 := by
      have hμ2' : ‖μ‖ ^ 2 ≤ 1 := by nlinarith [hμn, norm_nonneg μ]
      have hν2' : ‖ν‖ ^ 2 ≤ 1 := by nlinarith [hνn, norm_nonneg ν]
      have hc := Real.sin_sq_add_cos_sq ϕ
      nlinarith [hsq1, mul_le_mul_of_nonneg_left hμ2' (sq_nonneg (Real.cos ϕ)),
        mul_le_mul_of_nonneg_left hν2' (sq_nonneg (Real.sin ϕ)), hc]
    exact (sq_le_sq₀ (norm_nonneg φp) zero_le_one).mp (by simpa using hsqle)
  have hfixj : R (j + 1) (raaState unmarkRefl R x₀ j) = raaState unmarkRefl R x₀ j := by
    have h := hfix (j + 1) (Nat.le_add_left 1 j) hjt
    rwa [Nat.add_sub_cancel] at h
  have hboundj : ‖R (j + 1) φp + φp‖ ≤ betaAt γ (j + 1) * ‖φp‖ := by
    have hφporth : φp ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ (j + 1 - 1)})ᗮ := by
      rw [Nat.add_sub_cancel]
      exact hφporth0
    have h := hbound (j + 1) (Nat.le_add_left 1 j) hjt φp hφpRs hφporth
    rw [Nat.add_sub_cancel] at h
    have hlp : lineProj (raaState unmarkRefl R x₀ j) φp = 0 := by
      rw [mnrs_line_projection_eq]
      exact (Submodule.starProjection_apply_eq_zero_iff _).mpr hφporth0
    rw [hlp, smul_zero, sub_zero] at h
    exact h
  let ω := -(Real.sin (2 * ϕ) : ℂ) • (R (j + 1) φp + φp)
  have hωnorm : ‖ω‖ ≤ betaAt γ (j + 1) * |Real.sin (2 * ϕ)| := by
    have hβnn : 0 ≤ betaAt γ (j + 1) := by
      unfold betaAt
      positivity
    have h1 : ‖ω‖ = |Real.sin (2 * ϕ)| * ‖R (j + 1) φp + φp‖ := by
      show ‖-(Real.sin (2 * ϕ) : ℂ) • (R (j + 1) φp + φp)‖ =
          |Real.sin (2 * ϕ)| * ‖R (j + 1) φp + φp‖
      rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    rw [h1]
    calc |Real.sin (2 * ϕ)| * ‖R (j + 1) φp + φp‖
        ≤ |Real.sin (2 * ϕ)| * (betaAt γ (j + 1) * ‖φp‖) :=
          mul_le_mul_of_nonneg_left hboundj (abs_nonneg _)
      _ ≤ |Real.sin (2 * ϕ)| * (betaAt γ (j + 1) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hφpnorm hβnn) (abs_nonneg _)
      _ = betaAt γ (j + 1) * |Real.sin (2 * ϕ)| := by ring
  have hstate : raaState unmarkRefl R x₀ (j + 1) =
      (Real.sin (3 * ϕ) : ℂ) • μ + (Real.cos (3 * ϕ) : ℂ) • ν + ω := by
    have h1 : raaState unmarkRefl R x₀ (j + 1) =
        R (j + 1) (unmarkRefl (raaState unmarkRefl R x₀ j)) := rfl
    rw [h1, hUdecomp, map_sub, map_smul, map_smul, hfixj]
    show (Real.cos (2 * ϕ) : ℂ) • raaState unmarkRefl R x₀ j -
        (Real.sin (2 * ϕ) : ℂ) • R (j + 1) φp =
      (Real.sin (3 * ϕ) : ℂ) • μ + (Real.cos (3 * ϕ) : ℂ) • ν + ω
    have h2 : (Real.cos (2 * ϕ) : ℂ) • raaState unmarkRefl R x₀ j -
        (Real.sin (2 * ϕ) : ℂ) • R (j + 1) φp =
        (Real.cos (2 * ϕ) : ℂ) • raaState unmarkRefl R x₀ j + (Real.sin (2 * ϕ) : ℂ) • φp +
          ω := by
      show (Real.cos (2 * ϕ) : ℂ) • raaState unmarkRefl R x₀ j -
          (Real.sin (2 * ϕ) : ℂ) • R (j + 1) φp =
        (Real.cos (2 * ϕ) : ℂ) • raaState unmarkRefl R x₀ j + (Real.sin (2 * ϕ) : ℂ) • φp +
          (-(Real.sin (2 * ϕ) : ℂ) • (R (j + 1) φp + φp))
      module
    rw [h2, hideal]
  have hproj : markProj Mr (raaState unmarkRefl R x₀ (j + 1)) =
      (Real.sin (3 * ϕ) : ℂ) • μ + markProj Mr ω := by
    have hμfix : markProj Mr μ = μ := by
      rw [mnrs_mark_projection_eq]
      exact (Submodule.starProjection_eq_self_iff).mpr hμM
    have hν0 : markProj Mr ν = 0 := by
      rw [mnrs_mark_projection_eq]
      exact (Submodule.starProjection_apply_eq_zero_iff _).mpr hνM
    rw [hstate, map_add, map_add, map_smul, map_smul, hμfix, hν0, smul_zero, add_zero]
  have hs3nn : 0 ≤ Real.sin (3 * ϕ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hϕnn]
    · linarith [hϕle, Real.pi_pos]
  have hμ3 : Real.sin (3 * ϕ) * ‖μ‖ = Real.sin (3 * ϕ) := by
    rcases eq_or_ne y 0 with hy0 | hy0
    · have hs0 : Real.sin ϕ = 0 := by rw [hsinϕ, hy0, norm_zero]
      have h3 : Real.sin (3 * ϕ) = 0 := by
        rw [Real.sin_three_mul, hs0]
        simp
      rw [h3, zero_mul]
    · rw [NormedSpace.norm_normalize hy0, mul_one]
  have hmain : |‖markProj Mr (raaState unmarkRefl R x₀ (j + 1))‖ - Real.sin (3 * ϕ)| ≤
      ‖ω‖ := by
    have h1 : ‖(Real.sin (3 * ϕ) : ℂ) • μ‖ = Real.sin (3 * ϕ) * ‖μ‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs3nn]
    have h2 := abs_norm_sub_norm_le ((Real.sin (3 * ϕ) : ℂ) • μ + markProj Mr ω)
      ((Real.sin (3 * ϕ) : ℂ) • μ)
    rw [h1, add_sub_cancel_left] at h2
    rw [hproj]
    calc |‖(Real.sin (3 * ϕ) : ℂ) • μ + markProj Mr ω‖ - Real.sin (3 * ϕ)|
        = |‖(Real.sin (3 * ϕ) : ℂ) • μ + markProj Mr ω‖ - Real.sin (3 * ϕ) * ‖μ‖| := by
          rw [hμ3]
      _ ≤ ‖markProj Mr ω‖ := h2
      _ ≤ ‖ω‖ := Submodule.norm_starProjection_apply_le Mr ω
  constructor
  · exact hmain.trans hωnorm
  · have h1 : raaState unmarkRefl R x₀ (j + 1) =
        R (j + 1) (unmarkRefl (raaState unmarkRefl R x₀ j)) := rfl
    rw [h1]
    apply hRRs (j + 1) (Nat.le_add_left 1 j) hjt
    rw [hUφ]
    exact Rs.add_mem (Rs.smul_mem _ hμRs) (Rs.smul_mem _ hνRs)

theorem mnrs_projection_lower
    (Mr Rs : Submodule ℂ W) (unmarkRefl : W ≃ₗᵢ[ℂ] W)
    (hMneg : ∀ z ∈ Mr, unmarkRefl z = -z)
    (hMid : ∀ z ∈ Mrᗮ, unmarkRefl z = z)
    (x₀ : W) (hx₀ : ‖x₀‖ = 1) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (t : ℕ) (R : ℕ → W ≃ₗᵢ[ℂ] W)
    (hxRs : x₀ ∈ Rs)
    (hclose : ∀ z ∈ Rs, markProj Mr z ∈ Rs)
    (hRRs : ∀ i, 1 ≤ i → i ≤ t → ∀ z ∈ Rs, R i z ∈ Rs)
    (hfix : ∀ i, 1 ≤ i → i ≤ t →
      R i (raaState unmarkRefl R x₀ (i - 1)) = raaState unmarkRefl R x₀ (i - 1))
    (hbound : ∀ i, 1 ≤ i → i ≤ t → ∀ ψ ∈ Rs,
      ψ ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ (i - 1)})ᗮ →
      ‖R i ψ + ψ - (2 : ℂ) • lineProj (raaState unmarkRefl R x₀ (i - 1)) ψ‖
        ≤ betaAt γ i * ‖ψ‖)
    (hwin : (3 : ℝ) ^ t * Real.arcsin (Real.sqrt (markedMass Mr x₀)) ∈
      Set.Icc (π / 4) (3 * π / 4))
    (hmin : ∀ j, j < t →
      (3 : ℝ) ^ j * Real.arcsin (Real.sqrt (markedMass Mr x₀)) ∉
        Set.Icc (π / 4) (3 * π / 4)) :
    1 / Real.sqrt 2 - γ ≤ ‖markProj Mr (raaState unmarkRefl R x₀ t)‖ := by
  have h0 : raaState unmarkRefl R x₀ 0 = x₀ := by simp [raaState, raaUnitary]
  have hs0val : ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ =
      Real.sqrt (markedMass Mr x₀) := by
    rw [h0]
    show ‖markProj Mr x₀‖ = Real.sqrt (‖markProj Mr x₀‖ ^ 2)
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hs0nn : 0 ≤ ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ := norm_nonneg _
  have hs0le : ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ ≤ 1 := by
    have h := Submodule.norm_starProjection_apply_le Mr (raaState unmarkRefl R x₀ 0)
    have hn : ‖raaState unmarkRefl R x₀ 0‖ = 1 := by rw [mnrs_raa_state_norm, hx₀]
    exact h.trans_eq hn
  have hwin' : (3 : ℝ) ^ t * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ ∈
      Set.Icc (π / 4) (3 * π / 4) := by
    rw [hs0val]
    exact hwin
  have hmin' : ∀ j, j < t →
      (3 : ℝ) ^ j * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ ∉
        Set.Icc (π / 4) (3 * π / 4) := by
    intro j hj
    rw [hs0val]
    exact hmin j hj
  rcases Nat.eq_zero_or_pos t with ht0 | ht0
  · subst ht0
    have hw' : 1 / Real.sqrt 2 ≤ ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ := by
      have hw0 : (3 : ℝ) ^ 0 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ ∈
          Set.Icc (π / 4) (3 * π / 4) := hwin'
      rw [pow_zero, one_mul] at hw0
      have hw := mnrs_sin_final_window _ hw0
      rwa [Real.sin_arcsin (by linarith [hs0nn]) hs0le] at hw
    linarith [hw', hγ0.le]
  · by_cases hγ2 : γ ≤ 1 / Real.sqrt 2
    swap
    · have hnn := norm_nonneg (markProj Mr (raaState unmarkRefl R x₀ t))
      linarith [hnn, not_le.mp hγ2]

    have hγ24 : γ ≤ 17 / 24 := by
      have h12 := mnrs_one_div_sqrt_two_le
      have h9924 : (99 : ℝ) / 140 ≤ 17 / 24 := by norm_num
      linarith [hγ2, h12, h9924]
    have hπ : Real.pi ≤ 63 / 20 := by
      rw [show (63 : ℝ) / 20 = 3.15 from by norm_num]
      exact Real.pi_lt_d2.le
    have hK : (18 : ℝ) / (4 * Real.pi ^ 3) ≤ 3 / 20 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi ^ 3)]
      have hπ3 : (30 : ℝ) ≤ Real.pi ^ 3 := by
        have h1 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3.14) Real.pi_gt_d2.le 3
        nlinarith [h1]
      nlinarith [hπ3]
    have hKnn : (0 : ℝ) ≤ 18 / (4 * Real.pi ^ 3) := by positivity
    have hβ : ∀ i : ℕ, betaAt γ i = (18 / (4 * Real.pi ^ 3)) * γ * ((i : ℝ) ^ 2)⁻¹ := by
      intro i
      unfold betaAt
      rw [div_eq_mul_inv]
    set A0 := Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ with hA0def
    set σ : ℕ → ℝ := fun n => ∑ l ∈ Finset.Icc 1 n, (1 : ℝ) / (l : ℝ) ^ 2 with hσdef
    set e : ℕ → ℝ := fun i =>
      |‖markProj Mr (raaState unmarkRefl R x₀ i)‖ - Real.sin ((3 : ℝ) ^ i * A0)| with hedef
    have hσeq : ∀ n, σ n = ∑ l ∈ Finset.Icc 1 n, (1 : ℝ) / (l : ℝ) ^ 2 := fun n => by
      rw [hσdef]
    have heeq : ∀ i, e i =
        |‖markProj Mr (raaState unmarkRefl R x₀ i)‖ - Real.sin ((3 : ℝ) ^ i * A0)| :=
      fun i => by rw [hedef]
    have hwin'' : (3 : ℝ) ^ t * A0 ∈ Set.Icc (π / 4) (3 * π / 4) := hwin'
    have hmin'' : ∀ j, j < t → (3 : ℝ) ^ j * A0 ∉ Set.Icc (π / 4) (3 * π / 4) := hmin'
    have hA0nn : 0 ≤ A0 := by
      rw [hA0def]
      exact Real.arcsin_nonneg.mpr hs0nn
    have hσ0 : σ 0 = 0 := by
      rw [hσeq]
      simp
    have hσsucc : ∀ n, σ (n + 1) = σ n + 1 / ((n : ℝ) + 1) ^ 2 := by
      intro n
      rw [hσeq (n + 1), hσeq n, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      congr 1
      simp only [Nat.cast_add, Nat.cast_one]
    have hσle : ∀ n, σ n ≤ 2 := fun n => by
      rw [hσeq n]
      exact mnrs_sum_inv_sq_le_two n
    have hσnn : ∀ n, 0 ≤ σ n := fun n => by
      rw [hσeq n]
      exact Finset.sum_nonneg (fun l _ => by positivity)
    have hbarnn : ∀ i, 0 ≤ (3 : ℝ) ^ i * A0 :=
      fun i => mul_nonneg (pow_nonneg (by norm_num) _) hA0nn
    have hbarmono : ∀ {a b : ℕ}, a ≤ b → (3 : ℝ) ^ a * A0 ≤ (3 : ℝ) ^ b * A0 :=
      fun hab => mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hab) hA0nn
    have hbarsucc : ∀ i, (3 : ℝ) ^ (i + 1) * A0 = 3 * ((3 : ℝ) ^ i * A0) := by
      intro i
      rw [pow_succ]
      ring
    have ht11 : t - 1 + 1 = t := by omega
    have hbarteq : (3 : ℝ) ^ t * A0 = 3 * ((3 : ℝ) ^ (t - 1) * A0) := by
      have h := hbarsucc (t - 1)
      rwa [ht11] at h
    have hbart1le : (3 : ℝ) ^ (t - 1) * A0 ≤ π / 4 := by
      have h := hwin''.2
      linarith [hbarteq, h, Real.pi_pos]
    have he0 : e 0 = 0 := by
      rw [heeq 0, hA0def, pow_zero, one_mul,
        Real.sin_arcsin (by linarith [hs0nn]) hs0le, sub_self, abs_zero]

    have hP : ∀ j, j + 1 ≤ t →
        (raaState unmarkRefl R x₀ j ∈ Rs) ∧
        e j ≤ γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * σ j := by
      intro j
      induction j with
      | zero =>
        intro _
        refine ⟨by rw [h0]; exact hxRs, ?_⟩
        rw [he0, hσ0]
        simp
      | succ j ih =>
        intro hj
        obtain ⟨hRsj, hej⟩ := ih (by omega)
        have hbarjle : (3 : ℝ) ^ j * A0 ≤ π / 12 := by
          have h1 := hbarmono (show j + 1 ≤ t - 1 by omega)
          rw [hbarsucc j] at h1
          linarith [hbart1le, Real.pi_pos]
        have hŝnn : 0 ≤ Real.sin ((3 : ℝ) ^ j * A0) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (hbarnn j)
            (by linarith [hbarjle, Real.pi_pos])
        have hŝ : Real.sin ((3 : ℝ) ^ j * A0) ≤ 21 / 80 := by
          have h1 := Real.sin_le_sin_of_le_of_le_pi_div_two
            (by linarith [hbarnn j, Real.pi_pos] : -(π / 2) ≤ (3 : ℝ) ^ j * A0)
            (by linarith [Real.pi_pos] : π / 12 ≤ π / 2) hbarjle
          have h2 := Real.sin_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 12)
          linarith [h1, h2, hπ]
        have hejnn : 0 ≤ e j := abs_nonneg _
        have hsjnn : 0 ≤ ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ := norm_nonneg _
        have hsjle : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ≤ 1 := by
          have h := Submodule.norm_starProjection_apply_le Mr (raaState unmarkRefl R x₀ j)
          have hn : ‖raaState unmarkRefl R x₀ j‖ = 1 := by rw [mnrs_raa_state_norm, hx₀]
          exact h.trans_eq hn
        have hsinϕj : Real.sin (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) =
            ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ :=
          Real.sin_arcsin (by linarith [hsjnn]) hsjle
        have hsje : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ≤
            Real.sin ((3 : ℝ) ^ j * A0) + e j := by
          have h : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ - Real.sin ((3 : ℝ) ^ j * A0) ≤
              e j := le_abs_self _
          linarith [h]
        have hej2 : e j ≤ γ * ((3 : ℝ) ^ j * A0) / 4 := by
          calc e j ≤ γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * σ j := hej
            _ ≤ γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * 2 :=
                mul_le_mul_of_nonneg_left (hσle j)
                  (mul_nonneg (mul_nonneg hγ0.le (hbarnn j)) (by norm_num))
            _ = γ * ((3 : ℝ) ^ j * A0) / 4 := by ring
        have hej3 : e j ≤ 21 / 320 := by
          have h1 : γ * ((3 : ℝ) ^ j * A0) ≤ 1 * (π / 12) :=
            mul_le_mul hγ1 hbarjle (hbarnn j) zero_le_one
          have h2 : (1 : ℝ) * (π / 12) / 4 ≤ 21 / 320 := by linarith [hπ]
          calc e j ≤ γ * ((3 : ℝ) ^ j * A0) / 4 := hej2
            _ ≤ 1 * (π / 12) / 4 := by gcongr
            _ ≤ 21 / 320 := h2
        have hsj : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ≤ 21 / 64 := by
          linarith [hsje, hŝ, hej3]
        have hsjsq : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 ≤ 3 / 4 := by
          have h1 : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 ≤ (21 / 64 : ℝ) ^ 2 :=
            (sq_le_sq₀ hsjnn (by norm_num)).mpr hsj
          nlinarith [h1]
        have hϕjle : Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ≤ π / 3 :=
          mnrs_arcsin_le_pi_div_three hsjnn hsjsq
        have hTj : |3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 +
            ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ * Real.sin ((3 : ℝ) ^ j * A0) +
            Real.sin ((3 : ℝ) ^ j * A0) ^ 2)| ≤ 3 := by
          have hTnn : 0 ≤ ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 +
              ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ * Real.sin ((3 : ℝ) ^ j * A0) +
              Real.sin ((3 : ℝ) ^ j * A0) ^ 2 :=
            add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hsjnn hŝnn)) (sq_nonneg _)
          have hTle : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 +
              ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ * Real.sin ((3 : ℝ) ^ j * A0) +
              Real.sin ((3 : ℝ) ^ j * A0) ^ 2 ≤ 3 / 2 := by
            have h1 : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 ≤ (21 / 64 : ℝ) ^ 2 :=
              (sq_le_sq₀ hsjnn (by norm_num)).mpr hsj
            have h2 : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ *
                Real.sin ((3 : ℝ) ^ j * A0) ≤ (21 / 64 : ℝ) * (21 / 80) :=
              mul_le_mul hsj hŝ hŝnn (by norm_num : (0 : ℝ) ≤ 21 / 64)
            have h3 : Real.sin ((3 : ℝ) ^ j * A0) ^ 2 ≤ (21 / 80 : ℝ) ^ 2 :=
              (sq_le_sq₀ hŝnn (by norm_num)).mpr hŝ
            nlinarith [h1, h2, h3]
          rw [abs_le]
          constructor <;> linarith [hTnn, hTle]
        obtain ⟨hstep, hRsj1⟩ := mnrs_raa_step Mr Rs unmarkRefl hMneg hMid x₀ hx₀ γ hγ0 R t
          hclose hRRs hfix hbound j (by omega) hRsj hϕjle
        have h2ϕnn : 0 ≤ Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) := by
          apply Real.sin_nonneg_of_nonneg_of_le_pi
          · have h1 := Real.arcsin_nonneg.mpr hsjnn
            linarith [h1]
          · linarith [hϕjle, Real.pi_pos]
        have hsin2 : |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)| ≤
            2 * (((3 : ℝ) ^ j * A0) + e j) := by
          rw [abs_of_nonneg h2ϕnn, Real.sin_two_mul]
          have hc1 := Real.cos_le_one (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)
          have hsc : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ *
              Real.cos (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) ≤
              ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ := by
            have h := mul_le_mul_of_nonneg_left hc1 hsjnn
            simpa using h
          have hsgbar : ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ≤
              (3 : ℝ) ^ j * A0 + e j := by
            have h1 := Real.sin_le (hbarnn j)
            linarith [hsje, h1]
          rw [hsinϕj]
          linarith [hsc, hsgbar, hsjnn]
        have hrec : e (j + 1) ≤
            2 * betaAt γ (j + 1) * (((3 : ℝ) ^ j * A0) + e j) + 3 * e j := by
          have hsplit : e (j + 1) ≤ |‖markProj Mr (raaState unmarkRefl R x₀ (j + 1))‖ -
              Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)| +
              |Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) -
                Real.sin ((3 : ℝ) ^ (j + 1) * A0)| := by
            rw [heeq (j + 1)]
            have h2 : ‖markProj Mr (raaState unmarkRefl R x₀ (j + 1))‖ -
                Real.sin ((3 : ℝ) ^ (j + 1) * A0) =
                (‖markProj Mr (raaState unmarkRefl R x₀ (j + 1))‖ -
                  Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)) +
                (Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) -
                  Real.sin ((3 : ℝ) ^ (j + 1) * A0)) := by ring
            rw [h2]
            exact abs_add_le _ _
          have hfac : |Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) -
              Real.sin ((3 : ℝ) ^ (j + 1) * A0)| =
              e j * |3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 +
                ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ * Real.sin ((3 : ℝ) ^ j * A0) +
                Real.sin ((3 : ℝ) ^ j * A0) ^ 2)| := by
            rw [hbarsucc j]
            have h := mnrs_sin_three_sub
              (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖) ((3 : ℝ) ^ j * A0)
            rw [hsinϕj] at h
            rw [h, abs_mul, heeq j]
          calc e (j + 1) ≤ _ := hsplit
            _ = |‖markProj Mr (raaState unmarkRefl R x₀ (j + 1))‖ -
                  Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)| +
                e j * |3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ j)‖ ^ 2 +
                  ‖markProj Mr (raaState unmarkRefl R x₀ j)‖ * Real.sin ((3 : ℝ) ^ j * A0) +
                  Real.sin ((3 : ℝ) ^ j * A0) ^ 2)| := by rw [hfac]
            _ ≤ betaAt γ (j + 1) *
                  |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ j)‖)| +
                e j * 3 := add_le_add hstep (mul_le_mul_of_nonneg_left hTj hejnn)
            _ ≤ 2 * betaAt γ (j + 1) * (((3 : ℝ) ^ j * A0) + e j) + 3 * e j := by
                have hβnn : 0 ≤ betaAt γ (j + 1) := by
                  rw [hβ (j + 1)]
                  exact mul_nonneg (mul_nonneg hKnn hγ0.le) (inv_nonneg.mpr (sq_nonneg _))
                have h1 := mul_le_mul_of_nonneg_left hsin2 hβnn
                nlinarith [h1]
        have hkey : 2 * (18 / (4 * Real.pi ^ 3)) +
            (18 / (4 * Real.pi ^ 3)) * γ * σ j / 4 ≤ 3 / 8 := by
          have hKγ : (18 / (4 * Real.pi ^ 3)) * γ ≤ 18 / (4 * Real.pi ^ 3) := by
            calc (18 / (4 * Real.pi ^ 3)) * γ ≤ (18 / (4 * Real.pi ^ 3)) * 1 :=
                  mul_le_mul_of_nonneg_left hγ1 hKnn
              _ = 18 / (4 * Real.pi ^ 3) := mul_one _
          have hKγσ : (18 / (4 * Real.pi ^ 3)) * γ * σ j ≤ (18 / (4 * Real.pi ^ 3)) * 2 := by
            calc (18 / (4 * Real.pi ^ 3)) * γ * σ j ≤ (18 / (4 * Real.pi ^ 3)) * σ j :=
                  mul_le_mul_of_nonneg_right hKγ (hσnn j)
              _ ≤ (18 / (4 * Real.pi ^ 3)) * 2 :=
                  mul_le_mul_of_nonneg_left (hσle j) hKnn
          linarith [hK, hKγσ]
        have hβj1 : betaAt γ (j + 1) =
            (18 / (4 * Real.pi ^ 3)) * γ * (((j : ℝ) + 1) ^ 2)⁻¹ := by
          rw [hβ (j + 1)]
          simp only [Nat.cast_add, Nat.cast_one]
        have hest : 2 * betaAt γ (j + 1) * (((3 : ℝ) ^ j * A0) + e j) + 3 * e j ≤
            γ * ((3 : ℝ) ^ (j + 1) * A0) * (1 / 8) * σ (j + 1) := by
          rw [hβj1, hbarsucc j, hσsucc j, one_div]
          have hq : (0 : ℝ) < ((j : ℝ) + 1) ^ 2 := by positivity
          have hstep1 : 2 * ((18 / (4 * Real.pi ^ 3)) * γ * (((j : ℝ) + 1) ^ 2)⁻¹) *
                (((3 : ℝ) ^ j * A0) + e j) + 3 * e j ≤
              2 * ((18 / (4 * Real.pi ^ 3)) * γ * (((j : ℝ) + 1) ^ 2)⁻¹) *
                (((3 : ℝ) ^ j * A0) + γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * σ j) +
                3 * (γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * σ j) := by
            have hXnn : (0 : ℝ) ≤
                2 * ((18 / (4 * Real.pi ^ 3)) * γ * (((j : ℝ) + 1) ^ 2)⁻¹) :=
              mul_nonneg (by norm_num)
                (mul_nonneg (mul_nonneg hKnn hγ0.le) (inv_nonneg.mpr (sq_nonneg _)))
            have hXR : (3 : ℝ) ^ j * A0 + e j ≤
                (3 : ℝ) ^ j * A0 + γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * σ j := by
              linarith only [hej]
            exact add_le_add
              (mul_le_mul_of_nonneg_left hXR hXnn)
              (mul_le_mul_of_nonneg_left hej (by norm_num : (0 : ℝ) ≤ 3))
          have hstep2 : 2 * ((18 / (4 * Real.pi ^ 3)) * γ * (((j : ℝ) + 1) ^ 2)⁻¹) *
                (((3 : ℝ) ^ j * A0) + γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * σ j) +
                3 * (γ * ((3 : ℝ) ^ j * A0) * (1 / 8) * σ j) =
              γ * ((3 : ℝ) ^ j * A0) * ((2 * (18 / (4 * Real.pi ^ 3)) +
                (18 / (4 * Real.pi ^ 3)) * γ * σ j / 4) * (((j : ℝ) + 1) ^ 2)⁻¹ +
                (3 / 8) * σ j) := by
            ring
          have hstep3 : γ * ((3 : ℝ) ^ j * A0) * ((2 * (18 / (4 * Real.pi ^ 3)) +
                (18 / (4 * Real.pi ^ 3)) * γ * σ j / 4) * (((j : ℝ) + 1) ^ 2)⁻¹ +
                (3 / 8) * σ j) ≤
              γ * ((3 : ℝ) ^ j * A0) * ((3 / 8) * (((j : ℝ) + 1) ^ 2)⁻¹ + (3 / 8) * σ j) := by
            have hmulinv := mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr hq.le)
            have hinner : (2 * (18 / (4 * Real.pi ^ 3)) +
                (18 / (4 * Real.pi ^ 3)) * γ * σ j / 4) * (((j : ℝ) + 1) ^ 2)⁻¹ +
                (3 / 8) * σ j ≤
                (3 / 8) * (((j : ℝ) + 1) ^ 2)⁻¹ + (3 / 8) * σ j := by
              linarith only [hmulinv]
            exact mul_le_mul_of_nonneg_left hinner (mul_nonneg hγ0.le (hbarnn j))
          have hstep4 : γ * ((3 : ℝ) ^ j * A0) *
                ((3 / 8) * (((j : ℝ) + 1) ^ 2)⁻¹ + (3 / 8) * σ j) =
              γ * (3 * ((3 : ℝ) ^ j * A0)) * (1 / 8) * (σ j + (((j : ℝ) + 1) ^ 2)⁻¹) := by
            ring
          calc 2 * ((18 / (4 * Real.pi ^ 3)) * γ * (((j : ℝ) + 1) ^ 2)⁻¹) *
                (((3 : ℝ) ^ j * A0) + e j) + 3 * e j ≤ _ := hstep1
            _ = _ := hstep2
            _ ≤ _ := hstep3
            _ = γ * (3 * ((3 : ℝ) ^ j * A0)) * (1 / 8) * (σ j + (((j : ℝ) + 1) ^ 2)⁻¹) :=
              hstep4
            _ = γ * (3 * ((3 : ℝ) ^ j * A0)) * 8⁻¹ * (σ j + 1 / ((j : ℝ) + 1) ^ 2) := by
              ring
        exact ⟨hRsj1, hrec.trans hest⟩

    obtain ⟨hRs1, he1⟩ := hP (t - 1) (by omega)
    have he1nn : 0 ≤ e (t - 1) := abs_nonneg _
    have he1b : e (t - 1) ≤ γ * ((3 : ℝ) ^ (t - 1) * A0) / 4 := by
      calc e (t - 1) ≤ γ * ((3 : ℝ) ^ (t - 1) * A0) * (1 / 8) * σ (t - 1) := he1
        _ ≤ γ * ((3 : ℝ) ^ (t - 1) * A0) * (1 / 8) * 2 :=
            mul_le_mul_of_nonneg_left (hσle _)
              (mul_nonneg (mul_nonneg hγ0.le (hbarnn _)) (by norm_num))
        _ = γ * ((3 : ℝ) ^ (t - 1) * A0) / 4 := by ring
    have he1c : e (t - 1) ≤ γ * (63 / 320) := by
      have h1 : (3 : ℝ) ^ (t - 1) * A0 / 4 ≤ (π / 4) / 4 := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
        have h2 := hbart1le
        linarith [h2, Real.pi_pos]
      have h4 : (π / 4 : ℝ) / 4 ≤ 63 / 320 := by linarith [hπ]
      calc e (t - 1) ≤ γ * ((3 : ℝ) ^ (t - 1) * A0) / 4 := he1b
        _ = γ * ((3 : ℝ) ^ (t - 1) * A0 / 4) := by ring
        _ ≤ γ * (63 / 320) := mul_le_mul_of_nonneg_left (h1.trans h4) hγ0.le
    have he1d : e (t - 1) ≤ 1071 / 7680 := by
      calc e (t - 1) ≤ γ * (63 / 320) := he1c
        _ ≤ (17 / 24) * (63 / 320) := mul_le_mul_of_nonneg_right hγ24 (by norm_num)
        _ = 1071 / 7680 := by norm_num
    have hŝ1nn : 0 ≤ Real.sin ((3 : ℝ) ^ (t - 1) * A0) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (hbarnn _)
        (by linarith [hbart1le, Real.pi_pos])
    have hŝ1 : Real.sin ((3 : ℝ) ^ (t - 1) * A0) ≤ 1 / Real.sqrt 2 := by
      have h1 := Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [hbarnn (t - 1), Real.pi_pos] : -(π / 2) ≤ (3 : ℝ) ^ (t - 1) * A0)
        (by linarith [Real.pi_pos] : π / 4 ≤ π / 2) hbart1le
      rwa [Real.sin_pi_div_four, mnrs_sqrt_two_div_two] at h1
    have hs1nn : 0 ≤ ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ := norm_nonneg _
    have hs1le : ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ≤ 1 := by
      have h := Submodule.norm_starProjection_apply_le Mr (raaState unmarkRefl R x₀ (t - 1))
      have hn : ‖raaState unmarkRefl R x₀ (t - 1)‖ = 1 := by rw [mnrs_raa_state_norm, hx₀]
      exact h.trans_eq hn
    have hs1e : ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ≤
        Real.sin ((3 : ℝ) ^ (t - 1) * A0) + e (t - 1) := by
      have h : ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ -
          Real.sin ((3 : ℝ) ^ (t - 1) * A0) ≤ e (t - 1) := le_abs_self _
      linarith [h]
    have hs1 : ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ≤ 15171 / 17920 := by
      have h1 := hŝ1.trans mnrs_one_div_sqrt_two_le
      linarith [hs1e, h1, he1d]
    have hs1sq : ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 ≤ 3 / 4 := by
      have h1 : ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 ≤
          (15171 / 17920 : ℝ) ^ 2 := (sq_le_sq₀ hs1nn (by norm_num)).mpr hs1
      nlinarith [h1]
    have hϕ1le : Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ≤ π / 3 :=
      mnrs_arcsin_le_pi_div_three hs1nn hs1sq
    have hT1 : |3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 +
        ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ * Real.sin ((3 : ℝ) ^ (t - 1) * A0) +
        Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2)| ≤
        3 + 6 * Real.sqrt 2 * e (t - 1) + 4 * e (t - 1) ^ 2 := by
      have hTnn : 0 ≤ ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 +
          ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ * Real.sin ((3 : ℝ) ^ (t - 1) * A0) +
          Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2 :=
        add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hs1nn hŝ1nn)) (sq_nonneg _)
      have hsq2 : Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2 ≤ 1 / 2 := by
        have h1 : Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2 ≤ (1 / Real.sqrt 2) ^ 2 :=
          (sq_le_sq₀ hŝ1nn (by positivity)).mpr hŝ1
        have h2 : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
          rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        rwa [h2] at h1
      have hssq : ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 ≤
          (Real.sin ((3 : ℝ) ^ (t - 1) * A0) + e (t - 1)) ^ 2 :=
        (sq_le_sq₀ hs1nn (add_nonneg hŝ1nn he1nn)).mpr hs1e
      have hsŝ : ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ *
          Real.sin ((3 : ℝ) ^ (t - 1) * A0) ≤
          (Real.sin ((3 : ℝ) ^ (t - 1) * A0) + e (t - 1)) *
            Real.sin ((3 : ℝ) ^ (t - 1) * A0) :=
        mul_le_mul_of_nonneg_right hs1e hŝ1nn
      have h12 : (12 : ℝ) / Real.sqrt 2 = 6 * Real.sqrt 2 := by
        rw [div_eq_iff (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
        calc (12 : ℝ) = 6 * 2 := by norm_num
          _ = 6 * (Real.sqrt 2 * Real.sqrt 2) := by
              rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          _ = 6 * Real.sqrt 2 * Real.sqrt 2 := by ring
      have h12e : (12 / Real.sqrt 2) * e (t - 1) = 6 * Real.sqrt 2 * e (t - 1) := by
        rw [h12]
      have hexp1 : (Real.sin ((3 : ℝ) ^ (t - 1) * A0) + e (t - 1)) ^ 2 =
          Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2 +
          2 * Real.sin ((3 : ℝ) ^ (t - 1) * A0) * e (t - 1) + e (t - 1) ^ 2 := by ring
      rw [hexp1] at hssq
      have hexp2 : (Real.sin ((3 : ℝ) ^ (t - 1) * A0) + e (t - 1)) *
          Real.sin ((3 : ℝ) ^ (t - 1) * A0) =
          Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2 +
          Real.sin ((3 : ℝ) ^ (t - 1) * A0) * e (t - 1) := by ring
      rw [hexp2] at hsŝ
      have hse12 : 12 * Real.sin ((3 : ℝ) ^ (t - 1) * A0) * e (t - 1) ≤
          6 * Real.sqrt 2 * e (t - 1) := by
        have h1 := mul_le_mul_of_nonneg_right hŝ1 he1nn
        have h1' : (12 : ℝ) * (Real.sin ((3 : ℝ) ^ (t - 1) * A0) * e (t - 1)) ≤
            12 * ((1 / Real.sqrt 2) * e (t - 1)) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
        have h2 : 12 * ((1 / Real.sqrt 2) * e (t - 1)) =
            6 * Real.sqrt 2 * e (t - 1) := by
          rw [← h12]; ring
        calc 12 * Real.sin ((3 : ℝ) ^ (t - 1) * A0) * e (t - 1) =
              12 * (Real.sin ((3 : ℝ) ^ (t - 1) * A0) * e (t - 1)) := by ring
          _ ≤ 12 * ((1 / Real.sqrt 2) * e (t - 1)) := h1'
          _ = 6 * Real.sqrt 2 * e (t - 1) := h2
      have hd : 4 * (‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 +
          ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ * Real.sin ((3 : ℝ) ^ (t - 1) * A0) +
          Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2) =
          4 * ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 +
          4 * ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ *
            Real.sin ((3 : ℝ) ^ (t - 1) * A0) +
          4 * Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2 := by ring
      have hTle : 4 * (‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 +
          ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ * Real.sin ((3 : ℝ) ^ (t - 1) * A0) +
          Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2) ≤
          6 + 6 * Real.sqrt 2 * e (t - 1) + 4 * e (t - 1) ^ 2 := by
        rw [hd]
        linarith [hssq, hsŝ, hsq2, hse12]
      rw [show 3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 +
            ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ *
              Real.sin ((3 : ℝ) ^ (t - 1) * A0) +
            Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2) =
          3 - 4 * ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 -
          4 * ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ *
            Real.sin ((3 : ℝ) ^ (t - 1) * A0) -
          4 * Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2 from by ring]
      rw [abs_le]
      constructor
      · linarith [hTle]
      · have hRHSnn : (0 : ℝ) ≤ 3 + 6 * Real.sqrt 2 * e (t - 1) + 4 * e (t - 1) ^ 2 := by
          positivity
        have hprod1 : (0 : ℝ) ≤ 6 * Real.sqrt 2 * e (t - 1) :=
          mul_nonneg (by positivity) he1nn
        have hprod2 : (0 : ℝ) ≤ 4 * e (t - 1) ^ 2 := by positivity
        linarith [hTnn, hprod1, hprod2]
    obtain ⟨hstep10, -⟩ := mnrs_raa_step Mr Rs unmarkRefl hMneg hMid x₀ hx₀ γ hγ0 R t
      hclose hRRs hfix hbound (t - 1) (by omega) hRs1 hϕ1le
    rw [ht11] at hstep10
    have h2ϕ1nn : 0 ≤
        Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · have h1 := Real.arcsin_nonneg.mpr hs1nn
        linarith [h1]
      · linarith [hϕ1le, Real.pi_pos]
    have hsinϕ1 : Real.sin (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖) =
        ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ :=
      Real.sin_arcsin (by linarith [hs1nn]) hs1le
    have hsin2' : |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖)| ≤
        2 * (((3 : ℝ) ^ (t - 1) * A0) + e (t - 1)) := by
      rw [abs_of_nonneg h2ϕ1nn, Real.sin_two_mul]
      have hc1 := Real.cos_le_one (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖)
      have hsc : ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ *
          Real.cos (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖) ≤
          ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ := by
        have h := mul_le_mul_of_nonneg_left hc1 hs1nn
        simpa using h
      have hsgbar1 : ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ≤
          (3 : ℝ) ^ (t - 1) * A0 + e (t - 1) := by
        have h1 := Real.sin_le (hbarnn (t - 1))
        linarith [hs1e, h1]
      rw [hsinϕ1]
      linarith [hsc, hsgbar1, hs1nn]
    have hfac1 : |Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖) -
        Real.sin ((3 : ℝ) ^ t * A0)| =
        e (t - 1) * |3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 +
          ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ * Real.sin ((3 : ℝ) ^ (t - 1) * A0) +
          Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2)| := by
      rw [hbarteq]
      have h := mnrs_sin_three_sub
        (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖) ((3 : ℝ) ^ (t - 1) * A0)
      rw [hsinϕ1] at h
      rw [h, abs_mul, heeq (t - 1)]
    have het : e t ≤ betaAt γ t *
        |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖)| +
        e (t - 1) * |3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 +
          ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ * Real.sin ((3 : ℝ) ^ (t - 1) * A0) +
          Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2)| := by
      have hsplit : e t ≤ |‖markProj Mr (raaState unmarkRefl R x₀ t)‖ -
          Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖)| +
          |Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖) -
            Real.sin ((3 : ℝ) ^ t * A0)| := by
        rw [heeq t]
        have h2 : ‖markProj Mr (raaState unmarkRefl R x₀ t)‖ - Real.sin ((3 : ℝ) ^ t * A0) =
            (‖markProj Mr (raaState unmarkRefl R x₀ t)‖ -
              Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖)) +
            (Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖) -
              Real.sin ((3 : ℝ) ^ t * A0)) := by ring
        rw [h2]
        exact abs_add_le _ _
      calc e t ≤ _ := hsplit
        _ = |‖markProj Mr (raaState unmarkRefl R x₀ t)‖ -
              Real.sin (3 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖)| +
            e (t - 1) * |3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 +
              ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ *
                Real.sin ((3 : ℝ) ^ (t - 1) * A0) +
              Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2)| := by rw [hfac1]
        _ ≤ _ := add_le_add hstep10 le_rfl
    have hetγ : e t ≤ γ := by
      by_cases ht2 : 2 ≤ t
      · have ht2' : (4 : ℝ) ≤ (t : ℝ) ^ 2 := by
          have h1 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht2
          nlinarith [h1]
        have hβt : betaAt γ t ≤ (18 / (4 * Real.pi ^ 3)) * γ / 4 := by
          show (18 / (4 * Real.pi ^ 3)) * γ / (t : ℝ) ^ 2 ≤ (18 / (4 * Real.pi ^ 3)) * γ / 4
          exact div_le_div_of_nonneg_left (mul_nonneg hKnn hγ0.le) (by norm_num) ht2'
        have hterm1 : betaAt γ t *
            |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖)| ≤
            γ * (7119 / 102400) := by
          have h1 : (0 : ℝ) ≤ (18 / (4 * Real.pi ^ 3)) * γ / 4 :=
            div_nonneg (mul_nonneg hKnn hγ0.le) (by norm_num)
          have hK' : (18 / (4 * Real.pi ^ 3)) / 4 * 2 ≤ (3 / 20 : ℝ) / 4 * 2 := by
            calc (18 / (4 * Real.pi ^ 3)) / 4 * 2 = (18 / (4 * Real.pi ^ 3)) * (1 / 4 * 2) := by
                  ring
              _ ≤ (3 / 20) * (1 / 4 * 2) :=
                  mul_le_mul_of_nonneg_right hK (by norm_num)
              _ = (3 / 20) / 4 * 2 := by ring
          have hX : (π : ℝ) / 4 + γ * (63 / 320) ≤ (63 / 20) / 4 + (17 / 24) * (63 / 320) := by
            have h1 : (π : ℝ) / 4 ≤ (63 / 20) / 4 := by linarith [hπ]
            have h2 : γ * (63 / 320 : ℝ) ≤ (17 / 24) * (63 / 320) :=
              mul_le_mul_of_nonneg_right hγ24 (by norm_num)
            linarith [h1, h2]
          have hXnn : (0 : ℝ) ≤ (π : ℝ) / 4 + γ * (63 / 320) :=
            add_nonneg (by positivity) (mul_nonneg hγ0.le (by norm_num))
          calc betaAt γ t *
              |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖)|
              ≤ ((18 / (4 * Real.pi ^ 3)) * γ / 4) *
                  (2 * (((3 : ℝ) ^ (t - 1) * A0) + e (t - 1))) :=
                mul_le_mul hβt hsin2' (abs_nonneg _) h1
            _ ≤ ((18 / (4 * Real.pi ^ 3)) * γ / 4) * (2 * ((π / 4) + γ * (63 / 320))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (add_le_add hbart1le he1c) (by norm_num)) h1
            _ = γ * ((18 / (4 * Real.pi ^ 3)) / 4 * 2 * ((π / 4) + γ * (63 / 320))) := by ring
            _ ≤ γ * ((3 / 20) / 4 * 2 * (((63 / 20) / 4) + (17 / 24) * (63 / 320))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul hK' hX hXnn (by norm_num)) hγ0.le
            _ = γ * (7119 / 102400) := by
                congr 1
                norm_num
        have hterm2 : e (t - 1) * |3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 +
            ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ * Real.sin ((3 : ℝ) ^ (t - 1) * A0) +
            Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2)| ≤
            γ * ((63 / 320) * (3 + 6 * (99 / 70) * (1071 / 7680) + 4 * (1071 / 7680) ^ 2)) := by
          have hC0 : |3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 +
              ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ *
                Real.sin ((3 : ℝ) ^ (t - 1) * A0) +
              Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2)| ≤
              3 + 6 * (99 / 70) * (1071 / 7680) + 4 * (1071 / 7680) ^ 2 := by
            have h1 : Real.sqrt 2 * e (t - 1) ≤ (99 / 70) * e (t - 1) :=
              mul_le_mul_of_nonneg_right mnrs_sqrt_two_le he1nn
            have h2 : (99 / 70 : ℝ) * e (t - 1) ≤ (99 / 70) * (1071 / 7680) :=
              mul_le_mul_of_nonneg_left he1d (by norm_num)
            have h3 : e (t - 1) ^ 2 ≤ (1071 / 7680 : ℝ) ^ 2 :=
              (sq_le_sq₀ he1nn (by norm_num)).mpr he1d
            linarith [hT1, h1, h2, h3]
          calc e (t - 1) * |3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 +
              ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ *
                Real.sin ((3 : ℝ) ^ (t - 1) * A0) +
              Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2)|
              ≤ (γ * (63 / 320)) *
                  (3 + 6 * (99 / 70) * (1071 / 7680) + 4 * (1071 / 7680) ^ 2) :=
                mul_le_mul he1c hC0 (abs_nonneg _) (mul_nonneg hγ0.le (by norm_num))
            _ = γ * ((63 / 320) * (3 + 6 * (99 / 70) * (1071 / 7680) + 4 * (1071 / 7680) ^ 2)) :=
                by ring
        have hF : (7119 / 102400 : ℝ) +
            (63 / 320) * (3 + 6 * (99 / 70) * (1071 / 7680) + 4 * (1071 / 7680) ^ 2) ≤ 1 := by
          norm_num
        calc e t ≤ betaAt γ t *
              |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖)| +
              e (t - 1) * |3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ ^ 2 +
                ‖markProj Mr (raaState unmarkRefl R x₀ (t - 1))‖ *
                  Real.sin ((3 : ℝ) ^ (t - 1) * A0) +
                Real.sin ((3 : ℝ) ^ (t - 1) * A0) ^ 2)| := het
          _ ≤ γ * (7119 / 102400) +
              γ * ((63 / 320) * (3 + 6 * (99 / 70) * (1071 / 7680) + 4 * (1071 / 7680) ^ 2)) :=
            add_le_add hterm1 hterm2
          _ = γ * ((7119 / 102400) +
              (63 / 320) * (3 + 6 * (99 / 70) * (1071 / 7680) + 4 * (1071 / 7680) ^ 2)) := by ring
          _ ≤ γ * 1 := mul_le_mul_of_nonneg_left hF hγ0.le
          _ = γ := mul_one γ
      · have ht1 : t = 1 := by omega
        subst ht1
        have het1 : e 1 ≤ betaAt γ 1 *
            |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖)| +
            e 0 * |3 - 4 * (‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ ^ 2 +
              ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ * Real.sin ((3 : ℝ) ^ 0 * A0) +
              Real.sin ((3 : ℝ) ^ 0 * A0) ^ 2)| := het
        rw [he0] at het1
        simp only [zero_mul, add_zero] at het1
        have hϕ0le : Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ ≤ π / 4 := by
          have h := hwin''.2
          rw [pow_one] at h
          rw [← hA0def]
          linarith [h, Real.pi_pos]
        have hsin20 : |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖)| ≤
            2 * (π / 4) := by
          have h2ϕ0nn : 0 ≤ Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖) := by
            apply Real.sin_nonneg_of_nonneg_of_le_pi
            · have h1 := Real.arcsin_nonneg.mpr hs0nn
              linarith [h1]
            · linarith [hϕ0le, Real.pi_pos]
          rw [abs_of_nonneg h2ϕ0nn, Real.sin_two_mul]
          have hsinϕ0 : Real.sin (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖) =
              ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ :=
            Real.sin_arcsin (by linarith [hs0nn]) hs0le
          have hc1 := Real.cos_le_one (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖)
          have hsc : ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ *
              Real.cos (Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖) ≤
              ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ := by
            have h := mul_le_mul_of_nonneg_left hc1 hs0nn
            simpa using h
          have hs0ϕ : ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ ≤
              Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ := by
            have h := Real.sin_le (Real.arcsin_nonneg.mpr hs0nn)
            rwa [hsinϕ0] at h
          rw [hsinϕ0]
          have h2 : ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖ ≤ π / 4 := hs0ϕ.trans hϕ0le
          linarith [hsc, h2, hs0nn]
        have hβ1 : betaAt γ 1 = (18 / (4 * Real.pi ^ 3)) * γ := by
          rw [hβ 1]
          norm_num
        calc e 1 ≤ betaAt γ 1 *
            |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖)| := het1
          _ = (18 / (4 * Real.pi ^ 3)) * γ *
              |Real.sin (2 * Real.arcsin ‖markProj Mr (raaState unmarkRefl R x₀ 0)‖)| := by
            rw [hβ1]
          _ ≤ (18 / (4 * Real.pi ^ 3)) * γ * (2 * (π / 4)) :=
              mul_le_mul_of_nonneg_left hsin20 (mul_nonneg hKnn hγ0.le)
          _ ≤ (3 / 20) * γ * (2 * ((63 / 20) / 4)) := by
              have h1 : γ * (2 * (π / 4)) ≤ γ * (2 * ((63 / 20) / 4)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (by linarith [hπ] : (π : ℝ) / 4 ≤ (63 / 20) / 4)
                    (by norm_num)) hγ0.le
              have h2 : (0 : ℝ) ≤ γ * (2 * (π / 4)) :=
                mul_nonneg hγ0.le (mul_nonneg (by norm_num) (by positivity))
              calc (18 / (4 * Real.pi ^ 3)) * γ * (2 * (π / 4))
                  = (18 / (4 * Real.pi ^ 3)) * (γ * (2 * (π / 4))) := by ring
                _ ≤ (3 / 20) * (γ * (2 * ((63 / 20) / 4))) :=
                    mul_le_mul hK h1 h2 (by norm_num)
                _ = (3 / 20) * γ * (2 * ((63 / 20) / 4)) := by ring
          _ = γ * (189 / 800) := by ring
          _ ≤ γ * 1 := mul_le_mul_of_nonneg_left (by norm_num) hγ0.le
          _ = γ := mul_one γ

    have hsin_win : 1 / Real.sqrt 2 ≤ Real.sin ((3 : ℝ) ^ t * A0) :=
      mnrs_sin_final_window _ hwin''
    have hfin : Real.sin ((3 : ℝ) ^ t * A0) - e t ≤
        ‖markProj Mr (raaState unmarkRefl R x₀ t)‖ := by
      have h : -(‖markProj Mr (raaState unmarkRefl R x₀ t)‖ - Real.sin ((3 : ℝ) ^ t * A0)) ≤
          e t := neg_le_abs _
      linarith [h]
    linarith [hsin_win, hetγ, hfin]

theorem mnrs_approximate_raa_lemma_one : Lemma1 := by
  intro W _ _ _ Mr unmarkRefl hMneg hMid x₀ hx₀ γ hγ0 hγ1 t R c₁ c₂ hc₁ hc₂
    costR costMark Rs hxRs hclose hRRs hfix hbound hcost hmark hwin hmin
  constructor
  · exact mnrs_projection_lower Mr Rs unmarkRefl hMneg hMid x₀ hx₀ γ hγ0 hγ1 t R
      hxRs hclose hRRs hfix hbound hwin hmin
  · have hlognn : 0 ≤ Real.log (1 / γ) := Real.log_nonneg ((one_le_div hγ0).mpr hγ1)
    have hX : 0 ≤ c₁ * (Real.log (1 / γ) + 3) + c₂ := by
      have h1 : 0 ≤ c₁ * (Real.log (1 / γ) + 3) := mul_nonneg hc₁ (by linarith)
      linarith [h1, hc₂]
    have hcost' := mnrs_raa_cost_bound γ c₁ c₂ hγ0 hc₁ costR costMark t hcost hmark
    have h3t : (0 : ℝ) ≤ (3 : ℝ) ^ t := by positivity
    have hc₁t : 0 ≤ c₁ * (t : ℝ) := mul_nonneg hc₁ (Nat.cast_nonneg t)
    calc raaCost costR costMark t ≤
          ((3 : ℝ) ^ t - 1) * (c₁ * (Real.log (1 / γ) + 3) + c₂) / 2 - c₁ * (t : ℝ) := hcost'
      _ ≤ (3 : ℝ) ^ t * (c₁ * (Real.log (1 / γ) + 3) + c₂) := by
          nlinarith [hX, h3t, hc₁t, mul_nonneg hX h3t]

end Qatlib.Concepts.WalkSearch.MnrsAmplify
