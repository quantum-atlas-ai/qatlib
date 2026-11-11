/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorPCA19.MainResults.Model.TensorPCAConfig
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor PCA — spectral and probabilistic model layer

The source states its results for the largest eigenvalue `λ₁` of the Gaussian
Hamiltonian `H(G)` and for a state-dependent quantity `⟨Ψ|H(T₀)|Ψ⟩`.  Those
random objects are not rebuilt from the Gaussian measure in this paper layer
(no iid-normal tensor measure is constructed).  Instead this module fixes the
two modelling interfaces used by every source statement:

* `GaussianSpectralModel s Ω` — the law of `λ₁ = λ_max(H(G))` for the Gaussian
  ensemble of §1.1.  It carries the trace-MGF `Z(τ) = E[tr exp(τ H(G))]` together
  with the two facts the paper uses: `Z(0) = D(N, n_bos)` (§3.1 p.6) and the
  Chernoff bound `Pr[λ₁ ≥ x] ≤ Z(τ) e^{-τx}` obtained from
  `tr exp(τH(G)) ≥ exp(τ λ₁)` (proof of Lemma 5, p.14).
* `SpectralDecomposition n` — the finite real spectral decomposition of a
  Hermitian operator **on a unit state**: eigenvalues `eig`, squared overlaps
  `weight` (nonnegative, summing to one), the largest eigenvalue `lamMax`, and
  the projector mass `projMass t = Σ_{eigᵢ ≥ t} weightᵢ`.  This is the form of
  the spectral theorem used in §5.2 (Lemma 8 and Eqs. (17), (24)).

The generic exponential-tail lemma `exp_tail_bound` below is proved in full: it
is the algebra shared by Lemma 5 (even `p`) and Lemma 7 (odd `p`), namely the
optimisation of `D exp(τ²A − τx)` at `τ = ξ⁻¹`.
-/

namespace Qatlib.Papers.TensorPCA19.MainResults

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
noncomputable section

/-! ## 1. The Gaussian spectral model -/

/-- The law of the largest eigenvalue `λ₁` of the Gaussian Hamiltonian `H(G)`,
together with the trace-MGF `Z(τ) = E[tr exp(τ H(G))]`.  The fields `Z_zero` and
`tail_le_Z` are the two standard structural facts used by the source's §4
computation (Lemmas 4–7). -/
structure GaussianSpectralModel (s : SpikedTensor) (Ω : Type*) [MeasurableSpace Ω] where
  /-- Law of the noise Hamiltonian's largest eigenvalue. -/
  μ : Measure Ω
  /-- Probability measure. -/
  instProb : IsProbabilityMeasure μ
  /-- The largest eigenvalue `λ₁(H(G))` as a random variable. -/
  eig : Ω → ℝ
  /-- Measurability of `λ₁`. -/
  measurable_eig : Measurable eig
  /-- The trace MGF `Z(τ) = E[tr exp(τ H(G))]`. -/
  Z : ℝ → ℝ
  /-- `Z(0) = D(N, n_bos)`, the dimension of the symmetric subspace (§3.1, p.6). -/
  Z_zero : Z 0 = symmetricDim s
  /-- Chernoff bound from `tr exp(τ H(G)) ≥ exp(τ λ₁)` (proof of Lemma 5, p.14):
  `Pr[λ₁ ≥ x] ≤ Z(τ) e^{−τx}`. -/
  tail_le_Z : ∀ (τ x : ℝ), 0 ≤ τ → (μ {ω | x ≤ eig ω}).toReal ≤ Z τ * Real.exp (-(τ * x))

attribute [instance] GaussianSpectralModel.instProb

/-- The source's tail probability `Pr[λ₁ ≥ x]`. -/
def GaussianSpectralModel.tail {s : SpikedTensor} {Ω : Type*} [MeasurableSpace Ω]
    (M : GaussianSpectralModel s Ω) (x : ℝ) : ℝ :=
  (M.μ {ω | x ≤ M.eig ω}).toReal

/-- `D(N, n_bos) ≤ N^n_bos`: the factorial in `D` is at least one. -/
theorem symmetricDim_le_pow (s : SpikedTensor) :
    symmetricDim s ≤ (s.N : ℝ) ^ s.nbos := by
  unfold symmetricDim
  refine div_le_self ?_ ?_
  · positivity
  · exact_mod_cast Nat.factorial_pos s.nbos

/-- `D(N, n_bos) > 0`. -/
theorem symmetricDim_pos (s : SpikedTensor) : 0 < symmetricDim s := by
  unfold symmetricDim
  have h1 : (0 : ℝ) < (s.N : ℝ) ^ s.nbos :=
    pow_pos (by exact_mod_cast s.hN) _
  have h2 : (0 : ℝ) < (Nat.factorial s.nbos : ℝ) := by exact_mod_cast Nat.factorial_pos s.nbos
  exact div_pos h1 h2

/-- `log D(N, n_bos) ≤ n_bos log N`, the dimension estimate used in the proof of
Lemma 5 (p.14: `D(N, n_bos) ≤ N^n_bos`). -/
theorem log_symmetricDim_le (s : SpikedTensor) :
    Real.log (symmetricDim s) ≤ (s.nbos : ℝ) * Real.log (s.N : ℝ) := by
  have hpow : 0 < (s.N : ℝ) ^ s.nbos := pow_pos (by exact_mod_cast s.hN) _
  have hfac : (0 : ℝ) < (Nat.factorial s.nbos : ℝ) := by exact_mod_cast Nat.factorial_pos s.nbos
  have hfac1 : (1 : ℝ) ≤ (Nat.factorial s.nbos : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos s.nbos)
  have hlogfac : 0 ≤ Real.log (Nat.factorial s.nbos : ℝ) := Real.log_nonneg hfac1
  unfold symmetricDim
  rw [Real.log_div hpow.ne' hfac.ne']
  rw [Real.log_pow]
  linarith

/-! ## 2. The shared exponential-tail optimisation -/

/-- **The tail optimisation of Lemmas 5 and 7.**  If
`tail x ≤ Z(τ) e^{−τx}` for all `τ ≥ 0`, `Z(τ) ≤ D e^{τ²A}`, `log D ≤ n L`,
`Emax = 2nLξ`, `A ξ⁻² = nL` and `ξ > 0`, then
`tail x ≤ exp(−(x − Emax)/ξ)` for every `x`.

This is the algebra of the proof of Lemma 5 (p.14) and Lemma 7 (p.17): choose
`τ = ξ⁻¹`, so that `D e^{τ²A} e^{−τx} = exp(log D + nL − x/ξ) ≤ exp(2nL − x/ξ)`,
and `2nL − x/ξ = −(x − Emax)/ξ`. -/
theorem exp_tail_bound {Z tail : ℝ → ℝ} {D Emax ξ A n L : ℝ}
    (hD : 0 < D) (hlogD : Real.log D ≤ n * L)
    (hZ : ∀ τ : ℝ, 0 ≤ τ → Z τ ≤ D * Real.exp (τ ^ 2 * A))
    (hξ : 0 < ξ) (hA : A * (ξ⁻¹) ^ 2 = n * L)
    (hEmax : Emax = 2 * n * L * ξ)
    (hChernoff : ∀ (τ x : ℝ), 0 ≤ τ → tail x ≤ Z τ * Real.exp (-(τ * x)))
    (x : ℝ) : tail x ≤ Real.exp (-(x - Emax) / ξ) := by
  have hτ : 0 ≤ ξ⁻¹ := by positivity
  have hstep1 : tail x ≤ Z ξ⁻¹ * Real.exp (-(ξ⁻¹ * x)) := hChernoff ξ⁻¹ x hτ
  have hstep2 : Z ξ⁻¹ * Real.exp (-(ξ⁻¹ * x))
      ≤ (D * Real.exp ((ξ⁻¹) ^ 2 * A)) * Real.exp (-(ξ⁻¹ * x)) := by
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    simpa [mul_comm] using hZ ξ⁻¹ hτ
  have hpos : 0 < Real.exp (-(ξ⁻¹ * x)) := Real.exp_pos _
  have hDexp : Real.exp (Real.log D) = D := Real.exp_log hD
  have hrate : (ξ⁻¹) ^ 2 * A = n * L := by
    rw [mul_comm, hA]
  have hxdiv : ξ⁻¹ * x = x / ξ := by
    rw [div_eq_mul_inv, mul_comm]
  have hprod : (D * Real.exp ((ξ⁻¹) ^ 2 * A)) * Real.exp (-(ξ⁻¹ * x))
      = Real.exp (Real.log D + n * L - x / ξ) := by
    rw [hrate, hxdiv]
    conv_lhs =>
      rw [← Real.exp_log hD]
      rw [← Real.exp_add]
      rw [← Real.exp_add]
    congr 1
  have harg : Real.log D + n * L - x / ξ ≤ 2 * (n * L) - x / ξ := by linarith
  have hexpmono : Real.exp (Real.log D + n * L - x / ξ)
      ≤ Real.exp (2 * (n * L) - x / ξ) := Real.exp_le_exp.2 harg
  have hfinal : Real.exp (2 * (n * L) - x / ξ) = Real.exp (-(x - Emax) / ξ) := by
    rw [hEmax]
    congr 1
    field_simp
    ring
  calc tail x ≤ Z ξ⁻¹ * Real.exp (-(ξ⁻¹ * x)) := hstep1
    _ ≤ (D * Real.exp ((ξ⁻¹) ^ 2 * A)) * Real.exp (-(ξ⁻¹ * x)) := hstep2
    _ = Real.exp (Real.log D + n * L - x / ξ) := hprod
    _ ≤ Real.exp (2 * (n * L) - x / ξ) := hexpmono
    _ = Real.exp (-(x - Emax) / ξ) := hfinal

/-! ## 3. Finite spectral decomposition on a unit state -/

/-- The finite real spectral decomposition of a Hermitian operator on a single
unit state, in the form used in §5.2: eigenvalues `eig`, squared overlaps
`weight` (a probability distribution), largest eigenvalue `lamMax`.  `projMass t`
is the squared norm of the projection of the state onto the eigenspace with
eigenvalue `≥ t`, i.e. the quantity bounded in Lemma 8 (p.24). -/
structure SpectralDecomposition (n : ℕ) where
  /-- Eigenvalues of the Hermitian operator. -/
  eig : Fin n → ℝ
  /-- Squared overlaps of the state with the eigenvectors. -/
  weight : Fin n → ℝ
  /-- Squared overlaps are nonnegative. -/
  weight_nonneg : ∀ i, 0 ≤ weight i
  /-- The unit state has total squared overlap one. -/
  weight_sum : (∑ i, weight i) = 1
  /-- The largest eigenvalue. -/
  lamMax : ℝ
  /-- `lamMax` is an upper bound for every eigenvalue. -/
  eig_le_lamMax : ∀ i, eig i ≤ lamMax

/-- The energy `⟨Ψ|H|Ψ⟩ = Σᵢ wᵢ eᵢ`. -/
def SpectralDecomposition.energy {n : ℕ} (D : SpectralDecomposition n) : ℝ :=
  ∑ i, D.weight i * D.eig i

/-- The projector mass `projMass t = Σ_{eᵢ ≥ t} wᵢ`. -/
def SpectralDecomposition.projMass {n : ℕ} (D : SpectralDecomposition n) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => t ≤ D.eig i), D.weight i

/-- The projector mass is at most one. -/
theorem SpectralDecomposition.projMass_le_one {n : ℕ} (D : SpectralDecomposition n) (t : ℝ) :
    D.projMass t ≤ 1 := by
  calc D.projMass t ≤ ∑ i, D.weight i := by
        unfold SpectralDecomposition.projMass
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => D.weight_nonneg i)
    _ = 1 := D.weight_sum

/-- **Spectral energy split.**  For any threshold `t`,
`⟨Ψ|H|Ψ⟩ ≤ t (1 − projMass t) + λmax · projMass t`.

This is the spectral theorem step used in the proof of Lemma 8 (p.25): the
weight below `t` contributes at most `t`, the weight at or above `t` contributes
at most the largest eigenvalue. -/
theorem SpectralDecomposition.energy_le_projMass {n : ℕ} (D : SpectralDecomposition n) (t : ℝ) :
    D.energy ≤ t * (1 - D.projMass t) + D.lamMax * D.projMass t := by
  classical
  set S := Finset.univ.filter (fun i => t ≤ D.eig i) with hS
  have hsplit : (∑ i, D.weight i * D.eig i)
      = (∑ i ∈ S, D.weight i * D.eig i) + (∑ i ∈ Sᶜ, D.weight i * D.eig i) := by
    exact (Finset.sum_add_sum_compl S (fun i => D.weight i * D.eig i)).symm
  have hSle : (∑ i ∈ S, D.weight i * D.eig i) ≤ (∑ i ∈ S, D.weight i) * D.lamMax := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_left (D.eig_le_lamMax i) (D.weight_nonneg i)
  have hScle : (∑ i ∈ Sᶜ, D.weight i * D.eig i) ≤ t * (∑ i ∈ Sᶜ, D.weight i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hit : ¬ t ≤ D.eig i := by
      simpa [hS] using hi
    have hle : D.eig i ≤ t := le_of_not_ge hit
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hle (D.weight_nonneg i)
  have hcompl : (∑ i ∈ Sᶜ, D.weight i) = 1 - ∑ i ∈ S, D.weight i := by
    have h := Finset.sum_compl_add_sum (s := S) (f := D.weight)
    rw [D.weight_sum] at h
    linarith
  unfold SpectralDecomposition.energy SpectralDecomposition.projMass
  rw [hS] at *
  rw [hsplit]
  rw [hcompl] at hScle
  nlinarith [hSle, hScle]


/-- The projector mass is antitone in the threshold. -/
theorem SpectralDecomposition.projMass_antitone {n : ℕ} (D : SpectralDecomposition n)
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) : D.projMass t₂ ≤ D.projMass t₁ := by
  unfold SpectralDecomposition.projMass
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => D.weight_nonneg i)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact le_trans h hi

/-- **Markov step of Lemma 8** (p.24).  For a threshold `t` below the largest
eigenvalue, `⟨Ψ|H|Ψ⟩ ≤ t + p(t)(λmax − t)`, hence the projector mass satisfies
`(⟨Ψ|H|Ψ⟩ − t)/(λmax − t) ≤ p(t)`.  This is the spectral form of Markov's
inequality applied to `λmax − H` used in the proof of Lemma 8. -/
theorem SpectralDecomposition.markov_projMass {n : ℕ} (D : SpectralDecomposition n)
    {t : ℝ} (ht : t < D.lamMax) :
    (D.energy - t) / (D.lamMax - t) ≤ D.projMass t := by
  classical
  set S := Finset.univ.filter (fun i => t ≤ D.eig i) with hS
  have hp : D.projMass t = ∑ i ∈ S, D.weight i := by
    unfold SpectralDecomposition.projMass
    rw [← hS]
  have hden : 0 < D.lamMax - t := sub_pos.mpr ht
  have hsumf : (∑ i, D.weight i * (D.eig i - t)) = D.energy - t := by
    calc ∑ i, D.weight i * (D.eig i - t)
        = ∑ i, (D.weight i * D.eig i - D.weight i * t) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i, D.weight i * D.eig i) - (∑ i, D.weight i) * t := by
          rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = D.energy - t := by
          unfold SpectralDecomposition.energy
          rw [D.weight_sum, one_mul]
  have hsplit := (Finset.sum_add_sum_compl S (fun i => D.weight i * (D.eig i - t))).symm
  have hSc : (∑ i ∈ Sᶜ, D.weight i * (D.eig i - t)) ≤ 0 := by
    refine Finset.sum_nonpos fun i hi => ?_
    have hit : ¬ t ≤ D.eig i := by simpa [hS] using hi
    exact mul_nonpos_of_nonneg_of_nonpos (D.weight_nonneg i) (sub_nonpos.mpr (le_of_not_ge hit))
  have hSle : (∑ i ∈ S, D.weight i * (D.eig i - t))
      ≤ (∑ i ∈ S, D.weight i) * (D.lamMax - t) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (D.weight_nonneg i)
    linarith [D.eig_le_lamMax i]
  rw [div_le_iff₀ hden, hp]
  linarith [hsumf, hsplit, hSc, hSle]

end

end Qatlib.Papers.TensorPCA19.MainResults
