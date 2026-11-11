/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAssistedPGM16.MainResults.SourceModel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add

set_option backward.isDefEq.respectTransparency false

/-!
# QAssistedPGM16 — the gray-box learning rule of Eqs. (10)-(13)

Fixed source: arXiv:1609.02542, p.5-6.  Eq. (9) defines the quantum relative
entropy `S(ρ_D‖ρ)`; Eqs. (10)-(11) are gradient updates of the couplings and
local fields; Eqs. (12)-(13) are the evaluated gradients

`(1/β) ∂S/∂J_ij = ⟨Z_i Z_j⟩_{ρ_D} − ⟨Z_i Z_j⟩_ρ`,
`(1/β) ∂S/∂h_i  = ⟨Z_i⟩_{ρ_D} − ⟨Z_i⟩_ρ`.

Sign convention.  With the paper's energy `E = −Σ J z z − Σ h z` (Eq. (5),
p.3) and `S = D(p_D‖P_θ)` (Eq. (9), p.5), differentiating the relative
entropy gives the *negative* of the printed right-hand side; the printed
`⟨·⟩_D − ⟨·⟩_ρ` is the gradient of the average log-likelihood `L = −S`
(equivalently, the relative entropy is being minimized).  We therefore state
the exact printed identities for `L = −S`; the relative-entropy gradient
itself is recorded separately (`relativeEntropy_gradient`).  This is a
sign-convention bookkeeping issue in the source, not a weakened statement:
both signs are proved.

The results are the classical-diagonal finite-sum specialization of the
quantum Gibbs identities; the paper itself uses the classical Boltzmann form
when `A(τ*) ≪ B(τ*)` (p.6).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QAssistedPGM16.MainResults

/-- Changing one parameter by `t` changes the energy by `−t` times the
associated monomial (Eq. (5), p.3). -/
theorem energy_update {M : ℕ} (θ : ParamIndex M → ℝ) (a : ParamIndex M) (t : ℝ)
    (z : Config M) :
    energy (Function.update θ a t) z = energy θ z - (t - θ a) * feature a z := by
  unfold energy
  have htot : θ a * feature a z +
      ∑ b ∈ (Finset.univ.erase a : Finset (ParamIndex M)), θ b * feature b z
      = ∑ b : ParamIndex M, θ b * feature b z :=
    Finset.add_sum_erase Finset.univ (fun b => θ b * feature b z) (Finset.mem_univ a)
  have hsum : ∑ b : ParamIndex M, Function.update θ a t b * feature b z
      = ∑ b : ParamIndex M, θ b * feature b z + (t - θ a) * feature a z := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun b => Function.update θ a t b * feature b z) (Finset.mem_univ a)]
    rw [Function.update_self]
    have herase : ∑ b ∈ (Finset.univ.erase a : Finset (ParamIndex M)),
        Function.update θ a t b * feature b z
        = ∑ b ∈ (Finset.univ.erase a : Finset (ParamIndex M)), θ b * feature b z := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]
    rw [herase, ← htot]
    ring
  rw [hsum]
  ring

/-- Along the unit-speed path in coordinate `a`, the energy decreases at rate
`−A_a` (the derivative of Eq. (5) with respect to a coupling or field). -/
theorem hasDerivAt_energy_path {M : ℕ} (θ : ParamIndex M → ℝ) (a : ParamIndex M)
    (z : Config M) :
    HasDerivAt (fun t : ℝ => energy (path θ a t) z) (-(feature a z)) 0 := by
  have hfun : (fun t : ℝ => energy (path θ a t) z)
      = fun t : ℝ => energy θ z - t * feature a z := by
    funext t
    unfold path
    rw [energy_update]
    ring
  rw [hfun]
  have h : HasDerivAt (fun t : ℝ => energy θ z - t * feature a z)
      (0 - 1 * feature a z) 0 :=
    (hasDerivAt_const (x := (0 : ℝ)) (c := energy θ z)).sub
      ((hasDerivAt_id (0 : ℝ)).mul_const (feature a z))
  simpa using h

/-- Along the unit-speed path, each Boltzmann weight changes at rate
`β A_a exp(−βE)`. -/
theorem hasDerivAt_boltzmannWeight_path {M : ℕ} (β : ℝ) (θ : ParamIndex M → ℝ)
    (a : ParamIndex M) (z : Config M) :
    HasDerivAt (fun t : ℝ => boltzmannWeight β (path θ a t) z)
      (β * feature a z * boltzmannWeight β θ z) 0 := by
  unfold boltzmannWeight
  have hinner : HasDerivAt (fun t : ℝ => -(β * energy (path θ a t) z))
      (-(β * -(feature a z))) 0 :=
    ((hasDerivAt_energy_path θ a z).const_mul β).neg
  have h0 : -(β * energy (path θ a 0) z) = -(β * energy θ z) := by
    rw [path_zero]
  have hexp := hinner.exp
  convert hexp using 1
  rw [h0]
  ring

/-- Derivative of the partition function along a parameter path:
`∂Z/∂θ_a = β Z ⟨A_a⟩_ρ`. -/
theorem hasDerivAt_partition_path {M : ℕ} (β : ℝ) (θ : ParamIndex M → ℝ)
    (a : ParamIndex M) :
    HasDerivAt (fun t : ℝ => partition β (path θ a t))
      (β * partition β θ * expectation β θ (feature a)) 0 := by
  have hterm : ∀ z : Config M, HasDerivAt
      (fun t : ℝ => boltzmannWeight β (path θ a t) z)
      (β * feature a z * boltzmannWeight β θ z) 0 :=
    fun z => hasDerivAt_boltzmannWeight_path β θ a z
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun z _ => hterm z)
  have hval : (∑ z : Config M, β * feature a z * boltzmannWeight β θ z)
      = β * partition β θ * expectation β θ (feature a) := by
    have hps : expectation β θ (feature a) * partition β θ
        = ∑ z : Config M, feature a z * boltzmannWeight β θ z :=
      expectation_mul_partition β θ (feature a)
    calc
      ∑ z : Config M, β * feature a z * boltzmannWeight β θ z
          = β * ∑ z : Config M, feature a z * boltzmannWeight β θ z := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z _
            ring
      _ = β * (expectation β θ (feature a) * partition β θ) := by rw [hps]
      _ = β * partition β θ * expectation β θ (feature a) := by ring
  exact HasDerivAt.congr_deriv hsum hval

/-- Derivative of `log Z` along a parameter path: `∂ log Z/∂θ_a = β⟨A_a⟩_ρ`. -/
theorem hasDerivAt_log_partition_path {M : ℕ} (β : ℝ) (θ : ParamIndex M → ℝ)
    (a : ParamIndex M) :
    HasDerivAt (fun t : ℝ => Real.log (partition β (path θ a t)))
      (β * expectation β θ (feature a)) 0 := by
  have hZ := hasDerivAt_partition_path β θ a
  have hg0 : partition β (path θ a 0) ≠ 0 :=
    ne_of_gt (partition_pos β (path θ a 0))
  have hlog := hZ.log hg0
  have hgval : partition β (path θ a 0) = partition β θ := by rw [path_zero]
  have hZne : partition β θ ≠ 0 := ne_of_gt (partition_pos β θ)
  convert hlog using 1
  rw [hgval]
  field_simp [hZne]

/-- Derivative of the data-weighted energy `Σ_z p z E_θ(z)` along a parameter
path: `−Σ_z p z A_a(z)`. -/
theorem hasDerivAt_weightedEnergy_path {M : ℕ} (p : Config M → ℝ)
    (θ : ParamIndex M → ℝ) (a : ParamIndex M) :
    HasDerivAt (fun t : ℝ => ∑ z : Config M, p z * energy (path θ a t) z)
      (-(∑ z : Config M, p z * feature a z)) 0 := by
  have hterm : ∀ z : Config M, HasDerivAt
      (fun t : ℝ => p z * energy (path θ a t) z) (p z * -(feature a z)) 0 :=
    fun z => (hasDerivAt_energy_path θ a z).const_mul (p z)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun z _ => hterm z)
  have hval : (∑ z : Config M, p z * -(feature a z))
      = -(∑ z : Config M, p z * feature a z) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro z _
    ring
  exact HasDerivAt.congr_deriv hsum hval

/-- Derivative of the free-energy form of the relative entropy, Eq. (9) with
`p = ρ_D` and `q` the Gibbs state. -/
theorem hasDerivAt_freeEnergy_path {M : ℕ} (p : Config M → ℝ) (β : ℝ)
    (θ : ParamIndex M → ℝ) (a : ParamIndex M) :
    HasDerivAt (fun t : ℝ => freeEnergy p β (path θ a t))
      (β * expectation β θ (feature a) - β * ∑ z : Config M, p z * feature a z) 0 := by
  unfold freeEnergy
  have h1 := hasDerivAt_weightedEnergy_path p θ a
  have h2 := hasDerivAt_log_partition_path β θ a
  have hconst : HasDerivAt (fun _ : ℝ => ∑ z : Config M, p z * Real.log (p z)) 0 0 :=
    hasDerivAt_const (x := (0 : ℝ)) (c := ∑ z : Config M, p z * Real.log (p z))
  have h := (hconst.add (h1.const_mul β)).add h2
  refine HasDerivAt.congr_deriv h ?_
  ring

/-- Gradient of the relative entropy `S(ρ_D‖ρ)` with respect to a coupling or
field: `β(⟨A_a⟩_ρ − ⟨A_a⟩_{ρ_D})`. -/
theorem relativeEntropy_gradient {M : ℕ} (p : Config M → ℝ)
    (hp : ∑ z : Config M, p z = 1) (β : ℝ) (θ : ParamIndex M → ℝ) (a : ParamIndex M) :
    HasDerivAt (fun t : ℝ => relativeEntropy p (gibbsDist β (path θ a t)))
      (β * (expectation β θ (feature a) - ∑ z : Config M, p z * feature a z)) 0 := by
  have hfun : (fun t : ℝ => relativeEntropy p (gibbsDist β (path θ a t)))
      = fun t : ℝ => freeEnergy p β (path θ a t) := by
    funext t
    exact relativeEntropy_gibbs_eq p hp β (path θ a t)
  rw [hfun]
  have h := hasDerivAt_freeEnergy_path p β θ a
  refine HasDerivAt.congr_deriv h ?_
  ring

/-- Gradient of the average log-likelihood `L = −S(ρ_D‖ρ)`; this is the sign
convention of the printed Eqs. (12)-(13), p.6. -/
theorem logLikelihood_gradient {M : ℕ} (p : Config M → ℝ)
    (hp : ∑ z : Config M, p z = 1) (β : ℝ) (θ : ParamIndex M → ℝ) (a : ParamIndex M) :
    HasDerivAt (fun t : ℝ => -relativeEntropy p (gibbsDist β (path θ a t)))
      (β * (∑ z : Config M, p z * feature a z - expectation β θ (feature a))) 0 := by
  have h := (relativeEntropy_gradient p hp β θ a).neg
  refine HasDerivAt.congr_deriv h ?_
  ring

/-- Eq. (12), p.6, for a coupling `J_ij`: the log-likelihood derivative is
`β(⟨Z_i Z_j⟩_{ρ_D} − ⟨Z_i Z_j⟩_ρ)`. -/
theorem Eq12_coupling_gradient {M : ℕ} (p : Config M → ℝ)
    (hp : ∑ z : Config M, p z = 1) (β : ℝ) (θ : ParamIndex M → ℝ) (i j : Fin M) :
    HasDerivAt
      (fun t : ℝ => -relativeEntropy p (gibbsDist β (path θ (Sum.inl (i, j)) t)))
      (β * ((∑ z : Config M, p z * (spin z i * spin z j)) -
        expectation β θ (feature (Sum.inl (i, j))))) 0 := by
  have h := logLikelihood_gradient p hp β θ (Sum.inl (i, j))
  simpa [feature] using h

/-- Eq. (13), p.6, for a local field `h_i`: the log-likelihood derivative is
`β(⟨Z_i⟩_{ρ_D} − ⟨Z_i⟩_ρ)`. -/
theorem Eq13_field_gradient {M : ℕ} (p : Config M → ℝ)
    (hp : ∑ z : Config M, p z = 1) (β : ℝ) (θ : ParamIndex M → ℝ) (i : Fin M) :
    HasDerivAt
      (fun t : ℝ => -relativeEntropy p (gibbsDist β (path θ (Sum.inr i) t)))
      (β * ((∑ z : Config M, p z * spin z i) -
        expectation β θ (feature (Sum.inr i)))) 0 := by
  have h := logLikelihood_gradient p hp β θ (Sum.inr i)
  simpa [feature] using h

/-- Eq. (12) in the printed `1/β` normalization (p.6): the gradient of
`L/β = −S/β` equals the positive-minus-negative phase difference. -/
theorem Eq12_coupling_gradient_scaled {M : ℕ} (p : Config M → ℝ)
    (hp : ∑ z : Config M, p z = 1) (β : ℝ) (hβ : β ≠ 0)
    (θ : ParamIndex M → ℝ) (i j : Fin M) :
    HasDerivAt
      (fun t : ℝ => (1 / β) *
        -relativeEntropy p (gibbsDist β (path θ (Sum.inl (i, j)) t)))
      ((∑ z : Config M, p z * (spin z i * spin z j)) -
        expectation β θ (feature (Sum.inl (i, j)))) 0 := by
  have h := (Eq12_coupling_gradient p hp β θ i j).const_mul (1 / β)
  refine HasDerivAt.congr_deriv h ?_
  field_simp [hβ]

/-- Eq. (13) in the printed `1/β` normalization (p.6). -/
theorem Eq13_field_gradient_scaled {M : ℕ} (p : Config M → ℝ)
    (hp : ∑ z : Config M, p z = 1) (β : ℝ) (hβ : β ≠ 0)
    (θ : ParamIndex M → ℝ) (i : Fin M) :
    HasDerivAt
      (fun t : ℝ => (1 / β) *
        -relativeEntropy p (gibbsDist β (path θ (Sum.inr i) t)))
      ((∑ z : Config M, p z * spin z i) -
        expectation β θ (feature (Sum.inr i))) 0 := by
  have h := (Eq13_field_gradient p hp β θ i).const_mul (1 / β)
  refine HasDerivAt.congr_deriv h ?_
  field_simp [hβ]

end Qatlib.Papers.QAssistedPGM16.MainResults
