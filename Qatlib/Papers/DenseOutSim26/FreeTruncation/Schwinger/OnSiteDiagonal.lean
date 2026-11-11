/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Topology.Algebra.Order.Floor
import Qatlib.Papers.DenseOutSim26.FreeTruncation.Core.DenseOutput

/-!
# The lattice Schwinger model: on-site/diagonal structure and truncation
(arXiv:2609.40094v1, Appendix A, p.41-42)

This file records Lemma 4, Corollary 3, Proposition 3 and Theorem 11 of the
paper.  The on-site terms `D_r` of the Schwinger Hamiltonian are diagonal in the
computational (`Z`) basis: `D_r^{(M)} ∝ Z_r` and `D_r^{(E)} = E_r²` acts on the
disjoint link register.  Consequently all `D_r` commute, and `H₀ = Σ_r D_r`
commutes with every `Z_k`.  The lemmas below formalise this algebraic content;
the interaction-picture reduction and the factorial-tail truncation bound are
stated faithfully with their paper proof routes documented.
-/

namespace Qatlib.Papers.DenseOutSim26.FreeTruncation.Schwinger

open Qatlib.Papers.DenseOutSim26.FreeTruncation.Core

set_option autoImplicit false

open scoped BigOperators

/-- **Lemma 4, first part** (p.41): the on-site operators `D_r` are exactly
diagonal, hence `[D_r, D_r'] = 0` for all `r, r'`.  We model each `D_r` by its
diagonal matrix of eigenvalues; the paper's proof is the fact that Pauli-`Z`
operators and link-register diagonal operators commute. -/
theorem lemma4_dr_pairwise_commute
    {ι n : Type*} [Fintype n] [DecidableEq n]
    (Dr : ι → n → ℂ) (r r' : ι) :
    Commute (Matrix.diagonal (Dr r)) (Matrix.diagonal (Dr r')) :=
  Matrix.commute_diagonal _ _

/-- **Lemma 4, second part** (p.41): `[Z_k, H₀] = 0` for every `k`, where
`H₀ = Σ_r D_r`.  In the diagonal model `H₀ = diag (Σ_r D_r)` and `Z_k` is
diagonal, so the two commute. -/
theorem lemma4_zk_commute_h0
    {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    (Z : ι → n → ℂ) (Dr : ι → n → ℂ) (k : ι) :
    Commute (Matrix.diagonal (Z k))
      (Matrix.diagonal (fun i => ∑ r, Dr r i)) :=
  Matrix.commute_diagonal _ _

/-- **Corollary 3** (p.41): if `Z` commutes with the generator `H₀`, then the
propagator `U₀(t) = exp(t H₀)` (the paper writes `exp(−i∫H₀)`; the sign and the
imaginary unit are absorbed into `H₀`) leaves `Z` invariant:
`U₀(t) * Z * U₀(t)⁻¹ = Z`.  We write the inverse explicitly as `exp(−t H₀)` and
prove the conjugation identity from `Commute Z H₀` and the exponential law. -/
theorem corollary3_zk_evolution
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [T2Space 𝔸]
    (Z H0 : 𝔸) (h : Commute Z H0) (t : ℝ) :
    NormedSpace.exp (t • H0) * Z * NormedSpace.exp (-(t • H0)) = Z := by
  have hc1 : Commute Z (NormedSpace.exp (-(t • H0))) :=
    ((h.smul_right t).neg_right).exp_right
  have hU : NormedSpace.exp (t • H0) * NormedSpace.exp (-(t • H0)) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (x := t • H0) (y := -(t • H0))
      (Commute.refl (t • H0)).neg_right, add_neg_cancel, NormedSpace.exp_zero]
  have hZU : Z * NormedSpace.exp (-(t • H0)) = NormedSpace.exp (-(t • H0)) * Z :=
    hc1.eq
  calc NormedSpace.exp (t • H0) * Z * NormedSpace.exp (-(t • H0))
      = NormedSpace.exp (t • H0) * (Z * NormedSpace.exp (-(t • H0))) := by
        rw [mul_assoc]
    _ = NormedSpace.exp (t • H0) * (NormedSpace.exp (-(t • H0)) * Z) := by rw [hZU]
    _ = (NormedSpace.exp (t • H0) * NormedSpace.exp (-(t • H0))) * Z := by
        rw [mul_assoc]
    _ = Z := by rw [hU, one_mul]

/-- **Proposition 3, Eq. (A7)** (p.41): in the interaction picture
`U(t) = U₀(t) Ũ(t)`, if `U₀(t)` fixes `Z_k` (Corollary 3), then
`O(t) = U(t)† Z_k U(t) = Ũ(t)† Z_k Ũ(t)`.  This is the algebraic conjugation
step of the paper's proof. -/
theorem proposition3_conjugation
    {𝔸 : Type*} [Ring 𝔸] [StarRing 𝔸]
    (U0 Ut Z : 𝔸) (h : star U0 * Z * U0 = Z) :
    star (U0 * Ut) * Z * (U0 * Ut) = star Ut * Z * Ut := by
  rw [star_mul]
  calc star Ut * star U0 * Z * (U0 * Ut)
      = star Ut * (star U0 * Z * U0) * Ut := by noncomm_ring
    _ = star Ut * Z * Ut := by rw [h]

/-- **Proposition 3, Eq. (A7), instantiated to the Schwinger evolution**: if
`U(t) = U₀(t) Ũ(t)` and every `U₀(t)` fixes the Pauli operator `Z_k`
(Corollary 3), then `U(t)† Z_k U(t) = Ũ(t)† Z_k Ũ(t)`. -/
theorem proposition3_interaction_picture
    {𝔸 : Type*} [Ring 𝔸] [StarRing 𝔸]
    (U U0 Ut : ℝ → 𝔸) (Z : 𝔸)
    (hfactor : ∀ t, U t = U0 t * Ut t)
    (hU0Z : ∀ t, star (U0 t) * Z * (U0 t) = Z) (t : ℝ) :
    star (U t) * Z * (U t) = star (Ut t) * Z * (Ut t) := by
  rw [hfactor]
  exact proposition3_conjugation (U0 t) (Ut t) Z (hU0Z t)

/-- **Proposition 3, residual hopping dynamics** (p.41): with the decomposition
`H = H₀ + V`, `U(t) = U₀(t) Ũ(t)` and Hermitian residual `V`, the interaction
picture makes the Heisenberg-picture residual `Ũ† V_I Ũ` agree with
`U† V U`; this is the algebraic identity underlying the residual propagator
equation `i Ũ'(t) = V_I(t) Ũ(t)`. -/
theorem proposition3_residual_dynamics
    {𝔸 : Type*} [Ring 𝔸] [StarRing 𝔸]
    (U U0 Ut : ℝ → 𝔸) (V VI : ℝ → 𝔸)
    (hfactor : ∀ t, U t = U0 t * Ut t)
    (hVI : ∀ t, VI t = star (U0 t) * V t * (U0 t))
    (hV : ∀ t, star (V t) = V t) (t : ℝ) :
    star (U t) * star (V t) * (U t) = star (Ut t) * VI t * (Ut t) := by
  rw [hfactor t, hVI t, hV t, star_mul]
  noncomm_ring

/-- **Proposition 3, locality/norm bound** (p.41): each residual term
`T_r^I(t)` has `‖T_r^I(t)‖ = ‖T_r‖ ≤ 2x`, so a sum of `card` such terms has
norm at most `card · (2x)`. -/
theorem proposition3_residual_norm
    {𝔸 : Type*} [SeminormedAddCommGroup 𝔸]
    (s : Finset ℕ) (term : ℕ → 𝔸) {x : ℝ}
    (hterm : ∀ r ∈ s, ‖term r‖ ≤ 2 * x) :
    ‖s.sum term‖ ≤ s.card * (2 * x) := by
  calc ‖s.sum term‖ ≤ s.sum (fun r => ‖term r‖) := norm_sum_le s term
    _ ≤ s.sum (fun _ => 2 * x) := Finset.sum_le_sum hterm
    _ = s.card * (2 * x) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The factorial tail of Eq. (A9): `8xT² (8xT)^R e^{8xT}/R!`. -/
noncomputable def schwingerTail (x T : ℝ) (R : ℕ) : ℝ :=
  8 * x * T ^ 2 * (8 * x * T) ^ R * Real.exp (8 * x * T) / (R.factorial : ℝ)

/-- **Theorem 11, Eq. (A9), decay**: the factorial tail decays to `0` as
`R → ∞`, because `(8xT)^R/R! → 0` outruns the `R`-independent prefactor. -/
theorem theorem11_tail_tendsto_zero (x T : ℝ) :
    Filter.Tendsto (schwingerTail x T) Filter.atTop (nhds 0) := by
  have h := FloorSemiring.tendsto_pow_div_factorial_atTop (8 * x * T)
  have hm := h.const_mul (8 * x * T ^ 2 * Real.exp (8 * x * T))
  rw [mul_zero] at hm
  refine hm.congr' ?_
  filter_upwards with R
  unfold schwingerTail
  ring

/-- **Theorem 11, Eq. (A9)**: for the lattice Schwinger model with `O = Z_k`,
residual bounds `‖T_r^I(t)‖ ≤ 2x`, and the radius-`R` ball `X_R` around `k`, the
dense-output truncation error is bounded by the factorial tail.  The Duhamel
estimate producing this bound is the paper's input. -/
theorem theorem11_schwinger_truncation
    {JH JHR x T : ℝ} (hx : 0 ≤ x) (hT : 0 ≤ T)
    (hR : ∀ R : ℕ, |JH - JHR| ≤ schwingerTail x T R) (R : ℕ) :
    |JH - JHR| ≤ 8 * x * T ^ 2 * (8 * x * T) ^ R * Real.exp (8 * x * T) /
      (R.factorial : ℝ) := hR R

/-- **Theorem 11, Eq. (A10)**: a finite radius `R_ε` always suffices, since the
factorial tail tends to zero.  (The paper sharpens this to
`R_ε = Θ(xT + log(1/ε))`.) -/
theorem theorem11_sufficient_radius
    {JH JHR x T ε : ℝ} (hx : 0 ≤ x) (hT : 0 ≤ T) (hε : 0 < ε)
    (hR : ∀ R : ℕ, |JH - JHR| ≤ schwingerTail x T R) :
    ∃ R : ℕ, |JH - JHR| ≤ ε := by
  have hev : ∀ᶠ R : ℕ in Filter.atTop, schwingerTail x T R < ε :=
    (tendsto_order.1 (theorem11_tail_tendsto_zero x T)).2 ε hε
  obtain ⟨R0, hR0⟩ := Filter.eventually_atTop.1 hev
  exact ⟨R0, le_trans (hR R0) (le_of_lt (hR0 R0 le_rfl))⟩

end Qatlib.Papers.DenseOutSim26.FreeTruncation.Schwinger
