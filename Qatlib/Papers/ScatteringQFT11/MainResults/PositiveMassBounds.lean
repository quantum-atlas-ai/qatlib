/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ScatteringQFT11.MainResults.ExpectationCore

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 3: energy bounds in the positive-mass regime

Jordan–Lee–Preskill, *Quantum Computation of Scattering in Scalar Quantum Field
Theories* (arXiv:1112.4833v1), Proposition 3 (p. 22, inequalities (74)–(75)):
let `H` be the lattice `φ⁴` Hamiltonian (4)

`H = ∑_y a^d [ π(y)²/2 + (∇ₐφ)²(y)/2 + m₀²φ(y)²/2 + λ₀φ(y)⁴/4! ]`,

with `m₀² > 0` and `λ₀ ≥ 0`, and let `|ψ⟩` be any state with `⟨ψ|H|ψ⟩ ≤ E`. Then for
every lattice site `x`,

`⟨ψ|φ(x)²|ψ⟩ ≤ 2E/(a^d m₀²)`,  `⟨ψ|π(x)²|ψ⟩ ≤ 2E/a^d`.

The paper's proof (p. 23) drops from `H` every term other than the one at `x`
that is wanted, using that each dropped term is a positive semidefinite operator;
the two bounds then follow by dividing by the (positive) coefficient `a^d m₀²/2`
resp. `a^d/2`.

Finite model: `sites` is the finite lattice, `φ(y)` and `π(y)` are Hermitian
matrices on a common register, and `gradSq y` is the observed discretized
gradient energy `(∇ₐφ)²(y)`, taken as a positive semidefinite matrix — which is
exactly the only property of the gradient term that the argument uses. The
concrete discretized square `(∇ₐφ)²(y) = ∑_j ((φ(y+ar̂ⱼ) − φ(y))/a)²` is a sum of
squares of Hermitian matrices, hence positive semidefinite; see
`QuantumAlgorithmDev.Papers.ScatteringQFT11.MainResults.diff_sq_posSemidef`.
-/

namespace Qatlib.Papers.ScatteringQFT11.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath

open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {sites : Type*} [Fintype sites] [DecidableEq sites]

/-- The **local `φ⁴` Hamiltonian density** at one lattice site, matching the
bracket of equation (4): `π(y)²/2 + (∇ₐφ)²(y)/2 + m₀²φ(y)²/2 + λ₀φ(y)⁴/4!`. -/
noncomputable def phi4LocalTerm (m0sq lam : ℝ) (gradSq phi piOp : sites → Matrix n n ℂ)
    (y : sites) : Matrix n n ℂ :=
  ((1 / 2 : ℝ) : ℂ) • (piOp y * piOp y) + ((1 / 2 : ℝ) : ℂ) • gradSq y
    + ((m0sq / 2 : ℝ) : ℂ) • (phi y * phi y) + ((lam / 24 : ℝ) : ℂ) • (phi y ^ 4)

/-- The **lattice `φ⁴` Hamiltonian** of equation (4): the sum of the local
densities weighted by the cell volume `a^d`. -/
noncomputable def phi4Hamiltonian (d : ℕ) (a m0sq lam : ℝ)
    (gradSq phi piOp : sites → Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ y : sites, ((a ^ d : ℝ) : ℂ) • phi4LocalTerm m0sq lam gradSq phi piOp y

/-- Expansion of the energy functional of the lattice Hamiltonian (4) into the
four contributions of every site. -/
theorem expectation_phi4Hamiltonian (d : ℕ) (a m0sq lam : ℝ)
    (gradSq phi piOp : sites → Matrix n n ℂ) (ψ : QState n) :
    expectation (phi4Hamiltonian d a m0sq lam gradSq phi piOp) ψ
      = ∑ y : sites, a ^ d *
          ((1 / 2) * expectation (piOp y * piOp y) ψ
            + (1 / 2) * expectation (gradSq y) ψ
            + (m0sq / 2) * expectation (phi y * phi y) ψ
            + (lam / 24) * expectation (phi y ^ 4) ψ) := by
  classical
  rw [phi4Hamiltonian, expectation_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [expectation_smul_real, phi4LocalTerm]
  simp only [expectation_add, expectation_smul_real]

/-- The energy functional of the local density is nonnegative in the
positive-mass regime `m₀² > 0`, `λ₀ ≥ 0`: every contribution is a nonnegative
multiple of an expectation of a positive semidefinite operator. -/
theorem expectation_phi4LocalTerm_nonneg (m0sq lam : ℝ) (hm : 0 < m0sq) (hl : 0 ≤ lam)
    (gradSq phi piOp : sites → Matrix n n ℂ)
    (hgrad : ∀ y, (gradSq y).PosSemidef) (hphi : ∀ y, (phi y)ᴴ = phi y)
    (hpi : ∀ y, (piOp y)ᴴ = piOp y) (ψ : QState n) (y : sites) :
    0 ≤ expectation (phi4LocalTerm m0sq lam gradSq phi piOp y) ψ := by
  rw [phi4LocalTerm]
  simp only [expectation_add, expectation_smul_real]
  have h1 : (0:ℝ) ≤ expectation (piOp y * piOp y) ψ := expectation_sq_nonneg (hpi y) ψ
  have h2 : (0:ℝ) ≤ expectation (gradSq y) ψ := expectation_nonneg (hgrad y) ψ
  have h3 : (0:ℝ) ≤ expectation (phi y * phi y) ψ := expectation_sq_nonneg (hphi y) ψ
  have h4 : (0:ℝ) ≤ expectation (phi y ^ 4) ψ := expectation_pow_four_nonneg (hphi y) ψ
  have hm2 : (0:ℝ) ≤ m0sq / 2 := by linarith
  have hl2 : (0:ℝ) ≤ lam / 24 := by linarith
  nlinarith [mul_nonneg hm2 h3, mul_nonneg hl2 h4, mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) h1,
    mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) h2]

/-- **Proposition 3**, inequality (74) (p. 22): in the positive-mass regime every
unit-energy-bounded state has bounded field fluctuations at each site,
`⟨ψ|φ(x)²|ψ⟩ ≤ 2E/(a^d m₀²)`. -/
theorem phi4_positive_mass_field_bound (d : ℕ) (a m0sq lam : ℝ)
    (ha : 0 < a) (hm : 0 < m0sq) (hl : 0 ≤ lam)
    (gradSq phi piOp : sites → Matrix n n ℂ)
    (hgrad : ∀ y, (gradSq y).PosSemidef) (hphi : ∀ y, (phi y)ᴴ = phi y)
    (hpi : ∀ y, (piOp y)ᴴ = piOp y) (ψ : QState n) {E : ℝ}
    (hE : expectation (phi4Hamiltonian d a m0sq lam gradSq phi piOp) ψ ≤ E) (x : sites) :
    expectation (phi x * phi x) ψ ≤ 2 * E / (a ^ d * m0sq) := by
  have haD : (0:ℝ) < a ^ d := pow_pos ha d
  have hm2 : (0:ℝ) < m0sq / 2 := by linarith
  -- Each site contributes a nonnegative amount to the total energy.
  have hterm : ∀ y ∈ Finset.univ, (0:ℝ) ≤ a ^ d *
      ((1 / 2) * expectation (piOp y * piOp y) ψ
        + (1 / 2) * expectation (gradSq y) ψ
        + (m0sq / 2) * expectation (phi y * phi y) ψ
        + (lam / 24) * expectation (phi y ^ 4) ψ) := by
    intro y _
    have h0 := expectation_phi4LocalTerm_nonneg m0sq lam hm hl gradSq phi piOp hgrad hphi hpi ψ y
    rw [phi4LocalTerm] at h0
    simp only [expectation_add, expectation_smul_real] at h0
    have : (0:ℝ) ≤ a ^ d := le_of_lt haD
    exact mul_nonneg this h0
  have hsingle := Finset.single_le_sum hterm (Finset.mem_univ x)
  rw [expectation_phi4Hamiltonian] at hE
  -- At the chosen site only the `m₀²φ(x)²/2` term survives the comparison.
  have hsite : a ^ d * ((m0sq / 2) * expectation (phi x * phi x) ψ) ≤ a ^ d *
      ((1 / 2) * expectation (piOp x * piOp x) ψ
        + (1 / 2) * expectation (gradSq x) ψ
        + (m0sq / 2) * expectation (phi x * phi x) ψ
        + (lam / 24) * expectation (phi x ^ 4) ψ) := by
    have h1 : (0:ℝ) ≤ expectation (piOp x * piOp x) ψ := expectation_sq_nonneg (hpi x) ψ
    have h2 : (0:ℝ) ≤ expectation (gradSq x) ψ := expectation_nonneg (hgrad x) ψ
    have h4 : (0:ℝ) ≤ expectation (phi x ^ 4) ψ := expectation_pow_four_nonneg (hphi x) ψ
    have h3 : (0:ℝ) ≤ expectation (phi x * phi x) ψ := expectation_sq_nonneg (hphi x) ψ
    have hlm : (0:ℝ) ≤ lam / 24 := by linarith
    have haD' : (0:ℝ) ≤ a ^ d := le_of_lt haD
    nlinarith [mul_nonneg haD' (by nlinarith [h1, h2, h3, h4, hlm] :
      (0:ℝ) ≤ (1 / 2) * expectation (piOp x * piOp x) ψ
        + (1 / 2) * expectation (gradSq x) ψ
        + (lam / 24) * expectation (phi x ^ 4) ψ)]
  have hchain : a ^ d * ((m0sq / 2) * expectation (phi x * phi x) ψ) ≤ E :=
    le_trans (le_trans hsite hsingle) hE
  rw [le_div_iff₀ (mul_pos haD hm)]
  nlinarith [hchain]

/-- **Proposition 3**, inequality (75) (p. 22): in the positive-mass regime every
unit-energy-bounded state has bounded momentum fluctuations at each site,
`⟨ψ|π(x)²|ψ⟩ ≤ 2E/a^d`. -/
theorem phi4_positive_mass_momentum_bound (d : ℕ) (a m0sq lam : ℝ)
    (ha : 0 < a) (hm : 0 < m0sq) (hl : 0 ≤ lam)
    (gradSq phi piOp : sites → Matrix n n ℂ)
    (hgrad : ∀ y, (gradSq y).PosSemidef) (hphi : ∀ y, (phi y)ᴴ = phi y)
    (hpi : ∀ y, (piOp y)ᴴ = piOp y) (ψ : QState n) {E : ℝ}
    (hE : expectation (phi4Hamiltonian d a m0sq lam gradSq phi piOp) ψ ≤ E) (x : sites) :
    expectation (piOp x * piOp x) ψ ≤ 2 * E / (a ^ d) := by
  have haD : (0:ℝ) < a ^ d := pow_pos ha d
  have hterm : ∀ y ∈ Finset.univ, (0:ℝ) ≤ a ^ d *
      ((1 / 2) * expectation (piOp y * piOp y) ψ
        + (1 / 2) * expectation (gradSq y) ψ
        + (m0sq / 2) * expectation (phi y * phi y) ψ
        + (lam / 24) * expectation (phi y ^ 4) ψ) := by
    intro y _
    have h0 := expectation_phi4LocalTerm_nonneg m0sq lam hm hl gradSq phi piOp hgrad hphi hpi ψ y
    rw [phi4LocalTerm] at h0
    simp only [expectation_add, expectation_smul_real] at h0
    exact mul_nonneg (le_of_lt haD) h0
  have hsingle := Finset.single_le_sum hterm (Finset.mem_univ x)
  rw [expectation_phi4Hamiltonian] at hE
  have hsite : a ^ d * ((1 / 2) * expectation (piOp x * piOp x) ψ) ≤ a ^ d *
      ((1 / 2) * expectation (piOp x * piOp x) ψ
        + (1 / 2) * expectation (gradSq x) ψ
        + (m0sq / 2) * expectation (phi x * phi x) ψ
        + (lam / 24) * expectation (phi x ^ 4) ψ) := by
    have h1 : (0:ℝ) ≤ expectation (piOp x * piOp x) ψ := expectation_sq_nonneg (hpi x) ψ
    have h2 : (0:ℝ) ≤ expectation (gradSq x) ψ := expectation_nonneg (hgrad x) ψ
    have h3 : (0:ℝ) ≤ expectation (phi x * phi x) ψ := expectation_sq_nonneg (hphi x) ψ
    have h4 : (0:ℝ) ≤ expectation (phi x ^ 4) ψ := expectation_pow_four_nonneg (hphi x) ψ
    have hm2 : (0:ℝ) ≤ m0sq / 2 := by linarith
    have hlm : (0:ℝ) ≤ lam / 24 := by linarith
    have haD' : (0:ℝ) ≤ a ^ d := le_of_lt haD
    nlinarith [mul_nonneg haD' (by nlinarith [h1, h2, h3, h4, hm2, hlm] :
      (0:ℝ) ≤ (1 / 2) * expectation (gradSq x) ψ
        + (m0sq / 2) * expectation (phi x * phi x) ψ
        + (lam / 24) * expectation (phi x ^ 4) ψ)]
  have hchain : a ^ d * ((1 / 2) * expectation (piOp x * piOp x) ψ) ≤ E :=
    le_trans (le_trans hsite hsingle) hE
  rw [le_div_iff₀ haD]
  nlinarith [hchain]

/-- The discretized derivative of a Hermitian field is Hermitian, so its square is
positive semidefinite: this is the gradient term `(∇ₐφ)²(y)` of equation (5). -/
theorem diff_sq_posSemidef {A B : Matrix n n ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B) :
    ((A - B) * (A - B)).PosSemidef := by
  have h : (A - B)ᴴ = A - B := by
    rw [Matrix.conjTranspose_sub, hA, hB]
  have h' := Matrix.posSemidef_conjTranspose_mul_self (A - B)
  rwa [h] at h'

/-- The discretized gradient energy of equation (5) is positive semidefinite: every
direction contributes the square of the Hermitian difference
`(φ(y + ar̂ⱼ) − φ(y))/a`, whose square is positive semidefinite, and a finite sum of
positive semidefinite matrices is positive semidefinite. This is the hypothesis
`hgrad` used by Propositions 3 and 4, derived from the Hermiticity of the field. -/
theorem grad_term_posSemidef {dirs : Type*} [Fintype dirs] (a : ℝ)
    (nbr : sites → dirs → sites) (phi : sites → Matrix n n ℂ) (hphi : ∀ y, (phi y)ᴴ = phi y)
    (y : sites) :
    (∑ j : dirs, (((a⁻¹ : ℝ) : ℂ) • (phi (nbr y j) - phi y)) ^ 2).PosSemidef := by
  classical
  have hterm : ∀ j : dirs, ((((a⁻¹ : ℝ) : ℂ) • (phi (nbr y j) - phi y)) ^ 2).PosSemidef := by
    intro j
    have h : ((((a⁻¹ : ℝ) : ℂ) • (phi (nbr y j) - phi y))ᴴ)
        = ((a⁻¹ : ℝ) : ℂ) • (phi (nbr y j) - phi y) := by
      simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hphi]
    have h' := Matrix.posSemidef_conjTranspose_mul_self
      (((a⁻¹ : ℝ) : ℂ) • (phi (nbr y j) - phi y))
    rw [h] at h'
    simpa [pow_two] using h'
  induction (Finset.univ : Finset dirs) using Finset.induction with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert b s hb ih => simp only [Finset.sum_insert hb]; exact (hterm b).add ih

end Qatlib.Papers.ScatteringQFT11.MainResults
