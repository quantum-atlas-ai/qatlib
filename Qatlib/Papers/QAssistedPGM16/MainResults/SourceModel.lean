/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QAssistedPGM16 — finite classical Ising model for hardware-embedded learning

Fixed source: arXiv:1609.02542, *Quantum-Assisted Learning of Hardware-Embedded
Probabilistic Graphical Models* (17-page PDF, TeX build dated 2018-01-29).
Relevant pages: Eq. (3)-(5) on p.3, Eq. (6)-(11) on p.5, Eq. (12)-(13) and the
complexity discussion on p.6, Table I on p.7, OptDigits / bars-and-stripes
experiments on p.9.

The paper works with binary Ising variables `z ∈ {−1,+1}^M` and the Boltzmann
distribution `P(z) = exp(−β E(z))/Z`, with the energy of Eq. (5),
`E(z) = −Σ_{ij} J_ij z_i z_j − Σ_i h_i z_i`.  We code the finite configuration
space explicitly so the learning-rule identities of Eqs. (12)-(13) become
elementary finite-sum calculus.

Boundary: this file only supplies the paper-level finite classical Gibbs model.
It does not assert the physical claim that a D-Wave annealer samples exactly
from `exp(−β E)/Z`; that working assumption is stated in the paper (p.5) and is
kept outside Lean, as in all other paper-layer contracts.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QAssistedPGM16.MainResults

/-- Configuration space of `M` physical Ising qubits, each valued in `Bool`
(`true` = spin `+1`, `false` = spin `−1`). -/
abbrev Config (M : ℕ) := Fin M → Bool

/-- Ising spin value: `true ↦ +1`, `false ↦ −1` (paper p.3, `z ∈ {−1,+1}`). -/
def spin {M : ℕ} (z : Config M) (i : Fin M) : ℝ := if z i then 1 else -1

/-- Parameter index of the fully connected model: `Sum.inl (i,j)` is the
coupling `J_ij`, `Sum.inr i` is the local field `h_i` (Eq. (5), p.3). -/
abbrev ParamIndex (M : ℕ) := (Fin M × Fin M) ⊕ Fin M

/-- The monomial multiplying each parameter: `Z_i Z_j` for a coupling and `Z_i`
for a local field (Eqs. (12)-(13), p.6). -/
def feature {M : ℕ} : ParamIndex M → Config M → ℝ
  | Sum.inl (i, j) => fun z => spin z i * spin z j
  | Sum.inr i => fun z => spin z i

/-- Energy of Eq. (5), p.3: `E_θ(z) = −Σ_a θ_a A_a(z)`. -/
def energy {M : ℕ} (θ : ParamIndex M → ℝ) (z : Config M) : ℝ :=
  -∑ a, θ a * feature a z

/-- Boltzmann weight `exp(−β E_θ(z))` (Eq. (4), p.3). -/
def boltzmannWeight {M : ℕ} (β : ℝ) (θ : ParamIndex M → ℝ) (z : Config M) : ℝ :=
  Real.exp (-(β * energy θ z))

/-- Partition function `Z = Σ_z exp(−β E_θ(z))` (Eq. (4), p.3). -/
def partition {M : ℕ} (β : ℝ) (θ : ParamIndex M → ℝ) : ℝ :=
  ∑ z : Config M, boltzmannWeight β θ z

/-- Normalized Gibbs/Boltzmann probability of a configuration. -/
def gibbsDist {M : ℕ} (β : ℝ) (θ : ParamIndex M → ℝ) (z : Config M) : ℝ :=
  boltzmannWeight β θ z / partition β θ

/-- Ensemble average `⟨f⟩_ρ = Σ_z f(z) P_θ(z)` (the "negative phase" of p.6). -/
def expectation {M : ℕ} (β : ℝ) (θ : ParamIndex M → ℝ) (f : Config M → ℝ) : ℝ :=
  (∑ z : Config M, f z * boltzmannWeight β θ z) / partition β θ

/-- Classical relative entropy `S(p‖q) = Σ_z p(z) (log p(z) − log q(z))`, the
diagonal counterpart of Eq. (9), p.5. -/
def relativeEntropy {M : ℕ} (p q : Config M → ℝ) : ℝ :=
  ∑ z : Config M, p z * (Real.log (p z) - Real.log (q z))

/-- Unit-speed path through the parameter vector `θ` in coordinate `a`:
`θ_a(t) = θ_a + t`, all other coordinates fixed.  This is the continuous-time
counterpart of the update of Eqs. (10)-(11), p.5. -/
def path {M : ℕ} (θ : ParamIndex M → ℝ) (a : ParamIndex M) (t : ℝ) : ParamIndex M → ℝ :=
  Function.update θ a (θ a + t)

/-- The parameter path starts at `θ`. -/
theorem path_zero {M : ℕ} (θ : ParamIndex M → ℝ) (a : ParamIndex M) : path θ a 0 = θ := by
  unfold path
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · rw [Function.update_of_ne hb]

/-- Free-energy form of the relative entropy against a Gibbs state; equal to
`relativeEntropy p (gibbsDist β θ)` for a normalized `p` (see
`relativeEntropy_gibbs_eq`). -/
def freeEnergy {M : ℕ} (p : Config M → ℝ) (β : ℝ) (θ : ParamIndex M → ℝ) : ℝ :=
  (∑ z : Config M, p z * Real.log (p z)) + β * (∑ z : Config M, p z * energy θ z) +
    Real.log (partition β θ)

/-- The partition function is positive (every Boltzmann weight is a positive
exponential). -/
theorem partition_pos {M : ℕ} (β : ℝ) (θ : ParamIndex M → ℝ) : 0 < partition β θ := by
  unfold partition
  apply Finset.sum_pos
  · intro z _
    exact Real.exp_pos _
  · exact ⟨fun _ => false, Finset.mem_univ _⟩

/-- `expectation f * Z = Σ_z f(z) exp(−β E(z))`. -/
theorem expectation_mul_partition {M : ℕ} (β : ℝ) (θ : ParamIndex M → ℝ)
    (f : Config M → ℝ) :
    expectation β θ f * partition β θ = ∑ z : Config M, f z * boltzmannWeight β θ z := by
  unfold expectation
  exact div_mul_cancel₀ _ (ne_of_gt (partition_pos β θ))

/-- Logarithm of the Gibbs probabilities, Eq. (4): `log P(z) = −βE(z) − log Z`. -/
theorem log_gibbsDist {M : ℕ} (β : ℝ) (θ : ParamIndex M → ℝ) (z : Config M) :
    Real.log (gibbsDist β θ z) = -(β * energy θ z) - Real.log (partition β θ) := by
  unfold gibbsDist boltzmannWeight
  rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt (partition_pos β θ)), Real.log_exp]

/-- Eq. (9) written in free-energy form: for normalized data weights `p`,
`S(p‖P_θ) = Σ p log p + β ⟨E⟩_p + log Z`.  This is the classical-diagonal
counterpart of `Tr ρ_D log ρ_D − Tr ρ_D log ρ`. -/
theorem relativeEntropy_gibbs_eq {M : ℕ} (p : Config M → ℝ) (hp : ∑ z : Config M, p z = 1)
    (β : ℝ) (θ : ParamIndex M → ℝ) :
    relativeEntropy p (gibbsDist β θ) = freeEnergy p β θ := by
  unfold relativeEntropy freeEnergy
  have h1 : ∀ z : Config M, p z * Real.log (gibbsDist β θ z)
      = -(β * (p z * energy θ z)) - p z * Real.log (partition β θ) := by
    intro z
    rw [log_gibbsDist]
    ring
  have hsum : ∑ z : Config M, p z * Real.log (gibbsDist β θ z)
      = -(β * ∑ z : Config M, p z * energy θ z) - Real.log (partition β θ) := by
    calc
      ∑ z : Config M, p z * Real.log (gibbsDist β θ z)
          = ∑ z : Config M,
              (-(β * (p z * energy θ z)) - p z * Real.log (partition β θ)) :=
            Finset.sum_congr rfl (fun z _ => h1 z)
      _ = (∑ z : Config M, -(β * (p z * energy θ z))) -
            ∑ z : Config M, p z * Real.log (partition β θ) := by
            rw [Finset.sum_sub_distrib]
      _ = -(∑ z : Config M, β * (p z * energy θ z)) -
            ∑ z : Config M, p z * Real.log (partition β θ) := by
            rw [Finset.sum_neg_distrib]
      _ = -(β * ∑ z : Config M, p z * energy θ z) -
            ∑ z : Config M, p z * Real.log (partition β θ) := by
            rw [Finset.mul_sum]
      _ = -(β * ∑ z : Config M, p z * energy θ z) -
            (∑ z : Config M, p z) * Real.log (partition β θ) := by
            rw [Finset.sum_mul]
      _ = -(β * ∑ z : Config M, p z * energy θ z) - Real.log (partition β θ) := by
            rw [hp, one_mul]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib, hsum]
  ring

end Qatlib.Papers.QAssistedPGM16.MainResults
