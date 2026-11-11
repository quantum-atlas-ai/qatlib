/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# VariationalPositiveMass — Proposition 3 field/momentum bounds

Source: Jordan–Lee–Preskill, *Quantum Algorithms for Quantum Field Theories*,
fixed arXiv:1111.3633v1 (2011).

Proposition 3 (p.25): let `H` be the lattice scalar-field Hamiltonian of Eq. 15,
`H = Σ_{x∈Ω} aᵈ [ ½π(x)² + ½(∇ₐφ)²(x) + (m₀²/2)φ(x)² + (λ₀/4!)φ(x)⁴ ]`.
If `m₀² > 0` and `λ₀ ≥ 0`, and `|ψ⟩` is any field state with `⟨ψ|H|ψ⟩ ≤ E`, then
for every lattice site `x`,
`⟨ψ|φ(x)²|ψ⟩ ≤ 2E/(aᵈ m₀²)   (Eq.45)` and
`⟨ψ|π(x)²|ψ⟩ ≤ 2E/aᵈ       (Eq.46)`.

The paper's proof (Eqs.47–50) rewrites `E ≥ ⟨H⟩` as the lattice sum Eq.48 and drops
all the positive-semidefinite local operators except one. The formalization below
keeps exactly that structure: the Hamiltonian expectation is an explicit finite sum
over lattice sites of real local expectation values, each local term
`½π² + ½(∇ₐφ)² + (m₀²/2)φ² + (λ₀/4!)φ⁴` is nonnegative (all coefficients and the
squared expectations are), and dropping the nonnegative terms yields the two bounds.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QFieldTheory11.MainResults.VariationalPositiveMass

/-- Fixed arXiv:1111.3633v1, Proposition 3 (p.25, Eqs.45–46). For a lattice scalar-field
Hamiltonian of Eq.15 with positive mass `m₀² > 0` and `λ₀ ≥ 0`, any state whose energy
expectation `⟨H⟩` (the finite sum over sites of `aᵈ(½π² + ½(∇ₐφ)² + (m₀²/2)φ² + (λ₀/4!)φ⁴)`)
is at most `E` satisfies, at every site `x`,
`⟨φ(x)²⟩ ≤ 2E/(aᵈ m₀²)` and `⟨π(x)²⟩ ≤ 2E/aᵈ`. -/
theorem prop3_positive_mass_bounds
    {ι : Type*} [Fintype ι]
    (E a m0sq lam0 : ℝ) (d : ℕ)
    (φ2 π2 grad2 φ4 : ι → ℝ)
    (ha : 0 < a) (hm : 0 < m0sq) (hl : 0 ≤ lam0)
    (hφ2 : ∀ i, 0 ≤ φ2 i) (hπ2 : ∀ i, 0 ≤ π2 i)
    (hgrad2 : ∀ i, 0 ≤ grad2 i) (hφ4 : ∀ i, 0 ≤ φ4 i)
    (hH : ∑ i, a ^ d *
        (π2 i / 2 + grad2 i / 2 + m0sq * φ2 i / 2 + lam0 * φ4 i / 24) ≤ E)
    (x : ι) :
    φ2 x ≤ 2 * E / (a ^ d * m0sq) ∧ π2 x ≤ 2 * E / a ^ d := by
  -- The local Hamiltonian term and its nonnegativity (all summands are PSD expectations).
  set term : ι → ℝ := fun i =>
    a ^ d * (π2 i / 2 + grad2 i / 2 + m0sq * φ2 i / 2 + lam0 * φ4 i / 24) with hterm
  have hπ2half : ∀ i, 0 ≤ π2 i / 2 := fun i => by linarith [hπ2 i]
  have hgrad2half : ∀ i, 0 ≤ grad2 i / 2 := fun i => by linarith [hgrad2 i]
  have hmφ2 : ∀ i, 0 ≤ m0sq * φ2 i / 2 := fun i => by
    have := mul_nonneg hm.le (hφ2 i); linarith
  have hlφ4 : ∀ i, 0 ≤ lam0 * φ4 i / 24 := fun i => by
    have := mul_nonneg hl (hφ4 i); linarith
  have hapos : 0 < a ^ d := pow_pos ha d
  have hterm_nonneg : ∀ i, 0 ≤ term i := fun i => by
    have hin : 0 ≤ π2 i / 2 + grad2 i / 2 + m0sq * φ2 i / 2 + lam0 * φ4 i / 24 := by
      linarith [hπ2half i, hgrad2half i, hmφ2 i, hlφ4 i]
    exact mul_nonneg hapos.le hin
  -- The single site's term is at most the whole sum (Eq.48 ≥ one term).
  have hx_le : term x ≤ ∑ i, term i :=
    Finset.single_le_sum (f := term) (fun i _ => hterm_nonneg i) (Finset.mem_univ x)
  have hsum_le : ∑ i, term i ≤ E := hH
  -- Bound on ⟨φ(x)²⟩: drop every nonnegative term except `aᵈ(m₀²/2)φ(x)²`.
  have hφ_lower : a ^ d * (m0sq * φ2 x / 2) ≤ term x := by
    have hin : m0sq * φ2 x / 2 ≤
        π2 x / 2 + grad2 x / 2 + m0sq * φ2 x / 2 + lam0 * φ4 x / 24 := by
      linarith [hπ2half x, hgrad2half x, hlφ4 x]
    exact mul_le_mul_of_nonneg_left hin hapos.le
  have hφ_energy : a ^ d * (m0sq * φ2 x / 2) ≤ E :=
    le_trans hφ_lower (le_trans hx_le hsum_le)
  have hφ_bound : φ2 x ≤ 2 * E / (a ^ d * m0sq) := by
    have hpos : 0 < a ^ d * m0sq := mul_pos hapos hm
    rw [le_div_iff₀ hpos]
    nlinarith [hφ_energy]
  -- Bound on ⟨π(x)²⟩: drop every nonnegative term except `aᵈ(1/2)π(x)²`.
  have hπ_lower : a ^ d * (π2 x / 2) ≤ term x := by
    have hin : π2 x / 2 ≤
        π2 x / 2 + grad2 x / 2 + m0sq * φ2 x / 2 + lam0 * φ4 x / 24 := by
      linarith [hgrad2half x, hmφ2 x, hlφ4 x]
    exact mul_le_mul_of_nonneg_left hin hapos.le
  have hπ_energy : a ^ d * (π2 x / 2) ≤ E :=
    le_trans hπ_lower (le_trans hx_le hsum_le)
  have hπ_bound : π2 x ≤ 2 * E / a ^ d := by
    rw [le_div_iff₀ hapos]
    nlinarith [hπ_energy]
  exact ⟨hφ_bound, hπ_bound⟩

end Qatlib.Papers.QFieldTheory11.MainResults.VariationalPositiveMass
