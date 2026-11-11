/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Finite reuse and oblivious amplitude amplification (Lemma 4.9)

Shen--Wu--Yuan--Zhang, fixed arXiv:2610.05362v1, Lemma 4.9, page 22.

Let `S = [[S00, S01], [S10, S11]]` be the block matrix of the collision
transducer in the public/private splitting and suppose `S (I, Γ)^T = (V, Γ)^T`
with `V` unitary on the public space.  Applying `S` in turn to `N` public slots
and one shared private slot, preparing and unpreparing the uniform public
superposition, selects the operator

`P_N = V - S01 g_N(S11) Γ`,   `g_N(z) = (1/N) Σ_{j<N} z^j`.

The source proof solves the recursion `z_k = S10 x + S11 z_{k-1}`,
`b_k = S00 x + S01 z_{k-1}` using `(I - S11) Γ = S10` and averages the `b_k`.
We formalize the operator identity behind the averaging step: the sum of the
selected amplitudes equals `N V` minus `S01 (Σ_j S11^j) Γ`.  Dividing by `N`
gives the stated selection; the division-free form is the exact content and
avoids any invertibility hypothesis on `N`.
-/

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.ShallowLind26.ShallowSim.FiniteReuse

set_option autoImplicit false

variable {d : ℕ}

/-- The partially averaged geometric series `g_N(S11) = (1/N) Σ_{j<N} S11^j`. -/
noncomputable def geomSum (A : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (N : ℂ)⁻¹ • ∑ j ∈ Finset.range N, A ^ j

/-- **Lemma 4.9, selection identity (division-free form).**  If the public
identity `S00 + S01 Γ = V` holds, then the sum of the `N` selected public
amplitudes `S00 + S01 (I - S11^k) Γ` equals `N V - S01 (Σ_j S11^j) Γ`. -/
theorem selected_sum_identity (S00 S01 S11 Γ V : Matrix (Fin d) (Fin d) ℂ) (N : ℕ)
    (hV : S00 + S01 * Γ = V) :
    (∑ k ∈ Finset.range N, (S00 + S01 * (1 - S11 ^ k) * Γ))
      = (N : ℂ) • V - S01 * (∑ k ∈ Finset.range N, S11 ^ k) * Γ := by
  have hterm : ∀ k : ℕ, (S00 + S01 * (1 - S11 ^ k) * Γ)
      = V - S01 * S11 ^ k * Γ := by
    intro k
    have h1 : S01 * (1 - S11 ^ k) = S01 - S01 * S11 ^ k := by
      rw [mul_sub, mul_one]
    have h2 : (S01 - S01 * S11 ^ k) * Γ = S01 * Γ - S01 * S11 ^ k * Γ := by
      rw [sub_mul]
    rw [h1, h2]
    rw [show S00 + (S01 * Γ - S01 * S11 ^ k * Γ)
          = (S00 + S01 * Γ) - S01 * S11 ^ k * Γ from by abel, hV]
  calc (∑ k ∈ Finset.range N, (S00 + S01 * (1 - S11 ^ k) * Γ))
      = ∑ k ∈ Finset.range N, (V - S01 * S11 ^ k * Γ) :=
        Finset.sum_congr rfl (fun k _ => hterm k)
    _ = (∑ _k ∈ Finset.range N, V) - ∑ k ∈ Finset.range N, (S01 * S11 ^ k * Γ) :=
        Finset.sum_sub_distrib (fun _ => V) (fun k => S01 * S11 ^ k * Γ)
    _ = (N : ℂ) • V - S01 * (∑ k ∈ Finset.range N, S11 ^ k) * Γ := by
        rw [Finset.sum_const, Finset.card_range, Finset.mul_sum, Finset.sum_mul,
          ← Nat.cast_smul_eq_nsmul ℂ]

/-- **Lemma 4.9, averaged selection.**  If `N ≠ 0`, dividing the selection
identity by `N` gives `V - S01 g_N(S11) Γ`, the selected operator of the finite
reuse circuit. -/
theorem finite_reuse_selected (S00 S01 S11 Γ V : Matrix (Fin d) (Fin d) ℂ) (N : ℕ)
    (hN : (N : ℂ) ≠ 0) (hV : S00 + S01 * Γ = V) :
    (N : ℂ)⁻¹ • (∑ k ∈ Finset.range N, (S00 + S01 * (1 - S11 ^ k) * Γ))
      = V - S01 * geomSum S11 N * Γ := by
  rw [selected_sum_identity S00 S01 S11 Γ V N hV]
  simp only [geomSum, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
    inv_mul_cancel₀ hN, one_smul]

end Qatlib.Papers.ShallowLind26.ShallowSim.FiniteReuse
