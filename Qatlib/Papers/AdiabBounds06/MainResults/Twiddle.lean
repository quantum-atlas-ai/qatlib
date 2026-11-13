/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabBounds06.MainResults.Defs

/-!
# Spectral-band data and twiddle identities

`BandData` packages orthogonal spectral projections, reduced resolvents, and a positive gap
bound. Its `BandData.twiddle` operation is defined by a finite resolvent sum and satisfies the
block and commutator identities used in the adiabatic analysis of [JansenRuskaiSeiler2007].

## Main statements

* `BandData.twiddle`: the finite sum defining the twiddle operation.
* `BandData.commutator_H_twiddle`: the identity `[H, twiddle X] = P * X - X * P`.
* `BandData.twiddle_adiSandwich`: the two off-diagonal blocks of the adiabatic commutator.

## References

* [Jansen et al., 2007][JansenRuskaiSeiler2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.AdiabBounds06.MainResults

variable {n : ℕ}

/-- The corrected Hamiltonian `H + (i/τ)[Pdot, P]` for fixed matrices and real parameter `τ`. -/
def HτAconst (τ : ℝ) (H P Pdot : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  H + (Complex.I / (τ : ℂ)) • (Pdot * P - P * Pdot)

/-- Spectral-band data consisting of orthogonal projections summing to `P`, associated real
eigenvalues, complementary reduced resolvents, and a positive gap controlling their norms. -/
structure BandData (H : Matrix (Fin n) (Fin n) ℂ) where
  m : ℕ
  lam : Fin m → ℝ
  P : Matrix (Fin n) (Fin n) ℂ
  Pj : Fin m → Matrix (Fin n) (Fin n) ℂ
  Rhat : Fin m → Matrix (Fin n) (Fin n) ℂ
  g : ℝ
  hg : 0 < g
  P_proj : IsProj P
  Pj_proj : ∀ j, IsProj (Pj j)
  Pj_sum : (∑ j, Pj j) = P
  Pj_orth : ∀ j k, j ≠ k → Pj j * Pj k = 0
  H_Pj : ∀ j, H * Pj j = (lam j : ℂ) • Pj j
  Pj_H : ∀ j, Pj j * H = (lam j : ℂ) • Pj j
  Rhat_left : ∀ j, (1 - P) * Rhat j = Rhat j
  Rhat_right : ∀ j, Rhat j * (1 - P) = Rhat j
  Rhat_res : ∀ j, (H - (lam j : ℂ) • 1) * Rhat j = 1 - P
  Rhat_res' : ∀ j, Rhat j * (H - (lam j : ℂ) • 1) = 1 - P
  Rhat_bound : ∀ j, ‖Rhat j‖ ≤ 1 / g

namespace BandData

variable {H : Matrix (Fin n) (Fin n) ℂ}

/-- The negative sum of `Pj * X * Rhat + Rhat * X * Pj` over the spectral-band components. -/
def twiddle (D : BandData H) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  -∑ j, (D.Pj j * X * D.Rhat j + D.Rhat j * X * D.Pj j)

/-- The twiddle operation is the negative finite sum of its two reduced-resolvent terms for each
band component. See [JansenRuskaiSeiler2007]. -/
theorem twiddle_eq_sum_resolvents (D : BandData H) (X : Matrix (Fin n) (Fin n) ℂ) :
    D.twiddle X
      = -∑ j, (D.Pj j * X * D.Rhat j + D.Rhat j * X * D.Pj j) := rfl

/-- Left multiplication by the total band projection fixes each component projection. -/
theorem P_mul_Pj (D : BandData H) (j : Fin D.m) : D.P * D.Pj j = D.Pj j := by
  rw [← D.Pj_sum, Finset.sum_mul, Finset.sum_eq_single j]
  · exact (D.Pj_proj j).1
  · intro k _ hk
    exact D.Pj_orth k j hk
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- Right multiplication by the total band projection fixes each component projection. -/
theorem Pj_mul_P (D : BandData H) (j : Fin D.m) : D.Pj j * D.P = D.Pj j := by
  rw [← D.Pj_sum, Finset.mul_sum, Finset.sum_eq_single j]
  · exact (D.Pj_proj j).1
  · intro k _ hk
    exact D.Pj_orth j k hk.symm
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The complementary band projection annihilates each component projection on the left. -/
theorem one_sub_mul_Pj (D : BandData H) (j : Fin D.m) :
    (1 - D.P) * D.Pj j = 0 := by
  rw [sub_mul, one_mul, D.P_mul_Pj j, sub_self]

/-- Each component projection annihilates the complementary band projection on the right. -/
theorem Pj_mul_one_sub (D : BandData H) (j : Fin D.m) :
    D.Pj j * (1 - D.P) = 0 := by
  rw [mul_sub, mul_one, D.Pj_mul_P j, sub_self]

/-- The total band projection annihilates each reduced resolvent on the left. -/
theorem P_mul_Rhat (D : BandData H) (j : Fin D.m) : D.P * D.Rhat j = 0 := by
  rw [← D.Rhat_left j, ← mul_assoc,
    show D.P * (1 - D.P) = 0 from (mul_orthCompl D.P_proj).1, zero_mul]

/-- Each reduced resolvent annihilates the total band projection on the right. -/
theorem Rhat_mul_P (D : BandData H) (j : Fin D.m) : D.Rhat j * D.P = 0 := by
  rw [← D.Rhat_right j, mul_assoc,
    show (1 - D.P) * D.P = 0 from (mul_orthCompl D.P_proj).2, mul_zero]

/-- The Hamiltonian commutes with each reduced resolvent. -/
theorem H_Rhat_comm (D : BandData H) (j : Fin D.m) : H * D.Rhat j = D.Rhat j * H := by
  set R := D.Rhat j with hR
  set K : Matrix (Fin n) (Fin n) ℂ := (D.lam j : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) with hK
  have hsplit : H = (H - K) + K := by abel
  have hres : (H - K) * R = 1 - D.P := by rw [hR, hK]; exact D.Rhat_res j
  have hres' : R * (H - K) = 1 - D.P := by rw [hR, hK]; exact D.Rhat_res' j
  have h1 : H * R = (1 - D.P) + K * R := by
    calc H * R = ((H - K) + K) * R := by conv_lhs => rw [hsplit]
      _ = (H - K) * R + K * R := by rw [add_mul]
      _ = (1 - D.P) + K * R := by rw [hres]
  have h2 : R * H = (1 - D.P) + R * K := by
    calc R * H = R * ((H - K) + K) := by conv_lhs => rw [hsplit]
      _ = R * (H - K) + R * K := by rw [mul_add]
      _ = (1 - D.P) + R * K := by rw [hres']
  have hKR : K * R = (D.lam j : ℂ) • R := by rw [hK, Matrix.smul_mul, one_mul]
  have hRK : R * K = (D.lam j : ℂ) • R := by rw [hK, Matrix.mul_smul, mul_one]
  rw [h1, h2, hKR, hRK]

/-- Left multiplication of a reduced resolvent by the Hamiltonian equals its eigenvalue multiple
plus the complementary band projection. -/
theorem H_mul_Rhat (D : BandData H) (j : Fin D.m) :
    H * D.Rhat j = (D.lam j : ℂ) • D.Rhat j + (1 - D.P) := by
  have h := D.Rhat_res j
  rw [sub_mul, Matrix.smul_mul, one_mul] at h
  calc H * D.Rhat j
      = (H * D.Rhat j - (D.lam j : ℂ) • D.Rhat j) + (D.lam j : ℂ) • D.Rhat j := by abel
    _ = (1 - D.P) + (D.lam j : ℂ) • D.Rhat j := by rw [h]
    _ = (D.lam j : ℂ) • D.Rhat j + (1 - D.P) := by abel

/-- Right multiplication of a reduced resolvent by the Hamiltonian equals its eigenvalue
multiple plus the complementary band projection. -/
theorem Rhat_mul_H (D : BandData H) (j : Fin D.m) :
    D.Rhat j * H = (D.lam j : ℂ) • D.Rhat j + (1 - D.P) := by
  have h := D.Rhat_res' j
  rw [mul_sub, Matrix.mul_smul, mul_one] at h
  calc D.Rhat j * H
      = (D.Rhat j * H - (D.lam j : ℂ) • D.Rhat j) + (D.lam j : ℂ) • D.Rhat j := by abel
    _ = (1 - D.P) + (D.lam j : ℂ) • D.Rhat j := by rw [h]
    _ = (D.lam j : ℂ) • D.Rhat j + (1 - D.P) := by abel

/-- Left multiplication by the total band projection fixes a product beginning with a component
projection. -/
theorem P_mul_Pj_mul (D : BandData H) (j : Fin D.m) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    D.P * (D.Pj j * X * Y) = D.Pj j * X * Y := by
  rw [← mul_assoc D.P (D.Pj j * X) Y, ← mul_assoc D.P (D.Pj j) X, D.P_mul_Pj j]

/-- Left multiplication by the total band projection annihilates a product beginning with a
reduced resolvent. -/
theorem P_mul_Rhat_mul (D : BandData H) (j : Fin D.m) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    D.P * (D.Rhat j * X * Y) = 0 := by
  rw [← mul_assoc D.P (D.Rhat j * X) Y, ← mul_assoc D.P (D.Rhat j) X, D.P_mul_Rhat j]
  simp

/-- The diagonal block `P * twiddle X * P` vanishes. See [JansenRuskaiSeiler2007]. -/
theorem P_twiddle_P (D : BandData H) (X : Matrix (Fin n) (Fin n) ℂ) :
    D.P * D.twiddle X * D.P = 0 := by
  have hA : ∀ j : Fin D.m, D.P * (D.Pj j * X * D.Rhat j) * D.P = 0 := by
    intro j
    rw [D.P_mul_Pj_mul j X (D.Rhat j),
      mul_assoc (D.Pj j * X) (D.Rhat j) D.P, D.Rhat_mul_P j, mul_zero]
  have hB : ∀ j : Fin D.m, D.P * (D.Rhat j * X * D.Pj j) * D.P = 0 := by
    intro j
    rw [D.P_mul_Rhat_mul j X (D.Pj j), zero_mul]
  have hterm : ∀ j : Fin D.m,
      D.P * (D.Pj j * X * D.Rhat j + D.Rhat j * X * D.Pj j) * D.P = 0 := by
    intro j
    rw [mul_add, add_mul, hA j, hB j, add_zero]
  rw [D.twiddle_eq_sum_resolvents X, mul_neg, neg_mul]
  have hsum :
      D.P * (∑ j, (D.Pj j * X * D.Rhat j + D.Rhat j * X * D.Pj j)) * D.P = 0 := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_eq_zero (fun j _ => hterm j)
  rw [hsum, neg_zero]

/-- The complementary band projection annihilates a product beginning with a component
projection. -/
theorem Q_mul_Pj_mul (D : BandData H) (j : Fin D.m) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    (1 - D.P) * (D.Pj j * X * Y) = 0 := by
  rw [← mul_assoc (1 - D.P) (D.Pj j * X) Y, ← mul_assoc (1 - D.P) (D.Pj j) X,
    D.one_sub_mul_Pj j]
  simp

/-- The diagonal block `(1 - P) * twiddle X * (1 - P)` vanishes. See [JansenRuskaiSeiler2007]. -/
theorem Q_twiddle_Q (D : BandData H) (X : Matrix (Fin n) (Fin n) ℂ) :
    (1 - D.P) * D.twiddle X * (1 - D.P) = 0 := by
  have hA : ∀ j : Fin D.m, (1 - D.P) * (D.Pj j * X * D.Rhat j) * (1 - D.P) = 0 := by
    intro j
    rw [← mul_assoc (1 - D.P) (D.Pj j * X) (D.Rhat j),
      ← mul_assoc (1 - D.P) (D.Pj j) X, D.one_sub_mul_Pj j]
    simp
  have hB : ∀ j : Fin D.m, (1 - D.P) * (D.Rhat j * X * D.Pj j) * (1 - D.P) = 0 := by
    intro j
    rw [← mul_assoc (1 - D.P) (D.Rhat j * X) (D.Pj j),
      ← mul_assoc (1 - D.P) (D.Rhat j) X, D.Rhat_left j,
      mul_assoc (D.Rhat j * X) (D.Pj j) (1 - D.P), D.Pj_mul_one_sub j, mul_zero]
  have hterm : ∀ j : Fin D.m,
      (1 - D.P) * (D.Pj j * X * D.Rhat j + D.Rhat j * X * D.Pj j) * (1 - D.P) = 0 := by
    intro j
    rw [mul_add, add_mul, hA j, hB j, add_zero]
  rw [D.twiddle_eq_sum_resolvents X, mul_neg, neg_mul]
  have hsum :
      (1 - D.P) * (∑ j, (D.Pj j * X * D.Rhat j + D.Rhat j * X * D.Pj j))
        * (1 - D.P) = 0 := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_eq_zero (fun j _ => hterm j)
  rw [hsum, neg_zero]

/-- Left multiplication of `twiddle X` by `P` retains only the terms `-Pj * X * Rhat`. -/
theorem P_mul_twiddle (D : BandData H) (X : Matrix (Fin n) (Fin n) ℂ) :
    D.P * D.twiddle X = -∑ j, D.Pj j * X * D.Rhat j := by
  rw [D.twiddle_eq_sum_resolvents X, mul_neg, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_add, D.P_mul_Pj_mul j X (D.Rhat j), D.P_mul_Rhat_mul j X (D.Pj j), add_zero]

/-- Right multiplication of `twiddle X` by `P` retains only the terms `-Rhat * X * Pj`. -/
theorem twiddle_mul_P (D : BandData H) (X : Matrix (Fin n) (Fin n) ℂ) :
    D.twiddle X * D.P = -∑ j, D.Rhat j * X * D.Pj j := by
  rw [D.twiddle_eq_sum_resolvents X, neg_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [add_mul]
  have h1 : (D.Pj j * X * D.Rhat j) * D.P = 0 := by
    rw [mul_assoc, D.Rhat_mul_P j, mul_zero]
  have h2 : (D.Rhat j * X * D.Pj j) * D.P = D.Rhat j * X * D.Pj j := by
    rw [mul_assoc, D.Pj_mul_P j]
  rw [h1, h2, zero_add]

/-- The block `P * twiddle X * (1 - P)` equals the negative sum of `Pj * X * Rhat`. See
[JansenRuskaiSeiler2007]. -/
theorem P_twiddle_Q (D : BandData H) (X : Matrix (Fin n) (Fin n) ℂ) :
    D.P * D.twiddle X * (1 - D.P) = -∑ j, D.Pj j * X * D.Rhat j := by
  rw [D.P_mul_twiddle, neg_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, D.Rhat_right j]

/-- The block `(1 - P) * twiddle X * P` equals the negative sum of `Rhat * X * Pj`. See
[JansenRuskaiSeiler2007]. -/
theorem Q_twiddle_P (D : BandData H) (X : Matrix (Fin n) (Fin n) ℂ) :
    (1 - D.P) * D.twiddle X * D.P = -∑ j, D.Rhat j * X * D.Pj j := by
  rw [mul_assoc, D.twiddle_mul_P, mul_neg, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc (1 - D.P) (D.Rhat j * X) (D.Pj j), ← mul_assoc (1 - D.P) (D.Rhat j) X,
    D.Rhat_left j]

/-- The commutator of `H` with `Pj * X * Rhat` equals `-Pj * X * (1 - P)`. -/
theorem commutator_H_PjXR (D : BandData H) (X : Matrix (Fin n) (Fin n) ℂ) (j : Fin D.m) :
    H * (D.Pj j * X * D.Rhat j) - (D.Pj j * X * D.Rhat j) * H
      = -(D.Pj j * X * (1 - D.P)) := by
  have hl : H * (D.Pj j * X * D.Rhat j) = (D.lam j : ℂ) • (D.Pj j * X * D.Rhat j) := by
    rw [← mul_assoc, ← mul_assoc, D.H_Pj j, Matrix.smul_mul, Matrix.smul_mul]
  have hr : (D.Pj j * X * D.Rhat j) * H
      = (D.lam j : ℂ) • (D.Pj j * X * D.Rhat j) + D.Pj j * X * (1 - D.P) := by
    calc (D.Pj j * X * D.Rhat j) * H = (D.Pj j * X) * (D.Rhat j * H) := by rw [mul_assoc]
      _ = (D.Pj j * X) * ((D.lam j : ℂ) • D.Rhat j + (1 - D.P)) := by rw [Rhat_mul_H D j]
      _ = (D.Pj j * X) * ((D.lam j : ℂ) • D.Rhat j) + (D.Pj j * X) * (1 - D.P) := by
          rw [mul_add]
      _ = (D.lam j : ℂ) • ((D.Pj j * X) * D.Rhat j) + (D.Pj j * X) * (1 - D.P) := by
          rw [Matrix.mul_smul]
  rw [hl, hr]
  abel

/-- The commutator of `H` with `Rhat * X * Pj` equals `(1 - P) * X * Pj`. -/
theorem commutator_H_RXP (D : BandData H) (X : Matrix (Fin n) (Fin n) ℂ) (j : Fin D.m) :
    H * (D.Rhat j * X * D.Pj j) - (D.Rhat j * X * D.Pj j) * H
      = (1 - D.P) * X * D.Pj j := by
  have hl : H * (D.Rhat j * X * D.Pj j)
      = (D.lam j : ℂ) • (D.Rhat j * X * D.Pj j) + (1 - D.P) * X * D.Pj j := by
    calc H * (D.Rhat j * X * D.Pj j) = (H * D.Rhat j) * X * D.Pj j := by
          rw [← mul_assoc, ← mul_assoc]
      _ = ((D.lam j : ℂ) • D.Rhat j + (1 - D.P)) * X * D.Pj j := by rw [H_mul_Rhat D j]
      _ = ((D.lam j : ℂ) • D.Rhat j) * X * D.Pj j + ((1 - D.P) * X) * D.Pj j := by
          rw [add_mul, add_mul]
      _ = (D.lam j : ℂ) • ((D.Rhat j * X) * D.Pj j) + (1 - D.P) * X * D.Pj j := by
          rw [Matrix.smul_mul, Matrix.smul_mul]
  have hr : (D.Rhat j * X * D.Pj j) * H
      = (D.lam j : ℂ) • (D.Rhat j * X * D.Pj j) := by
    calc (D.Rhat j * X * D.Pj j) * H = (D.Rhat j * X) * (D.Pj j * H) := by rw [mul_assoc]
      _ = (D.Rhat j * X) * ((D.lam j : ℂ) • D.Pj j) := by rw [D.Pj_H j]
      _ = (D.lam j : ℂ) • ((D.Rhat j * X) * D.Pj j) := by rw [Matrix.mul_smul]
  rw [hl, hr]
  abel

/-- The commutator of `H` with `twiddle X` equals `P * X - X * P`. See [JansenRuskaiSeiler2007]. -/
theorem commutator_H_twiddle (D : BandData H) (X : Matrix (Fin n) (Fin n) ℂ) :
    commutator H (D.twiddle X) = D.P * X - X * D.P := by
  set S : Matrix (Fin n) (Fin n) ℂ :=
    ∑ j, (D.Pj j * X * D.Rhat j + D.Rhat j * X * D.Pj j) with hS
  have hcommj : ∀ j : Fin D.m,
      H * (D.Pj j * X * D.Rhat j + D.Rhat j * X * D.Pj j)
        - (D.Pj j * X * D.Rhat j + D.Rhat j * X * D.Pj j) * H
      = -(D.Pj j * X * (1 - D.P)) + (1 - D.P) * X * D.Pj j := by
    intro j
    have hA := commutator_H_PjXR D X j
    have hB := commutator_H_RXP D X j
    calc H * (D.Pj j * X * D.Rhat j + D.Rhat j * X * D.Pj j)
          - (D.Pj j * X * D.Rhat j + D.Rhat j * X * D.Pj j) * H
        = (H * (D.Pj j * X * D.Rhat j) - (D.Pj j * X * D.Rhat j) * H)
            + (H * (D.Rhat j * X * D.Pj j) - (D.Rhat j * X * D.Pj j) * H) := by
          noncomm_ring
      _ = -(D.Pj j * X * (1 - D.P)) + (1 - D.P) * X * D.Pj j := by rw [hA, hB]
  have hcommS : commutator H S
      = ∑ j, (-(D.Pj j * X * (1 - D.P)) + (1 - D.P) * X * D.Pj j) := by
    rw [commutator, hS, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => hcommj j)
  have htw : D.twiddle X = -S := by
    rw [D.twiddle_eq_sum_resolvents X, hS]
  rw [htw]
  have hneg : commutator H (-S) = -commutator H S := by
    rw [commutator, commutator]
    noncomm_ring
  rw [hneg, hcommS]
  have hsumA : (∑ j, D.Pj j * X * (1 - D.P)) = D.P * X * (1 - D.P) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, D.Pj_sum]
  have hsumB : (∑ j, (1 - D.P) * X * D.Pj j) = (1 - D.P) * X * D.P := by
    rw [← Finset.mul_sum, D.Pj_sum]
  have hsplit : (∑ j, (-(D.Pj j * X * (1 - D.P)) + (1 - D.P) * X * D.Pj j))
      = -(∑ j, D.Pj j * X * (1 - D.P)) + ∑ j, (1 - D.P) * X * D.Pj j := by
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [hsplit, hsumA, hsumB]
  noncomm_ring

/-- The `P` to complementary block of `[H, twiddle X]` equals `P * X * (1 - P)`. -/
theorem P_commutator_H_twiddle_Q (D : BandData H) (X : Matrix (Fin n) (Fin n) ℂ) :
    D.P * commutator H (D.twiddle X) * (1 - D.P) = D.P * X * (1 - D.P) := by
  rw [commutator_H_twiddle]
  have hPP : D.P * D.P = D.P := D.P_proj.1
  have hPQ : D.P * (1 - D.P) = 0 := (mul_orthCompl D.P_proj).1
  calc D.P * (D.P * X - X * D.P) * (1 - D.P)
      = D.P * (D.P * X) * (1 - D.P) - D.P * (X * D.P) * (1 - D.P) := by noncomm_ring
    _ = (D.P * D.P) * X * (1 - D.P) - D.P * X * (D.P * (1 - D.P)) := by noncomm_ring
    _ = D.P * X * (1 - D.P) - D.P * X * 0 := by rw [hPP, hPQ]
    _ = D.P * X * (1 - D.P) := by rw [mul_zero, sub_zero]

/-- The complementary to `P` block of `[H, twiddle X]` equals `-(1 - P) * X * P`. -/
theorem Q_commutator_H_twiddle_P (D : BandData H) (X : Matrix (Fin n) (Fin n) ℂ) :
    (1 - D.P) * commutator H (D.twiddle X) * D.P = -((1 - D.P) * X * D.P) := by
  rw [commutator_H_twiddle]
  have hPP : D.P * D.P = D.P := D.P_proj.1
  have hQP : (1 - D.P) * D.P = 0 := (mul_orthCompl D.P_proj).2
  calc (1 - D.P) * (D.P * X - X * D.P) * D.P
      = (1 - D.P) * (D.P * X) * D.P - (1 - D.P) * (X * D.P) * D.P := by noncomm_ring
    _ = ((1 - D.P) * D.P) * X * D.P - (1 - D.P) * X * (D.P * D.P) := by noncomm_ring
    _ = 0 - (1 - D.P) * X * D.P := by simp [hQP, hPP]
    _ = -((1 - D.P) * X * D.P) := by rw [zero_sub]

/-- For an idempotent `P`, both diagonal blocks of the commutator `Pdot * P - P * Pdot` vanish. -/
theorem Pdot_diag_blocks (P Pdot : Matrix (Fin n) (Fin n) ℂ) (hPP : P * P = P) :
    P * (Pdot * P - P * Pdot) * P = 0 ∧
      (1 - P) * (Pdot * P - P * Pdot) * (1 - P) = 0 := by
  have hPQ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPP, sub_self]
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
  constructor
  · have h1 : P * (Pdot * P) * P = P * Pdot * P := by
      rw [← mul_assoc P Pdot P, mul_assoc, hPP]
    have h2 : P * (P * Pdot) * P = P * Pdot * P := by
      rw [← mul_assoc P P Pdot, hPP]
    rw [mul_sub, sub_mul, h1, h2, sub_self]
  · have h3 : (1 - P) * (Pdot * P) * (1 - P) = 0 := by
      have hstep : (1 - P) * (Pdot * P) * (1 - P) = (1 - P) * Pdot * (P * (1 - P)) := by
        noncomm_ring
      rw [hstep]
      simp [hPQ]
    have h4 : (1 - P) * (P * Pdot) * (1 - P) = 0 := by
      have hstep : (1 - P) * (P * Pdot) * (1 - P) = ((1 - P) * P) * Pdot * (1 - P) := by
        noncomm_ring
      rw [hstep]
      simp [hQP]
    calc (1 - P) * (Pdot * P - P * Pdot) * (1 - P)
        = (1 - P) * (Pdot * P) * (1 - P) - (1 - P) * (P * Pdot) * (1 - P) := by
          noncomm_ring
      _ = 0 := by rw [h3, h4, sub_self]

/-- If both diagonal blocks of `A` and `Z` vanish relative to `P`, then `P * (A * Z - Z * A) *
(1 - P)` vanishes. -/
theorem offdiag_comm_sandwich (P A Z : Matrix (Fin n) (Fin n) ℂ)
    (hAPA : P * A * P = 0) (hQAQ : (1 - P) * A * (1 - P) = 0)
    (hPZP : P * Z * P = 0) (hQZQ : (1 - P) * Z * (1 - P) = 0) :
    P * (A * Z - Z * A) * (1 - P) = 0 := by
  have hone : P + (1 - P) = 1 := by abel
  have hPA : P * A = P * A * (1 - P) := by
    calc P * A = P * A * 1 := (mul_one _).symm
      _ = P * A * (P + (1 - P)) := by rw [hone]
      _ = P * A * P + P * A * (1 - P) := by rw [mul_add]
      _ = P * A * (1 - P) := by rw [hAPA, zero_add]
  have hPZ : P * Z = P * Z * (1 - P) := by
    calc P * Z = P * Z * 1 := (mul_one _).symm
      _ = P * Z * (P + (1 - P)) := by rw [hone]
      _ = P * Z * P + P * Z * (1 - P) := by rw [mul_add]
      _ = P * Z * (1 - P) := by rw [hPZP, zero_add]
  have hAZ : P * (A * Z) * (1 - P) = 0 := by
    rw [show P * (A * Z) * (1 - P) = P * A * Z * (1 - P) from by noncomm_ring]
    conv_lhs => rw [hPA]
    rw [show P * A * (1 - P) * Z * (1 - P)
          = P * A * ((1 - P) * Z * (1 - P)) from by noncomm_ring]
    rw [hQZQ, mul_zero]
  have hZA : P * (Z * A) * (1 - P) = 0 := by
    rw [show P * (Z * A) * (1 - P) = P * Z * A * (1 - P) from by noncomm_ring]
    conv_lhs => rw [hPZ]
    rw [show P * Z * (1 - P) * A * (1 - P)
          = P * Z * ((1 - P) * A * (1 - P)) from by noncomm_ring]
    rw [hQAQ, mul_zero]
  calc P * (A * Z - Z * A) * (1 - P)
      = P * (A * Z) * (1 - P) - P * (Z * A) * (1 - P) := by noncomm_ring
    _ = 0 := by rw [hAZ, hZA, sub_self]

/-- Under the stated nonzero parameter, off-diagonal derivative, and commutation hypotheses, the
two off-diagonal blocks of `[HτAconst, twiddle X]` equal `P * X * (1 - P)` and `-(1 - P) * X
* P`. See [JansenRuskaiSeiler2007]. -/
theorem twiddle_adiSandwich (D : BandData H) (τ : ℝ) (_hτ : τ ≠ 0)
    (Pdot : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (_hPdot_off : Pdot = Pdot * D.P + D.P * Pdot)
    (_hHcomm : H * D.P = D.P * H) :
    D.P * commutator (HτAconst τ H D.P Pdot) (D.twiddle X) * (1 - D.P)
        = D.P * X * (1 - D.P) ∧
      (1 - D.P) * commutator (HτAconst τ H D.P Pdot) (D.twiddle X) * D.P
        = -((1 - D.P) * X * D.P) := by
  set C : Matrix (Fin n) (Fin n) ℂ := Pdot * D.P - D.P * Pdot with hCdef
  have hCblk := Pdot_diag_blocks D.P Pdot D.P_proj.1
  have hZP : D.P * D.twiddle X * D.P = 0 := D.P_twiddle_P X
  have hZQ : (1 - D.P) * D.twiddle X * (1 - D.P) = 0 := D.Q_twiddle_Q X
  have hHA : HτAconst τ H D.P Pdot = H + (Complex.I / (τ : ℂ)) • C := by
    rw [HτAconst, hCdef]
  have hcomm_add : commutator (H + (Complex.I / (τ : ℂ)) • C) (D.twiddle X)
      = commutator H (D.twiddle X)
        + (Complex.I / (τ : ℂ)) • commutator C (D.twiddle X) := by
    rw [commutator, commutator, commutator, add_mul, mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    abel
  have hQAQ' : (1 - (1 - D.P)) * C * (1 - (1 - D.P)) = 0 := by
    simpa [sub_sub_cancel] using! hCblk.1
  have hPZP' : (1 - (1 - D.P)) * D.twiddle X * (1 - (1 - D.P)) = 0 := by
    simpa [sub_sub_cancel] using! hZP
  constructor
  · rw [hHA, hcomm_add]
    rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
      D.P_commutator_H_twiddle_Q X]
    have hz : D.P * commutator C (D.twiddle X) * (1 - D.P) = 0 :=
      offdiag_comm_sandwich D.P C (D.twiddle X) hCblk.1 hCblk.2 hZP hZQ
    rw [hz, smul_zero, add_zero]
  · rw [hHA, hcomm_add]
    rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
      D.Q_commutator_H_twiddle_P X]
    have hz : (1 - D.P) * commutator C (D.twiddle X) * D.P = 0 := by
      have h := offdiag_comm_sandwich (1 - D.P) C (D.twiddle X) hCblk.2 hQAQ' hZQ hPZP'
      simpa [commutator, sub_sub_cancel] using! h
    rw [hz, smul_zero, add_zero]

end BandData

end Qatlib.Papers.AdiabBounds06.MainResults
