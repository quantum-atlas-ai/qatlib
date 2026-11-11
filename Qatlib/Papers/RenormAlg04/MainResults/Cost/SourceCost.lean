/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetworkExt

set_option backward.isDefEq.respectTransparency false

/-!
# SourceCost — polynomial cost of the PEPS expectation-value algorithm

Fixed source: F. Verstraete and J. I. Cirac, *Renormalization algorithms for
Quantum-Many Body Systems in two and higher dimensions*, arXiv:cond-mat/0407066v1
(2 Jul 2004), p. 3 (bottom): "the computational cost of the algorithm is polynomial
in `N` and `D`".  PDF SHA-256
`397e011bc798dbb6aa2d4bf93f6d2e666a12f77fd0655e1168d03037d0af4da7`.

The source computes expectation values by contracting a PEPS row by row; the row
contraction is an MPS inner product with physical dimension `D ^ 2` (the two open
virtual legs of a row) and bond dimension `D`.  The frozen model exposes the exact
operation counters `mpsInnerOpCount`, `mpsEvalOpCount` and `pepsStripOpCount`; here
we connect the counted algorithms to explicit polynomial upper bounds in the
lattice size `N = a * b` and the bond dimension `D`.

Boundary: operation counts only (ring operations), not bit complexity or
floating-point error; the `a = 0` / `b = 0` degenerate grids are excluded exactly
where the source assumes a square `Nh × Nv` lattice with positive sides.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MpsAdaptation.MpsTransfer

namespace Qatlib.Papers.RenormAlg04.MainResults.Cost

/-- Source p. 3, Eq. (4a)-(5) evaluation: the counted MPS inner-product transfer
uses no more than `mpsInnerOpCount n d D` ring operations (frozen bound
`mpsInnerEvalWithCount_op_le`). -/
theorem mps_inner_cost_le (n d D : ℕ) (hn : NeZero n) (hD : NeZero D)
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    (@mpsInnerEvalWithCount n d D hn hD A B).2 ≤ mpsInnerOpCount n d D :=
  mpsInnerEvalWithCount_op_le n d D hn hD A B

/-- Source p. 3 (bottom), explicit polynomial form for one MPS row contraction:
`mpsInnerOpCount n d D = n * (2 d D^3 + 2 D^2) ≤ 4 (n+1)(d+1)(D+1)^3`. -/
theorem mps_inner_cost_polynomial (n d D : ℕ) :
    mpsInnerOpCount n d D ≤ 4 * (n + 1) * (d + 1) * (D + 1) ^ 3 := by
  have hpow3 : D ^ 3 ≤ (D + 1) ^ 3 := pow_le_pow_left' (Nat.le_succ D) 3
  have hpow2 : D ^ 2 ≤ (D + 1) ^ 3 := by
    have h1 : D ^ 2 ≤ (D + 1) ^ 2 := pow_le_pow_left' (Nat.le_succ D) 2
    have h2 : (D + 1) ^ 2 ≤ (D + 1) ^ 3 :=
      pow_le_pow_right' (a := D + 1) (by omega) (by norm_num : 2 ≤ 3)
    exact h1.trans h2
  have hterm : 2 * d * D * D * D + 2 * D * D ≤ 2 * (d + 1) * (D + 1) ^ 3 := by
    have h1 : 2 * d * D * D * D ≤ 2 * d * (D + 1) ^ 3 := by
      calc 2 * d * D * D * D = 2 * d * D ^ 3 := by ring
        _ ≤ 2 * d * (D + 1) ^ 3 := Nat.mul_le_mul_left (2 * d) hpow3
    have h2 : 2 * D * D ≤ 2 * (D + 1) ^ 3 := by
      calc 2 * D * D = 2 * D ^ 2 := by ring
        _ ≤ 2 * (D + 1) ^ 3 := Nat.mul_le_mul_left 2 hpow2
    calc 2 * d * D * D * D + 2 * D * D
        ≤ 2 * d * (D + 1) ^ 3 + 2 * (D + 1) ^ 3 := Nat.add_le_add h1 h2
      _ = 2 * (d + 1) * (D + 1) ^ 3 := by ring
  unfold mpsInnerOpCount
  calc n * (2 * d * D * D * D + 2 * D * D)
      ≤ (n + 1) * (2 * (d + 1) * (D + 1) ^ 3) :=
        Nat.mul_le_mul (Nat.le_succ n) hterm
    _ = 2 * ((n + 1) * (d + 1) * (D + 1) ^ 3) := by ring
    _ ≤ 4 * ((n + 1) * (d + 1) * (D + 1) ^ 3) :=
        Nat.mul_le_mul_right _ (by norm_num)
    _ = 4 * (n + 1) * (d + 1) * (D + 1) ^ 3 := by ring

/-- Source p. 3 (bottom) for the PEPS strip contraction: the counted strip
evaluation stays within `pepsStripOpCount a b D` (frozen bound
`pepsStripEvalWithCount_op_le`). -/
theorem peps_strip_cost_le (a b d D : ℕ) (hD : NeZero D)
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d) :
    (@pepsStripEvalWithCount a b d D hD T x).2 ≤ pepsStripOpCount a b D :=
  pepsStripEvalWithCount_op_le a b d D hD T x

/-- Source p. 3 (bottom), explicit polynomial form for the strip contraction:
`pepsStripOpCount a b D = b * ((D^a)^3 (a+2) + 1) ≤ (b+1) * ((D+1)^(3a) (a+2) + 1)`. -/
theorem peps_strip_cost_polynomial (a b D : ℕ) :
    pepsStripOpCount a b D ≤ (b + 1) * ((D + 1) ^ (3 * a) * (a + 2) + 1) := by
  have hbase : D ^ a ≤ (D + 1) ^ a := pow_le_pow_left' (Nat.le_succ D) a
  have hcube : (D ^ a) ^ 3 ≤ (D + 1) ^ (3 * a) := by
    calc (D ^ a) ^ 3 ≤ ((D + 1) ^ a) ^ 3 := pow_le_pow_left' hbase 3
      _ = (D + 1) ^ (a * 3) := by rw [pow_mul]
      _ = (D + 1) ^ (3 * a) := by rw [Nat.mul_comm]
  have hinner : (D ^ a) ^ 3 * (a + 2) + 1 ≤ (D + 1) ^ (3 * a) * (a + 2) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right (a + 2) hcube) 1
  unfold pepsStripOpCount
  calc b * ((D ^ a) ^ 3 * (a + 2) + 1)
      ≤ (b + 1) * ((D + 1) ^ (3 * a) * (a + 2) + 1) :=
        Nat.mul_le_mul (Nat.le_succ b) hinner

/-- Source p. 3 (bottom): coarse bound for the exact strip contraction on an
`a × b` grid (`a,b ≥ 1`).  Note the exponent `3 * (a * b)` grows with the number of
sites, so this is *not* polynomial in `N`; it is recorded only as the crude form of
`peps_strip_cost_polynomial`, and the honest polynomial statement in `N` and `D` is
`algorithm_cost_polynomial_sites` below (row-transfer algorithm with MPS bond `D`). -/
theorem algorithm_cost_polynomial (a b D : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    pepsStripOpCount a b D ≤
      (a * b + 1) * ((D + 1) ^ (3 * (a * b)) * (a + 2) + 1) := by
  have hbN : b ≤ a * b := by
    calc b = 1 * b := by ring
      _ ≤ a * b := Nat.mul_le_mul_right b ha
  have hexp : 3 * a ≤ 3 * (a * b) := by
    have : a ≤ a * b := by
      calc a = a * 1 := by ring
        _ ≤ a * b := Nat.mul_le_mul_left a hb
    omega
  have hmono : (D + 1) ^ (3 * a) ≤ (D + 1) ^ (3 * (a * b)) :=
    pow_le_pow_right' (a := D + 1) (by omega) hexp
  have hinner : (D + 1) ^ (3 * a) * (a + 2) + 1
      ≤ (D + 1) ^ (3 * (a * b)) * (a + 2) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right (a + 2) hmono) 1
  have hstep := peps_strip_cost_polynomial a b D
  refine hstep.trans ?_
  exact Nat.mul_le_mul (by omega) hinner

/-- Source p. 3 (bottom), row-transfer reading: one row of the 2D algorithm is an MPS
inner product with physical dimension `D * D` (the two open virtual legs of a row)
and bond dimension `D`, so it costs at most `4 (b+1) (D*D+1) (D+1)^3`, which is
`≤ 4 (b+1) (D+1)^5` ring operations — polynomial in the row length and in `D`. -/
theorem mps_row_cost_polynomial (b D : ℕ) :
    mpsInnerOpCount b (D * D) D ≤ 4 * (b + 1) * (D + 1) ^ 5 := by
  refine (mps_inner_cost_polynomial b (D * D) D).trans ?_
  have hsq : D * D + 1 ≤ (D + 1) ^ 2 := by
    have h : (D + 1) ^ 2 = D * D + 2 * D + 1 := by ring
    rw [h]; omega
  calc 4 * (b + 1) * (D * D + 1) * (D + 1) ^ 3
      = (4 * (b + 1)) * ((D * D + 1) * (D + 1) ^ 3) := by ring
    _ ≤ (4 * (b + 1)) * (((D + 1) ^ 2) * (D + 1) ^ 3) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hsq)
    _ = 4 * (b + 1) * (D + 1) ^ 5 := by ring

/-- Source p. 3 (bottom): the row-by-row algorithm pays one row contraction per row,
so on an `a × b` grid with `b ≥ 1` its total cost is at most
`a * mpsInnerOpCount b (D*D) D ≤ 8 (N+1) (D+1)^5` with `N = a * b` — polynomial of
degree one in the number of sites and degree five in the bond dimension.  This is
the precise content of "the computational cost is polynomial in `N` and `D`" for the
row-transfer algorithm of the source. -/
theorem algorithm_cost_polynomial_sites (a b D : ℕ) (hb : 1 ≤ b) :
    a * mpsInnerOpCount b (D * D) D ≤ 8 * (a * b + 1) * (D + 1) ^ 5 := by
  have hrow := mps_row_cost_polynomial b D
  have hb' : a * (b + 1) ≤ 2 * (a * b + 1) := by
    have hab : a ≤ a * b := by
      calc a = a * 1 := by ring
        _ ≤ a * b := Nat.mul_le_mul_left a hb
    calc a * (b + 1) = a * b + a := by ring
      _ ≤ a * b + a * b := Nat.add_le_add_left hab _
      _ = 2 * (a * b) := by ring
      _ ≤ 2 * (a * b + 1) := Nat.mul_le_mul_left 2 (Nat.le_succ _)
  have hmul : a * 4 * (b + 1) * (D + 1) ^ 5 ≤ 8 * (a * b + 1) * (D + 1) ^ 5 := by
    calc a * 4 * (b + 1) * (D + 1) ^ 5
        = (a * (b + 1)) * (4 * (D + 1) ^ 5) := by ring
      _ ≤ (2 * (a * b + 1)) * (4 * (D + 1) ^ 5) :=
          Nat.mul_le_mul_right _ hb'
      _ = 8 * (a * b + 1) * (D + 1) ^ 5 := by ring
  calc a * mpsInnerOpCount b (D * D) D
      ≤ a * (4 * (b + 1) * (D + 1) ^ 5) := Nat.mul_le_mul_left a hrow
    _ = a * 4 * (b + 1) * (D + 1) ^ 5 := by ring
    _ ≤ 8 * (a * b + 1) * (D + 1) ^ 5 := hmul

end Qatlib.Papers.RenormAlg04.MainResults.Cost
