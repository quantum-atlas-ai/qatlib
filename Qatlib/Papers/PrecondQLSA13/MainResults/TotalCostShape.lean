/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Plain QLSA cost shape and FEM condition scaling

Fixed source arXiv:1301.2340v4 (Clader, Jacobs, Sprouse, *Preconditioned
quantum linear system algorithm*).  The paper's combined algorithm runs in
`Õ(d^7 κ log N / ε^2)`; without preconditioning, finite element condition
numbers scale as `N^(2/n)`, while the SPAI-preconditioned spectrum is
banded, making the condition number `N`-independent.

Distinct from `TildeUpgrade` (which upgrades the frozen library's composed
cost with the Suzuki factor), this module proves the *plain-shape* scalar
algebra: the cost shape `d^7 κ log N / ε^2` under a bounded condition number
with the honest `K log N ≤ K N` linear comparison — no speedup claim — the
unpreconditioned 3-D FEM bound `N^(2/3) log N ≤ 3 N`, the eigenvalue-band
condition bound `λmax/λmin ≤ hmax/hmin`, and the concrete polylog-versus-
linear threshold `K log N ≤ N` for `N ≥ 4K^2`.  No SPAI construction,
Hamiltonian simulation, classical lower bound or executable circuit is
modeled here.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PrecondQLSA13.MainResults.TotalCostShape

/-- The plain total-cost shape `d^7 κ log N / ε^2` of the combined
preconditioned QLSA, with the tilde of `Õ` stripped. -/
def qlsaCost (d κ N ε : ℝ) : ℝ := d ^ 7 * κ * Real.log N / ε ^ 2

/-- The plain cost shape is nonnegative for nonnegative parameters,
`1 ≤ N` and `ε > 0`. -/
theorem qlsaCostNonneg (d κ N ε : ℝ) (hd : 0 ≤ d) (hκ : 0 ≤ κ) (hN : 1 ≤ N)
    (_hε : 0 < ε) : 0 ≤ qlsaCost d κ N ε := by
  have : 0 ≤ Real.log N := Real.log_nonneg hN
  unfold qlsaCost
  positivity

/-- For `1 ≤ N` the natural logarithm is at most `N`; this is the honest
`K log N ≤ K N` comparison, bounding the polylogarithmic quantum cost by a
linear-in-`N` expression without establishing any speedup by itself. -/
theorem logLeSelf (N : ℝ) (hN : 1 ≤ N) : Real.log N ≤ N :=
  (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)

/-- Monotone composition: if the condition number is bounded by `K` (the
effect of Eq. (12) of the source), the plain cost is at most
`d^7 K N / ε^2` — an at-most-linear envelope in `N`, not a speedup. -/
theorem boundedKappa (d κ K N ε : ℝ) (hd : 0 ≤ d) (hK : 0 ≤ K) (hκ : κ ≤ K)
    (hN : 1 ≤ N) (_hε : 0 < ε) :
    qlsaCost d κ N ε ≤ d ^ 7 * K * N / ε ^ 2 := by
  have hdl : 0 ≤ d ^ 7 := pow_nonneg hd 7
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hκ hdl) (logLeSelf N hN)
    (Real.log_nonneg hN) (mul_nonneg hdl hK)

/-- The unpreconditioned 3-D FEM condition scaling: with `κ = N^(2/3)` and
`1 ≤ N`, the plain cost is at most `3 d^7 N / ε^2` — the quantum cost stays
at most linear in `N` even without preconditioning. -/
theorem fem3dUnprecond (d N ε : ℝ) (hd : 0 ≤ d) (hN : 1 ≤ N) (_hε : 0 < ε) :
    qlsaCost d (N ^ (2 / 3 : ℝ)) N ε ≤ 3 * d ^ 7 * N / ε ^ 2 := by
  have hNp : 0 < N := by linarith
  have hlog : Real.log N ≤ N ^ (1 / 3 : ℝ) / (1 / 3 : ℝ) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have hrw : N ^ (1 / 3 : ℝ) / (1 / 3 : ℝ) = 3 * N ^ (1 / 3 : ℝ) := by
    field_simp
  rw [hrw] at hlog
  have hκlog : N ^ (2 / 3 : ℝ) * Real.log N ≤ 3 * N := by
    calc N ^ (2 / 3 : ℝ) * Real.log N
        ≤ N ^ (2 / 3 : ℝ) * (3 * N ^ (1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg (by linarith) _)
      _ = 3 * (N ^ (2 / 3 : ℝ) * N ^ (1 / 3 : ℝ)) := by ring
      _ = 3 * N ^ ((2 / 3 : ℝ) + (1 / 3 : ℝ)) := by rw [← Real.rpow_add hNp]
      _ = 3 * N ^ (1 : ℝ) := by norm_num
      _ = 3 * N := by rw [Real.rpow_one]
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
  calc d ^ 7 * N ^ (2 / 3 : ℝ) * Real.log N
      = d ^ 7 * (N ^ (2 / 3 : ℝ) * Real.log N) := by ring
    _ ≤ d ^ 7 * (3 * N) := mul_le_mul_of_nonneg_left hκlog (by positivity)
    _ = 3 * d ^ 7 * N := by ring

/-- Eigenvalue-band condition bound (Eq. (12) style): a spectrum contained in
`[hmin, hmax]` with `0 < hmin ≤ λmin ≤ λmax ≤ hmax` bounds the spectral
condition ratio `λmax / λmin` by `hmax / hmin` — the SPAI-preconditioned
spectrum is assumed to lie in the supplied band. If its endpoints are
`N`-independent then so is this scalar bound; no SPAI construction is derived. -/
theorem eigenBandKappa (lmin lmax hmin hmax : ℝ) (hminp : 0 < hmin)
    (hhmax : 0 ≤ hmax) (hLmin : hmin ≤ lmin) (hLmax : lmax ≤ hmax)
    (hLpos : 0 < lmin) :
    lmax / lmin ≤ hmax / hmin := by
  rw [div_le_div_iff₀ hLpos hminp]
  nlinarith

/-- Concrete polylog-versus-linear threshold: for `0 ≤ K` and `4K^2 ≤ N`
one has `K log N ≤ N`.  With a preconditioned condition number bounded by a
constant `K`, the `N`-dependence of the bounded-`κ` cost is therefore below
the linear envelope from `N ≥ 4K^2` on; compare `TildeUpgrade` for the
asymptotic ratio statement. -/
theorem polylogLe (K N : ℝ) (hK : 0 ≤ K) (hN : 4 * K ^ 2 ≤ N) :
    K * Real.log N ≤ N := by
  have hNn : 0 ≤ N := by nlinarith
  have hlog : Real.log N ≤ N ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
    Real.log_le_rpow_div hNn (by norm_num)
  have hrw : N ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) = 2 * Real.sqrt N := by
    rw [← Real.sqrt_eq_rpow]
    field_simp
  rw [hrw] at hlog
  have hstep : K * (2 * Real.sqrt N) ≤ N := by
    have hsn : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (Real.sqrt N - 2 * K), Real.sq_sqrt hNn]
  calc K * Real.log N ≤ K * (2 * Real.sqrt N) :=
        mul_le_mul_of_nonneg_left hlog hK
    _ ≤ N := hstep

end Qatlib.Papers.PrecondQLSA13.MainResults.TotalCostShape
