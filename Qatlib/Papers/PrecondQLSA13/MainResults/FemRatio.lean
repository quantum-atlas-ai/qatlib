/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PrecondQLSA13.MainResults.Complexity.SourceComplexity
public import Qatlib.Papers.PrecondQLSA13.MainResults.ScatteringApplication.SourceScatteringApplication
public import Qatlib.Papers.PrecondQLSA13.MainResults.TildeUpgrade
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # FEM condition number and the unpreconditioned quantum advantage

Fixed arXiv:1301.2340v4, p. 4, last paragraph.  The paper notes that without
preconditioning the three-dimensional finite-element condition number scales
as `N^{2/3}` (frozen `femConditionNumber`/`fem_condition_three_dim`), so the
composed quantum cost carries an `N^{2/3}` factor while a classical solver
costs at least linearly in `N`; and that with the quantum SPAI
preconditioner the eigenvalues are bounded (frozen Eq. (12)), giving the
scalar asymptotic comparison in `TildeUpgrade`.

This module adds the missing quantitative composition on the unpreconditioned
side:

* `fem_totalCost_bound`: substituting `κ = N^{2/3}` into the composed cost
  and applying the sub-polynomial Suzuki upgrade with exponent `1/8` gives
  `totalCost d N^{2/3} N ε ≤ C(d,ε) · N^{3/4} · log N` in the regime where
  the Suzuki-log condition holds at the base `N = 2`;
* `fem_ratio_decays`: dividing by `N` and using `log N ≤ 8·N^{1/8}` yields
  the explicit decay `≤ 8·C(d,ε)·N^{-1/8}`, hence a ratio below any target
  `e > 0` beyond an explicit `N₀` — the paper's "scales better than its
  classical counterpart" as an honest asymptotic statement in the standard
  reading-cost model (`N ≤ classical cost`).

Boundary: the FEM condition-number law `N^{2/3}` itself is the frozen
prescribed scalar model (citing Brenner–Scott/Bank–Scott as in the paper);
no instance construction is formalized here.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PrecondQLSA13.MainResults.FemRatio

open Qatlib.Papers.PrecondQLSA13.MainResults.Complexity
open Qatlib.Papers.PrecondQLSA13.MainResults.ScatteringApplication
open Qatlib.Papers.PrecondQLSA13.MainResults.TildeUpgrade

/-- The regime hypothesis at the base `N = 2`: the Suzuki-log condition for
exponent `1/8`, which then propagates to every `N ≥ 2` by monotonicity. -/
theorem femLogGrows (d ε N : ℝ) (hd : 0 < d) (hε : 0 < ε) (hN : 2 ≤ N)
    (hbase : (2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2
      ≤ Real.log (6 * d ^ 2 * ((2 : ℝ) ^ ((2 / 3 : ℝ))) / ε ^ 2)) :
    (2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2
      ≤ Real.log (6 * d ^ 2 * N ^ ((2 / 3 : ℝ)) / ε ^ 2) := by
  have hm1 : ((2 : ℝ) ^ ((2 / 3 : ℝ))) ≤ N ^ ((2 / 3 : ℝ)) :=
    Real.rpow_le_rpow (by norm_num) hN (by norm_num)
  have h2pos : (0 : ℝ) < ((2 : ℝ) ^ ((2 / 3 : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hpos2 : (0 : ℝ) < 6 * d ^ 2 * ((2 : ℝ) ^ ((2 / 3 : ℝ))) / ε ^ 2 :=
    div_pos (mul_pos (by positivity) h2pos) (by positivity)
  have hNpos0 : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hN
  have hposN : (0 : ℝ) < 6 * d ^ 2 * N ^ ((2 / 3 : ℝ)) / ε ^ 2 :=
    div_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos hNpos0 _))
      (by positivity)
  have hinner : 6 * d ^ 2 * ((2 : ℝ) ^ ((2 / 3 : ℝ)))
      ≤ 6 * d ^ 2 * N ^ ((2 / 3 : ℝ)) :=
    mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ 6 * d ^ 2)
  have hm2 : 6 * d ^ 2 * ((2 : ℝ) ^ ((2 / 3 : ℝ))) / ε ^ 2
      ≤ 6 * d ^ 2 * N ^ ((2 / 3 : ℝ)) / ε ^ 2 := by
    rw [div_le_div_iff₀ (show (0 : ℝ) < ε ^ 2 by positivity)
      (show (0 : ℝ) < ε ^ 2 by positivity)]
    exact mul_le_mul_of_nonneg_right hinner (by positivity : (0 : ℝ) ≤ ε ^ 2)
  exact le_trans hbase (Real.log_le_log hpos2 hm2)

/-- Substituting the three-dimensional FEM condition number `N^{2/3}` into
the composed cost and upgrading the Suzuki factor at exponent `1/8`:
`totalCost ≤ C(d,ε) · N^{3/4} · log N` for every `N ≥ 2` in the base regime. -/
theorem fem_totalCost_bound (d N ε : ℝ) (hd : 0 < d) (hε : 0 < ε) (hN : 2 ≤ N)
    (hbase : (2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2
      ≤ Real.log (6 * d ^ 2 * ((2 : ℝ) ^ ((2 / 3 : ℝ))) / ε ^ 2)) :
    totalCost d (N ^ ((2 / 3 : ℝ))) N ε
      ≤ (72 * d ^ 7 / ε ^ 2 * ((6 * d ^ 2 / ε ^ 2) ^ ((1 / 8 : ℝ))))
        * (N ^ ((3 / 4 : ℝ))) * Real.log N := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hN
  have hκ : (0 : ℝ) < N ^ ((2 / 3 : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have hlog := femLogGrows d ε N hd hε hN hbase
  have h := totalCost_subpolylog d (N ^ ((2 / 3 : ℝ))) N ε ((1 / 8 : ℝ))
    hd hκ (by linarith) hε (by norm_num) hlog
  have hEq : 6 * d ^ 2 * N ^ ((2 / 3 : ℝ)) / ε ^ 2
      = (6 * d ^ 2 / ε ^ 2) * N ^ ((2 / 3 : ℝ)) := by
    field_simp
  have hsplit : (6 * d ^ 2 * N ^ ((2 / 3 : ℝ)) / ε ^ 2) ^ ((1 / 8 : ℝ))
      = (6 * d ^ 2 / ε ^ 2) ^ ((1 / 8 : ℝ)) * (N ^ ((2 / 3 : ℝ))) ^ ((1 / 8 : ℝ)) := by
    rw [hEq, Real.mul_rpow (by positivity : (0 : ℝ) ≤ 6 * d ^ 2 / ε ^ 2)
      (Real.rpow_nonneg hNpos.le _)]
  have hpow : (N ^ ((2 / 3 : ℝ))) ^ ((1 / 8 : ℝ)) = N ^ ((1 / 12 : ℝ)) := by
    rw [← Real.rpow_mul hNpos.le, show ((2 / 3 : ℝ) * (1 / 8 : ℝ)) = (1 / 12 : ℝ) by
      norm_num]
  have hcomb : N ^ ((2 / 3 : ℝ)) * N ^ ((1 / 12 : ℝ)) = N ^ ((3 / 4 : ℝ)) := by
    rw [← Real.rpow_add hNpos, show ((2 / 3 : ℝ) + (1 / 12 : ℝ)) = (3 / 4 : ℝ) by
      norm_num]
  rw [hsplit, hpow] at h
  calc totalCost d (N ^ ((2 / 3 : ℝ))) N ε
      ≤ 72 * d ^ 7 * N ^ ((2 / 3 : ℝ)) * Real.log N / ε ^ 2
          * ((6 * d ^ 2 / ε ^ 2) ^ ((1 / 8 : ℝ)) * N ^ ((1 / 12 : ℝ))) := h
    _ ≤ (72 * d ^ 7 / ε ^ 2 * ((6 * d ^ 2 / ε ^ 2) ^ ((1 / 8 : ℝ))))
        * (N ^ ((3 / 4 : ℝ))) * Real.log N := by
        refine le_of_eq ?_
        rw [← hcomb]
        field_simp

/-- The paper's "scales better" statement as an explicit decay: the
unpreconditioned three-dimensional FEM quantum cost divided by `N` is at
most `8·C(d,ε)·N^{-1/8}`, below any target `e > 0` beyond an explicit
threshold relative to the stipulated positive linear comparison
`cclassical * N`; no classical lower bound or operational speedup is derived. -/
theorem fem_ratio_decays (d ε e cclassical : ℝ) (hd : 0 < d) (hε : 0 < ε)
    (hcc : 0 < cclassical) (he : 0 < e)
    (hbase : (2 * Real.log 5 / ((1 / 8 : ℝ))) ^ 2
      ≤ Real.log (6 * d ^ 2 * ((2 : ℝ) ^ ((2 / 3 : ℝ))) / ε ^ 2)) :
    ∃ N₀ : ℝ, 1 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      totalCost d (N ^ ((2 / 3 : ℝ))) N ε / (cclassical * N) ≤ e := by
  set C := 72 * d ^ 7 / ε ^ 2 * ((6 * d ^ 2 / ε ^ 2) ^ ((1 / 8 : ℝ))) with hCdef
  have hC0 : (0 : ℝ) ≤ C := by
    rw [hCdef]
    positivity
  refine ⟨max 2 (max ((8 * C / (cclassical * e)) ^ 8 + 1) 2), by norm_num, ?_⟩
  intro N hN
  have hN2 : (2 : ℝ) ≤ N := le_trans (le_max_left _ _) hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hN2
  have hcost := fem_totalCost_bound d N ε hd hε hN2 hbase
  have hlog8 : Real.log N ≤ 8 * N ^ ((1 / 8 : ℝ)) := by
    have hsmall : (1 / 8 : ℝ) * Real.log N = Real.log (N ^ ((1 / 8 : ℝ))) :=
      (Real.log_rpow hNpos ((1 / 8 : ℝ))).symm
    have h2 : Real.log (N ^ ((1 / 8 : ℝ))) ≤ N ^ ((1 / 8 : ℝ)) - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hNpos _)
    linarith
  have hPpos : (0 : ℝ) < N ^ ((1 / 8 : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have hccN : (0 : ℝ) < cclassical * N := mul_pos hcc hNpos
  have hce : (0 : ℝ) < cclassical * e := mul_pos hcc he
  have htge : (0 : ℝ) ≤ 8 * C / (cclassical * e) :=
    div_nonneg (mul_nonneg (by norm_num) hC0) hce.le
  have hNbig : ((8 * C / (cclassical * e)) ^ 8 + 1) ≤ N := by
    have h1 : ((8 * C / (cclassical * e)) ^ 8 + 1)
        ≤ max ((8 * C / (cclassical * e)) ^ 8 + 1) 2 := le_max_left _ _
    have h2 : (max ((8 * C / (cclassical * e)) ^ 8 + 1) 2)
        ≤ max 2 (max ((8 * C / (cclassical * e)) ^ 8 + 1) 2) := le_max_right _ _
    exact le_trans (le_trans h1 h2) hN
  have hPbig : 8 * C / (cclassical * e) ≤ N ^ ((1 / 8 : ℝ)) := by
    set t := 8 * C / (cclassical * e) with htdef
    have ht8 : t ^ (8 : ℕ) ≤ N := by
      have h1 : t ^ (8 : ℕ) ≤ t ^ (8 : ℕ) + 1 := by
        have : (0 : ℝ) ≤ t ^ (8 : ℕ) := pow_nonneg htge 8
        linarith
      exact le_trans h1 hNbig
    have hnat : t ^ (8 : ℕ) = t ^ ((8 : ℝ)) := (Real.rpow_natCast t 8).symm
    have hrew : (t ^ (8 : ℕ)) ^ ((1 / 8 : ℝ)) = t := by
      rw [hnat, ← Real.rpow_mul htge,
        show ((8 : ℝ) * (1 / 8 : ℝ)) = 1 by norm_num, Real.rpow_one]
    have hmono : (t ^ (8 : ℕ)) ^ ((1 / 8 : ℝ)) ≤ N ^ ((1 / 8 : ℝ)) :=
      Real.rpow_le_rpow (pow_nonneg htge 8) ht8 (by norm_num)
    rw [hrew] at hmono
    exact hmono
  have h74 : N ^ ((3 / 4 : ℝ)) * N ^ ((1 / 8 : ℝ)) = N ^ ((7 / 8 : ℝ)) := by
    rw [← Real.rpow_add hNpos, show ((3 / 4 : ℝ) + (1 / 8 : ℝ)) = (7 / 8 : ℝ) by
      norm_num]
  have hN1 : N ^ ((7 / 8 : ℝ)) * N ^ ((1 / 8 : ℝ)) = N := by
    rw [← Real.rpow_add hNpos, show ((7 / 8 : ℝ) + (1 / 8 : ℝ)) = 1 by norm_num,
      Real.rpow_one]
  have hlast : 8 * C * N ^ ((7 / 8 : ℝ)) ≤ e * (cclassical * N) := by
    have hkey : 8 * C ≤ (cclassical * e) * N ^ ((1 / 8 : ℝ)) :=
      ((div_le_iff₀ hce).mp hPbig).trans_eq (by ring)
    have hA : (0 : ℝ) ≤ N ^ ((7 / 8 : ℝ)) := Real.rpow_nonneg hNpos.le _
    nlinarith [hkey, hN1, hA]
  rw [div_le_iff₀ hccN]
  calc totalCost d (N ^ ((2 / 3 : ℝ))) N ε
      ≤ (72 * d ^ 7 / ε ^ 2 * ((6 * d ^ 2 / ε ^ 2) ^ ((1 / 8 : ℝ))))
        * (N ^ ((3 / 4 : ℝ))) * Real.log N := hcost
    _ = C * (N ^ ((3 / 4 : ℝ))) * Real.log N := rfl
    _ ≤ C * (N ^ ((3 / 4 : ℝ))) * (8 * N ^ ((1 / 8 : ℝ))) :=
          mul_le_mul_of_nonneg_left hlog8
            (mul_nonneg hC0 (Real.rpow_nonneg hNpos.le _))
    _ = 8 * C * (N ^ ((3 / 4 : ℝ)) * N ^ ((1 / 8 : ℝ))) := by ring
    _ = 8 * C * N ^ ((7 / 8 : ℝ)) := by rw [h74]
    _ ≤ e * (cclassical * N) := hlast

end Qatlib.Papers.PrecondQLSA13.MainResults.FemRatio
