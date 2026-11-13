/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem7Stat
import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem7Aux2

/-!
# Terminal block mass in the V2 Taylor system

`theorem7V2` proves `Theorem7V2` by comparing history mass with the repeated terminal block.
Under the accuracy and trajectory-growth assumptions, each terminal block has norm at least the
full history-state norm divided by `sqrt (p + 77*m*g²)`. See [BerryEtAl2017ODE] for the paper's
setting.

## Main statements

* `theorem7V2`: Under the hypotheses of `Theorem7V2`, every terminal block has norm at least
  `‖stateVector x‖ / sqrt (p + 77*m*g²)`.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BlockEncoding.Postselection

set_option autoImplicit false
namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

/-- Under the hypotheses of `Theorem7V2`, every terminal block has norm at least `‖stateVector
x‖ / sqrt (p + 77*m*g²)`. See [BerryEtAl2017ODE]. -/
theorem theorem7V2 : Theorem7V2 := by
  classical
  intro N _ _ m k p A V D h g x_in b x hm hk hp hh hg hd hA hV1 hV2 hre hM hq hacc hdecay hx
  let q := ‖stateVector (taylorODESolution A b x_in ((m : ℝ)*h))‖
  let Y := ‖stateVector (taylorBlock x (taylorTimeLabel m k p m (le_refl m)))‖
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have herr := taylorV2_error_of_accuracy m k p A V D h x_in b x hm hk hp hh
    hd hA hV1 hV2 hre hM hq hacc hx
  have hbase (i : ℕ) (hi : i ≤ m) :
      ‖stateVector (taylorNatBlock x (i*(k+1)))‖ ≤ (g+(i : ℝ)/(25*m))*q := by
    change ‖stateVector (taylorNatBlock x (taylorTimeLabel m k p i hi).val)‖ ≤ _
    rw [taylorNatBlock_eq x (taylorTimeLabel m k p i hi)]
    have hiR : (i : ℝ) ≤ m := by exact_mod_cast hi
    have ht : (i : ℝ)*h ≤ (m : ℝ)*h := mul_le_mul_of_nonneg_right hiR hh.le
    have hnorm := hdecay ((i : ℝ)*h) (by positivity) ht
    have herror := herr i hi
    have htri := norm_le_norm_add_norm_sub
      (stateVector (taylorODESolution A b x_in ((i : ℝ)*h)))
      (stateVector (taylorBlock x (taylorTimeLabel m k p i hi)))
    dsimp [q] at ⊢
    nlinarith
  have hhist := taylorV2_history_mass_le m k p (h • A) h g q x_in b x hm (by omega)
    hg (by exact hq.le) hx hM hbase
  have hmass : ‖stateVector x‖^2 ≤ ((p : ℝ)+1)*Y^2+70*m*g^2*q^2 := by
    rw [taylorV2_norm_partition]
    have hpad : (∑ j ∈ Finset.range (p+1),
        ‖stateVector (taylorNatBlock x (m*(k+1)+j))‖^2) = ((p : ℝ)+1)*Y^2 := by
      have he (j : ℕ) (hj : j ∈ Finset.range (p+1)) :
          ‖stateVector (taylorNatBlock x (m*(k+1)+j))‖^2 = Y^2 := by
        rw [taylorNatBlock_pad m k p (h • A) h x_in b x hx j
          (by have := Finset.mem_range.mp hj; omega)]
      rw [Finset.sum_congr rfl he]
      simp
    rw [hpad]
    linarith
  have hfinal : (24/25 : ℝ)*q ≤ Y := by
    have he := herr m (le_refl m)
    have hdiv : (m : ℝ)/(25*m) = 1/25 := by field_simp
    rw [hdiv] at he
    have htri := norm_le_norm_add_norm_sub
      (stateVector (taylorBlock x (taylorTimeLabel m k p m (le_refl m))))
      (stateVector (taylorODESolution A b x_in ((m : ℝ)*h)))
    rw [norm_sub_rev] at htri
    dsimp [q, Y] at ⊢
    linarith
  have hbound := taylorV2_mass_arithmetic m p g q ‖stateVector x‖ Y hm hg hq
    (norm_nonneg _) (norm_nonneg _) hfinal hmass
  intro j hj
  have hcopy : taylorBlock x (taylorFinalLabel m k p j hj) =
      taylorBlock x (taylorTimeLabel m k p m (le_refl m)) := by
    exact (taylorNatBlock_eq x (taylorFinalLabel m k p j hj)).symm.trans
      (taylorNatBlock_pad m k p (h • A) h x_in b x hx j hj)
  rw [hcopy]
  exact hbound

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
