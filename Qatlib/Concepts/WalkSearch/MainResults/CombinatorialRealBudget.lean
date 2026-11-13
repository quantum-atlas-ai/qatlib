/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.CombinatorialAllocatedCost
import Qatlib.Concepts.WalkSearch.MainResults.CombinatorialTargets
import Qatlib.Concepts.WalkSearch.MainResults.IntegerBounds

/-!
# Real bounds for combinatorial query budgets

This module converts integer search reservations into explicit real power bounds, controlling
logarithms, square roots, and rounding. `sourceCombinatorialBudget_real_bound` combines the
component estimates into a capability factor and a logarithmic factor multiplying
`sourceFourTermBudget`. For background on quantum search and amplitude amplification, see
[BrassardEtAl2002].

## Main statements

* `source_log_polynomial_bound`: For `1 ≤ n`, if `x ≤ 2^a * n^p` and `2 ≤ a + p`, then `Nat.log
  2 x + 2` is at most `(a + p) * (Nat.log 2 n + 2)`.
* `sourceCombinatorialBudget_real_bound`: Under the stated exponent assumptions and with `1 ≤
  dLo`, the total integer budget at the prescribed rounded parameters is at most `2^24 *
  sourceCapabilityFeeFactor family ets * (Nat.log 2 n + 2)^4` times `sourceFourTermBudget n ε δ
  ε'`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.Primitives

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical

/-- For `1 ≤ n`, if `x ≤ 2^a * n^p` and `2 ≤ a + p`, then `Nat.log 2 x + 2` is at most `(a + p)
* (Nat.log 2 n + 2)`. -/
theorem source_log_polynomial_bound (n x a p : ℕ) (_hn : 1 ≤ n)
    (hap : 2 ≤ a+p) (hx : x ≤ 2^a*n^p) :
    Nat.log 2 x+2 ≤ (a+p)*(Nat.log 2 n+2) := by
  have hn2 : n ≤ 2^(Nat.log 2 n+1) := (Nat.lt_pow_succ_log_self (by norm_num) n).le
  have hb : x ≤ 2^(a+p*(Nat.log 2 n+1)) := by
    apply hx.trans
    rw [Nat.pow_add, show p*(Nat.log 2 n+1)=(Nat.log 2 n+1)*p by ring, Nat.pow_mul]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn2 p)
  have hl := Nat.log_mono_right (b:=2) hb
  rw [Nat.log_pow (by norm_num : 1 < 2)] at hl
  nlinarith [Nat.zero_le (a*Nat.log 2 n)]

/-- For positive `n` and nonnegative `C`, the bound `(x : ℝ) ≤ C^2 * n^e` implies `(Nat.sqrt x :
ℝ) ≤ C * n^(e / 2)`. -/
theorem source_sqrt_rpow_bound (n x : ℕ) (e C : ℝ) (hn : 0 < n) (hC : 0 ≤ C)
    (hx : (x : ℝ) ≤ C^2*(n : ℝ)^e) :
    (Nat.sqrt x : ℝ) ≤ C*(n : ℝ)^(e/2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (Nat.sqrt x : ℝ)^2 ≤ x := by exact_mod_cast Nat.sqrt_le' x
  have he : ((n : ℝ)^(e/2))^2 = (n : ℝ)^e := by
    rw [← Real.rpow_two, ← Real.rpow_mul hnR.le]
    congr 1
    ring
  have hp : (C*(n : ℝ)^(e/2))^2 = C^2*(n : ℝ)^e := by rw [mul_pow, he]
  have hc : 0 ≤ C*(n : ℝ)^(e/2) := by positivity
  rw [← hp] at hx
  exact (sq_le_sq₀ (by positivity) hc).mp (hs.trans hx)

/-- For `1 ≤ n` and `1 ≤ κ` bounding the search fee factor, `n + neighborhoodFee n sgs` is at
most `20 * κ * (Nat.log 2 n + 2) * n`. -/
theorem source_neighborhood_real_bound (n : ℕ) (sgs : SGSExecution) (κ : ℕ)
    (hn : 1 ≤ n) (hκ : 1 ≤ κ) (hsgs : sgs.κ ≤ κ) :
    (n+neighborhoodFee n sgs : ℕ) ≤
      (20 : ℝ)*(κ : ℝ)*(Nat.log 2 n+2 : ℕ)*(n : ℝ) := by
  have hlog := source_log_polynomial_bound n (n*n+1) 1 2 hn (by norm_num) (by nlinarith)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hκR : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hs : (sgs.κ : ℝ) ≤ κ := by exact_mod_cast hsgs
  have hl : (Nat.log 2 (n*n+1)+2 : ℕ) ≤ (3 : ℝ)*(Nat.log 2 n+2 : ℕ) := by exact_mod_cast hlog
  have hL : (2 : ℝ) ≤ (Nat.log 2 n+2 : ℕ) := by exact_mod_cast (Nat.le_add_left 2 (Nat.log 2 n))
  have hn1 : (n+1 : ℕ) ≤ (2 : ℝ)*(n : ℝ) := by push_cast; linarith
  have hf := mul_le_mul (mul_le_mul hs hl (by positivity) (by positivity)) hn1
    (by positivity) (by positivity)
  have hkn : (n : ℝ) ≤ (κ : ℝ)*(Nat.log 2 n+2 : ℕ)*(n : ℝ) := by
    have hKL : (1 : ℝ) ≤ (κ : ℝ)*(Nat.log 2 n+2 : ℕ) := by nlinarith
    nlinarith
  unfold neighborhoodFee
  push_cast at hf hkn ⊢
  nlinarith [hf]

/-- Under the stated nonnegativity and fee assumptions, the prescribed preparation budget is at
most `160 * κ * (Nat.log 2 n + 2)^2 * n^(1 + ε)`. -/
theorem source_preparation_budget_real_bound (n : ℕ) (ε : ℝ) (sgs : SGSExecution) (κ : ℕ)
    (hn : 1≤n) (hε : 0≤ε) (hκ : 1≤κ) (hsgs : sgs.κ≤κ) :
    ((Nat.ceil (4*(n:ℝ)^ε*(Nat.log 2 n+1)))*(n+neighborhoodFee n sgs):ℕ) ≤
      (160:ℝ)*(κ:ℝ)*(Nat.log 2 n+2:ℕ)^2*(n:ℝ)^(1+ε) := by
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hpow : (1:ℝ)≤(n:ℝ)^ε := Real.one_le_rpow hnR hε
  have hlog : (1:ℝ)≤(Nat.log 2 n+1:ℕ) := by exact_mod_cast (Nat.le_add_left 1 (Nat.log 2 n))
  have hk := ceil_le_twice_of_one_le (4*(n:ℝ)^ε*(Nat.log 2 n+1)) (by nlinarith)
  have hk' : (Nat.ceil (4*(n:ℝ)^ε*(Nat.log 2 n+1)):ℝ) ≤ 8*(n:ℝ)^ε*(Nat.log 2 n+2:ℕ) := by
    push_cast at hk ⊢
    nlinarith [Real.rpow_nonneg hn0.le ε]
  have hf := source_neighborhood_real_bound n sgs κ hn hκ hsgs
  have hh := mul_le_mul hk' hf (by positivity) (by positivity)
  have he : (8*(n:ℝ)^ε*(Nat.log 2 n+2:ℕ))*(20*(κ:ℝ)*(Nat.log 2 n+2:ℕ)*(n:ℝ)) =
      (160:ℝ)*(κ:ℝ)*(Nat.log 2 n+2:ℕ)^2*(n:ℝ)^(1+ε) := by
    rw [Real.rpow_add hn0,Real.rpow_one]
    ring
  simpa only [Nat.cast_mul,he] using! hh

/-- With positive rounded low degree threshold and the stated fee bounds, the corrected
classification budget is at most `548 * κ * (Nat.log 2 n + 2)^2 * n^(1 + δ + ε')`. -/
theorem source_classification_budget_real_bound (n : ℕ) (δ ε' : ℝ) (sgs : SGSExecution) (κ : ℕ)
    (hn : 1≤n) (hδ : 0≤δ) (hε' : 0≤ε') (hκ : 1≤κ) (hsgs : sgs.κ≤κ)
    (hdLo : 1≤Nat.floor ((n:ℝ)^(1-δ)/10)) :
    (classifyBudgetCorrected n (Nat.floor ((n:ℝ)^(1-δ)/10)) (Nat.ceil ((n:ℝ)^(1-ε')))
      (64*(Nat.log 2 n+2)) (Nat.ceil ((n:ℝ)^δ)) sgs : ℝ) ≤
      (548:ℝ)*(κ:ℝ)*(Nat.log 2 n+2:ℕ)^2*(n:ℝ)^(1+δ+ε') := by
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hκR : (1:ℝ)≤κ := by exact_mod_cast hκ
  have hL : (1:ℝ)≤(Nat.log 2 n+2:ℕ) := by exact_mod_cast (Nat.le_add_left 1 (Nat.log 2 n+1))
  have hc := ceil_le_twice_of_one_le ((n:ℝ)^δ) (Real.one_le_rpow hnR hδ)
  have hμ := source_iteration_real_bound n δ ε' hn hδ hε' hdLo
  have hf := source_neighborhood_real_bound n sgs κ hn hκ hsgs
  have he1 : (n:ℝ)*64*(Nat.log 2 n+2:ℕ)*(2*(n:ℝ)^δ) =
      128*(Nat.log 2 n+2:ℕ)*(n:ℝ)^(1+δ) := by
    rw [Real.rpow_add hn0,Real.rpow_one];ring
  have he2 : (21*(n:ℝ)^(δ+ε'))*(20*(κ:ℝ)*(Nat.log 2 n+2:ℕ)*(n:ℝ)) =
      420*(κ:ℝ)*(Nat.log 2 n+2:ℕ)*(n:ℝ)^(1+δ+ε') := by
    rw [show 1+δ+ε'=1+(δ+ε') by ring,Real.rpow_add hn0 (1:ℝ) (δ+ε'),Real.rpow_one];ring
  have hb1 : (n:ℝ)*(64*(Nat.log 2 n+2:ℕ))*(Nat.ceil ((n:ℝ)^δ):ℝ) ≤
      128*(Nat.log 2 n+2:ℕ)*(n:ℝ)^(1+δ) := by
    calc
      _ ≤ (n:ℝ)*64*(Nat.log 2 n+2:ℕ)*(2*(n:ℝ)^δ) := by nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ)≤(n:ℝ)*64*(Nat.log 2 n+2:ℕ))]
      _ = _ := he1
  have hb2 := mul_le_mul hμ hf (by positivity) (by positivity)
  rw [he2] at hb2
  have hpow : (n:ℝ)^(1+δ)≤(n:ℝ)^(1+δ+ε') := Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  have hb1' : (n:ℝ)*(64*(Nat.log 2 n+2:ℕ))*(Nat.ceil ((n:ℝ)^δ):ℝ) ≤
      128*(κ:ℝ)*(Nat.log 2 n+2:ℕ)^2*(n:ℝ)^(1+δ+ε') := by
    apply hb1.trans
    have hfac : (Nat.log 2 n+2:ℕ) ≤ (κ:ℝ)*(Nat.log 2 n+2:ℕ)^2 := by nlinarith
    exact mul_le_mul (by nlinarith : 128*(Nat.log 2 n+2:ℕ)≤128*(κ:ℝ)*(Nat.log 2 n+2:ℕ)^2) hpow
        (by positivity) (by positivity)
  have hb2' : ((n*n/(Nat.floor ((n:ℝ)^(1-δ)/10)*Nat.ceil ((n:ℝ)^(1-ε')))+1:ℕ):ℝ)*
      (n+neighborhoodFee n sgs:ℕ) ≤ 420*(κ:ℝ)*(Nat.log 2 n+2:ℕ)^2*(n:ℝ)^(1+δ+ε') := by
    apply hb2.trans
    have hfac : (Nat.log 2 n+2:ℕ) ≤ ((Nat.log 2 n+2:ℕ):ℝ)^2 := by nlinarith
    gcongr
  unfold classifyBudgetCorrected
  push_cast
  unfold neighborhoodFee at hb2'
  push_cast at hb1' hb2'
  nlinarith

/-- For `0 ≤ ε' < 1` and the stated fee bounds, the triangle reservation is at most `60 * κ *
(Nat.log 2 n + 2) * n^((3 - ε') / 2)`. -/
theorem source_triangle_budget_real_bound (n : ℕ) (ε' : ℝ) (sgs : SGSExecution) (κ : ℕ)
    (hn : 1≤n) (hε' : 0≤ε') (hε'1 : ε'<1) (_hκ : 1≤κ) (hsgs : sgs.κ≤κ) :
    (sourceTriangleReservation sgs n (Nat.ceil ((n:ℝ)^(1-ε'))) : ℝ) ≤
      (60:ℝ)*(κ:ℝ)*(Nat.log 2 n+2:ℕ)*(n:ℝ)^((3-ε')/2) := by
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  let τ := Nat.ceil ((n:ℝ)^(1-ε'))
  let x := max (n.choose 2*τ) (n*n)+1
  have hτ : (τ:ℝ)≤2*(n:ℝ)^(1-ε') :=
    ceil_le_twice_of_one_le _ (Real.one_le_rpow hnR (by linarith))
  have hpτ : (n:ℝ)^(1-ε')≤(n:ℝ) := by
    simpa only [Real.rpow_one] using! Real.rpow_le_rpow_of_exponent_le hnR (by linarith : 1-ε'≤1)
  have hτN : τ≤2*n := by
    have hh : (τ:ℝ)≤2*(n:ℝ) := by nlinarith
    exact_mod_cast hh
  have hchoose := Nat.choose_le_pow n 2
  have hdbN : n.choose 2*τ≤2*n^3 := by nlinarith [Nat.mul_le_mul hchoose hτN]
  have hxN : x≤2^2*n^3 := by
    have hfloor : n*n≤2*n^3 := by
      nlinarith [Nat.pow_le_pow_right (by omega : 1≤n) (by norm_num : 2≤3)]
    have hm := max_le hdbN hfloor
    dsimp only [x]
    nlinarith [Nat.one_le_pow (3:ℕ) n (by omega)]
  have hlog := source_log_polynomial_bound n x 2 3 hn (by norm_num) hxN
  have hlogR : (Nat.log 2 x+2:ℕ) ≤ (5:ℝ)*(Nat.log 2 n+2:ℕ) := by exact_mod_cast hlog
  have hchooseR : (n.choose 2:ℝ)≤(n:ℝ)^2 := by exact_mod_cast hchoose
  have he : (n:ℝ)^2*(2*(n:ℝ)^(1-ε')) = 2*(n:ℝ)^(3-ε') := by
    rw [← Real.rpow_two,show (n:ℝ)^(2:ℝ)*(2*(n:ℝ)^(1-ε'))=2*((n:ℝ)^(2:ℝ)*(n:ℝ)^(1-ε')) by ring,
      ← Real.rpow_add hn0]
    congr 2
    ring
  have hdbR : (n.choose 2*τ:ℕ) ≤ (2:ℝ)*(n:ℝ)^(3-ε') := by
    rw [Nat.cast_mul]
    exact (mul_le_mul hchooseR hτ (by positivity) (by positivity)).trans_eq he
  have hfloorR : (n*n:ℕ)≤(n:ℝ)^(3-ε') := by
    rw [Nat.cast_mul,← pow_two,← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  have hp : (1:ℝ)≤(n:ℝ)^(3-ε') := Real.one_le_rpow hnR (by linarith)
  have hmR : ((max (n.choose 2*τ) (n*n)):ℝ)≤2*(n:ℝ)^(3-ε') := by
    have hm := max_le hdbR (hfloorR.trans (by nlinarith))
    simpa only [Nat.cast_max,Nat.cast_mul] using! hm
  have hxR : (x:ℝ)≤(2:ℝ)^2*(n:ℝ)^(3-ε') := by dsimp only [x];push_cast; nlinarith
  have hs := source_sqrt_rpow_bound n x (3-ε') 2 (by omega) (by norm_num) hxR
  have hpHalf : (1:ℝ)≤(n:ℝ)^((3-ε')/2) := Real.one_le_rpow hnR (by linarith)
  have hs' : (Nat.sqrt x+1:ℕ) ≤ (3:ℝ)*(n:ℝ)^((3-ε')/2) := by push_cast; linarith
  have hκR : (sgs.κ:ℝ)≤κ := by exact_mod_cast hsgs
  have hh :=
      mul_le_mul (mul_le_mul hκR hlogR (by positivity) (by positivity)) hs' (by positivity)
      (by positivity)
  unfold sourceTriangleReservation safeGroverReservation
  push_cast
  push_cast at hh
  dsimp only [x,τ] at hh
  nlinarith only [hh]

/-- Under the stated parameter and rounding assumptions, the moved edge mass bound is at most
`124 * n^(2 - min δ (ε - δ - ε'))`. -/
theorem source_edge_mass_real_bound (n : ℕ) (ε δ ε' : ℝ) (hn : 1≤n)
    (hε : ε≤1) (hδ : 0≤δ) (hδ1 : δ≤1) (hε' : 0≤ε') (_hparam : δ+ε'≤ε)
    (hdLo : 1≤Nat.floor ((n:ℝ)^(1-δ)/10)) :
    (sourceEdgeMassBound n (10*Nat.ceil ((n:ℝ)^(1-δ)))
      (Nat.floor ((n:ℝ)^(1-δ)/10)) (Nat.ceil ((n:ℝ)^(1-ε'))) (Nat.floor ((n:ℝ)^(1-ε))) : ℝ) ≤
      (124:ℝ)*(n:ℝ)^(2-min δ (ε-δ-ε')) := by
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hd := ceil_le_twice_of_one_le ((n:ℝ)^(1-δ)) (Real.one_le_rpow hnR (by linarith))
  have ht : (Nat.floor ((n:ℝ)^(1-ε))+1:ℕ) ≤ (2:ℝ)*(n:ℝ)^(1-ε) := by
    have hf := Nat.floor_le (Real.rpow_nonneg hn0.le (1-ε))
    have hp := Real.one_le_rpow hnR (by linarith : 0≤1-ε)
    push_cast
    linarith
  have hμ := source_iteration_real_bound n δ ε' hn hδ hε' hdLo
  have hb1 : (2*n*(10*Nat.ceil ((n:ℝ)^(1-δ))):ℕ) ≤ (40:ℝ)*(n:ℝ)^(2-δ) := by
    have hh := mul_le_mul_of_nonneg_left hd (by positivity : (0:ℝ)≤20*(n:ℝ))
    have he : 20*(n:ℝ)*(2*(n:ℝ)^(1-δ)) = 40*(n:ℝ)^(2-δ) := by
      rw [show 2-δ=1+(1-δ) by ring,Real.rpow_add hn0 (1:ℝ) (1-δ),Real.rpow_one];ring
    rw [he] at hh
    push_cast
    nlinarith only [hh]
  have hb2 : ((n*n/(Nat.floor ((n:ℝ)^(1-δ)/10)*Nat.ceil ((n:ℝ)^(1-ε')))+1)*
      (2*n*(Nat.floor ((n:ℝ)^(1-ε))+1)):ℕ) ≤ (84:ℝ)*(n:ℝ)^(2+δ+ε'-ε) := by
    have ht' := mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ)≤2*(n:ℝ))
    have hh := mul_le_mul hμ ht' (by positivity) (by positivity)
    have he : (21*(n:ℝ)^(δ+ε'))*(2*(n:ℝ)*(2*(n:ℝ)^(1-ε))) = 84*(n:ℝ)^(2+δ+ε'-ε) := by
      calc
        _ = 84*((n:ℝ)^(δ+ε')*((n:ℝ)^(1:ℝ)*(n:ℝ)^(1-ε))) := by rw [Real.rpow_one];ring
        _ = _ := by rw [← Real.rpow_add hn0,← Real.rpow_add hn0];congr 2;ring
    rw [he] at hh
    push_cast at hh ⊢
    nlinarith only [hh]
  have hp1 : (n:ℝ)^(2-δ) ≤ (n:ℝ)^(2-min δ (ε-δ-ε')) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith [min_le_left δ (ε-δ-ε')])
  have hp2 : (n:ℝ)^(2+δ+ε'-ε) ≤ (n:ℝ)^(2-min δ (ε-δ-ε')) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith [min_le_right δ (ε-δ-ε')])
  unfold sourceEdgeMassBound
  push_cast at hb1 hb2 ⊢
  nlinarith only [hb1,hb2,hp1,hp2]

/-- Under the stated parameter and fee assumptions, the promised edge reservation is at most
`140 * κ * (Nat.log 2 n + 2) * n^((3 - min δ (ε - δ - ε')) / 2)`. -/
theorem source_edge_budget_real_bound (n : ℕ) (ε δ ε' : ℝ) (ets : PromisedEdgeSearchFamily) (κ : ℕ)
    (hn : 1≤n) (hε : ε≤1) (hδ : 0≤δ) (hδ1 : δ<1) (hε' : 0≤ε') (hparam : δ+ε'≤ε)
    (_hκ : 1≤κ) (hets : ets.κ≤κ) (hdLo : 1≤Nat.floor ((n:ℝ)^(1-δ)/10)) :
    (sourceEdgeReservation ets n (10*Nat.ceil ((n:ℝ)^(1-δ)))
      (Nat.floor ((n:ℝ)^(1-δ)/10)) (Nat.ceil ((n:ℝ)^(1-ε'))) (Nat.floor ((n:ℝ)^(1-ε))) : ℝ) ≤
      (140:ℝ)*(κ:ℝ)*(Nat.log 2 n+2:ℕ)*(n:ℝ)^((3-min δ (ε-δ-ε'))/2) := by
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  let m := min δ (ε-δ-ε')
  let M := sourceEdgeMassBound n (10*Nat.ceil ((n:ℝ)^(1-δ)))
    (Nat.floor ((n:ℝ)^(1-δ)/10)) (Nat.ceil ((n:ℝ)^(1-ε'))) (Nat.floor ((n:ℝ)^(1-ε)))
  have hm : 0 ≤ m := le_min hδ (by linarith)
  have hm1 : m<1 := (min_le_left _ _).trans_lt hδ1
  have hM : (M:ℝ)≤124*(n:ℝ)^(2-m) :=
      source_edge_mass_real_bound n ε δ ε' hn hε hδ hδ1.le hε' hparam hdLo
  have hM2 : (M:ℝ)≤124*(n:ℝ)^2 := by
    have hp : (n:ℝ)^(2-m)≤(n:ℝ)^2 := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
    nlinarith
  have hMN : M≤124*n^2 := by exact_mod_cast hM2
  have hx : n*n+n*M+1≤2^7*n^3 := by
    have hh := Nat.mul_le_mul_left n hMN
    nlinarith [Nat.pow_le_pow_right (by omega : 1≤n) (by norm_num : 2≤3),Nat.one_le_pow (3:ℕ) n (by omega)]
  have hlog := source_log_polynomial_bound n (n*n+n*M+1) 7 3 hn (by norm_num) hx
  have hlogR : (Nat.log 2 (n*n+n*M+1)+2:ℕ)≤(10:ℝ)*(Nat.log 2 n+2:ℕ) := by exact_mod_cast hlog
  have hnM : (n*M:ℕ)≤(12:ℝ)^2*(n:ℝ)^(3-m) := by
    have hh := mul_le_mul_of_nonneg_left hM hn0.le
    have he : (n:ℝ)*(124*(n:ℝ)^(2-m))=124*(n:ℝ)^(3-m) := by
      rw [show 3-m=1+(2-m) by ring,Real.rpow_add hn0 (1:ℝ) (2-m),Real.rpow_one];ring
    rw [he] at hh
    rw [Nat.cast_mul]
    nlinarith [Real.rpow_nonneg hn0.le (3-m)]
  have hsM := source_sqrt_rpow_bound n (n*M) (3-m) 12 (by omega) (by norm_num) hnM
  have hsn : (Nat.sqrt (n*n):ℝ)≤(n:ℝ) := by
    have hh : Nat.sqrt (n*n)≤n := by nlinarith [Nat.sqrt_le (n*n)]
    exact_mod_cast hh
  have hpn : (n:ℝ)≤(n:ℝ)^((3-m)/2) := by
    simpa only [Real.rpow_one] using! Real.rpow_le_rpow_of_exponent_le hnR (by linarith : 1≤(3-m)/2)
  have hp1 : (1:ℝ)≤(n:ℝ)^((3-m)/2) := hnR.trans hpn
  have hs : (Nat.sqrt (n*n)+Nat.sqrt (n*M)+1:ℕ)≤(14:ℝ)*(n:ℝ)^((3-m)/2) := by push_cast;linarith
  have hκR : (ets.κ:ℝ)≤κ := by exact_mod_cast hets
  have hh :=
      mul_le_mul (mul_le_mul hκR hlogR (by positivity) (by positivity)) hs (by positivity)
      (by positivity)
  unfold sourceEdgeReservation promisedEdgeReservation
  push_cast at hh ⊢
  dsimp only [M,m] at hh
  nlinarith only [hh]

/-- Under the stated exponent assumptions and with `1 ≤ dLo`, the total integer budget at the
prescribed rounded parameters is at most `2^24 * sourceCapabilityFeeFactor family ets *
(Nat.log 2 n + 2)^4` times `sourceFourTermBudget n ε δ ε'`. -/
theorem sourceCombinatorialBudget_real_bound (n : ℕ) (ε δ ε' : ℝ)
    (family : ScopedGroverFamily) (ets : PromisedEdgeSearchFamily)
    (hn : 0<n) (hε : 0<ε) (hε1 : ε<1) (hδ : 0<δ) (hε' : 0<ε') (hparam : δ+ε'≤ε)
    (hdLo : 1≤Nat.floor ((n:ℝ)^(1-δ)/10)) :
    let k:=Nat.ceil (4*(n:ℝ)^ε*(Nat.log 2 n+1))
    let K:=64*(Nat.log 2 n+2)
    let c:=Nat.ceil ((n:ℝ)^δ)
    let dHi:=10*Nat.ceil ((n:ℝ)^(1-δ))
    let dLo:=Nat.floor ((n:ℝ)^(1-δ)/10)
    let τ:=Nat.ceil ((n:ℝ)^(1-ε'))
    let tThin:=Nat.floor ((n:ℝ)^(1-ε))
    let sgs:=sourceSearchExecution family n τ
    (sourceCombinatorialBudget sgs ets n k dHi dLo τ K c tThin : ℝ) ≤
      ((2^24:ℕ)*sourceCapabilityFeeFactor family ets*(Nat.log 2 n+2)^4:ℕ)*sourceFourTermBudget n ε δ ε' := by
  intro k K c dHi dLo τ tThin sgs
  let κ := sourceCapabilityFeeFactor family ets
  let L : ℝ := (Nat.log 2 n+2:ℕ)
  have hκ : 1≤κ := Nat.le_max_left _ _
  have hsgs : sgs.κ≤κ := (Nat.le_max_left family.κ ets.κ).trans (Nat.le_max_right _ _)
  have hets : ets.κ≤κ := (Nat.le_max_right family.κ ets.κ).trans (Nat.le_max_right _ _)
  have hn1 : 1≤n := by omega
  have hL : (2:ℝ)≤L := by dsimp only [L]; exact_mod_cast (Nat.le_add_left 2 (Nat.log 2 n))
  have hδ1 : δ<1 := by linarith
  have hε'1 : ε'<1 := by linarith
  have hb0 := source_preparation_budget_real_bound n ε sgs κ hn1 hε.le hκ hsgs
  have hb1 := source_classification_budget_real_bound n δ ε' sgs κ hn1 hδ.le hε'.le hκ hsgs hdLo
  have hb2 := source_triangle_budget_real_bound n ε' sgs κ hn1 hε'.le hε'1 hκ hsgs
  have hb3 :=
      source_edge_budget_real_bound n ε δ ε' ets κ hn1 hε1.le hδ.le hδ1 hε'.le hparam hκ hets hdLo
  have hL2 : L≤L^2 := by nlinarith
  have h0 : (k*(n+neighborhoodFee n sgs):ℕ) ≤ (1024:ℝ)*(κ:ℝ)*L^2*(n:ℝ)^(1+ε) := by
    apply hb0.trans
    dsimp only [L]
    gcongr
    norm_num
  have h1 : (classifyBudgetCorrected n dLo τ K c sgs : ℝ) ≤ (1024:ℝ)*(κ:ℝ)*L^2*(n:ℝ)^(1+δ+ε') := by
    apply hb1.trans
    dsimp only [L]
    gcongr
    norm_num
  have h2 : (sourceTriangleReservation sgs n τ : ℝ) ≤ (1024:ℝ)*(κ:ℝ)*L^2*(n:ℝ)^((3-ε')/2) := by
    apply hb2.trans
    change 60*(κ:ℝ)*L*(n:ℝ)^((3-ε')/2) ≤ _
    gcongr
    norm_num
  have h3 : (sourceEdgeReservation ets n dHi dLo τ tThin : ℝ) ≤ (1024:ℝ)*(κ:ℝ)*L^2*(n:ℝ)^((3-min δ (ε-δ-ε'))/2) := by
    apply hb3.trans
    change 140*(κ:ℝ)*L*(n:ℝ)^((3-min δ (ε-δ-ε'))/2) ≤ _
    gcongr
    norm_num
  have hs := add_le_add (add_le_add (add_le_add h0 h1) h2) h3
  have hb : (sourceCombinatorialBudget sgs ets n k dHi dLo τ K c tThin : ℝ) ≤
      (1024:ℝ)*(κ:ℝ)*L^2*sourceFourTermBudget n ε δ ε' := by
    unfold sourceCombinatorialBudget sourceFourTermBudget
    push_cast
    push_cast at hs
    convert! hs using 1 <;> ring
  have hL24 : L^2≤L^4 := by nlinarith [sq_nonneg (L^2-1)]
  have hfac : (1024:ℝ)*(κ:ℝ)*L^2 ≤ ((2^24:ℕ)*κ*(Nat.log 2 n+2)^4:ℕ) := by
    dsimp only [L] at hL24 ⊢
    push_cast at hL24 ⊢
    gcongr
    norm_num
  exact hb.trans (mul_le_mul_of_nonneg_right hfac (by unfold sourceFourTermBudget; positivity))

end Qatlib.Concepts.WalkSearch.MainResults
