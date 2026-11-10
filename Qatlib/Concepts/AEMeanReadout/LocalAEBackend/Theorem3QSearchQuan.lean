/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchStat
import Qatlib.Concepts.WalkSearch.QuantumAccess.GeometricSearchBudget
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Qatlib
open scoped ENNReal Classical

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchSpec
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch

private theorem geopow_ge_one (k : ℕ) : (1:ℝ) ≤ ((6/5:ℝ)^k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ ((6/5:ℝ)^k) * (6/5) := mul_le_mul ih (by norm_num) (by norm_num) (by norm_num)
        _ = (6/5:ℝ)^(k+1) := (pow_succ _ _).symm

private theorem geopow_mono {a b : ℕ} (h : a ≤ b) : ((6/5:ℝ)^a) ≤ ((6/5:ℝ)^b) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  rw [hd, pow_add]
  calc ((6/5:ℝ)^a) = ((6/5:ℝ)^a) * 1 := (mul_one _).symm
    _ ≤ ((6/5:ℝ)^a) * ((6/5:ℝ)^d) := mul_le_mul_of_nonneg_left (geopow_ge_one d)
      (by positivity)

private theorem window_raw_mul (k : ℕ) : (6:ℕ)^k ≤ 5^k * ((6^k + 5^k - 1) / 5^k) := by
  have h5 : (0:ℕ) < 5^k := Nat.pow_pos (by norm_num)
  have hd := Nat.div_add_mod (6^k + 5^k - 1) (5^k)
  have hmod : (6^k + 5^k - 1) % 5^k ≤ 5^k - 1 := Nat.le_pred_of_lt (Nat.mod_lt _ h5)
  omega

private theorem window_pow (k : ℕ) : ((6/5:ℝ)^k) = ((6^k:ℕ):ℝ)/((5^k:ℕ):ℝ) := by
  rw [div_pow]
  push_cast
  rfl

private theorem window_eq (l : ℕ) : qSearchWindow l = (6^l + 5^l - 1) / 5^l := by
  show max 1 ((6^l + 5^l - 1) / 5^l) = _
  have h5 : (0:ℕ) < 5^l := Nat.pow_pos (by norm_num)
  have hge : (1:ℕ) ≤ (6^l + 5^l - 1) / 5^l := by
    rw [Nat.one_le_div_iff h5]
    have : (1:ℕ) ≤ 6^l := Nat.pow_pos (by omega)
    omega
  omega

private theorem window_ge (l : ℕ) : ((6/5:ℝ)^l) ≤ (qSearchWindow l : ℝ) := by
  have h5 : (0:ℕ) < 5^l := Nat.pow_pos (by norm_num)
  have h5R : (0:ℝ) < ((5^l:ℕ):ℝ) := by exact_mod_cast h5
  have hceil : ((6^l:ℕ):ℝ)/((5^l:ℕ):ℝ) ≤ (((6^l + 5^l - 1)/5^l : ℕ):ℝ) := by
    rw [div_le_iff₀ h5R]
    calc ((6^l:ℕ):ℝ) ≤ ((5^l * ((6^l + 5^l - 1)/5^l) : ℕ):ℝ) := by
          push_cast
          exact_mod_cast window_raw_mul l
      _ = (((6^l + 5^l - 1)/5^l : ℕ):ℝ) * ((5^l:ℕ):ℝ) := by push_cast; ring
  rw [window_eq, window_pow]
  exact hceil

private theorem window_le (l : ℕ) : (qSearchWindow l : ℝ) ≤ 2 * ((6/5:ℝ)^l) := by
  have h5R : (0:ℝ) < ((5^l:ℕ):ℝ) := by
    have : (0:ℕ) < 5^l := Nat.pow_pos (by norm_num)
    exact_mod_cast this
  have hhigh : (((6^l+5^l-1)/5^l : ℕ):ℝ) ≤ ((6/5:ℝ)^l) + 1 := by
    have h1 : (((6^l+5^l-1)/5^l : ℕ):ℝ) ≤ ((6^l+5^l-1:ℕ):ℝ)/((5^l:ℕ):ℝ) := Nat.cast_div_le
    have h2 : ((6^l+5^l-1:ℕ):ℝ) ≤ ((6^l+5^l:ℕ):ℝ) := by exact_mod_cast (Nat.sub_le _ _)
    have h3 : ((6^l+5^l-1:ℕ):ℝ)/((5^l:ℕ):ℝ) ≤ ((6^l+5^l:ℕ):ℝ)/((5^l:ℕ):ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have h4 : ((6^l+5^l:ℕ):ℝ) = ((6^l:ℕ):ℝ) + ((5^l:ℕ):ℝ) := Nat.cast_add _ _
    calc (((6^l+5^l-1)/5^l : ℕ):ℝ) ≤ ((6^l+5^l-1:ℕ):ℝ)/((5^l:ℕ):ℝ) := h1
      _ ≤ ((6^l+5^l:ℕ):ℝ)/((5^l:ℕ):ℝ) := h3
      _ = ((6^l:ℕ):ℝ)/((5^l:ℕ):ℝ) + ((5^l:ℕ):ℝ)/((5^l:ℕ):ℝ) := by rw [h4, add_div]
      _ = ((6/5:ℝ)^l) + 1 := by rw [← window_pow, div_self (ne_of_gt h5R)]
  have hcast : (qSearchWindow l : ℝ) = (((6^l+5^l-1)/5^l : ℕ):ℝ) := by rw [window_eq]
  rw [hcast]
  have hge := geopow_ge_one l
  linarith

private theorem exists_geometric_cross {s : ℝ} (hs : 0 < s) :
    ∃ k : ℕ, 1 ≤ k ∧ 1 ≤ ((6/5:ℝ)^k)*s := by
  have hgrowth : ∀ k : ℕ, 1 + (k:ℝ)/5 ≤ ((6/5:ℝ)^k) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        calc (1:ℝ) + (((k+1:ℕ):ℝ))/5 ≤ (6/5:ℝ) * (1 + (k:ℝ)/5) := by
              have heq : (1:ℝ) + ((k+1:ℕ):ℝ)/5 + (k:ℝ)/25
                  = (6/5:ℝ) * (1 + (k:ℝ)/5) := by
                push_cast
                field_simp
                ring
              have hk25 : (0:ℝ) ≤ (k:ℝ)/25 := by positivity
              linarith
          _ ≤ (6/5:ℝ) * ((6/5:ℝ)^k) := mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (6/5:ℝ)^(k+1) := (pow_succ' _ _).symm
  refine ⟨max 1 (Nat.ceil (5/s)), Nat.le_max_left 1 _, ?_⟩
  have hceil5 : (5/s) ≤ ((Nat.ceil (5/s) : ℕ):ℝ) := Nat.le_ceil (5/s)
  have hmax1 : (5/s) ≤ ((max 1 (Nat.ceil (5/s) : ℕ)):ℝ) := by
    calc (5/s) ≤ ((Nat.ceil (5/s) : ℕ):ℝ) := hceil5
      _ ≤ ((max 1 (Nat.ceil (5/s) : ℕ)):ℝ) := by
          exact_mod_cast Nat.le_max_right 1 (Nat.ceil (5/s))
  have h1 : (1:ℝ) + ((max 1 (Nat.ceil (5/s) : ℕ)):ℝ)/5 ≥ 1 + (5/s)/5 := by
    apply add_le_add (le_refl 1)
    exact div_le_div_of_nonneg_right hmax1 (by norm_num)
  have h2 : (1:ℝ) + (5/s)/5 = 1 + 1/s := by field_simp
  have hgrow := hgrowth (max 1 (Nat.ceil (5/s)))
  simp only [Nat.cast_max, Nat.cast_one] at hgrow
  have hkey : 1/s ≤ ((6/5:ℝ)^(max 1 (Nat.ceil (5/s)))) := by
    calc 1/s ≤ 1 + 1/s := by linarith
      _ = 1 + (5/s)/5 := h2.symm
      _ ≤ 1 + ((max 1 (Nat.ceil (5/s) : ℕ)):ℝ)/5 := h1
      _ ≤ (6/5:ℝ)^(max 1 (Nat.ceil (5/s))) := hgrow
  calc (1:ℝ) = (1/s) * s := by field_simp
    _ ≤ ((6/5:ℝ)^(max 1 (Nat.ceil (5/s)))) * s :=
        mul_le_mul_of_nonneg_right hkey (le_of_lt hs)

private noncomputable def W (l : ℕ) : ℝ≥0∞ := ((6/5:ℝ≥0∞))^l

private theorem one_le_65 : (1:ℝ≥0∞) ≤ (6/5:ℝ≥0∞) := by
  rw [show ((6/5:ℝ≥0∞)) = ENNReal.ofReal ((6/5:ℝ)) from by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 5)]
      norm_num,
    ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

private theorem W_succ (l : ℕ) : W (l+1) = W l * (6/5:ℝ≥0∞) := pow_succ _ _

private theorem W_pos (l : ℕ) : (1:ℝ≥0∞) ≤ W l := by
  induction l with
  | zero => simp [W]
  | succ l ih =>
      calc (1:ℝ≥0∞) = 1 * 1 := by ring
        _ ≤ W l * (6/5:ℝ≥0∞) := mul_le_mul' ih one_le_65
        _ = W (l+1) := (W_succ l).symm

private theorem W_mono {a b : ℕ} (h : a ≤ b) : W a ≤ W b := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  rw [hd]
  clear hd h b
  induction d with
  | zero => simp
  | succ d ih =>
      calc W a ≤ W (a + d) := ih
        _ ≤ W (a + d + 1) := by
            rw [W_succ]
            simpa using mul_le_mul' (le_refl (W (a + d))) one_le_65

private theorem W_mul_real {c : ℝ} (hc : 0 ≤ c) (l : ℕ) :
    (ENNReal.ofReal c) * W l = ENNReal.ofReal (c * ((6/5:ℝ)^l)) := by
  have h65 : ((6/5:ℝ≥0∞)) = ENNReal.ofReal ((6/5:ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 5)]
    norm_num
  show ENNReal.ofReal c * ((6/5:ℝ≥0∞))^l = _
  rw [h65, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 6/5), ← ENNReal.ofReal_mul hc]

private theorem window_coe_le (l : ℕ) :
    ((qSearchWindow l : ℕ) : ℝ≥0∞) ≤ (4:ℝ≥0∞) * W l := by
  have h1 : ((qSearchWindow l : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((qSearchWindow l : ℕ):ℝ) :=
    (ENNReal.ofReal_natCast _).symm
  have h2 : (4:ℝ≥0∞) * W l = ENNReal.ofReal (4 * ((6/5:ℝ)^l)) := by
    rw [show (4:ℝ≥0∞) = ENNReal.ofReal (4:ℝ) from by norm_num, W_mul_real (by norm_num)]
  rw [h1, h2]
  exact ENNReal.ofReal_le_ofReal ((window_le l).trans (by
    have := geopow_ge_one l
    linarith))

section Closed
variable {E : ℕ → ℕ → ℝ≥0∞} {Ec F : ℕ → ℝ≥0∞}

private theorem closed_quarter (hrec : ∀ T off : ℕ,
    E (T+1) off = Ec (off+1) + F (off+1) * E T (off+1))
    (hzero : ∀ off : ℕ, E 0 off = 0)
    (hcost : ∀ l : ℕ, Ec l ≤ ENNReal.ofReal (4 * ((6/5:ℝ)^l)))
    (hfail : ∀ l : ℕ, F l ≤ ENNReal.ofReal (1/4)) :
    ∀ T off : ℕ, E T off ≤ ENNReal.ofReal (6 * ((6/5:ℝ)^(off+1))) := by
  intro T off
  induction T generalizing off with
  | zero => rw [hzero off]; simp
  | succ T ih =>
      have hcost' := hcost (off+1)
      have hfail' := hfail (off+1)
      have hIH := ih (off+1)
      have hgrow : (6/5:ℝ)^(off+1+1) = (6/5:ℝ)^(off+1) * (6/5:ℝ) := pow_succ _ _
      have h36 : (ENNReal.ofReal (1/4)) * ENNReal.ofReal (6 * ((6/5:ℝ)^(off+1+1)))
          = ENNReal.ofReal ((9/5) * ((6/5:ℝ)^(off+1))) := by
        rw [hgrow, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/4)]
        congr 1
        have hp : (0:ℝ) < (6/5:ℝ)^(off+1) := by positivity
        field_simp
        ring
      calc E (T+1) off = Ec (off+1) + F (off+1) * E T (off+1) := hrec T off
        _ ≤ ENNReal.ofReal (4 * ((6/5:ℝ)^(off+1)))
              + (ENNReal.ofReal (1/4)) * ENNReal.ofReal (6 * ((6/5:ℝ)^(off+1+1))) :=
              add_le_add hcost' (mul_le_mul' hfail' hIH)
        _ = ENNReal.ofReal (4 * ((6/5:ℝ)^(off+1)))
              + ENNReal.ofReal ((9/5) * ((6/5:ℝ)^(off+1))) := by rw [h36]
        _ = ENNReal.ofReal ((4 + 9/5) * ((6/5:ℝ)^(off+1))) := by
            rw [← ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ 4 * ((6/5:ℝ)^(off+1)))
              (by positivity : (0:ℝ) ≤ (9/5) * ((6/5:ℝ)^(off+1)))]
            congr 1
            ring
        _ ≤ ENNReal.ofReal (6 * ((6/5:ℝ)^(off+1))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have hx : (0:ℝ) ≤ (6/5:ℝ)^(off+1) := by positivity
            nlinarith [hx, mul_nonneg hx (by norm_num : (0:ℝ) ≤ 4 + 9/5)]

private theorem closed_mature (ls : ℕ) (hrec : ∀ T off : ℕ,
    E (T+1) off = Ec (off+1) + F (off+1) * E T (off+1))
    (hzero : ∀ off : ℕ, E 0 off = 0)
    (hcost : ∀ l : ℕ, Ec l ≤ ENNReal.ofReal (4 * ((6/5:ℝ)^l)))
    (hfail : ∀ l : ℕ, ls ≤ l → F l ≤ ENNReal.ofReal (3/4)) :
    ∀ T off : ℕ, ls ≤ off+1 →
    E T off ≤ ENNReal.ofReal (40 * ((6/5:ℝ)^(off+1))) := by
  intro T off
  induction T generalizing off with
  | zero => intro _; rw [hzero off]; simp
  | succ T ih =>
      intro hoff
      have hcost' := hcost (off+1)
      have hfail' := hfail (off+1) hoff
      have hIH := ih (off+1) (by omega)
      have hgrow : (6/5:ℝ)^(off+1+1) = (6/5:ℝ)^(off+1) * (6/5:ℝ) := pow_succ _ _
      have h36 : (ENNReal.ofReal (3/4)) * ENNReal.ofReal (40 * ((6/5:ℝ)^(off+1+1)))
          = ENNReal.ofReal (36 * ((6/5:ℝ)^(off+1))) := by
        rw [hgrow, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3/4)]
        congr 1
        have hp : (0:ℝ) < (6/5:ℝ)^(off+1) := by positivity
        field_simp
        ring
      calc E (T+1) off = Ec (off+1) + F (off+1) * E T (off+1) := hrec T off
        _ ≤ ENNReal.ofReal (4 * ((6/5:ℝ)^(off+1)))
              + (ENNReal.ofReal (3/4)) * ENNReal.ofReal (40 * ((6/5:ℝ)^(off+1+1))) :=
              add_le_add hcost' (mul_le_mul' hfail' hIH)
        _ = ENNReal.ofReal (4 * ((6/5:ℝ)^(off+1)))
              + ENNReal.ofReal (36 * ((6/5:ℝ)^(off+1))) := by rw [h36]
        _ = ENNReal.ofReal ((4 + 36) * ((6/5:ℝ)^(off+1))) := by
            rw [← ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ 4 * ((6/5:ℝ)^(off+1)))
              (by positivity : (0:ℝ) ≤ 36 * ((6/5:ℝ)^(off+1)))]
            congr 1
            ring
        _ = ENNReal.ofReal (40 * ((6/5:ℝ)^(off+1))) := by congr 1; norm_num

private theorem closed_immature (ls : ℕ) (hrec : ∀ T off : ℕ,
    E (T+1) off = Ec (off+1) + F (off+1) * E T (off+1))
    (hzero : ∀ off : ℕ, E 0 off = 0)
    (hcost : ∀ l : ℕ, Ec l ≤ ENNReal.ofReal (4 * ((6/5:ℝ)^l)))
    (hfail1 : ∀ l : ℕ, F l ≤ 1)
    (hfailm : ∀ l : ℕ, ls ≤ l → F l ≤ ENNReal.ofReal (3/4))
    (hmature : ∀ T off : ℕ, ls ≤ off+1 →
      E T off ≤ ENNReal.ofReal (40 * ((6/5:ℝ)^(off+1)))) :
    ∀ T off : ℕ, off+1 ≤ ls →
    E T off + ENNReal.ofReal (24 * ((6/5:ℝ)^(off+1)))
      ≤ ENNReal.ofReal (64 * ((6/5:ℝ)^ls)) := by
  intro T off
  induction T generalizing off with
  | zero =>
      intro hoff
      rw [hzero off, zero_add]
      have hle : ((6/5:ℝ)^(off+1)) ≤ ((6/5:ℝ)^ls) := geopow_mono (by omega)
      have hx2 : (0:ℝ) ≤ (6/5:ℝ)^ls := by positivity
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
  | succ T ih =>
      intro hoff
      rcases Nat.lt_or_ge (off+1) ls with hlt | hge
      · have hfail := hfail1 (off+1)
        have hcost4 := hcost (off+1)
        have hIH := ih (off+1) (by omega)
        have hgrow : (6/5:ℝ)^(off+1+1) = (6/5:ℝ)^(off+1) * (6/5:ℝ) := pow_succ _ _
        have hkey : ENNReal.ofReal (4 * ((6/5:ℝ)^(off+1)))
            + ENNReal.ofReal (24 * ((6/5:ℝ)^(off+1)))
            ≤ ENNReal.ofReal (24 * ((6/5:ℝ)^(off+1+1))) := by
          rw [hgrow, ← ENNReal.ofReal_add
            (by positivity : (0:ℝ) ≤ 4 * ((6/5:ℝ)^(off+1)))
            (by positivity : (0:ℝ) ≤ 24 * ((6/5:ℝ)^(off+1)))]
          refine ENNReal.ofReal_le_ofReal ?_
          have hx : (0:ℝ) ≤ (6/5:ℝ)^(off+1) := by positivity
          nlinarith [hx, mul_nonneg hx (by norm_num : (0:ℝ) ≤ 28)]
        calc E (T+1) off + ENNReal.ofReal (24 * ((6/5:ℝ)^(off+1)))
            = Ec (off+1) + F (off+1) * E T (off+1)
                + ENNReal.ofReal (24 * ((6/5:ℝ)^(off+1))) := by rw [hrec T off]
          _ ≤ (ENNReal.ofReal (4 * ((6/5:ℝ)^(off+1))) + E T (off+1))
                + ENNReal.ofReal (24 * ((6/5:ℝ)^(off+1))) := by
              refine add_le_add (add_le_add hcost4 ?_) le_rfl
              calc F (off+1) * E T (off+1) ≤ (1:ℝ≥0∞) * E T (off+1) :=
                    mul_le_mul' hfail le_rfl
                _ = E T (off+1) := one_mul _
          _ = E T (off+1) + (ENNReal.ofReal (4 * ((6/5:ℝ)^(off+1)))
                + ENNReal.ofReal (24 * ((6/5:ℝ)^(off+1)))) := by ring
          _ ≤ E T (off+1) + ENNReal.ofReal (24 * ((6/5:ℝ)^(off+1+1))) :=
              add_le_add le_rfl hkey
          _ ≤ ENNReal.ofReal (64 * ((6/5:ℝ)^ls)) := hIH
      · have hoffeq : off+1 = ls := by omega
        have hfailm' := hfailm (off+1) (by omega)
        have hmature' := hmature T (off+1) (by omega)
        have hgrow : (6/5:ℝ)^(off+1+1) = (6/5:ℝ)^(off+1) * (6/5:ℝ) := pow_succ _ _
        have h36 : (ENNReal.ofReal (3/4)) * ENNReal.ofReal (40 * ((6/5:ℝ)^(off+1+1)))
            = ENNReal.ofReal (36 * ((6/5:ℝ)^(off+1))) := by
          rw [hgrow, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3/4)]
          congr 1
          have hp : (0:ℝ) < (6/5:ℝ)^(off+1) := by positivity
          field_simp
          ring
        calc E (T+1) off + ENNReal.ofReal (24 * ((6/5:ℝ)^(off+1)))
            = Ec (off+1) + F (off+1) * E T (off+1)
                + ENNReal.ofReal (24 * ((6/5:ℝ)^(off+1))) := by rw [hrec T off]
          _ ≤ (ENNReal.ofReal (4 * ((6/5:ℝ)^(off+1)))
                + (ENNReal.ofReal (3/4)) * ENNReal.ofReal (40 * ((6/5:ℝ)^(off+1+1))))
                + ENNReal.ofReal (24 * ((6/5:ℝ)^(off+1))) :=
                add_le_add (add_le_add (hcost (off+1)) (mul_le_mul' hfailm' hmature')) le_rfl
          _ = ENNReal.ofReal (4 * ((6/5:ℝ)^(off+1)))
                + ENNReal.ofReal (36 * ((6/5:ℝ)^(off+1)))
                + ENNReal.ofReal (24 * ((6/5:ℝ)^(off+1))) := by rw [h36]
          _ = ENNReal.ofReal ((4 + 36 + 24) * ((6/5:ℝ)^(off+1))) := by
              have h1 : ENNReal.ofReal (36 * ((6/5:ℝ)^(off+1)))
                  + ENNReal.ofReal (24 * ((6/5:ℝ)^(off+1)))
                  = ENNReal.ofReal ((36 + 24) * ((6/5:ℝ)^(off+1))) := by
                rw [← ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ 36 * ((6/5:ℝ)^(off+1)))
                  (by positivity : (0:ℝ) ≤ 24 * ((6/5:ℝ)^(off+1)))]
                congr 1
                ring
              have h2 : ENNReal.ofReal (4 * ((6/5:ℝ)^(off+1)))
                  + ENNReal.ofReal ((36 + 24) * ((6/5:ℝ)^(off+1)))
                  = ENNReal.ofReal ((4 + (36 + 24)) * ((6/5:ℝ)^(off+1))) := by
                rw [← ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ 4 * ((6/5:ℝ)^(off+1)))
                  (by positivity : (0:ℝ) ≤ (36 + 24) * ((6/5:ℝ)^(off+1)))]
                congr 1
                ring
              rw [add_assoc, h1, h2]
              congr 1
              ring
          _ = ENNReal.ofReal (64 * ((6/5:ℝ)^ls)) := by
              rw [hoffeq]
              congr 1
              norm_num

end Closed

private theorem expectation_indicator_mul' {α : Type} (p : PMF α) (P : α → Prop)
    [DecidablePred P] (c : ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun a => if P a then c else 0) = c * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p P := by
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq p P,
      ← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
  exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
      (fun a => by by_cases hP : P a <;> simp [hP])

private theorem event_zero_nosup {α : Type} (p : PMF α) (P : α → Prop)
    (h : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p P = 0) : ∀ x ∈ p.support, ¬ P x := by
  intro x hx hPx
  have hsingle : p x ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p P := by
    show p x ≤ ∑' a, p a * (if P a then (1:ℝ≥0∞) else 0)
    calc p x = p x * (if P x then (1:ℝ≥0∞) else 0) := by rw [if_pos hPx, mul_one]
      _ ≤ ∑' a, p a * (if P a then (1:ℝ≥0∞) else 0) := ENNReal.le_tsum (f := fun a => p a * (if P a then (1:ℝ≥0∞) else 0)) x
  rw [h] at hsingle
  rw [PMF.mem_support_iff] at hx
  exact absurd (le_antisymm hsingle (by simp)) hx

private theorem uniform_apply_univ {m : ℕ} (hm : 0 < m)
    (hs : (Finset.univ : Finset (Fin m)).Nonempty) (j : Fin m) :
    PMF.uniformOfFinset (Finset.univ : Finset (Fin m)) hs j = ((m : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [PMF.uniformOfFinset_apply hs j, if_pos (Finset.mem_univ j), Finset.card_univ,
    Fintype.card_fin]

section Round
variable {I : Type} [Fintype I] [DecidableEq I]

private theorem window_pos (l : ℕ) : 0 < qSearchWindow l := by
  show 0 < max 1 _
  omega

private theorem qSearchRound_eq (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) :
    qSearchRound A hA j₀ S l =
      PMF.bind (preparedAATrial A hA j₀ S (⟨0, Nat.zero_lt_one⟩ : Fin 1))
        fun st =>
        if st.1.1 ∈ S then
          PMF.pure (some st.1.1, 1, 1)
        else
          PMF.bind
            (PMF.uniformOfFinset (Finset.univ : Finset (Fin (qSearchWindow l)))
              ⟨⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_one) (le_max_left 1
                ((6^l + 5^l - 1) / 5^l))⟩, Finset.mem_univ _⟩) fun j =>
            PMF.bind (preparedAATrial A hA j₀ S j) fun st2 =>
              PMF.pure (if st2.1.1 ∈ S then some st2.1.1 else none,
                2 + 2*j.val, 2 + j.val) := rfl

private theorem round_shape (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) (out : Option I × ℕ × ℕ)
    (hout : out ∈ (qSearchRound A hA j₀ S l).support) :
    (∀ y, out.1 = some y → y ∈ S) ∧ out.2.1 ≤ 2*qSearchWindow l ∧
      out.2.2 ≤ 2*qSearchWindow l := by
  have h1w : (1:ℕ) ≤ qSearchWindow l := by
    show (1:ℕ) ≤ max 1 _
    omega
  rw [qSearchRound_eq] at hout
  obtain ⟨st, hst, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  by_cases hS : st.1.1 ∈ S
  · rw [if_pos hS] at hout
    have hout' : out = (some st.1.1, 1, 1) := by
      simpa [PMF.mem_support_pure_iff] using hout
    subst hout'
    refine ⟨fun y hy => ?_, ?_, ?_⟩
    · rw [← Option.some.inj hy]; exact hS
    · show (1:ℕ) ≤ 2*qSearchWindow l; omega
    · show (1:ℕ) ≤ 2*qSearchWindow l; omega
  · rw [if_neg hS] at hout
    obtain ⟨j, hj, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    obtain ⟨st2, hst2, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    have hout' : out = (if st2.1.1 ∈ S then some st2.1.1 else none, 2 + 2*j.val, 2 + j.val) := by
      simpa [PMF.mem_support_pure_iff] using hout
    subst hout'
    have hjlt : j.val < qSearchWindow l := j.isLt
    refine ⟨fun y hy => ?_, ?_, ?_⟩
    · by_cases h2 : st2.1.1 ∈ S
      · rw [if_pos h2] at hy; rw [← Option.some.inj hy]; exact h2
      · rw [if_neg h2] at hy; exact absurd hy (by simp)
    · show (2 + 2*j.val : ℕ) ≤ 2*qSearchWindow l; omega
    · show (2 + j.val : ℕ) ≤ 2*qSearchWindow l; omega

private theorem trial_zero_mass (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAATrial A hA j₀ S (⟨0, Nat.zero_lt_one⟩ : Fin 1))
        (fun x => x.1.1 ∈ S)
      = ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S) := by
  rw [(prepared_aa_trial_actual_metadata A j₀ S hA (⟨0, Nat.zero_lt_one⟩ : Fin 1)).2.2,
    show ((⟨0, Nat.zero_lt_one⟩ : Fin 1) : ℕ) = 0 from rfl,
    (prepared_aa_actual_circuit A j₀ S 0 hA).2.2.2, pow_zero, applyGate_one]

private theorem trial_zero_compl (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAATrial A hA j₀ S (⟨0, Nat.zero_lt_one⟩ : Fin 1))
        (fun x => ¬ x.1.1 ∈ S)
      = 1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S) := by
  have hpair := event_compl (preparedAATrial A hA j₀ S (⟨0, Nat.zero_lt_one⟩ : Fin 1))
    (fun x => x.1.1 ∈ S)
  rw [trial_zero_mass] at hpair
  rw [add_comm] at hpair
  exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hpair

private theorem uniform_trial_event (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) {m : ℕ} (hm : 0 < m)
    {hs : (Finset.univ : Finset (Fin m)).Nonempty} :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (PMF.uniformOfFinset (Finset.univ : Finset (Fin m)) hs)
        (fun j => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAATrial A hA j₀ S j) (fun x => x.1.1 ∈ S))
      = ((m : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin m, ENNReal.ofReal
          (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ (j : ℕ)) (Ket j₀)) S) := by
  have hexp : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (PMF.uniformOfFinset (Finset.univ : Finset (Fin m)) hs)
      (fun j => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAATrial A hA j₀ S j) (fun x => x.1.1 ∈ S))
    = ∑' j, (PMF.uniformOfFinset (Finset.univ : Finset (Fin m)) hs) j *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAATrial A hA j₀ S j) (fun x => x.1.1 ∈ S) := rfl
  rw [hexp, tsum_fintype, Finset.sum_congr rfl (fun j _ => by
    rw [uniform_apply_univ hm hs j]),
    ← Finset.mul_sum, Finset.sum_congr rfl (fun j _ =>
      (prepared_aa_trial_actual_metadata A j₀ S hA j).2.2)]

private theorem round_succ_split (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => ∃ y, out.1 = some y)
      = ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)
        + (1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)) *
          (((qSearchWindow l : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin (qSearchWindow l), ENNReal.ofReal
            (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ (j : ℕ)) (Ket j₀)) S)) := by
  rw [qSearchRound_eq]
  have houter : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (PMF.bind (preparedAATrial A hA j₀ S (⟨0, Nat.zero_lt_one⟩ : Fin 1))
      (fun st => if st.1.1 ∈ S then PMF.pure (some st.1.1, 1, 1)
        else PMF.bind
          (PMF.uniformOfFinset (Finset.univ : Finset (Fin (qSearchWindow l)))
            ⟨⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_one) (le_max_left 1
              ((6^l + 5^l - 1) / 5^l))⟩, Finset.mem_univ _⟩) fun j =>
          PMF.bind (preparedAATrial A hA j₀ S j) fun st2 =>
            PMF.pure (if st2.1.1 ∈ S then some st2.1.1 else none,
              2 + 2*j.val, 2 + j.val)))
      (fun out => ∃ y, out.1 = some y)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAATrial A hA j₀ S (⟨0, Nat.zero_lt_one⟩ : Fin 1))
          (fun st => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
            (if st.1.1 ∈ S then PMF.pure (some st.1.1, 1, 1)
              else PMF.bind
                (PMF.uniformOfFinset (Finset.univ : Finset (Fin (qSearchWindow l)))
                  ⟨⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_one) (le_max_left 1
                    ((6^l + 5^l - 1) / 5^l))⟩, Finset.mem_univ _⟩) fun j =>
                PMF.bind (preparedAATrial A hA j₀ S j) fun st2 =>
                  PMF.pure (if st2.1.1 ∈ S then some st2.1.1 else none,
                    2 + 2*j.val, 2 + j.val))
            (fun out => ∃ y, out.1 = some y)) := by
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
    exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
        (fun out => (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq _ _).symm)
  have hsplit : ∀ st : (I × ℕ) × ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (if st.1.1 ∈ S then PMF.pure (some st.1.1, 1, 1)
          else PMF.bind
            (PMF.uniformOfFinset (Finset.univ : Finset (Fin (qSearchWindow l)))
              ⟨⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_one) (le_max_left 1
                ((6^l + 5^l - 1) / 5^l))⟩, Finset.mem_univ _⟩) fun j =>
            PMF.bind (preparedAATrial A hA j₀ S j) fun st2 =>
              PMF.pure (if st2.1.1 ∈ S then some st2.1.1 else none,
                2 + 2*j.val, 2 + j.val))
        (fun out => ∃ y, out.1 = some y)
      = if st.1.1 ∈ S then (1:ℝ≥0∞) else
          (((qSearchWindow l : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin (qSearchWindow l), ENNReal.ofReal
            (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ (j : ℕ)) (Ket j₀)) S)) := by
    intro st
    by_cases hS : st.1.1 ∈ S
    · rw [if_pos hS, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
      rw [if_pos ⟨st.1.1, rfl⟩, if_pos hS]
    · rw [if_neg hS]
      have inner : ∀ j : Fin (qSearchWindow l),
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (PMF.bind (preparedAATrial A hA j₀ S j) fun st2 =>
              PMF.pure (if st2.1.1 ∈ S then some st2.1.1 else none, 2 + 2*j.val, 2 + j.val))
              (fun out => ∃ y, out.1 = some y)
            = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAATrial A hA j₀ S j) (fun x => x.1.1 ∈ S) := by
        intro j
        rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq]
        refine Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
            (fun a => ?_)
        rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
        by_cases h2 : a.1.1 ∈ S <;> simp [h2]
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind,
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr (fun j => (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq _ _).symm),
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr inner,
        uniform_trial_event A hA j₀ S (window_pos l), if_neg hS]
  rw [houter, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hsplit]
  have hfun : ∀ st : (I × ℕ) × ℕ,
      (if st.1.1 ∈ S then (1:ℝ≥0∞)
          else (((qSearchWindow l : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin (qSearchWindow l), ENNReal.ofReal
            (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ (j : ℕ)) (Ket j₀)) S)))
        = (if st.1.1 ∈ S then (1:ℝ≥0∞) else 0)
          + (if ¬ (st.1.1 ∈ S) then
              (((qSearchWindow l : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin (qSearchWindow l), ENNReal.ofReal
                (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ (j : ℕ)) (Ket j₀)) S))
            else 0) := by
    intro st; by_cases hS : st.1.1 ∈ S <;> simp [hS]
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hfun, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add,
    expectation_indicator_mul', expectation_indicator_mul',
    trial_zero_mass, trial_zero_compl]
  ring

private theorem round_avg_ge_quarter (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (θ : ℝ) (l : ℕ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2)
    (hmass : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2)
    (hmature : 1 ≤ (qSearchWindow l : ℝ)*Real.sin (2*θ)) :
    ENNReal.ofReal (1/4) ≤ ((qSearchWindow l : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin (qSearchWindow l),
      ENNReal.ofReal (MeasureProb (Run (preparedMark S)
        (preparedAACircuit A j₀ (j : ℕ)) (Ket j₀)) S) := by
  have hm : 0 < qSearchWindow l := window_pos l
  have hsum : ∑ j : Fin (qSearchWindow l), ENNReal.ofReal
      (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ (j : ℕ)) (Ket j₀)) S)
    = ENNReal.ofReal (∑ j : Fin (qSearchWindow l),
        MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ (j : ℕ)) (Ket j₀)) S) :=
    (ENNReal.ofReal_sum_of_nonneg (fun j _ => measureProb_nonneg _ _)).symm
  have hlow := prepared_aa_uniform_success_lower A j₀ S θ (qSearchWindow l) hA hm hθ0 hθ1 hmass
    hmature
  rw [le_div_iff₀ (by exact_mod_cast hm : (0:ℝ) < (qSearchWindow l : ℝ))] at hlow
  have hkey : ENNReal.ofReal ((1/4:ℝ)) * ((qSearchWindow l : ℕ):ℝ≥0∞)
      ≤ ∑ j : Fin (qSearchWindow l), ENNReal.ofReal
        (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ (j : ℕ)) (Ket j₀)) S) := by
    rw [hsum]
    calc ENNReal.ofReal ((1/4:ℝ)) * ((qSearchWindow l : ℕ):ℝ≥0∞)
        = ENNReal.ofReal ((1/4:ℝ) * ((qSearchWindow l : ℕ):ℝ)) := by
          rw [show ((qSearchWindow l : ℕ):ℝ≥0∞) = ENNReal.ofReal (((qSearchWindow l : ℕ):ℝ)) from
            (ENNReal.ofReal_natCast _).symm,
            ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/4)]
      _ ≤ ENNReal.ofReal (∑ j : Fin (qSearchWindow l),
          MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ (j : ℕ)) (Ket j₀)) S) :=
          ENNReal.ofReal_le_ofReal (by linarith)
  calc ENNReal.ofReal ((1/4:ℝ))
      = ENNReal.ofReal ((1/4:ℝ)) * (((qSearchWindow l : ℕ):ℝ≥0∞) * ((qSearchWindow l : ℕ):ℝ≥0∞)⁻¹) := by
        rw [ENNReal.mul_inv_cancel (by exact_mod_cast (Nat.ne_of_gt hm))
          (ENNReal.natCast_ne_top _), mul_one]
    _ = (ENNReal.ofReal ((1/4:ℝ)) * ((qSearchWindow l : ℕ):ℝ≥0∞))
        * ((qSearchWindow l : ℕ):ℝ≥0∞)⁻¹ := by ring
    _ ≤ (∑ j : Fin (qSearchWindow l), ENNReal.ofReal
          (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ (j : ℕ)) (Ket j₀)) S))
        * ((qSearchWindow l : ℕ):ℝ≥0∞)⁻¹ := mul_le_mul' hkey (le_refl _)
    _ = ((qSearchWindow l : ℕ):ℝ≥0∞)⁻¹ * ∑ j : Fin (qSearchWindow l), ENNReal.ofReal
          (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ (j : ℕ)) (Ket j₀)) S) := by
        ring

private theorem round_fail (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => out.1 = none)
      ≤ 1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S) := by
  have hge : ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => ∃ y, out.1 = some y) := by
    rw [round_succ_split A hA j₀ S l]
    exact le_add_of_nonneg_right (by simp)
  have hpart := event_compl (qSearchRound A hA j₀ S l) (fun out => ∃ y, out.1 = some y)
  refine ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top ?_
  have hcongr : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => ¬ ∃ y, out.1 = some y)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => out.1 = none) :=
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr (fun out => by
      constructor
      · intro h
        cases ho : out.1 with
        | none => rfl
        | some y => exact absurd ⟨y, ho⟩ h
      · intro h hex
        obtain ⟨y, hy⟩ := hex
        rw [h] at hy
        exact absurd hy (by simp))
  rw [hcongr] at hpart
  calc ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)
      + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => out.1 = none)
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => ∃ y, out.1 = some y)
          + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => out.1 = none) :=
          add_le_add hge (le_refl _)
    _ = 1 := hpart

private theorem round_fail_mature (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (θ : ℝ) (l : ℕ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2)
    (hmass : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2)
    (hmature : 1 ≤ (qSearchWindow l : ℝ)*Real.sin (2*θ)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => out.1 = none)
      ≤ ENNReal.ofReal (3/4) := by
  have ha0 : (0:ℝ) ≤ MeasureProb (preparedAAState A j₀) S := measureProb_nonneg _ _
  have ha1 : MeasureProb (preparedAAState A j₀) S ≤ 1 :=
    measureProb_le_one ((prepared_aa_reflection_and_access A j₀ S hA).2.1) S
  have havg := round_avg_ge_quarter A hA j₀ S θ l hθ0 hθ1 hmass hmature
  have hsplit := round_succ_split A hA j₀ S l
  have hge : ENNReal.ofReal (1/4)
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => ∃ y, out.1 = some y) := by
    rw [hsplit]
    have hstep : (1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S))
        * (((qSearchWindow l : ℕ) : ℝ≥0∞)⁻¹ * ∑ j : Fin (qSearchWindow l), ENNReal.ofReal
            (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ (j : ℕ)) (Ket j₀)) S))
      ≥ (1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)) * ENNReal.ofReal (1/4) :=
      mul_le_mul' (le_refl _) havg
    have hex : ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)
        + (1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)) * ENNReal.ofReal ((1/4:ℝ))
      = ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S
          + (1 - MeasureProb (preparedAAState A j₀) S) * (1/4)) := by
      rw [show (1:ℝ≥0∞) = ENNReal.ofReal ((1:ℝ)) from ENNReal.ofReal_one.symm,
        ← ENNReal.ofReal_sub 1 ha0,
        ← ENNReal.ofReal_mul (sub_nonneg.mpr ha1),
        ← ENNReal.ofReal_add ha0
          (mul_nonneg (sub_nonneg.mpr ha1) (by norm_num))]
    have hfin : (1/4:ℝ) ≤ MeasureProb (preparedAAState A j₀) S
        + (1 - MeasureProb (preparedAAState A j₀) S) * (1/4) := by nlinarith
    calc ENNReal.ofReal ((1/4:ℝ))
        ≤ ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S)
          + (1 - ENNReal.ofReal (MeasureProb (preparedAAState A j₀) S))
            * ENNReal.ofReal ((1/4:ℝ)) := by
          rw [hex]
          exact ENNReal.ofReal_le_ofReal hfin
      _ ≤ _ := add_le_add (le_refl _) hstep
  have hpart := event_compl (qSearchRound A hA j₀ S l) (fun out => ∃ y, out.1 = some y)
  have hcongr : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => ¬ ∃ y, out.1 = some y)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => out.1 = none) :=
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr (fun out => by
      constructor
      · intro h
        cases ho : out.1 with
        | none => rfl
        | some y => exact absurd ⟨y, ho⟩ h
      · intro h hex
        obtain ⟨y, hy⟩ := hex
        rw [h] at hy
        exact absurd hy (by simp))
  rw [hcongr] at hpart
  have hrw : ENNReal.ofReal ((3/4:ℝ)) = (1:ℝ≥0∞) - ENNReal.ofReal ((1/4:ℝ)) := by
    rw [show (1:ℝ≥0∞) = ENNReal.ofReal ((1:ℝ)) from ENNReal.ofReal_one.symm,
      ← ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 1/4)]
    congr 1
    norm_num
  rw [hrw]
  refine ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top ?_
  calc ENNReal.ofReal ((1/4:ℝ))
      + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => out.1 = none)
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => ∃ y, out.1 = some y)
          + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => out.1 = none) :=
          add_le_add hge (le_refl _)
    _ = 1 := hpart

private theorem round_none_of_zero (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ)
    (ha : MeasureProb (preparedAAState A j₀) S = 0) :
    ∀ out ∈ (qSearchRound A hA j₀ S l).support, out.1 = none := by
  have hzero : ∀ (m : ℕ) (i : Fin m),
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAATrial A hA j₀ S i) (fun x => x.1.1 ∈ S) = 0 := by
    intro m i
    rw [(prepared_aa_trial_actual_metadata A j₀ S hA i).2.2,
      (prepared_aa_endpoint_states A j₀ S (i : ℕ) hA).1 ha, ha, ENNReal.ofReal_zero]
  intro out hout
  rw [qSearchRound_eq] at hout
  obtain ⟨st, hst, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have hstS : ¬ st.1.1 ∈ S := event_zero_nosup _ _ (hzero _ _) st hst
  rw [if_neg hstS] at hout
  obtain ⟨j, hj, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨st2, hst2, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have hst2S : ¬ st2.1.1 ∈ S := event_zero_nosup _ _ (hzero _ _) st2 hst2
  have hout' : out = (if st2.1.1 ∈ S then some st2.1.1 else none, 2 + 2*j.val, 2 + j.val) := by
    simpa [PMF.mem_support_pure_iff] using hout
  rw [hout', if_neg hst2S]

private theorem round_cost1 (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchRound A hA j₀ S l) (fun out => (out.2.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal (4 * ((6/5:ℝ)^l)) := by
  refine le_trans (expectation_le_of_support (qSearchRound A hA j₀ S l)
    (fun out => (out.2.1 : ℝ≥0∞)) ((2 * qSearchWindow l : ℕ) : ℝ≥0∞) ?_) ?_
  · intro out hout
    show ((out.2.1 : ℕ) : ℝ≥0∞) ≤ ((2 * qSearchWindow l : ℕ) : ℝ≥0∞)
    exact_mod_cast (round_shape A hA j₀ S l out hout).2.1
  · have h1 : ((2 * qSearchWindow l : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal (((2 * qSearchWindow l : ℕ):ℝ)) := (ENNReal.ofReal_natCast _).symm
    rw [h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have hw := window_le l
    have hge := geopow_ge_one l
    have hsplit : (((2 * qSearchWindow l : ℕ):ℝ)) = 2 * ((qSearchWindow l : ℕ):ℝ) := by
      push_cast
      ring
    rw [hsplit]
    nlinarith

private theorem round_cost2 (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (l : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchRound A hA j₀ S l) (fun out => (out.2.2 : ℝ≥0∞))
      ≤ ENNReal.ofReal (4 * ((6/5:ℝ)^l)) := by
  refine le_trans (expectation_le_of_support (qSearchRound A hA j₀ S l)
    (fun out => (out.2.2 : ℝ≥0∞)) ((2 * qSearchWindow l : ℕ) : ℝ≥0∞) ?_) ?_
  · intro out hout
    show ((out.2.2 : ℕ) : ℝ≥0∞) ≤ ((2 * qSearchWindow l : ℕ) : ℝ≥0∞)
    exact_mod_cast (round_shape A hA j₀ S l out hout).2.2
  · have h1 : ((2 * qSearchWindow l : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal (((2 * qSearchWindow l : ℕ):ℝ)) := (ENNReal.ofReal_natCast _).symm
    rw [h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have hw := window_le l
    have hge := geopow_ge_one l
    have hsplit : (((2 * qSearchWindow l : ℕ):ℝ)) = 2 * ((qSearchWindow l : ℕ):ℝ) := by
      push_cast
      ring
    rw [hsplit]
    nlinarith

end Round

section Loop
variable {I : Type} [Fintype I] [DecidableEq I]

private theorem qSearchLoop_zero_eq (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (off : ℕ) :
    qSearchLoop A hA j₀ S 0 off = PMF.pure (none, 0, 0) := by simp [qSearchLoop]

private noncomputable def loopCont {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (T off : ℕ) (out : Option I × ℕ × ℕ) : PMF (Option I × ℕ × ℕ) :=
  match out.1 with
  | some _ => PMF.pure out
  | none => PMF.map (fun r => (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2))
      (qSearchLoop A hA j₀ S T (off+1))

private theorem qSearchLoop_succ_eq (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (T off : ℕ) :
    qSearchLoop A hA j₀ S (T+1) off =
      PMF.bind (qSearchRound A hA j₀ S (off+1)) (loopCont A hA j₀ S T off) := by
  rw [qSearchLoop]
  congr 1

private theorem loop_expect_zero1 (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (off : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S 0 off) (fun out => (out.2.1 : ℝ≥0∞)) = 0 := by
  rw [qSearchLoop_zero_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
  norm_num

private theorem loop_expect_zero2 (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (off : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S 0 off) (fun out => (out.2.2 : ℝ≥0∞)) = 0 := by
  rw [qSearchLoop_zero_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
  norm_num

private theorem loop_expect_succ1 (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (T off : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S (T+1) off) (fun out => (out.2.1 : ℝ≥0∞))
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchRound A hA j₀ S (off+1)) (fun out => (out.2.1 : ℝ≥0∞))
        + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S (off+1)) (fun out => out.1 = none)
          * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S T (off+1))
              (fun out => (out.2.1 : ℝ≥0∞)) := by
  rw [qSearchLoop_succ_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  have hsplit : ∀ out : Option I × ℕ × ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (loopCont A hA j₀ S T off out) (fun o => (o.2.1 : ℝ≥0∞))
        = (out.2.1 : ℝ≥0∞)
          + (if out.1 = none then
              Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S T (off+1))
                (fun out => (out.2.1 : ℝ≥0∞))
            else 0) := by
    intro out
    obtain ⟨o1, o2, o3⟩ := out
    cases o1 with
    | none =>
        show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
            (PMF.map (fun r => (r.1, r.2.1 + o2, r.2.2 + o3)) (qSearchLoop A hA j₀ S T (off+1)))
            (fun o => (o.2.1 : ℝ≥0∞))
          = ((o2 : ℕ) : ℝ≥0∞)
            + (if (none : Option I) = none then
                Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S T (off+1))
                  (fun out => (out.2.1 : ℝ≥0∞))
              else 0)
        have hfun : ∀ r : Option I × ℕ × ℕ,
            (((r.1, r.2.1 + o2, r.2.2 + o3)).2.1 : ℝ≥0∞)
              = ((r.2.1 : ℕ) : ℝ≥0∞) + ((o2 : ℕ) : ℝ≥0∞) := by
          intro r
          rw [show (((r.1, r.2.1 + o2, r.2.2 + o3)).2.1 : ℕ) = r.2.1 + o2 from rfl, Nat.cast_add]
        rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hfun,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const, if_pos rfl]
        ring
    | some y =>
        show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (PMF.pure (some y, o2, o3))
            (fun o => (o.2.1 : ℝ≥0∞))
          = ((o2 : ℕ) : ℝ≥0∞)
            + (if (some y : Option I) = none then
                Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S T (off+1))
                  (fun out => (out.2.1 : ℝ≥0∞))
              else 0)
        rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, if_neg (by simp)]
        ring
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hsplit, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add,
    expectation_indicator_mul']
  ring

private theorem loop_expect_succ2 (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (T off : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S (T+1) off) (fun out => (out.2.2 : ℝ≥0∞))
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchRound A hA j₀ S (off+1)) (fun out => (out.2.2 : ℝ≥0∞))
        + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S (off+1)) (fun out => out.1 = none)
          * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S T (off+1))
              (fun out => (out.2.2 : ℝ≥0∞)) := by
  rw [qSearchLoop_succ_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  have hsplit : ∀ out : Option I × ℕ × ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (loopCont A hA j₀ S T off out) (fun o => (o.2.2 : ℝ≥0∞))
        = (out.2.2 : ℝ≥0∞)
          + (if out.1 = none then
              Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S T (off+1))
                (fun out => (out.2.2 : ℝ≥0∞))
            else 0) := by
    intro out
    obtain ⟨o1, o2, o3⟩ := out
    cases o1 with
    | none =>
        show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
            (PMF.map (fun r => (r.1, r.2.1 + o2, r.2.2 + o3)) (qSearchLoop A hA j₀ S T (off+1)))
            (fun o => (o.2.2 : ℝ≥0∞))
          = ((o3 : ℕ) : ℝ≥0∞)
            + (if (none : Option I) = none then
                Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S T (off+1))
                  (fun out => (out.2.2 : ℝ≥0∞))
              else 0)
        have hfun : ∀ r : Option I × ℕ × ℕ,
            (((r.1, r.2.1 + o2, r.2.2 + o3)).2.2 : ℝ≥0∞)
              = ((r.2.2 : ℕ) : ℝ≥0∞) + ((o3 : ℕ) : ℝ≥0∞) := by
          intro r
          rw [show (((r.1, r.2.1 + o2, r.2.2 + o3)).2.2 : ℕ) = r.2.2 + o3 from rfl, Nat.cast_add]
        rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hfun,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const, if_pos rfl]
        ring
    | some y =>
        show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (PMF.pure (some y, o2, o3))
            (fun o => (o.2.2 : ℝ≥0∞))
          = ((o3 : ℕ) : ℝ≥0∞)
            + (if (some y : Option I) = none then
                Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S T (off+1))
                  (fun out => (out.2.2 : ℝ≥0∞))
              else 0)
        rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, if_neg (by simp)]
        ring
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hsplit, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add,
    expectation_indicator_mul']
  ring

private theorem loop_shape (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) :
    ∀ (T off : ℕ) (out : Option I × ℕ × ℕ), out ∈ (qSearchLoop A hA j₀ S T off).support →
    ∀ y, out.1 = some y → y ∈ S := by
  intro T
  induction T with
  | zero =>
      intro off out hout y hy
      rw [qSearchLoop_zero_eq] at hout
      have hout' : out = (none, 0, 0) := by simpa [PMF.mem_support_pure_iff] using hout
      subst hout'
      exact absurd hy (by simp)
  | succ T ih =>
      intro off out hout y hy
      rw [qSearchLoop_succ_eq] at hout
      obtain ⟨out1, hout1, hout2⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨o1, o2, o3⟩ := out1
      cases o1 with
      | none =>
          obtain ⟨r, hr, hgr⟩ := (PMF.mem_support_map_iff _ _ _).mp hout2
          refine ih (off+1) r hr y ?_
          have hout1' : out.1 = r.1 := by rw [← hgr]
          rw [← hout1']
          exact hy
      | some z =>
          have hpure : out ∈ (PMF.pure (some z, o2, o3)).support := hout2
          have hout2' : out = (some z, o2, o3) := by
            simpa [PMF.mem_support_pure_iff] using hpure
          subst hout2'
          exact (round_shape A hA j₀ S (off+1) _ hout1).1 y hy

private theorem loop_none_of_zero (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (ha : MeasureProb (preparedAAState A j₀) S = 0) :
    ∀ (T off : ℕ) (out : Option I × ℕ × ℕ), out ∈ (qSearchLoop A hA j₀ S T off).support →
    out.1 = none := by
  intro T
  induction T with
  | zero =>
      intro off out hout
      rw [qSearchLoop_zero_eq] at hout
      obtain ⟨rfl⟩ : out = (none, 0, 0) := by simpa [PMF.mem_support_pure_iff] using hout
      rfl
  | succ T ih =>
      intro off out hout
      rw [qSearchLoop_succ_eq] at hout
      obtain ⟨out1, hout1, hout2⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨o1, o2, o3⟩ := out1
      have hnone1 := round_none_of_zero A hA j₀ S (off+1) ha (o1, o2, o3) hout1
      have ho1 : o1 = none := hnone1
      subst ho1
      obtain ⟨r, hr, hgr⟩ := (PMF.mem_support_map_iff _ _ _).mp hout2
      have hout1' : out.1 = r.1 := by rw [← hgr]
      rw [hout1']
      exact ih (off+1) r hr

end Loop

private theorem exists_crossing {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∃ ls : ℕ, 1 ≤ ls ∧ ((6/5:ℝ)^ls)*s ≤ 6/5 ∧ ∀ l : ℕ, ls ≤ l → 1 ≤ ((6/5:ℝ)^l)*s := by
  have hex : ∃ k : ℕ, 1 ≤ k ∧ 1 ≤ ((6/5:ℝ)^k)*s := exists_geometric_cross hs0
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, ?_⟩
  · rcases Nat.lt_or_ge 1 (Nat.find hex) with h2 | h2
    · have hmin : ¬ (1 ≤ (Nat.find hex) - 1 ∧ 1 ≤ ((6/5:ℝ)^((Nat.find hex) - 1))*s) :=
        Nat.find_min hex (by omega)
      have hlt : ((6/5:ℝ)^((Nat.find hex) - 1))*s < 1 := by
        by_cases hc : ((6/5:ℝ)^((Nat.find hex) - 1))*s < 1
        · exact hc
        · push Not at hc
          exact absurd ⟨by omega, hc⟩ hmin
      have hexp : ((6/5:ℝ)^(Nat.find hex))*s
          = (6/5:ℝ)*(((6/5:ℝ)^((Nat.find hex) - 1))*s) := by
        have h := pow_succ (6/5:ℝ) ((Nat.find hex) - 1)
        rw [show (Nat.find hex) - 1 + 1 = Nat.find hex from by omega] at h
        rw [h]
        ring
      rw [hexp]
      calc (6/5:ℝ)*(((6/5:ℝ)^((Nat.find hex) - 1))*s)
          ≤ (6/5:ℝ)*1 := mul_le_mul_of_nonneg_left (le_of_lt hlt) (by norm_num)
        _ = 6/5 := mul_one _
    · have h1 : Nat.find hex = 1 := le_antisymm h2 (Nat.find_spec hex).1
      rw [h1, pow_one]
      calc (6/5:ℝ)*s ≤ (6/5:ℝ)*1 := mul_le_mul_of_nonneg_left hs1 (by norm_num)
        _ = 6/5 := mul_one _
  · intro l hl
    have hmono : ((6/5:ℝ)^(Nat.find hex)) ≤ ((6/5:ℝ)^l) := geopow_mono hl
    calc (1:ℝ) ≤ ((6/5:ℝ)^(Nat.find hex))*s := (Nat.find_spec hex).2
      _ ≤ ((6/5:ℝ)^l)*s := mul_le_mul_of_nonneg_right hmono (le_of_lt hs0)

private theorem ledger_bound {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (L : Option I × ℕ × ℕ → ℕ)
    (hrec : ∀ (T off : ℕ), Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S (T+1) off)
        (fun out => (L out : ℝ≥0∞))
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchRound A hA j₀ S (off+1)) (fun out => (L out : ℝ≥0∞))
        + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S (off+1)) (fun out => out.1 = none)
          * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S T (off+1))
              (fun out => (L out : ℝ≥0∞)))
    (hzero : ∀ off : ℕ, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S 0 off)
        (fun out => (L out : ℝ≥0∞)) = 0)
    (hcost : ∀ l : ℕ, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchRound A hA j₀ S l)
        (fun out => (L out : ℝ≥0∞)) ≤ ENNReal.ofReal (4 * ((6/5:ℝ)^l)))
    (ha0 : (0:ℝ) ≤ MeasureProb (preparedAAState A j₀) S)
    (ha1 : MeasureProb (preparedAAState A j₀) S ≤ 1) (T : ℕ)
    (ha : 0 < MeasureProb (preparedAAState A j₀) S) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S T 0) (fun out => (L out : ℝ≥0∞))
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) := by
  have hsqrt : (0:ℝ) < Real.sqrt (MeasureProb (preparedAAState A j₀) S) :=
    Real.sqrt_pos.mpr ha
  rcases lt_or_ge (MeasureProb (preparedAAState A j₀) S) (3/4) with h34 | h43
  · have hsqlt : Real.sqrt (MeasureProb (preparedAAState A j₀) S) < 1 := by
      rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 1)]
      linarith
    have hsθ : Real.sin (Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S)))
        = Real.sqrt (MeasureProb (preparedAAState A j₀) S) :=
      Real.sin_arcsin (le_trans (by norm_num : (-1:ℝ) ≤ 0) (Real.sqrt_nonneg _))
        (Real.sqrt_le_one.mpr ha1)
    have hθ0 : 0 < Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S)) :=
      Real.arcsin_pos.mpr hsqrt
    have hθ1 : Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S)) < Real.pi/2 :=
      Real.arcsin_lt_pi_div_two.mpr hsqlt
    have hmass : MeasureProb (preparedAAState A j₀) S
        = (Real.sin (Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))))^2 := by
      rw [hsθ, Real.sq_sqrt ha0]
    have hsin2 : Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S)))
        = 2 * Real.sqrt (MeasureProb (preparedAAState A j₀) S)
            * Real.sqrt (1 - MeasureProb (preparedAAState A j₀) S) := by
      rw [Real.sin_two_mul, hsθ, Real.cos_arcsin, Real.sq_sqrt ha0]
    have hsin2pos : 0 < Real.sin
        (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) := by
      rw [hsin2]
      exact mul_pos (mul_pos (by norm_num) hsqrt)
        (Real.sqrt_pos.mpr (by linarith))
    have hge : Real.sqrt (MeasureProb (preparedAAState A j₀) S)
        ≤ Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) := by
      rw [hsin2]
      have h1a : (1:ℝ)/2 ≤ Real.sqrt (1 - MeasureProb (preparedAAState A j₀) S) := by
        have hq : ((1:ℝ)/2)^2 ≤ 1 - MeasureProb (preparedAAState A j₀) S := by
          nlinarith [h34]
        calc (1:ℝ)/2 = Real.sqrt (((1:ℝ)/2)^2) := (Real.sqrt_sq (by norm_num)).symm
          _ ≤ Real.sqrt (1 - MeasureProb (preparedAAState A j₀) S) := Real.sqrt_le_sqrt hq
      have hkey : (0:ℝ) ≤ Real.sqrt (MeasureProb (preparedAAState A j₀) S)
          * (2 * Real.sqrt (1 - MeasureProb (preparedAAState A j₀) S) - 1) :=
        mul_nonneg (Real.sqrt_nonneg _) (by nlinarith)
      nlinarith [hkey]
    obtain ⟨ls, hls1, hlsbound, hlsmature⟩ := exists_crossing hsin2pos (Real.sin_le_one _)
    have hwinmat : ∀ l : ℕ, ls ≤ l → 1 ≤ (qSearchWindow l : ℝ)
        *Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) := by
      intro l hl
      have h1 : 1 ≤ ((6/5:ℝ)^l)
          *Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) :=
        hlsmature l hl
      calc (1:ℝ) ≤ ((6/5:ℝ)^l)
          *Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) := h1
        _ ≤ (qSearchWindow l : ℝ)
            *Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) :=
            mul_le_mul_of_nonneg_right (window_ge l) (le_of_lt hsin2pos)
    have hfailm : ∀ l : ℕ, ls ≤ l →
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => out.1 = none)
          ≤ ENNReal.ofReal (3/4) := fun l hl =>
      round_fail_mature A hA j₀ S
        (Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) l hθ0 hθ1 hmass
        (hwinmat l hl)
    have hmature := closed_mature (ls := ls)
      (E := fun T' off' => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S T' off')
        (fun out => (L out : ℝ≥0∞)))
      (Ec := fun l => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchRound A hA j₀ S l)
        (fun out => (L out : ℝ≥0∞)))
      (F := fun l => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => out.1 = none))
      hrec hzero hcost hfailm
    have himm := closed_immature (ls := ls)
      (E := fun T' off' => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S T' off')
        (fun out => (L out : ℝ≥0∞)))
      (Ec := fun l => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchRound A hA j₀ S l)
        (fun out => (L out : ℝ≥0∞)))
      (F := fun l => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => out.1 = none))
      hrec hzero hcost (fun l => Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _) hfailm hmature
    have himm0 := himm T 0 (by omega)
    have hle := le_trans (le_add_right (le_refl _)) himm0
    refine le_trans hle ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hkey : ((6/5:ℝ)^ls)
        ≤ (6/5:ℝ)/Real.sqrt (MeasureProb (preparedAAState A j₀) S) := by
      rw [le_div_iff₀ hsqrt]
      calc ((6/5:ℝ)^ls) * Real.sqrt (MeasureProb (preparedAAState A j₀) S)
          ≤ ((6/5:ℝ)^ls)
              *Real.sin (2*Real.arcsin (Real.sqrt (MeasureProb (preparedAAState A j₀) S))) :=
            mul_le_mul_of_nonneg_left hge (pow_nonneg (by norm_num : (0:ℝ) ≤ 6/5) ls)
        _ ≤ 6/5 := hlsbound
    have h1 : (64:ℝ) * ((6/5:ℝ)^ls)
        ≤ 64 * ((6/5:ℝ)/Real.sqrt (MeasureProb (preparedAAState A j₀) S)) :=
      mul_le_mul_of_nonneg_left hkey (by norm_num)
    have h2 : (64:ℝ) * ((6/5:ℝ)/Real.sqrt (MeasureProb (preparedAAState A j₀) S))
        ≤ 400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S) := by
      rw [le_div_iff₀ hsqrt]
      rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hsqrt)]
      norm_num
    exact le_trans h1 h2
  · have hfail : ∀ l : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => out.1 = none)
          ≤ ENNReal.ofReal (1/4) := by
      intro l
      refine le_trans (round_fail A hA j₀ S l) ?_
      rw [show (1:ℝ≥0∞) = ENNReal.ofReal ((1:ℝ)) from ENNReal.ofReal_one.symm,
        ← ENNReal.ofReal_sub 1 ha0]
      refine ENNReal.ofReal_le_ofReal ?_
      linarith
    have hE := closed_quarter
      (E := fun T' off' => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchLoop A hA j₀ S T' off')
        (fun out => (L out : ℝ≥0∞)))
      (Ec := fun l => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (qSearchRound A hA j₀ S l)
        (fun out => (L out : ℝ≥0∞)))
      (F := fun l => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (qSearchRound A hA j₀ S l) (fun out => out.1 = none))
      hrec hzero hcost hfail T 0
    refine le_trans hE ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hp : ((6/5:ℝ)^(0+1)) = 6/5 := by rw [Nat.zero_add, pow_one]
    have h400 : (400:ℝ) ≤ 400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S) := by
      rw [le_div_iff₀ hsqrt]
      nlinarith [Real.sqrt_le_one.mpr ha1]
    rw [hp]
    linarith

theorem bhmt_theorem3_qsearch : ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (T : ℕ),
    let a : ℝ := MeasureProb (preparedAAState A j₀) S
    let p := qSearchLoop A hA j₀ S T 0
    (∀ out ∈ PMF.support p, ∀ y, out.1 = some y → y ∈ S) ∧
    (a = 0 → ∀ out ∈ PMF.support p, out.1 = none) ∧
    (0 < a →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun out => (out.2.1 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt a) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun out => (out.2.2 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt a)) := by
  intro I _ _ A hA j₀ S T
  have ha0 : (0:ℝ) ≤ MeasureProb (preparedAAState A j₀) S := measureProb_nonneg _ _
  have ha1 : MeasureProb (preparedAAState A j₀) S ≤ 1 :=
    measureProb_le_one ((prepared_aa_reflection_and_access A j₀ S hA).2.1) S
  exact ⟨loop_shape A hA j₀ S T 0,
    fun ha => loop_none_of_zero A hA j₀ S ha T 0,
    fun ha => ⟨ledger_bound A hA j₀ S (fun out => out.2.1)
      (loop_expect_succ1 A hA j₀ S) (loop_expect_zero1 A hA j₀ S)
      (round_cost1 A hA j₀ S) ha0 ha1 T ha,
    ledger_bound A hA j₀ S (fun out => out.2.2)
      (loop_expect_succ2 A hA j₀ S) (loop_expect_zero2 A hA j₀ S)
      (round_cost2 A hA j₀ S) ha0 ha1 T ha⟩⟩

theorem bhmt_theorem3_qsearch_contract :
    Theorem3QSearchSpec.expected :=
  bhmt_theorem3_qsearch

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch
