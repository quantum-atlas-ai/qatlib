/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WaterLevel.WaterPrecision.Defs

/-!
# Perturbation bounds for water-level fidelity

Theorems `g1` and `g2` propagate coordinatewise table errors through clipped fills, mass,
overlap, and normalized fidelity, with a positive mass lower bound controlling the quotient.
Theorem `g3` certifies the signs returned by a rational residual test and bounds the uncertainty
when it returns no answer.

These estimates support the water-level viewpoint of quantum rejection sampling
[OzolsRoettelerRoland2013], developed by [Ozols et al., 2013][OzolsRoettelerRoland2013].
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.WaterLevel.WaterPrecision
open Qatlib.Concepts.WaterLevel.WaterPrecision Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Taking the minimum of two real inputs preserves a common absolute perturbation bound on the
two arguments. -/
private theorem min_error (a b c d e : ℝ) (hac : |a-c| ≤ e) (hbd : |b-d| ≤ e) :
    |min a b - min c d| ≤ e := by
  obtain ⟨hac₁,hac₂⟩ := abs_le.mp hac
  obtain ⟨hbd₁,hbd₂⟩ := abs_le.mp hbd
  have hupper : min a b-e ≤ min c d :=
    le_min (by linarith [min_le_left a b]) (by linarith [min_le_right a b])
  have hlower : min c d-e ≤ min a b :=
    le_min (by linarith [min_le_left c d]) (by linarith [min_le_right c d])
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- For bounded nonnegative tables and a nonnegative level, each clipped fill lies between zero
and the table bound `B`. -/
private theorem fill_bounds {m : ℕ} {p s : Fin m → ℝ} {B γ : ℝ}
    (h : TableBound p s B) (hγ : 0 ≤ γ) (i : Fin m) :
    0 ≤ realFill p s γ i ∧ realFill p s γ i ≤ B := by
  exact ⟨le_min (h i).1 (mul_nonneg hγ (h i).2.2.1),
    (min_le_left _ _).trans (h i).2.1⟩

/-- If two values lie in `[0, B]` and differ by at most a nonnegative `e`, their squares differ
by at most `2 * B * e`. -/
private theorem square_error (a b B e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haB : a ≤ B) (hbB : b ≤ B) (he : 0 ≤ e) (hab : |a-b| ≤ e) :
    |a^2-b^2| ≤ 2*B*e := by
  rw [show a^2-b^2=(a-b)*(a+b) by ring, abs_mul, abs_of_nonneg (add_nonneg ha hb)]
  calc
    _ ≤ e*(a+b) := mul_le_mul_of_nonneg_right hab (add_nonneg ha hb)
    _ ≤ e*(2*B) := mul_le_mul_of_nonneg_left (by linarith) he
    _ = _ := by ring

/-- For nonnegative tables bounded by `B` and a nonnegative level, the fill overlap lies between
zero and `m * B^2`. -/
private theorem dot_bounds {m : ℕ} {p s : Fin m → ℝ} {B γ : ℝ}
    (hB : 0 ≤ B) (hγ : 0 ≤ γ) (h : TableBound p s B) :
    0 ≤ realDot p s γ ∧ realDot p s γ ≤ (m:ℝ)*B^2 := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (h i).2.2.1 (fill_bounds h hγ i).1)
  · calc
      _ ≤ ∑ _i : Fin m, B^2 := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [(fill_bounds h hγ i).1, (fill_bounds h hγ i).2,
          (h i).2.2.1, (h i).2.2.2,
          mul_le_mul (h i).2.2.2 (fill_bounds h hγ i).2 (fill_bounds h hγ i).1 hB]
      _ = _ := by simp

/-- Propagates coordinatewise input error through clipped fills, squared mass, and target
overlap using `fillError`, `massError`, and `dotError`. Both tables must satisfy the same
nonnegative bound, and the level must lie in `[0, L]`. -/
theorem g1 :
  ∀ (m : ℕ) (p s p' s' : Fin m→ℝ) (B L δ γ : ℝ),
    0≤B → 0≤L → 0≤δ → 0≤γ → γ≤L → TableBound p s B → TableBound p' s' B → inputError p s p' s' δ →
    (∀ i, |realFill p s γ i-realFill p' s' γ i|≤fillError L δ) ∧
    |realMass p s γ-realMass p' s' γ|≤massError m B L δ ∧
    |realDot p s γ-realDot p' s' γ|≤dotError m B L δ := by
  intro m p s p' s' B L δ γ hB hL hδ hγ hγL hp hp' hi
  have he : 0 ≤ fillError L δ := by dsimp [fillError]; positivity
  have hf (i : Fin m) : |realFill p s γ i-realFill p' s' γ i| ≤ fillError L δ := by
    apply min_error
    · exact (hi i).1.trans (by dsimp [fillError]; nlinarith [mul_nonneg hL hδ])
    · rw [← mul_sub, abs_mul, abs_of_nonneg hγ]
      calc
        _ ≤ γ*δ := mul_le_mul_of_nonneg_left (hi i).2 hγ
        _ ≤ fillError L δ := by dsimp [fillError]; nlinarith [mul_le_mul_of_nonneg_right hγL hδ]
  refine ⟨hf, ?_, ?_⟩
  · unfold realMass
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i : Fin m, |realFill p s γ i^2-realFill p' s' γ i^2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin m, 2*B*fillError L δ := by
        apply Finset.sum_le_sum
        intro i _
        exact square_error _ _ _ _ (fill_bounds hp hγ i).1 (fill_bounds hp' hγ i).1
          (fill_bounds hp hγ i).2 (fill_bounds hp' hγ i).2 he (hf i)
      _ = massError m B L δ := by simp [massError]; ring
  · unfold realDot
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i : Fin m, |s i*realFill p s γ i-s' i*realFill p' s' γ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin m, B*(fillError L δ+δ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [show s i*realFill p s γ i-s' i*realFill p' s' γ i =
          s i*(realFill p s γ i-realFill p' s' γ i)+(s i-s' i)*realFill p' s' γ i by ring]
        calc
          _ ≤ |s i*(realFill p s γ i-realFill p' s' γ i)|+
              |(s i-s' i)*realFill p' s' γ i| := abs_add_le _ _
          _ = s i*|realFill p s γ i-realFill p' s' γ i|+
              |s i-s' i| *realFill p' s' γ i := by
            rw [abs_mul,abs_mul,abs_of_nonneg (hp i).2.2.1,abs_of_nonneg (fill_bounds hp' hγ i).1]
          _ ≤ B*fillError L δ+δ*B := add_le_add
            (mul_le_mul (hp i).2.2.2 (hf i) (abs_nonneg _) hB)
            (mul_le_mul (hi i).2 (fill_bounds hp' hγ i).2 (fill_bounds hp' hγ i).1 hδ)
          _ = _ := by ring
      _ = dotError m B L δ := by simp [dotError]; ring

/-- Bounds the perturbation of `a^2 / u` when nonnegative numerators are bounded by `K` and both
denominators are at least a positive `r`. The estimate separates numerator error and
denominator error with factors `1 / r` and `1 / r^2`. -/
private theorem quotient_error (a b u v K ed em r : ℝ)
    (ha : 0≤a) (hb : 0≤b) (haK : a≤K) (hbK : b≤K)
    (hed : 0≤ed) (hem : 0≤em) (hr : 0<r) (hu : r≤u) (hv : r≤v)
    (hd : |a-b|≤ed) (hm : |u-v|≤em) :
    |a^2/u-b^2/v| ≤ 2*K*ed/r+K^2*em/r^2 := by
  have hu0 : 0<u := hr.trans_le hu
  have hv0 : 0<v := hr.trans_le hv
  have hK : 0≤K := ha.trans haK
  have hnum := square_error a b K ed ha hb haK hbK hed hd
  have hb2 : b^2≤K^2 := by nlinarith [mul_le_mul hbK hbK hb hK]
  have hden : r^2≤u*v := by nlinarith [mul_le_mul hu hv (le_of_lt hr) (le_of_lt hu0)]
  rw [show a^2/u-b^2/v=(a^2-b^2)/u+b^2*(v-u)/(u*v) by
    field_simp [ne_of_gt hu0,ne_of_gt hv0]; ring]
  calc
    _ ≤ |(a^2-b^2)/u|+|b^2*(v-u)/(u*v)| := abs_add_le _ _
    _ = |a^2-b^2|/u+b^2*|u-v|/(u*v) := by
      rw [abs_div,abs_div,abs_mul,abs_of_nonneg (sq_nonneg b),abs_sub_comm v u,
        abs_of_pos hu0,abs_of_pos (mul_pos hu0 hv0)]
    _ ≤ (2*K*ed)/u+(K^2*em)/(u*v) := by gcongr
    _ ≤ (2*K*ed)/r+(K^2*em)/r^2 := by gcongr

/-- Bounds the change in normalized water-level fidelity under bounded coordinatewise table
perturbations. A common positive lower bound `ρ` on both masses controls the overlap and
mass contributions to the quotient error. -/
theorem g2 :
  ∀ (m : ℕ) (p s p' s' : Fin m→ℝ) (B L δ γ ρ : ℝ),
    0≤B → 0≤L → 0≤δ → 0≤γ → γ≤L → 0<ρ →
    TableBound p s B → TableBound p' s' B → inputError p s p' s' δ →
    ρ≤realMass p s γ → ρ≤realMass p' s' γ →
    |realFidelity p s γ-realFidelity p' s' γ| ≤
      2*((m:ℝ)*B^2)*dotError m B L δ/ρ+
      ((m:ℝ)*B^2)^2*massError m B L δ/ρ^2 := by
  intro m p s p' s' B L δ γ ρ hB hL hδ hγ hγL hρ hp hp' hi hm hm'
  obtain ⟨_, heM, heD⟩ := g1 m p s p' s' B L δ γ hB hL hδ hγ hγL hp hp' hi
  have hpos : 0<realMass p s γ := hρ.trans_le hm
  have hpos' : 0<realMass p' s' γ := hρ.trans_le hm'
  rw [realFidelity,realFidelity,if_neg (ne_of_gt hpos),if_neg (ne_of_gt hpos')]
  exact quotient_error _ _ _ _ _ _ _ _
    (dot_bounds hB hγ hp).1 (dot_bounds hB hγ hp').1
    (dot_bounds hB hγ hp).2 (dot_bounds hB hγ hp').2
    (by dsimp [dotError,fillError]; positivity) (by dsimp [massError,fillError]; positivity)
    hρ hm hm' heD heM

/-- Bounds the perturbation of the fidelity residual by the squared-overlap error plus `|a|`
times the mass error, under the bounded-table and level hypotheses. -/
private theorem residual_error {m : ℕ} (p s p' s' : Fin m→ℝ) (B L δ γ a : ℝ)
    (hB : 0≤B) (hL : 0≤L) (hδ : 0≤δ) (hγ : 0≤γ) (hγL : γ≤L)
    (hp : TableBound p s B) (hp' : TableBound p' s' B) (hi : inputError p s p' s' δ) :
    |residual p s γ a-residual p' s' γ a| ≤
      2*((m:ℝ)*B^2)*dotError m B L δ+|a| *massError m B L δ := by
  obtain ⟨_,heM,heD⟩ := g1 m p s p' s' B L δ γ hB hL hδ hγ hγL hp hp' hi
  have hs := square_error _ _ ((m:ℝ)*B^2) (dotError m B L δ)
    (dot_bounds hB hγ hp).1 (dot_bounds hB hγ hp').1
    (dot_bounds hB hγ hp).2 (dot_bounds hB hγ hp').2
    (by dsimp [dotError,fillError]; positivity) heD
  unfold residual
  rw [show realDot p s γ^2-a*realMass p s γ-(realDot p' s' γ^2-a*realMass p' s' γ) =
    (realDot p s γ^2-realDot p' s' γ^2)-a*(realMass p s γ-realMass p' s' γ) by ring]
  exact (abs_sub _ _).trans
      (by rw [abs_mul]; exact add_le_add hs (mul_le_mul_of_nonneg_left heM (abs_nonneg a)))

/-- Casting a rational residual to the reals gives the real residual of the cast tables at the
same level and threshold. -/
private theorem residualRat_cast {m : ℕ} (q r : Fin m→ℚ) (γ a : ℚ) :
    (residualRat q r γ a : ℝ) = residual (fun i => (q i:ℝ)) (fun i => (r i:ℝ)) γ a := by
  unfold residualRat residual realDot realMass realFill
  push_cast
  all_goals rfl

/-- Certifies positive and negative answers from a rational residual approximation with error at
most `e`. An undecided answer forces the true residual to have magnitude at most `2 * e`,
and a larger gap forces a decision. -/
private theorem classify (x : ℝ) (q e : ℚ) (_he : 0≤e) (hx : |x-(q:ℝ)|≤(e:ℝ)) :
    (decideResidual q e=some true → 0<x) ∧
    (decideResidual q e=some false → x<0) ∧
    (decideResidual q e=none → |x|≤2*(e:ℝ)) ∧
    (2*(e:ℝ)< |x| → decideResidual q e≠none) := by
  obtain ⟨hx₁,hx₂⟩ := abs_le.mp hx
  unfold decideResidual
  split_ifs with h h'
  · have hr : (e:ℝ)<q := by exact_mod_cast h
    exact ⟨fun _ => by linarith,by simp,by simp,by simp⟩
  · have hr : (q:ℝ) < -(e:ℝ) := by exact_mod_cast h'
    exact ⟨by simp,fun _ => by linarith,by simp,by simp⟩
  · have hq₁ : (q:ℝ)≤e := by exact_mod_cast (le_of_not_gt h)
    have hq₂ : -(e:ℝ)≤q := by exact_mod_cast (le_of_not_gt h')
    have hbound : |x|≤2*(e:ℝ) := abs_le.mpr ⟨by linarith,by linarith⟩
    exact ⟨by simp,by simp,fun _ => hbound,
      fun hgap => False.elim ((not_lt_of_ge hbound) hgap)⟩

/-- Certifies the three outcomes of the rational residual test for a bounded approximation to
real input tables, including a `2 * residualError` uncertainty bound. A positive answer also
puts the real fidelity strictly above the threshold whenever the real mass is positive. -/
theorem g3 :
  ∀ (m : ℕ) (p s : Fin m→ℝ) (q r : Fin m→ℚ) (B L δ γ a : ℚ),
    0≤B → 0≤L → 0≤δ → 0≤γ → γ≤L →
    TableBound p s (B:ℝ) → TableBound (fun i => (q i:ℝ)) (fun i => (r i:ℝ)) (B:ℝ) →
    inputError p s (fun i => (q i:ℝ)) (fun i => (r i:ℝ)) (δ:ℝ) →
    let e := residualError m B L δ a
    let ans := decideResidual (residualRat q r γ a) e
    (ans=some true → 0<residual p s (γ:ℝ) (a:ℝ)) ∧
    (ans=some false → residual p s (γ:ℝ) (a:ℝ)<0) ∧
    (ans=none → |residual p s (γ:ℝ) (a:ℝ)|≤2*(e:ℝ)) ∧
    (2*(e:ℝ)< |residual p s (γ:ℝ) (a:ℝ)| → ans≠none) ∧
    (ans=some true → 0<realMass p s (γ:ℝ) → (a:ℝ)<realFidelity p s (γ:ℝ)) := by
  intro m p s q r B L δ γ a hB hL hδ hγ hγL hp hq hi
  (try dsimp only)
  have hB' : (0:ℝ)≤B := by exact_mod_cast hB
  have hL' : (0:ℝ)≤L := by exact_mod_cast hL
  have hδ' : (0:ℝ)≤δ := by exact_mod_cast hδ
  have hγ' : (0:ℝ)≤γ := by exact_mod_cast hγ
  have hγL' : (γ:ℝ)≤L := by exact_mod_cast hγL
  have he : 0≤residualError m B L δ a := by dsimp [residualError]; positivity
  have hx : |residual p s γ a-(residualRat q r γ a:ℝ)|≤(residualError m B L δ a:ℝ) := by
    rw [residualRat_cast]
    calc
      _ ≤ 2*((m:ℝ)*(B:ℝ)^2)*dotError m B L δ+|(a:ℝ)| * massError m B L δ :=
        residual_error p s (fun i => (q i:ℝ)) (fun i => (r i:ℝ)) B L δ γ a
          hB' hL' hδ' hγ' hγL' hp hq hi
      _ = (residualError m B L δ a:ℝ) := by
        dsimp [residualError,dotError,massError,fillError]
        push_cast
        all_goals ring
  obtain ⟨ht,hf,hn,hgap⟩ := classify (residual p s γ a) (residualRat q r γ a) _ he hx
  refine ⟨ht,hf,hn,hgap,?_⟩
  intro ha hm
  rw [realFidelity,if_neg (ne_of_gt hm)]
  apply (lt_div_iff₀ hm).mpr
  have hh := ht ha
  unfold residual at hh
  linarith
end Qatlib.Concepts.WaterLevel.WaterPrecision
