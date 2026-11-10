/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound.GridMarkov
import Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound.Symmetrization
import Mathlib.Algebra.Polynomial.Degree.Lemmas
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound
open Qatlib.Papers.QMedianStats98.MainResults.Model
open Polynomial

def sourceRescale (n : ℕ) (q : Polynomial ℝ) : Polynomial ℝ :=
  q.comp (C ((n : ℝ)/2)*X+C ((n : ℝ)/2))

theorem sourceRescale_degree (n : ℕ) (q : Polynomial ℝ) :
    (sourceRescale n q).natDegree ≤ q.natDegree := by
  have hd : (C ((n : ℝ)/2)*X+C ((n : ℝ)/2)).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le
      ((natDegree_C_mul_le _ X).trans (by simp)) (by simp)
  exact natDegree_comp_le.trans ((Nat.mul_le_mul_left q.natDegree hd).trans_eq (Nat.mul_one _))

theorem sourceRescale_grid {n : ℕ} (hn : 0 < n) (q : Polynomial ℝ) (k : ℕ) :
    (sourceRescale n q).eval (sourceGrid n k) = q.eval (k : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [sourceRescale,eval_comp,eval_add,eval_mul,eval_C,eval_X]
  congr 1
  dsimp [sourceGrid]
  field_simp
  ring

theorem source_univariate_first_term {n lo hi : ℕ} (hn : 0 < n)
    (hl : lo ≤ n) (hh : hi ≤ n) (hne : lo ≠ hi)
    (q : Polynomial ℝ) (d : ℕ) (hd : q.natDegree ≤ d)
    (error : ℝ) (he0 : 0 ≤ error) (he : error < 1/2)
    (hgrid : ∀ k : ℕ, k ≤ n → q.eval (k : ℝ) ∈ Set.Icc (-error) (1+error))
    (hlo : |q.eval (lo : ℝ)-1| ≤ error) (hhi : |q.eval (hi : ℝ)| ≤ error) :
    Real.sqrt ((1-2*error)*(n : ℝ)/(8*(Nat.dist lo hi : ℝ))) ≤ (d : ℝ) := by
  have hrange : ∀ k : ℕ, k ≤ n → |(sourceRescale n q).eval (sourceGrid n k)| ≤ 3/2 := by
    intro k hk
    rw [sourceRescale_grid hn]
    have hg := hgrid k hk
    exact abs_le.mpr ⟨by linarith [hg.1],by linarith [hg.2]⟩
  have hsep : 1-2*error ≤
      |(sourceRescale n q).eval (sourceGrid n lo)-(sourceRescale n q).eval (sourceGrid n hi)| := by
    rw [sourceRescale_grid hn,sourceRescale_grid hn]
    have ha := (abs_le.mp hlo).1
    have hb := (abs_le.mp hhi).2
    exact (by linarith : 1-2*error ≤ q.eval (lo : ℝ)-q.eval (hi : ℝ)).trans (le_abs_self _)
  have hs := source_grid_first_term_sq hn hl hh hne d (sourceRescale n q)
    ((sourceRescale_degree n q).trans hd) hrange (1-2*error) (by linarith) hsep
  exact Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg d,hs⟩

theorem source_polynomial_first_term {n lo hi : ℕ} (hn : 0 < n)
    (hl : lo ≤ n) (hh : hi ≤ n) (hne : lo ≠ hi)
    (p : MvPolynomial (Fin n) ℝ) (error : ℝ) (he0 : 0 ≤ error) (he : error < 1/2)
    (hp : ApproximatesWithin p lo hi error) :
    Real.sqrt ((1-2*error)*(n : ℝ)/(8*(Nat.dist lo hi : ℝ))) ≤ (p.totalDegree : ℝ) := by
  obtain ⟨q,hq,hgrid,hlo,hhi⟩ := source_symmetrization p lo hi error hp hl hh
  exact source_univariate_first_term hn hl hh hne q p.totalDegree hq error he0 he hgrid hlo hhi

theorem source_first_constant_pos (error : ℝ) (he : error < 1/2) :
    0 < Real.sqrt ((1-2*error)/8) := by
  apply Real.sqrt_pos.mpr
  linarith

theorem source_polynomial_first_term_scaled {n lo hi : ℕ} (hn : 0 < n)
    (hl : lo ≤ n) (hh : hi ≤ n) (hne : lo ≠ hi)
    (p : MvPolynomial (Fin n) ℝ) (error : ℝ) (he0 : 0 ≤ error) (he : error < 1/2)
    (hp : ApproximatesWithin p lo hi error) :
    Real.sqrt ((1-2*error)/8) * Real.sqrt ((n : ℝ)/(Nat.dist lo hi : ℝ)) ≤
      (p.totalDegree : ℝ) := by
  rw [← Real.sqrt_mul (by linarith : 0 ≤ (1-2*error)/8)]
  have heq : (1-2*error)/8*((n : ℝ)/(Nat.dist lo hi : ℝ)) =
      (1-2*error)*(n : ℝ)/(8*(Nat.dist lo hi : ℝ)) := by ring
  rw [heq]
  exact source_polynomial_first_term hn hl hh hne p error he0 he hp

end Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound
