/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ApproxPolynomialBlockSensitivityStat
import Qatlib.Concepts.QueryComplexity.DegreeMethod.BlockSubstitution
import Qatlib.Concepts.QueryComplexity.DegreeMethod.DiscreteNodeDerivative
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityCombinatorics

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib
open scoped Classical BigOperators

theorem approximatePolynomialBlockSensitivity_of_discrete
    (hdiscrete : ∀ (N : ℕ) (p : Polynomial ℝ) (b1 b2 c x : ℝ), 0 < c →
      (∀ i : ℕ, i ≤ N → b1 ≤ p.eval (i:ℝ) ∧ p.eval (i:ℝ) ≤ b2) →
      x ∈ Set.Icc (0 : ℝ) (N:ℝ) → c ≤ |p.derivative.eval x| →
      c*(N:ℝ) ≤ (p.natDegree:ℝ)^2*(c+b2-b1)) : ApproximatePolynomialBlockSensitivity := by
  intro n f p ε hε hεhalf hpoly
  change ∀ y, 0 ≤ p.eval (boolPoint y) ∧ p.eval (boolPoint y) ≤ 1 ∧
    |p.eval (boolPoint y)-(if f y then (1:ℝ) else 0)| ≤ ε at hpoly
  have hfactor : 0 ≤ 2-2*ε := by linarith
  have hfamily (x : Fin n → Bool) (F : Finset (Finset (Fin n))) (hF : SensitiveFamily f x F) :
      (1-2*ε)*(F.card:ℝ) ≤ (2-2*ε)*(p.totalDegree:ℝ)^2 := by
    by_cases hF0 : F = ∅
    · subst F
      simp only [Finset.card_empty,Nat.cast_zero,mul_zero]
      exact mul_nonneg hfactor (sq_nonneg _)
    have hcard : 1 ≤ Fintype.card F := by
      rw [Fintype.card_coe]
      exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hF0)
    let b := sensitiveBlockPolynomial x F p
    let r : MvPolynomial F ℝ := if f x then 1-b else b
    let q := avgPoly r
    have hdeg : q.natDegree ≤ p.totalDegree := by
      apply (avgPoly_natDegree_le r).trans
      dsimp [r]
      split_ifs
      · exact (block_complement_totalDegree b).trans (sensitiveBlockPolynomial_totalDegree x F p)
      · exact sensitiveBlockPolynomial_totalDegree x F p
    have heval (y : F → Bool) : r.eval (boolPoint y) =
        if f x then 1-p.eval (boolPoint (sensitiveBlockPoint x F y)) else
          p.eval (boolPoint (sensitiveBlockPoint x F y)) := by
      have hbEval : b.eval (boolPoint y) = p.eval (boolPoint (sensitiveBlockPoint x F y)) :=
        sensitiveBlockPolynomial_eval x F p y
      change (if f x then 1-b else b).eval (boolPoint y) = _
      split_ifs <;> simp only [MvPolynomial.eval_sub,map_one,hbEval]
    have hrange (y : F → Bool) : 0 ≤ r.eval (boolPoint y) ∧ r.eval (boolPoint y) ≤ 1 := by
      have hy := hpoly (sensitiveBlockPoint x F y)
      rw [heval]
      split_ifs <;> constructor <;> linarith [hy.1,hy.2.1]
    have hz (y : F → Bool) (hy : boolWeight y = 0) : r.eval (boolPoint y) ≤ ε := by
      rw [block_zero_weight y hy,heval,sensitiveBlockPoint_zero]
      have herr := (hpoly x).2.2
      cases hfx : f x <;> simp only [hfx,Bool.false_eq_true,if_true,if_false] at herr ⊢
      all_goals have hab := abs_le.mp herr; linarith [hab.1,hab.2]
    have ho (y : F → Bool) (hy : boolWeight y = 1) : 1-ε ≤ r.eval (boolPoint y) := by
      obtain ⟨B,hB⟩ := block_one_weight y hy
      rw [hB,heval,sensitiveBlockPoint_singleton f x F hF B]
      have hsens := hF.1 B.val B.property
      have herr := (hpoly (flipBlock x B.val)).2.2
      cases hfx : f x <;> cases hfb : f (flipBlock x B.val) <;>
        simp only [BlockSensitive,hfx,hfb,ne_eq,not_true_eq_false] at hsens
      all_goals
        simp only [hfb,Bool.false_eq_true,if_true,if_false] at herr ⊢
        have hab := abs_le.mp herr
        linarith [hab.1,hab.2]
    have hq0 : q.eval 0 ≤ ε := by
      have hbounds := block_layerAverage_bounds r 0 (Nat.zero_le _) 0 ε
        (fun y hy => ⟨(hrange y).1,hz y hy⟩)
      dsimp [q]
      simpa only [layerAverage_eq_avgPoly r 0 (Nat.zero_le _),Nat.cast_zero] using hbounds.2
    have hq1 : 1-ε ≤ q.eval 1 := by
      have hbounds := block_layerAverage_bounds r 1 hcard (1-ε) 1
        (fun y hy => ⟨ho y hy,(hrange y).2⟩)
      dsimp [q]
      simpa only [layerAverage_eq_avgPoly r 1 hcard,Nat.cast_one] using hbounds.1
    have hnodes (k : ℕ) (hk : k ≤ Fintype.card F) : 0 ≤ q.eval (k:ℝ) ∧ q.eval (k:ℝ) ≤ 1 := by
      dsimp [q]
      rw [← layerAverage_eq_avgPoly r k hk]
      exact block_layerAverage_bounds r k hk 0 1 (fun y _ => hrange y)
    obtain ⟨z,hzI,hzDeriv⟩ := exists_hasDerivAt_eq_slope (fun t => q.eval t)
      (fun t => q.derivative.eval t) (by norm_num : (0:ℝ) < 1) q.continuous.continuousOn
      (fun t _ => q.hasDerivAt t)
    have hzInterval : z ∈ Set.Icc (0:ℝ) (Fintype.card F:ℝ) := by
      have hc : (1:ℝ) ≤ Fintype.card F := by exact_mod_cast hcard
      exact ⟨hzI.1.le,hzI.2.le.trans hc⟩
    have hpositive : 0 < 1-2*ε := by linarith
    have hslope : 1-2*ε ≤ |q.derivative.eval z| := by
      simp only [sub_zero,div_one] at hzDeriv
      have he := le_abs_self (q.derivative.eval z)
      linarith
    have hnode := hdiscrete (Fintype.card F) q 0 1 (1-2*ε) z hpositive hnodes hzInterval hslope
    have hdegSq : (q.natDegree:ℝ)^2 ≤ (p.totalDegree:ℝ)^2 :=
      (sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (by exact_mod_cast hdeg)
    have hmul := mul_le_mul_of_nonneg_left hdegSq hfactor
    have he : (1-2*ε)*(Fintype.card F:ℝ) ≤ (2-2*ε)*(p.totalDegree:ℝ)^2 := by nlinarith
    simpa only [Fintype.card_coe] using he
  let S := Finset.univ.image (fun x : Fin n → Bool => blockSensitivityAt f x)
  have hS : S.Nonempty := ⟨blockSensitivityAt f (fun _ => false),by simp [S]⟩
  obtain ⟨v,hv,hmax⟩ := Finset.exists_mem_eq_sup S hS id
  obtain ⟨x,_hx,hx⟩ := Finset.mem_image.mp hv
  have hmax' : blockSensitivity f = blockSensitivityAt f x := by
    change S.sup id = _
    rw [hmax]
    exact hx.symm
  let Fs := Finset.univ.filter (fun F : Finset (Finset (Fin n)) => SensitiveFamily f x F)
  have hFs : Fs.Nonempty := ⟨∅,by simp [Fs,SensitiveFamily]⟩
  obtain ⟨F,hF,hFmax⟩ := Finset.exists_mem_eq_sup Fs hFs Finset.card
  have hF' : SensitiveFamily f x F := (Finset.mem_filter.mp hF).2
  have hmax'' : blockSensitivityAt f x = F.card := by
    simpa only [Fs,blockSensitivityAt,SensitiveFamily] using hFmax
  rw [hmax',hmax'']
  exact hfamily x F hF'

theorem approximatePolynomialBlockSensitivity : ApproximatePolynomialBlockSensitivity :=
  approximatePolynomialBlockSensitivity_of_discrete discrete_node_derivative_bound

end Qatlib.Concepts.QueryComplexity.DegreeMethod
