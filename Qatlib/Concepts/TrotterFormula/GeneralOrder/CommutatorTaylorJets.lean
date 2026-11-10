/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
set_option warningAsError false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix Set
open scoped Classical BigOperators Matrix.Norms.L2Operator ContDiff Topology
variable {I : Type} [Fintype I] [DecidableEq I]

theorem pf_monomial_contDiff (C : Matrix I I ℂ) (n : ℕ) :
    ContDiff ℝ ∞ (fun t : ℝ=>t^n • C) := (contDiff_id.pow n).smul contDiff_const

theorem pf_monomial_jet (C : Matrix I I ℂ) (n j : ℕ) :
    iteratedDeriv j (fun t : ℝ=>t^n • C) 0=if j=n then (n.factorial:ℝ) • C else 0 := by
  have hpow : ContDiff ℝ ∞ (fun t : ℝ=>t^n) := contDiff_id.pow n
  rw [iteratedDeriv_smul_const (hpow.contDiffAt.of_le
    (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))) C,iteratedDeriv_fun_pow_zero]
  split_ifs <;> simp

theorem pfConjTrunc_contDiff (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) :
    ContDiff ℝ ∞ (pfConjTrunc xs B p) := by
  unfold pfConjTrunc
  exact ContDiff.sum (fun _ _=>pf_monomial_contDiff _ _)

theorem pfConjTrunc_jet (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p j : ℕ) :
    iteratedDeriv j (pfConjTrunc xs B p) 0=
      if j<p then (j.factorial:ℝ) • pfConjCoeff xs B j else 0 := by
  rw [show pfConjTrunc xs B p=(fun t : ℝ=>∑ n : Fin p,t^n.val • pfConjCoeff xs B n.val) from rfl,
    iteratedDeriv_fun_sum (fun _ _=>(pf_monomial_contDiff _ _).contDiffAt.of_le
      (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤)))]
  simp_rw [pf_monomial_jet]
  by_cases hj : j<p
  · rw [if_pos hj]
    let k : Fin p := ⟨j,hj⟩
    have he (n : Fin p) : (j=n.val)↔n=k := by
      constructor
      · intro h;exact Fin.ext h.symm
      · intro h;subst n;rfl
    simp only [he,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rfl
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro n _
    rw [if_neg (by have hn:=n.isLt;omega : ¬j=n.val)]

theorem pfConjWord_remainder_order (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) :
    trotterOrder (fun t=>pfConjWord xs B t-pfConjTrunc xs B p t) p := by
  let a := pfCommAlphaInner xs B p
  have ha : 0≤a := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  let c := a*Real.exp (2*suzukiMass xs)
  have hc : 0≤c := by dsimp [c];positivity
  refine ⟨c+1,1,by positivity,by norm_num,?_⟩
  intro t ht
  have hb := pfConjWord_remainder_norm_mode false xs B p t (by simp)
  rw [pfWordInflation_false] at hb
  have he : Real.exp (2*|t| *suzukiMass xs)≤Real.exp (2*suzukiMass xs) := by
    apply Real.exp_le_exp.mpr
    have hm := general_trotter_mass_nonneg xs
    nlinarith [mul_le_mul_of_nonneg_right ht hm]
  calc _≤a*|t| ^p*Real.exp (2*|t| *suzukiMass xs) := hb
       _≤a*|t| ^p*Real.exp (2*suzukiMass xs) := mul_le_mul_of_nonneg_left he (by positivity)
       _=c*|t| ^p := by dsimp [c];ring
       _≤(c+1)*|t| ^p := by gcongr;linarith

theorem pfConjWord_jet (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (j : ℕ) :
    iteratedDeriv j (pfConjWord xs B) 0=(j.factorial:ℝ) • pfConjCoeff xs B j := by
  have hR := (trotter_matrix_order_jets
    (fun t=>pfConjWord xs B t-pfConjTrunc xs B (j+1) t) (j+1)
    ((pfConjWord_contDiff xs B).sub (pfConjTrunc_contDiff xs B (j+1)))).mp
    (pfConjWord_remainder_order xs B (j+1)) j (by omega)
  rw [iteratedDeriv_fun_sub ((pfConjWord_contDiff xs B).contDiffAt.of_le
      (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤)))
    ((pfConjTrunc_contDiff xs B (j+1)).contDiffAt.of_le
      (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))),pfConjTrunc_jet,if_pos (by omega : j<j+1)] at hR
  exact sub_eq_zero.mp hR

theorem pfConjWord_taylor_before (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) :
    pfTaylorBefore (pfConjWord xs B) p t=pfConjTrunc xs B p t := by
  unfold pfTaylorBefore pfConjTrunc
  rw [← Fin.sum_univ_eq_sum_range (fun n=>(t^n/(n.factorial:ℝ)) • iteratedDeriv n (pfConjWord xs B) 0) p]
  apply Finset.sum_congr rfl
  intro n _
  rw [pfConjWord_jet,smul_smul,div_mul_cancel₀ _ (by exact_mod_cast Nat.factorial_ne_zero n.val)]
end Qatlib.Concepts.TrotterFormula.GeneralOrder
