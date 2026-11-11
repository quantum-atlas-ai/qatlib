/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationCommutatorCoefficients

/-!
# Remainders of exponential conjugation words

The recursive conjugation `pfConjWord` is identified with conjugation by
`suzukiExponentialWord`. Its Taylor remainder is bounded by the ordered nested commutator budget
`pfCommAlphaInner`; `pfWordInflation` supplies the general exponential factor and specializes to
one when all generators are skew-Hermitian. For background, see [ChildsEtAl2021Trotter].

## Main statements

* `pfConjWord_eq_word_conjugation`: interpretation as conjugation by an exponential product.
* `pfConjWord_remainder_norm_mode`: uniform commutator remainder bound in both generator modes.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ContDiff Topology
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Successive exponential conjugation along a matrix list, with the head conjugation applied
outside the tail conjugation. -/
def pfConjWord : List (Matrix I I ℂ)→Matrix I I ℂ→ℝ→Matrix I I ℂ
  | [],B,_ => B
  | X::xs,B,t => pfConjExp X (pfConjWord xs B t) t

/-- A conjugation word equals `suzukiExponentialWord xs t * B * Ring.inverse
(suzukiExponentialWord xs t)`. -/
theorem pfConjWord_eq_word_conjugation (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (t : ℝ) :
    pfConjWord xs B t=suzukiExponentialWord xs t*B*Ring.inverse (suzukiExponentialWord xs t) := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  induction xs with
  | nil => simp [pfConjWord,suzukiExponentialWord]
  | cons X xs ih =>
    rw [pfConjWord,ih]
    simp only [suzukiExponentialWord,List.map_cons,List.prod_cons]
    rw [Ring.inverse_mul (Or.inl (NormedSpace.isUnit_exp (t • X))),Ring.inverse_exp]
    simp only [pfConjExp,neg_smul,mul_assoc]

/-- The conjugation word has norm at most `‖B‖ * exp (2 * |t| * suzukiMass xs)`. -/
theorem pfConjWord_norm_general (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (t : ℝ) :
    ‖pfConjWord xs B t‖≤‖B‖*Real.exp (2*|t| *suzukiMass xs) := by
  induction xs with
  | nil => simp [pfConjWord,suzukiMass]
  | cons X xs ih =>
    apply (pfConjExp_norm_general X (pfConjWord xs B t) t).trans
    calc _≤(‖B‖*Real.exp (2*|t| *suzukiMass xs))*Real.exp (2*|t| *‖X‖) :=
           mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
         _=‖B‖*Real.exp (2*|t| *suzukiMass (X::xs)) := by
           rw [show 2*|t| *suzukiMass (X::xs)=2*|t| *suzukiMass xs+2*|t| *‖X‖ by simp only [suzukiMass,List.map_cons,List.sum_cons];ring,Real.exp_add]
           ring

/-- If every generator is skew-Hermitian, the conjugation word has norm at most `‖B‖`. -/
theorem pfConjWord_norm_skew (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (t : ℝ)
    (hxs : ∀ X∈xs,Xᴴ=-X) : ‖pfConjWord xs B t‖≤‖B‖ := by
  induction xs with
  | nil => simp [pfConjWord]
  | cons X xs ih =>
    exact (pfConjExp_norm_skew X _ t (hxs X List.mem_cons_self)).trans
      (ih (fun Y hY=>hxs Y (List.mem_cons_of_mem X hY)))

/-- A finite conjugation word is infinitely differentiable in time. -/
theorem pfConjWord_contDiff (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) : ContDiff ℝ ∞ (pfConjWord xs B) := by
  induction xs with
  | nil => exact contDiff_const
  | cons X xs ih =>
    have hn := (trotter_exp_contDiff X).comp contDiff_id.neg
    simpa only [pfConjWord,pfConjExp,Function.comp_def] using!
        ((trotter_exp_contDiff X).mul ih).mul hn

/-- The remainder for `X :: xs` splits into the conjugated tail remainder and the sum of Taylor
remainders for the tail coefficients. -/
theorem pfConjWord_remainder_cons (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) (p : ℕ) (t : ℝ) :
    pfConjWord (X::xs) B t-pfConjTrunc (X::xs) B p t=
      pfConjExp X (pfConjWord xs B t-pfConjTrunc xs B p t) t+
      ∑ k : Fin p,t^k.val • (pfConjExp X (pfConjCoeff xs B k.val) t-
        pfTaylorBefore (pfConjExp X (pfConjCoeff xs B k.val)) (p-k.val) t) := by
  rw [pfConjWord,pfConjTrunc_cons]
  let L := pfConjExpLinear X t
  change L (pfConjWord xs B t)-(∑ k : Fin p,t^k.val •
    pfTaylorBefore (pfConjExp X (pfConjCoeff xs B k.val)) (p-k.val) t)=
      L (pfConjWord xs B t-pfConjTrunc xs B p t)+
      ∑ k : Fin p,t^k.val • (L (pfConjCoeff xs B k.val)-
        pfTaylorBefore (pfConjExp X (pfConjCoeff xs B k.val)) (p-k.val) t)
  unfold pfConjTrunc
  simp only [map_sub,map_sum,map_smul,smul_sub,Finset.sum_sub_distrib]
  abel

/-- The conjugation growth factor, equal to one in skew mode and `exp (2 * |t| * suzukiMass xs)`
otherwise. -/
def pfWordInflation (skew : Bool) (xs : List (Matrix I I ℂ)) (t : ℝ) : ℝ :=
  if skew then 1 else Real.exp (2*|t| *suzukiMass xs)

/-- In general mode, the word inflation factor is `exp (2 * |t| * suzukiMass xs)`. -/
@[simp] theorem pfWordInflation_false (xs : List (Matrix I I ℂ)) (t : ℝ) :
    pfWordInflation false xs t=Real.exp (2*|t| *suzukiMass xs) := by simp [pfWordInflation]

/-- In skew mode, the word inflation factor is one. -/
@[simp] theorem pfWordInflation_true (xs : List (Matrix I I ℂ)) (t : ℝ) :
    pfWordInflation true xs t=1 := by simp [pfWordInflation]

/-- The word inflation factor is nonnegative in either mode. -/
theorem pfWordInflation_nonneg (skew : Bool) (xs : List (Matrix I I ℂ)) (t : ℝ) :
    0≤pfWordInflation skew xs t := by cases skew <;> simp only [pfWordInflation_false,pfWordInflation_true] <;> positivity

/-- The word inflation factor is at least one in either mode. -/
theorem pfWordInflation_one_le (skew : Bool) (xs : List (Matrix I I ℂ)) (t : ℝ) :
    1≤pfWordInflation skew xs t := by
  cases skew
  · rw [pfWordInflation_false]
    exact Real.one_le_exp (by have hm:=general_trotter_mass_nonneg xs;positivity)
  · rw [pfWordInflation_true]

/-- The inflation factor for `X :: xs` is the product of the head factor and the tail factor. -/
theorem pfWordInflation_cons (skew : Bool) (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) (t : ℝ) :
    pfWordInflation skew (X::xs) t=pfWordInflation skew [X] t*pfWordInflation skew xs t := by
  cases skew
  · simp only [pfWordInflation_false]
    rw [← Real.exp_add]
    congr 1
    simp only [suzukiMass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    ring
  · simp only [pfWordInflation_true,mul_one]

/-- The inflation factor for a single head is at most the factor for the full nonempty word. -/
theorem pfWordInflation_head_le (skew : Bool) (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) (t : ℝ) :
    pfWordInflation skew [X] t≤pfWordInflation skew (X::xs) t := by
  rw [pfWordInflation_cons skew X xs t]
  exact le_mul_of_one_le_right (pfWordInflation_nonneg skew [X] t)
      (pfWordInflation_one_le skew xs t)

/-- Exponential conjugation is bounded by `‖B‖` times the selected inflation factor, assuming
skew-Hermitianity when skew mode is selected. -/
theorem pfConjExp_norm_mode (skew : Bool) (X B : Matrix I I ℂ) (t : ℝ)
    (hX : skew=true→Xᴴ=-X) : ‖pfConjExp X B t‖≤‖B‖*pfWordInflation skew [X] t := by
  cases skew
  · simpa only
      [pfWordInflation_false,suzukiMass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using! pfConjExp_norm_general X B t
  · simpa only [pfWordInflation_true,mul_one] using! pfConjExp_norm_skew X B t (hX rfl)

/-- The single-conjugation Taylor remainder is bounded by the factorial-weighted iterated
commutator norm times the selected inflation factor. -/
theorem pfConjExp_remainder_mode (skew : Bool) (X B : Matrix I I ℂ) (p : ℕ) (t : ℝ)
    (hX : skew=true→Xᴴ=-X) :
    ‖pfConjExp X B t-pfTaylorBefore (pfConjExp X B) p t‖≤
      ‖pfAdPower X B p‖*|t| ^p/(p.factorial:ℝ)*pfWordInflation skew [X] t := by
  cases skew
  · simpa only
      [pfWordInflation_false,suzukiMass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using! pf_conjugation_single_general X B p t
  · simpa only [pfWordInflation_true,mul_one] using! pf_conjugation_single_skew X B p t (hX rfl)

/-- A time-scaled coefficient conjugation remainder is bounded by `pfInnerAdSum X B xs k.val (p
- k.val) * |t| ^ p` times the head inflation factor. -/
theorem pfConjCoeff_remainder_scaled_le (skew : Bool) (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ))
    (p : ℕ) (t : ℝ) (k : Fin p) (hX : skew=true→Xᴴ=-X) :
    ‖t^k.val • (pfConjExp X (pfConjCoeff xs B k.val) t-
      pfTaylorBefore (pfConjExp X (pfConjCoeff xs B k.val)) (p-k.val) t)‖≤
      pfInnerAdSum X B xs k.val (p-k.val)*|t| ^p*pfWordInflation skew [X] t := by
  have hr := pfConjExp_remainder_mode skew X (pfConjCoeff xs B k.val) (p-k.val) t hX
  have hc : ‖pfAdPower X (pfConjCoeff xs B k.val) (p-k.val)‖≤pfInnerAdSum X B xs k.val (p-k.val) :=
    pfConjCoeff_linear_norm_le xs B k.val (pfAdPowerLinear X (p-k.val))
  have hf : (1:ℝ)≤(p-k.val).factorial := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (p-k.val))
  have hi := pfWordInflation_nonneg skew [X] t
  rw [norm_smul,Real.norm_eq_abs,abs_pow]
  calc _≤|t| ^k.val*(‖pfAdPower X (pfConjCoeff xs B k.val) (p-k.val)‖*|t| ^(p-k.val)/( (p-k.val).factorial:ℝ)*pfWordInflation skew [X] t) :=
         mul_le_mul_of_nonneg_left hr (by positivity)
       _≤|t| ^k.val*(pfInnerAdSum X B xs k.val (p-k.val)*|t| ^(p-k.val)*pfWordInflation skew [X] t) := by
         gcongr
         exact (div_le_self (by positivity) hf).trans
             (mul_le_mul_of_nonneg_right hc (by positivity))
       _=pfInnerAdSum X B xs k.val (p-k.val)*(|t| ^k.val*|t| ^(p-k.val))*pfWordInflation skew
           [X] t := by ring
       _=pfInnerAdSum X B xs k.val (p-k.val)*|t| ^p*pfWordInflation skew [X] t := by
         rw [← pow_add,Nat.add_sub_of_le k.isLt.le]

/-- The conjugation word remainder below degree `p` is bounded by `pfCommAlphaInner xs B p * |t|
^ p` times the word inflation factor. -/
theorem pfConjWord_remainder_norm_mode (skew : Bool) (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) (hxs : skew=true→∀ X∈xs,Xᴴ=-X) :
    ‖pfConjWord xs B t-pfConjTrunc xs B p t‖≤
      pfCommAlphaInner xs B p*|t| ^p*pfWordInflation skew xs t := by
  induction xs generalizing p with
  | nil =>
    cases p with
    | zero =>
      rw [pf_comm_alpha_inner_zero]
      simp [pfConjWord,pfConjTrunc,pfWordInflation,suzukiMass]
    | succ n =>
      have hp : pfConjTrunc [] B (n+1) t=B := by
        rw [pfConjTrunc,Fin.sum_univ_succ]
        simp [pfConjCoeff]
      rw [pfConjWord,hp,sub_self,norm_zero]
      have hα : 0≤pfCommAlphaInner ([] : List (Matrix I I ℂ)) B (n+1) :=
        Finset.sum_nonneg (fun _ _=>norm_nonneg _)
      have hi := pfWordInflation_nonneg skew ([] : List (Matrix I I ℂ)) t
      positivity
  | cons X xs ih =>
    have hX : skew=true→Xᴴ=-X := fun h=>hxs h X List.mem_cons_self
    have htail : skew=true→∀ Y∈xs,Yᴴ=-Y := fun h Y hY=>hxs h Y (List.mem_cons_of_mem X hY)
    have hr := ih p htail
    have hh : ‖pfConjExp X (pfConjWord xs B t-pfConjTrunc xs B p t) t‖≤
        pfCommAlphaInner xs B p*|t| ^p*pfWordInflation skew (X::xs) t := by
      apply ((pfConjExp_norm_mode skew X _ t hX).trans
        (mul_le_mul_of_nonneg_right hr (pfWordInflation_nonneg skew [X] t))).trans_eq
      rw [pfWordInflation_cons skew X xs t]
      ring
    have hs : ‖∑ k : Fin p,t^k.val • (pfConjExp X (pfConjCoeff xs B k.val) t-
        pfTaylorBefore (pfConjExp X (pfConjCoeff xs B k.val)) (p-k.val) t)‖≤
        (∑ k : Fin p,pfInnerAdSum X B xs k.val (p-k.val))*|t| ^p*pfWordInflation skew (X::xs) t := by
      calc _≤∑ k : Fin p,‖t^k.val • (pfConjExp X (pfConjCoeff xs B k.val) t-
                 pfTaylorBefore (pfConjExp X (pfConjCoeff xs B k.val)) (p-k.val) t)‖ := norm_sum_le _ _
           _≤∑ k : Fin p,pfInnerAdSum X B xs k.val (p-k.val)*|t| ^p*pfWordInflation skew (X::xs) t := by
             apply Finset.sum_le_sum
             intro k _
             apply (pfConjCoeff_remainder_scaled_le skew X B xs p t k hX).trans
             apply mul_le_mul_of_nonneg_left (pfWordInflation_head_le skew X xs t)
             exact mul_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) (by positivity)
           _=_ := by rw [← Finset.sum_mul,← Finset.sum_mul]
    rw [pfConjWord_remainder_cons]
    calc _≤‖pfConjExp X (pfConjWord xs B t-pfConjTrunc xs B p t) t‖+
             ‖∑ k : Fin p,t^k.val • (pfConjExp X (pfConjCoeff xs B k.val) t-
               pfTaylorBefore (pfConjExp X (pfConjCoeff xs B k.val)) (p-k.val) t)‖ := norm_add_le _ _
         _≤pfCommAlphaInner xs B p*|t| ^p*pfWordInflation skew (X::xs) t+
             (∑ k : Fin p,pfInnerAdSum X B xs k.val (p-k.val))*|t| ^p*pfWordInflation skew (X::xs) t := add_le_add hh hs
         _=(pfCommAlphaInner xs B p+∑ k : Fin p,pfInnerAdSum X B xs k.val (p-k.val))*|t| ^p*pfWordInflation skew (X::xs) t := by ring
         _≤_ := mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_right (pf_inner_remainder_budget_le X B xs p) (by positivity))
           (pfWordInflation_nonneg skew (X::xs) t)

end Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
