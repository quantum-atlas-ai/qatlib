/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.CommutatorExp
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def word : List A → ℝ → A
  | [], _ => 1
  | K :: ks, t => NormedSpace.exp (t • K) * word ks t

def generator : List A → ℝ → A
  | [], _ => 0
  | K :: ks, t => K + NormedSpace.exp (t • K) * generator ks t * NormedSpace.exp ((-t) • K)

def interaction (K : A) (ks : List A) (t : ℝ) : A :=
  NormedSpace.exp ((-t) • K) * word ks t

def interactionGenerator (K : A) (ks : List A) (t : ℝ) : A :=
  NormedSpace.exp ((-t) • K) * (generator ks t - K) * NormedSpace.exp (t • K)
local instance : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ _

theorem exp_neg_time_mul (K : A) (t : ℝ) :
    NormedSpace.exp ((-t) • K) * NormedSpace.exp (t • K) = 1 := by
  rw [neg_smul, ← NormedSpace.exp_add_of_commute (Commute.refl (t • K)).neg_left,
    neg_add_cancel, NormedSpace.exp_zero]
omit [CompleteSpace A] in

theorem word_zero (ks : List A) : word ks 0 = 1 := by
  induction ks with
  | nil => rfl
  | cons K ks ih => simp only [word, zero_smul, NormedSpace.exp_zero, one_mul, ih]

theorem word_hasDerivAt (ks : List A) (t : ℝ) :
    HasDerivAt (word ks) (generator ks t * word ks t) t := by
  induction ks with
  | nil => simpa only [word, generator, zero_mul] using (hasDerivAt_const t (1 : A))
  | cons K ks ih =>
    have hd := (hasDerivAt_exp_smul_const' K t).mul ih
    convert! hd using 1
    change (K + NormedSpace.exp (t • K) * generator ks t * NormedSpace.exp ((-t) • K)) *
        (NormedSpace.exp (t • K) * word ks t) = _
    calc
      _ = (K * NormedSpace.exp (t • K)) * word ks t +
          NormedSpace.exp (t • K) * generator ks t *
            (NormedSpace.exp ((-t) • K) * NormedSpace.exp (t • K)) * word ks t := by
              noncomm_ring
      _ = _ := by rw [exp_neg_time_mul]; noncomm_ring
omit [CompleteSpace A] in

theorem interaction_zero (K : A) (ks : List A) : interaction K ks 0 = 1 := by
  simp only [interaction, neg_zero, zero_smul, NormedSpace.exp_zero, word_zero, one_mul]

theorem interaction_hasDerivAt (K : A) (ks : List A) (t : ℝ) :
    HasDerivAt (interaction K ks) (interactionGenerator K ks t * interaction K ks t) t := by
  have he : HasDerivAt (fun s : ℝ => NormedSpace.exp ((-s) • K))
      ((-K) * NormedSpace.exp ((-t) • K)) t := by
    simpa only [smul_neg, neg_smul] using hasDerivAt_exp_smul_const' (-K) t
  have hc : K * NormedSpace.exp ((-t) • K) = NormedSpace.exp ((-t) • K) * K :=
    ((Commute.refl K).smul_right (-t)).exp_right.eq
  have hi : NormedSpace.exp (t • K) * NormedSpace.exp ((-t) • K) = 1 := by
    simpa only [neg_neg] using exp_neg_time_mul K (-t)
  convert! he.mul (word_hasDerivAt ks t) using 1
  change (NormedSpace.exp ((-t) • K) * (generator ks t - K) * NormedSpace.exp (t • K)) *
      (NormedSpace.exp ((-t) • K) * word ks t) = _
  calc
    _ = NormedSpace.exp ((-t) • K) * (generator ks t - K) *
        (NormedSpace.exp (t • K) * NormedSpace.exp ((-t) • K)) * word ks t := by
          noncomm_ring
    _ = _ := by rw [hi]; simp only [mul_one]; noncomm_ring [hc]
end Qatlib.Foundations.MatrixAlgebra.CommutatorExp
