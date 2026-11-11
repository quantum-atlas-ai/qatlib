/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSymmetry
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDistribution

/-!
# Product cube Poincaré estimates

The module splits product Bernoulli expectations and influences according to the first
coordinate and proves the resulting variance decomposition. Induction gives a Poincaré estimate
bounding variance by total squared flip influence and hence the existence of a coordinate with a
quantitative influence bound.

These are finite product variance tools for the Boolean acceptance functions studied through the
polynomial method in [BealsEtAl2001].

## Main statements

* `cube_mu_variance_cons`: variance decomposition along the first coordinate.
* `cube_mu_variance_le_total_inf`: variance is bounded by total influence.
* `cube_mu_exists_large_influence`: a coordinate controls variance with factor `2 * n²`.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

/-- A product cube weight factors into the first Bernoulli coordinate weight and the remaining
cube weight. -/
theorem cube_mu_cons_weight (p : ℝ) (n : ℕ) (b : Bool) (x : Fin n → Bool) :
    muWeight p (n+1) (Fin.cons b x) = (if b then p else 1-p)*muWeight p n x := by
  simp [muWeight, Fin.prod_univ_succ]

/-- Product cube expectation splits into the false and true first coordinate expectations with
weights `1 - p` and `p`. -/
theorem cube_mu_expect_cons (p : ℝ) (n : ℕ) (f : (Fin (n+1) → Bool) → ℝ) :
    cubeExpect (n+1) (muWeight p (n+1)) f =
      (1-p)*cubeExpect n (muWeight p n) (fun x => f (Fin.cons false x))+
      p*cubeExpect n (muWeight p n) (fun x => f (Fin.cons true x)) := by
  have he := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Bool))
    (fun x => muWeight p (n+1) x*f x)
  rw [cubeExpect, ← he, Fintype.sum_prod_type]
  rw [Fintype.sum_bool]
  change (∑ x, muWeight p (n+1) (Fin.cons true x)*f (Fin.cons true x))+
    (∑ x, muWeight p (n+1) (Fin.cons false x)*f (Fin.cons false x)) = _
  simp_rw [cube_mu_cons_weight]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold cubeExpect
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- Flipping the first coordinate of a cons input negates its initial bit. -/
theorem cube_flip_cons_zero (n : ℕ) (b : Bool) (x : Fin n → Bool) :
    cubeFlip (Fin.cons b x) 0 = Fin.cons (!b) x := by
  ext k
  refine Fin.cases ?_ (fun j => ?_) k <;> simp [cubeFlip]

/-- Flipping a successor coordinate of a cons input flips the corresponding coordinate of its
tail. -/
theorem cube_flip_cons_succ (n : ℕ) (b : Bool) (x : Fin n → Bool) (i : Fin n) :
    cubeFlip (Fin.cons b x) i.succ = Fin.cons b (cubeFlip x i) := by
  ext k
  refine Fin.cases ?_ (fun j => ?_) k
  · have hi : (0 : Fin (n+1)) ≠ i.succ := by intro he; have hv := congrArg Fin.val he; simp at hv
    simp [cubeFlip,hi]
  · simp [cubeFlip]

/-- The first coordinate influence is the expected squared difference between the true and false
restrictions. -/
theorem cube_mu_inf_cons_zero (p : ℝ) (n : ℕ) (f : (Fin (n+1) → Bool) → ℝ) :
    cubeInf (n+1) (muWeight p (n+1)) f 0 =
      cubeExpect n (muWeight p n) (fun x => (f (Fin.cons true x)-f (Fin.cons false x))^2) := by
  rw [cubeInf, cube_mu_expect_cons]
  simp only [cube_flip_cons_zero, Bool.not_false, Bool.not_true]
  have he : (fun x => (f (Fin.cons false x)-f (Fin.cons true x))^2) =
      (fun x => (f (Fin.cons true x)-f (Fin.cons false x))^2) := by funext x; ring
  rw [he]
  ring

/-- A successor coordinate influence is the Bernoulli weighted sum of the corresponding
influences of the two first coordinate restrictions. -/
theorem cube_mu_inf_cons_succ (p : ℝ) (n : ℕ) (f : (Fin (n+1) → Bool) → ℝ) (i : Fin n) :
    cubeInf (n+1) (muWeight p (n+1)) f i.succ =
      (1-p)*cubeInf n (muWeight p n) (fun x => f (Fin.cons false x)) i+
      p*cubeInf n (muWeight p n) (fun x => f (Fin.cons true x)) i := by
  rw [cubeInf, cube_mu_expect_cons]
  simp only [cube_flip_cons_succ]
  rfl

/-- For `0 ≤ p ≤ 1`, variance is the weighted sum of the two restricted variances plus `p * (1 -
p)` times the squared difference of their means. -/
theorem cube_mu_variance_cons {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ)
    (f : (Fin (n+1) → Bool) → ℝ) :
    cubeVar (n+1) (muWeight p (n+1)) f =
      (1-p)*cubeVar n (muWeight p n) (fun x => f (Fin.cons false x))+
      p*cubeVar n (muWeight p n) (fun x => f (Fin.cons true x))+
      p*(1-p)*(cubeExpect n (muWeight p n) (fun x => f (Fin.cons true x))-
        cubeExpect n (muWeight p n) (fun x => f (Fin.cons false x)))^2 := by
  rw [cube_var_eq_second_moment_sub_sq _ (muWeight_cubeWeight hp0 hp1 _) f,
    cube_mu_expect_cons, cube_mu_expect_cons,
    cube_var_eq_second_moment_sub_sq _ (muWeight_cubeWeight hp0 hp1 _) _,
    cube_var_eq_second_moment_sub_sq _ (muWeight_cubeWeight hp0 hp1 _) _]
  ring

/-- For `0 ≤ p ≤ 1`, variance under the product cube law is at most the sum of squared flip
influences. -/
theorem cube_mu_variance_le_total_inf {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ)
    (f : (Fin n → Bool) → ℝ) : cubeVar n (muWeight p n) f ≤ cubeTotalInf n (muWeight p n) f := by
  induction n with
  | zero => simp [cubeVar,cubeExpect,muWeight,cubeTotalInf]
  | succ n ih =>
    let f0 := fun x : Fin n → Bool => f (Fin.cons false x)
    let f1 := fun x : Fin n → Bool => f (Fin.cons true x)
    let D := fun x => f1 x-f0 x
    have hw := muWeight_cubeWeight hp0 hp1 n
    have hJ : (cubeExpect n (muWeight p n) D)^2 ≤ cubeExpect n (muWeight p n) (fun x => D x^2) := by
      have hv := cubeVar_nonneg n hw D
      rw [cube_var_eq_second_moment_sub_sq n hw D] at hv
      linarith
    have hmean : cubeExpect n (muWeight p n) D = cubeExpect n (muWeight p n) f1-
        cubeExpect n (muWeight p n) f0 := by simp [D,cubeExpect,mul_sub,Finset.sum_sub_distrib]
    have hd0 : 0 ≤ cubeExpect n (muWeight p n) (fun x => D x^2) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (hw.1 x) (sq_nonneg _)
    have hc0 : 0 ≤ p*(1-p) := by positivity
    have hc1 : p*(1-p) ≤ 1 := by nlinarith [sq_nonneg p]
    have hcross := (mul_le_mul_of_nonneg_left hJ hc0).trans
      (mul_le_of_le_one_left hd0 hc1)
    rw [hmean] at hcross
    have h0 := mul_le_mul_of_nonneg_left (ih f0) (sub_nonneg.2 hp1)
    have h1 := mul_le_mul_of_nonneg_left (ih f1) hp0
    rw [cube_mu_variance_cons hp0 hp1 n f]
    have htotal : cubeTotalInf (n+1) (muWeight p (n+1)) f =
        cubeExpect n (muWeight p n) (fun x => D x^2)+
        ((1-p)*cubeTotalInf n (muWeight p n) f0+p*cubeTotalInf n (muWeight p n) f1) := by
      unfold cubeTotalInf
      rw [Fin.sum_univ_succ, cube_mu_inf_cons_zero]
      simp only [cube_mu_inf_cons_succ, Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    rw [htotal]
    change (1-p)*cubeVar n (muWeight p n) f0+p*cubeVar n (muWeight p n) f1+
      p*(1-p)*(cubeExpect n (muWeight p n) f1-cubeExpect n (muWeight p n) f0)^2 ≤ _
    linarith only [h0,h1,hcross]

/-- For a nonempty cube and `0 < p < 1`, some coordinate influence controls the product law
variance with factor `2 * n²`. -/
theorem cube_mu_exists_large_influence {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 0 < n) (f : (Fin n → Bool) → ℝ) :
    ∃ i : Fin n, cubeVar n (muWeight p n) f ≤ 2*(n : ℝ)^2*cubeInf n (muWeight p n) f i := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n => cubeInf n (muWeight p n) f i) Finset.univ_nonempty
  refine ⟨i, (cube_mu_variance_le_total_inf hp0.le hp1.le n f).trans ?_⟩
  calc
    cubeTotalInf n (muWeight p n) f ≤ ∑ _j : Fin n, cubeInf n (muWeight p n) f i :=
      Finset.sum_le_sum fun j _ => hmax j (Finset.mem_univ j)
    _ = (n : ℝ)*cubeInf n (muWeight p n) f i := by simp
    _ ≤ _ := by
      have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hc : (n : ℝ) ≤ 2*(n : ℝ)^2 := by
        nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (show 0 ≤ (n : ℝ)-1 by linarith)]
      exact mul_le_mul_of_nonneg_right hc
          (cubeInf_nonneg n (muWeight_cubeWeight hp0.le hp1.le n) f i)

end Qatlib.Concepts.ProbabilityCore.DistributionAA
