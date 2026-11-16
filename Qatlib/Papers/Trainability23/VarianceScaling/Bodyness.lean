/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic

@[expose] public section


/-!
# Bodyness source results

These finite probability identities and conditional estimates preserve closed
results from arXiv:2305.02881v2. They do not assert the missing full Haar-product
MMD variance identity or an unconditional trainability theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace Qatlib.Papers.Trainability23.VarianceScaling.Bodyness

/-- The binomial weight `w_σ(l) = C(n,l)(1 − p)^{n−l} p^l` of Eq. (166): the probability that a
`2l`-body Pauli sum is sampled. -/
def binomWeight (n : ℕ) (p : ℝ) (l : ℕ) : ℝ :=
  (n.choose l : ℝ) * (1 - p) ^ (n - l) * p ^ l

/-- **Eq. (166) is a probability distribution.**  Since `p + (1 − p) = 1`, the binomial theorem
gives `Σ_{l=0}^{n} w_σ(l) = 1`; this is the normalisation making `E_{l∼w_σ}` a well-defined
average. -/
theorem binom_sum (n : ℕ) (p : ℝ) :
    ∑ l ∈ Finset.range (n + 1), binomWeight n p l = 1 := by
  have h := add_pow p (1 - p) n
  rw [show p + (1 - p) = (1 : ℝ) by ring, one_pow] at h
  rw [h]
  refine Finset.sum_congr rfl fun l _ => ?_
  unfold binomWeight
  ring

/-- The weights are nonnegative for `p ∈ [0,1]`. -/
theorem binom_nonneg (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (l : ℕ) :
    0 ≤ binomWeight n p l := by
  unfold binomWeight
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · positivity
  · exact pow_nonneg (by linarith) _
  · exact pow_nonneg hp0 _

/-- The paper's `p_σ = (1 − e^{−1/(2σ)})/2` of Eq. (162) (repeated from the `SuppProp2` block,
where it is file-local because paper files cannot import each other under the single-file gate). -/
def pSigmaVal (σ : ℝ) : ℝ := (1 - Real.exp (-(1 / (2 * σ)))) / 2

/-- The mean bodyness `E_{l∼w_σ}[2l]` of Eq. (168). -/
def bodyMean (n : ℕ) (p : ℝ) : ℝ :=
  ∑ l ∈ Finset.range (n + 1), binomWeight n p l * (2 * (l : ℝ))

/-- The variance of the bodyness `Var_{l∼w_σ}[2l]` of Eq. (169). -/
def bodyVar (n : ℕ) (p : ℝ) : ℝ :=
  ∑ l ∈ Finset.range (n + 1), binomWeight n p l * (2 * (l : ℝ) - bodyMean n p) ^ 2

/-- The truncation error `4 ∑_{l=k+1}^{n} w_σ(l)` of Eq. (189): four times the binomial tail mass
beyond `2k` bodies.  This is the combinatorial core of the operator-norm bound of Eqs.
(184)–(188): `|L_MMD − L̃_MMD| ⩽ 4‖O − Õ‖_∞ = truncErr`. -/
def truncErr (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  4 * ∑ l ∈ (Finset.range (n + 1)).filter (fun l => k < l), binomWeight n p l

/-- The truncation error is nonnegative for `p ∈ [0,1]`. -/
theorem tail_nonneg (n k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ truncErr n p k := by
  unfold truncErr
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun l _ => ?_)
  exact binom_nonneg n p hp0 hp1 l


/-- Pascal's rule gives a recurrence for any binomial weighted statistic. -/
theorem binom_recur (n : ℕ) (p : ℝ) (f : ℕ → ℝ) :
    (∑ l ∈ Finset.range (n + 2), binomWeight (n + 1) p l * f l) =
      (1 - p) * (∑ l ∈ Finset.range (n + 1), binomWeight n p l * f l) +
        p * (∑ l ∈ Finset.range (n + 1), binomWeight n p l * f (l + 1)) := by
  have h := Finset.sum_choose_succ_mul
    (fun (i j : ℕ) => (1 - p) ^ j * p ^ i * f i) n
  unfold binomWeight
  simp_rw [mul_assoc] at h ⊢
  rw [h, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ]
    ring

/-- The first binomial moment is `np`, as a polynomial identity for real `p`. -/
theorem first_moment (n : ℕ) (p : ℝ) :
    (∑ l ∈ Finset.range (n + 1), binomWeight n p l * (l : ℝ)) = (n : ℝ) * p := by
  induction n with
  | zero => simp [binomWeight]
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega, binom_recur]
    have hs : (∑ l ∈ Finset.range (n + 1), binomWeight n p l * ((l + 1 : ℕ) : ℝ)) =
        (n : ℝ) * p + 1 := by
      simp_rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      rw [Finset.sum_add_distrib, ih, binom_sum]
    rw [ih, hs]
    push_cast
    ring

/-- The second binomial moment is `np(1-p)+(np)^2`. -/
theorem second_moment (n : ℕ) (p : ℝ) :
    (∑ l ∈ Finset.range (n + 1), binomWeight n p l * (l : ℝ) ^ 2) =
      (n : ℝ) * p * (1 - p) + ((n : ℝ) * p) ^ 2 := by
  induction n with
  | zero => simp [binomWeight]
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega, binom_recur]
    have hs : (∑ l ∈ Finset.range (n + 1), binomWeight n p l * ((l + 1 : ℕ) : ℝ) ^ 2) =
        (n : ℝ) * p * (1 - p) + ((n : ℝ) * p) ^ 2 + 2 * ((n : ℝ) * p) + 1 := by
      calc
        _ = ∑ l ∈ Finset.range (n + 1),
            (binomWeight n p l * (l : ℝ) ^ 2 +
              2 * (binomWeight n p l * (l : ℝ)) + binomWeight n p l) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          push_cast
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            ih, first_moment, binom_sum]
    rw [ih, hs]
    push_cast
    ring

/-- Equation (168): the mean of twice a binomial variable is `2np`. -/
theorem body_mean (n : ℕ) (p : ℝ) : bodyMean n p = 2 * (n : ℝ) * p := by
  unfold bodyMean
  calc
    _ = 2 * ∑ l ∈ Finset.range (n + 1), binomWeight n p l * (l : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => by ring
    _ = _ := by rw [first_moment]; ring

/-- Equation (169): the variance of twice a binomial variable is `4np(1-p)`. -/
theorem body_variance (n : ℕ) (p : ℝ) : bodyVar n p = 4 * (n : ℝ) * p * (1 - p) := by
  unfold bodyVar
  rw [body_mean]
  calc
    _ = 4 * (∑ l ∈ Finset.range (n + 1), binomWeight n p l * (l : ℝ) ^ 2) -
          8 * ((n : ℝ) * p) *
            (∑ l ∈ Finset.range (n + 1), binomWeight n p l * (l : ℝ)) +
          4 * ((n : ℝ) * p) ^ 2 *
            (∑ l ∈ Finset.range (n + 1), binomWeight n p l) := by
      simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => by ring
    _ = _ := by rw [second_moment, first_moment, binom_sum]; ring

/-- Two real sequences have the same eventual order up to positive constants. -/
def IsThetaSeq (f g : ℕ → ℝ) : Prop :=
  (∃ c : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop, c * |g n| ≤ |f n|) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop, |f n| ≤ C * |g n|)

/-- An eventually positive bounded coefficient preserves linear asymptotic order. -/
theorem linear_theta (f : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hf : ∀ᶠ n in Filter.atTop, c ≤ f n ∧ f n ≤ 1) :
    IsThetaSeq (fun n => (n : ℝ) * f n) (fun n => (n : ℝ)) := by
  constructor
  · refine ⟨c, hc, ?_⟩
    filter_upwards [hf] with n hn
    have hfn : 0 ≤ f n := hc.le.trans hn.1
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [abs_of_nonneg hnn, abs_of_nonneg (mul_nonneg hnn hfn)]
    nlinarith [mul_le_mul_of_nonneg_left hn.1 (Nat.cast_nonneg n)]
  · refine ⟨1, one_pos, ?_⟩
    filter_upwards [hf] with n hn
    have hfn : 0 ≤ f n := hc.le.trans hn.1
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [abs_of_nonneg hnn, abs_of_nonneg (mul_nonneg hnn hfn)]
    simpa using mul_le_mul_of_nonneg_left hn.2 (Nat.cast_nonneg n)

/-- Positive bandwidths with a fixed upper bound give linearly growing mean and variance. -/
theorem body_theta (σ : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (hσ : ∀ᶠ n in Filter.atTop, 0 < σ n ∧ σ n ≤ C) :
    IsThetaSeq (fun n => bodyMean n (pSigmaVal (σ n))) (fun n => (n : ℝ)) ∧
      IsThetaSeq (fun n => bodyVar n (pSigmaVal (σ n))) (fun n => (n : ℝ)) := by
  let c : ℝ := (1 - Real.exp (-(1 / (2 * C)))) / 2
  have hc : 0 < c := by
    have he : Real.exp (-(1 / (2 * C))) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (by positivity))
    dsimp [c]
    linarith
  have hp : ∀ᶠ n in Filter.atTop,
      c ≤ pSigmaVal (σ n) ∧ pSigmaVal (σ n) ≤ 1 / 2 := by
    filter_upwards [hσ] with n hn
    have hinv : 1 / (2 * C) ≤ 1 / (2 * σ n) :=
      div_le_div_of_nonneg_left (by norm_num) (by nlinarith [hn.1]) (by nlinarith [hn.2])
    have hexp : Real.exp (-(1 / (2 * σ n))) ≤ Real.exp (-(1 / (2 * C))) :=
      Real.exp_le_exp.mpr (by linarith)
    dsimp [pSigmaVal, c]
    constructor <;> linarith [Real.exp_pos (-(1 / (2 * σ n)))]
  have hmean : ∀ᶠ n in Filter.atTop, c ≤ 2 * pSigmaVal (σ n) ∧ 2 * pSigmaVal (σ n) ≤ 1 := by
    filter_upwards [hp] with n hn
    constructor <;> linarith
  have hvar : ∀ᶠ n in Filter.atTop,
      c ≤ 4 * pSigmaVal (σ n) * (1 - pSigmaVal (σ n)) ∧
        4 * pSigmaVal (σ n) * (1 - pSigmaVal (σ n)) ≤ 1 := by
    filter_upwards [hp] with n hn
    have hp0 : 0 ≤ pSigmaVal (σ n) := hc.le.trans hn.1
    constructor <;> nlinarith [sq_nonneg (pSigmaVal (σ n) - 1 / 2),
      mul_nonneg hp0 (show 0 ≤ 1 / 2 - pSigmaVal (σ n) by linarith)]
  constructor
  · simpa [body_mean, mul_assoc, mul_comm, mul_left_comm] using linear_theta _ c hc hmean
  · simpa [body_variance, mul_assoc, mul_comm, mul_left_comm] using linear_theta _ c hc hvar

end Qatlib.Papers.Trainability23.VarianceScaling.Bodyness
