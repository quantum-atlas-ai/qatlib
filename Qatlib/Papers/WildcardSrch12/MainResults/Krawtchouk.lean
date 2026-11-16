/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.WildcardSrch12.MainResults.Model.GramOverlap

@[expose] public section


/-! Preserved closed mathematical components; no credit for deferred source algorithms. -/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.WildcardSrch12.MainResults.KrawtchoukGramFormula

open Qatlib.Papers.WildcardSrch12.MainResults

/-- The paper's Krawtchouk polynomial (p. 11):
`K^n_k(x) = Σ_{i=0}^{k} (−1)^i C(x,i) C(n−x, k−i)`, as an integer. -/
noncomputable def krawtchouk (N k t : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (k + 1),
    (-1 : ℤ) ^ i * (Nat.choose t i : ℤ) * (Nat.choose (N - t) (k - i) : ℤ)


/-- The degree-zero Krawtchouk polynomial is identically `1`; this is the case that
turns eq. (3) at `x = y` into the starting formula of Lemma 9's proof. -/
theorem krawtchouk_zero (N t : ℕ) : krawtchouk N 0 t = 1 := by
  unfold krawtchouk
  simp


/-- The degree-one Krawtchouk polynomial: `K^n_1(x) = n − 2x` (paper's use of
`K^n_{d(x,y)}` at `d(x,y) = 1`, and the `ĝ(e_i)` computation of §3). -/
theorem krawtchouk_one {N t : ℕ} (ht : t ≤ N) :
    krawtchouk N 1 t = (N : ℤ) - 2 * (t : ℤ) := by
  unfold krawtchouk
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.sub_zero, pow_zero, pow_one, one_mul, Nat.cast_one, mul_one]
  rw [Nat.cast_sub ht, Nat.choose_zero_right]
  push_cast
  ring


/-- The inner sum of eq. (3) at degree `d`: `Σ_{z=0}^{n} K^n_d(z) C(n,z)^{1/2} C(k,z)^{1/2}`. -/
noncomputable def krawtchoukSum (n k d : ℕ) : ℝ :=
  ∑ z ∈ Finset.range (n + 1),
    (krawtchouk n d z : ℝ) * Real.sqrt (Nat.choose n z : ℝ) * Real.sqrt (Nat.choose k z : ℝ)


/-- The actual Gram matrix vanishes when there is no subset of the requested size. -/
theorem gramOutOfRange {n k : ℕ} (hk : n < k) : (gramMat n k).mat = 0 := by
  ext x y
  rw [gramMat_mat]
  simp [gramEntry, Nat.choose_eq_zero_of_lt hk]

/-- The old Lemma 8 fails at n=0,k=1, outside the paper's k≤n domain. -/
theorem legacyEightFalse (x : BitStr 0) :
    pgmProb 0 1 x x ≠ (2 : ℝ) ^ (-(0 + 1) : ℤ) *
      ((Nat.choose 0 (hammingDist x x) : ℝ) ^ 2)⁻¹ *
      (krawtchoukSum 0 1 (hammingDist x x)) ^ 2 := by
  have hs := HermitianMat.sqrt_sq
    (Qatlib.Concepts.MbqcFlow.FlowDecision.ensembleGram_nonneg (psiEnsemble 0 1))
  have hmul := congrArg (fun A : Matrix (BitStr 0) (BitStr 0) ℂ => A x x) hs
  have hg := gramOutOfRange (n := 0) (k := 1) (by omega)
  have hsum : (∑ j : BitStr 0, (gramMat 0 1).sqrt.mat x j *
      (gramMat 0 1).sqrt.mat j x) =
      (gramMat 0 1).sqrt.mat x x * (gramMat 0 1).sqrt.mat x x := by
    apply Finset.sum_eq_single x
    · intro j _ hj
      exact (hj (Subsingleton.elim j x)).elim
    · intro hx
      exact (hx (Finset.mem_univ x)).elim
  change (∑ j : BitStr 0, (gramMat 0 1).sqrt.mat x j *
    (gramMat 0 1).sqrt.mat j x) = (gramMat 0 1).mat x x at hmul
  have hzero : (gramMat 0 1).sqrt.mat x x * (gramMat 0 1).sqrt.mat x x = 0 := by
    simpa only [hsum, hg, Matrix.zero_apply] using hmul
  have hz : (gramMat 0 1).sqrt.mat x x = 0 := (mul_self_eq_zero).mp hzero
  have hp : pgmProb 0 1 x x = 0 := by
    change Complex.normSq ((gramMat 0 1).sqrt.mat x x) = 0
    rw [hz]
    norm_num
  rw [hp]
  norm_num [hammingDist_self, krawtchoukSum, krawtchouk]

end Qatlib.Papers.WildcardSrch12.MainResults.KrawtchoukGramFormula
