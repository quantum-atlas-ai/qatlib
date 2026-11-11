/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EigTransform26.Representation.SourceModel
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option backward.isDefEq.respectTransparency false

/-!
# EigTransform26 — Representation block (§2, §5.1, §7, Appendix B.1)

Paper-layer Lean statements for the LCHM representation claims with complete proofs for:

* `c018` Lemma 5.6 — exact negative-binomial tail (eq. (5.51));
* `c027` Lemma B.1 — boundary eigenvalues of an accretive matrix (eq. (B.1)).

The contour-integration identities (Theorems 2.1/2.3, Corollary 5.1, Proposition 7.1,
Theorem 1.1) face a genuine Mathlib gap — no residue theorem for Banach-valued
integrals, no dominated convergence for `VectorMeasure.integral` — their first-pass
statements are preserved in branch history (see the PR body for the difficulty log).
-/

set_option autoImplicit false
noncomputable section

open Matrix Polynomial Filter MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Topology

namespace Qatlib.Papers.EigTransform26.Representation

variable {n J : Type*} [Fintype n] [DecidableEq n] [Fintype J] [DecidableEq J]

/-! ## c018 — Lemma 5.6: exact negative-binomial tail -/

/-- Polynomial recursion underlying Lemma 5.6: for weights `x + y = 1` and all `n, K`,
`x · ∑_{j≤K} C(n+j, j) y^j + C(n+K, K) y^{K+1} = ∑_{j≤K} C(n+j-1, j) y^j`.
This is the one-step `n ↦ n+1` identity for the negative-binomial CDF polynomial,
proved by induction on `K` using Pascal's rule. -/
private lemma poly_negbinom {x y : ℝ} (hxy : x + y = 1) (K n : ℕ) :
    x * (∑ j ∈ Finset.range (K + 1), (Nat.choose (n + j) j : ℝ) * y ^ j)
      + (Nat.choose (n + K) K : ℝ) * y ^ (K + 1)
      = ∑ j ∈ Finset.range (K + 1), (Nat.choose (n + j - 1) j : ℝ) * y ^ j := by
  induction K generalizing n with
  | zero =>
    simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.add_zero, pow_zero,
      pow_one, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul]
    linarith [hxy]
  | succ K ih =>
    have hsplitL : ∑ j ∈ Finset.range (K + 1 + 1), (Nat.choose (n + j) j : ℝ) * y ^ j
        = (∑ j ∈ Finset.range (K + 1), (Nat.choose (n + j) j : ℝ) * y ^ j)
          + (Nat.choose (n + K + 1) (K + 1) : ℝ) * y ^ (K + 1) := by
      rw [Finset.sum_range_succ]
      have hi : n + (K + 1) = n + K + 1 := by omega
      rw [hi]
    have hsplitR : ∑ j ∈ Finset.range (K + 1 + 1), (Nat.choose (n + j - 1) j : ℝ) * y ^ j
        = (∑ j ∈ Finset.range (K + 1), (Nat.choose (n + j - 1) j : ℝ) * y ^ j)
          + (Nat.choose (n + K) (K + 1) : ℝ) * y ^ (K + 1) := by
      rw [Finset.sum_range_succ]
      have hi : n + (K + 1) - 1 = n + K := by omega
      rw [hi]
    have hpascal : (Nat.choose (n + K + 1) (K + 1) : ℝ)
        = (Nat.choose (n + K) (K + 1) : ℝ) + (Nat.choose (n + K) K : ℝ) := by
      have h := Nat.choose_succ_succ (n + K) K
      simp only [Nat.succ_eq_add_one] at h
      have h2 : ((Nat.choose (n + K + 1) (K + 1) : ℕ) : ℝ)
          = ((Nat.choose (n + K) (K + 1) : ℕ) : ℝ) + ((Nat.choose (n + K) K : ℕ) : ℝ) := by
        rw [h]
        push_cast
        ring
      exact h2
    have hy2 : y ^ (K + 1 + 1) = y ^ (K + 1) * y := by ring
    have hmix : ∀ a : ℝ, x * (a * y ^ (K + 1)) + a * (y ^ (K + 1) * y) = a * y ^ (K + 1) := by
      intro a
      have hmix0 : x * (a * y ^ (K + 1)) + a * (y ^ (K + 1) * y)
          = (a * y ^ (K + 1)) * (x + y) := by ring
      rw [hmix0, hxy, mul_one]
    have hxT : x * ((Nat.choose (n + K + 1) (K + 1) : ℝ) * y ^ (K + 1))
        + (Nat.choose (n + K + 1) (K + 1) : ℝ) * (y ^ (K + 1) * y)
        = (Nat.choose (n + K + 1) (K + 1) : ℝ) * y ^ (K + 1) := hmix _
    have hCsplit : (Nat.choose (n + K + 1) (K + 1) : ℝ) * y ^ (K + 1)
        = (Nat.choose (n + K) (K + 1) : ℝ) * y ^ (K + 1)
          + (Nat.choose (n + K) K : ℝ) * y ^ (K + 1) := by
      rw [hpascal, add_mul]
    have ihn := ih n
    have hgoalidx : (Nat.choose (n + (K + 1)) (K + 1) : ℝ)
        = (Nat.choose (n + K + 1) (K + 1) : ℝ) := by
      have hidx : n + (K + 1) = n + K + 1 := by omega
      rw [hidx]
    rw [hgoalidx, hsplitL, hsplitR, hy2, mul_add]
    linarith [hxT, hCsplit, ihn]

/-- **Lemma 5.6 (Exact negative-binomial tail).**
arXiv:2607.25812v1, §5, eq. (5.51), p.36.

For `0 < x < 1`, `n ≥ 1`, and `k ≥ 1`,
`∑_{m=n}^∞ C(m+k-1, k-1) x^m = x^n/(1-x)^k · ∑_{j=0}^{k-1} C(n+j-1, j) (1-x)^j`. -/
theorem lemma_5_6 (x : ℝ) (n k : ℕ)
    (hx0 : 0 < x) (hx1 : x < 1) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (∑' m : ℕ, if n ≤ m then (Nat.choose (m + k - 1) (k - 1) : ℝ) * x ^ m else 0)
      = x ^ n / (1 - x) ^ k
          * (∑ j ∈ Finset.range k, (Nat.choose (n + j - 1) j : ℝ) * (1 - x) ^ j) := by
  -- SOURCE: arXiv:2607.25812v1, Lemma 5.6, §5, eq. (5.51), p.36.
  -- KEY STEPS: anchor the full negative-binomial series at
  -- `hasSum_choose_mul_geometric_of_norm_lt_one'`, peel one index at a time with
  -- `hasSum_nat_add_iff'`, drive the values by the polynomial recursion `poly_negbinom`,
  -- then bridge to the `if n ≤ m` guard via `hasSum_nat_add_iff`.
  obtain ⟨K, hK⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  subst hK
  simp only [← Nat.add_assoc, Nat.add_sub_cancel]
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hyne : (1 - x : ℝ) ≠ 0 := by
    have : (0:ℝ) < 1 - x := by linarith
    exact ne_of_gt this
  have key : ∀ n : ℕ, HasSum (fun i : ℕ => (Nat.choose (i + n + K) K : ℝ) * x ^ i)
      ((∑ j ∈ Finset.range (K + 1), (Nat.choose (n + j - 1) j : ℝ) * (1 - x) ^ j)
        / (1 - x) ^ (K + 1)) := by
    intro n
    induction n with
    | zero =>
      have hanchor : HasSum (fun i : ℕ => (Nat.choose (i + K) K : ℝ) * x ^ i)
          (1 / (1 - x) ^ (K + 1)) := by
        have h := hasSum_choose_mul_geometric_of_norm_lt_one' K (r := x) (by
          rw [Real.norm_eq_abs]
          exact abs_lt.mpr ⟨by linarith, hx1⟩)
        simpa using h
      have hP0 : (∑ j ∈ Finset.range (K + 1), (Nat.choose (0 + j - 1) j : ℝ) * (1 - x) ^ j)
          = 1 := by
        rw [Finset.sum_eq_single (0 : ℕ)]
        · simp
        · intro b _ hb
          have hlt : 0 + b - 1 < b := by omega
          rw [Nat.choose_eq_zero_of_lt hlt]
          simp
        · intro h
          exact absurd (Finset.mem_range.mpr (Nat.succ_pos K)) h
      rw [hP0]
      simpa only [Nat.add_zero] using hanchor
    | succ n ih =>
      have hpeel := (hasSum_nat_add_iff' 1).mpr ih
      simp only [Finset.sum_range_one, Nat.zero_add, pow_zero, mul_one] at hpeel
      have hfam2 : (fun i : ℕ => (Nat.choose (i + 1 + n + K) K : ℝ) * x ^ (i + 1))
          = fun i : ℕ => x * ((Nat.choose (i + (n + 1) + K) K : ℝ) * x ^ i) := by
        funext i
        have hidx : i + 1 + n + K = i + (n + 1) + K := by omega
        rw [hidx]
        ring
      rw [hfam2] at hpeel
      have hdiv := hpeel.const_smul (x⁻¹ : ℝ)
      have hfam3 : (fun i : ℕ => (x⁻¹ : ℝ) • (x * ((Nat.choose (i + (n + 1) + K) K : ℝ)
              * x ^ i)))
          = fun i : ℕ => (Nat.choose (i + (n + 1) + K) K : ℝ) * x ^ i := by
        funext i
        rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hxne, one_mul]
      rw [hfam3] at hdiv
      simp only [smul_eq_mul] at hdiv
      have hpoly := poly_negbinom (x := x) (y := 1 - x) (by ring) K n
      have hval : (x⁻¹ : ℝ) * ((∑ j ∈ Finset.range (K + 1),
              (Nat.choose (n + j - 1) j : ℝ) * (1 - x) ^ j) / (1 - x) ^ (K + 1)
            - (Nat.choose (n + K) K : ℝ))
          = (∑ j ∈ Finset.range (K + 1), (Nat.choose (n + 1 + j - 1) j : ℝ) * (1 - x) ^ j)
            / (1 - x) ^ (K + 1) := by
        have hsum1 : (∑ j ∈ Finset.range (K + 1), (Nat.choose (n + 1 + j - 1) j : ℝ)
              * (1 - x) ^ j)
            = ∑ j ∈ Finset.range (K + 1), (Nat.choose (n + j) j : ℝ) * (1 - x) ^ j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have hidx : n + 1 + j - 1 = n + j := by omega
          rw [hidx]
        rw [hsum1]
        have hyK : (1 - x) ^ (K + 1) ≠ 0 := pow_ne_zero _ hyne
        field_simp
        linarith [hpoly]
      rw [hval] at hdiv
      exact hdiv
  have hshift : HasSum (fun i : ℕ => (if n ≤ i + n then
          (Nat.choose (i + n + K) K : ℝ) * x ^ (i + n) else 0))
      (x ^ n * ((∑ j ∈ Finset.range (K + 1), (Nat.choose (n + j - 1) j : ℝ) * (1 - x) ^ j)
        / (1 - x) ^ (K + 1))) := by
    have h := (key n).const_smul (x ^ n : ℝ)
    simp only [smul_eq_mul] at h
    have hfam4 : (fun i : ℕ => (if n ≤ i + n then (Nat.choose (i + n + K) K : ℝ)
            * x ^ (i + n) else 0))
        = fun i : ℕ => x ^ n * ((Nat.choose (i + n + K) K : ℝ) * x ^ i) := by
      funext i
      rw [if_pos (Nat.le_add_left n i)]
      ring
    rw [hfam4]
    exact h
  have hsum0 : ∑ i ∈ Finset.range n, (if n ≤ i then
      (Nat.choose (i + K) K : ℝ) * x ^ i else 0) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hlt : i < n := Finset.mem_range.mp hi
    rw [if_neg (by omega : ¬ n ≤ i)]
  have hmain := (hasSum_nat_add_iff
      (f := fun m : ℕ => if n ≤ m then (Nat.choose (m + K) K : ℝ) * x ^ m else 0)
      n).mp hshift
  simp only [] at hmain
  rw [hsum0, add_zero] at hmain
  rw [hmain.tsum_eq]
  ring

/-! ## c026 — Proposition 7.1: separation from finite-measure inverse-Laplace forms -/

/-- The inverse-Laplace value `f(x) = ∫_{[0,∞)} e^{-x t} dμ(t)` of eq. (7.5), for a finite
complex Borel measure `μ` on `[0, ∞)` (represented as a `ComplexMeasure` on `ℝ` supported
on `[0, ∞)`).  The integral is the vector-measure integral against the ℂ-bilinear product. -/
def inverseLaplace (μ : MeasureTheory.ComplexMeasure ℝ) (x : ℝ) : ℂ :=
  MeasureTheory.VectorMeasure.integral μ (fun t : ℝ => Complex.exp (-(x : ℂ) * (t : ℂ)))
    (ContinuousLinearMap.mul ℝ ℂ)

/-! ## c027 — Lemma B.1: boundary eigenvalues of an accretive matrix -/

/-- **Lemma B.1 (Boundary eigenvalues of an accretive matrix).**
arXiv:2607.25812v1, Appendix B.1, eq. (B.1), p.47.

Let `B = L + iH` with `L = L† ⪰ 0` and `H = H†`.  Then:
* every eigenvalue of `B` lies in the closed right half-plane;
* if `Bv = iαv` for a real `α`, then `Lv = 0`, `Hv = αv`, and `B†v = −iαv` (eq. (B.1)).

(The "consequently semisimple" corollary is recorded in the docstring: it follows because
the `iα`-eigenspace is invariant under `H`, which is diagonalisable.) -/
theorem lemma_B_1
    (L H : Matrix n n ℂ) (hLh : L.IsHermitian) (hLpsd : PSD L) (hHh : H.IsHermitian) :
    (∀ (lam : ℂ) (v : n → ℂ), v ≠ 0 → (L + Complex.I • H).mulVec v = lam • v → 0 ≤ lam.re)
    ∧ (∀ (α : ℝ) (v : n → ℂ), v ≠ 0 →
        (L + Complex.I • H).mulVec v = (Complex.I * (α : ℂ)) • v →
        L.mulVec v = 0 ∧ H.mulVec v = (α : ℂ) • v
          ∧ (L + Complex.I • H)ᴴ.mulVec v = (-(Complex.I * (α : ℂ))) • v) := by
  -- SOURCE: arXiv:2607.25812v1, Lemma B.1, Appendix B.1, eq. (B.1), p.47.
  -- KEY STEPS: take real parts of `⟪v, Bv⟫ = λ⟪v, v⟫`; the Hermitian quadratic forms of `L`
  -- and `H` are real (`Matrix.IsHermitian.im_star_dotProduct_mulVec_self`), so
  -- `Re λ · ‖v‖² = Re ⟪v, Lv⟫ ≥ 0` by `PSD`; on the boundary `λ = iα` this forces the `L`-form
  -- to vanish, hence `Lv = 0` by `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`; the rest is
  -- linear algebra with `B† = L† − iH† = L − iH`.
  -- Bridge the paper's `L ⪰ 0` to Mathlib's `PosSemidef` on the RCLike star order.
  have hLps : L.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hLpsd.1, fun x => ?_⟩
    rw [RCLike.nonneg_iff]
    exact ⟨hLpsd.2 x, hLpsd.1.im_star_dotProduct_mulVec_self x⟩
  -- The squared norm `S := star v ⬝ᵥ v` is real and strictly positive for `v ≠ 0`.
  have hSpos : ∀ v : n → ℂ, v ≠ 0 →
      (dotProduct (star v) v).im = 0 ∧ 0 < (dotProduct (star v) v).re := by
    intro v hv0
    have hSsum : dotProduct (star v) v = ∑ i, ((Complex.normSq (v i) : ℝ) : ℂ) := by
      rw [dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact Complex.normSq_eq_conj_mul_self.symm
    have hSim : (dotProduct (star v) v).im = 0 := by
      rw [hSsum, Complex.im_sum]
      simp
    refine ⟨hSim, ?_⟩
    have hSre : (dotProduct (star v) v).re = ∑ i, Complex.normSq (v i) := by
      rw [hSsum, Complex.re_sum]
      simp
    rw [hSre]
    by_contra hS0
    have hSle : (0:ℝ) ≤ ∑ i, Complex.normSq (v i) :=
      Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (v i)
    have hSeq : ∑ i, Complex.normSq (v i) = 0 := le_antisymm (by linarith) hSle
    have hvall : ∀ i, v i = 0 := by
      have hmem := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Complex.normSq_nonneg (v i))).mp hSeq
      intro i
      exact Complex.normSq_eq_zero.mp (hmem i (Finset.mem_univ i))
    exact hv0 (funext hvall)
  -- Expansion of the eigenvalue equation in quadratic forms.
  have hexpand : ∀ (lam : ℂ) (v : n → ℂ),
      (L + Complex.I • H).mulVec v = lam • v →
      dotProduct (star v) (L.mulVec v) + Complex.I * dotProduct (star v) (H.mulVec v)
        = lam * dotProduct (star v) v := by
    intro lam v hBv
    calc dotProduct (star v) (L.mulVec v) + Complex.I * dotProduct (star v) (H.mulVec v)
        = dotProduct (star v) ((L + Complex.I • H).mulVec v) := by
          rw [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
            smul_eq_mul]
      _ = dotProduct (star v) (lam • v) := by rw [hBv]
      _ = lam * dotProduct (star v) v := by rw [dotProduct_smul, smul_eq_mul]
  constructor
  · intro lam v hv0 hBv
    have hexp := hexpand lam v hBv
    obtain ⟨hSim, hSre⟩ := hSpos v hv0
    have hHim : (dotProduct (star v) (H.mulVec v)).im = 0 :=
      hHh.im_star_dotProduct_mulVec_self v
    -- Real parts: qL.re = lam.re * S.re.
    have hqL : (dotProduct (star v) (L.mulVec v)).re
        = lam.re * (dotProduct (star v) v).re := by
      have h := congrArg Complex.re hexp
      rw [Complex.add_re, Complex.mul_re, Complex.mul_re] at h
      simp only [Complex.I_re, Complex.I_im, hSim, hHim, zero_mul, one_mul, sub_zero,
        add_zero, mul_zero] at h
      linarith
    have hnonneg := hLpsd.2 v
    rcases lt_or_ge lam.re 0 with hneg | hge
    · exfalso
      have hlt : lam.re * (dotProduct (star v) v).re < 0 :=
        mul_neg_of_neg_of_pos hneg hSre
      linarith
    · exact hge
  · intro α v hv0 hBv
    have hexp := hexpand (Complex.I * (α : ℂ)) v hBv
    obtain ⟨hSim, hSre⟩ := hSpos v hv0
    have hHim : (dotProduct (star v) (H.mulVec v)).im = 0 :=
      hHh.im_star_dotProduct_mulVec_self v
    have hIre : (Complex.I * (α : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    have hqLre : (dotProduct (star v) (L.mulVec v)).re = 0 := by
      have h := congrArg Complex.re hexp
      rw [Complex.add_re, Complex.mul_re, Complex.mul_re, hIre, hSim] at h
      simp only [Complex.I_re, Complex.I_im, hHim, zero_mul, one_mul, sub_zero, add_zero,
        mul_zero] at h
      linarith
    have hqL : dotProduct (star v) (L.mulVec v) = 0 := by
      refine Complex.ext_iff.mpr ⟨hqLre, ?_⟩
      exact hLh.im_star_dotProduct_mulVec_self v
    have hLv : L.mulVec v = 0 := hLps.dotProduct_mulVec_zero_iff.mp hqL
    -- From Bv = iα v and Lv = 0, recover Hv = α v.
    have hBv2 : Complex.I • H.mulVec v = (Complex.I * (α : ℂ)) • v := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, hLv, zero_add] at hBv
      exact hBv
    have hHv : H.mulVec v = (α : ℂ) • v := by
      have h3 : Complex.I • H.mulVec v = Complex.I • ((α : ℂ) • v) := by
        rw [hBv2, smul_smul]
      exact smul_right_injective (R := ℂ) (M := n → ℂ) Complex.I_ne_zero h3
    refine ⟨hLv, hHv, ?_⟩
    -- B†v = (L − iH)v = 0 − iα v.
    have hBdag : (L + Complex.I • H)ᴴ = L - Complex.I • H := by
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hLh, hHh]
      simp [Complex.star_def, Complex.conj_I, sub_eq_add_neg, neg_smul]
    rw [hBdag, Matrix.sub_mulVec, hLv, zero_sub, Matrix.smul_mulVec, hHv, smul_smul, neg_smul]

end Qatlib.Papers.EigTransform26.Representation
