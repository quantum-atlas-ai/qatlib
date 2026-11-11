/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 1 of *Quantum algorithm and circuit design solving the Poisson equation*
(arXiv:1207.2485, Appendix 2)

The paper computes `v⁻¹` (`v > 1`) by `s` Newton steps of `φ x = 2 x - v x ^ 2` started at
`x̂₀ = 2 ^ (-p)` with `2 ^ (p - 1) < v ≤ 2 ^ p`, in `b`-bit fixed-precision arithmetic, and claims

`|x̂_s - v⁻¹| ≤ ε_N + s · 2 ^ (-b)`,

where `ε_N ≥ 2 ^ (-2 ^ s)` is the accuracy that `s` exact Newton steps reach.

The formalisation follows the paper's proof:

* the exact iteration satisfies `e_{n+1} = v e_n ^ 2`, so `v e_n = (v e_0) ^ (2 ^ n)` and
  `e_s ≤ 2 ^ (-2 ^ s) ≤ ε_N` because `v e_0 ≤ 1 / 2`;
* on the Newton basin `[1 / (2 v), 1 / v]` the iteration is invariant and `|φ'| ≤ 1`, so `s`
  truncations of size `2 ^ (-b)` accumulate to at most `s · 2 ^ (-b)`.

The paper asserts `|φ'| ≤ 1` without tracking that the truncated iterates stay in the basin.  The
formalisation takes that containment (`hbasin`) as an explicit hypothesis of the fixed-precision
part; the exact iterates are proved to stay in the basin, and the basin itself is proved
`φ`-invariant.  The paper's side condition `b > p` only serves to keep the truncation error
inside the basin margin, which the containment hypothesis already covers, so it is not repeated
here; the theorem is therefore slightly stronger than the paper's statement.
-/

namespace Qatlib.Papers.PoissonEq12.MainResults

set_option autoImplicit false

/-- One step of Newton iteration for the reciprocal: `φ x = 2 x - v x ^ 2`. -/
noncomputable def recipStep (v x : ℝ) : ℝ := 2 * x - v * x ^ 2

/-- The exact Newton iteration for `v⁻¹` started at `x₀`. -/
noncomputable def recipIter (v x₀ : ℝ) (n : ℕ) : ℝ :=
  Nat.rec x₀ (fun _ x => recipStep v x) n

/-- The starting point of the exact Newton iteration. -/
@[simp] lemma recipIter_zero (v x₀ : ℝ) : recipIter v x₀ 0 = x₀ := rfl

/-- One Newton step of the exact iteration. -/
@[simp] lemma recipIter_succ (v x₀ : ℝ) (n : ℕ) :
    recipIter v x₀ (n + 1) = recipStep v (recipIter v x₀ n) := rfl

/-- On the Newton basin `[1 / (2 v), 1 / v]` the running value `v x` lies in `[1 / 2, 1]`. -/
lemma mul_v_basin {v x : ℝ} (hv : 0 < v) (hx : x ∈ Set.Icc (1 / (2 * v)) (1 / v)) :
    (1 : ℝ) / 2 ≤ v * x ∧ v * x ≤ 1 := by
  constructor
  · have h2v : (2 * v) ≠ 0 := by positivity
    have h := mul_le_mul_of_nonneg_left hx.1 (by positivity : (0 : ℝ) ≤ 2 * v)
    rw [show 2 * v * (1 / (2 * v)) = 1 by field_simp] at h
    nlinarith
  · have hvne : v ≠ 0 := ne_of_gt hv
    have h := mul_le_mul_of_nonneg_left hx.2 (le_of_lt hv)
    rw [show v * (1 / v) = 1 by field_simp] at h
    linarith

/-- The Newton basin `[1 / (2 v), 1 / v]` is invariant under one Newton step. -/
lemma recipStep_mem_basin {v x : ℝ} (hv : 0 < v) (hx : x ∈ Set.Icc (1 / (2 * v)) (1 / v)) :
    recipStep v x ∈ Set.Icc (1 / (2 * v)) (1 / v) := by
  obtain ⟨hlo, hhi⟩ := mul_v_basin hv hx
  constructor
  · rw [recipStep, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * v)]
    nlinarith [sq_nonneg (v * x - 1)]
  · rw [recipStep, le_div_iff₀ hv]
    nlinarith [sq_nonneg (v * x - 1)]

/-- The exact Newton iterates started in the basin stay in the basin. -/
lemma recipIter_mem_basin {v x₀ : ℝ} (hv : 0 < v) (hx₀ : x₀ ∈ Set.Icc (1 / (2 * v)) (1 / v))
    (n : ℕ) : recipIter v x₀ n ∈ Set.Icc (1 / (2 * v)) (1 / v) := by
  induction n with
  | zero => simpa using hx₀
  | succ k ih => simpa using recipStep_mem_basin hv ih

/-- The Newton step contracts the distance to `v⁻¹` quadratically:
`φ x - v⁻¹ = -v (x - v⁻¹) ^ 2`. -/
lemma recipStep_sub_inv {v x : ℝ} (hv : v ≠ 0) :
    recipStep v x - 1 / v = -v * (x - 1 / v) ^ 2 := by
  rw [recipStep]
  field_simp
  ring

/-- The error of the exact iteration obeys `v e_{n+1} = (v e_n) ^ 2`. -/
lemma recipIter_f_succ {v : ℝ} (hv : 0 < v) (x₀ : ℝ) (n : ℕ) :
    v * |recipIter v x₀ (n + 1) - 1 / v| = (v * |recipIter v x₀ n - 1 / v|) ^ 2 := by
  have hstep : recipIter v x₀ (n + 1) - 1 / v = -v * (recipIter v x₀ n - 1 / v) ^ 2 := by
    rw [recipIter_succ]
    exact recipStep_sub_inv (ne_of_gt hv)
  have hsq : |(recipIter v x₀ n - 1 / v) ^ 2| = (recipIter v x₀ n - 1 / v) ^ 2 := by
    rw [abs_pow, sq_abs]
  rw [hstep, abs_mul, abs_neg, abs_of_pos hv, hsq, mul_pow, sq_abs]
  ring

/-- The scaled error after `n` exact Newton steps is `(v e_0) ^ (2 ^ n)`. -/
lemma recipIter_scaled_error {v : ℝ} (hv : 0 < v) (x₀ : ℝ) (n : ℕ) :
    v * |recipIter v x₀ n - 1 / v| = (v * |x₀ - 1 / v|) ^ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [recipIter_f_succ hv x₀ k, ih, ← pow_mul]
    rw [show 2 ^ k * 2 = 2 ^ (k + 1) by rw [pow_succ]]

/-- **Theorem 1** of arXiv:1207.2485: `s` Newton steps for `v⁻¹` started at `2 ^ (-p)`, carried
out in `b`-bit fixed-precision arithmetic with truncation error `2 ^ (-b)` per step, satisfy
`|x̂_s - v⁻¹| ≤ ε_N + s · 2 ^ (-b)` whenever `ε_N ≥ 2 ^ (-2 ^ s)`. -/
theorem theorem1 (v : ℝ) (hv : 1 < v) (p s b : ℕ) (hp1 : 1 ≤ p)
    (hp : (2 : ℝ) ^ (p - 1) < v) (hpv : v ≤ (2 : ℝ) ^ p)
    (εN : ℝ) (hε : 1 / 2 ^ (2 ^ s) ≤ εN)
    (xhat : ℕ → ℝ) (hx0 : xhat 0 = 1 / 2 ^ p)
    (htrunc : ∀ n, |xhat (n + 1) - recipStep v (xhat n)| ≤ 1 / 2 ^ b)
    (hbasin : ∀ n ≤ s, xhat n ∈ Set.Icc (1 / (2 * v)) (1 / v)) :
    |xhat s - 1 / v| ≤ εN + (s : ℝ) / 2 ^ b := by
  have hvpos : (0 : ℝ) < v := by linarith
  have hbpos : (0 : ℝ) < 2 ^ b := by positivity
  have hx0' : xhat 0 = 1 / 2 ^ p := hx0
  -- the exact iteration stays in the basin
  have hbasin0 : (1 / 2 ^ p : ℝ) ∈ Set.Icc (1 / (2 * v)) (1 / v) := by
    constructor
    · have h2v : (2 * v) ≠ 0 := by positivity
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * v) (by positivity : (0 : ℝ) < 2 ^ p),
        one_mul, one_mul]
      have hpdec : (2 : ℝ) ^ p = 2 ^ (p - 1) * 2 := by
        conv_lhs => rw [show p = p - 1 + 1 by omega]
        rw [pow_succ]
      linarith
    · rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ p) hvpos, one_mul, one_mul]
      exact hpv
  -- accumulation of the per-step truncation errors
  have hacc : ∀ n ≤ s, |xhat n - recipIter v (1 / 2 ^ p) n| ≤ (n : ℝ) / 2 ^ b := by
    intro n hn
    induction n with
    | zero => rw [hx0']; simp
    | succ k ih =>
      have hk : k ≤ s := by omega
      have hbnd := ih hk
      have hxk := hbasin k (by omega)
      have hXk : recipIter v (1 / 2 ^ p) k ∈ Set.Icc (1 / (2 * v)) (1 / v) :=
        recipIter_mem_basin hvpos hbasin0 k
      obtain ⟨hlo1, hhi1⟩ := mul_v_basin hvpos hxk
      obtain ⟨hlo2, hhi2⟩ := mul_v_basin hvpos hXk
      -- one Newton step is `1`-Lipschitz on the basin
      have hlip : |recipStep v (xhat k) - recipStep v (recipIter v (1 / 2 ^ p) k)|
          ≤ |xhat k - recipIter v (1 / 2 ^ p) k| := by
        have hfac : recipStep v (xhat k) - recipStep v (recipIter v (1 / 2 ^ p) k)
            = (xhat k - recipIter v (1 / 2 ^ p) k)
              * (2 - v * (xhat k + recipIter v (1 / 2 ^ p) k)) := by
          simp only [recipStep]
          ring
        have hs1 : 1 ≤ v * (xhat k + recipIter v (1 / 2 ^ p) k) := by nlinarith
        have hs2 : v * (xhat k + recipIter v (1 / 2 ^ p) k) ≤ 2 := by nlinarith
        have hd : |2 - v * (xhat k + recipIter v (1 / 2 ^ p) k)| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        rw [hfac, abs_mul]
        calc |xhat k - recipIter v (1 / 2 ^ p) k|
              * |2 - v * (xhat k + recipIter v (1 / 2 ^ p) k)|
            ≤ |xhat k - recipIter v (1 / 2 ^ p) k| * 1 := by gcongr
          _ = |xhat k - recipIter v (1 / 2 ^ p) k| := by ring
      have hdec : xhat (k + 1) - recipIter v (1 / 2 ^ p) (k + 1)
          = (xhat (k + 1) - recipStep v (xhat k))
            + (recipStep v (xhat k) - recipStep v (recipIter v (1 / 2 ^ p) k)) := by
        simp
      calc |xhat (k + 1) - recipIter v (1 / 2 ^ p) (k + 1)|
          ≤ |xhat (k + 1) - recipStep v (xhat k)|
            + |recipStep v (xhat k) - recipStep v (recipIter v (1 / 2 ^ p) k)| := by
            rw [hdec]
            exact abs_add_le _ _
        _ ≤ 1 / 2 ^ b + |xhat k - recipIter v (1 / 2 ^ p) k| :=
            add_le_add (htrunc k) hlip
        _ ≤ 1 / 2 ^ b + (k : ℝ) / 2 ^ b := by linarith
        _ = ((k + 1 : ℕ) : ℝ) / 2 ^ b := by push_cast; ring
  -- the exact iteration reaches `ε_N`
  have hbase : v * |1 / 2 ^ p - 1 / v| ≤ 1 / 2 := by
    have hle0 : (1 : ℝ) / 2 ^ p ≤ 1 / v := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ p) hvpos, one_mul, one_mul]
      exact hpv
    have habs : |1 / 2 ^ p - 1 / v| = 1 / v - 1 / 2 ^ p := by
      rw [abs_of_nonpos (by linarith)]
      ring
    have hvne : v ≠ 0 := ne_of_gt hvpos
    have hv1 : v * (1 / v) = 1 := by field_simp
    have hvq : (1 : ℝ) / 2 ≤ v / 2 ^ p := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ p)]
      have hpdec : (2 : ℝ) ^ p = 2 ^ (p - 1) * 2 := by
        conv_lhs => rw [show p = p - 1 + 1 by omega]
        rw [pow_succ]
      nlinarith
    rw [habs]
    calc v * (1 / v - 1 / 2 ^ p) = v * (1 / v) - v / 2 ^ p := by ring
      _ = 1 - v / 2 ^ p := by rw [hv1]
      _ ≤ 1 / 2 := by linarith
  have hexact : |recipIter v (1 / 2 ^ p) s - 1 / v| ≤ 1 / 2 ^ (2 ^ s) := by
    have hscaled := recipIter_scaled_error hvpos (1 / 2 ^ p) s
    have hnonneg : (0 : ℝ) ≤ v * |1 / 2 ^ p - 1 / v| := by positivity
    have hle : v * |recipIter v (1 / 2 ^ p) s - 1 / v| ≤ (1 / 2 : ℝ) ^ 2 ^ s := by
      rw [hscaled]
      exact pow_le_pow_left₀ hnonneg hbase _
    have hge : |recipIter v (1 / 2 ^ p) s - 1 / v|
        ≤ v * |recipIter v (1 / 2 ^ p) s - 1 / v| := by
      nlinarith [abs_nonneg (recipIter v (1 / 2 ^ p) s - 1 / v), hvpos]
    have hpow : (1 / 2 : ℝ) ^ 2 ^ s = 1 / 2 ^ (2 ^ s) := by
      rw [div_pow, one_pow]
    linarith
  -- assemble
  have haccs := hacc s le_rfl
  have htri : |xhat s - 1 / v|
      ≤ |xhat s - recipIter v (1 / 2 ^ p) s| + |recipIter v (1 / 2 ^ p) s - 1 / v| := by
    have heq : xhat s - 1 / v
        = (xhat s - recipIter v (1 / 2 ^ p) s) + (recipIter v (1 / 2 ^ p) s - 1 / v) := by
      ring
    rw [heq]
    exact abs_add_le _ _
  calc |xhat s - 1 / v|
      ≤ |xhat s - recipIter v (1 / 2 ^ p) s| + |recipIter v (1 / 2 ^ p) s - 1 / v| := htri
    _ ≤ (s : ℝ) / 2 ^ b + 1 / 2 ^ (2 ^ s) := add_le_add haccs hexact
    _ ≤ (s : ℝ) / 2 ^ b + εN := by linarith
    _ = εN + (s : ℝ) / 2 ^ b := by ring

end Qatlib.Papers.PoissonEq12.MainResults
