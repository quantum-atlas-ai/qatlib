/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

set_option backward.isDefEq.respectTransparency false

/-!
# System-size-independent pulse duration for the SK spin glass (claim `c003`)

Source: Zhi-Cheng Yang, Armin Rahmani, Alireza Shabani, Hartmut Neven,
Claudio Chamon, *Optimizing Variational Quantum Algorithms using Pontryagin's
Minimum Principle*, arXiv:1607.06473v3 (11 March 2017), Sec. IV Eq. (9), p. 4,
and Sec. VII, pp. 7-8, the paragraph containing Eq. (32):

> Thus, the energy difference `ΔC_{z,k} ≡ C_z - C_{\bar z(k)}`, which has zero
> mean (as both `C_z` and `C_{\bar z(k)}` have zero mean) and variance
> `overline{ΔC_{z,k}^2} = 4(J² + h²)`, sets the characteristic time scale
> proportional to `1/√(J² + h²)` observed in Fig. 3. Importantly, this time
> scale is finite and system-size independent.

The SK energy of Eq. (9) is
`C = (1/√n) ∑_{i,j} J_ij σ^z_i σ^z_j + ∑_i h_i σ^z_i`, with independent
zero-mean Gaussian couplings.  In the standard SK convention used for the
variance computation of Sec. VII the double sum is the unordered pair sum
`∑_{i<j}`; we encode it as `∑_{i,j}` with the factor `1/2` and a symmetric,
zero-diagonal coupling matrix, which is the same object.  The exact finite-`n`
variance obtained below is `4(h² + ((n-1)/n) J²)`; the paper's displayed
`4(J² + h²)` is its leading (`n → ∞`) value, and the difference is
`(4/n) J²`, which vanishes with `n`.  The two-sided bounds
`4 h² ≤ Var ≤ 4(J² + h²)` are independent of `n`, which is the precise
content of "finite and system-size independent".

The time-ordered propagator that evolves the state between the pulses is the
frozen concept `TimeEvolution.DysonPropagator` (`evolution`,
`evolution_eq_ordered`); `TrotterFormula.TimeOrdered` is quoted only as the
semantic anchor for the alternative Trotterised protocols mentioned in the
same paragraph.  No theorem of either module is re-proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Qatlib.Papers.PontryaginVQA16.MainResults.SKPulseDuration

/-- The coupling normalised by the SK factor `1/√n`. -/
def pairWeight {n : ℕ} (J : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  J i j / Real.sqrt (n : ℝ)

/-- The local field `∑_j J_ij z_j / √n` of spin `i`. -/
def localField {n : ℕ} (J : Fin n → Fin n → ℝ) (z : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, pairWeight J i j * z j

/-- The SK energy of Eq. (9) in the standard pair convention
`C = ∑_{i<j} J_ij z_i z_j / √n + ∑_i h_i z_i`, written with a symmetric
zero-diagonal `J` as `∑_i (h_i + (1/2) ∑_j J_ij z_j / √n) z_i`.  The factor
`1/2` compensates the ordered double sum, so this is `∑_{i<j}` for symmetric
`J` with zero diagonal. -/
def skEnergy {n : ℕ} (J : Fin n → Fin n → ℝ) (h : Fin n → ℝ)
    (z : Fin n → ℝ) : ℝ :=
  ∑ i, (h i + (1 / 2) * localField J z i) * z i

/-- The spin configuration obtained by flipping spin `k`. -/
def flipSpin {n : ℕ} (k : Fin n) (z : Fin n → ℝ) : Fin n → ℝ :=
  Function.update z k (- z k)

/-- The SK energy as an ordered double sum with the compensating `1/2`, which
is the displayed Eq. (9) restricted to symmetric zero-diagonal couplings. -/
theorem skEnergy_eq_pairSum {n : ℕ} (J : Fin n → Fin n → ℝ) (h : Fin n → ℝ)
    (z : Fin n → ℝ) :
    skEnergy J h z =
      ∑ i, h i * z i + (1 / 2) * ∑ i, ∑ j, pairWeight J i j * z i * z j := by
  unfold skEnergy localField
  have hpt : ∀ i : Fin n,
      (h i + (1 / 2) * (∑ j, pairWeight J i j * z j)) * z i
        = h i * z i + ∑ j, (1 / 2) * (pairWeight J i j * z i * z j) := by
    intro i
    rw [add_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]

/-- Flipping one spin changes the local field by the coupling to that spin:
`L_i(z̄(k)) = L_i(z) - 2 J_ik z_k / √n`. -/
theorem localField_flip {n : ℕ} (J : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (k : Fin n) (_hz : ∀ i, z i * z i = 1) (i : Fin n) :
    localField J (flipSpin k z) i = localField J z i - 2 * pairWeight J i k * z k := by
  unfold localField
  have hpoint : ∀ j : Fin n,
      pairWeight J i j * flipSpin k z j - pairWeight J i j * z j =
        if j = k then -2 * pairWeight J i k * z k else 0 := by
    intro j
    by_cases hjk : j = k
    · rw [hjk]
      simp only [flipSpin, Function.update_self, ite_true]
      ring
    · simp only [flipSpin]
      rw [Function.update_of_ne hjk, if_neg hjk]
      ring
  have hsingle :
      ∑ j : Fin n, (if j = k then -2 * pairWeight J i k * z k else 0)
        = -2 * pairWeight J i k * z k := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hjk
      simp [hjk]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have hthis :
      (∑ j, pairWeight J i j * flipSpin k z j) - ∑ j, pairWeight J i j * z j
        = ∑ j, (if j = k then -2 * pairWeight J i k * z k else 0) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => hpoint j
  linarith [hthis, hsingle]

/-- **Deterministic energy-difference identity.**  Flipping spin `k` changes
the SK energy by `2 z_k (h_k + ∑_j J_kj z_j / √n)`.  This is the energy
difference `ΔC_{z,k}` of Sec. VII, before any probabilistic average. -/
theorem skEnergy_flip_sub {n : ℕ} (J : Fin n → Fin n → ℝ) (h : Fin n → ℝ)
    (z : Fin n → ℝ) (k : Fin n)
    (hsym : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (hz : ∀ i, z i * z i = 1) :
    skEnergy J h z - skEnergy J h (flipSpin k z) =
      2 * z k * (h k + localField J z k) := by
  have hflip : ∀ i, flipSpin k z i = if i = k then - z k else z i := by
    intro i
    by_cases hik : i = k
    · rw [hik]
      simp only [flipSpin, Function.update_self, ite_true]
    · simp only [flipSpin]
      rw [Function.update_of_ne hik, if_neg hik]
  have hL : ∀ i, localField J (flipSpin k z) i =
      localField J z i - 2 * pairWeight J i k * z k := fun i =>
    localField_flip J z k hz i
  have hWkk : pairWeight J k k = 0 := by
    simp [pairWeight, hdiag k]
  -- Rewrite both energies through the local-field form.
  rw [skEnergy, skEnergy]
  -- Split the difference at the flipped coordinate `k`.
  have hfk : (h k + (1 / 2) * localField J z k) * z k -
      (h k + (1 / 2) * localField J (flipSpin k z) k) * flipSpin k z k =
      2 * z k * h k + z k * localField J z k := by
    rw [hL k, hflip k, if_pos rfl, hWkk]
    ring
  have herase : ∑ i ∈ Finset.univ.erase k,
      ((h i + (1 / 2) * localField J z i) * z i -
        (h i + (1 / 2) * localField J (flipSpin k z) i) * flipSpin k z i) =
      z k * localField J z k := by
    -- For `i ≠ k` the difference is `(J_ik / √n) z_k z_i`.
    have hterm : ∀ i ∈ Finset.univ.erase k,
        ((h i + (1 / 2) * localField J z i) * z i -
          (h i + (1 / 2) * localField J (flipSpin k z) i) * flipSpin k z i) =
        pairWeight J i k * z k * z i := by
      intro i hi
      have hik : i ≠ k := by
        simpa using hi
      rw [hL i, hflip i, if_neg hik]
      ring
    rw [Finset.sum_congr rfl hterm]
    -- By symmetry this is `z_k` times the local field at `k`.
    have hsym' : ∑ i ∈ Finset.univ.erase k, pairWeight J i k * z k * z i =
        z k * ∑ i ∈ Finset.univ.erase k, pairWeight J k i * z i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pairWeight, pairWeight, hsym i k]
      ring
    have hlocal : (∑ i ∈ Finset.univ.erase k, pairWeight J k i * z i) =
        localField J z k := by
      unfold localField
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), hWkk]
      ring
    rw [hsym', hlocal]
  have hsum :
      ∑ i, ((h i + (1 / 2) * localField J z i) * z i -
          (h i + (1 / 2) * localField J (flipSpin k z) i) * flipSpin k z i) =
        ((h k + (1 / 2) * localField J z k) * z k -
          (h k + (1 / 2) * localField J (flipSpin k z) k) * flipSpin k z k) +
        ∑ i ∈ Finset.univ.erase k,
          ((h i + (1 / 2) * localField J z i) * z i -
            (h i + (1 / 2) * localField J (flipSpin k z) i) * flipSpin k z i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
    ring
  rw [← Finset.sum_sub_distrib, hsum, hfk, herase]
  ring

/-- **The energy difference `ΔC_{z,k}` as an affine random variable.**  The
deterministic flip identity rewrites `C_z - C_{\bar z(k)}` as
`2 z_k h_k + ∑_i (2 z_k z_i / √n) J_ki`; the `i = k` term is set to zero since
the diagonal coupling cancels exactly. -/
theorem deltaEnergy_eq_affine {n : ℕ} (J : Fin n → Fin n → ℝ) (h : Fin n → ℝ)
    (z : Fin n → ℝ) (k : Fin n)
    (hsym : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (hz : ∀ i, z i * z i = 1) :
    skEnergy J h z - skEnergy J h (flipSpin k z) =
      2 * z k * h k +
        ∑ i, (if i = k then 0 else 2 * z k * z i / Real.sqrt (n : ℝ)) * J k i := by
  rw [skEnergy_flip_sub J h z k hsym hdiag hz]
  have hsplit : 2 * z k * (h k + localField J z k) =
      2 * z k * h k + 2 * z k * ∑ i, pairWeight J k i * z i := by
    unfold localField
    ring
  rw [hsplit, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold pairWeight
  by_cases hik : i = k
  · rw [hik]
    simp [hdiag k]
  · simp [hik]
    ring

/-- The family of independent summands whose sum is `ΔC_{z,k}`: the `none`
component is the field term `2 z_k h_k`, and the `some i` components are the
coupling terms `(2 z_k z_i / √n) J_ki`. -/
def deltaTerm {Ω : Type*} {n : ℕ} (J : Ω → Fin n → Fin n → ℝ)
    (h : Ω → Fin n → ℝ) (z : Fin n → ℝ) (k : Fin n) :
    Option (Fin n) → Ω → ℝ
  | none => fun ω => 2 * z k * h ω k
  | some i => fun ω =>
      (if i = k then 0 else 2 * z k * z i / Real.sqrt (n : ℝ)) * J ω k i

/-- The energy difference `ΔC_{z,k}` as a random variable on `Ω`. -/
def deltaEnergy {Ω : Type*} {n : ℕ} (J : Ω → Fin n → Fin n → ℝ)
    (h : Ω → Fin n → ℝ) (z : Fin n → ℝ) (k : Fin n) : Ω → ℝ :=
  fun ω => skEnergy (J ω) (h ω) z - skEnergy (J ω) (h ω) (flipSpin k z)

/-- Summing the `Option`-indexed summands gives the affine expression for
`ΔC_{z,k}`. -/
theorem deltaEnergy_eq_sum {Ω : Type*} {n : ℕ} (J : Ω → Fin n → Fin n → ℝ)
    (h : Ω → Fin n → ℝ) (z : Fin n → ℝ) (k : Fin n)
    (hsym : ∀ ω i j, J ω i j = J ω j i)
    (hdiag : ∀ ω i, J ω i i = 0) (hz : ∀ i, z i * z i = 1) :
    deltaEnergy J h z k = fun ω => ∑ o : Option (Fin n), deltaTerm J h z k o ω := by
  funext ω
  simp only [deltaEnergy]
  rw [deltaEnergy_eq_affine (J ω) (h ω) z k (hsym ω) (hdiag ω) hz]
  rw [show (∑ o : Option (Fin n), deltaTerm J h z k o ω)
        = deltaTerm J h z k none ω +
            ∑ i : Fin n, deltaTerm J h z k (some i) ω from by
      rw [Fintype.sum_option]]
  simp only [deltaTerm]

/-- **Claim `c003`: the variance of the SK energy difference.**  For fixed
`z ∈ {±1}^n`, symmetric zero-diagonal couplings and independent zero-mean
couplings, the energy difference `ΔC_{z,k} = C_z - C_{\bar z(k)}` has variance
`4 h² + 4 J² (n-1)/n`.  The paper's `4(J² + h²)` is the leading value as
`n → ∞`; the exact finite-size value differs only by `4 J²/n`. -/
theorem variance_deltaEnergy {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (Jsq hsq : ℝ) (J : Ω → Fin n → Fin n → ℝ)
    (h : Ω → Fin n → ℝ) (z : Fin n → ℝ) (k : Fin n)
    (hsym : ∀ ω i j, J ω i j = J ω j i)
    (hdiag : ∀ ω i, J ω i i = 0) (hz : ∀ i, z i * z i = 1)
    (hX : ∀ o, MemLp (deltaTerm J h z k o) 2 μ)
    (hindep : Set.Pairwise Set.univ fun o o' =>
      IndepFun (deltaTerm J h z k o) (deltaTerm J h z k o') μ)
    (hvarJ : ∀ i, i ≠ k → variance (fun ω => J ω k i) μ = Jsq)
    (hvarh : variance (fun ω => h ω k) μ = hsq) :
    variance (deltaEnergy J h z k) μ =
      4 * hsq + 4 * Jsq * (((n : ℝ) - 1) / (n : ℝ)) := by
  rw [deltaEnergy_eq_sum J h z k hsym hdiag hz]
  -- identify the pointwise sum with the function-valued sum
  have hbr : (fun ω => ∑ o : Option (Fin n), deltaTerm J h z k o ω)
      = (∑ o : Option (Fin n), deltaTerm J h z k o) := by
    funext ω
    rw [Finset.sum_apply]
  rw [hbr]
  rw [IndepFun.variance_sum (s := Finset.univ) (fun i _ => hX i) (by simpa using hindep)]
  rw [show (∑ i : Option (Fin n), variance (deltaTerm J h z k i) μ)
        = variance (deltaTerm J h z k none) μ +
            ∑ i : Fin n, variance (deltaTerm J h z k (some i)) μ from by
      rw [Fintype.sum_option]]
  have hnone : variance (deltaTerm J h z k none) μ = 4 * hsq := by
    have hfun : deltaTerm J h z k none = fun ω => 2 * z k * h ω k := rfl
    rw [hfun, variance_const_mul, hvarh]
    have hcoef : (2 * z k) ^ 2 = 4 := by
      have hk := hz k
      nlinarith [hk]
    rw [hcoef]
  rw [hnone]
  have hsome : ∀ i : Fin n, variance (deltaTerm J h z k (some i)) μ =
      if i = k then 0 else 4 * Jsq / (n : ℝ) := by
    intro i
    by_cases hik : i = k
    · rw [hik]
      have hfun : deltaTerm J h z k (some k) = fun _ => (0 : ℝ) := by
        funext ω
        simp [deltaTerm]
      rw [hfun]
      have hz0 : variance (fun _ : Ω => (0 : ℝ)) μ = 0 := variance_zero μ
      rw [hz0]
      simp
    · have hfun : deltaTerm J h z k (some i)
          = fun ω => (2 * z k * z i / Real.sqrt (n : ℝ)) * J ω k i := by
        funext ω
        simp only [deltaTerm, if_neg hik]
      rw [hfun, variance_const_mul, hvarJ i hik]
      rw [if_neg hik]
      have hnpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
      have hs : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
      have h4 : (2 * z k * z i) ^ 2 = 4 := by
        have hk := hz k
        have hi := hz i
        calc (2 * z k * z i) ^ 2 = 4 * (z k * z k) * (z i * z i) := by ring
          _ = 4 := by rw [hk, hi]; ring
      have hc : (2 * z k * z i / Real.sqrt (n : ℝ)) ^ 2 = 4 / (n : ℝ) := by
        field_simp
        nlinarith [h4, hs]
      rw [hc]
      ring
  rw [Finset.sum_congr rfl fun i _ => hsome i]
  have hc : (∑ i : Fin n, (if i = k then (0 : ℝ) else 4 * Jsq / (n : ℝ))) =
      (4 * Jsq / (n : ℝ)) * ((n : ℝ) - 1) := by
    have hmem : (∑ i : Fin n, (if i = k then (0 : ℝ) else 4 * Jsq / (n : ℝ))) =
        (∑ _i : Fin n, 4 * Jsq / (n : ℝ)) - 4 * Jsq / (n : ℝ) := by
      have hstep : ∀ i : Fin n,
          (if i = k then (0 : ℝ) else 4 * Jsq / (n : ℝ)) =
            4 * Jsq / (n : ℝ) -
              (if i = k then 4 * Jsq / (n : ℝ) else 0) := by
        intro i
        by_cases hik : i = k <;> simp [hik]
      calc (∑ i : Fin n, (if i = k then (0 : ℝ) else 4 * Jsq / (n : ℝ)))
          = ∑ i : Fin n,
              (4 * Jsq / (n : ℝ) - (if i = k then 4 * Jsq / (n : ℝ) else 0)) :=
            Finset.sum_congr rfl fun i _ => hstep i
        _ = (∑ _i : Fin n, 4 * Jsq / (n : ℝ)) -
              ∑ i : Fin n, (if i = k then 4 * Jsq / (n : ℝ) else 0) := by
            rw [Finset.sum_sub_distrib]
        _ = (∑ _i : Fin n, 4 * Jsq / (n : ℝ)) - 4 * Jsq / (n : ℝ) := by
            rw [Finset.sum_ite_eq']
            simp
    rw [hmem, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hc]
  ring

/-- **Claim `c003`: the variance scale is finite and independent of `n`.**
Under the same hypotheses, `4 h² ≤ Var(ΔC_{z,k}) ≤ 4 (J² + h²)` with both
bounds free of `n`; in particular the characteristic time
`1/√(J² + h²)` is finite and system-size independent. -/
theorem variance_deltaEnergy_bounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (Jsq hsq : ℝ)
    (J : Ω → Fin n → Fin n → ℝ) (h : Ω → Fin n → ℝ) (z : Fin n → ℝ)
    (k : Fin n) (hsym : ∀ ω i j, J ω i j = J ω j i)
    (hdiag : ∀ ω i, J ω i i = 0) (hz : ∀ i, z i * z i = 1)
    (hX : ∀ o, MemLp (deltaTerm J h z k o) 2 μ)
    (hindep : Set.Pairwise Set.univ fun o o' =>
      IndepFun (deltaTerm J h z k o) (deltaTerm J h z k o') μ)
    (hvarJ : ∀ i, i ≠ k → variance (fun ω => J ω k i) μ = Jsq)
    (hvarh : variance (fun ω => h ω k) μ = hsq)
    (hJ : 0 ≤ Jsq) (_hh : 0 ≤ hsq) :
    4 * hsq ≤ variance (deltaEnergy J h z k) μ ∧
      variance (deltaEnergy J h z k) μ ≤ 4 * (Jsq + hsq) := by
  rw [variance_deltaEnergy Jsq hsq J h z k hsym hdiag hz hX hindep hvarJ hvarh]
  have hnpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hnpos)
  have hr0 : 0 ≤ ((n : ℝ) - 1) / (n : ℝ) :=
    div_nonneg (by linarith) (le_of_lt hn0)
  have hr1 : ((n : ℝ) - 1) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn0]
    linarith
  have h4 : 0 ≤ 4 * Jsq := by linarith
  constructor
  · nlinarith [mul_nonneg h4 hr0]
  · nlinarith [mul_le_mul_of_nonneg_left hr1 h4]

/-- **Zero mean of the energy difference.**  If all couplings have zero mean,
then the energy difference has zero mean, as stated in Sec. VII. -/
theorem integral_deltaEnergy_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} (J : Ω → Fin n → Fin n → ℝ) (h : Ω → Fin n → ℝ)
    (z : Fin n → ℝ) (k : Fin n) (hsym : ∀ ω i j, J ω i j = J ω j i)
    (hdiag : ∀ ω i, J ω i i = 0) (hz : ∀ i, z i * z i = 1)
    (hIntJ : ∀ i, Integrable (fun ω => J ω k i) μ)
    (hInth : Integrable (fun ω => h ω k) μ)
    (hmeanJ : ∀ i, i ≠ k → ∫ ω, J ω k i ∂μ = 0)
    (hmeanh : ∫ ω, h ω k ∂μ = 0) :
    ∫ ω, deltaEnergy J h z k ω ∂μ = 0 := by
  have hfun : deltaEnergy J h z k = fun ω => 2 * z k * h ω k +
      ∑ i, (if i = k then 0 else 2 * z k * z i / Real.sqrt (n : ℝ)) * J ω k i := by
    funext ω
    exact deltaEnergy_eq_affine (J ω) (h ω) z k (hsym ω) (hdiag ω) hz
  rw [hfun]
  have hIntTerm : ∀ i : Fin n,
      Integrable (fun ω =>
        (if i = k then 0 else 2 * z k * z i / Real.sqrt (n : ℝ)) * J ω k i) μ := by
    intro i
    exact (hIntJ i).const_mul _
  rw [integral_add (hInth.const_mul _) (integrable_finsetSum _ (fun i _ => hIntTerm i))]
  rw [integral_const_mul, hmeanh, mul_zero]
  rw [integral_finsetSum _ (fun i _ => hIntTerm i)]
  have hzero : ∀ i : Fin n,
      ∫ ω, (if i = k then 0 else 2 * z k * z i / Real.sqrt (n : ℝ)) * J ω k i ∂μ = 0 := by
    intro i
    rw [integral_const_mul]
    by_cases hik : i = k
    · simp [hik]
    · rw [hmeanJ i hik, mul_zero]
  rw [Finset.sum_eq_zero (fun i _ => hzero i)]
  ring

/-- The characteristic time scale `1/√(J² + h²)` of Sec. VII.  Its definition
uses only the coupling variances, not the number of spins `n`. -/
def characteristicTime (Jsq hsq : ℝ) : ℝ :=
  1 / Real.sqrt (Jsq + hsq)

/-- The characteristic time is positive whenever the energy scales are
positive. -/
theorem characteristicTime_pos {Jsq hsq : ℝ} (h : 0 < Jsq + hsq) :
    0 < characteristicTime Jsq hsq := by
  unfold characteristicTime
  exact one_div_pos.mpr (Real.sqrt_pos.2 h)

end Qatlib.Papers.PontryaginVQA16.MainResults.SKPulseDuration
