/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ReflectQuery10.MainResults.BarePowerTestModel
import Mathlib.Tactic.Linarith
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp

set_option backward.isDefEq.respectTransparency false

/-!
# Reichardt 2010 — Algorithm 3, the bare-power test: completeness

Fixed source: Ben W. Reichardt, *Reflections for quantum query algorithms*,
arXiv:1005.1601v1, Section 2, third algorithm (p. 5), Proposition 3.6 (p. 9).

The source's completeness clause for the third algorithm is the "crude bound" on
p. 9: if `f x = 1`, then `p₁ = E_{T∈[τ]} |⟨0|U_x^T|0⟩|² ≥ (9/10 − 1/10)² = 64%`.
The argument is exactly the one recorded here: Lemma 3.4's true clause supplies a
nonzero `U_x`-fixed vector `ψ` whose root Born mass in `ψ` is at least `9/10`; in
the orthogonal split `|0⟩ = c ψ + w` the fixed part contributes `9/10` and the
whole moving part `w` contributes at most `‖w‖² ≤ 1/10`, so *every* individual
power keeps root amplitude at least `4/5`, and the uniform average of its squares
is at least `(4/5)² = 64/100`.

The soundness clause of Proposition 3.6 (`f x = 0` gives `p₁ ≤ 61%`) is *not*
proved here; it needs source Eqs. (3.19)–(3.27), i.e. the paired `|β⟩`/`|−β⟩`
phase cancellation, and is recorded as the remaining gap of the claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.ReflectQuery10.MainResults

open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.QueryComplexity.Reflections
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open scoped BigOperators

/-- A real shift of a complex number lowers the norm by at most the imaginary part. -/
theorem barePower_norm_ofReal_add_lower (R : ℝ) (X : ℂ) :
    R - ‖X‖ ≤ ‖(R : ℂ) + X‖ := by
  have h1 : |R + X.re| ≤ ‖(R : ℂ) + X‖ := by
    have h := Complex.abs_re_le_norm ((R : ℂ) + X)
    rwa [Complex.add_re, Complex.ofReal_re] at h
  have h2 : R - ‖X‖ ≤ |R + X.re| := by
    have hy : |X.re| ≤ ‖X‖ := Complex.abs_re_le_norm X
    have h3 : |R| ≤ |R + X.re| + |X.re| := by
      have h := abs_add_le (R + X.re) (-X.re)
      rw [show R + X.re + -X.re = R by ring, abs_neg] at h
      exact h
    have h4 : R ≤ |R| := le_abs_self R
    linarith
  linarith

/-! ## Bilinear bookkeeping for the library inner product -/

variable {J : Type} [Fintype J] [DecidableEq J]

/-- `⟨z|φ⟩` reads the single amplitude `φ z`. -/
theorem barePower_inner_ket_left (z : J) (v : QState J) : Inner (Ket z) v = v z := by
  rw [inner_apply, Finset.sum_eq_single z]
  · simp [Ket]
  · intro k _ hk
    simp [Ket, hk]
  · simp

/-- `⟨φ|z⟩` reads the conjugate amplitude `conj (φ z)`. -/
theorem barePower_inner_ket_right (z : J) (v : QState J) : Inner v (Ket z) = star (v z) := by
  rw [inner_apply, Finset.sum_eq_single z]
  · simp [Ket]
  · intro k _ hk
    simp [Ket, hk]
  · simp

omit [DecidableEq J] in
/-- The library inner product is additive in its first argument. -/
theorem barePower_inner_add_left (a b c : QState J) :
    Inner (a + b) c = Inner a c + Inner b c := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct,
    Pi.add_apply, Pi.star_apply, star_add, add_mul, Finset.sum_add_distrib]

omit [DecidableEq J] in
/-- The library inner product is additive in its second argument. -/
theorem barePower_inner_add_right (a b c : QState J) :
    Inner a (b + c) = Inner a b + Inner a c := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct,
    Pi.add_apply, mul_add, Finset.sum_add_distrib]

omit [DecidableEq J] in
/-- The library inner product is additive in subtraction on the second argument. -/
theorem barePower_inner_sub_right (a b c : QState J) :
    Inner a (b - c) = Inner a b - Inner a c := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct,
    Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq J] in
/-- The library inner product is conjugate-linear in its first argument. -/
theorem barePower_inner_smul_left (x : ℂ) (a b : QState J) :
    Inner (x • a) b = star x * Inner a b := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct,
    Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

omit [DecidableEq J] in
/-- The library inner product is linear in its second argument. -/
theorem barePower_inner_smul_right (x : ℂ) (a b : QState J) :
    Inner a (x • b) = x * Inner a b := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

omit [DecidableEq J] in
/-- The library inner product is conjugate-symmetric. -/
theorem barePower_inner_conj (a b : QState J) : Inner b a = star (Inner a b) := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct,
    Pi.star_apply, star_sum, star_mul, star_star, mul_comm]

/-! ## The source's crude completeness bound -/

/-- **The paper's crude bound `(9/10 − 1/10)² = 64%` at a single power.**  If a
unitary `U` fixes a nonzero vector `φ` whose root Born mass is at least `9/10` of
`‖φ‖²`, then every power `U^k` keeps the root amplitude at modulus at least `4/5`.

Proof (source p. 9): write `|0⟩ = c φ + w` with `c = conj (φ 0) / ‖φ‖²`, so
`⟨φ|w⟩ = 0`, the fixed part has mass `‖c‖² ‖φ‖² ≥ 9/10`, and the moving part
`U^k w` contributes at most `‖w‖² = 1 − ‖c‖² ‖φ‖² ≤ 1/10` to `⟨0|U^k|0⟩`. -/
theorem bare_power_fixed_lower (U : Matrix J J ℂ) (hU : U ∈ Matrix.unitaryGroup J ℂ)
    (φ : QState J) (hφ : φ ≠ 0) (hfix : U *ᵥ φ = φ) (z : J)
    (hover : (9 / 10 : ℝ) * (∑ i, ‖φ i‖ ^ 2) ≤ ‖φ z‖ ^ 2) (k : ℕ) :
    (16 / 25 : ℝ) ≤ ‖(U ^ k *ᵥ Ket z) z‖ ^ 2 := by
  classical
  set N : ℝ := ∑ i, ‖φ i‖ ^ 2 with hNdef
  have hNpos : 0 < N := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hφ
    have h1 : 0 < ‖φ i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
    have h2 : ‖φ i‖ ^ 2 ≤ N := by
      rw [hNdef]
      exact Finset.single_le_sum (fun j _ => sq_nonneg ‖φ j‖) (Finset.mem_univ i)
    linarith
  set c : ℂ := star (φ z) / (N : ℂ) with hcdef
  set w : QState J := Ket z - c • φ with hwdef
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hinnerφφ : Inner φ φ = (N : ℂ) := by
    rw [inner_self, ← Complex.ofReal_sum, hNdef]
  have horth : Inner φ w = 0 := by
    rw [hwdef, barePower_inner_sub_right, barePower_inner_ket_right,
      barePower_inner_smul_right, hinnerφφ, hcdef]
    field_simp
    ring
  have hwhort : Inner w φ = 0 := by
    rw [barePower_inner_conj, horth, star_zero]
  have hsplit : c • φ + w = Ket z := by
    rw [hwdef]
    abel
  have hpowφ (j : ℕ) : U ^ j *ᵥ φ = φ := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hfix]
  have hpoww : Inner φ (U ^ k *ᵥ w) = 0 := by
    have he := inner_applyGate ((Matrix.unitaryGroup J ℂ).pow_mem hU k) φ w
    simp only [ApplyGate] at he
    rw [hpowφ k] at he
    rw [he, horth]
  have hstarc : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hprod : c * (star c * (N : ℂ)) = ((‖c‖ ^ 2 * N : ℝ) : ℂ) := by
    rw [← mul_assoc, hstarc, ← Complex.ofReal_mul]
  have hkey : Inner (Ket z) (U ^ k *ᵥ Ket z) =
      ((‖c‖ ^ 2 * N : ℝ) : ℂ) + Inner w (U ^ k *ᵥ w) := by
    have hUk : U ^ k *ᵥ Ket z = c • φ + U ^ k *ᵥ w := by
      rw [← hsplit, Matrix.mulVec_add, Matrix.mulVec_smul, hpowφ]
    have h1 : Inner (Ket z) (U ^ k *ᵥ Ket z) =
        Inner (c • φ + w) (c • φ + U ^ k *ᵥ w) := by rw [hUk, ← hsplit]
    rw [h1]
    simp only [barePower_inner_add_left, barePower_inner_add_right,
      barePower_inner_smul_left, barePower_inner_smul_right, hpoww, hwhort,
      mul_zero, add_zero, zero_add]
    rw [hinnerφφ, hprod]
  have hkey0 : Inner (Ket z) (Ket z) = ((‖c‖ ^ 2 * N : ℝ) : ℂ) + Inner w w := by
    have h1 : Inner (Ket z) (Ket z) = Inner (c • φ + w) (c • φ + w) := by rw [← hsplit]
    rw [h1]
    simp only [barePower_inner_add_left, barePower_inner_add_right,
      barePower_inner_smul_left, barePower_inner_smul_right, horth, hwhort,
      mul_zero, add_zero, zero_add]
    rw [hinnerφφ, hprod]
  have hKz : Inner (Ket z) (Ket z) = 1 :=
    (normalized_iff_inner_self (Ket z)).mp (normalized_ket z)
  have hww : Inner w w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self, ← Complex.ofReal_sum]
  have hwnorm : ∑ i, ‖w i‖ ^ 2 = 1 - ‖c‖ ^ 2 * N := by
    have h := hkey0
    rw [hKz, hww] at h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re] at hre
    linarith
  have hcnorm : ‖c‖ = ‖φ z‖ / N := by
    rw [hcdef, norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNpos]
  have hcN : ‖c‖ ^ 2 * N = ‖φ z‖ ^ 2 / N := by
    rw [hcnorm]
    field_simp
  have hcNlower : (9 / 10 : ℝ) ≤ ‖c‖ ^ 2 * N := by
    rw [hcN, le_div_iff₀ hNpos]
    linarith
  have hcs : ‖Inner w (U ^ k *ᵥ w)‖ ≤ ∑ i, ‖w i‖ ^ 2 := by
    have hinner : Inner w (U ^ k *ᵥ w) =
        inner ℂ (toEuclidean_fromVec w) (toEuclidean_fromVec (U ^ k *ᵥ w)) :=
      (inner_euclidean_fromVec w (U ^ k *ᵥ w)).symm
    have h1 : ‖Inner w (U ^ k *ᵥ w)‖ ≤
        ‖toEuclidean_fromVec w‖ * ‖toEuclidean_fromVec (U ^ k *ᵥ w)‖ := by
      rw [hinner]
      exact norm_inner_le_norm (toEuclidean_fromVec w) (toEuclidean_fromVec (U ^ k *ᵥ w))
    have h2 : ‖toEuclidean_fromVec (U ^ k *ᵥ w)‖ = ‖toEuclidean_fromVec w‖ :=
      norm_applyGate_of_mem_unitaryGroup ((Matrix.unitaryGroup J ℂ).pow_mem hU k) w
    rw [h2, ← pow_two, norm_toEuclidean_fromVec_sq] at h1
    exact h1
  have hmain : (4 / 5 : ℝ) ≤ ‖(U ^ k *ᵥ Ket z) z‖ := by
    rw [show (U ^ k *ᵥ Ket z) z = Inner (Ket z) (U ^ k *ᵥ Ket z) from
      (barePower_inner_ket_left z (U ^ k *ᵥ Ket z)).symm, hkey]
    have h1 := barePower_norm_ofReal_add_lower (‖c‖ ^ 2 * N) (Inner w (U ^ k *ᵥ w))
    have h2 : ‖Inner w (U ^ k *ᵥ w)‖ ≤ 1 - ‖c‖ ^ 2 * N := by
      rw [← hwnorm]; exact hcs
    linarith
  nlinarith [hmain, norm_nonneg ((U ^ k *ᵥ Ket z) z)]

/-- **Uniform averaging retains the crude bound.**  Over any positive horizon the
acceptance probability of source Algorithm 3 is at least `64/100` whenever the
per-power root amplitude stays above `4/5`. -/
theorem bare_power_mean_lower (U : Matrix J J ℂ) (hU : U ∈ Matrix.unitaryGroup J ℂ)
    (φ : QState J) (hφ : φ ≠ 0) (hfix : U *ᵥ φ = φ) (z : J)
    (hover : (9 / 10 : ℝ) * (∑ i, ‖φ i‖ ^ 2) ≤ ‖φ z‖ ^ 2)
    (τ : ℕ) (hτ : 0 < τ) :
    (16 / 25 : ℝ) ≤ barePowerScore U z τ := by
  have hterm (t : Fin τ) : (16 / 25 : ℝ) ≤ ‖barePowerState U z t z‖ ^ 2 :=
    bare_power_fixed_lower U hU φ hφ hfix z hover (t.val + 1)
  have hsum : (τ : ℝ) * (16 / 25) ≤
      ∑ t : Fin τ, ‖barePowerState U z t z‖ ^ 2 := by
    have h := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin τ))) => hterm t)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  have hτpos : (0 : ℝ) < τ := by exact_mod_cast hτ
  rw [barePowerScore]
  have hinv : (0 : ℝ) ≤ (τ : ℝ)⁻¹ := by positivity
  have hstep : (16 / 25 : ℝ) = (τ : ℝ)⁻¹ * ((τ : ℝ) * (16 / 25)) := by
    field_simp
  rw [hstep]
  exact mul_le_mul_of_nonneg_left hsum hinv

/-! ## Source-level completeness -/

/-- **Proposition 3.6, completeness clause.**  For a true input `x` (`f x = true`)
the third source algorithm accepts with probability at least `64%`: with the
source horizon `τ = ⌈10⁵W⌉`, the uniform average of `|⟨0|U_x^T|0⟩|²` is at least
`64/100`.  The source witness and the source kernel projector enter exactly as in
Lemma 3.4's true clause. -/
theorem barePower_true {X : Type} [Fintype X] [DecidableEq X] {n m : ℕ}
    (input : X → Fin n → Bool) (f : X → Bool) (v : X → Fin n → Fin m → ℂ) (W : ℝ)
    (hd : SourceDualFeasible input f v W) (hW : 1 ≤ W)
    (Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ) (hΔ : IsOrthogonalProjector Δ)
    (hk : ∀ z, adjacency input f v W *ᵥ z = 0 ↔ Δ *ᵥ z = z)
    (x : X) (hx : f x = true) :
    (64 / 100 : ℝ) ≤ barePowerScore (twoReflectionUnitary input f x Δ)
      (Sum.inr (Sum.inl ())) (Nat.ceil (100000 * W)) := by
  obtain ⟨ψ, hψne, hfix, hover⟩ :=
    reflections_true_zero_witness input f v W hd hW Δ hk x hx
  have hp := (twoReflectionConstruction X n m input f v W).2.1 x
  have hU := reflections_product_unitary _ _ hp hΔ
  have hτ : 0 < Nat.ceil (100000 * W) := by
    apply Nat.ceil_pos.mpr
    nlinarith
  have hmean := bare_power_mean_lower (twoReflectionUnitary input f x Δ) hU ψ hψne hfix
    (Sum.inr (Sum.inl ())) hover (Nat.ceil (100000 * W)) hτ
  have hconst : (64 / 100 : ℝ) = 16 / 25 := by norm_num
  rw [hconst]
  exact hmean

end Qatlib.Papers.ReflectQuery10.MainResults
