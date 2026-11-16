/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PolySysCrypto18.MainResults.Sec2Reductions.SourceMQ
public import Qatlib.Papers.PolySysCrypto18.MainResults.Sec2Reductions.SourceTheta
public import Qatlib.Papers.PolySysCrypto18.MainResults.Sec3FiniteField.SourceFiniteField
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.PolySysCrypto18.MainResults
open Qatlib.Papers.PolySysCrypto18.MainResults
open Qatlib.Papers.PolySysCrypto18.MainResults.Sec2Reductions

/-- A positive natural product absorbs a one-unit additive count slack. -/
theorem countSlack (x a b : ℕ) (ha : 1 ≤ a) :
    x * a + b ≤ (x + 1) * a * (b + 1) := by
  have h1 : x * a ≤ x * a * (b + 1) := by
    calc x * a = x * a * 1 := by simp
      _ ≤ x * a * (b + 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : b ≤ a * (b + 1) := by nlinarith
  calc x * a + b ≤ x * a * (b + 1) + a * (b + 1) := Nat.add_le_add h1 h2
    _ = (x + 1) * a * (b + 1) := by ring

/-- A positive scalar QBoolSol count has the stated fractional-power majorant. -/
theorem costMajorant (x y : ℝ) (hx : 0 < x) (hy : 1 < y) :
    ((x * y) ^ ((5 / 2 : ℝ) : ℝ)) * (x * y + x * y ^ 2) ≤
      8 * ((x ^ ((7 / 2 : ℝ) : ℝ)) * (y ^ ((9 / 2 : ℝ) : ℝ))) := by
  have hxp : (x ^ ((7 / 2 : ℝ) : ℝ)) = (x ^ ((5 / 2 : ℝ) : ℝ)) * x := by
    rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num, Real.rpow_add hx, Real.rpow_one]
  have hyp : (y ^ ((9 / 2 : ℝ) : ℝ)) = (y ^ ((5 / 2 : ℝ) : ℝ)) * y ^ 2 := by
    rw [show (9 / 2 : ℝ) = 5 / 2 + 2 by norm_num, Real.rpow_add (by linarith : 0 < y),
      Real.rpow_two]
  have hy2 : y ≤ y ^ 2 := by nlinarith
  have hsum : x * y + x * y ^ 2 ≤ 2 * (x * y ^ 2) := by
    have := mul_le_mul_of_nonneg_left hy2 hx.le
    linarith
  calc ((x * y) ^ ((5 / 2 : ℝ) : ℝ)) * (x * y + x * y ^ 2)
      = ((x ^ ((5 / 2 : ℝ) : ℝ)) * (y ^ ((5 / 2 : ℝ) : ℝ))) *
          (x * y + x * y ^ 2) := by rw [Real.mul_rpow hx.le (by linarith : 0 ≤ y)]
    _ ≤ ((x ^ ((5 / 2 : ℝ) : ℝ)) * (y ^ ((5 / 2 : ℝ) : ℝ))) *
          (2 * (x * y ^ 2)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * ((x ^ ((7 / 2 : ℝ) : ℝ)) * (y ^ ((9 / 2 : ℝ) : ℝ))) := by
      rw [hxp, hyp]; ring
    _ ≤ 8 * ((x ^ ((7 / 2 : ℝ) : ℝ)) * (y ^ ((9 / 2 : ℝ) : ℝ))) := by
      have hp : 0 ≤ (x ^ ((7 / 2 : ℝ) : ℝ)) * (y ^ ((9 / 2 : ℝ) : ℝ)) := by positivity
      linarith

namespace Sec3FiniteField
def pSparseness (p TF : ℕ) : ℕ := bSparseness p TF + (Nat.log2 TF + 1)
def pIndets (p n TF : ℕ) : ℕ := xBitCount p n + (Nat.log2 TF + 1)
def qBoolSolCost (N T κ logInvε : ℝ) : ℝ :=
  (N ^ ((5 / 2 : ℝ) : ℝ)) * (N + T) * κ ^ 2 * logInvε
def bound37 (TF D logp κ logInvε : ℝ) : ℝ :=
  (TF ^ ((7 / 2 : ℝ) : ℝ)) * (D ^ ((7 / 2 : ℝ) : ℝ)) *
    (logp ^ ((9 / 2 : ℝ) : ℝ)) * κ ^ 2 * logInvε
def derived37 (TF D logp κ logInvε : ℝ) : ℝ :=
  qBoolSolCost (TF * D * logp) (TF * D * logp ^ 2) κ logInvε
def bound39 (n TF logd logp κ logInvε : ℝ) : ℝ :=
  (n ^ ((7 / 2 : ℝ) : ℝ)) * (TF ^ ((7 / 2 : ℝ) : ℝ)) *
    (logd ^ ((7 / 2 : ℝ) : ℝ)) * (logp ^ ((9 / 2 : ℝ) : ℝ)) * κ ^ 2 * logInvε
def bound313 (m TF D logp κ logInvε : ℝ) : ℝ :=
  (m ^ ((11 / 2 : ℝ) : ℝ)) * (TF ^ ((7 / 2 : ℝ) : ℝ)) * (D ^ ((7 / 2 : ℝ) : ℝ)) *
    (logp ^ ((9 / 2 : ℝ) : ℝ)) * κ ^ 2 * logInvε

/-- The expanded Boolean counts satisfy the explicit natural-number slack bounds. -/
theorem lemma_3_3 (p n TF : ℕ) (_hTF : 1 ≤ TF) :
    pSparseness p TF ≤ (TF + 1) * (Nat.log2 (p - 1) + 1) ^ 2 * (Nat.log2 TF + 2) ∧
    pIndets p n TF ≤ (n + 1) * (Nat.log2 (p - 1) + 1) * (Nat.log2 TF + 2) := by
  constructor
  · simpa [pSparseness, bSparseness, Nat.add_assoc] using
      countSlack TF ((Nat.log2 (p - 1) + 1) ^ 2) (Nat.log2 TF + 1)
        (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))
  · simpa [pIndets, xBitCount, Nat.add_assoc] using
      countSlack n (Nat.log2 (p - 1) + 1) (Nat.log2 TF + 1) (by omega)

/-- The linear Boolean count obeys the corresponding product slack bound. -/
theorem corollary_3_4 (p TF : ℕ) (_hTF : 1 ≤ TF) :
    TF * (Nat.log2 (p - 1) + 1) + (Nat.log2 TF + 1) ≤
      (TF + 1) * (Nat.log2 (p - 1) + 1) * (Nat.log2 TF + 2) := by
  simpa [Nat.add_assoc] using
    countSlack TF (Nat.log2 (p - 1) + 1) (Nat.log2 TF + 1) (by omega)

/-- Substitution of the MQ counts gives the reported scalar cost majorant. -/
theorem theorem_3_7 (TF D logp κ logInvε : ℝ)
    (hTF : 0 < TF) (hD : 0 < D) (hlogp : 1 < logp) (_hκ : 0 < κ) (hε : 0 < logInvε) :
    derived37 TF D logp κ logInvε ≤ 8 * bound37 TF D logp κ logInvε := by
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (costMajorant (TF * D) logp (mul_pos hTF hD) hlogp)
      (sq_nonneg κ)) hε.le
  simpa [derived37, qBoolSolCost, bound37, Real.mul_rpow hTF.le hD.le,
    mul_assoc] using h

/-- The MQ count bounds remain valid after Boolean expansion. -/
theorem lemma_3_8 (pp : PolyParams) (logp : ℕ) (hTF : 1 ≤ pp.TF) (hD : 1 ≤ pp.D) :
    pp.sparseness * (logp + 1) ^ 2 ≤ 7 * pp.TF * pp.D * (logp + 1) ^ 2 ∧
    pp.numIndets * (logp + 1) ≤ 4 * pp.TF * pp.D * (logp + 1) := by
  have h := lemma_2_3 pp hTF hD
  exact ⟨Nat.mul_le_mul_right _ h.2.2.2, Nat.mul_le_mul_right _ h.2.1⟩

/-- Splitting a positive degree product gives the same fractional-power cost. -/
theorem corollary_3_9 (n TF logd logp κ logInvε : ℝ)
    (hn : 0 < n) (hTF : 0 < TF) (hlogd : 0 < logd) (hlogp : 1 < logp)
    (hκ : 0 < κ) (hε : 0 < logInvε) :
    bound37 TF (n * logd) logp κ logInvε ≤
      8 * bound39 n TF logd logp κ logInvε := by
  have heq : bound37 TF (n * logd) logp κ logInvε = bound39 n TF logd logp κ logInvε := by
    unfold bound37 bound39
    rw [Real.mul_rpow hn.le hlogd.le]
    ring
  rw [heq]
  have hnon : 0 ≤ bound39 n TF logd logp κ logInvε := by unfold bound39; positivity
  linarith

/-- Multiplying the base cost bound by the field-extension factor preserves it. -/
theorem theorem_3_13 (m TF D logp κ logInvε : ℝ)
    (hm : 0 < m) (hTF : 0 < TF) (hD : 0 < D) (hlogp : 1 < logp)
    (hκ : 0 < κ) (hε : 0 < logInvε) :
    (m ^ ((11 / 2 : ℝ) : ℝ)) * derived37 TF D logp κ logInvε ≤
      8 * bound313 m TF D logp κ logInvε := by
  have h := mul_le_mul_of_nonneg_left (theorem_3_7 TF D logp κ logInvε hTF hD hlogp hκ hε)
    (Real.rpow_nonneg hm.le (11 / 2 : ℝ))
  simpa [bound313, bound37, mul_assoc, mul_left_comm, mul_comm] using h
end Sec3FiniteField

open Sec3FiniteField
namespace Sec4Inequalities
def bound47 (m n TG dg h κ logInvε : ℝ) : ℝ :=
  ((m + n) ^ ((7 / 2 : ℝ) : ℝ)) * (TG ^ ((7 / 2 : ℝ) : ℝ)) *
    (dg ^ ((9 / 2 : ℝ) : ℝ)) * (h ^ ((9 / 2 : ℝ) : ℝ)) * κ ^ 2 * logInvε
def bound48 (m TG dg h κ logInvε : ℝ) : ℝ :=
  (m ^ ((7 / 2 : ℝ) : ℝ)) * (TG ^ ((7 / 2 : ℝ) : ℝ)) *
    (dg ^ ((9 / 2 : ℝ) : ℝ)) * (h ^ ((9 / 2 : ℝ) : ℝ)) * κ ^ 2 * logInvε

/-- Expanding the two positive inequality-count scales yields their cost bound. -/
theorem proposition_4_7 (m n TG dg h κ logInvε : ℝ)
    (hmn : 0 < m + n) (hTG : 0 < TG) (hdg : 1 < dg) (hh : 1 < h)
    (_hκ : 0 < κ) (hε : 0 < logInvε) :
    qBoolSolCost ((m + n) * TG * dg * h) ((m + n) * TG * dg ^ 2 * h ^ 2) κ logInvε ≤
      8 * bound47 m n TG dg h κ logInvε := by
  have hdg0 : 0 < dg := by linarith
  have hh0 : 0 < h := by linarith
  have hprod : 1 < dg * h := by nlinarith
  have hc := costMajorant ((m + n) * TG) (dg * h) (mul_pos hmn hTG) hprod
  have hc' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (sq_nonneg κ)) hε.le
  simpa [qBoolSolCost, bound47, mul_pow,
    Real.mul_rpow hmn.le hTG.le, Real.mul_rpow hdg0.le hh0.le,
    mul_assoc] using hc'

/-- The pure integer inequality-count scale is the zero-field-variable case. -/
theorem proposition_4_8 (m TG dg h κ logInvε : ℝ)
    (hm : 0 < m) (hTG : 0 < TG) (hdg : 1 < dg) (hh : 1 < h)
    (hκ : 0 < κ) (hε : 0 < logInvε) :
    qBoolSolCost (m * TG * dg * h) (m * TG * dg ^ 2 * h ^ 2) κ logInvε ≤
      8 * bound48 m TG dg h κ logInvε := by
  simpa [bound47, bound48] using proposition_4_7 m 0 TG dg h κ logInvε
    (by simpa using hm) hTG hdg hh hκ hε
end Sec4Inequalities

namespace Sec6Noise
def bound63 (n TF logp κ logInvε : ℝ) : ℝ :=
  (n ^ ((7 / 2 : ℝ) : ℝ)) * (TF ^ ((7 / 2 : ℝ) : ℝ)) * (logp ^ (8 : ℝ)) * κ ^ 2 * logInvε

/-- The noise reduction count has the stated eighth-power logarithmic majorant. -/
theorem proposition_6_3 (n TF logp κ logInvε : ℝ)
    (hn : 0 < n) (hTF : 0 < TF) (hlogp : 1 < logp) (_hκ : 0 < κ) (hε : 0 < logInvε) :
    qBoolSolCost (TF * n * logp ^ 2) (TF * n * logp ^ 3) κ logInvε ≤
      8 * bound63 n TF logp κ logInvε := by
  have hl : 0 < logp := by linarith
  have hc := costMajorant (TF * n * logp) logp (mul_pos (mul_pos hTF hn) hl) hlogp
  have hc' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (sq_nonneg κ)) hε.le
  have hp : (logp ^ ((7 / 2 : ℝ) : ℝ)) * (logp ^ ((9 / 2 : ℝ) : ℝ)) = (logp ^ (8 : ℝ)) := by
    rw [← Real.rpow_add hl]
    norm_num
  convert hc' using 1 <;> simp only [qBoolSolCost, bound63,
    Real.mul_rpow (mul_pos hTF hn).le hl.le, Real.mul_rpow hTF.le hn.le]
  · congr 2; ring
  · rw [show (TF ^ ((7 / 2 : ℝ) : ℝ)) * (n ^ ((7 / 2 : ℝ) : ℝ)) *
      (logp ^ ((7 / 2 : ℝ) : ℝ)) * (logp ^ ((9 / 2 : ℝ) : ℝ)) =
      (n ^ ((7 / 2 : ℝ) : ℝ)) * (TF ^ ((7 / 2 : ℝ) : ℝ)) *
        ((logp ^ ((7 / 2 : ℝ) : ℝ)) * (logp ^ ((9 / 2 : ℝ) : ℝ))) by ring]
    rw [hp]
    ring
end Sec6Noise

namespace Sec7SIS
def bound74 (n TF logd logp κ logInvε : ℝ) : ℝ :=
  (n ^ ((7 / 2 : ℝ) : ℝ)) * (TF ^ ((7 / 2 : ℝ) : ℝ)) * (logd ^ ((7 / 2 : ℝ) : ℝ)) *
    (logp ^ ((9 / 2 : ℝ) : ℝ)) * κ ^ 2 * logInvε

/-- The generic SIS polynomial reduction has the claimed scalar cost majorant. -/
theorem proposition_7_4 (n TF logd logp κ logInvε : ℝ)
    (hn : 0 < n) (hTF : 0 < TF) (hlogd : 0 < logd) (hlogp : 1 < logp)
    (_hκ : 0 < κ) (hε : 0 < logInvε) :
    qBoolSolCost (n * TF * logd * logp) (n * TF * logd * logp ^ 2) κ logInvε ≤
      8 * bound74 n TF logd logp κ logInvε := by
  have hc := costMajorant (n * TF * logd) logp (mul_pos (mul_pos hn hTF) hlogd) hlogp
  have hc' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (sq_nonneg κ)) hε.le
  simpa [qBoolSolCost, bound74,
    Real.mul_rpow (mul_pos hn hTF).le hlogd.le, Real.mul_rpow hn.le hTF.le,
    Real.mul_rpow hn.le (mul_pos hTF hlogd).le, Real.mul_rpow hTF.le hlogd.le,
    mul_assoc] using hc'

/-- The minimum-norm scalar statement is identical to the SIS scalar bound. -/
theorem proposition_7_6 (n TF logd logp κ logInvε : ℝ)
    (hn : 0 < n) (hTF : 0 < TF) (hlogd : 0 < logd) (hlogp : 1 < logp)
    (hκ : 0 < κ) (hε : 0 < logInvε) :
    qBoolSolCost (n * TF * logd * logp) (n * TF * logd * logp ^ 2) κ logInvε ≤
      8 * bound74 n TF logd logp κ logInvε :=
  proposition_7_4 n TF logd logp κ logInvε hn hTF hlogd hlogp hκ hε

/-- A nonzero vector of integral multiples of the modulus strictly increases the Euclidean norm of a vector whose coordinates lie in the centered interval of radius `(p - 1) / 2`. -/
theorem lemma_7_2 {p n : ℕ} (hp : 2 ≤ p) (X : Fin n → ℝ)
    (hX : ∀ i, |X i| ≤ ((p : ℝ) - 1) / 2)
    (v : Fin n → ℝ) (hv : ∀ i, ∃ k : ℤ, v i = (p : ℝ) * k) (hvne : v ≠ 0) :
    l2Norm X < l2Norm (fun i => X i + v i) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hstrict : ∀ i, v i ≠ 0 → (X i) ^ 2 < (X i + v i) ^ 2 := by
    intro i hvi
    obtain ⟨k, hk⟩ := hv i
    have hk0 : k ≠ 0 := by intro h; simp [h] at hk; exact hvi hk
    have hks : (1 : ℤ) ≤ k ∨ k ≤ -1 := by omega
    have hxi := abs_le.mp (hX i)
    rcases hks with hpos | hneg
    · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hpos
      have hvr : (p : ℝ) ≤ v i := by rw [hk]; nlinarith
      have hh : 0 < v i * (2 * X i + v i) := mul_pos (by linarith) (by linarith)
      nlinarith
    · have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast hneg
      have hvr : v i ≤ -(p : ℝ) := by rw [hk]; nlinarith
      have hh : 0 < v i * (2 * X i + v i) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
      nlinarith
  have hle : ∀ i, (X i) ^ 2 ≤ (X i + v i) ^ 2 := by
    intro i
    by_cases hi : v i = 0
    · simp [hi]
    · exact (hstrict i hi).le
  have hex : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hvne (by funext i; exact h i)
  obtain ⟨i, hi⟩ := hex
  have hsum : sqNorm X < sqNorm (fun i => X i + v i) :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hstrict i hi⟩
  exact Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (X j))) hsum
end Sec7SIS

namespace Counterexamples
def bound54 (NL TL κ E u : ℝ) : ℝ := (NL ^ ((5 / 2 : ℝ) : ℝ)) * TL * κ ^ 2 * E * u

/-- An unconstrained variable count cannot be absorbed into a fixed sparsity bound. -/
theorem cost54Counter : ¬ (qBoolSolCost 8 1 1 1 * 2 ≤ 8 * bound54 8 1 1 1 2) := by
  have hp : 0 < ((8 : ℝ) ^ ((5 / 2 : ℝ) : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  norm_num [qBoolSolCost, bound54] at *
  nlinarith

structure IsHNF {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℤ) : Prop where
  pivot_pos : ∀ j : Fin n, ∃ i : Fin m, 0 < H i j

/-- The scalar positive-pivot matrix does not bound arbitrary lattice coefficients. -/
theorem hnf82Counter :
    ∃ (H : Matrix (Fin 1) (Fin 1) ℤ) (v c : Fin 1 → ℤ),
      IsHNF H ∧ (∀ i, v i = ∑ j, c j * H i j) ∧
      ¬ |((c 0 : ℤ) : ℝ)| ≤ (infNorm H : ℝ) := by
  refine ⟨fun _ _ => 1, fun _ => 2, fun _ => 2, ⟨fun _ => ⟨0, by norm_num⟩⟩, ?_, ?_⟩
  · intro i; simp
  · norm_num [infNorm, Finset.univ_unique]

def bB (n m : ℕ) (infB : ℝ) : ℝ :=
  Real.sqrt n * Real.sqrt m * infB * (((Real.sqrt n * infB) ^ (n : ℝ)) + 1) ^ (n + 1)

/-- Arbitrary coefficients have no bound determined by a zero basis-height input. -/
theorem coefficient84Counter : ¬ (∀ _i : Fin 1, |((1 : ℤ) : ℝ)| ≤ bB 1 1 0) := by
  simp [bB]

def bound86 (m n h h0 κ E : ℝ) : ℝ :=
  m * ((n ^ 3 * h + m * h + h0) ^ ((5 / 2 : ℝ) : ℝ)) *
    (n ^ 3 * h + (h + h0) ^ 2) * κ ^ 2 * E

/-- A merely positive dimension parameter does not absorb the missing additive cost. -/
theorem cost86Counter : ¬ (qBoolSolCost 1 1 1 1 ≤ 16 * bound86 (1 / 100) 1 0 1 1 1) := by
  norm_num [qBoolSolCost, bound86]
end Counterexamples
end Qatlib.Papers.PolySysCrypto18.MainResults
