/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Theorem 3 cost assembly

Fixed arXiv:1010.4458v2, Section 4 "Main algorithm" (pp. 15--17).  The printed
Theorem 3 time `O(C κ log³(κ/ε)/ε³ · log²(1/ε))` is obtained in the source by
combining the displayed facts:

* Lemma (l₂-average running time): `Tav² ≤ A·S·k_uniq²` with the spectral sum
  `S = Σᵢ|αᵢ|²·2^{2jᵢ}`;
* Lemma (success probability): `psucc ≥ B·S·ε²/κ²` with the *same* sum `S`;
* Corollary (ratio): dividing the two cancels `S` and gives
  `Tav/√psucc = O(κ·k_uniq/ε)`;
* the variable-time amplification overhead `O(Tmax·√log Tmax +
  (Tav/√psucc)·log^1.5 Tmax)` with the source's dominance assertion
  `Tmax ≤ Tav/√psucc`, the subroutine-error choice `ε = ε_final/m` inside
  `k_uniq = O((1/ε²)·log(1/ε))`, and `O(√m·log(1/ε_final))` repetitions
  against the `1/m` Fourier-readout success probability.

This module proves the mathematical steps that carry content and no unstated
asymptotics: the shared-sum cancellation of the ratio corollary, the
domination step that absorbs the `Tmax·√log Tmax` term, and the
derivation-faithful composition of every charged factor into one explicit
bound (`thm3DerivedCost`).  The source's last displayed line then collapses
the polylogarithmic powers to `log³(κ/ε)·log²(1/ε)` "since m = O(log(κ/ε))";
that collapse removes more logarithmic powers than the preceding derivation
actually produces, so it is not asserted here.  Every hypothesis of
`thm3DerivedCost` is one of the source's displayed facts; no hypothesis
states the conclusion.

Throughout, `log^1.5 x` is written `log x * √(log x)`, exact for `x ≥ 0`.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.CostAssembly

open Real

/-- The ratio (division) step of the source's Corollary on the running time:
the same spectral sum `S = Σᵢ|αᵢ|²·2^{2jᵢ}` appears in the `Tav` upper bound
and the `psucc` lower bound, so dividing cancels it and yields
`Tav/√psucc ≤ √(A/B)·(κ/ε)·|k_uniq|`. -/
theorem vtRatioBound (κ ε A B S Tav psucc kuniq : ℝ)
    (hκ : 0 < κ) (hε : 0 < ε) (hA : 0 ≤ A) (hB : 0 < B) (hS : 0 < S)
    (hTav : 0 ≤ Tav)
    (hTavsq : Tav ^ 2 ≤ A * S * kuniq ^ 2)
    (hps : B * S * ε ^ 2 / κ ^ 2 ≤ psucc) :
    Tav / Real.sqrt psucc ≤ Real.sqrt (A / B) * (κ / ε) * |kuniq| := by
  have hpspos : 0 < psucc := lt_of_lt_of_le (by positivity) hps
  have hR : 0 ≤ Real.sqrt (A / B) * (κ / ε) * |kuniq| :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hκ.le hε.le))
      (abs_nonneg _)
  have hdenpos : 0 < B * S * ε ^ 2 / κ ^ 2 := by positivity
  have hAb := div_nonneg hA hB.le
  have hsq : (Real.sqrt (A / B)) ^ 2 = A / B := Real.sq_sqrt hAb
  have hRsq : (Real.sqrt (A / B) * (κ / ε) * |kuniq|) ^ 2
      = (A / B) * (κ / ε) ^ 2 * kuniq ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs kuniq, hsq]
  have hident : A * S * kuniq ^ 2 / (B * S * ε ^ 2 / κ ^ 2)
      = (A / B) * (κ / ε) ^ 2 * kuniq ^ 2 := by
    field_simp
  have hkey : Tav ^ 2 / psucc
      ≤ (Real.sqrt (A / B) * (κ / ε) * |kuniq|) ^ 2 := by
    calc Tav ^ 2 / psucc
        ≤ A * S * kuniq ^ 2 / (B * S * ε ^ 2 / κ ^ 2) := by
          rw [div_le_div_iff₀ hpspos hdenpos]
          calc Tav ^ 2 * (B * S * ε ^ 2 / κ ^ 2)
              ≤ (A * S * kuniq ^ 2) * (B * S * ε ^ 2 / κ ^ 2) :=
                mul_le_mul_of_nonneg_right hTavsq (by positivity)
            _ ≤ (A * S * kuniq ^ 2) * psucc :=
                mul_le_mul_of_nonneg_left hps (by positivity)
      _ = (A / B) * (κ / ε) ^ 2 * kuniq ^ 2 := hident
      _ = (Real.sqrt (A / B) * (κ / ε) * |kuniq|) ^ 2 := hRsq.symm
  rw [← abs_of_nonneg (div_nonneg hTav (Real.sqrt_nonneg psucc)),
    ← abs_of_nonneg hR, ← sq_le_sq, div_pow, Real.sq_sqrt hpspos.le]
  exact hkey

/-- The domination step of the source's running-time argument: in the
variable-time amplification overhead
`c·(Tmax·√log Tmax + (Tav/√psucc)·log^1.5(κm/εf))`, the term `Tmax·√log Tmax`
is absorbed into twice the ratio term whenever `1 ≤ Tmax ≤ Tav/√psucc` and
`Tmax ≤ κ·m/εf` with `e ≤ κ·m/εf` (so that `log(κm/εf) ≥ 1` and hence
`√log Tmax ≤ log(κm/εf)^1.5`). -/
theorem vtDominate (c tmax Tav psucc κ m εf : ℝ)
    (hc : 0 ≤ c)
    (hTav : 0 ≤ Tav)
    (htmax1 : 1 ≤ tmax)
    (htmax : tmax ≤ Tav / Real.sqrt psucc)
    (htmaxle : tmax ≤ κ * m / εf) (hkme : Real.exp 1 ≤ κ * m / εf)
    (total : ℝ)
    (hvt : total ≤ c * (tmax * Real.sqrt (Real.log tmax)
        + (Tav / Real.sqrt psucc)
          * (Real.log (κ * m / εf) * Real.sqrt (Real.log (κ * m / εf))))) :
    total ≤ 2 * c * ((Tav / Real.sqrt psucc)
      * (Real.log (κ * m / εf) * Real.sqrt (Real.log (κ * m / εf)))) := by
  have hL1 : (1 : ℝ) ≤ Real.log (κ * m / εf) := by
    have hlogk : Real.log (Real.exp 1) ≤ Real.log (κ * m / εf) :=
      Real.log_le_log (Real.exp_pos 1) hkme
    rwa [Real.log_exp] at hlogk
  have hlogt : Real.log tmax ≤ Real.log (κ * m / εf) :=
    Real.log_le_log (by linarith) htmaxle
  have hsqrtlt : Real.sqrt (Real.log tmax)
      ≤ Real.log (κ * m / εf) * Real.sqrt (Real.log (κ * m / εf)) := by
    refine le_trans (Real.sqrt_le_sqrt hlogt) ?_
    exact le_trans (le_of_eq (one_mul _).symm) (mul_le_mul_of_nonneg_right hL1
      (Real.sqrt_nonneg _))
  have hstep : tmax * Real.sqrt (Real.log tmax)
      ≤ (Tav / Real.sqrt psucc)
        * (Real.log (κ * m / εf) * Real.sqrt (Real.log (κ * m / εf))) :=
    mul_le_mul htmax hsqrtlt (Real.sqrt_nonneg _)
      (div_nonneg hTav (Real.sqrt_nonneg psucc))
  refine le_trans (hvt.trans (mul_le_mul_of_nonneg_left
    (add_le_add hstep (le_refl _)) hc)) ?_
  exact le_of_eq (by ring)

/-- The derivation-faithful composed cost bound for Theorem 3.  Each
hypothesis is one displayed source fact: `hratio` is the ratio corollary with
the subroutine-error choice `ε = εf/m` substituted into
`k_uniq ≤ cu·(m/εf)²·log(m/εf)`, `hvt` is the variable-time amplification
overhead charged per repetition, and the `√m·log(1/εf)` repetitions against
the `1/m` Fourier success are folded into the leading constant of `hvt`.
The conclusion multiplies every charged factor with the exact powers the
derivation produces. -/
theorem thm3DerivedCost (κ εf m Tav psucc tmax total : ℝ)
    (cu cv cr : ℝ) (hκ : 0 < κ) (hεf : 0 < εf) (hεf1 : εf ≤ 1) (hm : 1 ≤ m)
    (_hcu : 0 ≤ cu) (_hcv : 0 ≤ cv) (hcr : 0 ≤ cr)
    (hkm : Real.exp 1 ≤ κ * m / εf)
    (hratio : Tav / Real.sqrt psucc
      ≤ cv * (κ * m / εf) * (cu * (m / εf) ^ 2 * Real.log (m / εf)))
    (hvt : total ≤ cr * (Real.sqrt m * Real.log (1 / εf)) * (tmax
        * Real.sqrt (Real.log tmax)
        + (Tav / Real.sqrt psucc)
          * (Real.log (κ * m / εf) * Real.sqrt (Real.log (κ * m / εf)))))
    (hTav : 0 ≤ Tav)
    (htmax1 : 1 ≤ tmax)
    (htmax : tmax ≤ Tav / Real.sqrt psucc)
    (htmaxle : tmax ≤ κ * m / εf) :
    total ≤ (2 * cr * cv * cu) * κ * m ^ 3 * Real.sqrt m * Real.log (m / εf)
      * (Real.log (κ * m / εf) * Real.sqrt (Real.log (κ * m / εf)))
      * Real.log (1 / εf) / εf ^ 3 := by
  have hlog1 : (0 : ℝ) ≤ Real.log (1 / εf) :=
    Real.log_nonneg (by
      rw [one_le_div_iff]
      exact Or.inl ⟨hεf, hεf1⟩)
  have hc : 0 ≤ cr * (Real.sqrt m * Real.log (1 / εf)) :=
    mul_nonneg hcr (mul_nonneg (Real.sqrt_nonneg _) hlog1)
  have hdom := vtDominate (cr * (Real.sqrt m * Real.log (1 / εf))) tmax Tav
    psucc κ m εf hc hTav htmax1 htmax htmaxle hkm total hvt
  have hLpos : (0 : ℝ) ≤ Real.log (κ * m / εf) := by
    have hlogk : Real.log (Real.exp 1) ≤ Real.log (κ * m / εf) :=
      Real.log_le_log (Real.exp_pos 1) hkm
    rw [Real.log_exp] at hlogk
    linarith
  have hR1 : (Tav / Real.sqrt psucc)
        * (Real.log (κ * m / εf) * Real.sqrt (Real.log (κ * m / εf)))
      ≤ (cv * (κ * m / εf) * (cu * (m / εf) ^ 2 * Real.log (m / εf)))
        * (Real.log (κ * m / εf) * Real.sqrt (Real.log (κ * m / εf))) :=
    mul_le_mul_of_nonneg_right hratio
      (mul_nonneg hLpos (Real.sqrt_nonneg _))
  have hX : (0 : ℝ) ≤ 2 * (cr * (Real.sqrt m * Real.log (1 / εf))) := by
    positivity
  have hstep2 : 2 * (cr * (Real.sqrt m * Real.log (1 / εf)))
        * ((Tav / Real.sqrt psucc)
          * (Real.log (κ * m / εf) * Real.sqrt (Real.log (κ * m / εf))))
      ≤ 2 * (cr * (Real.sqrt m * Real.log (1 / εf)))
        * ((cv * (κ * m / εf) * (cu * (m / εf) ^ 2 * Real.log (m / εf)))
          * (Real.log (κ * m / εf) * Real.sqrt (Real.log (κ * m / εf)))) :=
    mul_le_mul_of_nonneg_left hR1 hX
  refine le_trans (le_trans hdom hstep2) ?_
  have hEq : (2 * (cr * (Real.sqrt m * Real.log (1 / εf)))
        * ((cv * (κ * m / εf) * (cu * (m / εf) ^ 2 * Real.log (m / εf)))
          * (Real.log (κ * m / εf) * Real.sqrt (Real.log (κ * m / εf)))))
      = (2 * cr * cv * cu) * κ * m ^ 3 * Real.sqrt m * Real.log (m / εf)
        * (Real.log (κ * m / εf) * Real.sqrt (Real.log (κ * m / εf)))
        * Real.log (1 / εf) / εf ^ 3 := by
    field_simp
  rw [hEq]

end Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.CostAssembly
