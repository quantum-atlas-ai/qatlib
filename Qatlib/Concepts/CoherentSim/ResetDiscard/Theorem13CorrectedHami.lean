/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.CoherentSim.ResetDiscard.Theorem13CorrectedStat

/-!
# LCU success bounds and saturating circuits

This module proves the LCU success bound `theorem13Corrected` and constructs unitary preparation
and unpreparation matrices attaining it. It also computes explicit scalar-branch examples,
including a one-parameter phase family, within the linear-combination framework
[ChildsWiebe2012].

## Main statements

* `theorem13Corrected`: The coefficient-mass success-probability bound.
* `fig3SaturatingSuccess`: Unitary ancillary gates attaining the bound.
* `theorem13RefutedByPhaseFamily`: Explicit phase-family success and distance formulas.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix
open scoped Matrix.Norms.L2Operator

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

/-- The Figure 3 LCU circuit is unitary when all selected branches and both ancillary gates are
unitary. -/
theorem fig3CircuitUnitary (U : J → Matrix I I ℂ) (hU : ∀ m, U m ∈ Matrix.unitaryGroup I ℂ)
    (A B : Matrix J J ℂ) (hA : A ∈ Matrix.unitaryGroup J ℂ)
    (hB : B ∈ Matrix.unitaryGroup J ℂ) :
    Fig3Circuit U A B ∈ Matrix.unitaryGroup (J × I) ℂ :=
  Submonoid.mul_mem _
    (tensorGate_unitary hB (Submonoid.one_mem _))
    (Submonoid.mul_mem _ (select_unitary U hU) (tensorGate_unitary hA (Submonoid.one_mem _)))

/-- Each output coordinate of the Figure 3 circuit is the sum of branch outputs weighted by the
corresponding preparation-column and unpreparation-row entries. -/
theorem fig3Fiber (U : J → Matrix I I ℂ) (A B : Matrix J J ℂ) (j₀ : J) (ψ : QState I)
    (j : J) (i : I) :
    (Fig3Circuit U A B *ᵥ TensorState (Ket j₀) ψ) (j, i)
      = ∑ m, B j m * A m j₀ * (U m *ᵥ ψ) i := by
  have hselect : ∀ φ : QState J, ∀ q : J × I,
      (Select U *ᵥ TensorState φ ψ) q = φ q.1 * (U q.1 *ᵥ ψ) q.2 := by
    intro φ q
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Select, Matrix.of_apply,
      TensorState]
    rw [Finset.sum_eq_single q.1]
    · simp only [ite_true]
      have hsum : (∑ k : I, (U q.1) q.2 k * (φ q.1 * ψ k))
          = φ q.1 * ((U q.1 *ᵥ ψ) q.2) := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      simpa only [smul_eq_mul] using! hsum
    · intro m _ hm
      have hne : ¬(q.1 = m) := fun e => hm e.symm
      rw [Finset.sum_eq_zero]
      intro k _
      rw [ite_eq_right hne]
      ring
    · intro hcon
      exact absurd (Finset.mem_univ q.1) hcon
  have hentry : ∀ (Ξ : QState (J × I)) (x : J) (y : I),
      (TensorGate B (1 : Matrix I I ℂ) *ᵥ Ξ) (x, y) = ∑ m : J, B x m * Ξ (m, y) := by
    intro Ξ x y
    have hexp : ∀ m : J, ∀ k : I,
        TensorGate B (1 : Matrix I I ℂ) (x, y) (m, k)
          = B x m * (if y = k then (1 : ℂ) else 0) := by
      intro m k
      simp [TensorGate, Matrix.one_apply]
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, hexp]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_eq_single y]
    · rw [ite_eq_left rfl]
      ring
    · intro k _ hk
      rw [ite_eq_right (show ¬(y = k) from fun e => hk e.symm)]
      ring
    · intro hcon
      exact absurd (Finset.mem_univ y) hcon
  have h1 : (Fig3Circuit U A B *ᵥ TensorState (Ket j₀) ψ) (j, i)
      = (TensorGate B 1 *ᵥ (Select U *ᵥ TensorState (A *ᵥ Ket j₀) ψ)) (j, i) := by
    rw [Fig3Circuit, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_tensorGate,
      Matrix.one_mulVec]
  rw [h1, hentry]
  simp only [hselect]
  exact Finset.sum_congr rfl fun m _ => by rw [mulVec_ket_apply, mul_assoc]

/-- When the ancillary coefficient products equal `K * C m`, the selected-fiber success mass
equals `‖K‖²` times the squared norm of the weighted branch output. -/
theorem fig3SuccessProb_of_coeff (U : J → Matrix I I ℂ) (A B : Matrix J J ℂ) (C : J → ℂ)
    (j₀ : J) (K : ℂ) (hA3 : ∀ m, B j₀ m * A m j₀ = K * C m) (ψ : QState I) :
    Fig3SuccessProb U A B j₀ ψ
      = ‖K‖ ^ 2 * ∑ i, ‖((∑ m, C m • U m) *ᵥ ψ) i‖ ^ 2 := by
  have hsum : Fig3SuccessProb U A B j₀ ψ
      = ∑ i, ‖(Fig3Circuit U A B *ᵥ TensorState (Ket j₀) ψ) (j₀, i)‖ ^ 2 := by
    unfold Fig3SuccessProb MeasureProb BornProb ApplyGate
    rw [Finset.sum_product, Finset.sum_singleton]
  have hd : ∀ i : I, ((∑ m, C m • U m) *ᵥ ψ) i = ∑ m, C m * (U m *ᵥ ψ) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.mul_sum, Matrix.smul_apply,
      smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hfib : ∀ i : I, (Fig3Circuit U A B *ᵥ TensorState (Ket j₀) ψ) (j₀, i)
      = K * ((∑ m, C m • U m) *ᵥ ψ) i := by
    intro i
    rw [fig3Fiber U A B j₀ ψ j₀ i, hd i]
    have hstep : ∀ m : J, B j₀ m * A m j₀ * (U m *ᵥ ψ) i
        = K * (C m * (U m *ᵥ ψ) i) := by
      intro m
      rw [hA3 m]
      ring
    rw [Finset.sum_congr rfl fun m _ => hstep m, ← Finset.mul_sum]
  rw [hsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [hfib i, norm_mul, mul_pow]

omit [DecidableEq J] in

/-- The sum of products of two nonnegative real families is bounded by the product of their
Euclidean norms. -/
theorem cauchySchwarzSum (x y : J → ℝ) (hx : ∀ m, 0 ≤ x m) (hy : ∀ m, 0 ≤ y m) :
    ∑ m, x m * y m ≤ Real.sqrt (∑ m, x m ^ 2) * Real.sqrt (∑ m, y m ^ 2) := by
  have h := abs_real_inner_le_norm (x := WithLp.toLp 2 x) (WithLp.toLp 2 y)
  rw [EuclideanSpace.inner_toLp_toLp, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
  simp only [dotProduct, Pi.star_apply, star_trivial] at h
  have e1 : ∑ m, (‖x m‖ ^ 2) = ∑ m, x m ^ 2 :=
    Finset.sum_congr rfl fun m _ => by rw [Real.norm_eq_abs, abs_of_nonneg (hx m)]
  have e2 : ∑ m, (‖y m‖ ^ 2) = ∑ m, y m ^ 2 :=
    Finset.sum_congr rfl fun m _ => by rw [Real.norm_eq_abs, abs_of_nonneg (hy m)]
  rw [e1, e2] at h
  calc ∑ m, x m * y m = ∑ m, y m * x m := Finset.sum_congr rfl fun m _ => mul_comm _ _
    _ ≤ |∑ m, y m * x m| := le_abs_self _
    _ ≤ _ := h

/-- Each column of a unitary matrix has squared norm sum one. -/
theorem fig3ColNormSq {A : Matrix J J ℂ} (hA : A ∈ Matrix.unitaryGroup J ℂ) (j₀ : J) :
    ∑ m, ‖A m j₀‖ ^ 2 = 1 := by
  have h0 := (Matrix.mem_unitaryGroup_iff' (A := A)).mp hA
  rw [Matrix.star_eq_conjTranspose] at h0
  have e : ∑ m, (starRingEnd ℂ) (A m j₀) * A m j₀ = 1 := by
    have h1 : (Aᴴ * A) j₀ j₀ = (1 : Matrix J J ℂ) j₀ j₀ := by rw [h0]
    simpa using! h1
  have conv : ∀ m : J, ((‖A m j₀‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) (A m j₀) * A m j₀ := by
    intro m
    rw [← Complex.normSq_eq_norm_sq]
    exact Complex.normSq_eq_conj_mul_self
  have s : ∑ m, ((‖A m j₀‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [Finset.sum_congr rfl fun m _ => conv m, e]
  exact_mod_cast s

/-- Each row of a unitary matrix has squared norm sum one. -/
theorem fig3RowNormSq {B : Matrix J J ℂ} (hB : B ∈ Matrix.unitaryGroup J ℂ) (j₀ : J) :
    ∑ m, ‖B j₀ m‖ ^ 2 = 1 := by
  have h0 := (Matrix.mem_unitaryGroup_iff (A := B)).mp hB
  rw [Matrix.star_eq_conjTranspose] at h0
  have e : ∑ m, B j₀ m * (starRingEnd ℂ) (B j₀ m) = 1 := by
    have h1 : (B * Bᴴ) j₀ j₀ = (1 : Matrix J J ℂ) j₀ j₀ := by rw [h0]
    simpa using! h1
  have conv : ∀ m : J, ((‖B j₀ m‖ ^ 2 : ℝ) : ℂ) = B j₀ m * (starRingEnd ℂ) (B j₀ m) := by
    intro m
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    ring
  have s : ∑ m, ((‖B j₀ m‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [Finset.sum_congr rfl fun m _ => conv m, e]
  exact_mod_cast s

/-- For unitary branches and ancillary gates satisfying the coefficient factorization, the
normalized-input success probability is bounded by the squared weighted-output norm divided
by the squared total coefficient norm [ChildsWiebe2012]. -/
theorem theorem13Corrected : Theorem13Corrected := by
  intro J I _ _ _ _ U hU C hsC A hA B hB j₀ K hA3 ψ hψ
  have hred := fig3SuccessProb_of_coeff U A B C j₀ K hA3 ψ

  have hK : ‖K‖ * (∑ m, ‖C m‖) ≤ 1 := by
    calc ‖K‖ * ∑ m, ‖C m‖ = ∑ m, ‖K‖ * ‖C m‖ := by rw [Finset.mul_sum]
      _ = ∑ m, ‖B j₀ m * A m j₀‖ := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hA3 m, norm_mul]
      _ = ∑ m, ‖B j₀ m‖ * ‖A m j₀‖ :=
          Finset.sum_congr rfl fun m _ => by rw [norm_mul]
      _ ≤ Real.sqrt (∑ m, ‖B j₀ m‖ ^ 2) * Real.sqrt (∑ m, ‖A m j₀‖ ^ 2) :=
          cauchySchwarzSum _ _ (fun m => norm_nonneg _) (fun m => norm_nonneg _)
      _ = 1 := by rw [fig3RowNormSq hB j₀, fig3ColNormSq hA j₀, Real.sqrt_one, mul_one]
  have hN : 0 ≤ ∑ i, ‖((∑ m, C m • U m) *ᵥ ψ) i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs2 : 0 < (∑ m, ‖C m‖) ^ 2 := by positivity
  have hnn : 0 ≤ ‖K‖ * (∑ m, ‖C m‖) :=
    mul_nonneg (norm_nonneg K) (Finset.sum_nonneg fun m _ => norm_nonneg (C m))
  have hprod : (‖K‖ * (∑ m, ‖C m‖)) ^ 2 ≤ 1 := by
    nlinarith [hK, hnn]
  have key : ‖K‖ ^ 2 * (∑ m, ‖C m‖) ^ 2 ≤ 1 := by
    nlinarith [hprod, hnn]
  rw [hred, le_div_iff₀ hs2]
  calc ‖K‖ ^ 2 * (∑ i, ‖((∑ m, C m • U m) *ᵥ ψ) i‖ ^ 2) * (∑ m, ‖C m‖) ^ 2
      = (∑ i, ‖((∑ m, C m • U m) *ᵥ ψ) i‖ ^ 2) * (‖K‖ ^ 2 * (∑ m, ‖C m‖) ^ 2) := by ring
    _ ≤ (∑ i, ‖((∑ m, C m • U m) *ᵥ ψ) i‖ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left key hN
    _ = ∑ i, ‖((∑ m, C m • U m) *ᵥ ψ) i‖ ^ 2 := mul_one _

section ColumnCompletion

variable {K₁ : Type} [Fintype K₁] [DecidableEq K₁]

/-- Every complex vector with squared norm sum one can be prescribed as a specified column of a
unitary matrix. -/
theorem existsUnitaryColumn (j₀ : K₁) (v : QState K₁) (hv : ∑ m, ‖v m‖ ^ 2 = 1) :
    ∃ A : Matrix K₁ K₁ ℂ, A ∈ Matrix.unitaryGroup K₁ ℂ ∧ ∀ m, A m j₀ = v m := by
  classical

  set ω : ℂ := if v j₀ = 0 then 1 else (starRingEnd ℂ) (v j₀) / ‖v j₀‖ with hωdef
  have hω1 : ‖ω‖ = 1 := by
    by_cases h0 : v j₀ = 0
    · rw [hωdef, ite_eq_left h0]
      simp
    · rw [hωdef, ite_eq_right h0]
      have hz : ‖v j₀‖ ≠ 0 := by
        intro h
        exact h0 (norm_eq_zero.mp h)
      have hcast : ‖((‖v j₀‖ : ℝ) : ℂ)‖ = ‖v j₀‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (v j₀))]
      rw [norm_div, RCLike.norm_conj, hcast, div_self hz]
  have hωne : ω ≠ 0 := by
    intro h
    rw [h, norm_zero] at hω1
    exact zero_ne_one hω1
  have hωconj : ω * (starRingEnd ℂ) ω = 1 := by
    have hc0 : (starRingEnd ℂ) ω * ω = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hω1]
      push_cast
      norm_num
    rw [mul_comm]
    exact hc0
  have hconjw : (starRingEnd ℂ) ω = ω⁻¹ := by
    rw [inv_eq_one_div, eq_div_iff hωne, mul_comm]
    exact hωconj
  set v' : QState K₁ := fun m => ω * v m with hv'
  have hv'1 : ∑ m, ‖v' m‖ ^ 2 = 1 := by
    have h : ∀ m, ‖v' m‖ ^ 2 = ‖v m‖ ^ 2 := by
      intro m
      rw [hv', norm_mul, hω1]
      ring
    rw [Finset.sum_congr rfl fun m _ => h m, hv]
  have hv'j₀ : v' j₀ = ((‖v j₀‖ : ℝ) : ℂ) := by
    by_cases h0 : v j₀ = 0
    · rw [hv', hωdef, ite_eq_left h0]
      simp [h0]
    · rw [hv', hωdef, ite_eq_right h0]
      have hz : ‖v j₀‖ ≠ 0 := by
        intro h
        exact h0 (norm_eq_zero.mp h)
      show ((starRingEnd ℂ) (v j₀)) / ((‖v j₀‖ : ℝ) : ℂ) * v j₀
        = ((‖v j₀‖ : ℝ) : ℂ)
      rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq, ← Complex.ofReal_div]
      congr 1
      field_simp

  set u : QState K₁ := fun m => Ket j₀ m - v' m with hu
  have huapply : ∀ m : K₁, u m = Ket j₀ m - v' m := fun m => by simp only [hu]
  set c : ℝ := ∑ m, ‖u m‖ ^ 2 with hcu
  set uu : Matrix K₁ K₁ ℂ := Matrix.of fun j m => u j * (starRingEnd ℂ) (u m) with huu
  set H : Matrix K₁ K₁ ℂ := 1 - ((2 / c : ℝ) : ℂ) • uu with hH

  have huu2 : uu * uu = ((c : ℝ) : ℂ) • uu := by
    ext j m
    have hcsum : ∑ k, ((‖u k‖ ^ 2 : ℝ) : ℂ) = ((c : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sum]
    simp only [Matrix.mul_apply, huu, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    have hsumnd : ∀ x : K₁, u j * (starRingEnd ℂ) (u x) * (u x * (starRingEnd ℂ) (u m))
        = u j * (starRingEnd ℂ) (u m) * ((starRingEnd ℂ) (u x) * u x) := fun x => by ring
    have hcast : ∀ x : K₁, ((starRingEnd ℂ) (u x)) * u x = ((‖u x‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      rw [← Complex.normSq_eq_norm_sq]
      exact Complex.normSq_eq_conj_mul_self.symm
    rw [Finset.sum_congr rfl fun x _ => hsumnd x, ← Finset.mul_sum,
      Finset.sum_congr rfl fun x _ => hcast x, ← hcsum]
    ring
  have hq : (((2 / c : ℝ) : ℂ) * ((2 / c : ℝ) : ℂ)) * ((c : ℝ) : ℂ)
      = 2 * ((2 / c : ℝ) : ℂ) := by
    by_cases hc0 : c = 0
    · rw [hc0]
      simp
    · push_cast
      field_simp
  have hHH : H * H = 1 := by
    have hkey : (↑(2 / c : ℝ) : ℂ) • uu - (2 * (↑(2 / c : ℝ) : ℂ)) • uu
        = -(((2 / c : ℝ) : ℂ) • uu) := by
      rw [two_mul, add_smul, sub_add_eq_sub_sub, sub_self, zero_sub]
    rw [hH, sub_mul, mul_sub, mul_sub, one_mul, mul_one, smul_mul_smul, huu2, smul_smul,
      hq, one_mul, hkey, sub_neg_eq_add, sub_add_cancel]
  have huuh : uuᴴ = uu := by
    ext j m
    simp only [Matrix.conjTranspose_apply, huu, Matrix.of_apply, star_mul,
      starRingEnd_apply, star_star]
  have hHh : Hᴴ = H := by
    rw [hH, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
      huuh, ← starRingEnd_apply, Complex.conj_ofReal]

  have hvj₀le : ‖v j₀‖ ≤ 1 := by
    have h1 : ‖v j₀‖ ^ 2 ≤ ∑ m, ‖v m‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ j₀)
    rw [hv] at h1
    have hn := norm_nonneg (v j₀)
    nlinarith [h1, hn]
  have huj₀ : u j₀ = 1 - ((‖v j₀‖ : ℝ) : ℂ) := by
    rw [huapply, hv'j₀, ket_self]
  have hcform : c = 2 - 2 * ‖v j₀‖ := by
    have hu' : ∀ m : K₁, ((‖u m‖ ^ 2 : ℝ))
        = Complex.normSq (Ket j₀ m) + Complex.normSq (v' m)
          - 2 * ((Ket j₀ m * (starRingEnd ℂ) (v' m)).re : ℝ) := by
      intro m
      rw [← Complex.normSq_eq_norm_sq, huapply m, Complex.normSq_sub]
    have hket : ∑ m, Complex.normSq (Ket j₀ m) = 1 := by
      rw [Finset.sum_eq_single j₀]
      · simp [Ket]
      · intro m _ hm
        simp [Ket, hm]
      · intro hcon
        exact absurd (Finset.mem_univ j₀) hcon
    have hv'sum : ∑ m, Complex.normSq (v' m) = 1 := by
      rw [Finset.sum_congr rfl fun m _ => Complex.normSq_eq_norm_sq (v' m), hv'1]
    have hcross : ∑ m, ((Ket j₀ m * (starRingEnd ℂ) (v' m)).re : ℝ) = ‖v j₀‖ := by
      rw [Finset.sum_eq_single j₀]
      · rw [ket_self, one_mul, hv'j₀, Complex.conj_ofReal, Complex.ofReal_re]
      · intro m _ hm
        simp [Ket, hm]
      · intro hcon
        exact absurd (Finset.mem_univ j₀) hcon
    have hsplit : ∑ m, (Complex.normSq (Ket j₀ m) + Complex.normSq (v' m)
        - 2 * ((Ket j₀ m * (starRingEnd ℂ) (v' m)).re : ℝ))
        = ∑ m, Complex.normSq (Ket j₀ m) + ∑ m, Complex.normSq (v' m)
          - 2 * ∑ m, ((Ket j₀ m * (starRingEnd ℂ) (v' m)).re : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    calc c = ∑ m, ‖u m‖ ^ 2 := hcu
      _ = ∑ m, (Complex.normSq (Ket j₀ m) + Complex.normSq (v' m)
          - 2 * ((Ket j₀ m * (starRingEnd ℂ) (v' m)).re : ℝ)) :=
          Finset.sum_congr rfl fun m _ => hu' m
      _ = 2 - 2 * ‖v j₀‖ := by
          rw [hsplit, hket, hv'sum, hcross]
          ring

  have hHcol : ∀ m, H m j₀ = v' m := by
    intro m
    have hcconj : (starRingEnd ℂ) (u j₀) = u j₀ := by
      rw [huj₀, map_sub, map_one, Complex.conj_ofReal]
    have hvm : v' m = Ket j₀ m - u m := by rw [huapply m]; ring
    have huj₀c : u j₀ = ((c / 2 : ℝ) : ℂ) := by
      rw [huj₀]
      have hconv : (c : ℝ) / 2 = 1 - ‖v j₀‖ := by
        rw [hcform]
        linarith
      rw [hconv]
      push_cast
      ring
    rw [hH, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, huu,
      Matrix.of_apply, hcconj, hvm]
    by_cases hum : u m = 0
    · rw [hum, zero_mul, mul_zero, ket_apply]
    · have hpos : 0 < c := by
        have h1 : ‖u m‖ ^ 2 ≤ c := by
          rw [hcu]
          exact Finset.single_le_sum (f := fun i => ‖u i‖ ^ 2) (fun i _ => sq_nonneg _)
            (Finset.mem_univ m)
        have h2 : 0 < ‖u m‖ ^ 2 := by positivity
        linarith
      have hreal : (2 / c) * (c / 2) = (1 : ℝ) := by
        field_simp
      have hcancel : (((2 / c : ℝ) : ℂ) * ((c / 2 : ℝ) : ℂ)) = 1 := by
        rw [← Complex.ofReal_mul, hreal]
        push_cast
        norm_num
      rw [huj₀c]
      calc (if m = j₀ then (1 : ℂ) else 0) - ((2 / c : ℝ) : ℂ) * (u m * ((c / 2 : ℝ) : ℂ))
          = (if m = j₀ then (1 : ℂ) else 0)
              - (((2 / c : ℝ) : ℂ) * ((c / 2 : ℝ) : ℂ)) * u m := by ring
        _ = (if m = j₀ then (1 : ℂ) else 0) - 1 * u m := by rw [hcancel]
        _ = Ket j₀ m - u m := by rw [one_mul, ket_apply]

  refine ⟨ω⁻¹ • H, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
      hHh, smul_mul_smul, hHH, ← starRingEnd_apply, map_inv₀, hconjw, inv_inv,
      inv_mul_cancel₀ hωne, one_smul]
  · intro m
    rw [Matrix.smul_apply, smul_eq_mul, hHcol m, hv']
    show ω⁻¹ * (ω * v m) = v m
    rw [← mul_assoc, inv_mul_cancel₀ hωne, one_mul]

end ColumnCompletion

/-- For a coefficient family of positive total norm, there are unitary ancillary gates whose
selected row-column products equal the coefficients divided by their total norm. -/
theorem fig3SaturatingCircuit (j₀ : J) (C : J → ℂ)
    (hs : 0 < ∑ m, ‖C m‖) :
    ∃ A B : Matrix J J ℂ, A ∈ Matrix.unitaryGroup J ℂ ∧ B ∈ Matrix.unitaryGroup J ℂ ∧
      ∀ m, B j₀ m * A m j₀ = C m / ((∑ m, ‖C m‖ : ℝ) : ℂ) := by
  classical
  set s : ℝ := ∑ m, ‖C m‖ with hsr
  set ρ : J → ℝ := fun m => Real.sqrt (‖C m‖ / s) with hρ
  set a : QState J := fun m => if C m = 0 then 0 else C m * ((ρ m : ℝ) : ℂ) / ‖C m‖ with ha
  set b : QState J := fun m => ((ρ m : ℝ) : ℂ) with hb
  have hρ2 : ∀ m, (ρ m) ^ 2 = ‖C m‖ / s := fun m => Real.sq_sqrt (by positivity)
  have hsdiv : ∑ m, ‖C m‖ / s = 1 := by
    rw [← Finset.sum_div, ← hsr]
    exact div_self hs.ne'
  have hanorm : ∀ m, ‖a m‖ ^ 2 = ‖C m‖ / s := by
    intro m
    by_cases h0 : C m = 0
    · simp only [ha, ite_eq_left h0, h0]
      simp
    · simp only [ha, ite_eq_right h0]
      have hCn : ‖C m‖ ≠ 0 := fun h => h0 (norm_eq_zero.mp h)
      have hρn : 0 ≤ ρ m := Real.sqrt_nonneg _
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρn,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (C m)), ← hρ2 m]
      field_simp
  have hbanorm : ∑ m, ‖a m‖ ^ 2 = 1 := by
    rw [Finset.sum_congr rfl fun m _ => hanorm m, ← Finset.sum_div, ← hsr]
    exact div_self hs.ne'
  have hbbnorm : ∑ m, ‖b m‖ ^ 2 = 1 := by
    have h : ∀ m, ‖b m‖ ^ 2 = ‖C m‖ / s := by
      intro m
      rw [hb, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        hρ2 m]
    rw [Finset.sum_congr rfl fun m _ => h m, ← Finset.sum_div, ← hsr]
    exact div_self hs.ne'
  have hbconj : ∑ m, ‖(starRingEnd ℂ) (b m)‖ ^ 2 = 1 := by
    have h : ∀ m, ‖(starRingEnd ℂ) (b m)‖ ^ 2 = ‖b m‖ ^ 2 := fun m => by
      rw [RCLike.norm_conj]
    rw [Finset.sum_congr rfl fun m _ => h m, hbbnorm]
  obtain ⟨A, hAunit, hAcol⟩ := existsUnitaryColumn j₀ a hbanorm
  obtain ⟨X, hXunit, hXcol⟩ := existsUnitaryColumn j₀ (fun m => (starRingEnd ℂ) (b m)) hbconj
  refine ⟨A, Xᴴ, hAunit, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose]
    exact (Matrix.mem_unitaryGroup_iff (A := X)).mp hXunit
  · intro m
    have hXm : Xᴴ j₀ m = b m := by
      rw [Matrix.conjTranspose_apply, hXcol m, ← starRingEnd_apply, Complex.conj_conj]
    rw [hXm, hAcol m]
    by_cases h0 : C m = 0
    · simp only [hb, hρ, ha, ite_eq_left h0, h0]
      simp
    · simp only [hb, ha, ite_eq_right h0]
      have hCn : ‖C m‖ ≠ 0 := fun h => h0 (norm_eq_zero.mp h)
      have h1 : ((ρ m : ℝ) : ℂ) * ((ρ m : ℝ) : ℂ) = ((‖C m‖ / s : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, ← sq, hρ2 m]
      have h2 : ((‖C m‖ / s : ℝ) : ℂ) / ((‖C m‖ : ℝ) : ℂ) = ((1 / s : ℝ) : ℂ) := by
        rw [← Complex.ofReal_div]
        congr 1
        field_simp
      calc ((ρ m : ℝ) : ℂ) * (C m * ((ρ m : ℝ) : ℂ) / ‖C m‖)
          = C m * (((ρ m : ℝ) : ℂ) * ((ρ m : ℝ) : ℂ) / ((‖C m‖ : ℝ) : ℂ)) := by
            rw [div_eq_inv_mul]
            ring
        _ = C m * (((‖C m‖ / s : ℝ) : ℂ) / ((‖C m‖ : ℝ) : ℂ)) := by rw [h1]
        _ = C m * ((1 / s : ℝ) : ℂ) := by rw [h2]
        _ = C m / ((s : ℝ) : ℂ) := by
            rw [one_div, Complex.ofReal_inv, div_eq_inv_mul]
            ring

/-- For a coefficient family of positive total norm, unitary ancillary gates attain success mass
equal to the squared weighted-output norm divided by the squared total coefficient norm. -/
theorem fig3SaturatingSuccess (U : J → Matrix I I ℂ) (C : J → ℂ) (hs : 0 < ∑ m, ‖C m‖)
    (j₀ : J) (ψ : QState I) :
    ∃ A B : Matrix J J ℂ, A ∈ Matrix.unitaryGroup J ℂ ∧ B ∈ Matrix.unitaryGroup J ℂ ∧
      Fig3SuccessProb U A B j₀ ψ
        = (∑ i, ‖((∑ m, C m • U m) *ᵥ ψ) i‖ ^ 2) / (∑ m, ‖C m‖) ^ 2 := by
  obtain ⟨A, B, hA, hB, hcoef⟩ := fig3SaturatingCircuit j₀ C hs
  refine ⟨A, B, hA, hB, ?_⟩
  have hA3 : ∀ m, B j₀ m * A m j₀ = (((∑ m, ‖C m‖ : ℝ) : ℂ))⁻¹ * C m := by
    intro m
    rw [hcoef m]
    rw [div_eq_inv_mul]
  rw [fig3SuccessProb_of_coeff U A B C j₀ _ hA3 ψ]
  have hK : ‖(((∑ m, ‖C m‖ : ℝ) : ℂ))⁻¹‖ ^ 2 * (∑ i, ‖((∑ m, C m • U m) *ᵥ ψ) i‖ ^ 2)
      = (∑ i, ‖((∑ m, C m • U m) *ᵥ ψ) i‖ ^ 2) / (∑ m, ‖C m‖) ^ 2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, inv_pow,
      div_eq_inv_mul, ← inv_pow]
  exact hK

/-- The complex number given by the nonnegative real square root of `2 / 3`. -/
private noncomputable def cwSqrtTwoThirds : ℂ := ((Real.sqrt (2 / 3) : ℝ) : ℂ)

/-- The complex number given by the nonnegative real square root of `1 / 3`. -/
private noncomputable def cwSqrtOneThird : ℂ := ((Real.sqrt (1 / 3) : ℝ) : ℂ)

/-- The product of `cwSqrtTwoThirds` with itself equals `2 / 3`. -/
theorem cwSqrtTwoThirds_sq : cwSqrtTwoThirds * cwSqrtTwoThirds = 2 / 3 := by
  unfold cwSqrtTwoThirds
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast
  norm_num

/-- The product of `cwSqrtOneThird` with itself equals `1 / 3`. -/
theorem cwSqrtOneThird_sq : cwSqrtOneThird * cwSqrtOneThird = 1 / 3 := by
  unfold cwSqrtOneThird
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast
  norm_num

/-- The square of `cwSqrtTwoThirds` equals `2 / 3`. -/
theorem cwSqrtTwoThirds_pow : cwSqrtTwoThirds ^ 2 = 2 / 3 := by
  rw [pow_two]
  exact cwSqrtTwoThirds_sq

/-- The square of `cwSqrtOneThird` equals `1 / 3`. -/
theorem cwSqrtOneThird_pow : cwSqrtOneThird ^ 2 = 1 / 3 := by
  rw [pow_two]
  exact cwSqrtOneThird_sq

/-- A scalar multiple of the identity is unitary whenever the complex scalar has norm one. -/
theorem scalarOne_mem_unitaryGroup {z : ℂ} (hz : ‖z‖ = 1) :
    z • (1 : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, smul_mul_smul, one_mul]
  have hone : (starRingEnd ℂ) z * z = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]
    push_cast
    norm_num
  rw [starRingEnd_apply] at hone
  rw [hone, one_smul]

/-- The Boolean-indexed rotation matrix with diagonal entries `√(2 / 3)` and off-diagonal
entries `-√(1 / 3)` and `√(1 / 3)`. -/
noncomputable def cwRotation : Matrix Bool Bool ℂ :=
  Matrix.of fun j m =>
    if j then (if m then cwSqrtTwoThirds else cwSqrtOneThird)
    else if m then -cwSqrtOneThird else cwSqrtTwoThirds

/-- The explicit Boolean-indexed rotation `cwRotation` is unitary. -/
theorem cwRotation_unitary : cwRotation ∈ Matrix.unitaryGroup Bool ℂ := by
  have hreal : ∀ j m : Bool, (starRingEnd ℂ) (cwRotation j m) = cwRotation j m := by
    intro j m
    simp only [cwRotation, Matrix.of_apply, cwSqrtTwoThirds, cwSqrtOneThird]
    rcases j <;> rcases m <;> simp [Complex.conj_ofReal]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext j m
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool,
    Matrix.one_apply]
  simp only [← starRingEnd_apply]
  rw [hreal false j, hreal true j]
  rcases j <;> rcases m <;>
    simp only [cwRotation, Matrix.of_apply] <;>
    simp [cwSqrtTwoThirds_sq, cwSqrtOneThird_sq] <;>
    norm_num <;>
    ring

/-- The selected row-column product of `cwRotation` equals one third of the coefficient two or
minus one, according to the Boolean branch. -/
theorem cwRotation_coeff (m : Bool) :
    cwRotation false m * cwRotation m false = (1 / 3 : ℂ) * (if m then -1 else 2) := by
  rcases m <;>
    simp only [cwRotation, Matrix.of_apply, ite_true, ite_false, Bool.false_eq_true]
  · rw [cwSqrtTwoThirds_sq]
    norm_num
  · rw [← cwSqrtOneThird_sq]
    ring

/-- The one-dimensional branch family consisting of the identity and its negative. -/
noncomputable def cwBranchesTwoMinusOne : Bool → Matrix (Fin 1) (Fin 1) ℂ :=
  fun m => (if m then -1 else (1 : ℂ)) • 1

/-- Each branch in `cwBranchesTwoMinusOne` is unitary. -/
theorem cwBranchesTwoMinusOne_mem_unitaryGroup (m : Bool) :
    cwBranchesTwoMinusOne m ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  refine scalarOne_mem_unitaryGroup ?_
  rcases m <;> simp []

/-- The explicit rotation realizes the coefficients two and minus one with factor `1 / 3`, and
the corresponding identity and negative-identity branches give success probability one. -/
theorem theorem13RefutedByTwoMinusOne :
    (∀ m : Bool, cwRotation false m * cwRotation m false
        = (1 / 3 : ℂ) * (if m then -1 else (2 : ℂ))) ∧
      Fig3SuccessProb cwBranchesTwoMinusOne cwRotation cwRotation false (Ket (0 : Fin 1))
        = 1 := by
  refine ⟨cwRotation_coeff, ?_⟩
  rw [fig3SuccessProb_of_coeff cwBranchesTwoMinusOne cwRotation cwRotation
      (fun m => if m then -1 else (2 : ℂ)) false (1 / 3 : ℂ) cwRotation_coeff (Ket 0)]
  have hV : (∑ m : Bool, (if m then (-1 : ℂ) else 2) • cwBranchesTwoMinusOne m)
      = (3 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    simp only [Fintype.sum_bool, Bool.false_eq_true, cwBranchesTwoMinusOne, ite_true,
      ite_false, smul_smul]
    module
  rw [hV, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hket : ((3 : ℂ) • (Ket (0 : Fin 1))) = fun _ => (3 : ℂ) := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    rw [hi]
    simp [Ket]
  have hnorm : ‖(1 / 3 : ℂ)‖ ^ 2 = 1 / 9 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    norm_num
  rw [hket, hnorm, Fin.sum_univ_one]
  norm_num

/-- The complex phase candidate with real part `(n² - 1) / (n² + 1)` and imaginary part `2 * n /
(n² + 1)`. -/
noncomputable def cwZ (n : ℕ) : ℂ :=
  (((n : ℝ) ^ 2 - 1) / ((n : ℝ) ^ 2 + 1) : ℝ)
    + (((2 * (n : ℝ)) / ((n : ℝ) ^ 2 + 1) : ℝ)) * Complex.I

/-- The real part of `cwZ n` equals `(n² - 1) / (n² + 1)`. -/
theorem cwZ_re (n : ℕ) : (cwZ n).re = ((n : ℝ) ^ 2 - 1) / ((n : ℝ) ^ 2 + 1) := by
  rw [cwZ, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The imaginary part of `cwZ n` equals `2 * n / (n² + 1)`. -/
theorem cwZ_im (n : ℕ) : (cwZ n).im = (2 * (n : ℝ)) / ((n : ℝ) ^ 2 + 1) := by
  rw [cwZ, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- For positive `n`, the squared norm of `cwZ n` is one. -/
theorem cwZ_normSq (n : ℕ) (hn : 0 < n) : ‖cwZ n‖ ^ 2 = 1 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, cwZ_re, cwZ_im]
  have hne : ((n : ℝ) ^ 2 + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- The one-dimensional branch family consisting of the identity and the scalar phase `cwZ n`
times the identity. -/
noncomputable def cwBranchesPhase (n : ℕ) : Bool → Matrix (Fin 1) (Fin 1) ℂ :=
  fun m => (if m then cwZ n else (1 : ℂ)) • 1

/-- For positive `n`, each operator in the phase branch family is unitary. -/
theorem cwBranchesPhase_mem_unitaryGroup {n : ℕ} (hn : 0 < n) (m : Bool) :
    cwBranchesPhase n m ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  refine scalarOne_mem_unitaryGroup ?_
  rcases m
  · simp []
  · simp only [ite_true]
    have h1 : ‖cwZ n‖ = 1 := by
      rcases (sq_eq_one_iff (a := ‖cwZ n‖)).mp (cwZ_normSq n hn) with h' | h'
      · exact h'
      · exact absurd h' (by linarith [norm_nonneg (cwZ n)])
    rw [h1]

/-- For `n ≥ 1`, the explicit phase family has success probability `(n² + 9) / (9 * (n² + 1))`,
failure probability below `8 / 9`, and squared branch distance `4 / (n² + 1)`. The phase has
squared norm one. -/
theorem theorem13RefutedByPhaseFamily (n : ℕ) (hn : 1 ≤ n) :
    ‖cwZ n‖ ^ 2 = 1 ∧
      Fig3SuccessProb (cwBranchesPhase n) cwRotation cwRotation false (Ket (0 : Fin 1))
        = ((n : ℝ) ^ 2 + 9) / (9 * ((n : ℝ) ^ 2 + 1)) ∧
      1 - ((n : ℝ) ^ 2 + 9) / (9 * ((n : ℝ) ^ 2 + 1)) < 8 / 9 ∧
      ‖(1 : Matrix (Fin 1) (Fin 1) ℂ) - cwZ n • 1‖ ^ 2 = 4 / ((n : ℝ) ^ 2 + 1) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hne : ((n : ℝ) ^ 2 + 1) ≠ 0 := by positivity
  have hnormz : ‖((2 : ℂ) - cwZ n)‖ ^ 2 = ((n : ℝ) ^ 2 + 9) / ((n : ℝ) ^ 2 + 1) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      cwZ_re, cwZ_im]
    norm_num
    field_simp
    ring
  have hnorm1 : ‖((1 : ℂ) - cwZ n)‖ ^ 2 = 4 / ((n : ℝ) ^ 2 + 1) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      cwZ_re, cwZ_im]
    norm_num
    field_simp
    ring
  refine ⟨cwZ_normSq n hnpos, ?_, ?_, ?_⟩
  · rw [fig3SuccessProb_of_coeff (cwBranchesPhase n) cwRotation cwRotation
      (fun m => if m then (-1 : ℂ) else 2) false (1 / 3 : ℂ) cwRotation_coeff (Ket 0)]
    have hV : (∑ m : Bool, (if m then (-1 : ℂ) else 2) • cwBranchesPhase n m)
        = ((2 : ℂ) - cwZ n) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
      simp only [Fintype.sum_bool, Bool.false_eq_true, cwBranchesPhase, ite_true, ite_false,
        smul_smul]
      rw [← add_smul]
      congr 1
      ring
    rw [hV, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hket : (((2 : ℂ) - cwZ n) • (Ket (0 : Fin 1)))
        = fun _ => (2 : ℂ) - cwZ n := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      rw [hi]
      simp [Ket]
    have hnorm : ‖(1 / 3 : ℂ)‖ ^ 2 = 1 / 9 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      norm_num
    rw [hket, Fin.sum_univ_one, hnorm, hnormz]
    field_simp
  · have hle : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    rw [sub_lt_iff_lt_add]
    field_simp
    nlinarith [hsq]
  · have hM : ((1 : Matrix (Fin 1) (Fin 1) ℂ) - cwZ n • 1)
        = ((1 : ℂ) - cwZ n) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
      rw [sub_smul, one_smul]
    rw [hM, norm_smul, CStarRing.norm_one, mul_one, hnorm1]

end Qatlib.Concepts.CoherentSim.ResetDiscard
