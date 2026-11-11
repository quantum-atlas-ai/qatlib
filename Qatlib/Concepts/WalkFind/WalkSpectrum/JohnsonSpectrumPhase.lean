/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.WalkSpectrum.JohnsonFullSpectrumStat
import Qatlib.Concepts.WalkFind.WalkSpectrum.NormalSpectralPerturbationQuan
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Qatlib.Concepts.BlockEncoding.LinearCombination

/-!
# Paired eigenphases for the Johnson spectrum

`purePhase` parametrizes the complex unit circle. The functions `phaseAngle` and
`phaseEigenvalues` enumerate a distinguished phase zero followed by pairs of positive and
negative phases.

The module proves distinctness for strictly increasing angles in `(0, π)`, unit-modulus
identities, and the quadratic relation satisfied by each nontrivial eigenvalue. See
[Ambainis2007ElementDistinctness] for the mathematical background.

## Main statements

* `phaseEigenvalues_injective`: distinctness of the paired eigenvalues.
* `phaseEigenvalues_quadratic`: quadratic relation for nonzero indices.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false
open Matrix Polynomial
open scoped Classical BigOperators

namespace Qatlib.Concepts.WalkFind.WalkSpectrum
noncomputable section
/-- The complex phase `exp (a * I)` corresponding to a real angle `a`. -/
def purePhase (a : ℝ) : ℂ := Complex.exp ((a : ℂ)*Complex.I)
end
noncomputable section

/-- The imaginary part of `purePhase a` equals `sin a`. -/
theorem purePhase_im (a : ℝ) : (purePhase a).im = Real.sin a := by
  rw [purePhase, Complex.exp_ofReal_mul_I]
  simp [-Complex.ofReal_sin]
end
noncomputable section

/-- The product of the conjugate of `purePhase a` with `purePhase a` equals 1. -/
theorem purePhase_star_mul (a : ℝ) : star (purePhase a)*purePhase a = 1 := by
  have hc : star (purePhase a) = purePhase (-a) := by
    simp [purePhase, ← Complex.exp_conj]
  rw [hc]
  unfold purePhase
  rw [← Complex.exp_add]
  simp
end
noncomputable section

/-- Two angles in `(−π, π)` with equal complex phases are equal. -/
theorem purePhase_injective_between {a b : ℝ}
    (ha : -Real.pi < a ∧ a < Real.pi) (hb : -Real.pi < b ∧ b < Real.pi)
    (h : purePhase a = purePhase b) : a = b := by
  have heq := (Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := (a : ℂ)*Complex.I) (y := (b : ℂ)*Complex.I)
    (by simpa using! ha.1) (by simpa using! ha.2.le)
    (by simpa using! hb.1) (by simpa using! hb.2.le)) h
  have him := congrArg Complex.im heq
  simpa using! him
end
noncomputable section

/-- For `0 < a < π`, the square of `purePhase a` is not 1. -/
theorem purePhase_sq_ne_one {a : ℝ} (ha0 : 0 < a) (hapi : a < Real.pi) :
    (purePhase a)^2 ≠ 1 := by
  intro h
  have hs : 0 < (purePhase a).im := by
    rw [purePhase_im]; exact Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  have hroots : purePhase a = 1 ∨ purePhase a = -1 := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    simpa using! h
  rcases hroots with hroot | hroot <;> simp [hroot] at hs
end
noncomputable section

/-- The phase `purePhase a` satisfies the quadratic equation `z² - 2 * cos a * z + 1 = 0`. -/
theorem purePhase_quadratic (a : ℝ) :
    (purePhase a)^2-2*(Real.cos a : ℂ)*purePhase a+1 = 0 := by
  have hprod : purePhase (-a)*purePhase a = 1 := by
    unfold purePhase
    rw [← Complex.exp_add]
    simp
  have hsum : purePhase a+purePhase (-a) = 2*(Real.cos a : ℂ) := by
    unfold purePhase
    rw [Complex.exp_ofReal_mul_I a, Complex.exp_ofReal_mul_I (-a)]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    ring
  linear_combination (purePhase a)*hsum-hprod
end
noncomputable section
/-- The pair index `(i.val - 1) / 2` associated with a nonzero index in `Fin (2 * k + 1)`. -/
def phaseIndex {k : ℕ} (i : Fin (2*k+1)) (hi : i.val ≠ 0) : Fin k :=
  ⟨(i.val-1)/2, by omega⟩
end
noncomputable section
/-- The angle enumeration consisting of zero at index zero and alternating `θ j` and `-θ j` at
the remaining indices. -/
def phaseAngle {k : ℕ} (θ : Fin k → ℝ) (i : Fin (2*k+1)) : ℝ :=
  if hi : i.val = 0 then 0
  else if i.val%2 = 1 then θ (phaseIndex i hi) else -θ (phaseIndex i hi)
end
noncomputable section
/-- The complex phases obtained by applying `purePhase` to `phaseAngle θ`. -/
def phaseEigenvalues {k : ℕ} (θ : Fin k → ℝ) (i : Fin (2*k+1)) : ℂ :=
  purePhase (phaseAngle θ i)
end
noncomputable section

/-- If each `θ j` lies in `(0, π)`, then every enumerated phase angle lies in `(−π, π)`. -/
theorem phaseAngle_bounds {k : ℕ} (θ : Fin k → ℝ)
    (hθ : ∀ j, 0 < θ j ∧ θ j < Real.pi) (i : Fin (2*k+1)) :
    -Real.pi < phaseAngle θ i ∧ phaseAngle θ i < Real.pi := by
  unfold phaseAngle
  split_ifs with hi hip
  · constructor <;> linarith [Real.pi_pos]
  · constructor <;> linarith [(hθ (phaseIndex i hi)).1, (hθ (phaseIndex i hi)).2, Real.pi_pos]
  · constructor <;> linarith [(hθ (phaseIndex i hi)).1, (hθ (phaseIndex i hi)).2, Real.pi_pos]
end
noncomputable section

/-- Strictly increasing angles in `(0, π)` give an injective enumeration by zero and signed
angle pairs. -/
theorem phaseAngle_injective {k : ℕ} (θ : Fin k → ℝ)
    (hmono : StrictMono θ) (hθ : ∀ j, 0 < θ j ∧ θ j < Real.pi) :
    Function.Injective (phaseAngle θ) := by
  intro i j h
  by_cases hi : i.val = 0
  · by_cases hj : j.val = 0
    · exact Fin.ext (by omega)
    · have hpos := (hθ (phaseIndex j hj)).1
      simp [phaseAngle, hi, hj] at h
      split_ifs at h <;> linarith
  · by_cases hj : j.val = 0
    · have hpos := (hθ (phaseIndex i hi)).1
      simp [phaseAngle, hi, hj] at h
      split_ifs at h <;> linarith
    · have hposi := (hθ (phaseIndex i hi)).1
      have hposj := (hθ (phaseIndex j hj)).1
      by_cases hip : i.val%2 = 1 <;> by_cases hjp : j.val%2 = 1
      · simp [phaseAngle, hi, hj, hip, hjp] at h
        have hidx := congrArg Fin.val (hmono.injective h)
        change (i.val-1)/2 = (j.val-1)/2 at hidx
        exact Fin.ext (by omega)
      · simp [phaseAngle, hi, hj, hip, hjp] at h
        linarith
      · simp [phaseAngle, hi, hj, hip, hjp] at h
        linarith
      · simp [phaseAngle, hi, hj, hip, hjp] at h
        have hidx := congrArg Fin.val (hmono.injective h)
        change (i.val-1)/2 = (j.val-1)/2 at hidx
        have hiplt := Nat.mod_lt i.val (by decide : 0 < 2)
        have hjplt := Nat.mod_lt j.val (by decide : 0 < 2)
        exact Fin.ext (by omega)
end
noncomputable section

/-- Strictly increasing angles in `(0, π)` give distinct complex values in `phaseEigenvalues`. -/
theorem phaseEigenvalues_injective {k : ℕ} (θ : Fin k → ℝ)
    (hmono : StrictMono θ) (hθ : ∀ j, 0 < θ j ∧ θ j < Real.pi) :
    Function.Injective (phaseEigenvalues θ) := by
  intro i j h
  apply phaseAngle_injective θ hmono hθ
  exact purePhase_injective_between (phaseAngle_bounds θ hθ i) (phaseAngle_bounds θ hθ j) h
end
noncomputable section

/-- Each enumerated eigenvalue multiplied by its complex conjugate equals 1. -/
theorem phaseEigenvalues_star_mul {k : ℕ} (θ : Fin k → ℝ) (i : Fin (2*k+1)) :
    star (phaseEigenvalues θ i)*phaseEigenvalues θ i = 1 := purePhase_star_mul _
end
noncomputable section

/-- The enumerated eigenvalue at index zero is 1. -/
theorem phaseEigenvalues_zero {k : ℕ} (θ : Fin k → ℝ) :
    phaseEigenvalues θ ⟨0, by omega⟩ = 1 := by simp [phaseEigenvalues, phaseAngle, purePhase]
end
noncomputable section

/-- The eigenvalue at index `2 * j + 1` equals `exp (I * θ j)`. -/
theorem phaseEigenvalues_plus {k : ℕ} (θ : Fin k → ℝ) (j : Fin k) :
    phaseEigenvalues θ ⟨2*j.val+1, by omega⟩ = Complex.exp (Complex.I*(θ j : ℂ)) := by
  have hz : 2*j.val+1 ≠ 0 := by omega
  have hp : (2*j.val+1)%2 = 1 := by omega
  have hj : phaseIndex (⟨2*j.val+1, by omega⟩ : Fin (2*k+1)) hz = j := by
    apply Fin.ext
    change (2*j.val+1-1)/2 = j.val
    omega
  simp only [phaseEigenvalues, phaseAngle]
  rw [dif_neg hz, if_pos hp, hj]
  exact congrArg Complex.exp (mul_comm _ _)
end
noncomputable section

/-- The eigenvalue at index `2 * j + 2` equals `exp (-I * θ j)`. -/
theorem phaseEigenvalues_minus {k : ℕ} (θ : Fin k → ℝ) (j : Fin k) :
    phaseEigenvalues θ ⟨2*j.val+2, by omega⟩ = Complex.exp (-Complex.I*(θ j : ℂ)) := by
  have hz : 2*j.val+2 ≠ 0 := by omega
  have hp : ¬(2*j.val+2)%2 = 1 := by omega
  have hj : phaseIndex (⟨2*j.val+2, by omega⟩ : Fin (2*k+1)) hz = j := by
    apply Fin.ext
    change (2*j.val+2-1)/2 = j.val
    omega
  simp only [phaseEigenvalues, phaseAngle]
  rw [dif_neg hz, if_neg hp, hj]
  unfold purePhase
  congr 1
  simp only [Complex.ofReal_neg, neg_mul]
  rw [mul_comm]
end
noncomputable section

/-- For `0 < a < π`, the square of `purePhase (-a)` is not 1. -/
theorem purePhase_neg_sq_ne_one {a : ℝ} (ha0 : 0 < a) (hapi : a < Real.pi) :
    (purePhase (-a))^2 ≠ 1 := by
  intro h
  have hc : star (purePhase (-a)) = purePhase a := by simp [purePhase, ← Complex.exp_conj]
  have hs : (purePhase a)^2 = 1 := by
    simpa only [star_pow, hc, star_one] using! congrArg star h
  exact purePhase_sq_ne_one ha0 hapi hs
end
noncomputable section

/-- For angles in `(0, π)`, every eigenvalue with nonzero index has square different from 1. -/
theorem phaseEigenvalues_sq_ne_one {k : ℕ} (θ : Fin k → ℝ)
    (hθ : ∀ j, 0 < θ j ∧ θ j < Real.pi) (i : Fin (2*k+1)) (hi : i.val ≠ 0) :
    (phaseEigenvalues θ i)^2 ≠ 1 := by
  unfold phaseEigenvalues phaseAngle
  rw [dif_neg hi]
  split_ifs
  · exact purePhase_sq_ne_one (hθ (phaseIndex i hi)).1 (hθ (phaseIndex i hi)).2
  · exact purePhase_neg_sq_ne_one (hθ (phaseIndex i hi)).1 (hθ (phaseIndex i hi)).2
end
noncomputable section

/-- Every eigenvalue with nonzero index satisfies `z² - 2 * cos (θ j) * z + 1 = 0` for its
associated pair index `j`. -/
theorem phaseEigenvalues_quadratic {k : ℕ} (θ : Fin k → ℝ)
    (i : Fin (2*k+1)) (hi : i.val ≠ 0) :
    (phaseEigenvalues θ i)^2-2*(Real.cos (θ (phaseIndex i hi)) : ℂ)*phaseEigenvalues θ i+1 = 0 := by
  unfold phaseEigenvalues phaseAngle
  rw [dif_neg hi]
  split_ifs
  · exact purePhase_quadratic _
  · simpa only [Real.cos_neg] using! purePhase_quadratic (-θ (phaseIndex i hi))
end
noncomputable section

/-- Every index is either zero or belongs to the positive or negative position of a phase pair. -/
theorem phaseIndex_cover {k : ℕ} (i : Fin (2*k+1)) :
    i = ⟨0, by omega⟩ ∨ ∃ j : Fin k,
      i = ⟨2*j.val+1, by omega⟩ ∨ i = ⟨2*j.val+2, by omega⟩ := by
  by_cases hi : i.val = 0
  · exact Or.inl (Fin.ext hi)
  · refine Or.inr ⟨phaseIndex i hi, ?_⟩
    by_cases hp : i.val%2 = 1
    · left
      apply Fin.ext
      change i.val = 2*((i.val-1)/2)+1
      omega
    · right
      apply Fin.ext
      change i.val = 2*((i.val-1)/2)+2
      have := Nat.mod_lt i.val (by decide : 0 < 2)
      omega
end
end Qatlib.Concepts.WalkFind.WalkSpectrum
