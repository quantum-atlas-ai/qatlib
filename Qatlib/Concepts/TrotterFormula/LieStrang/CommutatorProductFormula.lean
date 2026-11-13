/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.LieStrang.HermitianEvolutionStability

/-!
# Commutator bounds for Lie and Strang product formulas

This module defines two-term Lie and Strang steps and labelled finite-family words, then proves
their operator-norm error bounds using single and nested commutators. The estimates follow the
commutator-scaling viewpoint of [ChildsEtAl2021Trotter].

`pfInterpret` applies word entries by successive left multiplication. The module also records
unitarity, exact word lengths, arbitrary label prices, and error accumulation over positive
segment counts.

## Main statements

* `product_formula_lie_two_term`: the quadratic two-term Lie error bound.
* `product_formula_strang_nested_commutator`: the cubic Strang bound with constants `1/12` and
  `1/24`.
* `product_formula_actual_word_and_tariffs`: unitarity, word length, price, and repetition
  identities.
* `product_formula_finite_family_segmented`: the finite-family segmented commutator bound.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
* [Trotter, 1959][Trotter1959]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.TrotterFormula.LieStrang
open Matrix Set
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The matrix commutator `A * B - B * A`. -/
noncomputable def pfComm {I : Type} [Fintype I] (A B : Matrix I I ℂ) : Matrix I I ℂ := A*B-B*A

/-- The two-term Lie step consisting of evolution under `A` followed by evolution under `B`. -/
noncomputable def pfLie {D : ℕ} (A B : Operator D) (t : ℝ) : Operator D :=
  HamiltonianEvolution B t * HamiltonianEvolution A t

/-- The symmetric Strang step with half-time `A` evolutions surrounding a full-time `B`
evolution. -/
noncomputable def pfStrang {D : ℕ} (A B : Operator D) (t : ℝ) : Operator D :=
  HamiltonianEvolution A (t/2) * HamiltonianEvolution B t * HamiltonianEvolution A (t/2)

/-- The labelled finite-family word formed by repeating `r` ordered family segments with time
step `t / r`. -/
noncomputable def pfFamilyWord {D m : ℕ} (H : Fin m  →  Operator D) (t : ℝ) (r : ℕ) : List (Operator D × ℕ) :=
  (List.replicate r (List.ofFn (fun j : Fin m => (HamiltonianEvolution (H j) (t/r),j.val)))).flatten

/-- The operator obtained from a labelled word by successive left multiplication, starting from
identity. -/
noncomputable def pfInterpret {D : ℕ} (xs : List (Operator D × ℕ)) : Operator D :=
  xs.foldl (fun U x => x.1*U) 1

/-- The operator obtained by interpreting the labelled segmented family word. -/
noncomputable def pfFamily {D m : ℕ} (H : Fin m  →  Operator D) (t : ℝ) (r : ℕ) : Operator D :=
  pfInterpret (pfFamilyWord H t r)

/-- The sum of pairwise commutator norms over family indices `j < k`. -/
noncomputable def pfCommutatorSum {D m : ℕ} (H : Fin m  →  Operator D) : ℝ :=
  ∑ j : Fin m, ∑ k : Fin m, if j  <  k then ‖pfComm (H j) (H k)‖ else 0

/-- The real-parameter matrix exponential `exp (s • X)`. -/
private noncomputable def pfExp {D : ℕ} (X : Operator D) (s : ℝ) : Operator D :=
  NormedSpace.exp (s • X)

/-- The exponential path for `(-i t) • H` at parameter `s` equals Hamiltonian evolution under
`H` at time `s * t`. -/
private theorem pfExp_line {D : ℕ} (H : Operator D) (t s : ℝ) :
    pfExp ((-Complex.I * (t : ℂ)) • H) s = HamiltonianEvolution H (s * t) := by
  unfold pfExp HamiltonianEvolution
  congr 1
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]
  ring

/-- The exponential path `pfExp X` has derivative `pfExp X s * X` at `s`. -/
private theorem pfExp_deriv {D : ℕ} (X : Operator D) (s : ℝ) :
    HasDerivAt (pfExp X) (pfExp X s * X) s := hasDerivAt_exp_smul_const X s

/-- The reversed exponential path has derivative `-(X * pfExp X (-s))` at `s`. -/
private theorem pfExp_neg_deriv {D : ℕ} (X : Operator D) (s : ℝ) :
    HasDerivAt (fun u => pfExp X (-u)) (-(X * pfExp X (-s))) s := by
  convert! (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X (-s)).scomp s (hasDerivAt_id s).neg using 1
  simp [pfExp]

/-- The derivative of exponential conjugation of `Y` is the exponential conjugation of `pfComm X
Y`. -/
private theorem pfConjugate_deriv {D : ℕ} (X Y : Operator D) (s : ℝ) :
    HasDerivAt (fun u => pfExp X u * Y * pfExp X (-u))
      (pfExp X s * pfComm X Y * pfExp X (-s)) s := by
  convert! ((pfExp_deriv X s).mul_const Y).mul (pfExp_neg_deriv X s) using 1
  simp only [pfComm]
  noncomm_ring

/-- If the exponential path is contractive for all real parameters, its conjugation has
first-order and second-order remainder bounds controlled by the first and second commutators
on `[0, 1]`. -/
private theorem pf_conjugate_bounds {D : ℕ} (X Y : Operator D)
    (hX : ∀ s : ℝ, ‖pfExp X s‖ ≤ 1) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      ‖pfExp X s * Y * pfExp X (-s) - Y‖ ≤ s * ‖pfComm X Y‖ ∧
      ‖pfExp X s * Y * pfExp X (-s) - Y - s • pfComm X Y‖ ≤
        s ^ 2 / 2 * ‖pfComm X (pfComm X Y)‖ := by
  have hlin (Z : Operator D) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖pfExp X s * Z * pfExp X (-s) - Z‖ ≤ s * ‖pfComm X Z‖ := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun u (_ : u ∈ Icc (0 : ℝ) 1) => (pfConjugate_deriv X Z u).hasDerivWithinAt)
      (fun u (_ : u ∈ Ico (0 : ℝ) 1) => l2_norm_sandwich_le _ _ _ (hX u) (hX (-u))) s hs
    simpa [pfExp, mul_comm] using! h
  have hder (s : ℝ) : HasDerivAt
      (fun u => pfExp X u * Y * pfExp X (-u) - Y - u • pfComm X Y)
      (pfExp X s * pfComm X Y * pfExp X (-s) - pfComm X Y) s := by
    simpa only [id_eq, one_smul] using!
      ((pfConjugate_deriv X Y s).sub_const Y).sub ((hasDerivAt_id s).smul_const (pfComm X Y))
  intro s hs
  refine ⟨hlin Y s hs, ?_⟩
  have hbound : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖pfExp X s * Y * pfExp X (-s) - Y - s • pfComm X Y‖ ≤
        s ^ 2 / 2 * ‖pfComm X (pfComm X Y)‖ := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun u => pfExp X u * Y * pfExp X (-u) - Y - u • pfComm X Y)
      (f' := fun u => pfExp X u * pfComm X Y * pfExp X (-u) - pfComm X Y)
      (B := fun u => u ^ 2 / 2 * ‖pfComm X (pfComm X Y)‖)
      (B' := fun u => u * ‖pfComm X (pfComm X Y)‖)
      (fun u _ => (hder u).continuousAt.continuousWithinAt)
      (fun u _ => (hder u).hasDerivWithinAt) (by simp [pfExp]) ?_ ?_
    · intro u
      convert! ((hasDerivAt_id u).pow 2).mul_const (‖pfComm X (pfComm X Y)‖ / 2) using 1
      · ext x; dsimp; ring
      · (try dsimp); ring
    · intro u hu
      exact hlin (pfComm X Y) u ⟨hu.1, hu.2.le⟩
  exact hbound s hs

/-- Conjugating `B` by the evolution of a Hermitian `A` changes it by operator norm at most `|t|
* ‖pfComm A B‖`. -/
theorem product_formula_conjugation_commutator (D : ℕ) (A B : Operator D) (t : ℝ)
    (hA : A.IsHermitian) :
    ‖HamiltonianEvolution A t * B * (HamiltonianEvolution A t)ᴴ - B‖ ≤ |t| * ‖pfComm A B‖ := by
  let X : Operator D := (-Complex.I * (t : ℂ)) • A
  have hn : ∀ s : ℝ, ‖pfExp X s‖ ≤ 1 := by
    intro s
    rw [pfExp_line]
    exact l2_norm_unitary_le_one (hamiltonianEvolution_unitary hA _)
  have h := (pf_conjugate_bounds X B hn 1 ⟨zero_le_one, le_rfl⟩).1
  have hc : pfComm X B = (-Complex.I * (t : ℂ)) • pfComm A B := by
    simp only [pfComm, X, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  have hi : pfExp X (-1) = (HamiltonianEvolution A t)ᴴ := by
    rw [pfExp_line]
    simp [HamiltonianEvolution, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hA.eq, RCLike.star_def]
  rw [hi, pfExp_line, one_mul, hc] at h
  simpa [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs] using! h

/-- The exponential path `pfExp X` has derivative `X * pfExp X s` at `s`. -/
private theorem pfExp_left_deriv {D : ℕ} (X : Operator D) (s : ℝ) :
    HasDerivAt (pfExp X) (X * pfExp X s) s := hasDerivAt_exp_smul_const' X s

/-- The path `pfExp X (1 - s)` has derivative `-(pfExp X (1 - s) * X)`. -/
private theorem pfExp_back_deriv {D : ℕ} (X : Operator D) (s : ℝ) :
    HasDerivAt (fun u => pfExp X (1-u)) (-(pfExp X (1-s) * X)) s := by
  have hi : HasDerivAt (fun u : ℝ => 1-u) (-1) s := by
    simpa using! (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)
  convert! (pfExp_deriv X (1-s)).scomp s hi using 1
  simp

/-- The exponential at parameter `-s` is a left inverse of the exponential at parameter `s`. -/
private theorem pfExp_inverse {D : ℕ} (X : Operator D) (s : ℝ) :
    pfExp X (-s) * pfExp X s = 1 := by
  dsimp [pfExp]
  rw [neg_smul]
  rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl (s • X)).neg_left),
    neg_add_cancel, NormedSpace.exp_zero]

/-- Scaling both entries of a commutator scales the commutator by the product of the scalars. -/
private theorem pfComm_scaled {D : ℕ} (A B : Operator D) (a b : ℂ) :
    pfComm (a • A) (b • B) = (a*b) • pfComm A B := by
  simp only [pfComm, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul]
  rw [mul_comm b a]

/-- If the exponential paths of `X`, `Y`, and `X + Y` are contractive for all real parameters,
the unit-time Lie error is at most half the commutator norm. -/
private theorem pf_lie_generators {D : ℕ} (X Y : Operator D)
    (hX : ∀ s : ℝ, ‖pfExp X s‖ ≤ 1) (hY : ∀ s : ℝ, ‖pfExp Y s‖ ≤ 1)
    (hZ : ∀ s : ℝ, ‖pfExp (X+Y) s‖ ≤ 1) :
    ‖pfExp Y 1 * pfExp X 1 - pfExp (X+Y) 1‖ ≤ ‖pfComm Y X‖ / 2 := by
  let f : ℝ → Operator D := fun s => pfExp (X+Y) (1-s) * pfExp Y s * pfExp X s
  let d : ℝ → Operator D := fun s =>
    pfExp (X+Y) (1-s) * (pfExp Y s * X - X * pfExp Y s) * pfExp X s
  have hd (s : ℝ) : HasDerivAt f (d s) s := by
    convert! ((pfExp_back_deriv (X+Y) s).mul (pfExp_left_deriv Y s)).mul
      (pfExp_left_deriv X s) using 1
    dsimp [f, d]
    noncomm_ring
  have hdn (s : ℝ) (hs : s ∈ Ico (0 : ℝ) 1) : ‖d s‖ ≤ s * ‖pfComm Y X‖ := by
    have hc : pfExp Y s * X - X * pfExp Y s =
        (pfExp Y s * X * pfExp Y (-s) - X) * pfExp Y s := by
      rw [sub_mul, mul_assoc (pfExp Y s * X), pfExp_inverse, mul_one]
    dsimp [d]
    calc
      _ ≤ ‖pfExp Y s * X - X * pfExp Y s‖ := l2_norm_sandwich_le _ _ _ (hZ _) (hX _)
      _ ≤ ‖pfExp Y s * X * pfExp Y (-s) - X‖ := by
        rw [hc]
        exact (norm_mul_le _ _).trans
            ((mul_le_mul_of_nonneg_left (hY s) (norm_nonneg _)).trans_eq (mul_one _))
      _ ≤ _ := (pf_conjugate_bounds Y X hY s ⟨hs.1, hs.2.le⟩).1
  have hbound : ∀ s ∈ Icc (0 : ℝ) 1, ‖f s - f 0‖ ≤ s^2 * ‖pfComm Y X‖ / 2 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s => f s - f 0) (f' := d)
      (B := fun s => s^2 * ‖pfComm Y X‖ / 2) (B' := fun s => s * ‖pfComm Y X‖)
      (fun s _ => ((hd s).sub_const _).continuousAt.continuousWithinAt)
      (fun s _ => ((hd s).sub_const _).hasDerivWithinAt) (by simp) ?_ hdn
    intro s
    convert! ((hasDerivAt_id s).pow 2).mul_const (‖pfComm Y X‖ / 2) using 1
    · ext u; dsimp; ring
    · (try dsimp); ring
  simpa [f, pfExp] using! hbound 1 ⟨zero_le_one, le_rfl⟩

/-- For Hermitian `A` and `B`, the two-term Lie error is at most `t² / 2 * ‖pfComm B A‖`, the
two-term instance of [Childs et al., Proposition 15][ChildsEtAl2021Trotter]. -/
theorem product_formula_lie_two_term (D : ℕ) (A B : Operator D) (t : ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖pfLie A B t - HamiltonianEvolution (A+B) t‖ ≤ t^2 / 2 * ‖pfComm B A‖ := by
  let c : ℂ := -Complex.I * (t : ℂ)
  let X : Operator D := c • A
  let Y : Operator D := c • B
  have hn (H : Operator D) (hH : H.IsHermitian) (s : ℝ) : ‖pfExp (c • H) s‖ ≤ 1 := by
    rw [pfExp_line]
    exact l2_norm_unitary_le_one (hamiltonianEvolution_unitary hH _)
  have hz : X+Y = c • (A+B) := (smul_add _ _ _).symm
  have h := pf_lie_generators X Y (hn A hA) (hn B hB) (by rw [hz]; exact hn _ (hA.add hB))
  have hc : ‖pfComm Y X‖ = t^2 * ‖pfComm B A‖ := by
    rw [pfComm_scaled, norm_smul, norm_mul]
    simp [c, Complex.norm_real, Real.norm_eq_abs, ← sq, sq_abs]
  rw [hz, pfExp_line, pfExp_line, pfExp_line, one_mul, hc] at h
  simpa only [pfLie, mul_div_assoc, div_mul_eq_mul_div] using! h

/-- Under contractivity of the three exponential paths, the symmetric step error is bounded by
one sixth of the sum of the stated two nested-commutator norms. -/
private theorem pf_strang_generators {D : ℕ} (T Y : Operator D)
    (hT : ∀ s : ℝ, ‖pfExp T s‖ ≤ 1) (hY : ∀ s : ℝ, ‖pfExp Y s‖ ≤ 1)
    (hZ : ∀ s : ℝ, ‖pfExp (T+T+Y) s‖ ≤ 1) :
    ‖pfExp T 1 * pfExp Y 1 * pfExp T 1 - pfExp (T+T+Y) 1‖ ≤
      (‖pfComm (-T) (pfComm (-T) Y)‖ + ‖pfComm Y (pfComm Y T)‖) / 6 := by
  let C := ‖pfComm (-T) (pfComm (-T) Y)‖ + ‖pfComm Y (pfComm Y T)‖
  let R : ℝ → Operator D := fun s =>
    Y - pfExp T (-s) * Y * pfExp T s + pfExp Y s * T * pfExp Y (-s) - T
  let f : ℝ → Operator D := fun s =>
    pfExp (T+T+Y) (1-s) * (pfExp T s * pfExp Y s * pfExp T s)
  let d : ℝ → Operator D := fun s =>
    pfExp (T+T+Y) (1-s) * (pfExp T s * R s * pfExp Y s * pfExp T s)
  have he (s : ℝ) : pfExp (-T) s = pfExp T (-s) := by simp [pfExp, smul_neg, neg_smul]
  have hback (s : ℝ) : pfExp T s * pfExp T (-s) = 1 := by
    simpa only [neg_neg] using! pfExp_inverse T (-s)
  have hcomm (s : ℝ) : T * pfExp T s = pfExp T s * T :=
    ((Commute.refl T).smul_right s).exp_right.eq
  have hcancel (s : ℝ) (V : Operator D) : pfExp T s * (pfExp T (-s) * V) = V := by
    rw [← mul_assoc, hback, one_mul]
  have hmove (s : ℝ) (V : Operator D) : pfExp T s * (T * V) = T * (pfExp T s * V) := by
    rw [← mul_assoc, ← hcomm, mul_assoc]
  have hd (s : ℝ) : HasDerivAt f (d s) s := by
    convert! (pfExp_back_deriv (T+T+Y) s).mul
      (((pfExp_left_deriv T s).mul (pfExp_left_deriv Y s)).mul (pfExp_left_deriv T s)) using 1
    dsimp [f, d, R]
    simp only [mul_sub, mul_add, sub_mul, add_mul]
    simp only [mul_assoc, pfExp_inverse, mul_one, hcancel, hmove]
    noncomm_ring
  have hR (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ‖R s‖ ≤ s^2 / 2 * C := by
    have hneg : ∀ s : ℝ, ‖pfExp (-T) s‖ ≤ 1 := by intro u; rw [he]; exact hT _
    have h1 := (pf_conjugate_bounds (-T) Y hneg s hs).2
    have h2 := (pf_conjugate_bounds Y T hY s hs).2
    have hc : pfComm (-T) Y = pfComm Y T := by dsimp [pfComm]; noncomm_ring
    have hr : R s =
        -(pfExp (-T) s * Y * pfExp (-T) (-s) - Y - s • pfComm (-T) Y) +
          (pfExp Y s * T * pfExp Y (-s) - T - s • pfComm Y T) := by
      rw [he, he, neg_neg, hc]
      dsimp [R]
      abel
    rw [hr]
    calc
      _ ≤ ‖pfExp (-T) s * Y * pfExp (-T) (-s) - Y - s • pfComm (-T) Y‖ +
          ‖pfExp Y s * T * pfExp Y (-s) - T - s • pfComm Y T‖ := by
        simpa only [norm_neg] using! norm_add_le
          (-(pfExp (-T) s * Y * pfExp (-T) (-s) - Y - s • pfComm (-T) Y))
          (pfExp Y s * T * pfExp Y (-s) - T - s • pfComm Y T)
      _ ≤ _ := (add_le_add h1 h2).trans_eq (by dsimp [C]; ring)
  have hdn (s : ℝ) (hs : s ∈ Ico (0 : ℝ) 1) : ‖d s‖ ≤ s^2 * C / 2 := by
    dsimp [d]
    calc
      _ ≤ ‖pfExp T s * R s * pfExp Y s * pfExp T s‖ := by
        exact (norm_mul_le _ _).trans
            ((mul_le_mul_of_nonneg_right (hZ _) (norm_nonneg _)).trans_eq (one_mul _))
      _ ≤ ‖pfExp T s * R s * pfExp Y s‖ :=
        (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left (hT _) (norm_nonneg _)).trans_eq (mul_one _))
      _ ≤ ‖R s‖ := l2_norm_sandwich_le _ _ _ (hT _) (hY _)
      _ ≤ _ := (hR s ⟨hs.1, hs.2.le⟩).trans_eq (by ring)
  have hbound : ∀ s ∈ Icc (0 : ℝ) 1, ‖f s - f 0‖ ≤ s^3 * C / 6 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s => f s - f 0) (f' := d)
      (B := fun s => s^3 * C / 6) (B' := fun s => s^2 * C / 2)
      (fun s _ => ((hd s).sub_const _).continuousAt.continuousWithinAt)
      (fun s _ => ((hd s).sub_const _).hasDerivWithinAt) (by simp) ?_ hdn
    intro s
    convert! ((hasDerivAt_id s).pow 3).mul_const (C / 6) using 1
    · ext u; dsimp; ring
    · (try dsimp); ring
  simpa [f, pfExp, C] using! hbound 1 ⟨zero_le_one, le_rfl⟩

/-- For Hermitian generators, the Strang error is bounded by `|t|³` times the two
nested-commutator norms with coefficients `1/12` and `1/24`, as in [Childs et al.,
Proposition 16][ChildsEtAl2021Trotter]. -/
theorem product_formula_strang_nested_commutator (D : ℕ) (A B : Operator D) (t : ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖pfStrang A B t - HamiltonianEvolution (A+B) t‖ ≤
      |t|^3 / 12 * ‖pfComm B (pfComm B A)‖ + |t|^3 / 24 * ‖pfComm A (pfComm A B)‖ := by
  let c : ℂ := -Complex.I * (t : ℂ)
  let a : ℂ := c / 2
  let T : Operator D := a • A
  let Y : Operator D := c • B
  have hn (H : Operator D) (hH : H.IsHermitian) (u s : ℝ) :
      ‖pfExp ((-Complex.I * (u : ℂ)) • H) s‖ ≤ 1 := by
    rw [pfExp_line]
    exact l2_norm_unitary_le_one (hamiltonianEvolution_unitary hH _)
  have ha : a = -Complex.I * ((t/2 : ℝ) : ℂ) := by dsimp [a, c]; push_cast; ring
  have hc2 : a+a = c := by dsimp [a]; ring
  have hz : T+T+Y = c • (A+B) := by
    simp only [T, Y, ← add_smul, hc2, smul_add]
  have h := pf_strang_generators T Y (by rw [show T = (-Complex.I * ((t/2 : ℝ) : ℂ)) • A from by rw [← ha]]; exact hn A hA _)
    (hn B hB t) (by rw [hz]; exact hn _ (hA.add hB) t)
  have hcn : ‖c‖ = |t| := by simp [c, Complex.norm_real, Real.norm_eq_abs]
  have han : ‖a‖ = |t| / 2 := by rw [show a = c / 2 from rfl, norm_div, hcn]; norm_num
  have hn1 : ‖pfComm (-T) (pfComm (-T) Y)‖ = |t|^3 / 4 * ‖pfComm A (pfComm A B)‖ := by
    rw [show -T = (-a) • A from (neg_smul a A).symm]
    change ‖pfComm ((-a) • A) (pfComm ((-a) • A) (c • B))‖ = _
    rw [pfComm_scaled, pfComm_scaled, norm_smul, norm_mul, norm_mul]
    simp only [norm_neg, han, hcn]
    ring
  have hn2 : ‖pfComm Y (pfComm Y T)‖ = |t|^3 / 2 * ‖pfComm B (pfComm B A)‖ := by
    rw [pfComm_scaled, pfComm_scaled, norm_smul]
    simp only [norm_mul, hcn, han]
    ring
  have ht1 : pfExp T 1 = HamiltonianEvolution A (t/2) := by
    change pfExp (a • A) 1 = _
    rw [ha, pfExp_line, one_mul]
  have hy1 : pfExp Y 1 = HamiltonianEvolution B t := by
    change pfExp ((-Complex.I * (t : ℂ)) • B) 1 = _
    rw [pfExp_line, one_mul]
  have hz1 : pfExp (T+T+Y) 1 = HamiltonianEvolution (A+B) t := by
    rw [hz]
    change pfExp ((-Complex.I * (t : ℂ)) • (A+B)) 1 = _
    rw [pfExp_line, one_mul]
  rw [hn1, hn2, ht1, hy1, hz1] at h
  exact h.trans_eq (by ring)

/-- Interpreting a word from accumulator `U` equals its interpretation from identity multiplied
on the right by `U`. -/
theorem pfInterpret_start {D : ℕ} (xs : List (Operator D × ℕ)) (U : Operator D) :
    xs.foldl (fun V x => x.1 * V) U = pfInterpret xs * U := by
  induction xs generalizing U with
  | nil => simp [pfInterpret]
  | cons x xs ih =>
    simp only [List.foldl_cons, pfInterpret, mul_one]
    rw [ih (x.1 * U), ih x.1]
    simp [mul_assoc]

/-- Interpreting `xs ++ ys` gives `pfInterpret ys * pfInterpret xs`. -/
theorem pfInterpret_append {D : ℕ} (xs ys : List (Operator D × ℕ)) :
    pfInterpret (xs ++ ys) = pfInterpret ys * pfInterpret xs := by
  exact (List.foldl_append ..).trans (pfInterpret_start ys _)

/-- Interpreting `q` repetitions of a word gives the `q`th power of its interpretation. -/
theorem pfInterpret_repeat {D : ℕ} (xs : List (Operator D × ℕ)) (q : ℕ) :
    pfInterpret ((List.replicate q xs).flatten) = (pfInterpret xs)^q := by
  induction q with
  | zero => simp [pfInterpret]
  | succ q ih =>
    rw [List.replicate_succ, List.flatten_cons, pfInterpret_append, ih, pow_succ]

/-- A labelled word of unitary operators has unitary interpretation. -/
private theorem pfInterpret_unitary {D : ℕ} (xs : List (Operator D × ℕ))
    (h : ∀ x ∈ xs, x.1 ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    pfInterpret xs ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  induction xs with
  | nil => exact (Matrix.unitaryGroup _ _).one_mem
  | cons x xs ih =>
    change xs.foldl (fun V y => y.1 * V) (x.1 * 1) ∈ _
    rw [pfInterpret_start, mul_one]
    exact (Matrix.unitaryGroup _ _).mul_mem (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))
      (h x List.mem_cons_self)

/-- For Hermitian family terms, the segmented word is unitary, has length `m * r` and price `r`
times the family price sum, and repeated words interpret as powers. -/
theorem product_formula_actual_word_and_tariffs
    (D m r : ℕ) (H : Fin m → Operator D) (t : ℝ) (cost : ℕ → ℕ)
    (hH : ∀ j, (H j).IsHermitian) :
    pfFamily H t r ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
    (pfFamilyWord H t r).length = m*r ∧
    ((pfFamilyWord H t r).map (fun x => cost x.2)).sum = r * ∑ j : Fin m, cost j.val ∧
    ∀ q : ℕ, pfInterpret ((List.replicate q (pfFamilyWord H t r)).flatten) = (pfFamily H t r)^q := by
  refine ⟨pfInterpret_unitary _ ?_, ?_, ?_, pfInterpret_repeat _⟩
  · intro x hx
    obtain ⟨ys, hys, hx⟩ := List.mem_flatten.mp hx
    have hy : ys = List.ofFn (fun j : Fin m => (HamiltonianEvolution (H j) (t/r), j.val)) :=
      List.eq_of_mem_replicate hys
    rw [hy] at hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact hamiltonianEvolution_unitary (hH j) _
  · simp [pfFamilyWord, List.length_flatten, List.map_replicate, Nat.mul_comm]
  · simp [pfFamilyWord, List.map_flatten, List.map_replicate, List.map_ofFn,
      List.sum_flatten, List.sum_ofFn]

/-- The single finite-family segment obtained by left-multiplying the ordered Hamiltonian
evolutions. -/
private noncomputable def pfSegment {D m : ℕ} (H : Fin m → Operator D) (t : ℝ) : Operator D :=
  (List.ofFn (fun j => HamiltonianEvolution (H j) t)).foldl (fun U V => V*U) 1

/-- Word interpretation depends only on the operator entries and equals their successive
left-multiplication fold. -/
private theorem pfInterpret_first {D : ℕ} (xs : List (Operator D × ℕ)) :
    pfInterpret xs = (xs.map Prod.fst).foldl (fun U V => V*U) 1 := by
  unfold pfInterpret
  exact (List.foldl_map (f := Prod.fst) (g := fun U V => V*U)).symm

/-- A segment for a nonempty family is the tail-family segment multiplied on the right by the
first evolution. -/
private theorem pfSegment_succ {D m : ℕ} (H : Fin (m+1) → Operator D) (t : ℝ) :
    pfSegment H t = pfSegment (fun j : Fin m => H j.succ) t * HamiltonianEvolution (H 0) t := by
  have he : pfSegment H t = pfInterpret (List.ofFn (fun j => (HamiltonianEvolution (H j) t, j.val))) := by
    rw [pfInterpret_first, List.map_ofFn]
    rfl
  rw [he, List.ofFn_succ]
  change (List.ofFn (fun j : Fin m => (HamiltonianEvolution (H j.succ) t, j.succ.val))).foldl
    (fun U x => x.1*U) (HamiltonianEvolution (H 0) t * 1) = _
  rw [pfInterpret_start, mul_one, pfInterpret_first, List.map_ofFn]
  rfl

/-- A single family segment is unitary when every family term is Hermitian. -/
private theorem pfSegment_unitary {D m : ℕ} (H : Fin m → Operator D) (t : ℝ)
    (hH : ∀ j, (H j).IsHermitian) : pfSegment H t ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  rw [show pfSegment H t = pfInterpret (List.ofFn (fun j => (HamiltonianEvolution (H j) t, j.val))) from by
    rw [pfInterpret_first, List.map_ofFn]; rfl]
  apply pfInterpret_unitary
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  exact hamiltonianEvolution_unitary (hH j) _

/-- The family commutator sum splits into pairs involving the first term and the commutator sum
of the tail family. -/
private theorem pfCommutatorSum_succ {D m : ℕ} (H : Fin (m+1) → Operator D) :
    pfCommutatorSum H = (∑ j : Fin m, ‖pfComm (H 0) (H j.succ)‖) +
      pfCommutatorSum (fun j : Fin m => H j.succ) := by
  simp [pfCommutatorSum, Fin.sum_univ_succ]

/-- The norm of the commutator of a family sum with `A` is at most the sum of the norms of the
commutators of `A` with each family term. -/
private theorem pfComm_sum_bound {D m : ℕ} (H : Fin m → Operator D) (A : Operator D) :
    ‖pfComm (∑ j, H j) A‖ ≤ ∑ j, ‖pfComm A (H j)‖ := by
  have he : pfComm (∑ j, H j) A = -(∑ j, pfComm A (H j)) := by
    simp only [pfComm, Matrix.sum_mul, Matrix.mul_sum, Finset.sum_sub_distrib, neg_sub]
  rw [he, norm_neg]
  exact norm_sum_le _ _

/-- For Hermitian family terms, the one-segment error is at most `t² / 2` times `pfCommutatorSum
H`. -/
private theorem pfSegment_error (D m : ℕ) (H : Fin m → Operator D) (t : ℝ)
    (hH : ∀ j, (H j).IsHermitian) :
    ‖pfSegment H t - HamiltonianEvolution (∑ j, H j) t‖ ≤ t^2 / 2 * pfCommutatorSum H := by
  induction m with
  | zero => simp [pfSegment, HamiltonianEvolution, pfCommutatorSum]
  | succ m ih =>
    let tail : Fin m → Operator D := fun j => H j.succ
    let B : Operator D := ∑ j, tail j
    have ht : B.IsHermitian := by
      change (∑ j : Fin m, H j.succ)ᴴ = _
      rw [Matrix.conjTranspose_sum]
      exact Finset.sum_congr rfl fun j _ => (hH j.succ).eq
    have hi := ih tail (fun j => hH j.succ)
    have hLie := product_formula_lie_two_term D (H 0) B t (hH 0) ht
    have hC := pfComm_sum_bound tail (H 0)
    have he : pfSegment H t - HamiltonianEvolution (∑ j, H j) t =
      (pfSegment tail t - HamiltonianEvolution B t) * HamiltonianEvolution (H 0) t +
        (pfLie (H 0) B t - HamiltonianEvolution (H 0+B) t) := by
      rw [pfSegment_succ, Fin.sum_univ_succ]
      dsimp [pfLie, B, tail]
      noncomm_ring
    rw [he]
    calc
      _ ≤ ‖(pfSegment tail t - HamiltonianEvolution B t) * HamiltonianEvolution (H 0) t‖ +
          ‖pfLie (H 0) B t - HamiltonianEvolution (H 0+B) t‖ := norm_add_le _ _
      _ ≤ ‖pfSegment tail t - HamiltonianEvolution B t‖ +
          ‖pfLie (H 0) B t - HamiltonianEvolution (H 0+B) t‖ := by
        gcongr
        exact (norm_mul_le _ _).trans
          ((mul_le_mul_of_nonneg_left (l2_norm_unitary_le_one (hamiltonianEvolution_unitary (hH 0) t))
            (norm_nonneg _)).trans_eq (mul_one _))
      _ ≤ t^2/2 * pfCommutatorSum tail + t^2/2 * ‖pfComm B (H 0)‖ := add_le_add hi hLie
      _ ≤ t^2/2 * pfCommutatorSum tail + t^2/2 * ∑ j, ‖pfComm (H 0) (tail j)‖ := by
        gcongr
      _ = _ := by rw [pfCommutatorSum_succ]; dsimp [tail]; ring

/-- The distance between the `r`th powers of two unitary matrices is at most `r` times their
operator-norm distance. -/
theorem pf_unitary_power_error {I : Type} [Fintype I] [DecidableEq I]
    (U V : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ) (r : ℕ) :
    ‖U^r - V^r‖ ≤ (r : ℝ) * ‖U-V‖ := by
  exact l2_norm_pow_sub_pow_le U V (l2_norm_unitary_le_one hU)
    (l2_norm_unitary_le_one hV) r

/-- The `r`th power of Hamiltonian evolution at time `t` equals evolution at time `r * t`. -/
theorem pf_evolution_pow {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (t : ℝ) (r : ℕ) : (HamiltonianEvolution H t)^r = HamiltonianEvolution H (r*t) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ih, ← hamiltonianEvolution_add]
    congr 1
    push_cast
    ring

/-- The segmented family operator is the `r`th power of its segment at time `t / r`. -/
private theorem pfFamily_power {D m : ℕ} (H : Fin m → Operator D) (t : ℝ) (r : ℕ) :
    pfFamily H t r = (pfSegment H (t/r))^r := by
  unfold pfFamily pfFamilyWord
  rw [pfInterpret_repeat, pfInterpret_first, List.map_ofFn]
  rfl

/-- For Hermitian family terms and positive `r`, the segmented Lie error is at most `t² / (2 *
r) * pfCommutatorSum H`, a finite first-order bound in the framework of
[ChildsEtAl2021Trotter]. -/
theorem product_formula_finite_family_segmented (D m r : ℕ) (H : Fin m → Operator D) (t : ℝ)
    (hr : 0 < r) (hH : ∀ j, (H j).IsHermitian) :
    ‖pfFamily H t r - HamiltonianEvolution (∑ j, H j) t‖ ≤ t^2 / (2*r) * pfCommutatorSum H := by
  have hsum : (∑ j, H j).IsHermitian := by
    change (∑ j, H j)ᴴ = _
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun j _ => (hH j).eq
  have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  have he : (HamiltonianEvolution (∑ j, H j) (t/r))^r = HamiltonianEvolution (∑ j, H j) t := by
    rw [pf_evolution_pow]
    congr 1
    field_simp
  rw [pfFamily_power, ← he]
  exact (pf_unitary_power_error _ _ (pfSegment_unitary H _ hH) (hamiltonianEvolution_unitary hsum _) r).trans
    ((mul_le_mul_of_nonneg_left (pfSegment_error D m H (t/r) hH) (Nat.cast_nonneg r)).trans_eq
      (by field_simp))

end Qatlib.Concepts.TrotterFormula.LieStrang
