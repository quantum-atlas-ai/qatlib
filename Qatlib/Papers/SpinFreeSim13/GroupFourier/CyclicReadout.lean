/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.Tactic

@[expose] public section

/-!
# Cyclic character readout: Wigner projectors and Born weights

[Whitfield2013], Eqs. (9) and (14)–(15) and the readout of Fig. 1 of
[arXiv:1306.1147v1](https://arxiv.org/abs/1306.1147v1).

The paper's phase-estimation readout is indexed by the irreducible representations of
the symmetry group `Γ`. For a cyclic group `ZMod N` every irreducible representation is
one-dimensional, and the character-weighted Wigner projector is

`P_r = (1 / N) * ∑_g χ_r(g) T_g`,

where `T_g` is the regular translation action and `χ_r(g) = exp (2 π i r g / N)`.
The paper conjugates the character in the projector coefficient. Since
`χ_r(g) = conj (χ_{-r}(g))`, the projector indexed by `r` here corresponds to
the paper's character label `-r`.
This module proves, for every `N > 0`, that

* `wignerOp_eq_smul_charVec`: `P_r` is the rank-one projector onto the normalized
  character vector `charVec r`, so the reconstructed component is
  `amplitude ψ r • charVec r`;
* `wignerOp_idem` and `wignerOp_orthogonal`: distinct Wigner projectors are orthogonal
  idempotents, the abelian matrix-unit relations;
* `sum_wignerOp`: the projectors resolve the identity;
* `total_weight`: the Born weights `‖P_r ψ‖²` of the readout sum to the Euclidean norm
  squared of `ψ` (`Parseval`), and `weight_charVec` gives probability one on the
  character eigenstate;
* `norm_wignerOp_le` and `uniform_contraction`: the readout branch is a contraction with
  the absolute constant `1` outside all quantifiers, uniformly in the group order.

State norms are taken in `EuclideanSpace` (`L²`). The hypothesis `NeZero N` ensures
that `ZMod N` is a finite cyclic group of positive order. The results concern the
projected branches on the regular representation for one-dimensional character labels.

## References

* [Whitfield, 2013][Whitfield2013]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open scoped BigOperators
open scoped InnerProductSpace ComplexConjugate

namespace Qatlib.Papers.SpinFreeSim13.GroupFourier

section Cyclic

variable {N : ℕ} [NeZero N]

/-- The character value `χ_r(g) = exp (2 π i r g / N)` of the cyclic group `ZMod N`. -/
def char (r g : ZMod N) : ℂ := ZMod.stdAddChar (r * g)

/-- The regular translation action of `ZMod N` on amplitude functions. -/
def regAct (g : ZMod N) : (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun ψ := fun x => ψ (x - g)
  map_add' f h := by ext x; rfl
  map_smul' c f := by ext x; rfl

/-- The normalized prefactor `1 / √N`. -/
def sqrtInv : ℂ := ((Real.sqrt (N : ℝ) : ℂ))⁻¹

/-- The character-weighted Wigner projector
`P_r = (1 / N) * ∑_g χ_r(g) T_g` of the cyclic readout. -/
def wignerOp (r : ZMod N) (ψ : ZMod N → ℂ) : ZMod N → ℂ :=
  ((N : ℂ)⁻¹) • ∑ g : ZMod N, char r g • regAct g ψ

/-- The normalized character vector `x ↦ χ_r(x) / √N`. -/
def charVec (r : ZMod N) : ZMod N → ℂ := fun x => sqrtInv (N := N) * char r x

/-- The Fourier amplitude `⟨charVec r, ψ⟩` using character values at inverse elements. -/
def amplitude (ψ : ZMod N → ℂ) (r : ZMod N) : ℂ :=
  sqrtInv (N := N) * ∑ g : ZMod N, char r (-g) * ψ g

/-- The amplitude function regarded as a vector in complex Euclidean space. -/
def toE (ψ : ZMod N → ℂ) : EuclideanSpace ℂ (ZMod N) := WithLp.toLp 2 ψ

/-- The finite `L²` inner product `∑ x, star (φ x) * χ x` of two amplitude functions. -/
def innerF (φ χ : ZMod N → ℂ) : ℂ := ∑ x, star (φ x) * χ x

/-- Characters are multiplicative in the group variable. -/
theorem char_add (r g h : ZMod N) : char r (g + h) = char r g * char r h := by
  unfold char
  rw [mul_add, AddChar.map_add_eq_mul]

/-- The character at an inverse group element is the multiplicative inverse. -/
theorem char_neg (r g : ZMod N) : char r (-g) = (char r g)⁻¹ := by
  unfold char
  rw [mul_neg, AddChar.map_neg_eq_inv]

/-- Character values have complex norm one. -/
theorem norm_char (r g : ZMod N) : ‖char r g‖ = 1 := by
  unfold char
  simp

/-- Complex conjugation of a character value is the character at the inverse element. -/
theorem star_char (r g : ZMod N) : star (char r g) = char r (-g) := by
  rw [char_neg]
  exact (Complex.inv_eq_conj (norm_char r g)).symm

/-- The product of the character at `-g` for `r` and at `g` for `s` is the character
of the difference `s - r`. -/
theorem char_mul_char_neg (r s g : ZMod N) :
    char r (-g) * char s g = char (s - r) g := by
  unfold char
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Summing a character over the group gives the order on the trivial character and zero
otherwise. -/
theorem sum_char (b : ZMod N) :
    (∑ g : ZMod N, char b g) = if b = 0 then (N : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (R := ZMod N) (R' := ℂ) b
    (ZMod.isPrimitive_stdAddChar N)
  simp only [char]
  rw [show (∑ g : ZMod N, ZMod.stdAddChar (b * g)) =
      ∑ g : ZMod N, ZMod.stdAddChar (g * b) from
    Finset.sum_congr rfl (fun g _ => by rw [mul_comm])]
  rw [h]
  by_cases hb : b = 0
  · simp [hb, ZMod.card]
  · simp [hb]

/-- Summing over the character label instead of the group element gives the same
orthogonality relation. -/
theorem sum_char_right (g : ZMod N) :
    (∑ r : ZMod N, char r g) = if g = 0 then (N : ℂ) else 0 := by
  have h : (∑ r : ZMod N, char r g) = ∑ r : ZMod N, char g r :=
    Finset.sum_congr rfl (fun r _ => by
      unfold char
      rw [mul_comm])
  rw [h]
  exact sum_char g

omit [NeZero N] in
/-- The normalized prefactor squares to the inverse group order. -/
theorem sqrtInv_mul_self :
    sqrtInv (N := N) * sqrtInv (N := N) = ((N : ℂ))⁻¹ := by
  have hsq : ((Real.sqrt (N : ℝ) : ℂ)) * ((Real.sqrt (N : ℝ) : ℂ)) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    norm_num
  unfold sqrtInv
  rw [← mul_inv, hsq]

/-- The normalized prefactor is nonzero. -/
theorem sqrtInv_ne_zero : sqrtInv (N := N) ≠ 0 := by
  have hN : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hs : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN
  have hc : ((Real.sqrt (N : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt hs)
  unfold sqrtInv
  exact inv_ne_zero hc

/-- Pointwise formula for the Wigner projector. -/
theorem wignerOp_apply (r : ZMod N) (ψ : ZMod N → ℂ) (x : ZMod N) :
    wignerOp r ψ x = ((N : ℂ))⁻¹ * ∑ g : ZMod N, char r g * ψ (x - g) := by
  simp [wignerOp, regAct, Pi.smul_apply, smul_eq_mul]

/-- Reindexing a sum over translations by `x`. -/
theorem sum_sub_reindex (x : ZMod N) (f : ZMod N → ℂ) :
    (∑ g : ZMod N, f (x - g)) = ∑ h : ZMod N, f h := by
  have h1 : (∑ g : ZMod N, f (x - g)) = ∑ g : ZMod N, f (x + g) := by
    rw [show (∑ g : ZMod N, f (x - g)) =
        ∑ g : ZMod N, (fun h => f (x + h)) (-g) from
      Finset.sum_congr rfl (fun g _ => by rw [sub_eq_add_neg])]
    exact Equiv.sum_comp (Equiv.neg (ZMod N)) (fun h => f (x + h))
  rw [h1]
  exact Equiv.sum_comp (Equiv.addLeft x) f

/-- The Wigner projector is the rank-one projector onto the character vector. -/
theorem wignerOp_eq_smul_charVec (r : ZMod N) (ψ : ZMod N → ℂ) :
    wignerOp r ψ = amplitude ψ r • charVec r := by
  ext x
  rw [wignerOp_apply]
  simp only [Pi.smul_apply, smul_eq_mul, amplitude, charVec]
  have hre : (∑ g : ZMod N, char r g * ψ (x - g)) =
      ∑ h : ZMod N, char r (x - h) * ψ h := by
    simpa [sub_sub_cancel] using
      sum_sub_reindex x (fun h => char r (x - h) * ψ h)
  rw [hre]
  have hsplit : (∑ h : ZMod N, char r (x - h) * ψ h) =
      char r x * ∑ h : ZMod N, char r (-h) * ψ h := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [sub_eq_add_neg, char_add]
    ring
  rw [hsplit]
  rw [show ((N : ℂ))⁻¹ = sqrtInv (N := N) * sqrtInv (N := N) from
    (sqrtInv_mul_self (N := N)).symm]
  ring

/-- The amplitude is linear in the state. -/
theorem amplitude_smul (c : ℂ) (ψ : ZMod N → ℂ) (r : ZMod N) :
    amplitude (c • ψ) r = c * amplitude ψ r := by
  simp only [amplitude, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ g : ZMod N, char r (-g) * (c * ψ g)) =
      c * ∑ g : ZMod N, char r (-g) * ψ g from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    ring]
  ring

/-- The amplitude of a normalized character vector is one on its own label and zero
elsewhere. -/
theorem amplitude_charVec (r s : ZMod N) :
    amplitude (charVec s) r = if r = s then 1 else 0 := by
  simp only [amplitude, charVec]
  rw [show (∑ g : ZMod N, char r (-g) * (sqrtInv (N := N) * char s g)) =
      sqrtInv (N := N) * ∑ g : ZMod N, char r (-g) * char s g from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    ring]
  simp only [char_mul_char_neg]
  rw [sum_char]
  by_cases h : s - r = 0
  · have hrs : r = s := by
      have : s = r := sub_eq_zero.mp h
      exact this.symm
    subst hrs
    simp only [sub_self, ↓reduceIte]
    rw [show sqrtInv (N := N) * (sqrtInv (N := N) * (N : ℂ)) = 1 from by
      rw [← mul_assoc, sqrtInv_mul_self]
      exact inv_mul_cancel₀ (by exact_mod_cast (NeZero.ne N))]
  · have hrs : r ≠ s := by
      intro hrs
      subst hrs
      exact h (sub_self r)
    simp [h, hrs]

/-- Distinct Wigner projectors multiply to zero, and each is idempotent. -/
theorem wignerOp_idem (r s : ZMod N) (ψ : ZMod N → ℂ) :
    wignerOp r (wignerOp s ψ) = if r = s then wignerOp s ψ else 0 := by
  rw [wignerOp_eq_smul_charVec s ψ,
    wignerOp_eq_smul_charVec r (amplitude ψ s • charVec s)]
  rw [amplitude_smul, amplitude_charVec]
  by_cases hrs : r = s
  · subst hrs
    simp
  · simp [hrs]

/-- Distinct Wigner projectors have orthogonal ranges. -/
theorem wignerOp_orthogonal {r s : ZMod N} (hrs : r ≠ s) (ψ : ZMod N → ℂ) :
    wignerOp r (wignerOp s ψ) = 0 := by
  rw [wignerOp_idem]
  simp [hrs]

/-- The Wigner projectors resolve the identity. -/
theorem sum_wignerOp (ψ : ZMod N → ℂ) :
    (∑ r : ZMod N, wignerOp r ψ) = ψ := by
  ext x
  simp only [Finset.sum_apply, wignerOp_apply]
  rw [← Finset.mul_sum]
  rw [show (∑ r : ZMod N, ∑ g : ZMod N, char r g * ψ (x - g)) =
      ∑ g : ZMod N, (∑ r : ZMod N, char r g) * ψ (x - g) from by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g _
    rw [Finset.sum_mul]]
  simp only [sum_char_right]
  rw [Finset.sum_eq_single (0 : ZMod N)]
  · simp [NeZero.ne N]
  · intro g _ hg
    simp [hg]
  · intro h
    simp at h

/-- The finite inner product of two amplitude functions as a Euclidean inner product. -/
theorem inner_toE (φ χ : ZMod N → ℂ) :
    ⟪toE φ, toE χ⟫_ℂ = innerF φ χ := by
  simp only [toE, innerF, PiLp.inner_apply, RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm, starRingEnd_apply]

/-- The finite inner product of a vector with itself is its squared Euclidean norm. -/
theorem innerF_self (ψ : ZMod N → ℂ) :
    innerF ψ ψ = ((‖toE ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [innerF, EuclideanSpace.norm_sq_eq]
  simp only [toE, WithLp.ofLp_toLp]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _
  simpa using Complex.conj_mul' (ψ x)

/-- Complex conjugating the finite inner product swaps its arguments. -/
theorem innerF_comm_star (φ χ : ZMod N → ℂ) :
    innerF φ χ = star (innerF χ φ) := by
  unfold innerF
  rw [star_sum]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [star_mul, star_star]

/-- The finite inner product is additive in its second argument. -/
theorem innerF_sum_right (φ : ZMod N → ℂ) (s : Finset (ZMod N))
    (f : ZMod N → ZMod N → ℂ) :
    innerF φ (fun x => ∑ r ∈ s, f r x) = ∑ r ∈ s, innerF φ (f r) := by
  simp only [innerF, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The finite inner product of a character vector with an arbitrary state is the
Fourier amplitude. -/
theorem innerF_charVec_eq_amplitude (r : ZMod N) (ψ : ZMod N → ℂ) :
    innerF (charVec r) ψ = amplitude ψ r := by
  rw [innerF, amplitude]
  have hconj : ∀ x : ZMod N, star (charVec r x) = sqrtInv (N := N) * char r (-x) := by
    intro x
    rw [charVec, star_mul, star_char]
    rw [show star (sqrtInv (N := N)) = sqrtInv (N := N) from by
      unfold sqrtInv
      simp]
    ring
  simp only [hconj]
  rw [show (∑ x : ZMod N, (sqrtInv (N := N) * char r (-x)) * ψ x) =
      sqrtInv (N := N) * ∑ x : ZMod N, char r (-x) * ψ x from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring]

/-- The normalized character vectors are orthonormal. -/
theorem innerF_charVec (r s : ZMod N) :
    innerF (charVec r) (charVec s) = if r = s then 1 else 0 := by
  rw [innerF_charVec_eq_amplitude, amplitude_charVec]

/-- The normalized character vectors have Euclidean norm one. -/
theorem norm_charVec (r : ZMod N) : ‖toE (charVec r)‖ = 1 := by
  have h := innerF_self (charVec r)
  have h1 : innerF (charVec r) (charVec r) = 1 := by
    rw [innerF_charVec]
    simp
  rw [h1] at h
  have h2 : ‖toE (charVec r)‖ ^ 2 = 1 := by
    exact_mod_cast (Complex.ofReal_inj.mp h.symm)
  nlinarith [norm_nonneg (toE (charVec r))]

/-- The inner product of a projected vector with an arbitrary vector. -/
theorem innerF_wignerOp_left (r : ZMod N) (φ χ : ZMod N → ℂ) :
    innerF (wignerOp r φ) χ = star (amplitude φ r) * amplitude χ r := by
  rw [wignerOp_eq_smul_charVec]
  unfold innerF
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (∑ x : ZMod N, star (amplitude φ r * charVec r x) * χ x) =
        star (amplitude φ r) * ∑ x : ZMod N, star (charVec r x) * χ x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [star_mul]
      ring
    _ = star (amplitude φ r) * amplitude χ r := by
      rw [show (∑ x : ZMod N, star (charVec r x) * χ x) = innerF (charVec r) χ from rfl]
      rw [innerF_charVec_eq_amplitude]

/-- The inner product of an arbitrary vector with a projected vector. -/
theorem innerF_wignerOp_right (r : ZMod N) (φ χ : ZMod N → ℂ) :
    innerF φ (wignerOp r χ) = star (amplitude φ r) * amplitude χ r := by
  rw [wignerOp_eq_smul_charVec]
  simp only [innerF, Pi.smul_apply, smul_eq_mul]
  have hsplit : (∑ x : ZMod N, star (φ x) * (amplitude χ r * charVec r x)) =
      amplitude χ r * ∑ x : ZMod N, star (φ x) * charVec r x := by
    calc
      (∑ x : ZMod N, star (φ x) * (amplitude χ r * charVec r x)) =
          ∑ x : ZMod N, amplitude χ r * (star (φ x) * charVec r x) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = amplitude χ r * ∑ x : ZMod N, star (φ x) * charVec r x := by
        rw [Finset.mul_sum]
  rw [hsplit]
  rw [show (∑ x : ZMod N, star (φ x) * charVec r x) = innerF φ (charVec r) from rfl]
  rw [innerF_comm_star, innerF_charVec_eq_amplitude]
  ring

/-- The cyclic Wigner projector is Hermitian for the Euclidean inner product. -/
theorem wignerOp_hermitian (r : ZMod N) (φ χ : ZMod N → ℂ) :
    ⟪toE (wignerOp r φ), toE χ⟫_ℂ = ⟪toE φ, toE (wignerOp r χ)⟫_ℂ := by
  rw [inner_toE, inner_toE, innerF_wignerOp_left, innerF_wignerOp_right]

/-- The amplitude of a projected state on its own label is unchanged. -/
theorem amplitude_wignerOp_self (r : ZMod N) (ψ : ZMod N → ℂ) :
    amplitude (wignerOp r ψ) r = amplitude ψ r := by
  rw [wignerOp_eq_smul_charVec, amplitude_smul, amplitude_charVec]
  have h : (if r = r then (1 : ℂ) else 0) = 1 := by simp
  rw [h, mul_one]

/-- The Wigner projector is a contraction in the Euclidean norm. -/
theorem norm_wignerOp_le (r : ZMod N) (ψ : ZMod N → ℂ) :
    ‖toE (wignerOp r ψ)‖ ≤ ‖toE ψ‖ := by
  by_cases hzero : toE (wignerOp r ψ) = 0
  · rw [hzero, norm_zero]
    exact norm_nonneg _
  · have hpos : 0 < ‖toE (wignerOp r ψ)‖ := norm_pos_iff.mpr hzero
    have hself : innerF (wignerOp r ψ) (wignerOp r ψ) = innerF ψ (wignerOp r ψ) := by
      rw [innerF_wignerOp_left, innerF_wignerOp_right, amplitude_wignerOp_self]
    have hcomplex : ((‖toE (wignerOp r ψ)‖ ^ 2 : ℝ) : ℂ) =
        ⟪toE ψ, toE (wignerOp r ψ)⟫_ℂ := by
      rw [inner_toE, ← hself]
      exact (innerF_self (wignerOp r ψ)).symm
    have hreal : ‖toE (wignerOp r ψ)‖ ^ 2 = Complex.re ⟪toE ψ, toE (wignerOp r ψ)⟫_ℂ := by
      have h' := congrArg Complex.re hcomplex
      change (Complex.ofReal (‖toE (wignerOp r ψ)‖ ^ 2)).re =
        (⟪toE ψ, toE (wignerOp r ψ)⟫_ℂ).re at h'
      have hre : (Complex.ofReal (‖toE (wignerOp r ψ)‖ ^ 2)).re =
          ‖toE (wignerOp r ψ)‖ ^ 2 :=
        Complex.ofReal_re _
      rw [hre] at h'
      exact h'
    have hbound : ‖toE (wignerOp r ψ)‖ ^ 2 ≤ ‖toE ψ‖ * ‖toE (wignerOp r ψ)‖ := by
      rw [hreal]
      exact le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
    nlinarith [norm_nonneg (toE ψ), hpos]

/-- The Born weight of a readout label is the squared Euclidean norm of the projected
branch. -/
def weight (ψ : ZMod N → ℂ) (r : ZMod N) : ℝ := ‖toE (wignerOp r ψ)‖ ^ 2

/-- A nonzero projected branch normalizes to a unit Euclidean vector. -/
theorem normalizedBranch_norm (ψ : ZMod N → ℂ) (r : ZMod N)
    (h : toE (wignerOp r ψ) ≠ 0) :
    ‖((‖toE (wignerOp r ψ)‖ : ℂ)⁻¹) • toE (wignerOp r ψ)‖ = 1 := by
  rw [norm_smul, norm_inv]
  have hnorm : ‖((‖toE (wignerOp r ψ)‖ : ℝ) : ℂ)‖ = ‖toE (wignerOp r ψ)‖ := by simp
  rw [hnorm]
  have hne : ‖toE (wignerOp r ψ)‖ ≠ 0 := norm_ne_zero_iff.mpr h
  field_simp [hne]

/-- The weight of a branch equals the squared modulus of its Fourier amplitude. -/
theorem weight_eq_amplitude (ψ : ZMod N → ℂ) (r : ZMod N) :
    weight ψ r = ‖amplitude ψ r‖ ^ 2 := by
  rw [weight, wignerOp_eq_smul_charVec]
  have h : toE (amplitude ψ r • charVec r) = amplitude ψ r • toE (charVec r) := by
    simp [toE]
  rw [h, norm_smul, norm_charVec, mul_one]

/-- The readout weights of a character eigenstate concentrate on its own label. -/
theorem weight_charVec (r s : ZMod N) :
    weight (charVec s) r = if r = s then 1 else 0 := by
  rw [weight_eq_amplitude, amplitude_charVec]
  by_cases hrs : r = s
  · simp [hrs]
  · simp [hrs]

/-- The Born weights of all readout labels sum to the squared Euclidean norm (Parseval). -/
theorem total_weight (ψ : ZMod N → ℂ) :
    (∑ r : ZMod N, weight ψ r) = ‖toE ψ‖ ^ 2 := by
  have hcomplex : (∑ r : ZMod N, ((weight ψ r : ℝ) : ℂ)) =
      ((‖toE ψ‖ ^ 2 : ℝ) : ℂ) := by
    have hterm : ∀ r : ZMod N, ((weight ψ r : ℝ) : ℂ) =
        innerF (wignerOp r ψ) (wignerOp r ψ) :=
      fun r => (innerF_self (wignerOp r ψ)).symm
    simp only [hterm]
    rw [show (∑ r : ZMod N, innerF (wignerOp r ψ) (wignerOp r ψ)) =
        ∑ r : ZMod N, innerF ψ (wignerOp r ψ) from by
      apply Finset.sum_congr rfl
      intro r _
      rw [innerF_wignerOp_left, innerF_wignerOp_right, amplitude_wignerOp_self]]
    rw [← innerF_sum_right]
    have hsum : (fun x => ∑ r : ZMod N, wignerOp r ψ x) =
        ∑ r : ZMod N, wignerOp r ψ := by
      funext x
      rw [Finset.sum_apply]
    rw [hsum, sum_wignerOp, innerF_self]
  exact_mod_cast hcomplex

/-- On a normalized state the readout weights sum to one. -/
theorem total_weight_unit (ψ : ZMod N → ℂ) (hψ : ‖toE ψ‖ = 1) :
    (∑ r : ZMod N, weight ψ r) = 1 := by
  rw [total_weight, hψ]
  norm_num

end Cyclic

section Uniform

/-- The Wigner readout is a contraction with the absolute constant `1`, uniformly over
every positive group order, every readout label and every state. -/
theorem uniform_contraction :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) [NeZero M] (r : ZMod M) (ψ : ZMod M → ℂ),
        ‖toE (wignerOp r ψ)‖ ≤ C * ‖toE ψ‖ := by
  refine ⟨1, one_pos, ?_⟩
  intro M _ r ψ
  simpa using norm_wignerOp_le (N := M) r ψ

end Uniform

end Qatlib.Papers.SpinFreeSim13.GroupFourier
