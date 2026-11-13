/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QHamDescent23.MainResults.HammingEncoding.HammingModel

set_option backward.isDefEq.respectTransparency false

/-!
# Hamming-Weight Basis States and Collective Pauli Ladder Operators

This module formalizes Appendix F.3 (Lemmas 5--7 and Corollary 2, Equations
(F.31)--(F.34) and (F.45)--(F.47)) of Leng, Hickman, Li, and Wu on the Hamming-weight
symmetric subspace of `(ℂ^2)^{⊗ n}`, establishing orthonormality of the Dicke/Hamming
states `|H_k⟩`, binomial decomposition of `|+⟩^{⊗ n}`, the exact action of collective
Pauli operators `∑_j σ_x^{(j)}` and `∑_j σ_z^{(j)}`, and the expectation values of the
encoded position and ladder operators `X̂` and `Â'`.

## Main definitions

* `sxCoeffUp`, `sxCoeffDown`, `sxImage`: collective `σ_x` ladder coefficients and image ket.
* `szMatrix`, `xHat`, `aPrime`: collective `σ_z` matrix, encoded position `X̂`, and normalized `Â'`.

## Main statements

* `source_lemma5_hamming_orthonormal`: Lemma 5, Eq. (F.31), `⟨H_j | H_k⟩ = δ_{jk}`.
* `source_lemma6_uniform_decomposition`: Lemma 6, Eq. (F.32), Hamming expansion of `|+⟩^{⊗ n}`.
* `source_lemma7_sx_action`, `source_lemma7_sz_action`: Lemma 7, Eqs. (F.33)--(F.34).
* `source_corollary2_hamming_encoding`: Corollary 2, Eqs. (F.45)--(F.47), `⟨H_k|X̂|H_k⟩ = k` and `⟨H_k|Â'|H_k⟩ = 0`.

## References

* [Leng et al., 2023][LengEtAl2023QHD], Appendix F.3, Lemmas 5--7 and Corollary 2, pp. 52--54.
-/

open scoped Matrix BigOperators
open Matrix

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QHamDescent23.MainResults.HammingEncoding
open Qatlib.Papers.QHamDescent23.MainResults Qatlib.Papers.QHamDescent23.MainResults.HammingEncoding


/-
### Lemma 5 (F.31)

Source: arXiv:2303.01471v1, Lemma 5, p.52, equation (F.31).

The Hamming states are orthonormal: `⟨H_j|H_k⟩ = δ_{jk}` for `0 ≤ j,k ≤ n`.

Paper proof route: the layers `{|b⟩ : |b| = j}` and `{|b⟩ : |b| = k}` are
disjoint for `j ≠ k`, and on the same layer the normalisation
`C_j^{-1/2}` gives `C_j · C_j^{-1} = 1`.

Formal proof: on the equal layer the sum reduces to
`#{b : weight b = j} · (C_j)⁻¹`; `card_weight_eq_choose` identifies the layer
cardinality with `Nat.choose n j`, and `Real.mul_self_sqrt` cancels the
normalisation `(√C_j)⁻¹`. On different layers each summand vanishes because no
bit string has two different weights.
-/
/-- Lemma 5 (F.31): Hamming states are orthonormal. -/
theorem source_lemma5_hamming_orthonormal (n j k : ℕ) (hj : j ≤ n) (hk : k ≤ n) :
    bracket (hammingState n j) (hammingState n k) = if j = k then 1 else 0 := by
  classical
  by_cases hjk : j = k
  · subst hjk
    simp only [ite_true, bracket]
    have hc : ((Real.sqrt (Nat.choose n j) : ℝ) : ℂ) ≠ 0 := by
      have hpos : 0 < Nat.choose n j :=
        Nat.choose_pos (le_trans (le_min hj hk) (min_le_left n n))
      have hs : (0:ℝ) < Real.sqrt (Nat.choose n j) := Real.sqrt_pos.mpr (by exact_mod_cast hpos)
      exact_mod_cast (ne_of_gt hs)
    have hcard : (Finset.univ.filter (fun b : BitString n => weight b = j)).card
        = Nat.choose n j := by
      rw [← Fintype.card_subtype (fun b : BitString n => weight b = j), card_weight_eq_choose]
    -- rewrite each summand
    have hpt : ∀ b : BitString n,
        star (hammingState n j b) * hammingState n j b
          = if weight b = j then (((Nat.choose n j : ℝ) : ℂ))⁻¹ else 0 := by
      intro b
      by_cases hb : weight b = j
      · simp only [hammingState, hb, ite_true]
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
        simp [Complex.normSq_ofReal]
      · simp [hammingState, hb]
    simp only [hpt]
    rw [← Finset.sum_filter, Finset.sum_const, hcard]
    rw [nsmul_eq_mul]
    have hcast : (((Nat.choose n j : ℝ)) : ℂ)
        = ((Real.sqrt (Nat.choose n j) : ℝ) : ℂ) * ((Real.sqrt (Nat.choose n j) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    have hnat : ((Nat.choose n j : ℕ) : ℂ) = (((Nat.choose n j : ℝ)) : ℂ) := by
      push_cast; ring
    rw [hnat, hcast]
    exact mul_inv_cancel₀ (mul_ne_zero hc hc)
  · simp only [bracket, hjk, ite_false]
    refine Finset.sum_eq_zero (fun b _ => ?_)
    by_cases hb : weight b = j
    · simp [hammingState, hb, hjk]
    · simp [hammingState, hb]

/-
### Lemma 6 (F.32)

Source: arXiv:2303.01471v1, Lemma 6, p.53, equation (F.32).

The uniform superposition `|s⟩ = |+⟩^{⊗n}` decomposes in the Hamming basis as

`s = Σ_{j=0}^n √(C_j / 2^n) |H_j⟩`.

Paper proof route: every computational basis state has some weight `j`, and on
the weight-`j` layer the coefficient of `|s⟩` is `2^{-n/2}`, matching
`√(C_j/2^n) · C_j^{-1/2}`.

Formal proof: `Finset.sum_eq_single (weight b)` leaves only the layer of `b`
(`weight_le` puts it in `range (n+1)`); the coefficient identity
`√(C_j/2ⁿ) · (√C_j)⁻¹ = (√2ⁿ)⁻¹` is `uniform_coeff`, proved with
`Real.sqrt_div` and `field_simp`.
-/
/-- Coefficient identity behind Lemma 6 (F.32): the uniform amplitude equals
the product of the Hamming-layer coefficient and the layer normalisation on
the layer of `b`. -/
private lemma uniform_coeff (n : ℕ) (b : BitString n) :
    (((Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ))⁻¹
      = (((Real.sqrt ((Nat.choose n (weight b) : ℝ) / (2 : ℝ) ^ n) : ℝ)) : ℂ) *
        (((Real.sqrt (Nat.choose n (weight b) : ℝ) : ℝ)) : ℂ)⁻¹ := by
  have hCpos : (0:ℝ) < (Nat.choose n (weight b) : ℝ) := by
    exact_mod_cast Nat.choose_pos (weight_le b)
  have hreal : Real.sqrt ((Nat.choose n (weight b) : ℝ) / (2 : ℝ) ^ n) *
      (Real.sqrt (Nat.choose n (weight b) : ℝ))⁻¹ = (Real.sqrt ((2 : ℝ) ^ n))⁻¹ := by
    rw [Real.sqrt_div (le_of_lt hCpos)]
    field_simp
  have := congrArg (fun r : ℝ => (r : ℂ)) hreal
  push_cast at this
  rw [this]

/-- Lemma 6 (F.32): the uniform superposition decomposes in the Hamming basis. -/
theorem source_lemma6_uniform_decomposition (n : ℕ) :
    uniformState n
      = Finset.sum (Finset.range (n + 1)) (fun j =>
          (((Real.sqrt ((Nat.choose n j : ℝ) / (2 : ℝ) ^ n) : ℝ)) : ℂ) •
            hammingState n j) := by
  funext b
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single (weight b)]
  · simp only [Pi.smul_apply, smul_eq_mul, hammingState, uniformState]
    exact uniform_coeff n b
  · intro j hj hja
    simp only [Pi.smul_apply, smul_eq_mul, hammingState]
    simp [Ne.symm hja]
  · intro hnotmem
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (weight_le b))) hnotmem

/-- Coefficient raising a weight-`k` Hamming state to weight `k+1` in the
action of `Σ_j σ_x^{(j)}` (Lemma 7, (F.33)): `(k+1) √(C_{k+1}/C_k)`, equal to
the `√((k+1)(n−k))` matrix element of (F.33). -/
def sxCoeffUp (n k : ℕ) : ℂ :=
  (((k + 1 : ℕ) : ℂ) *
    (((Real.sqrt ((Nat.choose n (k + 1) : ℝ) / (Nat.choose n k : ℝ)) : ℝ)) : ℂ))

/-- Coefficient lowering a weight-`k` Hamming state to weight `k−1` in the
action of `Σ_j σ_x^{(j)}` (Lemma 7, (F.33)): `(n−k+1) √(C_{k−1}/C_k)`, equal
to the `√(k(n−k+1))` matrix element of (F.33); it is zero for `k = 0`. -/
def sxCoeffDown (n k : ℕ) : ℂ :=
  if k = 0 then 0 else
    (((n - k + 1 : ℕ) : ℂ) *
      (((Real.sqrt ((Nat.choose n (k - 1) : ℝ) / (Nat.choose n k : ℝ)) : ℝ)) : ℂ))

/-- The right-hand side of (F.33): the image of `|H_k⟩` under `Σ_j σ_x^{(j)}`. -/
def sxImage (n k : ℕ) : Ket (BitString n) :=
  fun b => sxCoeffUp n k * hammingState n (k + 1) b
    + sxCoeffDown n k * hammingState n (k - 1) b

/-
### Lemma 7 (F.33)–(F.34)

Source: arXiv:2303.01471v1, Lemma 7, p.53, equations (F.33)–(F.34).

On the Hamming basis the global Pauli sums act as
`Σ_j σ_x^{(j)} |H_k⟩ = √((k+1)(n−k))|H_{k+1}⟩ + √(k(n−k+1))|H_{k−1}⟩`
(equivalently `(k+1)√(C_{k+1}/C_k)` and `(n−k+1)√(C_{k−1}/C_k)`) and
`Σ_j σ_z^{(j)} |H_k⟩ = (n−2k)|H_k⟩`.

Paper proof route: flipping a zero of a weight-`k` string produces weight
`k+1` and there are `n−k` zeros; grouping by the target weight-`(k+1)` string
shows each such string has `k+1` predecessors, giving the normalised
coefficient `(k+1)√(C_{k+1}/C_k)`.  Dually, a weight-`k` string has `k` ones
and each target weight-`(k−1)` string has `n−k+1` predecessors.  For `σ_z`,
each zero contributes `+1` and each one `−1`, giving `(n−k)·1 + k·(−1) = n−2k`.

The proof counts flips over the support and its complement. Only target
weights `k+1` and `k-1` contribute; square-root cancellation identifies the
normalised coefficients on these two layers.
-/
private lemma flipBit_involutive {n : ℕ} (i : Fin n) (b : BitString n) :
    flipBit i (flipBit i b) = b := by
  funext j
  by_cases hji : j = i
  · subst j
    cases hb : b i <;> simp [flipBit, hb]
  · simp [flipBit, hji]

private lemma weight_flipBit_of_true {n : ℕ} (i : Fin n) (b : BitString n)
    (hb : b i = true) : weight (flipBit i b) + 1 = weight b := by
  classical
  have hs : support (flipBit i b) = (support b).erase i := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [support, flipBit, hb]
    · simp [support, flipBit, hji]
  rw [weight_eq_support_card, hs, Finset.card_erase_add_one]
  · rfl
  · simp [support, hb]

private lemma weight_flipBit_of_false {n : ℕ} (i : Fin n) (b : BitString n)
    (hb : b i = false) : weight (flipBit i b) = weight b + 1 := by
  classical
  have hs : support (flipBit i b) = insert i (support b) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [support, flipBit, hb]
    · simp [support, flipBit, hji]
  rw [weight_eq_support_card, hs, Finset.card_insert_of_notMem]
  · rfl
  · simp [support, hb]

private lemma hamming_normalization_ratio (n j k : ℕ) (hj : j ≤ n) (hk : k ≤ n) :
    (Real.sqrt ((Nat.choose n j : ℝ) / (Nat.choose n k : ℝ)) : ℂ) *
        (Real.sqrt (Nat.choose n j) : ℂ)⁻¹ =
      (Real.sqrt (Nat.choose n k) : ℂ)⁻¹ := by
  have hjpos : (0 : ℝ) < Nat.choose n j := by exact_mod_cast Nat.choose_pos hj
  have hkpos : (0 : ℝ) < Nat.choose n k := by exact_mod_cast Nat.choose_pos hk
  have hjne := ne_of_gt (Real.sqrt_pos.mpr hjpos)
  have hkne := ne_of_gt (Real.sqrt_pos.mpr hkpos)
  have hr : Real.sqrt ((Nat.choose n j : ℝ) / (Nat.choose n k : ℝ)) *
      (Real.sqrt (Nat.choose n j))⁻¹ = (Real.sqrt (Nat.choose n k))⁻¹ := by
    rw [← one_div (Real.sqrt (Nat.choose n k))]
    apply (eq_div_iff hkne).2
    rw [Real.sqrt_div (le_of_lt hjpos)]
    field_simp [hjne, hkne]
  exact_mod_cast hr

/-- Lemma 7 (F.33): action of `Σ_j σ_x^{(j)}` on the Hamming basis. -/
theorem source_lemma7_sx_action (n k : ℕ) (hk : k ≤ n) :
    sxApply (hammingState n k) = sxImage n k := by
  classical
  funext b
  by_cases hup : weight b = k + 1
  · have hkn : k + 1 ≤ n := hup ▸ weight_le b
    have hsep : k + 1 ≠ k - 1 := by omega
    have hsum : sxApply (hammingState n k) b =
        ((k + 1 : ℕ) : ℂ) * (Real.sqrt (Nat.choose n k) : ℂ)⁻¹ := by
      calc
        _ = ∑ i : Fin n, if b i = true then
            (Real.sqrt (Nat.choose n k) : ℂ)⁻¹ else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          cases hb : b i
          · have hf := weight_flipBit_of_false i b hb
            have hne : weight (flipBit i b) ≠ k := by omega
            simp [hammingState, hne]
          · have hf := weight_flipBit_of_true i b hb
            have heq : weight (flipBit i b) = k := by omega
            simp [hammingState, heq]
        _ = _ := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          change (weight b : ℂ) * _ = _
          rw [hup]
    rw [hsum]
    simp only [sxImage, hammingState, hup, hsep, ite_true, ite_false, mul_zero,
      add_zero, sxCoeffUp]
    rw [mul_assoc, hamming_normalization_ratio n (k + 1) k hkn hk]
  · by_cases hdown : k ≠ 0 ∧ weight b = k - 1
    · have hpred : k - 1 ≤ n := le_trans (Nat.sub_le k 1) hk
      have hsep : k - 1 ≠ k + 1 := by omega
      have hsum : sxApply (hammingState n k) b =
          ((n - k + 1 : ℕ) : ℂ) * (Real.sqrt (Nat.choose n k) : ℂ)⁻¹ := by
        calc
          _ = ∑ i : Fin n, if b i = false then
              (Real.sqrt (Nat.choose n k) : ℂ)⁻¹ else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            cases hb : b i
            · have hf := weight_flipBit_of_false i b hb
              have heq : weight (flipBit i b) = k := by omega
              simp [hammingState, heq]
            · have hf := weight_flipBit_of_true i b hb
              have hne : weight (flipBit i b) ≠ k := by omega
              simp [hammingState, hne]
          _ = _ := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            have hcount : (Finset.univ.filter (fun i : Fin n => b i = false)).card +
                weight b = n := by
              simpa [weight, Bool.not_eq_true] using
                (Finset.card_filter_add_card_filter_not (s := Finset.univ)
                  (p := fun i : Fin n => b i = false))
            have hc : (Finset.univ.filter (fun i : Fin n => b i = false)).card =
                n - k + 1 := by omega
            rw [hc]
      rw [hsum]
      simp only [sxImage, hammingState, hdown.2, hsep, ite_true, ite_false,
        mul_zero, zero_add, sxCoeffDown, hdown.1]
      rw [mul_assoc, hamming_normalization_ratio n (k - 1) k hpred hk]
    · have hsum : sxApply (hammingState n k) b = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hne : weight (flipBit i b) ≠ k := by
          intro heq
          cases hb : b i
          · have hf := weight_flipBit_of_false i b hb
            omega
          · have hf := weight_flipBit_of_true i b hb
            omega
        simp [hammingState, hne]
      rw [hsum]
      by_cases hk0 : k = 0
      · subst k
        simp [sxImage, hammingState, hup, sxCoeffDown]
      · have hne : weight b ≠ k - 1 := by tauto
        simp [sxImage, hammingState, hup, hne]

/-- Source Lemma 7 (F.34): `Σ_j σ_z^{(j)} |H_k⟩ = (n − 2k)|H_k⟩`. -/
theorem source_lemma7_sz_action (n k : ℕ) (hk : k ≤ n) :
    szApply (hammingState n k) = ((n : ℂ) - 2 * (k : ℂ)) • hammingState n k := by
  funext b
  by_cases h : weight b = k
  · change ((n : ℂ) - 2 * (weight b : ℂ)) * hammingState n k b = _
    calc
      _ = (((n - k + k : ℕ) : ℂ) - 2 * (k : ℂ)) * hammingState n k b := by
        rw [Nat.sub_add_cancel hk, h]
      _ = _ := by simp [Nat.sub_add_cancel hk]
  · simp [szApply, hammingState, h]

/-- Diagonal matrix of `Σ_j σ_z^{(j)}` (Lemma 7). -/
def szMatrix (n : ℕ) : Matrix (BitString n) (BitString n) ℂ :=
  fun b b' => if b' = b then ((n : ℂ) - 2 * (weight b : ℂ)) else 0

/-- The encoded position operator `X̂ = ½ Σ_j (1 − σ_z^{(j)}) = ½ (n − Σ_j σ_z^{(j)})`
(Corollary 2, (F.45)). -/
def xHat (n : ℕ) : Matrix (BitString n) (BitString n) ℂ :=
  (1 / 2 : ℂ) • ((n : ℂ) • (1 : Matrix (BitString n) (BitString n) ℂ) - szMatrix n)

/-- The encoded operator `Â′ = n^{-1/2} Σ_j σ_x^{(j)}` (Corollary 2, (F.46)). -/
def aPrime (n : ℕ) : Matrix (BitString n) (BitString n) ℂ :=
  (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) • sxMatrix n

private lemma szMatrix_mulVec {n : ℕ} (ψ : Ket (BitString n)) :
    szMatrix n *ᵥ ψ = szApply ψ := by
  classical
  funext b
  simp [mulVec, dotProduct, szMatrix, szApply, ite_mul]

/-
### Corollary 2 (F.45)–(F.47)

Source: arXiv:2303.01471v1, Corollary 2, p.54.

The Hamming encoding realises the position variable as the Hamming weight
`X̂ = ½ Σ_j (1 − σ_z^{(j)})`, and the auxiliary operator `Â′` as
`n^{-1/2} Σ_j σ_x^{(j)}`. On the Hamming state `|H_k⟩` the encoded position has
expectation `k` and `Â′` has vanishing diagonal `⟨H_k|Â′|H_k⟩ = 0`; the
off-diagonal coefficients are the ladder coefficients of (F.46).

Paper proof route: combine Lemma 7 with the definitions of `X̂` and `Â′`:
`⟨H_k|½(n − S_z)|H_k⟩ = ½(n − (n − 2k)) = k`, and `Â′` is off-diagonal because
`S_x` raises/lowers the weight.

The matrix actions reduce to Lemma 7. Orthonormality evaluates the position
expectation, and the disjoint weights make every summand of the ladder
expectation vanish.
-/
/-- Corollary 2 (F.45)–(F.47): the encoded position has expectation `k` on
`|H_k⟩` and the encoded ladder operator has vanishing diagonal. -/
theorem source_corollary2_hamming_encoding (n k : ℕ) (hk : k ≤ n) :
    bracket (hammingState n k) (xHat n *ᵥ hammingState n k) = (k : ℂ) ∧
    bracket (hammingState n k) (aPrime n *ᵥ hammingState n k) = 0 := by
  classical
  have hx : xHat n *ᵥ hammingState n k = (k : ℂ) • hammingState n k := by
    rw [xHat, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, szMatrix_mulVec, source_lemma7_sz_action n k hk]
    funext b
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  constructor
  · rw [hx, bracket_smul_right, source_lemma5_hamming_orthonormal n k k hk hk]
    simp
  · rw [aPrime, Matrix.smul_mulVec, sxMatrix_mulVec, source_lemma7_sx_action n k hk]
    unfold bracket
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hw : weight b = k
    · have hup : weight b ≠ k + 1 := by omega
      have hz : sxImage n k b = 0 := by
        by_cases hk0 : k = 0
        · subst hk0
          simp [sxImage, hammingState, hup, sxCoeffDown]
        · have hdown : weight b ≠ k - 1 := by omega
          simp [sxImage, hammingState, hup, hdown]
      simp [hz]
    · simp [hammingState, hw]

end Qatlib.Papers.QHamDescent23.MainResults.HammingEncoding
