/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NLTSAnshu23.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# SourceLemma2 — no simultaneous concentration in the two bases (Lemma 2, p.4)

Anshu–Breuckmann–Nirkhe, fixed arXiv:2206.13228v4 (STOC 2023; v4 2024-12-05),
PDF https://arxiv.org/pdf/2206.13228v4, p.4:

> Lemma 2. For `ε₁` such that `2c₁ε₁ ≤ (k/(4n))²`, either `∀i, D_z(B_i^z) < 99/100`
> or else `∀j, D_x(B_j^x) < 99/100`.

The paper's proof uses:
* Fact 3 (p.4): `D_x(T) ≤ 2√(1 − D_z(S)) + √(|S||T|/2ⁿ)` for every pair of
  subsets, modelled by `HasHadamardUncertainty`;
* the cluster size bound `|B_i^z| ≤ 2^{r_x} · 2^{2√(2c₁ε₁n)}` obtained from
  Property 1 (`B_i^z` lies within `2c₁ε₁n` of a coset of `C_x^⊥`, whose size is
  `2^{r_x}`), and analogously for the `X` side;
* `n = k + r_x + r_z`;
* the numeric consequence `√(|B_i^z||B_j^x|/2ⁿ) < 79/100`, giving
  `D_x(B_j^x) ≤ 1/5 + 79/100 < 99/100`.

Formal split (all three theorems below are fully proved):
* `concentration_bound_of_uncertainty` is the logical heart:
  mass concentration on `S` plus a small radical term forces the `T`-mass below
  `99/100`.
* `cluster_radical_bound` is the numeric cluster-size step (p.4 display),
  proved by `Real.rpow` exponent arithmetic.
* `lemma2_no_simultaneous_concentration` assembles the paper's lemma from the
  two; the cluster size bounds appear as explicit hypotheses because the
  geometric construction of the clusters (equivalence classes of `G^z_{ε₁}`)
  is not formalized here.

Boundary: the lemma is stated for abstract measurement distributions satisfying
Fact 3; the derivation of Fact 3 from a quantum state is not formalized.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Papers.NLTSAnshu23.MainResults.Model

namespace Qatlib.Papers.NLTSAnshu23.MainResults.Lemma2

/-- Logical heart of Lemma 2 (p.4).  If `D_z` gives mass at least `99/100` to
`S`, and the uncertainty radical term `√(|S||T|/2ⁿ)` is below `79/100`, then
`D_x(T) < 99/100`.  This is exactly the step
`D_x(B_j^x) ≤ 1/5 + 2^{-k+4√(2c₁ε₁n)} < 99/100` of the source proof. -/
theorem concentration_bound_of_uncertainty {n : ℕ}
    (Dx Dz : Distribution n) (hunc : HasHadamardUncertainty Dx Dz)
    (S T : Finset (BitString n))
    (hS : 99 / 100 ≤ Dz.mass S)
    (hT : Real.sqrt ((S.card : ℝ) * (T.card : ℝ) / (2 : ℝ) ^ n) < 79 / 100) :
    Dx.mass T < 99 / 100 := by
  have hmain := hunc S T
  have hsmall : 1 - Dz.mass S ≤ (1 / 10) ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (1 - Dz.mass S) ≤ 1 / 10 := by
    calc Real.sqrt (1 - Dz.mass S) ≤ Real.sqrt ((1 / 10) ^ 2) :=
          Real.sqrt_le_sqrt hsmall
      _ = 1 / 10 := Real.sqrt_sq (by norm_num)
  linarith

/-- Numeric cluster-size step of Lemma 2 (p.4).  With
`|S| ≤ 2^{r_x}·2^{2√(2c₁ε₁n)}`, `|T| ≤ 2^{r_z}·2^{2√(2c₁ε₁n)}`,
`r_x + r_z + k = n`, and `2c₁ε₁ ≤ (k/(4n))²`, the radical term is below
`79/100` in the large-parameter regime `k ≥ 2`, `n ≥ 4`.

Source: the displayed chain
`|B_i^z| ≤ 2^{r_x}·2^{2√(2c₁ε₁n)}`, `|B_j^x| ≤ 2^{r_z}·2^{2√(2c₁ε₁n)}`, then
`√(|S||T|/2ⁿ) ≤ 2^{(-k+4√(2c₁ε₁n))/2} ≤ 2^{-1/2} < 79/100`.

Proof: `2c₁ε₁n ≤ k²/(16n) ≤ k²/64` gives `√(2c₁ε₁n) ≤ k/8`, hence
`4√(2c₁ε₁n) ≤ k-1` when `k ≥ 2`, so `|S||T| ≤ 2^{rx+rz}·2^{k-1} = 2^{n-1}`
and `√(|S||T|/2ⁿ) ≤ √(1/2) < 79/100`. -/
theorem cluster_radical_bound {n k rx rz : ℕ} {ε1 c1 : ℝ}
    (hn : 0 < n) (hk : 2 ≤ k) (hn4 : 4 ≤ n)
    (hε : 2 * c1 * ε1 ≤ ((k : ℝ) / (4 * (n : ℝ))) ^ 2)
    (hr : rx + rz + k = n)
    (S T : Finset (BitString n))
    (hS : (S.card : ℝ) ≤
      (2 : ℝ) ^ rx * (2 : ℝ) ^ (2 * Real.sqrt (2 * c1 * ε1 * (n : ℝ))))
    (hT : (T.card : ℝ) ≤
      (2 : ℝ) ^ rz * (2 : ℝ) ^ (2 * Real.sqrt (2 * c1 * ε1 * (n : ℝ)))) :
    Real.sqrt ((S.card : ℝ) * (T.card : ℝ) / (2 : ℝ) ^ n) < 79 / 100 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  -- Step 1: the radical is at most `k/8`.
  have hεn : 2 * c1 * ε1 * (n : ℝ) ≤ ((k : ℝ) / 8) ^ 2 := by
    have h1 : 2 * c1 * ε1 * (n : ℝ) ≤
        ((k : ℝ) / (4 * (n : ℝ))) ^ 2 * (n : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hε (le_of_lt hnpos)
      linarith
    have h2 : ((k : ℝ) / (4 * (n : ℝ))) ^ 2 * (n : ℝ) =
        (k : ℝ) ^ 2 / (16 * (n : ℝ)) := by
      field_simp
      ring
    have h3 : (k : ℝ) ^ 2 / (16 * (n : ℝ)) ≤ (k : ℝ) ^ 2 / 64 := by
      have hden : (64 : ℝ) ≤ 16 * (n : ℝ) := by nlinarith
      have hk2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := by positivity
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (n : ℝ))
        (by norm_num : (0 : ℝ) < 64)]
      nlinarith
    have h4 : (k : ℝ) ^ 2 / 64 = ((k : ℝ) / 8) ^ 2 := by ring
    linarith
  set s : ℝ := Real.sqrt (2 * c1 * ε1 * (n : ℝ)) with hs_def
  have hs_le : s ≤ (k : ℝ) / 8 := by
    rw [hs_def]
    calc Real.sqrt (2 * c1 * ε1 * (n : ℝ)) ≤ Real.sqrt (((k : ℝ) / 8) ^ 2) :=
          Real.sqrt_le_sqrt hεn
      _ = (k : ℝ) / 8 := Real.sqrt_sq (by positivity)
  have h4s : 4 * s ≤ (k : ℝ) - 1 := by nlinarith
  -- Step 2: bound the product of the two cluster sizes by `2^{n-1}`.
  set B : ℝ := (2 : ℝ) ^ (2 * s) with hBdef
  have hBpos : 0 < B := by
    rw [hBdef]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hS_le : (S.card : ℝ) ≤ (2 : ℝ) ^ rx * B := hS
  have hT_le : (T.card : ℝ) ≤ (2 : ℝ) ^ rz * B := hT
  have hprod : (S.card : ℝ) * (T.card : ℝ) ≤
      ((2 : ℝ) ^ rx * B) * ((2 : ℝ) ^ rz * B) :=
    mul_le_mul hS_le hT_le (by positivity)
      (le_of_lt (mul_pos (by positivity) hBpos))
  have hBB : B * B = (2 : ℝ) ^ (4 * s) := by
    rw [hBdef, show (4 : ℝ) * s = 2 * s + 2 * s by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hprod_eq : ((2 : ℝ) ^ rx * B) * ((2 : ℝ) ^ rz * B) =
      (2 : ℝ) ^ (rx + rz) * (2 : ℝ) ^ (4 * s) := by
    calc ((2 : ℝ) ^ rx * B) * ((2 : ℝ) ^ rz * B)
        = ((2 : ℝ) ^ rx * (2 : ℝ) ^ rz) * (B * B) := by ring
      _ = (2 : ℝ) ^ (rx + rz) * (2 : ℝ) ^ (4 * s) := by
          rw [← pow_add, hBB]
  have hrpow : (2 : ℝ) ^ (4 * s) ≤ (2 : ℝ) ^ (k - 1) := by
    have hle : (2 : ℝ) ^ (4 * s) ≤ (2 : ℝ) ^ ((k : ℝ) - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h4s
    have hcast : (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      norm_num
    have hval : (2 : ℝ) ^ ((k - 1 : ℕ) : ℝ) = (2 : ℝ) ^ (k - 1) :=
      Real.rpow_natCast 2 (k - 1)
    rw [hcast] at hle
    rwa [hval] at hle
  have hprod2 : (S.card : ℝ) * (T.card : ℝ) ≤ (2 : ℝ) ^ (n - 1) := by
    calc (S.card : ℝ) * (T.card : ℝ)
        ≤ ((2 : ℝ) ^ rx * B) * ((2 : ℝ) ^ rz * B) := hprod
      _ = (2 : ℝ) ^ (rx + rz) * (2 : ℝ) ^ (4 * s) := hprod_eq
      _ ≤ (2 : ℝ) ^ (rx + rz) * (2 : ℝ) ^ (k - 1) :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = (2 : ℝ) ^ (n - 1) := by
          rw [← pow_add]
          congr 1
          omega
  -- Step 3: divide by `2^n` and take the square root.
  have hdiv : (S.card : ℝ) * (T.card : ℝ) / (2 : ℝ) ^ n ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
    calc (S.card : ℝ) * (T.card : ℝ) ≤ (2 : ℝ) ^ (n - 1) := hprod2
      _ = (1 / 2) * (2 : ℝ) ^ n := by
          have hn1 : n = (n - 1) + 1 := by omega
          conv_rhs => rw [hn1, pow_succ]
          ring
  calc Real.sqrt ((S.card : ℝ) * (T.card : ℝ) / (2 : ℝ) ^ n)
      ≤ Real.sqrt (1 / 2) := Real.sqrt_le_sqrt hdiv
    _ < 79 / 100 := by
        have hsq : (Real.sqrt (1 / 2 : ℝ)) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
        have hnn := Real.sqrt_nonneg (1 / 2 : ℝ)
        nlinarith

/-- Lemma 2 (p.4): for `ε₁` with `2c₁ε₁ ≤ (k/(4n))²`, the `Z`- and
`X`-measurement distributions cannot both be concentrated on a single cluster.

The cluster size bounds `hBz`, `hBx` are the paper's derived intermediate
estimates (p.4); `hr` records `n = k + r_x + r_z`.  The disjunction is proved
from `concentration_bound_of_uncertainty` once some `Z`-cluster carries mass
`≥ 99/100`; otherwise the left disjunct holds outright. -/
theorem lemma2_no_simultaneous_concentration {n k rx rz : ℕ} {ε1 c1 : ℝ}
    (hn : 0 < n) (hk : 2 ≤ k) (hn4 : 4 ≤ n)
    (P : MeasurementPair n) (hP : HasHadamardUncertainty P.Dx P.Dz)
    {ι ι' : Type}
    (Bz : ι → Finset (BitString n)) (Bx : ι' → Finset (BitString n))
    (hBz : ∀ i : ι, ((Bz i).card : ℝ) ≤
      (2 : ℝ) ^ rx * (2 : ℝ) ^ (2 * Real.sqrt (2 * c1 * ε1 * (n : ℝ))))
    (hBx : ∀ j : ι', ((Bx j).card : ℝ) ≤
      (2 : ℝ) ^ rz * (2 : ℝ) ^ (2 * Real.sqrt (2 * c1 * ε1 * (n : ℝ))))
    (hr : rx + rz + k = n)
    (hε : 2 * c1 * ε1 ≤ ((k : ℝ) / (4 * (n : ℝ))) ^ 2) :
    (∀ i : ι, P.Dz.mass (Bz i) < 99 / 100) ∨
      (∀ j : ι', P.Dx.mass (Bx j) < 99 / 100) := by
  by_cases hconc : ∀ i : ι, P.Dz.mass (Bz i) < 99 / 100
  · exact Or.inl hconc
  · right
    push Not at hconc
    obtain ⟨i, hi⟩ := hconc
    intro j
    exact concentration_bound_of_uncertainty P.Dx P.Dz hP (Bz i) (Bx j) hi
      (cluster_radical_bound hn hk hn4 hε hr (Bz i) (Bx j) (hBz i) (hBx j))

end Qatlib.Papers.NLTSAnshu23.MainResults.Lemma2
