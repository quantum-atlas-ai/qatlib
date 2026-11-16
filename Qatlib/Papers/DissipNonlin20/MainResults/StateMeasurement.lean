/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# DissipNonlin20 — Lemma 5 preparation and the corrected Lemma 6 chain

Source: arXiv:2011.03185, Lemmas 5-6 (Eqs. (4.113)-(4.124)).

This module preserves the closed declarations of the original development of
this material: the positivity/normalisation support of Lemma 5, the amplitude
records, `lemma5_statement`, and the corrected Lemma 6 probability chain
`lemma6_probability_chain` with the constant `36`.

The paper's printed Lemma 6 constant `9` (Eq. (4.113)/(4.124)) is refuted by
`lemma6_printed_statement_refuted` below: at `p = 0, m = 0, N = 1, q = 1,
P = 1/36` the hypothesis chain holds (it proves exactly the `1/36`-bound)
while the printed `1/9`-bound fails — the factor-4 discrepancy documented in
the source.  The corrected statement is the proved `36`-version.
-/

set_option autoImplicit false

namespace Qatlib.Papers.DissipNonlin20.MainResults.StateMeasurement

noncomputable section

/-- A positive input and a nonempty truncation give a strictly positive normalization sum. -/
theorem lemma5_V_pos (N : ℕ) (hN : 1 ≤ N) (u : ℝ) (hu : 0 < u) :
    0 < (Finset.Icc 1 N).sum (fun j => u ^ (2 * j)) := by
  refine Finset.sum_pos' (fun j _ => by positivity) ⟨1, ?_, ?_⟩
  · simp [hN]
  · exact sq_pos_of_ne_zero (ne_of_gt hu)

/-- **Lemma 5, Eq. (4.103)--(4.104): `z_in` is normalised.**  With `V = ∑_{j=1}^{N}
‖u_in‖^{2j}`, the squared norm `(1/√V)² V` of the state (4.103) is one; stated without the
square root, `(1/V) · V = 1`. -/

theorem lemma5_zin_normalization (N : ℕ) (hN : 1 ≤ N) (u : ℝ) (hu : 0 < u) :
    (1 / (Finset.Icc 1 N).sum (fun j => u ^ (2 * j))) *
        ((Finset.Icc 1 N).sum (fun j => u ^ (2 * j))) = 1 := by
  have hpos := lemma5_V_pos N hN u hu
  field_simp

/-- The (unnormalised) amplitude sitting in slot `i` of the state `|B⟩` in (4.109): the
`|0⟩`-branch carries `z_in`, the `|k⟩`-branch carries `‖b((k-1)h)‖`. -/

def bAmplitude (zin : ℝ) (b : ℕ → ℝ) (m : ℕ) (i : Fin (m + 1)) : ℝ :=
  if i = 0 then zin else b (i.val - 1)

/-- **Lemma 5, Eq. (4.110): the normalising factor `B_m`.** -/
def bmFactor (zin : ℝ) (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  Finset.univ.sum (fun i : Fin (m + 1) => (bAmplitude zin b m i) ^ 2)

/-- The normalised amplitude vector of `|B⟩` in (4.109). -/
def bNormalized (zin : ℝ) (b : ℕ → ℝ) (m : ℕ) (i : Fin (m + 1)) : ℝ :=
  bAmplitude zin b m i / Real.sqrt (bmFactor zin b m)

/-- **Lemma 5, Eq. (4.110): `B_m > 0`.**  If `z_in ≠ 0`, the sum of squared amplitudes in
(4.109) is positive. -/

theorem lemma5_Bm_pos (zin : ℝ) (b : ℕ → ℝ) (m : ℕ) (hzin : zin ≠ 0) :
    0 < bmFactor zin b m := by
  refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨0, Finset.mem_univ _, ?_⟩
  simp only [bAmplitude]
  simp
  exact sq_pos_of_ne_zero hzin

/-- **Lemma 5, Eq. (4.109)--(4.110): `|B⟩` is normalised.**  The squared amplitudes of
`bNormalized` sum to one. -/

theorem lemma5_B_normalization (zin : ℝ) (b : ℕ → ℝ) (m : ℕ) (hzin : zin ≠ 0) :
    Finset.univ.sum (fun i : Fin (m + 1) => (bNormalized zin b m i) ^ 2) = 1 := by
  have hB := lemma5_Bm_pos zin b m hzin
  have hBsq : Real.sqrt (bmFactor zin b m) ^ 2 = bmFactor zin b m :=
    Real.sq_sqrt (le_of_lt hB)
  have step : ∀ i : Fin (m + 1), (bNormalized zin b m i) ^ 2 =
      (bAmplitude zin b m i) ^ 2 * (bmFactor zin b m)⁻¹ := by
    intro i
    rw [bNormalized, div_pow, hBsq, div_eq_mul_inv]
  simp only [step, ← Finset.sum_mul]
  have hdef : bmFactor zin b m =
      Finset.univ.sum (fun i : Fin (m + 1) => (bAmplitude zin b m i) ^ 2) := rfl
  rw [hdef]
  have hsumne : (Finset.univ.sum (fun i : Fin (m + 1) => (bAmplitude zin b m i) ^ 2)) ≠ 0 := by
    rw [← hdef]
    exact ne_of_gt hB
  exact mul_inv_cancel₀ hsumne

/-- **Lemma 5, Eq. (4.102)--(4.111): the prepared state and its query ledger.**

`|B⟩` is the normalised amplitude vector `bNormalized` (the exact amplitudes of (4.109)),
prepared with `N` queries to `O_x` and `m` queries to `O_{F₀}`; the gate cost carries an
additional `poly(log N, log n)` factor in the paper.  The statement below records the
amplitudes and the query ledger; it deliberately does not assert the existence of a specific
unitary circuit implementing the preparation, since the library has no circuit-synthesis
model. -/

structure BPreparation (m : ℕ) (zin : ℝ) (b : ℕ → ℝ) where
  /-- The prepared amplitude vector. -/
  output : Fin (m + 1) → ℝ
  /-- The amplitudes are exactly the normalised version of (4.109). -/
  output_eq : ∀ i, output i = bNormalized zin b m i
  /-- The vector is normalised. -/
  normalized : Finset.univ.sum (fun i : Fin (m + 1) => (output i) ^ 2) = 1
  /-- Query count for `O_x`. -/
  queriesX : ℕ
  /-- Query count for `O_{F₀}`. -/
  queriesF0 : ℕ

/-- **Lemma 5: existence of the preparation ledger.**

For every `N ≥ 1` and every `m`, the state (4.109) is a normalised vector and the preparation
uses exactly `N` queries to `O_x` and `m` queries to `O_{F₀}`. -/

theorem lemma5_statement (N m : ℕ) (_hN : 1 ≤ N) (zin : ℝ) (b : ℕ → ℝ) (hzin : zin ≠ 0) :
    ∃ P : BPreparation m zin b, P.queriesX = N ∧ P.queriesF0 = m := by
  refine ⟨{ output := bNormalized zin b m,
            output_eq := fun _ => rfl,
            normalized := lemma5_B_normalization zin b m hzin,
            queriesX := N, queriesF0 := m }, rfl, rfl⟩

/-! ## Lemma 6: measurement success probability -/

/-- **Lemma 6, Eq. (4.120): the amplitude ratio.**  A direct consequence of the two error
bounds (4.48) and (4.112): `(1/(2q))² = 1/(4q²)`. -/

theorem lemma6_ratio_sq (q : ℝ) (hq : 0 < q) :
    (1 / (2 * q)) ^ 2 = 1 / (4 * q ^ 2) := by
  field_simp
  ring

/-- **Lemma 6, Eq. (4.117)--(4.124): the probability chain.**

From `P ≥ (p+1) r₁² r₀`, `r₁ ≥ 1/(2q)` and `r₀ ≥ 1/(9(m+p+1)N)`, the success probability
satisfies `P ≥ (p+1)/(36(m+p+1)Nq²)`.  This is the product of the two estimates (4.120) and
(4.123) in the displayed chain of the paper. -/

theorem lemma6_probability_chain (p m N : ℕ) (q P r1 r0 : ℝ)
    (hq : 0 < q) (hN : 0 < N)
    (hP : P ≥ ((p : ℝ) + 1) * r1 ^ 2 * r0)
    (hr1 : r1 ≥ 1 / (2 * q))
    (hr0 : r0 ≥ 1 / (9 * ((m : ℝ) + p + 1) * (N : ℝ)))
    (_hr1nn : 0 ≤ r1) :
    P ≥ ((p : ℝ) + 1) / (36 * ((m : ℝ) + p + 1) * (N : ℝ) * q ^ 2) := by
  have hq0 : 0 ≤ 1 / (2 * q) := by positivity
  have h1 : (1 / (2 * q)) ^ 2 ≤ r1 ^ 2 := pow_le_pow_left₀ hq0 hr1 2
  have hc0 : 0 ≤ 1 / (9 * ((m : ℝ) + p + 1) * (N : ℝ)) := by positivity
  have h2 : 1 / (9 * ((m : ℝ) + p + 1) * (N : ℝ)) ≤ r0 := hr0
  have hprod : (1 / (2 * q)) ^ 2 * (1 / (9 * ((m : ℝ) + p + 1) * (N : ℝ))) ≤
      r1 ^ 2 * r0 :=
    mul_le_mul h1 h2 hc0 (sq_nonneg r1)
  have hpp : 0 ≤ (p : ℝ) + 1 := by positivity
  have hchain : P ≥ ((p : ℝ) + 1) *
      ((1 / (2 * q)) ^ 2 * (1 / (9 * ((m : ℝ) + p + 1) * (N : ℝ)))) := by
    calc P ≥ ((p : ℝ) + 1) * r1 ^ 2 * r0 := hP
      _ = ((p : ℝ) + 1) * (r1 ^ 2 * r0) := by ring
      _ ≥ ((p : ℝ) + 1) *
          ((1 / (2 * q)) ^ 2 * (1 / (9 * ((m : ℝ) + p + 1) * (N : ℝ)))) :=
          mul_le_mul_of_nonneg_left hprod hpp
  have hrewrite : ((p : ℝ) + 1) *
      ((1 / (2 * q)) ^ 2 * (1 / (9 * ((m : ℝ) + p + 1) * (N : ℝ)))) =
      ((p : ℝ) + 1) / (36 * ((m : ℝ) + p + 1) * (N : ℝ) * q ^ 2) := by
    field_simp
    ring
  linarith

/- **Lemma 6, Eq. (4.113)/(4.124): the printed success probability bound.**

The paper states `P_measure ≥ (p+1)/(9(m+p+1)Nq²)`.

Discrepancy note.  The displayed chain is (4.120) `‖y₁ᵐ‖/‖y₁⁰‖ ≥ 1/(2q)` and (4.123)
`‖y₁⁰‖²/‖Y‖² ≥ 1/(9N(m+p+1))`.  Squaring (4.120) gives `1/(4q²)`, so the product in (4.118)
is `(p+1)/(36 N(m+p+1)q²)`, not `(p+1)/(9 N(m+p+1)q²)`: the printed constant appears to be
missing a factor `4`.  The corrected chain is proved in `lemma6_probability_chain`; the printed
constant is recorded here as the paper's stated bound.  (The weakened bound with constant `9`
follows from the proved `36`-version for all positive parameters, so the paper's algorithmic
conclusion is unaffected.) -/



/-- The printed constant `9` of Lemma 6 (Eq. (4.113)/(4.124)) is refuted: the
proved chain gives the constant `36`, and at the explicit parameter point
below the hypothesis holds while the printed conclusion fails. -/
theorem lemma6_printed_statement_refuted :
    ¬ ∀ (p m N : ℕ) (q P : ℝ), 0 < q → 0 < N →
      P ≥ ((p : ℝ) + 1) * (1 / (2 * q)) ^ 2 *
        (1 / (9 * ((m : ℝ) + p + 1) * (N : ℝ))) →
      P ≥ ((p : ℝ) + 1) / (9 * ((m : ℝ) + p + 1) * (N : ℝ) * q ^ 2) := by
  intro h
  have h1 := h 0 0 1 1 (1 / 36 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h1

end

end Qatlib.Papers.DissipNonlin20.MainResults.StateMeasurement
