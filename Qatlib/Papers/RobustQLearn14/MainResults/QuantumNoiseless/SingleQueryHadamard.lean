/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

set_option backward.isDefEq.respectTransparency false

/-!
# RobustQLearn14.MainResults.QuantumNoiseless — one coherent query suffices

Fixed source: Cross--Smith--Smolin, *Quantum learning robust to noise*,
arXiv:1407.5088v1 (18 Jul 2014).

Claim `c003` (Sec. III, Eqs. (6)--(7), p. 3): given the quantum example state
`|ψ_f⟩ = 2^{-n/2} Σ_x |x, f_a(x)⟩`, applying Hadamards to all `n + 1` output
qubits yields

  `(1/√2) (|0^n, 0⟩ + |a, 1⟩)`.                                    (7)

Hence with probability `1/2` a computational-basis measurement reveals `a`
in the query register, and `O(log(1/δ))` repetitions amplify success to `1-δ`.

The computation is a Walsh--Hadamard transform on `GF(2)^{n+1}`.  The amplitude
at `(y,b)` is `2^{-n} · 2^{-1/2} Σ_x (-1)^{⟨y,x⟩ + b⟨a,x⟩}`; the character
orthogonality `Σ_x (-1)^{⟨u,x⟩} = 2^n [u = 0]` then gives Eq. (7).  This file
proves the character orthogonality and the amplitude identity exactly.
-/

open scoped BigOperators

namespace Qatlib.Papers.RobustQLearn14.MainResults

noncomputable section

/-! ## Characters of `GF(2)^n` -/

/-- The character value `(-1)^z` for `z ∈ GF(2)`, as a real number.
Source: arXiv:1407.5088v1, Sec. III, p. 3 (Walsh--Hadamard signs). -/
def realSign (z : ZMod 2) : ℝ := if z = 0 then 1 else -1

/-- The `GF(2)`-valued inner product `⟨u,x⟩ = Σ_i u_i x_i`.
Source: arXiv:1407.5088v1, Sec. III, p. 3 (parity `f_a(x) = ⟨a,x⟩`). -/
def dot {n : ℕ} (u x : Fin n → ZMod 2) : ZMod 2 := ∑ i, u i * x i

/-- In characteristic two, `x + x = 0`.
Source: arXiv:1407.5088v1, Sec. III, p. 2 (arithmetic in `GF(2)`). -/
theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc x + x = 2 * x := by ring
    _ = 0 := by rw [h2, zero_mul]

/-- Every element of `GF(2)` is `0` or `1`.
Source: arXiv:1407.5088v1, Sec. III, p. 2 (the field `GF(2)`). -/
theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  decide +revert

/-- The two elements of `ZMod 2` are `0` and `1`.
Source: arXiv:1407.5088v1, Sec. III, p. 2 (the field `GF(2)`). -/
theorem univ_zmod2 : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

/-- The character at `0` is `1`.
Source: arXiv:1407.5088v1, Sec. III, p. 3 (Walsh--Hadamard signs). -/
theorem realSign_zero : realSign 0 = 1 := by simp [realSign]

/-- The character at `1` is `-1`.
Source: arXiv:1407.5088v1, Sec. III, p. 3 (Walsh--Hadamard signs). -/
theorem realSign_one : realSign 1 = -1 := by
  unfold realSign
  rw [if_neg (by decide : (1 : ZMod 2) ≠ 0)]

/-- Additivity of the sign character on `GF(2)`.
Source: arXiv:1407.5088v1, Sec. III, p. 3 (`(-1)^{z+z'} = (-1)^z (-1)^{z'}`). -/
theorem realSign_add (a b : ZMod 2) : realSign (a + b) = realSign a * realSign b := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one b with rfl | rfl
  · rw [show (0 : ZMod 2) + 0 = 0 by decide, realSign_zero]; ring
  · rw [show (0 : ZMod 2) + 1 = 1 by decide, realSign_one, realSign_zero]; ring
  · rw [show (1 : ZMod 2) + 0 = 1 by decide, realSign_one, realSign_zero]; ring
  · rw [show (1 : ZMod 2) + 1 = 0 by decide, realSign_zero, realSign_one]; ring

/-- The sign of a finite sum is the product of the signs.
Source: arXiv:1407.5088v1, Sec. III, p. 3 (multiplicativity of characters). -/
theorem realSign_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ZMod 2) :
    realSign (∑ i ∈ s, f i) = ∏ i ∈ s, realSign (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [realSign]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, realSign_add, ih]

/-- The character splits over coordinates: `(-1)^{⟨u,x⟩} = ∏_i (-1)^{u_i x_i}`.
Source: arXiv:1407.5088v1, Sec. III, p. 3 (Walsh--Hadamard on `GF(2)^n`). -/
theorem realSign_dot {n : ℕ} (u x : Fin n → ZMod 2) :
    realSign (dot u x) = ∏ i, realSign (u i * x i) := by
  unfold dot
  exact realSign_sum Finset.univ (fun i => u i * x i)

/-- One-coordinate character sum: `Σ_{y ∈ GF(2)} (-1)^{c y} = 2` if `c = 0`
and `0` if `c ≠ 0`.
Source: arXiv:1407.5088v1, Sec. III, p. 3 (one-bit character orthogonality). -/
theorem sum_realSign_mul (c : ZMod 2) :
    (∑ y : ZMod 2, realSign (c * y)) = if c = 0 then 2 else 0 := by
  rcases zmod2_eq_zero_or_one c with rfl | rfl
  · rw [if_pos rfl, univ_zmod2]
    simp [realSign]
  · rw [if_neg (by decide : (1 : ZMod 2) ≠ 0), univ_zmod2]
    simp [realSign]

/-- Character orthogonality on the Boolean cube:
`Σ_x (-1)^{⟨u,x⟩} = 2^n` if `u = 0`, and `0` otherwise.  This is the
`GF(2)`-Fourier orthogonality underlying Eq. (7).
Source: arXiv:1407.5088v1, Sec. III, p. 3 (orthogonality used for Eq. (7)). -/
theorem sum_char_orthogonality {n : ℕ} (u : Fin n → ZMod 2) :
    (∑ x : Fin n → ZMod 2, realSign (dot u x)) = if u = 0 then (2 : ℝ) ^ n else 0 := by
  have hprod : (∑ x : Fin n → ZMod 2, realSign (dot u x))
      = ∑ x : Fin n → ZMod 2, ∏ i, realSign (u i * x i) := by
    apply Finset.sum_congr rfl
    intro x _
    exact realSign_dot u x
  rw [hprod]
  have hp := Finset.sum_prod_piFinset (s := (Finset.univ : Finset (ZMod 2)))
    (g := fun (i : Fin n) (y : ZMod 2) => realSign (u i * y))
  rw [Fintype.piFinset_univ] at hp
  rw [hp]
  have hinner : ∀ i : Fin n, (∑ y : ZMod 2, realSign (u i * y))
      = if u i = 0 then (2 : ℝ) else 0 := fun i => sum_realSign_mul (u i)
  have hprod2 : (∏ i : Fin n, (∑ y : ZMod 2, realSign (u i * y)))
      = ∏ i : Fin n, (if u i = 0 then (2 : ℝ) else 0) :=
    Finset.prod_congr rfl (fun i _ => hinner i)
  rw [hprod2]
  by_cases hu : u = 0
  · subst hu
    simp [Finset.prod_const, Fintype.card_fin]
  · rw [if_neg hu]
    have hex : ∃ i, u i ≠ 0 := by
      by_contra h
      apply hu
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-! ## Hadamard amplitude of the example state -/

/-- Amplitude at `(y,b)` after applying `H^{⊗(n+1)}` to `|ψ_{f_a}⟩`.
The amplitude is `2^{-n} · 2^{-1/2} Σ_x (-1)^{⟨y,x⟩ + b⟨a,x⟩}`, written with
the combined vector `u = y + b·a` (in `GF(2)`, `y + b·a` encodes the exponent).
Source: arXiv:1407.5088v1, Sec. III, Eq. (6), p. 3. -/
def hadamardAmplitude {n : ℕ} (a y : Fin n → ZMod 2) (b : ZMod 2) : ℝ :=
  (1 / Real.sqrt 2) * ((2 : ℝ) ^ n)⁻¹ *
    (∑ x : Fin n → ZMod 2, realSign (dot (fun i => y i + b * a i) x))

/-- Orthogonality turns the Hadamard amplitude into the indicator of
`y + b·a = 0`, scaled by `1/√2`.
Source: arXiv:1407.5088v1, Sec. III, Eq. (6), p. 3. -/
theorem hadamardAmplitude_eq {n : ℕ} (a y : Fin n → ZMod 2) (b : ZMod 2) :
    hadamardAmplitude a y b =
      (1 / Real.sqrt 2) * (if (fun i => y i + b * a i) = 0 then 1 else 0) := by
  unfold hadamardAmplitude
  rw [sum_char_orthogonality]
  by_cases hu : (fun i : Fin n => y i + b * a i) = 0
  · rw [if_pos hu, if_pos hu, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0))]
  · rw [if_neg hu, if_neg hu]
    ring

/-- An indicator times `1/√2` is the indicator with value `1/√2`.
Source: arXiv:1407.5088v1, Sec. III, Eq. (7), p. 3 (normalisation `1/√2`). -/
theorem sqrt2_inv_mul_indicator (P : Prop) [Decidable P] :
    (1 / Real.sqrt 2 : ℝ) * (if P then (1 : ℝ) else 0) =
      if P then 1 / Real.sqrt 2 else 0 := by
  by_cases h : P <;> simp [h]

/-- `y + a = 0` iff `y = a` in `GF(2)^n` (characteristic two).
Source: arXiv:1407.5088v1, Sec. III, p. 3 (the two peaks of Eq. (7)). -/
theorem add_self_eq_zero_iff {n : ℕ} (y a : Fin n → ZMod 2) :
    (fun i => y i + a i) = 0 ↔ y = a := by
  constructor
  · intro h
    funext i
    have hi : y i + a i = 0 := congrFun h i
    calc y i = y i + (a i + a i) := by rw [zmod2_add_self (a i), add_zero]
      _ = (y i + a i) + a i := (add_assoc _ _ _).symm
      _ = 0 + a i := by rw [hi]
      _ = a i := zero_add _
  · intro h
    funext i
    rw [h]
    exact zmod2_add_self (a i)

/-- `c003` / Eq. (7): after Hadamards the example state has amplitude `1/√2`
exactly on the two basis states `|0^n, 0⟩` and `|a, 1⟩`, and amplitude `0`
elsewhere.  Source: arXiv:1407.5088v1, Sec. III, Eqs. (6)--(7), p. 3. -/
theorem hadamard_example_amplitude {n : ℕ} (a y : Fin n → ZMod 2) (b : ZMod 2) :
    hadamardAmplitude a y b =
      if y = 0 ∧ b = 0 then 1 / Real.sqrt 2
      else if y = a ∧ b = 1 then 1 / Real.sqrt 2 else 0 := by
  rw [hadamardAmplitude_eq, sqrt2_inv_mul_indicator]
  have hiff : ((fun i : Fin n => y i + b * a i) = 0) ↔
      (y = 0 ∧ b = 0) ∨ (y = a ∧ b = 1) := by
    rcases zmod2_eq_zero_or_one b with rfl | rfl
    · constructor
      · intro h
        left
        refine ⟨?_, rfl⟩
        have hu : (fun i : Fin n => y i + (0 : ZMod 2) * a i) = y := by
          funext i; simp
        rw [hu] at h
        exact h
      · rintro (⟨hy, -⟩ | ⟨-, hb1⟩)
        · funext i
          rw [hy]
          simp
        · exact absurd hb1 (by decide : (0 : ZMod 2) ≠ 1)
    · constructor
      · intro h
        right
        refine ⟨?_, rfl⟩
        have hu : (fun i : Fin n => y i + (1 : ZMod 2) * a i) = fun i => y i + a i := by
          funext i; simp
        rw [hu] at h
        exact (add_self_eq_zero_iff y a).mp h
      · rintro (⟨hy, hb0⟩ | ⟨hya, -⟩)
        · exact absurd hb0 (by decide : (1 : ZMod 2) ≠ 0)
        · funext i
          rw [hya]
          simp only [one_mul, Pi.zero_apply]
          exact zmod2_add_self (a i)
  by_cases hA : y = 0 ∧ b = 0
  · rw [if_pos hA]
    have hu : (fun i : Fin n => y i + b * a i) = 0 := hiff.mpr (Or.inl hA)
    rw [if_pos hu]
  · rw [if_neg hA]
    by_cases hB : y = a ∧ b = 1
    · rw [if_pos hB]
      have hu : (fun i : Fin n => y i + b * a i) = 0 := hiff.mpr (Or.inr hB)
      rw [if_pos hu]
    · rw [if_neg hB]
      have hu : ¬ ((fun i : Fin n => y i + b * a i) = 0) := by
        intro h
        rcases hiff.mp h with h' | h'
        · exact hA h'
        · exact hB h'
      rw [if_neg hu]

/-- `c003` consequence: the probability of the measurement outcome `(a, 1)`,
whose query register carries `a`, is `1/2`.  Source: arXiv:1407.5088v1,
Sec. III, p. 3 ("with probability 1/2, measurement reveals the value of a"). -/
theorem single_query_success_probability :
    (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

end

end Qatlib.Papers.RobustQLearn14.MainResults
