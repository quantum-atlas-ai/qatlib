/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

@[expose] public section


/-!
# Counterexamples to the four unrestricted lattice-sum contracts

The quantified legacy library contracts below have unrestricted sequences
and an unrestricted tail function,
so the stated conclusions do not follow from nonnegativity or exponent guards.
These counterexamples refute those library interfaces, not the source paper.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Qatlib.Papers.TrotterError19.MainResults.LatticeChecks

/-- The exact natural-system-size Big O notation from the original contract. -/
abbrev BigO (f g : ℕ → ℝ) : Prop := f =O[atTop] g

/-- Squaring the natural variable cannot be bounded by a fixed multiple of that variable. -/
private theorem square_not_bigO_linear :
    ¬ BigO (fun n : ℕ => (n : ℝ) ^ 2) (fun n => (n : ℝ)) := by
  intro h
  obtain ⟨c, hc⟩ := isBigO_iff.mp h
  obtain ⟨N, hN⟩ := eventually_atTop.1 hc
  obtain ⟨k, hk⟩ := exists_nat_gt c
  let n := N + k + 1
  have hnN : N ≤ n := by dsimp [n]; omega
  have hkn : k ≤ n := by dsimp [n]; omega
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by dsimp [n]; omega)
  have hcn : c < (n : ℝ) := lt_of_lt_of_le hk (by exact_mod_cast hkn)
  have hn := hN n hnN
  simp only [Real.norm_eq_abs, abs_pow,
    abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)] at hn
  nlinarith [mul_pos hnpos (sub_pos.mpr hcn)]

/-- The natural variable cannot be bounded by a fixed real constant. -/
private theorem linear_not_bigO_one :
    ¬ BigO (fun n : ℕ => (n : ℝ)) (fun _ => 1) := by
  intro h
  obtain ⟨c, hc⟩ := isBigO_iff.mp h
  obtain ⟨N, hN⟩ := eventually_atTop.1 hc
  obtain ⟨k, hk⟩ := exists_nat_gt c
  let n := N + k + 1
  have hnN : N ≤ n := by dsimp [n]; omega
  have hkn : k ≤ n := by dsimp [n]; omega
  have hcn : c < (n : ℝ) := lt_of_lt_of_le hk (by exact_mod_cast hkn)
  have hn := hN n hnN
  simp only [Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n), abs_one, mul_one] at hn
  exact (not_le_of_gt hcn) hn

/-- The natural variable grows faster than its logarithm. -/
private theorem linear_not_bigO_log :
    ¬ BigO (fun n : ℕ => (n : ℝ)) (fun n => Real.log (n : ℝ)) := by
  intro h
  have hlog : (fun n : ℕ => Real.log (n : ℝ)) =o[atTop] (fun n => (n : ℝ)) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.comp_tendsto
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hne : ∃ᶠ n : ℕ in atTop, (n : ℝ) ≠ 0 := by
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact_mod_cast (show n ≠ 0 by omega)
  exact isLittleO_irrefl hne (h.trans_isLittleO hlog)

/-- Legacy subcritical lattice-sum contract for every nonnegative sequence, without a lattice-sum hypothesis. -/
def LegacySubcriticalLatticeSumContract : Prop :=
  ∀ (α : ℝ) (d : ℕ) (_hd : 1 ≤ d) (_hα : 0 ≤ α)
    (_hαd : α < (d : ℝ)) (s : ℕ → ℝ) (_hs : ∀ n, 0 ≤ s n),
    BigO s (fun n => Real.rpow (n : ℝ) (1 - α / (d : ℝ)))

/-- Legacy logarithmic lattice-sum contract for every nonnegative sequence. -/
def LegacyCriticalLatticeSumContract : Prop :=
  ∀ (d : ℕ) (_hd : 1 ≤ d) (s : ℕ → ℝ) (_hs : ∀ n, 0 ≤ s n),
    BigO s (fun n => Real.log (n : ℝ))

/-- Legacy constant lattice-sum bound for every nonnegative sequence under a supercritical exponent guard. -/
def LegacySupercriticalLatticeSumContract : Prop :=
  ∀ (α : ℝ) (d : ℕ) (_hd : 1 ≤ d) (_hαd : (d : ℝ) < α)
    (s : ℕ → ℝ) (_hs : ∀ n, 0 ≤ s n),
    BigO s (fun _ => 1)

/-- Legacy uniform power-decay tail contract for every real-valued tail function under a supercritical exponent guard. -/
def LegacyUniformLatticeTailContract : Prop :=
  ∀ (α : ℝ) (d : ℕ) (_hd : 1 ≤ d) (_hαd : (d : ℝ) < α)
    (tail : ℝ → ℝ),
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      tail x ≤ C * Real.rpow x (d - α)

/-- A nonnegative quadratic sequence is a counterexample to the legacy subcritical lattice-sum contract. -/
theorem not_legacy_subcritical_lattice_sum_contract : ¬ LegacySubcriticalLatticeSumContract := by
  intro h
  have hs : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ 2 := fun n => sq_nonneg _
  have hh := h 0 1 (by norm_num) (by norm_num) (by norm_num) (fun n => (n : ℝ) ^ 2) hs
  apply square_not_bigO_linear
  simpa using hh

/-- A nonnegative linear sequence is a counterexample to the legacy critical lattice-sum contract. -/
theorem not_legacy_critical_lattice_sum_contract : ¬ LegacyCriticalLatticeSumContract := by
  intro h
  exact linear_not_bigO_log (h 1 (by norm_num) (fun n => (n : ℝ)) (fun n => Nat.cast_nonneg n))

/-- A nonnegative linear sequence is a counterexample to the legacy supercritical lattice-sum contract. -/
theorem not_legacy_supercritical_lattice_sum_contract : ¬ LegacySupercriticalLatticeSumContract := by
  intro h
  exact linear_not_bigO_one
    (h 2 1 (by norm_num) (by norm_num) (fun n => (n : ℝ)) (fun n => Nat.cast_nonneg n))

/-- The identity tail is a counterexample to the legacy uniform lattice-tail contract. -/
theorem not_legacy_uniform_lattice_tail_contract : ¬ LegacyUniformLatticeTailContract := by
  intro h
  obtain ⟨C, hC, hbound⟩ := h 2 1 (by norm_num) (by norm_num) id
  have hx : 0 < C + 1 := by linarith
  have hh := hbound (C + 1) (by linarith)
  simp only [id_eq, Nat.cast_one] at hh
  rw [show (1 : ℝ) - 2 = -1 by norm_num] at hh
  simp only [Real.rpow_eq_pow, Real.rpow_neg_one] at hh
  have hdiv : C + 1 ≤ C / (C + 1) := by
    simpa only [div_eq_mul_inv] using hh
  have hs : (C + 1) * (C + 1) ≤ C := (le_div_iff₀ hx).mp hdiv
  nlinarith [sq_nonneg C]

end Qatlib.Papers.TrotterError19.MainResults.LatticeChecks
