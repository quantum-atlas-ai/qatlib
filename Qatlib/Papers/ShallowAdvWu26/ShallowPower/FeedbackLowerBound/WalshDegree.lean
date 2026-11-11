/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Qatlib.Papers.ShallowAdvWu26.ShallowPower.LightCone

set_option backward.isDefEq.respectTransparency false

/-!
# Walsh–Fourier degree versus light-cone support

Fixed version: arXiv:2608.15545v1 (2026-08-16), Appendix K (p.36-40) and
Appendix D (p.11).  Paper: *Quantum Advantage with Adaptive Shallow
Circuits*.

Appendix K argues that a shallow protocol's output, viewed as a Boolean
function on the `N` input bits, has small *Fourier* degree because it depends
on few input wires; Gyarmati's correlation bound then contradicts the DLP
output's large Fourier mass.  The Fourier half of that argument is elementary
and is proved here:

* the Walsh character `walsh T x = ∏_{j ∈ T} (-1)^{x_j}`;
* `walsh_flip` — flipping one input bit `i ∈ T` negates the character;
* `walshCoeff_eq_zero` — **the Fourier-support lemma**: if `f` depends on
  the variable set `S` and `T ⊄ S`, then the Walsh coefficient
  `∑_x f(x) walsh T x` vanishes.  The proof pairs the summands under the
  involution `x ↦ flip i x` for some `i ∈ T \ S`; `f` is invariant under
  that flip (by `DependsOn`) while `walsh T` changes sign;
* `walshCoeff_eq_zero_of_card_lt` — consequently the Fourier degree of `f`
  is at most `|S|`;
* `fourier_degree_le_lightcone` — combining with the Appendix-D bound
  `lightCone_bound`, the Fourier degree of a depth-`d`, `M`-feedback output is
  at most `(M + 1) 2^d`, which is the "small Fourier degree" input to
  Appendix K's step 2.

This file does not formalize Gyarmati's correlation bound or the DLP
Fourier-mass estimate; those remain the documented residual gap of
Theorem 3 (see `FeedbackLowerBound.lean`).
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShallowAdvWu26.ShallowPower.FeedbackLowerBound

open Qatlib.Papers.ShallowAdvWu26.ShallowPower.LightCone

/-- **Input dependence for real-valued functions.**  A real-valued function
`f` on `N` input bits depends on `S` if two inputs that agree on `S` have the
same value.  This is the `ℝ`-valued analogue of `LightCone.DependsOn`. -/
def DependsOnR {N : ℕ} (f : (Fin N → Bool) → ℝ) (S : Finset (Fin N)) : Prop :=
  ∀ x y : Fin N → Bool, (∀ i ∈ S, x i = y i) → f x = f y

/-- A Boolean function depending on `S` gives a real-valued indicator
depending on `S`. -/
theorem dependsOnR_indicator {N : ℕ} {g : (Fin N → Bool) → Bool}
    {S : Finset (Fin N)} (h : LightCone.DependsOn g S) :
    DependsOnR (fun x => if g x then (1 : ℝ) else 0) S := by
  intro x y hxy
  have hg : g x = g y := h x y hxy
  simp [hg]

/-- Flip the `i`-th input bit. -/
def flip {n : ℕ} (i : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  Function.update x i (!x i)

/-- Flipping a bit twice is the identity. -/
theorem flip_involutive {n : ℕ} (i : Fin n) (x : Fin n → Bool) :
    flip i (flip i x) = x := by
  funext j
  by_cases h : j = i
  · subst h
    simp [flip, Function.update]
  · simp [flip, Function.update, h]

/-- The bit-flip as an involutive permutation of the input cube. -/
def flipEquiv {n : ℕ} (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := flip i
  invFun := flip i
  left_inv := flip_involutive i
  right_inv := flip_involutive i

/-- **Walsh character.**  `walsh T x = ∏_{j ∈ T} (-1)^{x_j}`, the product of
`(-1)^{x_j}` over the support `T`.  This is the character `χ_T` of the group
`(Z/2Z)^n`. -/
noncomputable def walsh {n : ℕ} (T : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  ∏ j ∈ T, (if x j then (-1 : ℝ) else 1)

/-- **A character flips sign when an in-support bit flips.** -/
theorem walsh_flip {n : ℕ} (T : Finset (Fin n)) (x : Fin n → Bool) {i : Fin n}
    (hi : i ∈ T) : walsh T (flip i x) = -walsh T x := by
  unfold walsh
  rw [← Finset.mul_prod_erase T _ hi, ← Finset.mul_prod_erase T _ hi]
  have hsame : ∏ j ∈ T.erase i, (if flip i x j then (-1 : ℝ) else 1)
      = ∏ j ∈ T.erase i, (if x j then (-1 : ℝ) else 1) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [flip, Function.update, hji]
  rw [hsame]
  have hpt : (if flip i x i then (-1 : ℝ) else 1) = -(if x i then (-1 : ℝ) else 1) := by
    simp [flip, Function.update]
    cases x i <;> simp
  rw [hpt]
  ring

/-- **Fourier-support lemma.**  If `f` depends only on the variables in `S`
and `T ⊄ S`, then the Walsh coefficient of `f` at `T` vanishes.  The proof
pairs the summands under the involution `x ↦ flip i x` for `i ∈ T \ S`. -/
theorem walshCoeff_eq_zero {n : ℕ} (f : (Fin n → Bool) → ℝ) (S T : Finset (Fin n))
    (hdep : DependsOnR f S) (h : ¬ T ⊆ S) :
    ∑ x, f x * walsh T x = 0 := by
  classical
  obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp h
  have hterm : ∀ x : Fin n → Bool,
      f (flip i x) * walsh T (flip i x) = -(f x * walsh T x) := by
    intro x
    have hfx : f (flip i x) = f x :=
      (hdep x (flip i x) (fun j hj => by
        have hji : j ≠ i := fun e => hiS (e ▸ hj)
        simp [flip, Function.update, hji])).symm
    rw [hfx, walsh_flip T x hiT]
    ring
  have hflip : (∑ x, f (flip i x) * walsh T (flip i x))
      = ∑ x, f x * walsh T x :=
    Equiv.sum_comp (flipEquiv i) (fun x => f x * walsh T x)
  have hsum : (∑ x, f (flip i x) * walsh T (flip i x))
      = -(∑ x, f x * walsh T x) := by
    calc ∑ x, f (flip i x) * walsh T (flip i x)
        = ∑ x, -(f x * walsh T x) := Finset.sum_congr rfl (fun x _ => hterm x)
      _ = -(∑ x, f x * walsh T x) := by simp
  have hneg : (∑ x, f x * walsh T x) = -(∑ x, f x * walsh T x) :=
    hflip.symm.trans hsum
  linarith

/-- **Fourier degree bounded by the support size.**  If `f` depends on `S`
and `|T| > |S|`, then the coefficient at `T` vanishes: `f` has no Fourier
mass above its support size. -/
theorem walshCoeff_eq_zero_of_card_lt {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n)) (hdep : DependsOnR f S) {T : Finset (Fin n)}
    (hcard : S.card < T.card) : ∑ x, f x * walsh T x = 0 := by
  apply walshCoeff_eq_zero f S T hdep
  intro hTS
  have := Finset.card_le_card hTS
  omega

/-- **Appendix-D + Fourier bridge.**  For a depth-`d` circuit with `M`
feedback outcomes, every Walsh coefficient of the output at a set `T` of size
exceeding `(M + 1) 2^d` vanishes: the Fourier degree is at most the
light-cone support bound.  This is the "small Fourier degree" fact used in
Appendix K. -/
theorem fourier_degree_le_lightcone {N : ℕ} (Ls : List (LayerGate N))
    (readout : Finset (Fin N)) (M : ℕ) (hread : readout.card ≤ M + 1)
    (g : (Fin N → Bool) → Bool) (hg : LightCone.DependsOn g readout)
    {T : Finset (Fin N)} (hT : (M + 1) * 2 ^ Ls.length < T.card) :
    ∑ x, (if (g ∘ composeMap Ls) x then (1 : ℝ) else 0) * walsh T x = 0 := by
  obtain ⟨S, hcard, hdep⟩ := lightCone_bound Ls readout M hread g hg
  exact walshCoeff_eq_zero_of_card_lt
    (fun x => if (g ∘ composeMap Ls) x then (1 : ℝ) else 0) S
    (dependsOnR_indicator hdep) (by omega)

end Qatlib.Papers.ShallowAdvWu26.ShallowPower.FeedbackLowerBound
