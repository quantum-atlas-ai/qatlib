/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinBool08.MainResults.BentCore.BentFacts
import Qatlib.Papers.NonlinBool08.MainResults.AffineTransform
import Qatlib.Papers.NonlinBool08.MainResults.MaioranaMcFarland.Lemma4

/-!
# Bent hidden-shift identities and decoding

Defines the hidden-shift promises and proves uniqueness and spectral decoding for bent functions
with a Boolean dual. It also gives binary orthogonality constraints and matching exact query
bounds for the shifted dot-product family. See [Roetteler2008].

## Main statements

* `decode_eq`: the corrected Walsh spectrum identifies the hidden shift.
* `orth_ext`: all orthogonality constraints determine the shift.
* `mmZero_lower`: fewer than m fixed queries cannot distinguish all shifts in the dot-product
  family.

## References

* [Roetteler, 2008][Roetteler2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix
open Finset

namespace Qatlib.Papers.NonlinBool08.MainResults.HiddenShift

open Qatlib.Papers.NonlinBool08.MainResults.BentCore
open Qatlib.Papers.NonlinBool08.MainResults.AffineTransform
open Qatlib.Papers.NonlinBool08.MainResults.MaioranaMcFarland

/-- The relation that `g x = f (x + s)` for every input `x`. -/
def HidesShiftOn {Ω : Type} [Add Ω] (f g : Ω → ZMod 2) (s : Ω) : Prop :=
  ∀ x, g x = f (x + s)

/-- The binary hidden-shift promise consisting of bentness of `f` and the shift relation from
`f` to `g`. -/
def HidesShift {n : ℕ} (f g : BVec n → ZMod 2) (s : BVec n) : Prop :=
  Bent f ∧ HidesShiftOn f g s

/-- A function shifted from a bent function under `HidesShift` is itself bent. -/
theorem bent_of_hidesShift {n : ℕ} {f g : BVec n → ZMod 2} {s : BVec n}
    (h : HidesShift f g s) : Bent g := by
  have hfun : g = fun x => f ((1 : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec x + s) := by
    funext x
    show g x = f ((1 : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec x + s)
    rw [Matrix.one_mulVec]
    exact h.2 x
  rw [hfun]
  exact (lemma2_affine f 1 (by simp) s h.1).1

/-- The hidden-shift relation on pairs of binary vectors together with a Maiorana-McFarland
representation of the unshifted function. -/
def MMShift {m : ℕ} (f g : (BVec m × BVec m) → ZMod 2) (s : BVec m × BVec m) : Prop :=
  HidesShiftOn f g s ∧
    ∃ (π : Equiv.Perm (BVec m)) (h : BVec m → ZMod 2), f = mm π h

/-- A bent function cannot have two distinct shifts producing the same shifted function. -/
theorem hidesShift_unique {n : ℕ} {f g : BVec n → ZMod 2} {s s' : BVec n}
    (hf : Bent f) (hs : HidesShiftOn f g s) (hs' : HidesShiftOn f g s') :
    s = s' := by
  by_contra hne
  have hne0 : s + s' ≠ 0 := fun h => hne ((add_eq_zero_iff_eq_bvec s s').mp h)

  have hper : ∀ x : BVec n, f (x + (s + s')) = f x := by
    intro x
    have h1 := hs' (x + s')
    have h2 := hs (x + s')
    have e1 : (x + s') + s' = x := by
      rw [add_assoc, BentCore.add_self_bvec, add_zero]
    have e2 : (x + s') + s = x + (s + s') := by abel
    rw [e1] at h1
    rw [e2] at h2
    exact h2.symm.trans h1

  have hone : ∀ x : BVec n, eps (f x + f (x + (s + s'))) = 1 := by
    intro x
    rw [hper x, add_self_zmod2, eps_zero]
  have hac := bent_autocorrelation hf (s + s')
  rw [if_neg hne0] at hac
  have hsum : (∑ x : BVec n, eps (f x + f (x + (s + s')))) = (2 : ℤ) ^ n := by
    rw [show (∑ x : BVec n, eps (f x + f (x + (s + s'))))
        = ∑ _x : BVec n, (1 : ℤ) from
      Finset.sum_congr rfl (fun x _ => hone x)]
    simp [Finset.sum_const]
  rw [hsum] at hac
  exact pow_ne_zero n (by norm_num : (2 : ℤ) ≠ 0) hac

/-- The Walsh spectrum of `g` with its signs corrected by the Boolean function `ft`. -/
def phaseVec {n : ℕ} (ft g : BVec n → ZMod 2) (w : BVec n) : ℤ :=
  eps (ft w) * walsh g w

/-- The unnormalized Walsh sum of the corrected spectrum `phaseVec` at `u`. -/
def finalAmp {n : ℕ} (ft g : BVec n → ZMod 2) (u : BVec n) : ℤ :=
  ∑ w : BVec n, eps (dot w u) * phaseVec ft g w

/-- Under the dual and hidden-shift promises in even dimension, the final amplitude is zero away
from `s` and equals `2 ^ (n / 2) * 2 ^ n` at `s`. -/
theorem finalAmp_eq {n : ℕ} {f g ft : BVec n → ZMod 2} {s : BVec n}
    (hd : IsDual f ft) (hg : HidesShiftOn f g s) (_hn : Even n) (u : BVec n) :
    finalAmp ft g u = (2 : ℤ) ^ (n / 2) * (if u = s then (2 : ℤ) ^ n else 0) := by
  have hg' : g = fun x => f (x + s) := funext hg
  have hphase : ∀ w : BVec n,
      phaseVec ft g w = (2 : ℤ) ^ (n / 2) * eps (dot s w) := by
    intro w
    unfold phaseVec
    rw [hg', walsh_shift, hd w]
    have he : eps (ft w) * eps (ft w) = 1 := by
      rw [← pow_two]
      exact eps_sq (ft w)
    rw [show eps (ft w) * (eps (dot s w) * (2 ^ (n / 2) * eps (ft w)))
        = 2 ^ (n / 2) * (eps (ft w) * eps (ft w)) * eps (dot s w) from by ring]
    rw [he]
    ring
  calc finalAmp ft g u
      = ∑ w : BVec n, eps (dot w u) * ((2 : ℤ) ^ (n / 2) * eps (dot s w)) := by
        unfold finalAmp
        exact Finset.sum_congr rfl (fun w _ => by rw [hphase w])
    _ = (2 : ℤ) ^ (n / 2) * ∑ w : BVec n, eps (dot w u) * eps (dot s w) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun w _ => by ring)
    _ = (2 : ℤ) ^ (n / 2) * ∑ w : BVec n, eps (dot w (u + s)) := by
        congr 1
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [show dot w (u + s) = dot w u + dot s w from by
          rw [dot_add_dot]
          rw [show dot w s = dot s w from by
            simp only [dot]
            rw [dotProduct_comm]]]
        rw [eps_add]
    _ = (2 : ℤ) ^ (n / 2) * (if u + s = 0 then (2 : ℤ) ^ n else 0) := by
        rw [sum_w_eps_dot]
    _ = (2 : ℤ) ^ (n / 2) * (if u = s then (2 : ℤ) ^ n else 0) := by
        congr 1
        by_cases h : u = s
        · rw [if_pos h]
          rw [if_pos (by simpa [h] using BentCore.add_self_bvec s)]
        · rw [if_neg h, if_neg]
          intro h0
          exact h ((add_eq_zero_iff_eq_bvec u s).mp h0)

/-- Every bent Boolean function in even dimension possesses a Boolean dual in the sense of
`IsDual`. -/
theorem exists_isDual_of_bent {n : ℕ} {f : BVec n → ZMod 2}
    (hf : Bent f) (hn : Even n) : ∃ ft : BVec n → ZMod 2, IsDual f ft := by
  classical
  have hpm : ∀ w : BVec n, walsh f w = (2 : ℤ) ^ (n / 2)
      ∨ walsh f w = -((2 : ℤ) ^ (n / 2)) := by
    intro w
    have hs : walsh f w ^ 2 = ((2 : ℤ) ^ (n / 2)) ^ 2 := by
      rw [show ((2 : ℤ) ^ (n / 2)) ^ 2 = (2 : ℤ) ^ n from by
        rw [pow_two]
        exact pow_half_mul hn]
      exact hf w
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hs
  refine ⟨fun w => if walsh f w = (2 : ℤ) ^ (n / 2) then 0 else 1, ?_⟩
  intro w
  rcases hpm w with h | h
  · show walsh f w
      = (2 : ℤ) ^ (n / 2) * eps (if walsh f w = (2 : ℤ) ^ (n / 2) then 0 else 1)
    rw [if_pos h, eps_zero, mul_one]
    exact h
  · have hne : walsh f w ≠ (2 : ℤ) ^ (n / 2) := by
      intro heq
      have ha : (2 : ℤ) ^ (n / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [h] at heq
      have hzero : (2 : ℤ) ^ (n / 2) = 0 := by linarith
      exact ha hzero
    show walsh f w
      = (2 : ℤ) ^ (n / 2) * eps (if walsh f w = (2 : ℤ) ^ (n / 2) then 0 else 1)
    rw [if_neg hne, eps_one, h]
    ring

/-- Chooses an input with nonzero final amplitude, returning zero if no such input exists. -/
def decode {n : ℕ} (ft g : BVec n → ZMod 2) : BVec n :=
  if h : ∃ u : BVec n, finalAmp ft g u ≠ 0 then Classical.choose h else 0

/-- In even dimension, decoding the spectrum corrected by a dual of `f` recovers any shift from
`f` to `g`. -/
theorem decode_eq {n : ℕ} {f g ft : BVec n → ZMod 2} {s : BVec n}
    (hd : IsDual f ft) (hg : HidesShiftOn f g s) (hn : Even n) :
    decode ft g = s := by
  classical
  have hpos : finalAmp ft g s ≠ 0 := by
    rw [finalAmp_eq hd hg hn s, if_pos rfl]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
  have hex : ∃ u : BVec n, finalAmp ft g u ≠ 0 := ⟨s, hpos⟩
  unfold decode
  rw [dif_pos hex]
  have hprop : ∀ u : BVec n, finalAmp ft g u ≠ 0 → u = s := by
    intro u hu
    by_contra hne
    exact hu (by rw [finalAmp_eq hd hg hn u, if_neg hne, mul_zero])
  exact hprop _ (Classical.choose_spec hex)

/-- The cross-correlation of translated sign vectors of a bent function and its shift is `2 ^ n`
when the translations differ by `s` and zero otherwise. -/
theorem bent_gram_shift {n : ℕ} {f g : BVec n → ZMod 2} {s : BVec n}
    (hf : Bent f) (hg : HidesShiftOn f g s) (x x' : BVec n) :
    (∑ y : BVec n, eps (f (x + y) + g (x' + y)))
      = if x = x' + s then (2 : ℤ) ^ n else 0 := by
  rw [show (∑ y : BVec n, eps (f (x + y) + g (x' + y)))
      = ∑ y : BVec n, eps (f (x + y) + f (x' + y + s)) from
    Finset.sum_congr rfl (fun y _ => by rw [hg (x' + y)])]
  rw [show (∑ y : BVec n, eps (f (x + y) + f (x' + y + s)))
      = ∑ y : BVec n, eps (f (x + y) + f ((x' + s) + y)) from
    Finset.sum_congr rfl (fun y _ => by
      congr 2
      abel)]
  exact bent_gram hf x (x' + s)

/-- The dot product with a vector supported at coordinate `i` is `v i * c`. -/
lemma dot_single_left {n : ℕ} (i : Fin n) (c : ZMod 2) (v : BVec n) :
    dot (Pi.single i c) v = v i * c := by
  simp only [dot]
  rw [dotProduct_comm]
  exact dot_single v i c

/-- The binary linear constraint `dot a.1 s + a.2 = 0` on the shift `s`. -/
def orth {n : ℕ} (a : BVec n × ZMod 2) (s : BVec n) : Prop :=
  dot a.1 s + a.2 = 0

/-- Two shifts satisfying exactly the same binary orthogonality constraints are equal. -/
theorem orth_ext {n : ℕ} (s s' : BVec n)
    (h : ∀ a : BVec n × ZMod 2, orth a s ↔ orth a s') : s = s' := by
  funext i
  have hsingle : orth (Pi.single i (1 : ZMod 2), s i) s := by
    unfold orth
    rw [dot_single_left, mul_one, add_self_zmod2]
  have hzero : dot (Pi.single i (1 : ZMod 2)) s' + s i = 0 := (h _).mp hsingle
  rw [dot_single_left] at hzero
  simp only [mul_one] at hzero

  have hcalc : s' i = s i := by
    calc s' i = s' i + 0 := by rw [add_zero]
      _ = s' i + (s i + s i) := by rw [add_self_zmod2]
      _ = (s' i + s i) + s i := by abel
      _ = 0 + s i := by rw [hzero]
      _ = s i := by rw [zero_add]
  exact hcalc.symm

/-- The dot-product Boolean function on a pair of binary vectors. -/
def mmZero {m : ℕ} (p : BVec m × BVec m) : ZMod 2 := dot p.1 p.2

/-- The dot-product Boolean function with its second input translated by `s`. -/
def mmShiftFun {m : ℕ} (s : BVec m) (p : BVec m × BVec m) : ZMod 2 :=
  dot p.1 (p.2 + s)

/-- The function `mmShiftFun s` satisfies the Maiorana-McFarland shift promise for `mmZero` with
shift `(0, s)`. -/
theorem mmZero_isShift {m : ℕ} (s : BVec m) :
    MMShift (mmZero (m := m)) (mmShiftFun s) (0, s) := by
  constructor
  · intro p
    rcases p with ⟨x, y⟩
    simp [mmShiftFun, mmZero, add_comm]
  · refine ⟨Equiv.refl (BVec m), 0, ?_⟩
    funext p
    rcases p with ⟨x, y⟩
    simp [mmZero, mm]

/-- Any tuple of fewer than `m` binary vectors of length `m` possesses a nonzero common
orthogonal vector. -/
lemma exists_orthogonal_nonzero {m k : ℕ} (hk : k < m)
    (x : Fin k → BVec m) :
    ∃ δ : BVec m, δ ≠ 0 ∧ ∀ i, dot (x i) δ = 0 := by
  let L : BVec m →ₗ[ZMod 2] (Fin k → ZMod 2) :=
    LinearMap.pi (fun i => (dotProductBilin (ZMod 2) (ZMod 2)) (x i))
  have hnotinj : ¬ Function.Injective L := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at hle
    omega
  have hker : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    exact hnotinj (LinearMap.ker_eq_bot.mp hbot)
  obtain ⟨v, hvker, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨v, hvne, ?_⟩
  intro i
  have hv : L v = 0 := hvker
  have hi : L v i = 0 := by rw [hv]; rfl
  simpa [L, dot, dotProductBilin] using hi

/-- There are `m` fixed query points whose values distinguish all shifts of the dot-product
family. -/
theorem mmZero_upper {m : ℕ} :
    ∃ pts : Fin m → BVec m × BVec m,
      ∀ s s' : BVec m,
        (∀ i, mmShiftFun s (pts i) = mmShiftFun s' (pts i)) → s = s' := by
  refine ⟨fun i => (Pi.single i (1 : ZMod 2), 0), ?_⟩
  intro s s' h
  funext i
  have hi := h i
  have e1 : mmShiftFun s (Pi.single i (1 : ZMod 2), 0) = s i := by
    simp [mmShiftFun, zero_add]
  have e2 : mmShiftFun s' (Pi.single i (1 : ZMod 2), 0) = s' i := by
    simp [mmShiftFun, zero_add]
  rw [e1, e2] at hi
  exact hi

/-- For any fixed set of fewer than `m` query points, two distinct shifts of the dot-product
family give identical answers at every point. -/
theorem mmZero_lower {m k : ℕ} (hk : k < m)
    (pts : Fin k → BVec m × BVec m) :
    ∃ s s' : BVec m, s ≠ s' ∧
      ∀ i, mmShiftFun s (pts i) = mmShiftFun s' (pts i) := by
  obtain ⟨δ, hδne, hδorth⟩ := exists_orthogonal_nonzero hk (fun i => (pts i).1)
  refine ⟨0, δ, ?_, ?_⟩
  · intro h
    exact hδne h.symm
  · intro i
    rcases hq : pts i with ⟨x, y⟩
    have horth : dot x δ = 0 := by simpa [hq] using hδorth i
    simp only [mmShiftFun]
    rw [add_zero, dot_add_dot, horth, add_zero]

end Qatlib.Papers.NonlinBool08.MainResults.HiddenShift
