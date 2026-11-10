/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.FiniteSelection
import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Addition
import Mathlib.Algebra.BigOperators.Fin
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.RationalNormalization

open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
open FiniteSelection

def sumBits : List ℚ → ℚ × ℕ
  | [] => (0, 0)
  | a :: as =>
    let tail := sumBits as
    let step := binomialRatAddBits a tail.1
    (step.1, step.2 + tail.2)

theorem sum_value (as : List ℚ) : (sumBits as).1 = as.sum := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    change (binomialRatAddBits a (sumBits as).1).1 = a + as.sum
    rw [(binomial_rat_add_bits a (sumBits as).1).1, ih]

theorem add_cap_mono {a b : ℕ} (h : a ≤ b) :
    binomialRatAddGateCap a ≤ binomialRatAddGateCap b := by
  unfold binomialRatAddGateCap
  gcongr

theorem sum_bounds (as : List ℚ) :
    width (sumBits as).1 ≤ 1 + as.length + (as.map width).sum ∧
      (sumBits as).2 ≤ as.length *
        binomialRatAddGateCap (1 + as.length + (as.map width).sum) := by
  induction as with
  | nil => norm_num [sumBits, width, binomialRatHeight]
  | cons a as ih =>
    have h := binomial_rat_add_bits a (sumBits as).1
    have hw : 1 + width a + width (sumBits as).1 ≤
        1 + (a :: as).length + ((a :: as).map width).sum := by
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
    have ht : 1 + as.length + (as.map width).sum ≤
        1 + (a :: as).length + ((a :: as).map width).sum := by
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
    change width (binomialRatAddBits a (sumBits as).1).1 ≤ _ ∧
      (binomialRatAddBits a (sumBits as).1).2 + (sumBits as).2 ≤ _
    refine ⟨h.2.1.trans hw, ?_⟩
    have hs := h.2.2.trans (add_cap_mono hw)
    have hp := ih.2.trans (Nat.mul_le_mul_left as.length (add_cap_mono ht))
    simpa only [List.length_cons, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hs hp

structure Result (m : ℕ) where
  values : Vector ℚ m
  gates : ℕ
  deriving Repr

def divide {m : ℕ} (a : Vector ℚ m) (z : ℚ) (sumGates : ℕ) : Result m :=
  let rows := Vector.ofFn fun i : Fin m => binomialRatDivBits a[i.val] z
  ⟨rows.map Prod.fst, sumGates + (rows.toList.map Prod.snd).sum⟩

theorem divide_value {m : ℕ} (a : Vector ℚ m) (z : ℚ) (fee : ℕ) (i : Fin m) :
    (divide a z fee).values[i.val] = a[i.val] / z := by
  simp only [divide, Vector.getElem_map, Vector.getElem_ofFn]
  exact (binomial_rat_div_bits a[i.val] z).1

def normalize {m : ℕ} (a : Vector ℚ m) : Option (Result m) :=
  let total := sumBits (List.ofFn fun i : Fin m => a[i.val])
  if total.1 = 0 then none else some (divide a total.1 total.2)

def normalizeFamily {c m : ℕ} (a : Vector (Vector ℚ m) c) : Option (Vector (Result m) c) :=
  let totals := a.map fun col => sumBits (List.ofFn fun i : Fin m => col[i.val])
  if ∀ j : Fin c, totals[j.val].1 ≠ 0 then
    some (Vector.ofFn fun j : Fin c => divide a[j.val] totals[j.val].1 totals[j.val].2)
  else none

theorem normalizeFamily_column {c m : ℕ} (a : Vector (Vector ℚ m) c)
    (r : Vector (Result m) c) (hr : normalizeFamily a = some r) (j : Fin c) :
    normalize a[j.val] = some r[j.val] := by
  dsimp only [normalizeFamily] at hr
  split_ifs at hr with hz
  have he := Option.some.inj hr
  subst r
  have hj := hz j
  simp only [Vector.getElem_map] at hj
  simp only [Vector.getElem_ofFn, Vector.getElem_map]
  simp only [normalize, if_neg hj]

theorem normalize_none_iff {m : ℕ} (a : Vector ℚ m) :
    normalize a = none ↔ (∑ i : Fin m, a[i.val]) = 0 := by
  simp [normalize, sum_value, List.sum_ofFn]

theorem normalize_value {m : ℕ} (a : Vector ℚ m) (r : Result m)
    (hr : normalize a = some r) (i : Fin m) :
    r.values[i.val] = a[i.val] / (∑ j : Fin m, a[j.val]) := by
  dsimp only [normalize] at hr
  split_ifs at hr with hz
  have he := Option.some.inj hr
  subst r
  rw [divide_value, sum_value, List.sum_ofFn]

theorem divide_bounds {m : ℕ} (a : Vector ℚ m) (z : ℚ) (fee B S : ℕ)
    (ha : ∀ i : Fin m, width a[i.val] ≤ B) (hz : width z ≤ S) :
    (∀ i : Fin m, width (divide a z fee).values[i.val] ≤ B + S) ∧
      (divide a z fee).gates ≤ fee + m * binomialRatOpGateCap (B + S) := by
  have hh (i : Fin m) : width a[i.val] + width z ≤ B + S := Nat.add_le_add (ha i) hz
  constructor
  · intro i
    have h := (binomial_rat_div_bits a[i.val] z).2.1
    simpa only [divide, Vector.getElem_map, Vector.getElem_ofFn] using! h.trans (hh i)
  · change fee + ((Vector.ofFn fun i : Fin m => binomialRatDivBits a[i.val] z).toList.map Prod.snd).sum ≤ _
    rw [Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn]
    apply Nat.add_le_add_left
    calc
      _ ≤ ∑ _i : Fin m, binomialRatOpGateCap (B + S) :=
        Finset.sum_le_sum fun i _ => (binomial_rat_div_bits a[i.val] z).2.2.trans
          (product_cap_mono (hh i))
      _ = _ := by simp

theorem normalize_bounds {m : ℕ} (a : Vector ℚ m) (r : Result m)
    (hr : normalize a = some r) (B : ℕ) (ha : ∀ i : Fin m, width a[i.val] ≤ B) :
    (∀ i : Fin m, width r.values[i.val] ≤ B + (1 + m * (B + 1))) ∧
      r.gates ≤ m * (binomialRatAddGateCap (1 + m * (B + 1)) +
        binomialRatOpGateCap (B + (1 + m * (B + 1)))) := by
  let as := List.ofFn fun i : Fin m => a[i.val]
  have hs : (as.map width).sum ≤ m * B := by
    dsimp only [as]
    rw [List.map_ofFn, List.sum_ofFn]
    calc
      _ ≤ ∑ _i : Fin m, B := Finset.sum_le_sum fun i _ => ha i
      _ = _ := by simp
  have hw : 1 + as.length + (as.map width).sum ≤ 1 + m * (B + 1) := by
    simp only [as, List.length_ofFn, Nat.mul_add, Nat.mul_one] at hs ⊢
    omega
  have hsum := sum_bounds as
  have hg := hsum.2.trans (Nat.mul_le_mul_left _ (add_cap_mono hw))
  have hd := divide_bounds a (sumBits as).1 (sumBits as).2 B (1 + m * (B + 1)) ha
    (hsum.1.trans hw)
  dsimp only [normalize] at hr
  split_ifs at hr with hz
  have he := Option.some.inj hr
  subst r
  refine ⟨hd.1, ?_⟩
  have h := hd.2.trans (Nat.add_le_add_right hg _)
  simpa only [as, List.length_ofFn, Nat.mul_add] using h

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.RationalNormalization
