/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.Pairing

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Finset

variable {n : ℕ}

macro "zring" : tactic => `(tactic| (ring_nf <;> reduce_mod_char))

def mu (g h : Wreath n) : ZMod 2 :=
  ((∑ i, g.x i * h.x i) + (∑ i, g.y i * h.y i))
  + g.a * h.a
  + (g.a + h.a) * (((∑ i, g.x i * h.x i) + (∑ i, g.y i * h.y i)) + g.a * h.a
      + ((∑ i, g.x i * h.y i) + (∑ i, h.x i * g.y i)))

lemma mu_zero_zero (g h : Wreath n) (hg : g.a = 0) (hh : h.a = 0) :
    mu g h = (∑ i, g.x i * h.x i) + (∑ i, g.y i * h.y i) := by
  simp only [mu, hg, hh]
  zring

lemma mu_zero_one (g h : Wreath n) (hg : g.a = 0) (hh : h.a = 1) :
    mu g h = (∑ i, g.x i * h.y i) + (∑ i, h.x i * g.y i) := by
  simp only [mu, hg, hh]
  zring

lemma mu_one_zero (g h : Wreath n) (hg : g.a = 1) (hh : h.a = 0) :
    mu g h = (∑ i, g.x i * h.y i) + (∑ i, h.x i * g.y i) := by
  simp only [mu, hg, hh]
  zring

lemma mu_one_one (g h : Wreath n) (hg : g.a = 1) (hh : h.a = 1) :
    mu g h = (∑ i, g.x i * h.x i) + (∑ i, g.y i * h.y i) + 1 := by
  simp only [mu, hg, hh]
  zring

def perp (U : Set (Wreath n)) : Set (Wreath n) := {g | ∀ u ∈ U, mu g u = 0}

@[simp] lemma mem_perp {U : Set (Wreath n)} {g : Wreath n} :
    g ∈ perp U ↔ ∀ u ∈ U, mu g u = 0 := Iff.rfl

def perpSub (U : Subgroup (Wreath n)) : Set (Wreath n) := perp (U : Set (Wreath n))

lemma mem_perpSub {U : Subgroup (Wreath n)} {g : Wreath n} :
    g ∈ perpSub U ↔ ∀ u ∈ U, mu g u = 0 := Iff.rfl

lemma mu_swapFun_swapFun (g h : Wreath n) : mu (swapFun g) (swapFun h) = mu g h := by
  simp only [mu, swapFun_x, swapFun_y, swapFun_a]
  rw [show (∑ i, g.y i * h.x i) = ∑ i, h.x i * g.y i from
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
  rw [show (∑ i, g.x i * h.y i) = ∑ i, h.y i * g.x i from
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
  rw [show (∑ i, h.y i * g.x i) = ∑ i, g.x i * h.y i from
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
  zring

end Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
