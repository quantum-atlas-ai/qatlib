/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.ReceivedStatistics.StreamingCollision.Data
import Qatlib.Concepts.ShadowModels.UStatBackend.ReceivedStatistics.RationalPairMedian
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision
open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
open scoped BigOperators

@[simp] theorem step_pairs {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step s r).pairs = s.pairs + s.bank[r.1]*r.2 := by
  simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step]

theorem step_bank {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m) (i : Fin m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step s r).bank[i] = s.bank[i] + (if r.1=i then r.2 else 0) := by
  by_cases h : r.1=i
  · subst i
    simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step]
  · have hv : (r.1 : ℕ) ≠ (i : ℕ) := fun he => h (Fin.ext he)
    simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step, h, hv]

def mass {m : ℕ} (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m)) (i : Fin m) : ℚ :=
  (xs.map (fun r => if r.1=i then r.2 else 0)).sum

theorem scan_bank {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m)) (i : Fin m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan s xs).bank[i] = s.bank[i] + Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.mass xs i := by
  induction xs generalizing s with
  | nil => simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.mass]
  | cons r xs ih =>
    change (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step s r) xs).bank[i] = _
    rw [ih, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step_bank]
    simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.mass, List.map_cons,
        List.sum_cons]
    ring

@[simp] theorem scan_samples {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m)) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan s xs).samples = s.samples+xs.length := by
  induction xs generalizing s with
  | nil => simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan]
  | cons r xs ih =>
    change (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step s r) xs).samples = _
    rw [ih]
    change s.samples+1+xs.length = s.samples+(xs.length+1)
    omega

theorem scan_counts {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m)) (e : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Event) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan s xs).counts e = s.counts e + xs.length*Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.stepCounts e := by
  induction xs generalizing s with
  | nil => simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan]
  | cons r xs ih =>
    change (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step s r) xs).counts e = _
    rw [ih]
    simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step, Pi.add_apply,
        List.length_cons]
    ring

theorem scan_snoc_pairs {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m)) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan s (xs++[r])).pairs = (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan s xs).pairs + (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan s xs).bank[r.1]*r.2 := by
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan, List.foldl_append,
      List.foldl_cons, List.foldl_nil, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step_pairs]

theorem scaled_pairs_ofFn {m n : ℕ} (w : Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m) :
    (m : ℚ)*(Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initial m) (List.ofFn w)).pairs =
      ((Qatlib.Concepts.ShadowModels.UStatBackend.pairIndexList n).map (fun p => Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.kernel (w p.1) (w p.2))).sum := by
  induction n with
  | zero => simp [Qatlib.Concepts.ShadowModels.UStatBackend.pairIndexList, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initial]
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append,
        Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan_snoc_pairs, mul_add, ih]
    simp only [Qatlib.Concepts.ShadowModels.UStatBackend.pairIndexList, List.map_append, List.sum_append, List.map_map,
      List.map_ofFn, List.sum_ofFn]
    congr 1
    rw [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan_bank]
    simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initial, Fin.getElem_fin, Vector.getElem_replicate, zero_add, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.mass,
      List.map_ofFn, List.sum_ofFn, Function.comp_def]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (w i.castSucc).1 = (w (Fin.last n)).1 <;>
      simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.kernel, h, mul_assoc]

@[simp] theorem pairCount_eq_choose (n : ℕ) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.pairCount n = n.choose 2 :=
  (Nat.choose_two_right n).symm

private theorem div_value (a b : ℚ) : (Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.binomialRatDivBits a b).1 = a/b :=
  (Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.binomial_rat_div_bits a b).1

@[simp] theorem finish_value {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finish s).value = ((m : ℚ)*s.pairs)/(Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.pairCount s.samples : ℚ) := by
  simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finish, div_value]

theorem run_value {m n : ℕ} (w : Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.run (List.ofFn w)).value = (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.kernel w).1 := by
  change (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finish (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initial m) (List.ofFn w))).value = _
  have hn : (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initial m) (List.ofFn w)).samples = n := by
    simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initial]
  rw [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finish_value, hn,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.pairCount_eq_choose, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scaled_pairs_ofFn, Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate_spec]

theorem run_counts {m : ℕ} (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m)) (e : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Event) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.run xs).counts e = Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initialCounts m e + xs.length*Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.stepCounts e + Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finishCounts e := by
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.run,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finish, Pi.add_apply, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan_counts, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initial]

theorem weighted_call_counts {m : ℕ} (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m)) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.run xs).counts .records = xs.length ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.run xs).counts .bankReads = xs.length ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.run xs).counts .bankWrites = xs.length ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.run xs).counts .rationalAdds = 2*xs.length ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.run xs).counts .rationalMuls = xs.length+1 ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.run xs).counts .rationalDivs = 1 ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.run xs).counts .initialSlots = m := by
  simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.run_counts,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initialCounts, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.stepCounts, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finishCounts, Nat.mul_comm]

end Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision
