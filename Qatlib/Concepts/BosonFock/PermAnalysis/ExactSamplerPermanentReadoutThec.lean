/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.BosonFock.PermAnalysis.ExactSamplerPermanentReadoutStat
public import Mathlib.Data.Fintype.Perm

@[expose] public section
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib

namespace Qatlib.Concepts.BosonFock.PermAnalysis

open Qatlib

open scoped Matrix Nat

/-- Flat-mapping a list to empty lists yields the empty list. -/
private theorem flatMap_nil {α β : Type*} (l : List α) :
    l.flatMap (fun _ => ([] : List β)) = [] := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- The boson row list for unit occupation of the first `k` modes is the list of those modes in
increasing order. -/
private theorem bosonRows_indicator {m k : ℕ} (hk : k ≤ m) :
    bosonRows (fun i : Fin m => if (i : ℕ) < k then 1 else 0)
      = (List.finRange k).map (fun i => (Fin.castLE hk i : Fin m)) := by
  induction m generalizing k with
  | zero =>
      have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      rw [bosonRows, List.flatMap_congr fun i _ => by
        rw [show (if (i : ℕ) < 0 then (1 : ℕ) else 0) = 0 from ite_eq_right (by omega),
          List.replicate_zero], flatMap_nil]
      simp
  | succ m ih =>
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        rw [bosonRows, List.flatMap_congr fun i _ => by
          rw [ite_eq_right (by omega : ¬((i : ℕ) < 0)), List.replicate_zero], flatMap_nil]
        simp
      · obtain ⟨k', hk'eq⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        subst hk'eq
        have hk2 : k' ≤ m := by omega
        have hind : ∀ j : Fin m, (if ((Fin.succ j : Fin (m + 1)) : ℕ) < k' + 1 then 1 else 0)
            = (if (j : ℕ) < k' then 1 else 0) := by
          intro j
          have hsucc : ((Fin.succ j : Fin (m + 1)) : ℕ) = (j : ℕ) + 1 := rfl
          rw [hsucc]
          by_cases h : (j : ℕ) + 1 < k' + 1
          · rw [ite_eq_left h, ite_eq_left (by omega : (j : ℕ) < k')]
          · rw [ite_eq_right h, ite_eq_right (by omega : ¬((j : ℕ) < k'))]
        have hfun1 : (fun j : Fin m =>
              List.replicate (if ((Fin.succ j : Fin (m + 1)) : ℕ) < k' + 1 then 1 else 0)
                (Fin.succ j))
            = (fun j : Fin m => List.replicate (if (j : ℕ) < k' then 1 else 0) (Fin.succ j)) := by
          funext j; rw [hind j]
        have hfun2 : (fun j : Fin m => List.replicate (if (j : ℕ) < k' then 1 else 0) (Fin.succ j))
            = (fun j : Fin m =>
              List.map Fin.succ (List.replicate (if (j : ℕ) < k' then 1 else 0) j)) := by
          funext j; rw [List.map_replicate]
        rw [bosonRows, List.finRange_succ, List.flatMap_cons, List.flatMap_map, hfun1,
          hfun2, ← List.map_flatMap,
          show (List.finRange m).flatMap
              (fun i : Fin m => List.replicate (if (i : ℕ) < k' then 1 else 0) i)
            = bosonRows (fun i : Fin m => if (i : ℕ) < k' then 1 else 0) from rfl,
          ih hk2, List.map_map, List.finRange_succ, List.map_cons, Fin.val_zero,
          ite_eq_left (Nat.zero_lt_succ k'), List.replicate_one, List.cons_append]
        have hcast0 : (Fin.castLE hk (0 : Fin (k' + 1)) : Fin (m + 1)) = 0 := by
          ext; simp
        have hcastS : ∀ j : Fin k',
            (Fin.castLE hk (Fin.succ j) : Fin (m + 1)) = Fin.succ (Fin.castLE hk2 j) := by
          intro j; ext; simp [Fin.val_succ]
        rw [hcast0, List.map_map]
        rfl

/-- For an exact sampler of the embedded isometry, the probability of `bosonOneState` equals the
scaled squared modulus of the permanent. -/
theorem exactSamplerPermanentReadout : ExactSamplerPermanentReadout := by
  unfold ExactSamplerPermanentReadout
  intro n X ε _hε _hc W _hWW htop L O hO
  rw [hO (bosonOneState n)]
  unfold bosonWeight
  have hlen : (bosonRows (fun i : Fin (2 * n) => ((bosonOneState n).1 i : ℕ))).length = n := by
    rw [bosonRows_length]
    exact (bosonOneState n).2
  have hf : (fun i : Fin (2 * n) => ((bosonOneState n).1 i : ℕ))
      = fun i : Fin (2 * n) => if (i : ℕ) < n then 1 else 0 := by
    funext i
    by_cases h : (i : ℕ) < n <;> simp [bosonOneState, oneStateFun, h]
  have hrow : bosonRowMatrix W (bosonOneState n) = (ε : ℂ) • X := by
    ext p q
    have hPp : (p : ℕ) < (bosonRows (fun i : Fin (2 * n) => ((bosonOneState n).1 i : ℕ))).length := by
      rw [hlen]; exact p.isLt

    have hget : ∀ l : List (Fin (2 * n)),
        l = (List.finRange n).map (fun i => (Fin.castLE (by omega : n ≤ 2 * n) i : Fin (2 * n))) →
        ∀ h : (p : ℕ) < l.length,
        l.get ⟨(p : ℕ), h⟩ = (Fin.castLE (by omega : n ≤ 2 * n) p : Fin (2 * n)) := by
      intro l hl h
      subst hl
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
      ext
      simp
    show W ((bosonRows (fun i : Fin (2 * n) => ((bosonOneState n).1 i : ℕ))).get
        ⟨(p : ℕ), hPp⟩) q = ((ε : ℂ) • X) p q
    rw [hget _ ((congrArg bosonRows hf).trans
      (bosonRows_indicator (by omega : n ≤ 2 * n))) hPp, htop p q]
    simp only [Matrix.smul_apply, smul_eq_mul]

  have hden : (∏ i : Fin (2 * n), ((bosonOneState n).1 i : ℕ)!) = 1 := by
    have hfac : ∀ i : Fin (2 * n), ((bosonOneState n).1 i : ℕ)! = 1 := by
      intro i
      by_cases h : (i : ℕ) < n
      · have h1 : ((bosonOneState n).1 i : ℕ) = 1 := by simp [bosonOneState, oneStateFun, h]
        rw [h1]; simp
      · have h0 : ((bosonOneState n).1 i : ℕ) = 0 := by simp [bosonOneState, oneStateFun, h]
        rw [h0]; simp
    rw [Finset.prod_congr rfl (fun i _ => hfac i)]
    exact Finset.prod_const_one
  rw [hrow, Matrix.permanent_smul, Fintype.card_fin, hden, Nat.cast_one, div_one,
    Complex.normSq_mul]
  have hεpow : Complex.normSq ((ε : ℂ) ^ n) = (Complex.normSq ((ε : ℂ))) ^ n :=
    map_pow Complex.normSq _ n
  have hεval : Complex.normSq ((ε : ℂ)) = ε * ε := by
    simp [Complex.normSq, Complex.ofReal_re, Complex.ofReal_im]
  rw [hεpow, hεval, show ε * ε = ε ^ 2 by ring]

end Qatlib.Concepts.BosonFock.PermAnalysis
