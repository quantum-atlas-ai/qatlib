/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
import Qatlib.Concepts.WalkFind.UniqueCollision.NativeSingleSolutionQuan
import Mathlib.Tactic.FieldSimp
import Qatlib.Concepts.WalkFind.UniqueCollision.GeneralQueryMemory

/-!
# Native parameter bounds and full-memory search

This module bounds stage memory and the contraction of retained prefixes. It derives a nearby
even-power prime-power condition from `Algorithm3NativeContract`, proves a spacing obstruction
for powers of four, and constructs a full-memory search tree with explicit query and qubit
bounds.

The mathematical background is developed in [Ambainis2007ElementDistinctness].

## Main statements

* `algorithm3_prefix_ratio`: gives a uniform contraction ratio for a nearby enlarged domain.
* `algorithm3Native_full_memory`: constructs the full-memory initial-frame search tree.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkFind.UniqueCollision

open Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkFind.SearchAlgorithm
open scoped Classical

/-- If `k < n`, the stage-memory parameter lies between `k` and `n - 1`. -/
theorem stageMemory_bounds (k N r n : ℕ) (hk : k < n) :
    k ≤ stageMemory k N r n ∧ stageMemory k N r n < n := by
  unfold stageMemory
  constructor
  · exact le_min (by omega) (le_max_left _ _)
  · exact lt_of_le_of_lt (min_le_left _ _) (by omega)

/-- The stage-memory parameter is at most `k + r * n / N + 1` after coercion to the reals. -/
theorem stageMemory_upper (k N r n : ℕ) :
    (stageMemory k N r n : ℝ) ≤ (k : ℝ)+(r : ℝ)*n/N+1 := by
  have hle : stageMemory k N r n ≤ max k (Nat.ceil ((r : ℝ)*n/N)) := min_le_right _ _
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (r : ℝ)*n/N by positivity)
  have hnon : 0 ≤ (r : ℝ)*n/N := by positivity
  have hh : ((max k (Nat.ceil ((r : ℝ)*n/N))) : ℝ) ≤ (k : ℝ)+(r : ℝ)*n/N+1 := by
    apply max_le
    · linarith
    · linarith
  exact le_trans (by exact_mod_cast hle) hh

/-- For `k ≥ 2` and `n ≥ 8 * k^2`, the retained prefix of a sufficiently nearby enlarged domain
has size strictly below `n`. -/
theorem algorithm3_prefix_contraction (k n q : ℕ) (hk : 2 ≤ k)
    (hn : 8*k*k ≤ n) (hnear : (q : ℝ) ≤ (1+1/(2*(k : ℝ)^2))*n) :
    Nat.ceil ((2*(k : ℝ)/(2*k+1))*q) < n := by
  have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hnR : 8*(k : ℝ)^2 ≤ n := by
    have hh : 8*(k : ℝ)*(k : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have h2k : 0 < 2*(k : ℝ)+1 := by linarith
  have hk2 : 0 < 2*(k : ℝ)^2 := by positivity
  have hn1 : 1 ≤ n := by nlinarith [sq_nonneg (k : ℤ)]
  apply lt_of_le_of_lt (b := n-1) _ (by omega)
  apply Nat.ceil_le.mpr
  have hmul : (2*(k : ℝ)/(2*k+1))*(q : ℝ) ≤
      (2*(k : ℝ)/(2*k+1))*((1+1/(2*(k : ℝ)^2))*n) :=
    mul_le_mul_of_nonneg_left hnear (by positivity)
  have hstrict : (2*(k : ℝ)/(2*k+1))*((1+1/(2*(k : ℝ)^2))*n) ≤ (n : ℝ)-1 := by
    have hk0 : (k : ℝ) ≠ 0 := by linarith
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (show 0 ≤ (k : ℝ)-1 by linarith),
      mul_nonneg (show 0 ≤ (k : ℝ)-2 by linarith) (show 0 ≤ (k : ℝ)^2 by positivity)]
  have hcast : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by
    simpa using! (Nat.cast_sub hn1 : ((n-1 : ℕ) : ℝ) = (n : ℝ)-(1 : ℕ))
  simpa [hcast] using! le_trans hmul hstrict

/-- Under the stated size and nearby-domain bounds, the retained prefix has size at most `(1 - 1
/ (10 * k)) * n`. -/
theorem algorithm3_prefix_ratio (k n q : ℕ) (hk : 2 ≤ k) (hn : 8*k*k ≤ n)
    (hnear : (q : ℝ) ≤ (1+1/(2*(k : ℝ)^2))*n) :
    (Nat.ceil ((2*(k : ℝ)/(2*k+1))*q) : ℝ) ≤ (1-1/(10*(k : ℝ)))*n := by
  have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hnR : 8*(k : ℝ)^2 ≤ n := by
    have hh : 8*(k : ℝ)*(k : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (2*(k : ℝ)/(2*k+1))*(q : ℝ) by positivity)
  have hmul := mul_le_mul_of_nonneg_left hnear
    (show 0 ≤ 2*(k : ℝ)/(2*k+1) by positivity)
  have hmain : (2*(k : ℝ)/(2*k+1))*((1+1/(2*(k : ℝ)^2))*n)+1 ≤
      (1-1/(10*(k : ℝ)))*n := by
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (show 0 ≤ 8*(k : ℝ)-11 by linarith),
      mul_nonneg (show 0 ≤ (k : ℝ) by positivity) (sq_nonneg ((k : ℝ)-2)),
      mul_nonneg (show 0 ≤ (k : ℝ) by positivity) (show 0 ≤ (k : ℝ)-2 by linarith)]
  linarith

/-- The native contract implies that every sufficiently large `N` has a prime power `p^(2 * a)`
between `N` and `(1 + 1 / (2 * k^2)) * N` for each `k ≥ 2`. -/
theorem algorithm3Native_near_primepower (h : Algorithm3NativeContract) (k : ℕ) (hk : 2 ≤ k) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∃ q : ℕ, N ≤ q ∧ (q : ℝ) ≤ (1+1/(2*(k : ℝ)^2))*N ∧
        ∃ p a : ℕ, Nat.Prime p ∧ 0 < a ∧ q = p^(2*a) := by
  obtain ⟨C,p,N0,hC,hp,hp1,hrest⟩ := h k hk
  refine ⟨max N0 (k+2),?_⟩
  intro N hN
  have hNk : k < N := by omega
  obtain ⟨P,hframe,hvalid,_,_,_⟩ := hrest N 1 k (by omega) (by decide) (by omega) (by omega)
  cases P with
  | readAll f A =>
    have he : f.size = N := congrArg Algorithm3Frame.size hframe
    have hle := hvalid.2.1
    omega
  | grover f A =>
    have he : f.size = N := congrArg Algorithm3Frame.size hframe
    have hn1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hh : Real.sqrt N < (N : ℝ) := by
      apply (Real.sqrt_lt (Nat.cast_nonneg N) (by linarith : 0 ≤ (N : ℝ))).mpr
      nlinarith
    have hle : (f.size : ℝ) ≤ Real.sqrt N := hvalid.2.2.1
    rw [he] at hle
    linarith
  | walk f memory call P children =>
    have he : f.size = N := congrArg Algorithm3Frame.size hframe
    exact ⟨P.q,by simpa only [he] using! P.enough,by simpa only [he] using! P.near,P.evenPrimePower⟩

/-- No power of four lies between `2 * 4^a` and `9 / 8` times that value. -/
theorem binaryPrimePower_near_failure (a : ℕ) :
    ¬∃ b : ℕ, 2*4^a ≤ 4^b ∧ (4^b : ℝ) ≤ (9/8 : ℝ)*(2*4^a) := by
  rintro ⟨b,hlo,hhi⟩
  have hp : 0 < (4 : ℕ)^a := by positivity
  by_cases hb : b ≤ a
  · have hpow : (4 : ℕ)^b ≤ 4^a := Nat.pow_le_pow_right (by decide : 0 < 4) hb
    omega
  · have hpow : (4 : ℝ)^(a+1) ≤ 4^b := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega)
    have hpR : 0 < (4 : ℝ)^a := by positivity
    rw [pow_succ] at hpow
    nlinarith

/-- For positive `N` and `k ≤ N`, a full-memory initial-frame search tree satisfies the stated
validity, unique-call, query, and qubit bounds [Ambainis2007ElementDistinctness]. -/
theorem algorithm3Native_full_memory (k N M : ℕ) [NeZero M] (hN : 0 < N) (hkN : k ≤ N) :
    ∃ P : Algorithm3Tree N M k,
      treeFrame P = initialFrame N ∧ algorithm3Valid N 2 P ∧ uniqueCallProbability 1 P ∧
      (treeQueries P : ℝ) ≤ 2*queryScale k N N ∧
      (treeQubits P : ℝ) ≤ 2*N*dataBits N M := by
  let A := nativeReadAll N M k hN
  have hset : frameSet (initialFrame N) = Finset.univ := by
    ext i
    simp [frameSet,initialFrame]
  have hverified (x : Fin N → ZMod M) (q : OutputSpace N M k A.workBits) :
      verifiedInFrame (initialFrame N) x q ↔ verifiedOutput x q := by
    simp [verifiedInFrame,hset]
  have hsound : frameCallSound A (initialFrame N) := by
    intro x s
    simpa only [hverified] using! (nativeReadAll_correct N M k hN x).1 s
  have hprob (x : Fin N → ZMod M) : frameCallProbability A (initialFrame N) x =
      if frameHasCollision k x (initialFrame N) then 1 else 0 := by
    have hhas : frameHasCollision k x (initialFrame N) ↔ HasCollision k x := by
      simp [frameHasCollision,hset,HasCollision]
    simpa only [frameCallProbability,hverified,hhas] using! nativeReadAll_probability N M k hN x
  have hq : callQueries A = N := by
    unfold callQueries maximumFinite
    have hf : (fun s : Fin A.seeds => QueryCount (A.program s)) = fun _ => N := by
      funext s
      exact nativeReadAll_queries N M k hN s
    rw [hf]
    dsimp only [A,nativeReadAll]
    simp
  have hf : frameWellFormed (initialFrame N) := by
    intro i j v hi hj
    simp only [initialFrame,Option.some.injEq] at hi hj
    exact hi.trans hj.symm
  let P := Algorithm3Tree.readAll (initialFrame N) A
  refine ⟨P,rfl,⟨hf,le_rfl,hsound,hq.le,hprob⟩,True.intro,?_,?_⟩
  · change (callQueries A : ℝ) ≤ _
    rw [hq]
    have hs : (N : ℝ) ≤ queryScale k N N := by
      unfold queryScale
      exact le_add_of_nonneg_right (by positivity)
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  · change (callQubits A : ℝ) ≤ _
    dsimp only [callQubits,A,nativeReadAll]
    unfold dataBits
    push_cast
    have hkR : (k : ℝ) ≤ N := by exact_mod_cast hkN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hcn : 0 ≤ (Nat.clog 2 (N+1) : ℝ) := Nat.cast_nonneg _
    have hcm : 0 ≤ (Nat.clog 2 (M+1) : ℝ) := Nat.cast_nonneg _
    have hpad :=
        mul_nonneg (sub_nonneg.mpr hN1)
        (show 0 ≤ 1+(Nat.clog 2 (N+1) : ℝ)+Nat.clog 2 (M+1) by positivity)
    have hout := mul_le_mul_of_nonneg_right hkR hcn
    nlinarith

end Qatlib.Concepts.WalkFind.SearchAlgorithm
