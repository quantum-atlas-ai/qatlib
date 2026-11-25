/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamEfficiency10.SuzukiWord.SourceRecursive
public import Qatlib.Papers.HamEfficiency10.SuzukiWord.SourceDefinitions
public import Qatlib.Foundations.PureStateMath.Qubit

@[expose] public section

/-!
# The emitted Suzuki word after merging each central pair

The proof of Theorem 2 in arXiv:1005.1318v3 counts at most
`(2m - 1) * 5^(k - 1)` exponentials per segment. Replace the adjacent
halves of the last Hamiltonian in each Strang block by one full factor.
The higher orders preserve the five-block recurrence and its evaluation.
-/

set_option autoImplicit false

noncomputable section

open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability (hamiltonianEvolution)
open Qatlib.Papers.HamEfficiency10.SuzukiWord

namespace Qatlib.Papers.HamEfficiency10.SuzukiWord

/-- The chronological matrix-factor list for `m + 1` Hamiltonians.
Each Strang leaf uses a single factor for the last Hamiltonian. -/
def mergedSuzuki (m : ℕ) : ℕ → List (ℝ × Fin (m + 1))
  | 0 =>
      let pre := List.ofFn (fun j : Fin m => ((1 / 2 : ℝ), j.castSucc))
      pre ++ [(1, Fin.last m)] ++ pre.reverse
  | level + 1 =>
      let w := mergedSuzuki m level
      let u := recursiveSuzukiScale level
      let a := w.map (fun p => (u * p.1, p.2))
      let b := w.map (fun p => ((1 - 4 * u) * p.1, p.2))
      a ++ a ++ b ++ a ++ a

/-- One central merge at each of the `5^level` leaves gives the exact factor count. -/
theorem mergedSuzuki_length (m level : ℕ) :
    (mergedSuzuki m level).length = (2 * (m + 1) - 1) * 5 ^ level := by
  induction level with
  | zero => simp [mergedSuzuki]; omega
  | succ level ih =>
      simp only [mergedSuzuki, List.length_append, List.length_map, ih, pow_succ]
      rw [← Nat.mul_assoc]
      omega

private theorem manyTerm_append {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → Matrix I I ℂ) (x y : List (ℝ × Fin m)) (dt : ℝ) :
    manyTermWord H (x ++ y) dt = manyTermWord H x dt * manyTermWord H y dt := by
  simp only [manyTermWord, List.map_append, List.prod_append]

private theorem manyTerm_scale {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → Matrix I I ℂ) (w : List (ℝ × Fin m)) (a dt : ℝ) :
    manyTermWord H (w.map (fun p => (a * p.1, p.2))) dt =
      manyTermWord H w (a * dt) := by
  unfold manyTermWord
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply]
  congr 1
  ring

private theorem suzukiExp_append {I : Type} [Fintype I] [DecidableEq I]
    (xs ys : List (Matrix I I ℂ)) (t : ℝ) :
    suzukiExponentialWord (xs ++ ys) t =
      suzukiExponentialWord xs t * suzukiExponentialWord ys t := by
  simp only [suzukiExponentialWord, List.map_append, List.prod_append]

private theorem suzukiExp_scale {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (a t : ℝ) :
    suzukiExponentialWord (xs.map (fun X => a • X)) t = suzukiExponentialWord xs (a * t) := by
  simp only [suzukiExponentialWord, List.map_map, Function.comp_def, smul_smul, mul_comm t a]

private theorem exp_signed_half {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (t : ℝ) :
    NormedSpace.exp (t • ((1 / 2 : ℝ) • ((-Complex.I) • A))) =
      hamiltonianEvolution A ((1 / 2 : ℝ) * t) := by
  unfold hamiltonianEvolution
  congr 1
  rw [smul_smul t (1 / 2 : ℝ), ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  ring

private theorem halfWord_eval {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → Matrix I I ℂ) (is : List (Fin m)) (t : ℝ) :
    suzukiExponentialWord ((is.map H).map (fun X => (1 / 2 : ℝ) • ((-Complex.I) • X))) t =
      manyTermWord H (is.map (fun i => ((1 / 2 : ℝ), i))) t := by
  simp only [suzukiExponentialWord, manyTermWord, List.map_map, Function.comp_def, exp_signed_half]

/-- The compiled word evaluates to the exact matrix exponential product of the pinned
recursive generator list at every time and recursion level. -/
theorem mergedSuzuki_eval {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin (m + 1) → Matrix I I ℂ) (level : ℕ) (t : ℝ) :
    manyTermWord H (mergedSuzuki m level) t =
      suzukiExponentialWord
        (recursiveSuzukiGenerators (SourceRecursive.signed (List.ofFn H)) level) t := by
  induction level generalizing t with
  | zero =>
      let ix := List.ofFn (fun j : Fin m => j.castSucc)
      have hlist : List.ofFn H = (ix ++ [Fin.last m]).map H := by
        rw [List.ofFn_succ_last]
        simp [ix, List.map_append, List.map_ofFn, Function.comp_def]
      have hmid :
          hamiltonianEvolution (H (Fin.last m)) t =
            hamiltonianEvolution (H (Fin.last m)) ((1 / 2 : ℝ) * t) *
              hamiltonianEvolution (H (Fin.last m)) ((1 / 2 : ℝ) * t) := by
        simpa only [show (1 / 2 : ℝ) * t + (1 / 2 : ℝ) * t = t by ring,
            hamiltonianEvolution, Qatlib.Foundations.PureStateMath.HamiltonianEvolution] using
          Qatlib.Foundations.PureStateMath.hamiltonianEvolution_add (H (Fin.last m))
            ((1 / 2 : ℝ) * t) ((1 / 2 : ℝ) * t)
      have hhalf (xs : List (Fin (m + 1))) :
          suzukiExponentialWord
              (xs.map (fun j => (1 / 2 : ℝ) • ((-Complex.I) • H j))) t =
            manyTermWord H (xs.map (fun j => ((1 / 2 : ℝ), j))) t := by
        simpa only [List.map_map, Function.comp_def] using halfWord_eval H xs t
      have hp : List.ofFn (fun j : Fin m => ((1 / 2 : ℝ), j.castSucc)) =
          ix.map (fun j => ((1 / 2 : ℝ), j)) := by
        rw [List.map_ofFn]
        rfl
      simp only [mergedSuzuki, hp, hlist, recursiveSuzukiGenerators, SourceRecursive.signed,
        List.map_append, List.map_singleton, List.reverse_append, List.reverse_singleton,
        ← List.map_reverse, List.map_map, Function.comp_def, suzukiExp_append, hhalf,
        manyTerm_append]
      simp only [manyTermWord, suzukiExponentialWord, List.map_singleton, List.prod_singleton,
        exp_signed_half, one_mul, hmid, mul_assoc]
  | succ level ih =>
      simp only [mergedSuzuki, recursiveSuzukiGenerators, manyTerm_append, suzukiExp_append,
        manyTerm_scale, suzukiExp_scale, ih]

/-- For any nonempty Hamiltonian family, the source order-`2k` matrix product has
a word of at most `(2m - 1) * 5^(k - 1)` exponential primitives. -/
theorem sourceWord_merged_bound {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (hm : 0 < m) (H : Fin m → Matrix I I ℂ) (k : ℕ) (t : ℝ) :
    ∃ w : List (ℝ × Fin m), w.length ≤ (2 * m - 1) * 5 ^ (k - 1) ∧
      manyTermWord H w t = suzukiExponentialWord (SourceRecursive.sourceWord (List.ofFn H) k) t := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  exact ⟨mergedSuzuki m (k - 1), (mergedSuzuki_length m (k - 1)).le,
    mergedSuzuki_eval H (k - 1) t⟩

end Qatlib.Papers.HamEfficiency10.SuzukiWord
