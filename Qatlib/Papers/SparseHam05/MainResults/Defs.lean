/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.RecursiveSuzukiConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.SparseHam05.MainResults

def iteratedLog2 : ℕ → ℕ → ℕ
  | 0, n => n
  | r + 1, n => iteratedLog2 r (Nat.log2 n)

theorem nat_log2_lt_self {n : ℕ} (h : 2 ≤ n) : Nat.log2 n < n := by
  rw [Nat.log2_def, if_pos h]
  by_cases hn : n = 2
  · subst hn
    decide
  · have h3 : 2 < n := by omega
    have hle : Nat.log2 (n / 2) ≤ n / 2 := Nat.log2_le_self _
    have hdiv : n / 2 + 1 < n := by omega
    omega

theorem iteratedLog2_lt_two_eventually : ∀ n : ℕ, ∃ r, iteratedLog2 r n < 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 2
    · exact ⟨0, h⟩
    · have h2 : 2 ≤ n := by omega
      obtain ⟨r, hr⟩ := ih (Nat.log2 n) (nat_log2_lt_self h2)
      exact ⟨r + 1, hr⟩

def logStar (n : ℕ) : ℕ := Nat.find (iteratedLog2_lt_two_eventually n)

theorem logStar_spec (n : ℕ) : iteratedLog2 (logStar n) n < 2 :=
  Nat.find_spec (iteratedLog2_lt_two_eventually n)

theorem logStar_min {n r : ℕ} (h : iteratedLog2 r n < 2) : logStar n ≤ r :=
  Nat.find_min' (iteratedLog2_lt_two_eventually n) h

def paperAntiHermitian {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) : List (Matrix I I ℂ) :=
  hs.map (fun H => (-Complex.I) • H)

theorem paperAntiHermitian_antiHermitian {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (hh : ∀ X ∈ hs, Xᴴ = X) :
    ∀ Y ∈ paperAntiHermitian hs, Yᴴ = -Y := by
  intro Y hY
  simp only [paperAntiHermitian, List.mem_map] at hY
  obtain ⟨X, hX, rfl⟩ := hY
  rw [Matrix.conjTranspose_smul, hh X hX]
  simp

def paperSuzukiWord {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (t : ℝ) (r : ℕ) : List (Matrix I I ℂ) :=
  recursiveSuzukiWord (paperAntiHermitian hs) (k - 1) t r

def paperSuzukiError (m k : ℕ) (τ : ℝ) (r : ℕ) : ℝ :=
  5 * (2 * (5 : ℝ) ^ (k - 1) * (m : ℝ) * τ) ^ (2 * k + 1) / (r : ℝ) ^ (2 * k)

theorem paperSuzukiWord_length {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k r : ℕ) (t : ℝ) :
    (paperSuzukiWord hs k t r).length = r * (2 * hs.length * 5 ^ (k - 1)) := by
  have hgen := (recursive_suzuki_length_and_mass I (paperAntiHermitian hs) (k - 1)).1
  have hgen' :
      (recursiveSuzukiGenerators (paperAntiHermitian hs) (k - 1)).length
        = 2 * hs.length * 5 ^ (k - 1) := by
    rw [hgen]
    simp [paperAntiHermitian]
  simp only [paperSuzukiWord, recursiveSuzukiWord, List.length_flatten, List.length_map,
    List.map_replicate, List.sum_replicate_nat, hgen']

def ColSparse {N : ℕ} (d : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ j, (Finset.univ.filter (fun i => H i j ≠ 0)).card ≤ d

def OneSparse {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (∀ i, (Finset.univ.filter (fun j => H i j ≠ 0)).card ≤ 1) ∧
    (∀ j, (Finset.univ.filter (fun i => H i j ≠ 0)).card ≤ 1)

abbrev RowOracleFn (N d : ℕ) : Type := Fin N → Fin d → ℂ × Fin N

structure RowOracle (N d : ℕ) where

  entry : Fin N → Fin d → ℂ × Fin N

def RowOracle.matrix {N d : ℕ} (O : RowOracle N d) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ∑ k, if (O.entry i k).2 = j then (O.entry i k).1 else 0

def RowComputable {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∃ d, ∃ O : RowOracle N d, H = O.matrix

def RealisesOracle {N d : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (g : RowOracleFn N d) : Prop :=
  (∀ i k, (g i k).1 = 0 ∨ H i (g i k).2 = (g i k).1) ∧
    (∀ i j, H i j ≠ 0 → ∃ k, (g i k).1 = H i j ∧ (g i k).2 = j)

def basisZero (N : ℕ) : Fin N → ℂ := fun i => if i.val = 0 then 1 else 0

def pureTraceDistance {N : ℕ} (ψ φ : Fin N → ℂ) : ℝ :=
  Real.sqrt (1 - ‖∑ i, ψ i * star (φ i)‖ ^ 2)

structure RowAccessProgram (N d : ℕ) where
  queries : RowOracleFn N d → ℕ
  out : RowOracleFn N d → (Fin N → ℂ)

def RowAccessProgram.Local {N d : ℕ} (P : RowAccessProgram N d) : Prop :=
  ∀ g g' : RowOracleFn N d,
    (∀ i k, k.val < P.queries g → g i k = g' i k) → P.out g = P.out g'

def SimulatesWithin {N d : ℕ} (P : RowAccessProgram N d) (g : RowOracleFn N d)
    (target : Fin N → ℂ) (ε : ℝ) : Prop :=
  pureTraceDistance (P.out g) target ≤ ε

def ColSparseOn {α : Type} [Fintype α] (d : ℕ) (H : Matrix α α ℂ) : Prop :=
  ∀ j, (Finset.univ.filter (fun i => H i j ≠ 0)).card ≤ d

def RowComputableOn {α : Type} [Fintype α] [DecidableEq α]
    (H : Matrix α α ℂ) : Prop :=
  ∃ d, ∃ O : α → Fin d → ℂ × α,
    H = fun i j => ∑ k, if (O i k).2 = j then (O i k).1 else 0

abbrev RowOracleFnOn (α : Type) (d : ℕ) : Type := α → Fin d → ℂ × α

def RealisesOracleOn {α : Type} [Fintype α] [DecidableEq α] {d : ℕ}
    (H : Matrix α α ℂ) (g : RowOracleFnOn α d) : Prop :=
  (∀ i k, (g i k).1 = 0 ∨ H i (g i k).2 = (g i k).1) ∧
    (∀ i j, H i j ≠ 0 → ∃ k, (g i k).1 = H i j ∧ (g i k).2 = j)

def pureTraceDistanceOn {α : Type} [Fintype α] (ψ φ : α → ℂ) : ℝ :=
  Real.sqrt (1 - ‖∑ i, ψ i * star (φ i)‖ ^ 2)

structure RowAccessProgramOn (α : Type) (d : ℕ) where
  queries : RowOracleFnOn α d → ℕ
  out : RowOracleFnOn α d → (α → ℂ)

def RowAccessProgramOn.Local {α : Type} {d : ℕ}
    (P : RowAccessProgramOn α d) : Prop :=
  ∀ g g' : RowOracleFnOn α d,
    (∀ i k, k.val < P.queries g → g i k = g' i k) → P.out g = P.out g'

def SimulatesWithinOn {α : Type} [Fintype α] {d : ℕ}
    (P : RowAccessProgramOn α d) (g : RowOracleFnOn α d) (target : α → ℂ) (ε : ℝ) : Prop :=
  pureTraceDistanceOn (P.out g) target ≤ ε

def basisZeroOn {α : Type} [Fintype α] [DecidableEq α] (i₀ : α) : α → ℂ :=
  fun i => if i = i₀ then 1 else 0

def IsSparseDecomposition {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (m : ℕ) (Hs : Fin m → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  H = ∑ j, Hs j ∧ ∀ j, OneSparse (Hs j)

structure GeneralIntegrator where
  steps : ℝ → List (Bool × ℝ)

def generalIntegratorProduct {I : Type} [Fintype I] [DecidableEq I]
    (E : GeneralIntegrator) (H₁ H₂ : Matrix I I ℂ) (τ : ℝ) : Matrix I I ℂ :=
  ((E.steps τ).map
    (fun s => NormedSpace.exp (((-Complex.I) * (s.2 : ℂ)) •
      (if s.1 then H₁ else H₂)))).prod

def GeneralIntegrator.exponentials (E : GeneralIntegrator) (τ : ℝ) : ℕ :=
  (E.steps τ).length

end Qatlib.Papers.SparseHam05.MainResults
