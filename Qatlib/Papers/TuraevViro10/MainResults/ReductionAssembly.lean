/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TuraevViro10.MainResults.BqpHardness
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TuraevViro10.MainResults.ReductionAssembly

inductive Move

  | F

  | S
  deriving DecidableEq, Repr

abbrev Word := List Move

def countMove (m : Move) : Word → ℕ
  | [] => 0
  | a :: w => (if a = m then 1 else 0) + countMove m w

theorem count_F_add_S (w : Word) :
    countMove Move.F w + countMove Move.S w = w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a <;> simp [countMove] at ih ⊢ <;> omega

structure GenWord where

  word : Word

  fLe : countMove Move.F word ≤ 1

  sLe : countMove Move.S word ≤ 1

theorem GenWord.length_le_two (g : GenWord) : g.word.length ≤ 2 := by
  have h := count_F_add_S g.word
  have hf := g.fLe
  have hs := g.sLe
  omega

def wordsOf : List GenWord → Word
  | [] => []
  | g :: gs => g.word ++ wordsOf gs

theorem wordsOf_length_le (gens : List GenWord) :
    (wordsOf gens).length ≤ 2 * gens.length := by
  induction gens with
  | nil => simp [wordsOf]
  | cons g gs ih =>
    have hg : g.word.length ≤ 2 := g.length_le_two
    show (g.word ++ wordsOf gs).length ≤ 2 * (g :: gs).length
    rw [List.length_append, List.length_cons]
    omega

def twistsPerGate : ℕ := 5

def generatorsFor (T : ℕ) : ℕ := twistsPerGate * T

theorem word_length_le_ten (gens : List GenWord) (T : ℕ)
    (hT : gens.length = generatorsFor T) : (wordsOf gens).length ≤ 10 * T := by
  have h := wordsOf_length_le gens
  rw [hT] at h
  unfold generatorsFor twistsPerGate at h
  omega

def genusOfQubits (n : ℕ) : ℕ := n + 1

theorem genusOfQubits_eq (n : ℕ) : genusOfQubits n = n + 1 := rfl

theorem two_le_genus_of_one_qubit {n : ℕ} (hn : 1 ≤ n) : 2 ≤ genusOfQubits n := by
  unfold genusOfQubits
  omega

theorem qubits_of_genus (n : ℕ) : genusOfQubits n - 1 = n := by
  unfold genusOfQubits
  omega

def codeDim (n : ℕ) : ℕ := 2 ^ n

theorem codeDim_eq (n : ℕ) : codeDim (genusOfQubits n - 1) = 2 ^ n := by
  rw [qubits_of_genus]
  rfl

structure ReductionData where

  qubits : ℕ

  gates : ℕ

  gens : List GenWord

  hgen : gens.length = generatorsFor gates

def ReductionData.genus (d : ReductionData) : ℕ := genusOfQubits d.qubits

def ReductionData.word (d : ReductionData) : Word := wordsOf d.gens

theorem ReductionData.genus_eq (d : ReductionData) : d.genus = d.qubits + 1 := rfl

theorem ReductionData.word_length_le (d : ReductionData) :
    d.word.length ≤ 10 * d.gates :=
  word_length_le_ten d.gens d.gates d.hgen

theorem ReductionData.size_bound (d : ReductionData) :
    d.genus = d.qubits + 1 ∧ d.word.length ≤ 10 * d.gates :=
  ⟨d.genus_eq, d.word_length_le⟩

end Qatlib.Papers.TuraevViro10.MainResults.ReductionAssembly
