/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TuraevViro10.MainResults.BqpHardness
import Mathlib.Tactic

/-!
# Size accounting for a topological reduction word

Elementary generator words contain at most one `F` move and one `S` move,
so concatenating the prescribed generators uses at most ten moves per
modeled circuit gate. Encoding `n` qubits uses genus `n + 1`, and the code
dimension at that genus is `2 ^ n`. `ReductionData` packages these counts and
their resulting size bound.

The reduction setting is [AlagicEtAl2010]. These are combinatorial resource
identities for the supplied word data.
-/

set_option autoImplicit false

namespace Qatlib.Papers.TuraevViro10.MainResults.ReductionAssembly

/-- The two elementary move symbols `F` and `S`. -/
inductive Move

  | F

  | S
  deriving DecidableEq, Repr

/-- A finite list of elementary moves. -/
abbrev Word := List Move

/-- The number of occurrences of a specified move in a word. -/
def countMove (m : Move) : Word → ℕ
  | [] => 0
  | a :: w => (if a = m then 1 else 0) + countMove m w

/-- The counts of `F` and `S` in a word sum to its length. -/
theorem count_F_add_S (w : Word) :
    countMove Move.F w + countMove Move.S w = w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a <;> simp [countMove] at ih ⊢ <;> omega

/-- A generator word containing at most one `F` move and at most one `S` move. -/
structure GenWord where

  word : Word

  fLe : countMove Move.F word ≤ 1

  sLe : countMove Move.S word ≤ 1

/-- Every generator word has length at most two. -/
theorem GenWord.length_le_two (g : GenWord) : g.word.length ≤ 2 := by
  have h := count_F_add_S g.word
  have hf := g.fLe
  have hs := g.sLe
  omega

/-- Concatenation of the words in a list of generator words. -/
def wordsOf : List GenWord → Word
  | [] => []
  | g :: gs => g.word ++ wordsOf gs

/-- Concatenating generator words produces a word of length at most twice the number of
generators. -/
theorem wordsOf_length_le (gens : List GenWord) :
    (wordsOf gens).length ≤ 2 * gens.length := by
  induction gens with
  | nil => simp [wordsOf]
  | cons g gs ih =>
    have hg : g.word.length ≤ 2 := g.length_le_two
    show (g.word ++ wordsOf gs).length ≤ 2 * (g :: gs).length
    rw [List.length_append, List.length_cons]
    omega

/-- The fixed budget of five twists per gate. -/
def twistsPerGate : ℕ := 5

/-- The generator budget for `T` gates, equal to five times `T`. -/
def generatorsFor (T : ℕ) : ℕ := twistsPerGate * T

/-- A list containing the prescribed five generators per gate concatenates to a word of length
at most `10 * T`. See [AlagicEtAl2010]. -/
theorem word_length_le_ten (gens : List GenWord) (T : ℕ)
    (hT : gens.length = generatorsFor T) : (wordsOf gens).length ≤ 10 * T := by
  have h := wordsOf_length_le gens
  rw [hT] at h
  unfold generatorsFor twistsPerGate at h
  omega

/-- The genus assigned to `n` qubits, equal to `n + 1`. -/
def genusOfQubits (n : ℕ) : ℕ := n + 1

/-- The genus assigned to `n` qubits is `n + 1`. See [AlagicEtAl2010]. -/
theorem genusOfQubits_eq (n : ℕ) : genusOfQubits n = n + 1 := rfl

/-- At least one qubit gives assigned genus at least two. -/
theorem two_le_genus_of_one_qubit {n : ℕ} (hn : 1 ≤ n) : 2 ≤ genusOfQubits n := by
  unfold genusOfQubits
  omega

/-- Subtracting one from the genus assigned to `n` qubits recovers `n`. -/
theorem qubits_of_genus (n : ℕ) : genusOfQubits n - 1 = n := by
  unfold genusOfQubits
  omega

/-- The code-space dimension `2 ^ n`. -/
def codeDim (n : ℕ) : ℕ := 2 ^ n

/-- The code dimension at genus minus one for `n` qubits equals `2 ^ n`. -/
theorem codeDim_eq (n : ℕ) : codeDim (genusOfQubits n - 1) = 2 ^ n := by
  rw [qubits_of_genus]
  rfl

/-- Reduction bookkeeping consisting of qubit and gate counts and a generator list of the
prescribed length. -/
structure ReductionData where

  qubits : ℕ

  gates : ℕ

  gens : List GenWord

  hgen : gens.length = generatorsFor gates

/-- The genus determined by the qubit count in the reduction data. -/
def ReductionData.genus (d : ReductionData) : ℕ := genusOfQubits d.qubits

/-- The concatenated elementary-move word specified by the reduction generators. -/
def ReductionData.word (d : ReductionData) : Word := wordsOf d.gens

/-- The genus stored by the reduction construction equals the qubit count plus one. -/
theorem ReductionData.genus_eq (d : ReductionData) : d.genus = d.qubits + 1 := rfl

/-- The elementary-move word of the reduction has length at most ten times its gate count. -/
theorem ReductionData.word_length_le (d : ReductionData) :
    d.word.length ≤ 10 * d.gates :=
  word_length_le_ten d.gens d.gates d.hgen

/-- The supplied reduction data has genus `qubits + 1` and word length at most
ten times its gate count, matching the resource-accounting setting of
[Alagic et al.][AlagicEtAl2010]. -/
theorem ReductionData.size_bound (d : ReductionData) :
    d.genus = d.qubits + 1 ∧ d.word.length ≤ 10 * d.gates :=
  ⟨d.genus_eq, d.word_length_le⟩

end Qatlib.Papers.TuraevViro10.MainResults.ReductionAssembly
