/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.LatticeDecode
public import Qatlib.Papers.PottsPartEval07.CodeStructure.TraceCode

@[expose] public section

/-!
# Actual trace-code weight classes

A multiplicative orbit enumeration of the field induces a partition of its
trace code. The equal-weight property follows from actual coordinate
permutations, rather than an assumed list of weights. This is the algebraic
class compression used in arXiv:quant-ph/0703023v1, Proposition 1 and step 4
of the proof of Theorem 2.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped BigOperators
open Qatlib.Papers.PottsPartEval07.ExactRecovery
open Qatlib.Papers.PottsPartEval07.CodeStructure

variable {q : ℕ} [NeZero q] {E : Type*} [Fintype E] [DecidableEq E]

omit [NeZero q] [DecidableEq E] in
/-- Reindexing an actual codeword by a coordinate permutation preserves its Hamming weight. -/
theorem weight_comp_perm (word : E → ZMod q) (perm : Equiv.Perm E) :
    hammingWeight (fun e => word (perm e)) = hammingWeight word := by
  classical
  unfold hammingWeight
  apply Finset.card_equiv perm
  intro e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

variable {F : Type*} [Field F] [Fintype F]
  [Algebra (ZMod (ringChar F)) F]

/-- Concrete field elements are enumerated by multiplicative orbits of coordinate shifts. -/
structure TraceOrbits (g : E → F) (classes size : ℕ) where
  /-- Every field element has a unique zero-or-orbit record. -/
  enumerate : Option (Fin classes × Fin size) ≃ F
  /-- The separate record is the actual additive zero. -/
  at_zero : enumerate none = 0
  /-- One actual field element represents each nonzero orbit. -/
  representative : Fin classes → F
  /-- Orbit multipliers act on field elements, not on arbitrary weight labels. -/
  multiplier : Fin size → F
  /-- The orbit action permutes the actual trace coordinates. -/
  coordinate : Fin size → Equiv.Perm E
  /-- Every orbit record decodes by actual field multiplication. -/
  decode : ∀ i j, enumerate (some (i, j)) = representative i * multiplier j
  /-- The multipliers implement the indicated coordinate permutations. -/
  shift : ∀ j e, g (coordinate j e) = g e * multiplier j

variable [NeZero (ringChar F)]

/-- Actual field orbits induce codeword classes through the injective trace-word map. -/
def traceWeightClasses {classes size : ℕ} (g : E → F)
    (hspan : Submodule.span (ZMod (ringChar F)) (Set.range g) = ⊤)
    (orbits : TraceOrbits g classes size) : WeightClasses (traceCode g) classes size where
  encode := orbits.enumerate.trans (traceWordEquiv g hspan).toEquiv
  zero_word := by
    change traceWord g (orbits.enumerate none) = 0
    rw [orbits.at_zero]
    ext e
    simp [traceWord]
  representative i := traceWordEquiv g hspan (orbits.representative i)
  same_weight i j := by
    change hammingWeight (traceWord g (orbits.enumerate (some (i, j)))) =
      hammingWeight (traceWord g (orbits.representative i))
    rw [orbits.decode,
      traceWord_mul_eq_comp g (orbits.coordinate j) (orbits.multiplier j) (orbits.shift j)]
    exact weight_comp_perm _ _

/-- The compressed enumerator is consequently derived from the concrete trace code. -/
theorem trace_compressed_enum {classes size : ℕ} (g : E → F)
    (hspan : Submodule.span (ZMod (ringChar F)) (Set.range g) = ⊤)
    (orbits : TraceOrbits g classes size) (x y : ℂ) :
    compressedEnum (Fintype.card E) size
      (fun i => hammingWeight (traceWord g (orbits.representative i))) x y =
      weightEnum (traceCode g) x y := by
  exact compressedEnum_eq (traceCode g) (traceWeightClasses g hspan orbits) x y

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
