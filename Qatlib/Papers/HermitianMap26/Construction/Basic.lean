/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HermitianMap26.Construction.Definitions
import Qatlib.Concepts.KrausCompile.Normalize
import Qatlib.Concepts.KrausCompile.BinaryTree.PhysicalSemantics

/-!
# Automatic completion and binary-tree compilation

This module constructs the normalized physical Kraus family associated with a `SignedKraus`
representation in [CaiEtAl2026]. The normalization is positive in positive dimension, and
`automaticCompletion` fills the Gram deficit to make `compiledFamily` complete.

The complete family defines a completely positive, trace-preserving map and compiles to
`compiledProgram`, whose branches use a fixed logarithmic number of measurements and satisfy the
`SingleQubit` condition. If the unsigned Kraus sum is already a scalar identity with the
prescribed normalization, the completion vanishes.

## Main statements

* `completed_cptp`: proves completeness, complete positivity, and trace preservation.
* `construction_depth_bound`: gives the exact measurement count at each leaf.
* `compiledProgram_forget`: identifies the program's branch-forgetting semantics.
* `completion_trivial_of_scaled`: characterizes a case with zero completion.

## References

* [Cai et al., 2026][CaiEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.DimInstruments.DimTreeExec
open scoped ComplexOrder MatrixOrder BigOperators

namespace Qatlib.Papers.HermitianMap26.Construction.SignedKraus

variable {d r : ℕ} (D : SignedKraus d r)

/-- The normalization factor `gamma` of the underlying unsigned Kraus family. -/
def normalization : ℝ := Qatlib.Concepts.KrausCompile.Normalize.gamma D.K

/-- In positive dimension, the signed trace-preservation condition forces the normalization
factor to be at least one. -/
theorem normalization_ge_one (hd : 0 < d) : 1 ≤ D.normalization :=
  Qatlib.Concepts.KrausCompile.Normalize.gamma_ge_one hd D.K D.α D.sign
    D.tracePreserving

/-- In positive dimension, the normalization factor is strictly positive. -/
theorem normalization_pos (hd : 0 < d) : 0 < D.normalization :=
  lt_of_lt_of_le zero_lt_one (D.normalization_ge_one hd)

/-- The canonical completion operator associated with the underlying Kraus family. -/
def automaticCompletion : Op d :=
  Qatlib.Concepts.KrausCompile.Normalize.completion D.K

/-- Normalization by `D.normalization` agrees with the normalized Kraus family used by the
general compilation construction. -/
theorem normalizedKraus_actual (i : Fin r) :
    D.normalizedKraus D.normalization i =
      Qatlib.Concepts.KrausCompile.Normalize.normalizedKraus D.K i := by
  rw [Qatlib.Concepts.KrausCompile.Normalize.normalizedKraus_eq_complex]
  rfl

/-- In positive dimension, the Gram matrix of the automatic completion equals the identity minus
the normalized Kraus sum. -/
theorem automaticCompletion_gram (hd : 0 < d) :
    D.automaticCompletionᴴ * D.automaticCompletion = 1 - D.normalizedSum D.normalization := by
  have h := Qatlib.Concepts.KrausCompile.Normalize.completion_gram
    hd D.K D.α D.sign D.tracePreserving
  simpa only [automaticCompletion,
    Qatlib.Concepts.KrausCompile.Normalize.unsignedSum,
    ← D.normalizedKraus_actual, normalizedSum] using! h

/-- The normalized Kraus family extended by its automatic completion as the final branch. -/
def compiledFamily : Fin (r+1) → Op d :=
  D.completedKraus D.normalization D.automaticCompletion

/-- In positive dimension, the completed compiled Kraus family satisfies the Kraus completeness
identity. -/
theorem compiledFamily_complete (hd : 0 < d) : KrausComplete D.compiledFamily :=
  D.completedKraus_complete D.normalization (D.automaticCompletion_gram hd)

/-- In positive dimension, the compiled family is Kraus complete and its Kraus map is completely
positive and trace preserving. -/
theorem completed_cptp (hd : 0 < d) :
    KrausComplete D.compiledFamily ∧ CompletelyPositive (krausMap D.compiledFamily) ∧
      TracePreserving (krausMap D.compiledFamily) := by
  have h := D.compiledFamily_complete hd
  exact ⟨h, completelyPositive_of_krausForm (krausForm_krausMap D.compiledFamily),
    tracePreserving_of_krausComplete (krausForm_krausMap D.compiledFamily) h⟩

/-- The binary-tree program obtained by compiling the completed Kraus family in positive
dimension. -/
def compiledProgram (hd : 0 < d) : Program d d :=
  Qatlib.Concepts.KrausCompile.BinaryTree.compileFamily D.compiledFamily
    (D.compiledFamily_complete hd)

/-- Every leaf of the compiled program uses exactly `Nat.clog 2 (r + 1)` measurements. -/
theorem construction_depth_bound (hd : 0 < d) :
    ∀ t ∈ leaves (D.compiledProgram hd), t.measurements = Nat.clog 2 (r+1) :=
  Qatlib.Concepts.KrausCompile.BinaryTree.compileFamily_depth _ _

/-- Each original normalized Kraus operator occurs as the map of some leaf of the compiled
program. -/
theorem compiled_original_branch (hd : 0 < d) (i : Fin r) :
    ∃ t ∈ leaves (D.compiledProgram hd), ∀ ρ,
      t.map ρ = D.normalizedKraus D.normalization i * ρ *
        (D.normalizedKraus D.normalization i)ᴴ := by
  simpa only [compiledFamily, completedKraus_castSucc] using!
    Qatlib.Concepts.KrausCompile.BinaryTree.compileFamily_original
      D.compiledFamily (D.compiledFamily_complete hd) i.castSucc

/-- The compiled binary-tree program satisfies the `SingleQubit` circuit condition. -/
theorem compiled_binary_tree_circuit (hd : 0 < d) :
    Qatlib.Concepts.KrausCompile.BinaryTree.SingleQubit d (D.compiledProgram hd) :=
  Qatlib.Concepts.KrausCompile.BinaryTree.compileFamily_singleQubit _ _

/-- Forgetting the classical branches of the compiled program yields the Kraus map of the
completed family. -/
theorem compiledProgram_forget (hd : 0 < d) (ρ : Op d) :
    forget (D.compiledProgram hd) ρ = krausMap D.compiledFamily ρ := by
  rw [compiledProgram, Qatlib.Concepts.KrausCompile.BinaryTree.compileFamily_forget]
  simp only [krausMap, LinearMap.sum_apply, conjBranch_apply]

/-- If the unsigned Kraus sum is the normalization factor times the identity, the automatic
completion vanishes and the original normalized Kraus family is already complete. -/
theorem completion_trivial_of_scaled (hd : 0 < d)
    (hscale : D.krausSum = (D.normalization : ℂ) • (1 : Op d)) :
    D.automaticCompletion = 0 ∧ KrausComplete (D.normalizedKraus D.normalization) := by
  have hone : D.normalizedSum D.normalization = 1 := by
    rw [D.normalizedSum_eq_inv _ (D.normalization_pos hd), hscale, smul_smul,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (D.normalization_pos hd).ne'), one_smul]
  refine ⟨Matrix.conjTranspose_mul_self_eq_zero.mp ?_, ?_⟩
  · rw [D.automaticCompletion_gram hd, hone, sub_self]
  · exact hone

end Qatlib.Papers.HermitianMap26.Construction.SignedKraus
