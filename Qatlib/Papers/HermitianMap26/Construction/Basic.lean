/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HermitianMap26.Construction.Definitions
import Qatlib.Concepts.KrausCompile.Normalize
import Qatlib.Concepts.KrausCompile.BinaryTree.PhysicalSemantics
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

def normalization : ℝ := Qatlib.Concepts.KrausCompile.Normalize.gamma D.K

theorem normalization_ge_one (hd : 0 < d) : 1 ≤ D.normalization :=
  Qatlib.Concepts.KrausCompile.Normalize.gamma_ge_one hd D.K D.α D.sign
    D.tracePreserving

theorem normalization_pos (hd : 0 < d) : 0 < D.normalization :=
  lt_of_lt_of_le zero_lt_one (D.normalization_ge_one hd)

def automaticCompletion : Op d :=
  Qatlib.Concepts.KrausCompile.Normalize.completion D.K

theorem normalizedKraus_actual (i : Fin r) :
    D.normalizedKraus D.normalization i =
      Qatlib.Concepts.KrausCompile.Normalize.normalizedKraus D.K i := by
  rw [Qatlib.Concepts.KrausCompile.Normalize.normalizedKraus_eq_complex]
  rfl

theorem automaticCompletion_gram (hd : 0 < d) :
    D.automaticCompletionᴴ * D.automaticCompletion = 1 - D.normalizedSum D.normalization := by
  have h := Qatlib.Concepts.KrausCompile.Normalize.completion_gram
    hd D.K D.α D.sign D.tracePreserving
  simpa only [automaticCompletion,
    Qatlib.Concepts.KrausCompile.Normalize.unsignedSum,
    ← D.normalizedKraus_actual, normalizedSum] using! h

def compiledFamily : Fin (r+1) → Op d :=
  D.completedKraus D.normalization D.automaticCompletion

theorem compiledFamily_complete (hd : 0 < d) : KrausComplete D.compiledFamily :=
  D.completedKraus_complete D.normalization (D.automaticCompletion_gram hd)

theorem completed_cptp (hd : 0 < d) :
    KrausComplete D.compiledFamily ∧ CompletelyPositive (krausMap D.compiledFamily) ∧
      TracePreserving (krausMap D.compiledFamily) := by
  have h := D.compiledFamily_complete hd
  exact ⟨h, completelyPositive_of_krausForm (krausForm_krausMap D.compiledFamily),
    tracePreserving_of_krausComplete (krausForm_krausMap D.compiledFamily) h⟩

def compiledProgram (hd : 0 < d) : Program d d :=
  Qatlib.Concepts.KrausCompile.BinaryTree.compileFamily D.compiledFamily
    (D.compiledFamily_complete hd)

theorem construction_depth_bound (hd : 0 < d) :
    ∀ t ∈ leaves (D.compiledProgram hd), t.measurements = Nat.clog 2 (r+1) :=
  Qatlib.Concepts.KrausCompile.BinaryTree.compileFamily_depth _ _

theorem compiled_original_branch (hd : 0 < d) (i : Fin r) :
    ∃ t ∈ leaves (D.compiledProgram hd), ∀ ρ,
      t.map ρ = D.normalizedKraus D.normalization i * ρ *
        (D.normalizedKraus D.normalization i)ᴴ := by
  simpa only [compiledFamily, completedKraus_castSucc] using!
    Qatlib.Concepts.KrausCompile.BinaryTree.compileFamily_original
      D.compiledFamily (D.compiledFamily_complete hd) i.castSucc

theorem compiled_binary_tree_circuit (hd : 0 < d) :
    Qatlib.Concepts.KrausCompile.BinaryTree.SingleQubit d (D.compiledProgram hd) :=
  Qatlib.Concepts.KrausCompile.BinaryTree.compileFamily_singleQubit _ _

theorem compiledProgram_forget (hd : 0 < d) (ρ : Op d) :
    forget (D.compiledProgram hd) ρ = krausMap D.compiledFamily ρ := by
  rw [compiledProgram, Qatlib.Concepts.KrausCompile.BinaryTree.compileFamily_forget]
  simp only [krausMap, LinearMap.sum_apply, conjBranch_apply]

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
