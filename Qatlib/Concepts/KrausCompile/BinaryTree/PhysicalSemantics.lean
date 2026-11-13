/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.KrausCompile.BinaryTree.AdaptiveCompiler

/-!
# Single-qubit realizations of compiled Kraus programs

`SingleQubit` certifies programs with unitary terminal channels and binary measurement nodes
realized by unitaries on the data space and one auxiliary qubit. The module proves this property
for the binary compiler and identifies the channel obtained by forgetting all records. The
constructions relate to finite Kraus implementations in [CaiEtAl2026].

## Main statements

* `compileFamily_singleQubit`: the physical realization certificate.
* `compileFamily_forget`: the original Kraus sum after discarding records.
* `compileFamily_extra`: zero branches for padding indices.

## References

* [Cai et al., 2026][CaiEtAl2026]
* [Kraus, 1983][Kraus1983]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.DimInstruments.DimTreeExec
open scoped BigOperators ComplexOrder

namespace Qatlib.Concepts.KrausCompile.BinaryTree

/-- Certifies a program whose terminal channels are unitary conjugations and whose binary
measurement nodes possess unitary realizations on the data space with one clean auxiliary
qubit. -/
inductive SingleQubit (d : ℕ) : Program d d → Prop where

  | halt (T : QuantumChannel d d) (U : Operator d)
      (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
      (hT : ∀ ρ, T.map ρ = U * ρ * U.conjTranspose) : SingleQubit d (.halt T)

  | measure (K : Fin 2 → Operator d) (hK : KrausComplete K)
      (next : Fin 2 → Program d d) (hnext : ∀ b, SingleQubit d (next b))
      (W : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ)
      (hW : W ∈ Matrix.unitaryGroup (Fin d × Fin 2) ℂ)
      (hbranch : ∀ b ρ, (Instrument.ofKraus K hK).branch b ρ = measuredQubitBranch W b ρ) :
      SingleQubit d (.measure (Instrument.ofKraus K hK) next)

/-- The sole operator in a complete singleton square Kraus family is unitary. -/
theorem singleton_unitary {d : ℕ} (K : Fin 1 → Operator d) (hK : KrausComplete K) :
    K 0 ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  simpa only [KrausComplete, Fin.sum_univ_one] using! hK

/-- The binary compilation of a complete power-of-two Kraus family satisfies `SingleQubit`. -/
theorem compileTree_singleQubit {d : ℕ} (n : ℕ) (K : Fin (2 ^ n) → Operator d)
    (hK : KrausComplete K) : SingleQubit d (compileTree n K hK) := by
  induction n with
  | zero => exact .halt _ (K 0) (singleton_unitary K hK) (singleton_map K hK)
  | succ n ih =>
    obtain ⟨W, hW, hb⟩ := actual_binary_instrument_implementation (nodeB n K) (node_complete n K hK)
    exact .measure _ _ _ (fun b => ih _ _) W hW hb

/-- The padded binary compilation of any complete finite square Kraus family satisfies
`SingleQubit`. -/
theorem compileFamily_singleQubit {d s : ℕ} (K : Fin s → Operator d) (hK : KrausComplete K) :
    SingleQubit d (compileFamily K hK) := compileTree_singleQubit _ _ _

/-- Forgetting the measurement records of a compiled tree yields the sum of the original Kraus
conjugation branches. -/
theorem compileTree_forget {d : ℕ} (n : ℕ) (K : Fin (2 ^ n) → Operator d)
    (hK : KrausComplete K) (ρ : Operator d) :
    forget (compileTree n K hK) ρ = ∑ i, K i * ρ * (K i).conjTranspose := by
  induction n generalizing ρ with
  | zero => simp [compileTree, forget, leaves, familyChannel, krausMap]
  | succ n ih =>
    rw [compileTree, forget_measure]
    simp_rw [ih]
    have hterm (b : Fin 2) (j : Fin (2^n)) :
        nodeF n K b j * ((Instrument.ofKraus (nodeB n K) (node_complete n K hK)).branch b ρ) *
          (nodeF n K b j).conjTranspose =
          K (splitEquiv n (b,j)) * ρ * (K (splitEquiv n (b,j))).conjTranspose := by
      have hf : nodeF n K b j * nodeB n K b = K (splitEquiv n (b,j)) :=
        groupF_factor _ _ j
      change nodeF n K b j * (nodeB n K b * ρ * (nodeB n K b).conjTranspose) *
        (nodeF n K b j).conjTranspose = _
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hf, Matrix.mul_assoc,
        ← Matrix.conjTranspose_mul, hf]
    simp_rw [hterm]
    simpa only [Fintype.sum_prod_type] using!
      (splitEquiv n).sum_comp (fun i => K i * ρ * (K i).conjTranspose)

/-- Forgetting the measurement records of a padded compiled family yields its original Kraus
channel. -/
theorem compileFamily_forget {d s : ℕ} (K : Fin s → Operator d) (hK : KrausComplete K)
    (ρ : Operator d) : forget (compileFamily K hK) ρ = ∑ i, K i * ρ * (K i).conjTranspose := by
  rw [compileFamily, compileTree_forget]
  rw [← (paddingEquiv (Nat.le_pow_clog (by norm_num : 1 < 2) s)).sum_comp]
  simp only [padFamily, Equiv.symm_apply_apply, Fin.sum_univ_add,
    Fin.addCases_left, Fin.addCases_right, Matrix.conjTranspose_zero, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero]

/-- Each padding index in the compiled family corresponds to a leaf whose map is zero on every
input matrix. -/
theorem compileFamily_extra {d s : ℕ} (K : Fin s → Operator d) (hK : KrausComplete K)
    (i : Fin (2^(Nat.clog 2 s)-s)) :
    ∃ t ∈ leaves (compileFamily K hK), ∀ ρ, t.map ρ = 0 := by
  let h := Nat.le_pow_clog (by norm_num : 1 < 2) s
  let j := paddingEquiv h (Fin.natAdd s i)
  refine ⟨compiledLeaf _ (padFamily h K) _ j, compiledLeaf_mem _ _ _ _, ?_⟩
  intro ρ
  rw [compiledLeaf_apply, show padFamily h K j = 0 from padFamily_extra h K i]
  simp

end Qatlib.Concepts.KrausCompile.BinaryTree
