/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
public import Qatlib.Papers.PottsPartEval07.PottsBridge.KernelComponents

@[expose] public section

/-!
# Uniform-coupling bridge to the original partition-sum interface

The fixed source uses a common coupling on every edge. A color-register
equivalence and the product of monochromatic Boltzmann factors identify that
physical partition sum with the code-based variable `y = exp(-coupling)`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped BigOperators
open Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

variable {q : ℕ} [NeZero q] {V E : Type*}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The two concrete color registers represent the same spin configurations. -/
def spinEquiv : (V → ZMod q) ≃ (V → Fin q) :=
  Equiv.piCongrRight fun _ => (ZMod.finEquiv q).symm.toEquiv

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- A uniform Boltzmann product equals the inverse `y` power of its monochromatic count. -/
theorem uniform_weight (ends : E → V × V) (coupling : ℝ) (spin : V → ZMod q) :
    pottsBoltzmann q ends (fun _ => coupling) (spinEquiv spin) =
      ((Real.exp (-coupling)) ^
        (Qatlib.Papers.PottsPartEval07.PottsBridge.monochromatic q ends spin).card)⁻¹ := by
  classical
  have he : ∀ u v : V, spinEquiv spin u = spinEquiv spin v ↔ spin u = spin v := by
    intro u v
    exact (ZMod.finEquiv q).symm.injective.eq_iff
  unfold pottsBoltzmann
  simp only [he]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one]
  rw [Real.exp_neg, inv_pow, inv_inv]
  rfl

omit [DecidableEq E] in
/-- The original physical partition function equals the graph/code partition variable. -/
theorem uniform_partition (ends : E → V × V) (coupling : ℝ) :
    pottsPartition q ends (fun _ => coupling) =
      Qatlib.Papers.PottsPartEval07.PottsBridge.pottsZ q ends (Real.exp (-coupling)) := by
  classical
  unfold pottsPartition
  rw [← Equiv.sum_comp (spinEquiv (q := q) (V := V))]
  unfold Qatlib.Papers.PottsPartEval07.PottsBridge.pottsZ
  exact Finset.sum_congr rfl fun spin _ => uniform_weight ends coupling spin

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
