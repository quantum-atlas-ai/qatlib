/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.LinearCodeProgram

/-!
# Explicit additive circuits for linear encoders

`additions` compiles a list of known maps into additive gates, and `components` decomposes a
linear encoder into its individual matrix-entry contributions. The sparse variant omits zero
entries, yielding the same encoder with a gate count equal to the size of `support`. See
[TerhalSmolin1998] for the source development.

## Main statements

* `compiled_encoder` and `compiled_inverse`: evaluate the component circuits as the encoder and
  its additive inverse.
* `two_pass_resources`: counts `2 * m * n` gates for the dense forward and inverse passes.
* `sparse_resources` and `run_sparse`: give the support-based count and semantics of the sparse
  encoder.

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.EncoderCircuit

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.CyclicRecovery

section Additions
variable {I R : Type} [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [AddCommGroup R]

/-- The circuit of known additive gates obtained from a list of maps, with one gate for each
map. -/
noncomputable def additions (fs : List (I → R)) : Circuit (I × R) :=
  fs.map (fun f => Step.gate (AddOracle f))

omit [Fintype I] [Fintype R] in

/-- The known-addition circuit uses no queries and has one explicit gate per list entry. -/
theorem additions_resources (fs : List (I → R)) :
    QueryCount (additions fs) = 0 ∧ GateCount (additions fs) = fs.length := by
  induction fs with
  | nil => exact ⟨rfl, rfl⟩
  | cons f fs ih => simpa [additions] using ih

/-- Every gate in the known-addition circuit is unitary. -/
theorem additions_unitary (fs : List (I → R)) : IsUnitaryCircuit (additions fs) := by
  induction fs with
  | nil => exact isUnitaryCircuit_nil
  | cons f fs ih =>
    exact (isUnitaryCircuit_gate _ _).2 ⟨addOracle_unitary f, ih⟩

/-- Running the known-addition circuit applies the additive gate for `fs.sum`, independently of
the supplied hidden oracle. -/
theorem run_additions (oracle : Matrix (I × R) (I × R) ℂ)
    (fs : List (I → R)) (ψ : QState (I × R)) :
    Run oracle (additions fs) ψ = ApplyGate (AddOracle fs.sum) ψ := by
  induction fs generalizing ψ with
  | nil => simp [additions]
  | cons f fs ih =>
    simp only [additions, List.map_cons, Run]
    rw [show Run oracle (fs.map (fun f => Step.gate (AddOracle f)))
        (ApplyGate (AddOracle f) ψ) = _ from ih _]
    rw [← applyGate_mul, ← addOracle_add, List.sum_cons, add_comm f]

end Additions

variable {A m n : ℕ} [NeZero A]

/-- The contribution of matrix entry `g p.1 p.2` to the encoder, supported only at output
coordinate `p.2`. -/
def component (g : Fin m → Fin n → ZMod A) (p : Fin m × Fin n)
    (s : Fin m → ZMod A) : Fin n → ZMod A := Pi.single p.2 (s p.1 * g p.1 p.2)

/-- The list of encoder component maps indexed by all pairs of input and output coordinates. -/
noncomputable def components (g : Fin m → Fin n → ZMod A) :
    List ((Fin m → ZMod A) → (Fin n → ZMod A)) :=
  (Finset.univ : Finset (Fin m × Fin n)).toList.map (component g)

omit [NeZero A] in

/-- The component indexed by `(i, j)` has value `s i * g i j` at output coordinate `j` and zero
elsewhere. -/
theorem component_apply (g : Fin m → Fin n → ZMod A) (i : Fin m) (j t : Fin n)
    (s : Fin m → ZMod A) :
    component g (i,j) s t = if t = j then s i * g i j else 0 := by
  simp [component, Pi.single_apply]

omit [NeZero A] in

/-- The sum of all component maps is the linear encoding map `LinearCodeProgram.encode g`. -/
theorem components_sum (g : Fin m → Fin n → ZMod A) :
    (components g).sum = LinearCodeProgram.encode g := by
  classical
  rw [components, Finset.sum_map_toList]
  funext s j
  simp only [Finset.sum_apply, Fintype.sum_prod_type, component, Pi.single_apply]
  simp [LinearCodeProgram.encode]

omit [NeZero A] in

/-- The dense encoder circuit uses no queries and exactly `m * n` explicit gates. -/
theorem encoder_resources (g : Fin m → Fin n → ZMod A) :
    QueryCount (additions (components g)) = 0 ∧
    GateCount (additions (components g)) = m*n := by
  have h := additions_resources (components g)
  simpa [components] using h

/-- Running the dense component circuit is equivalent to applying the additive gate for the
linear encoder. -/
theorem compiled_encoder (g : Fin m → Fin n → ZMod A)
    (oracle : Matrix ((Fin m → ZMod A) × (Fin n → ZMod A))
      ((Fin m → ZMod A) × (Fin n → ZMod A)) ℂ)
    (ψ : QState ((Fin m → ZMod A) × (Fin n → ZMod A))) :
    Run oracle (additions (components g)) ψ =
      ApplyGate (AddOracle (LinearCodeProgram.encode g)) ψ := by
  rw [run_additions, components_sum]

/-- Running the component circuit with every map negated is equivalent to applying the additive
gate for the negative linear encoder. -/
theorem compiled_inverse (g : Fin m → Fin n → ZMod A)
    (oracle : Matrix ((Fin m → ZMod A) × (Fin n → ZMod A))
      ((Fin m → ZMod A) × (Fin n → ZMod A)) ℂ)
    (ψ : QState ((Fin m → ZMod A) × (Fin n → ZMod A))) :
    Run oracle (additions ((components g).map Neg.neg)) ψ =
      ApplyGate (AddOracle (-LinearCodeProgram.encode g)) ψ := by
  have hs (fs : List ((Fin m → ZMod A) → (Fin n → ZMod A))) :
      (fs.map Neg.neg).sum = -fs.sum := by
    induction fs with
    | nil => simp
    | cons f fs ih => simp [ih, add_comm]
  rw [run_additions, hs, components_sum]

/-- The dense forward encoder followed by its inverse uses no queries and exactly `2 * m * n`
explicit gates. -/
theorem two_pass_resources (g : Fin m → Fin n → ZMod A) :
    QueryCount (additions (components g) ++ additions ((components g).map Neg.neg)) = 0 ∧
    GateCount (additions (components g) ++ additions ((components g).map Neg.neg)) = 2*m*n := by
  rw [queryCount_append, gateCount_append]
  have h := additions_resources (components g)
  have hn := additions_resources ((components g).map Neg.neg)
  simp only [h.1, hn.1, h.2, hn.2, List.length_map, zero_add]
  simp only [components, List.length_map, Finset.length_toList, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin]
  constructor
  · trivial
  · ring

/-- The finite set of input-output coordinate pairs where the generator matrix has a nonzero
entry. -/
def support (g : Fin m → Fin n → ZMod A) : Finset (Fin m × Fin n) :=
  Finset.univ.filter (fun p => g p.1 p.2 ≠ 0)

/-- The list of encoder component maps indexed only by nonzero entries of the generator matrix. -/
noncomputable def sparseComponents (g : Fin m → Fin n → ZMod A) :
    List ((Fin m → ZMod A) → (Fin n → ZMod A)) := (support g).toList.map (component g)

omit [NeZero A] in

/-- The sparse component maps sum to the same linear encoder as the full component list. -/
theorem sparse_sum (g : Fin m → Fin n → ZMod A) :
    (sparseComponents g).sum = LinearCodeProgram.encode g := by
  classical
  rw [sparseComponents, Finset.sum_map_toList, ← components_sum g,
    components, Finset.sum_map_toList]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hn
  have hg : g p.1 p.2 = 0 := by simpa [support, hp] using hn
  funext s j
  simp [component, hg]

omit [NeZero A] in

/-- The sparse encoder circuit uses no queries and has exactly one gate per nonzero generator
entry. -/
theorem sparse_resources (g : Fin m → Fin n → ZMod A) :
    QueryCount (additions (sparseComponents g)) = 0 ∧
    GateCount (additions (sparseComponents g)) = (support g).card := by
  simpa [sparseComponents] using additions_resources (sparseComponents g)

/-- Running the sparse component circuit is equivalent to applying the additive gate for the
linear encoder. -/
theorem run_sparse (g : Fin m → Fin n → ZMod A)
    (oracle : Matrix ((Fin m → ZMod A) × (Fin n → ZMod A))
      ((Fin m → ZMod A) × (Fin n → ZMod A)) ℂ)
    (ψ : QState ((Fin m → ZMod A) × (Fin n → ZMod A))) :
    Run oracle (additions (sparseComponents g)) ψ =
      ApplyGate (AddOracle (LinearCodeProgram.encode g)) ψ := by
  rw [run_additions, sparse_sum]

omit [NeZero A] in

/-- The generator support size equals the sum, over rows, of the number of nonzero entries in
each row. -/
theorem support_card (g : Fin m → Fin n → ZMod A) :
    (support g).card = ∑ i, (Finset.univ.filter (fun j => g i j ≠ 0)).card := by
  simp [support, Finset.card_filter, Fintype.sum_prod_type]

end Qatlib.Papers.SingleQuery97.MainResults.EncoderCircuit
