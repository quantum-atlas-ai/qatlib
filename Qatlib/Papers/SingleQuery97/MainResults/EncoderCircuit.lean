/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.LinearCodeProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.EncoderCircuit

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.CyclicRecovery

section Additions
variable {I R : Type} [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [AddCommGroup R]

noncomputable def additions (fs : List (I → R)) : Circuit (I × R) :=
  fs.map (fun f => Step.gate (AddOracle f))

omit [Fintype I] [Fintype R] in

theorem additions_resources (fs : List (I → R)) :
    QueryCount (additions fs) = 0 ∧ GateCount (additions fs) = fs.length := by
  induction fs with
  | nil => exact ⟨rfl, rfl⟩
  | cons f fs ih => simpa [additions] using ih

theorem additions_unitary (fs : List (I → R)) : IsUnitaryCircuit (additions fs) := by
  induction fs with
  | nil => exact isUnitaryCircuit_nil
  | cons f fs ih =>
    exact (isUnitaryCircuit_gate _ _).2 ⟨addOracle_unitary f, ih⟩

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

def component (g : Fin m → Fin n → ZMod A) (p : Fin m × Fin n)
    (s : Fin m → ZMod A) : Fin n → ZMod A := Pi.single p.2 (s p.1 * g p.1 p.2)

noncomputable def components (g : Fin m → Fin n → ZMod A) :
    List ((Fin m → ZMod A) → (Fin n → ZMod A)) :=
  (Finset.univ : Finset (Fin m × Fin n)).toList.map (component g)

omit [NeZero A] in

theorem component_apply (g : Fin m → Fin n → ZMod A) (i : Fin m) (j t : Fin n)
    (s : Fin m → ZMod A) :
    component g (i,j) s t = if t = j then s i * g i j else 0 := by
  simp [component, Pi.single_apply]

omit [NeZero A] in

theorem components_sum (g : Fin m → Fin n → ZMod A) :
    (components g).sum = LinearCodeProgram.encode g := by
  classical
  rw [components, Finset.sum_map_toList]
  funext s j
  simp only [Finset.sum_apply, Fintype.sum_prod_type, component, Pi.single_apply]
  simp [LinearCodeProgram.encode]

omit [NeZero A] in

theorem encoder_resources (g : Fin m → Fin n → ZMod A) :
    QueryCount (additions (components g)) = 0 ∧
    GateCount (additions (components g)) = m*n := by
  have h := additions_resources (components g)
  simpa [components] using h

theorem compiled_encoder (g : Fin m → Fin n → ZMod A)
    (oracle : Matrix ((Fin m → ZMod A) × (Fin n → ZMod A))
      ((Fin m → ZMod A) × (Fin n → ZMod A)) ℂ)
    (ψ : QState ((Fin m → ZMod A) × (Fin n → ZMod A))) :
    Run oracle (additions (components g)) ψ =
      ApplyGate (AddOracle (LinearCodeProgram.encode g)) ψ := by
  rw [run_additions, components_sum]

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

def support (g : Fin m → Fin n → ZMod A) : Finset (Fin m × Fin n) :=
  Finset.univ.filter (fun p => g p.1 p.2 ≠ 0)

noncomputable def sparseComponents (g : Fin m → Fin n → ZMod A) :
    List ((Fin m → ZMod A) → (Fin n → ZMod A)) := (support g).toList.map (component g)

omit [NeZero A] in

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

theorem sparse_resources (g : Fin m → Fin n → ZMod A) :
    QueryCount (additions (sparseComponents g)) = 0 ∧
    GateCount (additions (sparseComponents g)) = (support g).card := by
  simpa [sparseComponents] using additions_resources (sparseComponents g)

theorem run_sparse (g : Fin m → Fin n → ZMod A)
    (oracle : Matrix ((Fin m → ZMod A) × (Fin n → ZMod A))
      ((Fin m → ZMod A) × (Fin n → ZMod A)) ℂ)
    (ψ : QState ((Fin m → ZMod A) × (Fin n → ZMod A))) :
    Run oracle (additions (sparseComponents g)) ψ =
      ApplyGate (AddOracle (LinearCodeProgram.encode g)) ψ := by
  rw [run_additions, sparse_sum]

omit [NeZero A] in

theorem support_card (g : Fin m → Fin n → ZMod A) :
    (support g).card = ∑ i, (Finset.univ.filter (fun j => g i j ≠ 0)).card := by
  simp [support, Finset.card_filter, Fintype.sum_prod_type]

end Qatlib.Papers.SingleQuery97.MainResults.EncoderCircuit
