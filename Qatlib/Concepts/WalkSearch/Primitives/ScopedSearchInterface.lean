/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.TriangleContracts

/-!
# Scoped search execution interfaces

`SGSExecution` packages sound search execution and cost bounds, while `ScopedGroverFamily`
supplies finite randomness and failure bounds for calls within a `SearchCallScope`. The
conversion to an execution rejects unsupported calls and preserves supported calls and their
failure bounds.

These interfaces express finite versions of the search guarantees studied in [BoyerEtAl1998].

## Main statements

* `ScopedGroverFamily.execution`: obtain an execution from a scoped family.
* `operationalSgsFind_sound`: transport soundness to an arbitrary finite type.
* `ScopedGroverFamily.execution_finds_supported`: preserve the supported-call failure bound.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical

/-- Search execution with a finite nonempty seed type, soundness, rejection on unmarked inputs,
and a stated cost bound. -/
structure SGSExecution where
  seed : Type
  [seedFin : Fintype seed]
  [seedNe : Nonempty seed]
  cExp : ℕ
  κ : ℕ
  run : {N : ℕ} → (Fin N → Bool) → (check floor : ℕ) → seed → Option (Fin N)
  cost : {N : ℕ} → (Fin N → Bool) → (check floor : ℕ) → seed → ℕ
  sound : ∀ {N} (marked : Fin N → Bool) (check floor : ℕ) (ρ : seed) {x : Fin N},
    run marked check floor ρ=some x → marked x=true
  reject : ∀ {N} (marked : Fin N → Bool) (check floor : ℕ) (ρ : seed),
    (∀ x,marked x=false) → run marked check floor ρ=none
  charges : ∀ {N} (marked : Fin N → Bool) (check floor : ℕ) (ρ : seed),
    cost marked check floor ρ≤ κ*(Nat.log 2 (max N floor+1)+2)*(check+1)*(Nat.sqrt (max N floor+1)+1)

/-- Upper bounds on database size, failure-floor parameter, and checker cost for a family of
search calls. -/
structure SearchCallScope where
  databaseBound : ℕ
  floorBound : ℕ
  checkerBound : ℕ

/-- A call is supported when its database size, floor, and checker cost lie within the
corresponding scope bounds. -/
def SearchCallScope.contains (scope : SearchCallScope) (N check floor : ℕ) : Prop :=
  N≤ scope.databaseBound ∧ floor≤ scope.floorBound ∧ check≤ scope.checkerBound

/-- A family of search procedures with finite nonempty seed spaces for each scope and
correctness, failure-count, and cost guarantees for supported calls. -/
structure ScopedGroverFamily where
  cExp : ℕ
  κ : ℕ
  seed : SearchCallScope → Type
  seedFin : ∀ scope,Fintype (seed scope)
  seedNe : ∀ scope,Nonempty (seed scope)
  run : (scope : SearchCallScope) → {N : ℕ} → (marked : Fin N → Bool) → (check floor : ℕ) →
    scope.contains N check floor → seed scope → Option (Fin N)
  cost : (scope : SearchCallScope) → {N : ℕ} → (marked : Fin N → Bool) → (check floor : ℕ) →
    scope.contains N check floor → seed scope → ℕ
  sound : ∀ scope {N} (marked : Fin N → Bool) (check floor : ℕ) (h : scope.contains N check floor)
    (ρ : seed scope) {x : Fin N},run scope marked check floor h ρ=some x → marked x=true
  reject : ∀ scope {N} (marked : Fin N → Bool) (check floor : ℕ) (h : scope.contains N check floor)
    (ρ : seed scope),(∀ x,marked x=false) → run scope marked check floor h ρ=none
  finds : ∀ scope {N} (marked : Fin N → Bool) (check floor : ℕ) (h : scope.contains N check floor),
    (∃ x,marked x=true) →
      letI:=seedFin scope
      (Finset.univ.filter (fun ρ : seed scope=>run scope marked check floor h ρ=none)).card*
        (max N floor+1)^cExp≤ Fintype.card (seed scope)
  charges : ∀ scope {N} (marked : Fin N → Bool) (check floor : ℕ) (h : scope.contains N check floor) (ρ : seed scope),
    cost scope marked check floor h ρ≤ κ*(Nat.log 2 (max N floor+1)+2)*(check+1)*(Nat.sqrt (max N floor+1)+1)

/-- Converts a scoped family to an execution, using the family on supported calls and returning
`none` at zero cost otherwise. -/
def ScopedGroverFamily.execution (family : ScopedGroverFamily) (scope : SearchCallScope) : SGSExecution where
  seed:=family.seed scope
  seedFin:=family.seedFin scope
  seedNe:=family.seedNe scope
  cExp:=family.cExp
  κ:=family.κ
  run:=fun {N} marked check floor ρ=>if h : scope.contains N check floor then family.run scope marked check floor h ρ else none
  cost:=fun {N} marked check floor ρ=>if h : scope.contains N check floor then family.cost scope marked check floor h ρ else 0
  sound:=by
    intro N marked check floor ρ x hx
    split_ifs at hx with h
    · exact family.sound scope marked check floor h ρ hx
  reject:=by
    intro N marked check floor ρ hm
    split_ifs with h
    · exact family.reject scope marked check floor h ρ hm
    · rfl
  charges:=by
    intro N marked check floor ρ
    split_ifs with h
    · exact family.charges scope marked check floor h ρ
    · exact Nat.zero_le _

/-- Runs an `SGSExecution` on an arbitrary finite type by transporting the predicate and result
through `Fintype.equivFin`. -/
def operationalSgsFind (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α → Bool)
    (check floor : ℕ) (ρ : sgs.seed) : Option α :=
  (sgs.run (fun i=>marked ((Fintype.equivFin α).symm i)) check floor ρ).map (fun i=>(Fintype.equivFin α).symm i)

/-- The execution cost of the search transported to an arbitrary finite type through
`Fintype.equivFin`. -/
def operationalSgsFindCost (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α → Bool)
    (check floor : ℕ) (ρ : sgs.seed) : ℕ :=
  sgs.cost (fun i=>marked ((Fintype.equivFin α).symm i)) check floor ρ

/-- Any value returned by `operationalSgsFind` satisfies the marked predicate. -/
theorem operationalSgsFind_sound (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α → Bool)
    (check floor : ℕ) (ρ : sgs.seed) (x : α) (h : operationalSgsFind sgs marked check floor ρ=some x) : marked x=true := by
  cases hr : sgs.run (fun i=>marked ((Fintype.equivFin α).symm i)) check floor ρ with
  | none=>simp only [operationalSgsFind,hr,Option.map_none] at h;cases h
  | some i=>
    have hm:=sgs.sound _ check floor ρ hr
    have he : (Fintype.equivFin α).symm i=x := by
      simpa only [operationalSgsFind,hr,Option.map_some,Option.some.injEq] using h
    simpa only [he] using hm

/-- On supported calls, the converted execution has exactly the result of the original scoped
family. -/
theorem ScopedGroverFamily.execution_run_supported (family : ScopedGroverFamily) (scope : SearchCallScope)
    {N : ℕ} (marked : Fin N→Bool) (check floor : ℕ) (h : scope.contains N check floor) (ρ : family.seed scope) :
    (family.execution scope).run marked check floor ρ=family.run scope marked check floor h ρ := by
  simp only [ScopedGroverFamily.execution,dif_pos h]

/-- For a supported call with a marked element, the converted execution satisfies the family's
inverse-power failure-count bound. -/
theorem ScopedGroverFamily.execution_finds_supported (family : ScopedGroverFamily) (scope : SearchCallScope)
    {N : ℕ} (marked : Fin N→Bool) (check floor : ℕ) (h : scope.contains N check floor)
    (hm : ∃ x,marked x=true) :
    letI:=family.seedFin scope
    (Finset.univ.filter (fun ρ : family.seed scope=>(family.execution scope).run marked check floor ρ=none)).card*
      (max N floor+1)^family.cExp≤Fintype.card (family.seed scope) := by
  letI:=family.seedFin scope
  simpa only [family.execution_run_supported scope marked check floor h] using
      family.finds scope marked check floor h hm
end Qatlib.Concepts.WalkSearch.Primitives
