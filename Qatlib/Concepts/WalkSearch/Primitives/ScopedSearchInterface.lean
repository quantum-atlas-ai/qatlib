/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.TriangleContracts
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical

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

structure SearchCallScope where
  databaseBound : ℕ
  floorBound : ℕ
  checkerBound : ℕ

def SearchCallScope.contains (scope : SearchCallScope) (N check floor : ℕ) : Prop :=
  N≤ scope.databaseBound ∧ floor≤ scope.floorBound ∧ check≤ scope.checkerBound

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

def operationalSgsFind (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α → Bool)
    (check floor : ℕ) (ρ : sgs.seed) : Option α :=
  (sgs.run (fun i=>marked ((Fintype.equivFin α).symm i)) check floor ρ).map (fun i=>(Fintype.equivFin α).symm i)

def operationalSgsFindCost (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α → Bool)
    (check floor : ℕ) (ρ : sgs.seed) : ℕ :=
  sgs.cost (fun i=>marked ((Fintype.equivFin α).symm i)) check floor ρ

theorem operationalSgsFind_sound (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α → Bool)
    (check floor : ℕ) (ρ : sgs.seed) (x : α) (h : operationalSgsFind sgs marked check floor ρ=some x) : marked x=true := by
  cases hr : sgs.run (fun i=>marked ((Fintype.equivFin α).symm i)) check floor ρ with
  | none=>simp only [operationalSgsFind,hr,Option.map_none] at h;cases h
  | some i=>
    have hm:=sgs.sound _ check floor ρ hr
    have he : (Fintype.equivFin α).symm i=x := by
      simpa only [operationalSgsFind,hr,Option.map_some,Option.some.injEq] using h
    simpa only [he] using hm

theorem ScopedGroverFamily.execution_run_supported (family : ScopedGroverFamily) (scope : SearchCallScope)
    {N : ℕ} (marked : Fin N→Bool) (check floor : ℕ) (h : scope.contains N check floor) (ρ : family.seed scope) :
    (family.execution scope).run marked check floor ρ=family.run scope marked check floor h ρ := by
  simp only [ScopedGroverFamily.execution,dif_pos h]

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
