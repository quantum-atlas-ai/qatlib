/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Armillary26.RoutingModel.Cyclic
public import Qatlib.Papers.Armillary26.Pairing.Internal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Internal semidirect form of cyclic routed interactions

Cell transport through the actual cyclic route is an internal action on each
fixed role rail and group.  Even matchings compose this action with a channel
permutation, while odd matchings compose it with a channel-dependent station
shift.  The resulting invariant shows that every effective interaction belongs
to the internal semidirect product used by the pairing theory.
-/

namespace Qatlib.Papers.Armillary26.RoutingModel

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Papers.Armillary26.Pairing

/-- A permutation has internal semidirect form for some shifts and channels. -/
def IntForm {p q : ℕ} (e : Equiv.Perm (ZMod p × Fin q)) : Prop :=
  ∃ (ell : Fin q → ZMod p) (sigma : Equiv.Perm (Fin q)), e = intAct ell sigma

/-- Internal semidirect forms are closed under composition. -/
theorem int_mul {p q : ℕ} {e e' : Equiv.Perm (ZMod p × Fin q)}
    (he : IntForm e) (he' : IntForm e') : IntForm (e * e') := by
  rcases he with ⟨ell, sigma, rfl⟩
  rcases he' with ⟨ell', sigma', rfl⟩
  exact ⟨_, _, intAct_mul ell ell' sigma sigma'⟩

/-- Internal semidirect forms are closed under inversion. -/
theorem int_inv {p q : ℕ} {e : Equiv.Perm (ZMod p × Fin q)}
    (he : IntForm e) : IntForm e⁻¹ := by
  rcases he with ⟨ell, sigma, rfl⟩
  exact ⟨_, _, intAct_inv ell sigma⟩

/-- Inverting a transported permutation swaps its source and target relabelings. -/
theorem role_inv {α β γ : Type*} (f : α ≃ β) (ra : γ ≃ α) (rb : γ ≃ β) :
    (roleMap f ra rb)⁻¹ = roleMap f.symm rb ra := by
  apply Equiv.ext
  intro x
  simp [roleMap]

/-- Composing transported maps composes their maps and cancels middle relabelings. -/
theorem role_mul {α β ε ι : Type*} (f : β ≃ ε) (g : α ≃ β)
    (ra : ι ≃ α) (rb : ι ≃ β) (rc : ι ≃ ε) :
    roleMap f rb rc * roleMap g ra rb = roleMap (g.trans f) ra rc := by
  apply Equiv.ext
  intro x
  simp [roleMap, Equiv.Perm.mul_apply]

/-- The physical column corresponding to a role rail and group. -/
def colE (s : RouteParam) (h : ℕ) (r : Bool) (g : ZMod (s.m + s.m)) :
    ZMod (s.m + s.m) :=
  if r then -g - (h : ℕ) else -g + (h : ℕ)

/-- An even-invariant transport restricts from physical cells to role cells. -/
def eCell (s : RouteParam) (h : ℕ) {rho : Equiv.Perm (Pos s)}
    (hi : EvenInv s h rho) (r : Bool) (g : ZMod (s.m + s.m)) :
    Cell s r (colE s h r g) ≃ Cell s r g :=
  rho.subtypeEquiv (by
    intro x
    constructor
    · intro hx
      have hr : (rho x).rail = r := (hi.1 x).trans hx.1
      refine ⟨hr, ?_⟩
      have hc := hi.2 x
      rw [hr, hx.2] at hc
      rw [hc]
      cases r <;> simp [colE]
    · intro hy
      have hr : x.rail = r := by
        rw [← hi.1 x]
        exact hy.1
      refine ⟨hr, ?_⟩
      have hc := hi.2 x
      rw [hy.1, hy.2] at hc
      cases r <;> simp [colE] at hc ⊢ <;> rw [hc] <;> ring)

/-- An odd-invariant transport restricts from complementary physical cells. -/
def oCell (s : RouteParam) (h : ℕ) {rho : Equiv.Perm (Pos s)}
    (hi : OddInv s h rho) (r : Bool) (g : ZMod (s.m + s.m)) :
    Cell s (!r) (colE s h r g) ≃ Cell s r g :=
  rho.subtypeEquiv (by
    intro x
    constructor
    · intro hx
      have hr : (rho x).rail = r := by
        rw [hi.1 x, hx.1]
        cases r <;> rfl
      refine ⟨hr, ?_⟩
      have hc := hi.2 x
      rw [hr, hx.2] at hc
      rw [hc]
      cases r <;> simp [colE]
    · intro hy
      have hr : x.rail = !r := by
        have hb := congrArg (fun b : Bool => !b) ((hi.1 x).symm.trans hy.1)
        simpa using hb
      refine ⟨hr, ?_⟩
      have hc := hi.2 x
      rw [hy.1, hy.2] at hc
      cases r <;> simp [colE] at hc ⊢ <;> rw [hc] <;> ring)

/-- Internal coordinates for one even-invariant cell transport. -/
def eMap (s : RouteParam) (h : ℕ) {rho : Equiv.Perm (Pos s)}
    (hi : EvenInv s h rho) (r : Bool) (g : ZMod (s.m + s.m)) :
    Equiv.Perm (ZMod s.p × Fin s.q) :=
  roleMap (eCell s h hi r g) (intRole s r (colE s h r g)) (intRole s r g)

/-- Internal coordinates for one odd-invariant cell transport. -/
def oMap (s : RouteParam) (h : ℕ) {rho : Equiv.Perm (Pos s)}
    (hi : OddInv s h rho) (r : Bool) (g : ZMod (s.m + s.m)) :
    Equiv.Perm (ZMod s.p × Fin s.q) :=
  roleMap (oCell s h hi r g) (intRole s (!r) (colE s h r g)) (intRole s r g)

/-- An even transport has internal semidirect form on every role cell. -/
def EForm (s : RouteParam) (h : ℕ) (rho : Equiv.Perm (Pos s)) : Prop :=
  ∃ hi : EvenInv s h rho, ∀ r g, IntForm (eMap s h hi r g)

/-- An odd transport has internal semidirect form on every role cell. -/
def OForm (s : RouteParam) (h : ℕ) (rho : Equiv.Perm (Pos s)) : Prop :=
  ∃ hi : OddInv s h rho, ∀ r g, IntForm (oMap s h hi r g)

/-- The channel permutation induced by an even matching on a role cell. -/
def evenPi (s : RouteParam) (h : Fin s.m) (r : Bool) (g : ZMod (s.m + s.m)) :
    Equiv.Perm (Fin s.q) :=
  let a : ZMod (s.m + s.m) := -colE s h r g - (h : ℕ)
  if r then (s.perm a h).symm else s.perm a h

/-- An even matching appends its channel permutation to cell transport. -/
theorem even_map (s : RouteParam) (h : Fin s.m) {rho : Equiv.Perm (Pos s)}
    (hi : EvenInv s h rho) (ho : OddInv s h ((evenPerm s h).trans rho))
    (r : Bool) (g : ZMod (s.m + s.m)) :
    oMap s h ho r g = eMap s h hi r g * intAct (fun _ => 0) (evenPi s h r g) := by
  apply Equiv.ext
  rintro ⟨i, j⟩
  cases r <;>
    simp [oMap, eMap, oCell, eCell, roleMap, intRole, intAct, evenPi,
      Equiv.subtypeEquiv_apply, Equiv.Perm.mul_apply, evenPerm, evenMap, colE] <;>
    constructor <;> rfl

/-- Even matching preserves internal semidirect cell transport. -/
theorem even_form (s : RouteParam) (h : Fin s.m) {rho : Equiv.Perm (Pos s)}
    (hf : EForm s h rho) : OForm s h ((evenPerm s h).trans rho) := by
  rcases hf with ⟨hi, hf⟩
  refine ⟨even_step s h hi, ?_⟩
  intro r g
  rw [even_map s h hi (even_step s h hi) r g]
  exact int_mul (hf r g) ⟨_, _, rfl⟩

/-- The station shift induced by an odd matching on a role cell. -/
def oddSh (s : RouteParam) (h : Fin s.m) (r : Bool) (g : ZMod (s.m + s.m)) :
    Fin s.q → ZMod s.p :=
  if r then fun j => -s.shift g h j else fun j => s.shift (g - 2 * (h : ℕ) - 1) h j

/-- An odd matching appends its station shift to cell transport. -/
theorem odd_map (s : RouteParam) (h : Fin s.m) {rho : Equiv.Perm (Pos s)}
    (ho : OddInv s h rho) (he : EvenInv s (h + 1) ((oddPerm s h).trans rho))
    (r : Bool) (g : ZMod (s.m + s.m)) :
    eMap s (h + 1) he r g = oMap s h ho r g * intAct (oddSh s h r g) (Equiv.refl _) := by
  apply Equiv.ext
  rintro ⟨i, j⟩
  cases r <;>
    simp [eMap, oMap, eCell, oCell, roleMap, intRole, intAct, oddSh,
      Equiv.subtypeEquiv_apply, Equiv.Perm.mul_apply, oddPerm, oddMap, colE,
      Nat.cast_add, Nat.cast_one] <;>
    constructor <;> congr 1 <;> ext <;> ring_nf <;> rfl

/-- Odd matching preserves internal semidirect cell transport. -/
theorem odd_form (s : RouteParam) (h : Fin s.m) {rho : Equiv.Perm (Pos s)}
    (hf : OForm s h rho) : EForm s (h + 1) ((oddPerm s h).trans rho) := by
  rcases hf with ⟨hi, hf⟩
  refine ⟨odd_step s h hi, ?_⟩
  intro r g
  rw [odd_map s h hi (odd_step s h hi) r g]
  exact int_mul (hf r g) ⟨_, _, rfl⟩

/-- The initial role transport is the identity internal action on each cell. -/
theorem init_form (s : RouteParam) : EForm s 0 (initPerm s) := by
  refine ⟨init_inv s, ?_⟩
  intro r g
  refine ⟨fun _ => 0, Equiv.refl _, ?_⟩
  apply Equiv.ext
  rintro ⟨i, j⟩
  cases r <;> simp [eMap, eCell, roleMap, intRole, initPerm, initRole, colE, intAct]

/-- Every route prefix has internal semidirect cell transport. -/
theorem before_form (s : RouteParam) (h : ℕ) (hh : h ≤ s.m) :
    EForm s h (before s h hh) := by
  induction h with
  | zero => exact init_form s
  | succ h ih =>
    have hl : h ≤ s.m := by omega
    have hf : h < s.m := by omega
    have he := even_form s ⟨h, hf⟩ (ih hl)
    have ho := odd_form s ⟨h, hf⟩ he
    simpa [before, hl] using ho

/-- Every route step has phase-appropriate internal semidirect cell transport. -/
theorem during_form (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) :
    (t % 2 = 0 → EForm s (t / 2) (during s t ht)) ∧
      (t % 2 ≠ 0 → OForm s (t / 2) (during s t ht)) := by
  constructor
  · intro he
    simp only [during, he, ↓reduceIte]
    exact before_form s (t / 2) (by omega)
  · intro ho
    simp only [during, ho, ↓reduceIte]
    exact even_form s ⟨t / 2, by omega⟩ (before_form s (t / 2) (by omega))

/-- An even matching restricted to its physical source and target cells. -/
def evSub (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) (he : t % 2 = 0)
    (a : ZMod (s.m + s.m)) :
    Cell s true (colE s (t / 2) true a) ≃
      Cell s false (colE s (t / 2) false (a + (t : ℕ))) :=
  (evenPerm s ⟨t / 2, by omega⟩).subtypeEquiv (by
    intro x
    have hnat : t = 2 * (t / 2) := by omega
    have hcast : (t : ZMod (s.m + s.m)) =
        2 * ((t / 2 : ℕ) : ZMod (s.m + s.m)) := by
      have hc := congrArg (fun n : ℕ => (n : ZMod (s.m + s.m))) hnat
      push_cast at hc
      exact hc
    have hc : colE s (t / 2) false (a + (t : ℕ)) = colE s (t / 2) true a := by
      change -(a + (t : ZMod (s.m + s.m))) + ((t / 2 : ℕ) : ZMod (s.m + s.m)) =
        -a - ((t / 2 : ℕ) : ZMod (s.m + s.m))
      rw [hcast]
      ring
    cases hx : x.rail <;> simp [evenPerm, evenMap, hx, hc])

/-- The even matching on physical-cell internal coordinates. -/
def evMap (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) (he : t % 2 = 0)
    (a : ZMod (s.m + s.m)) : Equiv.Perm (ZMod s.p × Fin s.q) :=
  roleMap (evSub s t ht he a) (intRole s true (colE s (t / 2) true a))
    (intRole s false (colE s (t / 2) false (a + (t : ℕ))))

/-- An even physical matching has zero shift and its source channel permutation. -/
theorem evMap_form (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) (he : t % 2 = 0)
    (a : ZMod (s.m + s.m)) : IntForm (evMap s t ht he a) := by
  refine ⟨fun _ => 0, s.perm a ⟨t / 2, by omega⟩, ?_⟩
  apply Equiv.ext
  rintro ⟨i, j⟩
  simp [evMap, evSub, roleMap, intRole, intAct, Equiv.subtypeEquiv_apply,
    evenPerm, evenMap, colE]

/-- An odd matching restricted to its physical source and target cells. -/
def odSub (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) (ho : t % 2 ≠ 0)
    (a : ZMod (s.m + s.m)) :
    Cell s false (colE s (t / 2) true a) ≃
      Cell s true (colE s (t / 2) false (a + (t : ℕ))) :=
  (oddPerm s ⟨t / 2, by omega⟩).subtypeEquiv (by
    intro x
    have hnat : t = 2 * (t / 2) + 1 := by omega
    have hcast : (t : ZMod (s.m + s.m)) =
        2 * ((t / 2 : ℕ) : ZMod (s.m + s.m)) + 1 := by
      have hc := congrArg (fun n : ℕ => (n : ZMod (s.m + s.m))) hnat
      push_cast at hc
      exact hc
    have hc : colE s (t / 2) true a - 1 =
        colE s (t / 2) false (a + (t : ℕ)) := by
      change -a - ((t / 2 : ℕ) : ZMod (s.m + s.m)) - 1 =
        -(a + (t : ZMod (s.m + s.m))) + ((t / 2 : ℕ) : ZMod (s.m + s.m))
      rw [hcast]
      ring
    cases hx : x.rail <;> simp [oddPerm, oddMap, hx, ← hc])

/-- The odd matching on physical-cell internal coordinates. -/
def odMap (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) (ho : t % 2 ≠ 0)
    (a : ZMod (s.m + s.m)) : Equiv.Perm (ZMod s.p × Fin s.q) :=
  roleMap (odSub s t ht ho a) (intRole s false (colE s (t / 2) true a))
    (intRole s true (colE s (t / 2) false (a + (t : ℕ))))

/-- An odd physical matching has its source station shift and identity channels. -/
theorem odMap_form (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) (ho : t % 2 ≠ 0)
    (a : ZMod (s.m + s.m)) : IntForm (odMap s t ht ho a) := by
  refine ⟨s.shift a ⟨t / 2, by omega⟩, Equiv.refl _, ?_⟩
  apply Equiv.ext
  rintro ⟨i, j⟩
  simp [odMap, odSub, roleMap, intRole, intAct, Equiv.subtypeEquiv_apply,
    oddPerm, oddMap, colE]

/-- Even cell transports and their matching compose to the effective role cell map. -/
theorem even_sub (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) (he : t % 2 = 0)
    (a : ZMod (s.m + s.m)) (hi : EvenInv s (t / 2) (during s t ht)) :
    (eCell s (t / 2) hi true a).symm.trans
        ((evSub s t ht he a).trans
          (eCell s (t / 2) hi false (a + (t : ℕ)))) = effSub s t ht a := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp [eCell, evSub, effSub, effRole, roleMap, stepPerm, he,
    Equiv.subtypeEquiv_apply]

/-- Odd cell transports and their matching compose to the effective role cell map. -/
theorem odd_sub (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) (ho : t % 2 ≠ 0)
    (a : ZMod (s.m + s.m)) (hi : OddInv s (t / 2) (during s t ht)) :
    (oCell s (t / 2) hi true a).symm.trans
        ((odSub s t ht ho a).trans
          (oCell s (t / 2) hi false (a + (t : ℕ)))) = effSub s t ht a := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp [oCell, odSub, effSub, effRole, roleMap, stepPerm, ho,
    Equiv.subtypeEquiv_apply]

/-- At an even step, effective interaction factors through three internal actions. -/
theorem even_eff (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) (he : t % 2 = 0)
    (a : ZMod (s.m + s.m)) (hi : EvenInv s (t / 2) (during s t ht)) :
    effInt s t ht a = eMap s (t / 2) hi false (a + (t : ℕ)) * evMap s t ht he a *
      (eMap s (t / 2) hi true a)⁻¹ := by
  simp only [eMap, evMap, role_inv, role_mul]
  rw [effInt_eq, even_sub s t ht he a hi]

/-- At an odd step, effective interaction factors through three internal actions. -/
theorem odd_eff (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) (ho : t % 2 ≠ 0)
    (a : ZMod (s.m + s.m)) (hi : OddInv s (t / 2) (during s t ht)) :
    effInt s t ht a = oMap s (t / 2) hi false (a + (t : ℕ)) * odMap s t ht ho a *
      (oMap s (t / 2) hi true a)⁻¹ := by
  simp only [oMap, odMap, role_inv]
  dsimp only [Bool.not]
  rw [role_mul, role_mul, effInt_eq, odd_sub s t ht ho a hi]

/-- Every effective interaction from the actual route has internal semidirect form. -/
theorem effInt_form (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m)
    (a : ZMod (s.m + s.m)) : IntForm (effInt s t ht a) := by
  by_cases he : t % 2 = 0
  · rcases (during_form s t ht).1 he with ⟨hi, hf⟩
    rw [even_eff s t ht he a hi]
    exact int_mul (int_mul (hf false (a + (t : ℕ))) (evMap_form s t ht he a))
      (int_inv (hf true a))
  · rcases (during_form s t ht).2 he with ⟨hi, hf⟩
    rw [odd_eff s t ht he a hi]
    exact int_mul (int_mul (hf false (a + (t : ℕ))) (odMap_form s t ht he a))
      (int_inv (hf true a))

end Qatlib.Papers.Armillary26.RoutingModel
