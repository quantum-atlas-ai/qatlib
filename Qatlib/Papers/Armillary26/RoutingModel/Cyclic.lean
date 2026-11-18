/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Armillary26.RoutingModel.Routing
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Cyclic Armillary routing from channel permutations and shifts

Physical positions carry a rail, cyclic module column, cyclic station, and
channel. Even and odd matchings are explicit fixed-point-free involutions.
Transporting the initial roles through these matchings proves the manuscript's
visit law `b = a + t`, unique round times, and the transported-interaction
formula. Internal role labels then induce one permutation per effective block.
-/

namespace Qatlib.Papers.Armillary26.RoutingModel

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodeCert.PermBlocks

/-- Generic cyclic routing parameters; `m + m` is the even module count. -/
structure RouteParam where
  m : ℕ
  p : ℕ
  q : ℕ
  hm : 0 < m
  hp : 0 < p
  hq : 0 < q
  perm : ZMod (m + m) → Fin m → Equiv.Perm (Fin q)
  shift : ZMod (m + m) → Fin m → Fin q → ZMod p

/-- A physical position, also used as an initial role label. -/
@[ext]
structure Pos (s : RouteParam) where
  rail : Bool
  col : ZMod (s.m + s.m)
  sta : ZMod s.p
  chan : Fin s.q

/-- Initial roles start at the negated module column. -/
def initRole {s : RouteParam} (x : Pos s) : Pos s :=
  { rail := x.rail, col := -x.col, sta := x.sta, chan := x.chan }

/-- Initial role assignment is a bijection. -/
def initPerm (s : RouteParam) : Equiv.Perm (Pos s) where
  toFun := initRole
  invFun := initRole
  left_inv x := by cases x; simp [initRole]
  right_inv x := by cases x; simp [initRole]

/-- The even matching directed from a syndrome position to its data partner. -/
def evenMap (s : RouteParam) (h : Fin s.m) (x : Pos s) : Pos s :=
  let a : ZMod (s.m + s.m) := -x.col - (h : ℕ)
  if x.rail then
    { rail := false, col := x.col, sta := x.sta, chan := s.perm a h x.chan }
  else
    { rail := true, col := x.col, sta := x.sta, chan := (s.perm a h).symm x.chan }

/-- The odd matching directed from a data position to its syndrome partner. -/
def oddMap (s : RouteParam) (h : Fin s.m) (x : Pos s) : Pos s :=
  if x.rail then
    let c : ZMod (s.m + s.m) := x.col + 1
    let a : ZMod (s.m + s.m) := -c - (h : ℕ)
    { rail := false, col := c, sta := x.sta - s.shift a h x.chan, chan := x.chan }
  else
    let a : ZMod (s.m + s.m) := -x.col - (h : ℕ)
    { rail := true, col := x.col - 1, sta := x.sta + s.shift a h x.chan, chan := x.chan }

/-- The even matching is an involution. -/
theorem evenInvol (s : RouteParam) (h : Fin s.m) :
    Function.Involutive (evenMap s h) := by
  intro x
  cases x with
  | mk rail col sta chan => cases rail <;> ext <;> simp [evenMap]

/-- The odd matching is an involution. -/
theorem oddInvol (s : RouteParam) (h : Fin s.m) :
    Function.Involutive (oddMap s h) := by
  intro x
  cases x with
  | mk rail col sta chan => cases rail <;> ext <;> simp [oddMap]

/-- The even matching as a position permutation. -/
def evenPerm (s : RouteParam) (h : Fin s.m) : Equiv.Perm (Pos s) :=
  (evenInvol s h).toPerm

/-- The odd matching as a position permutation. -/
def oddPerm (s : RouteParam) (h : Fin s.m) : Equiv.Perm (Pos s) :=
  (oddInvol s h).toPerm

/-- Roles and physical rails agree before an even matching, with the group-column law. -/
def EvenInv (s : RouteParam) (h : ℕ) (ρ : Equiv.Perm (Pos s)) : Prop :=
  (∀ x, (ρ x).rail = x.rail) ∧
    ∀ x, (ρ x).col = if (ρ x).rail then -x.col - (h : ℕ) else -x.col + (h : ℕ)

/-- Roles and physical rails are complementary before an odd matching. -/
def OddInv (s : RouteParam) (h : ℕ) (ρ : Equiv.Perm (Pos s)) : Prop :=
  (∀ x, (ρ x).rail = !x.rail) ∧
    ∀ x, (ρ x).col = if (ρ x).rail then -x.col - (h : ℕ) else -x.col + (h : ℕ)

/-- The initial role assignment satisfies the even-phase invariant. -/
theorem init_inv (s : RouteParam) : EvenInv s 0 (initPerm s) := by
  constructor
  · intro x
    rfl
  · intro x
    cases x with
    | mk rail col sta chan => cases rail <;> simp [initPerm, initRole]

/-- An even matching transports the even invariant to the odd invariant. -/
theorem even_step (s : RouteParam) (h : Fin s.m) {ρ : Equiv.Perm (Pos s)}
    (hi : EvenInv s h ρ) : OddInv s h ((evenPerm s h).trans ρ) := by
  rcases hi with ⟨hr, hg⟩
  constructor
  · intro x
    rw [Equiv.trans_apply, hr]
    cases hx : x.rail <;> simp [evenPerm, evenMap, hx]
  · intro x
    have hgx := hg (evenPerm s h x)
    have hrx := hr (evenPerm s h x)
    cases hx : x.rail
    · have hrole : (ρ (evenPerm s h x)).rail = true := by
        rw [hrx]
        simp [evenPerm, evenMap, hx]
      simp only [Equiv.trans_apply] at ⊢
      simp only [hrole] at hgx ⊢
      simpa [Equiv.trans_apply, evenPerm, evenMap, hx] using hgx
    · have hrole : (ρ (evenPerm s h x)).rail = false := by
        rw [hrx]
        simp [evenPerm, evenMap, hx]
      simp only [Equiv.trans_apply] at ⊢
      simp only [hrole] at hgx ⊢
      simpa [Equiv.trans_apply, evenPerm, evenMap, hx] using hgx

/-- An odd matching transports the odd invariant to the next even invariant. -/
theorem odd_step (s : RouteParam) (h : Fin s.m) {ρ : Equiv.Perm (Pos s)}
    (hi : OddInv s h ρ) : EvenInv s (h + 1) ((oddPerm s h).trans ρ) := by
  rcases hi with ⟨hr, hg⟩
  constructor
  · intro x
    rw [Equiv.trans_apply, hr]
    cases hx : x.rail <;> simp [oddPerm, oddMap, hx]
  · intro x
    have hgx := hg (oddPerm s h x)
    have hrx := hr (oddPerm s h x)
    cases hx : x.rail
    · have hrole : (ρ (oddPerm s h x)).rail = false := by
        rw [hrx]
        simp [oddPerm, oddMap, hx]
      simp only [Equiv.trans_apply] at ⊢
      simp only [hrole] at hgx ⊢
      simp [oddPerm, oddMap, hx, Nat.cast_add, Nat.cast_one] at hgx ⊢
      rw [hgx]
      ring
    · have hrole : (ρ (oddPerm s h x)).rail = true := by
        rw [hrx]
        simp [oddPerm, oddMap, hx]
      simp only [Equiv.trans_apply] at ⊢
      simp only [hrole] at hgx ⊢
      simp [oddPerm, oddMap, hx, Nat.cast_add, Nat.cast_one] at hgx ⊢
      rw [hgx]
      ring

/-- Role transport immediately before pair `h`. -/
def before (s : RouteParam) : (h : ℕ) → h ≤ s.m → Equiv.Perm (Pos s)
  | 0, _ => initPerm s
  | h + 1, hh =>
    let hf : Fin s.m := ⟨h, by omega⟩
    (oddPerm s hf).trans ((evenPerm s hf).trans (before s h (by omega)))

/-- Every prefix of the route satisfies the even-phase invariant. -/
theorem before_inv (s : RouteParam) (h : ℕ) (hh : h ≤ s.m) :
    EvenInv s h (before s h hh) := by
  induction h with
  | zero => exact init_inv s
  | succ h ih =>
    have hl : h ≤ s.m := by omega
    have hf : h < s.m := by omega
    have he := even_step s ⟨h, hf⟩ (ih hl)
    have ho := odd_step s ⟨h, hf⟩ he
    simpa [before, hl] using ho

/-- Role transport at any step of the full even-length round. -/
def during (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) : Equiv.Perm (Pos s) :=
  let h := t / 2
  let hh : h ≤ s.m := by omega
  if t % 2 = 0 then before s h hh
  else (evenPerm s ⟨h, by omega⟩).trans (before s h hh)

/-- The physical matching at any step of the full round. -/
def stepPerm (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) : Equiv.Perm (Pos s) :=
  let h := t / 2
  if t % 2 = 0 then evenPerm s ⟨h, by omega⟩ else oddPerm s ⟨h, by omega⟩

/-- Every step satisfies its phase-appropriate transport invariant. -/
theorem during_inv (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) :
    (t % 2 = 0 → EvenInv s (t / 2) (during s t ht)) ∧
      (t % 2 ≠ 0 → OddInv s (t / 2) (during s t ht)) := by
  constructor
  · intro he
    simp only [during, he, ↓reduceIte]
    exact before_inv s (t / 2) (by omega)
  · intro ho
    simp only [during, ho, ↓reduceIte]
    exact even_step s ⟨t / 2, by omega⟩ (before_inv s (t / 2) (by omega))

/-- Every matching step reverses the physical rail. -/
theorem step_rail (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) (x : Pos s) :
    (stepPerm s t ht x).rail = !x.rail := by
  by_cases he : t % 2 = 0
  · cases hx : x.rail <;> simp [stepPerm, he, evenPerm, evenMap, hx]
  · cases hx : x.rail <;> simp [stepPerm, he, oddPerm, oddMap, hx]

/-- Under the even invariant, the even partner carries the data role at `a + 2h`. -/
theorem visit_even (s : RouteParam) (h : Fin s.m) {ρ : Equiv.Perm (Pos s)}
    (hi : EvenInv s h ρ) (x : Pos s) (hx : (ρ x).rail = true) :
    (ρ (evenPerm s h x)).rail = false ∧
      (ρ (evenPerm s h x)).col = (ρ x).col + 2 * (h : ℕ) := by
  rcases hi with ⟨hr, hg⟩
  have hxr : x.rail = true := by rw [← hr x]; exact hx
  have hmr := hr (evenPerm s h x)
  have hmg := hg (evenPerm s h x)
  have hxg := hg x
  have hrole : (ρ (evenPerm s h x)).rail = false := by
    rw [hmr]
    simp [evenPerm, evenMap, hxr]
  refine ⟨hrole, ?_⟩
  rw [hrole] at hmg
  simp [hx, hxr, evenPerm, evenMap] at hmg hxg ⊢
  rw [hmg, hxg]
  ring

/-- Under the odd invariant, the odd partner carries the data role at `a + 2h + 1`. -/
theorem visit_odd (s : RouteParam) (h : Fin s.m) {ρ : Equiv.Perm (Pos s)}
    (hi : OddInv s h ρ) (x : Pos s) (hx : (ρ x).rail = true) :
    (ρ (oddPerm s h x)).rail = false ∧
      (ρ (oddPerm s h x)).col = (ρ x).col + (2 * (h : ℕ) + 1) := by
  rcases hi with ⟨hr, hg⟩
  have hxr : x.rail = false := by
    have h := hr x
    rw [hx] at h
    cases xr : x.rail <;> simp [xr] at h ⊢
  have hmr := hr (oddPerm s h x)
  have hmg := hg (oddPerm s h x)
  have hxg := hg x
  have hrole : (ρ (oddPerm s h x)).rail = false := by
    rw [hmr]
    simp [oddPerm, oddMap, hxr]
  refine ⟨hrole, ?_⟩
  rw [hrole] at hmg
  simp [hx, hxr, oddPerm, oddMap] at hmg hxg ⊢
  rw [hmg, hxg]
  ring

/-- The actual π/δ route satisfies the visit law at every step. -/
theorem visit_role (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m)
    (x : Pos s) (hx : (during s t ht x).rail = true) :
    (during s t ht (stepPerm s t ht x)).rail = false ∧
      (during s t ht (stepPerm s t ht x)).col
        = (during s t ht x).col + (t : ZMod (s.m + s.m)) := by
  by_cases he : t % 2 = 0
  · have hi := (during_inv s t ht).1 he
    have hv := visit_even s ⟨t / 2, by omega⟩ hi x hx
    have htime : t = 2 * (t / 2) := by omega
    have hcast : (t : ZMod (s.m + s.m)) = 2 * ((t / 2 : ℕ) : ZMod (s.m + s.m)) := by
      have hc := congrArg (fun n : ℕ => (n : ZMod (s.m + s.m))) htime
      push_cast at hc
      exact hc
    rw [hcast]
    simpa [during, stepPerm, he] using hv
  · have hi := (during_inv s t ht).2 he
    have hv := visit_odd s ⟨t / 2, by omega⟩ hi x hx
    have htime : t = 2 * (t / 2) + 1 := by omega
    have hcast : (t : ZMod (s.m + s.m))
        = 2 * ((t / 2 : ℕ) : ZMod (s.m + s.m)) + 1 := by
      have hc := congrArg (fun n : ℕ => (n : ZMod (s.m + s.m))) htime
      push_cast at hc
      exact hc
    rw [hcast]
    simpa [during, stepPerm, he] using hv

/-- A matching step flips the transported role rail. -/
theorem match_rail (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) (x : Pos s) :
    (during s t ht (stepPerm s t ht x)).rail = !(during s t ht x).rail := by
  by_cases he : t % 2 = 0
  · have hr := ((during_inv s t ht).1 he).1
    rw [hr, hr, step_rail]
  · have hr := ((during_inv s t ht).2 he).1
    rw [hr, hr, step_rail]

/-- The full transported interaction on initial role labels is Eq. (1). -/
def effRole (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) : Equiv.Perm (Pos s) :=
  roleMap (stepPerm s t ht) (during s t ht).symm (during s t ht).symm

/-- A syndrome role is transported to the data role `a + t`. -/
theorem eff_fwd (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) (x : Pos s)
    (hx : x.rail = true) :
    (effRole s t ht x).rail = false ∧
      (effRole s t ht x).col = x.col + (t : ZMod (s.m + s.m)) := by
  have hx' : (during s t ht ((during s t ht).symm x)).rail = true := by simpa using hx
  have hv := visit_role s t ht ((during s t ht).symm x) hx'
  simpa [effRole, roleMap, Equiv.trans_apply] using hv

/-- A data output of a transported interaction comes from a syndrome input. -/
theorem eff_back (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m) (x : Pos s)
    (hy : (effRole s t ht x).rail = false) :
    x.rail = true ∧
      (effRole s t ht x).col = x.col + (t : ZMod (s.m + s.m)) := by
  have hr := match_rail s t ht ((during s t ht).symm x)
  have hswap : (effRole s t ht x).rail = !x.rail := by
    simpa [effRole, roleMap, Equiv.trans_apply] using hr
  have hx : x.rail = true := by
    cases hx : x.rail
    · exfalso
      rw [hx] at hswap
      simp only [Bool.not_false] at hswap
      rw [hswap] at hy
      cases hy
    · rfl
  refine ⟨hx, (eff_fwd s t ht x hx).2⟩

/-- Roles with fixed rail, group, and free internal coordinates. -/
abbrev Cell (s : RouteParam) (r : Bool) (g : ZMod (s.m + s.m)) :=
  {x : Pos s // x.rail = r ∧ x.col = g}

/-- Internal coordinates are equivalent to a fixed role cell. -/
def intRole (s : RouteParam) (r : Bool) (g : ZMod (s.m + s.m)) :
    (ZMod s.p × Fin s.q) ≃ Cell s r g where
  toFun u := ⟨⟨r, g, u.1, u.2⟩, rfl, rfl⟩
  invFun x := (x.1.sta, x.1.chan)
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨rail, col, sta, chan⟩, hr, hc⟩
    cases hr
    cases hc
    rfl

/-- Transported interactions restrict to the corresponding syndrome/data cells. -/
def effSub (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m)
    (a : ZMod (s.m + s.m)) : Cell s true a ≃ Cell s false (a + (t : ℕ)) :=
  (effRole s t ht).subtypeEquiv (by
    intro x
    constructor
    · intro hx
      have hf := eff_fwd s t ht x hx.1
      exact ⟨hf.1, by rw [hf.2, hx.2]⟩
    · intro hy
      have hb := eff_back s t ht x hy.1
      refine ⟨hb.1, ?_⟩
      have hc := hb.2
      rw [hy.2] at hc
      exact (add_right_cancel hc).symm)

/-- The effective interaction on internal labels, obtained by role transport. -/
def effInt (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m)
    (a : ZMod (s.m + s.m)) : Equiv.Perm (ZMod s.p × Fin s.q) :=
  roleMap (effSub s t ht a) (intRole s true a) (intRole s false (a + (t : ℕ)))

/-- The internal interaction is literally the transported role-map composition. -/
theorem effInt_eq (s : RouteParam) (t : ℕ) (ht : t < s.m + s.m)
    (a : ZMod (s.m + s.m)) :
    effInt s t ht a = roleMap (effSub s t ht a)
      (intRole s true a) (intRole s false (a + (t : ℕ))) := rfl

/-- The finite cyclic index and additive group index agree. -/
theorem fin_cast (M : ℕ) [NeZero M] (t : Fin M) :
    (ZMod.finEquiv M) t = (t : ZMod M) := by
  cases M with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ M =>
    change (t : ZMod (M + 1)) = (t.val : ZMod (M + 1))
    exact (ZMod.natCast_zmod_val (n := M + 1) (t : ZMod (M + 1))).symm

/-- Every syndrome group visits every data group at exactly one round time. -/
theorem visit_once (s : RouteParam) (a b : ZMod (s.m + s.m)) :
    ∃! t : Fin (s.m + s.m), a + (t : ZMod (s.m + s.m)) = b := by
  let _ : NeZero (s.m + s.m) := ⟨Nat.ne_of_gt (Nat.add_pos_left s.hm s.m)⟩
  refine ⟨(ZMod.finEquiv (s.m + s.m)).symm (b - a), ?_, ?_⟩
  · change a + (((ZMod.finEquiv (s.m + s.m)).symm (b - a) : Fin (s.m + s.m)) :
      ZMod (s.m + s.m)) = b
    rw [← fin_cast, RingEquiv.apply_symm_apply]
    abel
  · intro t ht
    apply (ZMod.finEquiv (s.m + s.m)).injective
    rw [RingEquiv.apply_symm_apply, fin_cast]
    have ht' : (t : ZMod (s.m + s.m)) + a = b := by
      calc
        (t : ZMod (s.m + s.m)) + a = a + (t : ZMod (s.m + s.m)) := add_comm _ _
        _ = b := ht
    exact eq_sub_of_add_eq ht'

/-- Effective permutations indexed by finite syndrome and data groups. -/
def effPerms (s : RouteParam) (a b : Fin (s.m + s.m)) :
    Equiv.Perm (ZMod s.p × Fin s.q) := by
  let : NeZero (s.m + s.m) := ⟨Nat.ne_of_gt (Nat.add_pos_left s.hm s.m)⟩
  let ga := (ZMod.finEquiv (s.m + s.m)) a
  let gb := (ZMod.finEquiv (s.m + s.m)) b
  let t := (ZMod.finEquiv (s.m + s.m)).symm (gb - ga)
  exact effInt s t t.isLt ga

/-- Effective arrays assemble entrywise into permutation-block matrices. -/
theorem effBlocks_entry {K : Type*} [Field K]
    (s : RouteParam) (a b : Fin (s.m + s.m)) (u v : ZMod s.p × Fin s.q) :
    (permBlocks (K := K) (effPerms s)) (a, u) (b, v) = permMat (effPerms s a b) u v := rfl

end Qatlib.Papers.Armillary26.RoutingModel
