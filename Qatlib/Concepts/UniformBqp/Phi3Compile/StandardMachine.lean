/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.StandardMachineDefs

/-!
# Reversible gate programs and clocked machine guarantees

This module proves correctness and resource bounds for reversible gate ladders implementing
controlled bit flips with clean auxiliary wires. It also establishes bounded-clock simulation,
randomized-machine termination, polynomial-time complementation, and exact gate decompositions.

For `GeneralNativeMachine`, the finite-window results give exact Phi3 simulation with explicit
register and gate bounds. The final results show that a separator-based pair encoding collides
and prevents the stated gate-count emitter for the reference construction.

For background, see [Yao1993].

## Main statements

* `mcxProgram_run`: correctness of the pattern-controlled bit flip with clean auxiliary wires.
* `clocked_always_halts`: bounded termination of a clocked tape machine.
* `generalPhi3_cellTable`: exact Phi3 simulation and resource guarantees.
* `emitterClause_impossible_for_theorem2_build`: obstruction from an ambiguous input encoding.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.UniformBqp.Phi3Compile.StandardMachine
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Concepts.CircuitImpl.ReflectionCompile

namespace Qatlib.Concepts.UniformBqp.Phi3Compile
namespace StandardMachine

open Matrix

/-- Running concatenated gate words equals running the first word and then the second. -/
theorem BoundedGate.run_append {n : ℕ} (l m : List (BoundedGate n)) (x : Reg n) :
    BoundedGate.run (l ++ m) x = BoundedGate.run m (BoundedGate.run l x) := by
  induction l generalizing x with
  | nil => rfl
  | cons g l ih => simp only [List.cons_append, BoundedGate.run, ih]

/-- Reversing a word of well-formed involutive gates undoes its action on a register. -/
theorem BoundedGate.run_reverse {n : ℕ} (l : List (BoundedGate n)) (x : Reg n)
    (hg : ∀ g ∈ l, g.wellformed) :
    BoundedGate.run l.reverse (BoundedGate.run l x) = x := by
  induction l generalizing x with
  | nil => rfl
  | cons g l ih =>
      have hrev : ∀ (reg : Reg n), BoundedGate.run ((g :: l).reverse) reg
          = g.act (BoundedGate.run l.reverse reg) := by
        intro reg
        rw [List.reverse_cons, BoundedGate.run_append]
        rfl
      have hg' : ∀ g' ∈ l, g'.wellformed := fun g' hg' => hg g' (by simp [hg'])
      rw [hrev, BoundedGate.run, ih (g.act x) hg']
      exact (BoundedGate.act_involutive g (hg g (by simp))) x

/-- The matrix of a bounded-gate word is the permutation matrix associated with its register
action. -/
theorem BoundedGate.wordMatrix_eq_permMatrix {n : ℕ} (l : List (BoundedGate n)) :
    BoundedGate.wordMatrix l = permMatrix (BoundedGate.run l) := by
  induction l with
  | nil => ext i j; simp [BoundedGate.wordMatrix, BoundedGate.run, permMatrix, Matrix.one_apply]
  | cons g l ih =>
      rw [BoundedGate.wordMatrix, ih]
      simp only [BoundedGate.matrix]
      rw [permMatrix_mul]
      have hcomp : BoundedGate.run l ∘ (g.act : Reg n → Reg n) = BoundedGate.run (g :: l) := by
        funext reg
        rfl
      rw [hcomp]

/-- A gate word touches a wire when that wire belongs to the support of some gate in the word. -/
def BoundedGate.touches {n : ℕ} (w : List (BoundedGate n)) (s : Fin n) : Prop :=
  ∃ g ∈ w, s ∈ g.support

/-- A wire is touched by a nonempty word exactly when it is in the first gate support or touched
by the remaining word. -/
theorem BoundedGate.touches_cons {n : ℕ} (g : BoundedGate n) (l : List (BoundedGate n))
    (s : Fin n) : BoundedGate.touches (g :: l) s ↔ s ∈ g.support ∨ BoundedGate.touches l s := by
  constructor
  · rintro ⟨g', hg', hs'⟩
    rcases List.mem_cons.mp hg' with h | hg'
    · rw [h] at hs'
      exact Or.inl hs'
    · exact Or.inr ⟨g', hg', hs'⟩
  · rintro (h | ⟨g', hg', hs'⟩)
    · exact ⟨g, (List.mem_cons_self : g ∈ g :: l), h⟩
    · exact ⟨g', List.mem_cons_of_mem g hg', hs'⟩

/-- Reversing a gate word preserves the set of wires it touches. -/
theorem BoundedGate.touches_reverse {n : ℕ} (w : List (BoundedGate n)) (s : Fin n) :
    BoundedGate.touches w.reverse s ↔ BoundedGate.touches w s := by
  constructor
  · rintro ⟨g, hg, hs⟩
    exact ⟨g, List.mem_reverse.mp hg, hs⟩
  · rintro ⟨g, hg, hs⟩
    exact ⟨g, List.mem_reverse.mpr hg, hs⟩

/-- A gate preserves every register bit outside its support. -/
theorem BoundedGate.act_eq_of_not_mem_support {n : ℕ} (g : BoundedGate n) (reg : Reg n)
    {s : Fin n} (hs : s ∉ g.support) : (g.act reg) s = reg s := by
  cases g with
  | x i =>
      have hsi : s ≠ i := by
        intro hsi
        exact hs (by simp [BoundedGate.support, hsi])
      simp [BoundedGate.act, Function.update, hsi]
  | cx c t =>
      have hst : s ≠ t := by
        intro hst
        exact hs (by simp [BoundedGate.support, hst])
      simp [BoundedGate.act, Function.update, hst]
  | ccx a b c =>
      have hsc : s ≠ c := by
        intro hsc
        exact hs (by simp [BoundedGate.support, hsc])
      simp [BoundedGate.act, Function.update, hsc]

/-- A well-formed gate sends registers agreeing on its support to outputs agreeing on its
support. -/
theorem BoundedGate.act_congr_on {n : ℕ} (g : BoundedGate n) (hw : g.wellformed)
    {reg reg' : Reg n} (h : ∀ s ∈ g.support, reg s = reg' s) :
    ∀ s ∈ g.support, (g.act reg) s = (g.act reg') s := by
  cases g with
  | x i =>
      intro s hs
      have hsi : s = i := by simpa [BoundedGate.support] using! hs
      rw [hsi]
      simp [BoundedGate.act, Function.update, h i (by simp [BoundedGate.support])]
  | cx c t =>
      have hct : c ≠ t := hw
      intro s hs
      have hcases : s = c ∨ s = t := by simpa [BoundedGate.support] using! hs
      rcases hcases with hsc | hst
      · rw [hsc]
        simp [BoundedGate.act, Function.update, h c (by simp [BoundedGate.support]), hct]
      · rw [hst]
        have h1 := h t (by simp [BoundedGate.support])
        have h2 := h c (by simp [BoundedGate.support])
        simp [BoundedGate.act, Function.update, h1, h2]
  | ccx a b c =>
      have hca : c ≠ a := hw.1
      have hcb : c ≠ b := hw.2
      have hca' : a ≠ c := fun h => hca h.symm
      have hcb' : b ≠ c := fun h => hcb h.symm
      intro s hs
      have hcases : s = a ∨ s = b ∨ s = c := by simpa [BoundedGate.support] using! hs
      rcases hcases with hsa | hsb | hsc
      · rw [hsa]
        simp [BoundedGate.act, Function.update, h a (by simp [BoundedGate.support]), hca']
      · rw [hsb]
        simp [BoundedGate.act, Function.update, h b (by simp [BoundedGate.support]), hcb']
      · rw [hsc]
        have h1 := h c (by simp [BoundedGate.support])
        have h2 := h a (by simp [BoundedGate.support])
        have h3 := h b (by simp [BoundedGate.support])
        simp [BoundedGate.act, Function.update, h1, h2, h3]

/-- Running a gate word preserves every wire that the word does not touch. -/
theorem BoundedGate.run_untouched {n : ℕ} : ∀ (w : List (BoundedGate n)) (reg : Reg n) {s : Fin n},
    ¬ BoundedGate.touches w s → (BoundedGate.run w reg) s = reg s := by
  intro w
  induction w with
  | nil => intro reg s hs; rfl
  | cons g l ih =>
      intro reg s hs
      have hg : s ∉ g.support := by
        intro hg'
        exact hs ((BoundedGate.touches_cons g l s).2 (Or.inl hg'))
      have hl : ¬ BoundedGate.touches l s := by
        intro hl'
        exact hs ((BoundedGate.touches_cons g l s).2 (Or.inr hl'))
      rw [BoundedGate.run]
      rw [ih (g.act reg) hl]
      exact BoundedGate.act_eq_of_not_mem_support g reg hg

/-- A word of well-formed gates sends registers agreeing on all gate supports to outputs
agreeing on every touched wire. -/
theorem BoundedGate.run_congr_touched {n : ℕ} : ∀ (w : List (BoundedGate n)) {reg reg' : Reg n},
    (∀ g ∈ w, g.wellformed) →
    (∀ g ∈ w, ∀ s ∈ g.support, reg s = reg' s) →
    ∀ s, BoundedGate.touches w s → (BoundedGate.run w reg) s = (BoundedGate.run w reg') s := by
  intro w
  induction w with
  | nil => intro reg reg' hw h s hs; exact absurd hs (by simp [BoundedGate.touches])
  | cons g l ih =>
      intro reg reg' hw h s hs
      obtain ⟨g', hg', hs'⟩ := hs
      have hwg : g.wellformed := hw g (List.mem_cons_self : g ∈ g :: l)
      have hagx : ∀ g'' ∈ l, ∀ s'' ∈ g''.support, (g.act reg) s'' = (g.act reg') s'' := by
        intro g'' hg'' s'' hs''
        by_cases hmem : s'' ∈ g.support
        · exact BoundedGate.act_congr_on g hwg
            (fun t ht => h g (List.mem_cons_self : g ∈ g :: l) t ht) s'' hmem
        · have hx' : (g.act reg) s'' = reg s'' :=
            BoundedGate.act_eq_of_not_mem_support g reg hmem
          have hy' : (g.act reg') s'' = reg' s'' :=
            BoundedGate.act_eq_of_not_mem_support g reg' hmem
          have hxy : reg s'' = reg' s'' := h g'' (List.mem_cons_of_mem g hg'') s'' hs''
          rw [hx', hy', hxy]
      rcases List.mem_cons.mp hg' with hgm | hg'
      · rw [hgm] at hs'
        by_cases hlt : BoundedGate.touches l s
        · simpa [BoundedGate.run] using!
            (ih (reg := g.act reg) (reg' := g.act reg')
              (fun g'' hg'' => hw g'' (List.mem_cons_of_mem g hg''))
              hagx s hlt)
        · have hx' : (BoundedGate.run l (g.act reg)) s = (g.act reg) s :=
            BoundedGate.run_untouched l (g.act reg) hlt
          have hy' : (BoundedGate.run l (g.act reg')) s = (g.act reg') s :=
            BoundedGate.run_untouched l (g.act reg') hlt
          simp only [BoundedGate.run]
          rw [hx', hy']
          exact BoundedGate.act_congr_on g hwg
            (fun t ht => h g (List.mem_cons_self : g ∈ g :: l) t ht) s hs'
      · have hlt : BoundedGate.touches l s := ⟨g', hg', hs'⟩
        simpa [BoundedGate.run] using!
          (ih (reg := g.act reg) (reg' := g.act reg')
            (fun g'' hg'' => hw g'' (List.mem_cons_of_mem g hg''))
            hagx s hlt)

/-- A controlled-NOT from an address wire to an auxiliary wire preserves all address bits. -/
theorem cx_addr_preserved {n m : ℕ} (c : Fin n) (a : Fin m) (x : Reg (n + m)) :
    ∀ w : Fin n, ((BoundedGate.cx (addrWire m c) (ancWire n a)).act x) (addrWire m w)
      = x (addrWire m w) := by
  intro w
  simp [BoundedGate.act, Function.update, addrWire_ne_ancWire n m w a]

/-- A doubly controlled bit flip targeting an auxiliary wire preserves every address bit. -/
theorem ccx_addr_preserved {n m : ℕ} (p : Fin m) (c : Fin n) (a : Fin m) (x : Reg (n + m)) :
    ∀ w : Fin n, ((BoundedGate.ccx (ancWire n p) (addrWire m c) (ancWire n a)).act x) (addrWire m w)
      = x (addrWire m w) := by
  intro w
  simp [BoundedGate.act, Function.update, addrWire_ne_ancWire n m w a]

/-- The conjunction accumulation program preserves all address bits. -/
theorem conjAccum_preserves_addr {n m : ℕ} (l : List (Fin n × Fin m)) (prev : Fin m)
    (x : Reg (n + m)) :
    ∀ w : Fin n, (BoundedGate.run (conjAccum l prev) x) (addrWire m w) = x (addrWire m w) := by
  induction l generalizing prev x with
  | nil => intro w; rfl
  | cons p rest ih =>
      rcases p with ⟨c, a⟩
      intro w
      have hrun : BoundedGate.run (conjAccum ((c, a) :: rest) prev) x
          = BoundedGate.run (conjAccum rest a)
              ((BoundedGate.ccx (ancWire n prev) (addrWire m c) (ancWire n a)).act x) := by
        simp only [conjAccum, conjChain, BoundedGate.run]
      rw [hrun]
      rw [ih a _ w]
      exact ccx_addr_preserved prev c a x w

/-- The conjunction ladder preserves all address bits. -/
theorem conjLadder_preserves_addr {n m : ℕ} (l : List (Fin n × Fin m)) (x : Reg (n + m)) :
    ∀ w : Fin n, (BoundedGate.run (conjLadder l) x) (addrWire m w) = x (addrWire m w) := by
  induction l generalizing x with
  | nil => intro w; rfl
  | cons p rest ih =>
      rcases p with ⟨c, a⟩
      intro w
      have hrun : BoundedGate.run (conjLadder ((c, a) :: rest)) x
          = BoundedGate.run (conjAccum rest a)
              ((BoundedGate.cx (addrWire m c) (ancWire n a)).act x) := by
        simp only [conjLadder, conjAccum, BoundedGate.run]
      rw [hrun]
      rw [conjAccum_preserves_addr rest a _ w]
      exact cx_addr_preserved c a x w

/-- Every bounded gate has arity at most three. -/
theorem BoundedGate.arity_le_three {n : ℕ} (g : BoundedGate n) : g.arity ≤ 3 := by
  cases g <;> simp [BoundedGate.arity]

/-- Every gate in the all-true controlled bit-flip program has arity at most three. -/
theorem mcxProgramAll_arity {n m : ℕ} (l : List (Fin n × Fin m)) (t : Fin n) :
    ∀ g ∈ mcxProgramAll l t, g.arity ≤ 3 := by
  intro g hg
  cases g <;> simp [BoundedGate.arity] at hg ⊢

/-- Every gate in the pattern-controlled bit-flip program has arity at most three. -/
theorem mcxProgram_arity {n : ℕ} (t : Fin n) (p : Reg n) :
    ∀ g ∈ mcxProgram t p, g.arity ≤ 3 := by
  intro g hg
  cases g <;> simp [BoundedGate.arity] at hg ⊢

/-- Equality of embedded address wires implies equality of their original indices. -/
theorem addrWire_injective {n m : ℕ} {a b : Fin n} (h : addrWire m a = addrWire m b) : a = b := by
  have hv := congrArg Fin.val h
  simp only [addrWire_val] at hv
  exact Fin.ext hv

/-- Equality of embedded auxiliary wires implies equality of their original indices. -/
theorem ancWire_injective {n m : ℕ} {a b : Fin m} (h : ancWire n a = ancWire n b) : a = b := by
  have hv := congrArg Fin.val h
  simp only [ancWire_val] at hv
  exact Fin.ext (by omega)

/-- Distinct auxiliary indices give distinct embedded wires. -/
theorem ancWire_ne_ancWire {n m : ℕ} {a b : Fin m} (h : a ≠ b) : ancWire n a ≠ ancWire n b := by
  intro hcon
  exact h (ancWire_injective hcon)

/-- The conjunction of the selected address bits depends only on the address portion of the
register. -/
theorem ladderChain_congr_addr {n m : ℕ} : ∀ (l : List (Fin n × Fin m)) {x y : Reg (n + m)},
    (∀ w : Fin n, x (addrWire m w) = y (addrWire m w)) → ladderChain l x = ladderChain l y := by
  intro l
  induction l with
  | nil => intro x y h; rfl
  | cons p rest ih =>
      intro x y h
      rcases p with ⟨c, a⟩
      simp only [ladderChain]
      rw [h c, ih (x := x) (y := y) h]

/-- The recursive ladder conjunction equals the Boolean conjunction of all selected control
bits. -/
theorem ladderChain_eq_ctrlConjAll {n m : ℕ} (l : List (Fin n × Fin m)) (x : Reg (n + m)) :
    ladderChain l x = ctrlConjAll l x := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨c, a⟩
      simp [ladderChain, ctrlConjAll, ih]

/-- With distinct initially false destination wires and a separate initial auxiliary wire, a
nonempty conjunction chain stores the initial auxiliary bit conjoined with all selected
address bits in its last destination. -/
theorem conjChain_conj {n m : ℕ} : ∀ (l : List (Fin n × Fin m)) (x : Reg (n + m)),
    (∀ a ∈ ancOf l, x (ancWire n a) = false) →
    (ancOf l).Nodup →
    ∀ (prev : Fin m), prev ∉ ancOf l →
    ∀ (tail : List (Fin n × Fin m)) (p : Fin n × Fin m),
      l = tail ++ [p] →
      (BoundedGate.run (conjChain prev l) x) (ancWire n p.2)
        = (x (ancWire n prev) && ladderChain l x) := by
  intro l
  induction l with
  | nil =>
      intro x h1 h2 prev h3 tail p hp
      simp at hp
  | cons hd tl ih =>
      intro x h1 h2 prev h3 tail p hp
      rcases hd with ⟨hc, ha⟩
      cases tail with
      | nil =>
          rcases List.cons.inj hp with ⟨rfl, rfl⟩
          have hrun : BoundedGate.run (conjChain prev [(hc, ha)]) x
              = ((BoundedGate.ccx (ancWire n prev) (addrWire m hc) (ancWire n ha)).act x) := by
            simp [conjChain, BoundedGate.run]
          rw [hrun]
          have hanc : x (ancWire n ha) = false := h1 ha (by simp [ancOf])
          simp [BoundedGate.act, Function.update, hanc, ladderChain]
      | cons b tail' =>
          rcases List.cons.inj hp with ⟨hb, htl⟩
          have hrun : BoundedGate.run (conjChain prev ((hc, ha) :: tl)) x
              = BoundedGate.run (conjChain ha tl)
                  ((BoundedGate.ccx (ancWire n prev) (addrWire m hc) (ancWire n ha)).act x) := by
            simp only [conjChain, BoundedGate.run]
          rw [hrun]
          have hnodup : (ancOf tl).Nodup := (List.nodup_cons.mp h2).2
          have hprev : ha ∉ ancOf tl := by
            intro hmem
            exact (List.nodup_cons.mp h2).1 hmem
          have hanc' : ∀ a ∈ ancOf tl,
              ((BoundedGate.ccx (ancWire n prev) (addrWire m hc) (ancWire n ha)).act x)
                (ancWire n a) = false := by
            intro a hmem
            have hne : ancWire n a ≠ ancWire n ha := by
              intro hcon
              exact hprev ((ancWire_injective hcon) ▸ hmem)
            simp [BoundedGate.act, Function.update, hne]
            exact h1 a (by simp [ancOf, hmem])
          have hx1 : ((BoundedGate.ccx (ancWire n prev) (addrWire m hc) (ancWire n ha)).act x)
                (ancWire n ha) = (x (ancWire n prev) && x (addrWire m hc)) := by
            simp [BoundedGate.act, Function.update, h1 ha (by simp [ancOf])]
          have hchain := ih
            ((BoundedGate.ccx (ancWire n prev) (addrWire m hc) (ancWire n ha)).act x)
            hanc' hnodup ha hprev tail' p htl
          rw [hchain, hx1]
          simp [ladderChain, Bool.and_assoc,
            ladderChain_congr_addr tl (ccx_addr_preserved prev hc ha x)]

/-- A nonempty conjunction ladder with distinct initially false auxiliary wires stores the
conjunction of its address controls in its last auxiliary wire. -/
theorem conjLadder_conj {n m : ℕ} : ∀ (l : List (Fin n × Fin m)) (x : Reg (n + m)),
    (∀ a ∈ ancOf l, x (ancWire n a) = false) →
    (ancOf l).Nodup →
    ∀ (tail : List (Fin n × Fin m)) (p : Fin n × Fin m), l = tail ++ [p] →
      (BoundedGate.run (conjLadder l) x) (ancWire n p.2) = ladderChain l x := by
  intro l x h1 h2 tail p hp
  cases l with
  | nil => simp at hp
  | cons hd tl =>
      rcases hd with ⟨hc, ha⟩
      cases tail with
      | nil =>
          rcases List.cons.inj hp with ⟨rfl, rfl⟩
          have hrun : BoundedGate.run (conjLadder [(hc, ha)]) x
              = ((BoundedGate.cx (addrWire m hc) (ancWire n ha)).act x) := by
            simp [conjLadder, conjAccum, conjChain, BoundedGate.run]
          rw [hrun]
          simp [BoundedGate.act, Function.update, h1 ha (by simp [ancOf]), ladderChain]
      | cons b tail' =>
          rcases List.cons.inj hp with ⟨hb, htl⟩
          have hrun : BoundedGate.run (conjLadder ((hc, ha) :: tl)) x
              = BoundedGate.run (conjChain ha tl)
                  ((BoundedGate.cx (addrWire m hc) (ancWire n ha)).act x) := by
            simp only [conjLadder, conjAccum, BoundedGate.run]
          rw [hrun]
          have hnodup : (ancOf tl).Nodup := (List.nodup_cons.mp h2).2
          have hprev : ha ∉ ancOf tl := by
            intro hmem
            exact (List.nodup_cons.mp h2).1 hmem
          have hanc' : ∀ a ∈ ancOf tl,
              ((BoundedGate.cx (addrWire m hc) (ancWire n ha)).act x) (ancWire n a) = false := by
            intro a hmem
            have hne : ancWire n a ≠ ancWire n ha := by
              intro hcon
              exact hprev ((ancWire_injective hcon) ▸ hmem)
            simp [BoundedGate.act, Function.update, hne]
            exact h1 a (by simp [ancOf, hmem])
          have hx1 : ((BoundedGate.cx (addrWire m hc) (ancWire n ha)).act x) (ancWire n ha)
              = x (addrWire m hc) := by
            simp [BoundedGate.act, Function.update, h1 ha (by simp [ancOf])]
          have hchain := conjChain_conj tl
            ((BoundedGate.cx (addrWire m hc) (ancWire n ha)).act x)
            hanc' hnodup ha hprev tail' p htl
          rw [hchain, hx1]
          simp [ladderChain, ladderChain_congr_addr tl (cx_addr_preserved hc ha x)]

/-- A conjunction chain consists of well-formed gates when its auxiliary destinations are
distinct and exclude its initial auxiliary wire. -/
theorem conjChain_wellformed {n m : ℕ} : ∀ (l : List (Fin n × Fin m)),
    (ancOf l).Nodup → ∀ (prev : Fin m), prev ∉ ancOf l →
    ∀ g ∈ conjChain prev l, g.wellformed := by
  intro l
  induction l with
  | nil =>
      intro hd prev hp g hg
      simp [conjChain] at hg
  | cons p rest ih =>
      rcases p with ⟨pc, pa⟩
      intro hd prev hp g hg
      rw [conjChain] at hg
      rcases List.mem_cons.mp hg with hgm | hg'
      · rw [hgm]
        simp only [BoundedGate.wellformed]
        constructor
        · exact ancWire_ne_ancWire (by
            intro hcon
            apply hp
            simp [ancOf, hcon])
        · exact (addrWire_ne_ancWire n m pc pa).symm
      · exact ih (List.nodup_cons.mp hd).2 pa (by
          intro hmem
          exact (List.nodup_cons.mp hd).1 hmem) g hg'

/-- A conjunction ladder consists of well-formed gates when its auxiliary destinations are
distinct. -/
theorem conjLadder_wellformed {n m : ℕ} (l : List (Fin n × Fin m)) (hd : (ancOf l).Nodup) :
    ∀ g ∈ conjLadder l, g.wellformed := by
  induction l with
  | nil =>
      intro g hg
      simp [conjLadder] at hg
  | cons p rest ih =>
      rcases p with ⟨pc, pa⟩
      intro g hg
      rw [conjLadder] at hg
      rcases List.mem_cons.mp hg with hgm | hg'
      · rw [hgm]
        simp only [BoundedGate.wellformed]
        exact addrWire_ne_ancWire n m pc pa
      · exact conjChain_wellformed rest (List.nodup_cons.mp hd).2 pa (by
          intro hmem
          exact (List.nodup_cons.mp hd).1 hmem) g hg'

/-- A conjunction chain avoids an address target that is absent from its control indices. -/
theorem conjChain_not_touches_target {n m : ℕ} : ∀ (l : List (Fin n × Fin m)) (t : Fin n),
    (∀ p ∈ l, p.1 ≠ t) → ∀ (prev : Fin m),
    ∀ g ∈ conjChain prev l, addrWire m t ∉ g.support := by
  intro l
  induction l with
  | nil =>
      intro t ht prev g hg
      simp [conjChain] at hg
  | cons p rest ih =>
      rcases p with ⟨pc, pa⟩
      intro t ht prev g hg
      rw [conjChain] at hg
      rcases List.mem_cons.mp hg with hgm | hg'
      · rw [hgm]
        simp only [BoundedGate.support, List.mem_cons, List.mem_nil_iff, or_false]
        intro hmem
        rcases hmem with h1 | h2 | h3
        · exact absurd h1 (addrWire_ne_ancWire n m t prev)
        · exact absurd (addrWire_injective h2) (fun h => ht (pc, pa) (by simp) h.symm)
        · exact absurd h3 (addrWire_ne_ancWire n m t pa)
      · exact ih t (fun q hq => ht q (by simp [hq])) pa g hg'

/-- A conjunction ladder avoids an address target that is absent from its control indices. -/
theorem conjLadder_not_touches_target {n m : ℕ} (l : List (Fin n × Fin m)) (t : Fin n)
    (ht : ∀ p ∈ l, p.1 ≠ t) : ∀ g ∈ conjLadder l, addrWire m t ∉ g.support := by
  cases l with
  | nil =>
      intro g hg
      simp [conjLadder] at hg
  | cons p rest =>
      rcases p with ⟨pc, pa⟩
      intro g hg
      rw [conjLadder] at hg
      rcases List.mem_cons.mp hg with hgm | hg'
      · rw [hgm]
        simp only [BoundedGate.support, List.mem_cons, List.mem_nil_iff, or_false]
        intro hmem
        rcases hmem with h1 | h2
        · exact absurd (addrWire_injective h1) (fun h => ht (pc, pa) (by simp) h.symm)
        · exact absurd h2 (addrWire_ne_ancWire n m t pa)
      · exact conjChain_not_touches_target rest t (fun q hq => ht q (by simp [hq])) pa g hg'

/-- The last pair of a list with a final appended singleton is that singleton pair. -/
theorem lastPair_append_singleton {n m : ℕ} : ∀ (tail : List (Fin n × Fin m)) (p : Fin n × Fin m),
    lastPair (tail ++ [p]) = some p := by
  intro tail
  induction tail with
  | nil => intro p; rfl
  | cons q rest ih =>
      intro p
      cases rest with
      | nil => rfl
      | cons r rest' =>
          show lastPair (q :: (r :: (rest' ++ [p]))) = some p
          simp only [lastPair]
          simpa [List.cons_append] using! ih p

/-- With no control pairs, the all-true controlled program agrees with the unconditional target
flip. -/
theorem mcxProgramAll_run_nil {n m : ℕ} (t : Fin n) (x : Reg (n + m)) :
    BoundedGate.run (mcxProgramAll [] t) x = mcxAllPerm [] t x := by
  have h1 : lastPair (n := n) (m := m) [] = none := rfl
  rw [mcxProgramAll, h1]
  simp [mcxAllPerm, BoundedGate.run, BoundedGate.act]

/-- Computing the conjunction, toggling the target, and reversing the ladder changes only the
target by the control conjunction when auxiliary wires are clean and distinct and the target
is not a control. -/
theorem mcxMiddle_run {n m : ℕ} (l : List (Fin n × Fin m)) (t : Fin n) (x : Reg (n + m))
    (hanc : ∀ a : Fin m, x (ancWire n a) = false)
    (hd : (ancOf l).Nodup)
    (ht : ∀ p ∈ l, p.1 ≠ t)
    (tail : List (Fin n × Fin m)) (p : Fin n × Fin m) (hp : l = tail ++ [p]) :
    BoundedGate.run (conjLadder l ++ [.cx (ancWire n p.2) (addrWire m t)] ++ (conjLadder l).reverse) x
      = Function.update x (addrWire m t) (x (addrWire m t) ^^ ladderChain l x) := by
  have hconj : (BoundedGate.run (conjLadder l) x) (ancWire n p.2) = ladderChain l x :=
    conjLadder_conj l x (fun a _ => hanc a) hd tail p hp
  have haddr : ∀ w : Fin n, (BoundedGate.run (conjLadder l) x) (addrWire m w) = x (addrWire m w) :=
    conjLadder_preserves_addr l x
  have hnotouch : ¬ BoundedGate.touches (conjLadder l) (addrWire m t) := by
    intro hmem
    obtain ⟨g, hg, hs⟩ := hmem
    exact (conjLadder_not_touches_target l t
      (fun q hq => ht q hq) g hg) hs
  have hwell : ∀ g ∈ conjLadder l, g.wellformed := conjLadder_wellformed l hd
  have hinv : BoundedGate.run (conjLadder l).reverse (BoundedGate.run (conjLadder l) x) = x :=
    BoundedGate.run_reverse (conjLadder l) x hwell
  have hctrlraw : BoundedGate.run [.cx (ancWire n p.2) (addrWire m t)]
        (BoundedGate.run (conjLadder l) x)
      = Function.update (BoundedGate.run (conjLadder l) x) (addrWire m t)
          ((BoundedGate.run (conjLadder l) x) (addrWire m t)
            ^^ (BoundedGate.run (conjLadder l) x) (ancWire n p.2)) := by
    simp [BoundedGate.run, BoundedGate.act]
  have hrest : BoundedGate.run (conjLadder l).reverse
        (BoundedGate.run [.cx (ancWire n p.2) (addrWire m t)] (BoundedGate.run (conjLadder l) x))
      = Function.update x (addrWire m t) (x (addrWire m t) ^^ ladderChain l x) := by
    funext s
    by_cases hst : BoundedGate.touches (conjLadder l).reverse s
    · have h1 : BoundedGate.run (conjLadder l).reverse
            (BoundedGate.run [.cx (ancWire n p.2) (addrWire m t)] (BoundedGate.run (conjLadder l) x)) s
          = BoundedGate.run (conjLadder l).reverse (BoundedGate.run (conjLadder l) x) s := by
        refine BoundedGate.run_congr_touched (conjLadder l).reverse ?_ ?_ s hst
        · intro g hg
          exact hwell g (List.mem_reverse.mp hg)
        · intro g hg s' hs'
          have hgL : g ∈ conjLadder l := List.mem_reverse.mp hg
          have hne : s' ≠ addrWire m t := by
            intro hne
            exact hnotouch ⟨g, hgL, hne ▸ hs'⟩
          rw [hctrlraw]
          simp [Function.update, hne]
      have hne : s ≠ addrWire m t := by
        intro hne
        obtain ⟨g, hg, hs'⟩ := (BoundedGate.touches_reverse (conjLadder l) s).mp hst
        exact hnotouch ⟨g, hg, hne ▸ hs'⟩
      rw [h1, hinv]
      simp [Function.update, hne]
    · have h1 : BoundedGate.run (conjLadder l).reverse
            (BoundedGate.run [.cx (ancWire n p.2) (addrWire m t)] (BoundedGate.run (conjLadder l) x)) s
          = BoundedGate.run [.cx (ancWire n p.2) (addrWire m t)]
              (BoundedGate.run (conjLadder l) x) s :=
        BoundedGate.run_untouched (conjLadder l).reverse _ hst
      rw [h1, hctrlraw]
      by_cases hcon : s = addrWire m t
      · subst hcon
        simp [Function.update]
        rw [haddr t, hconj]
      · simp [Function.update, hcon]
        have hsy : (BoundedGate.run (conjLadder l) x) s = x s := by
          refine BoundedGate.run_untouched (conjLadder l) x ?_
          intro h
          exact hst ((BoundedGate.touches_reverse (conjLadder l) s).mpr h)
        rw [hsy]
  have hrun : BoundedGate.run
      (conjLadder l ++ [.cx (ancWire n p.2) (addrWire m t)] ++ (conjLadder l).reverse) x
      = BoundedGate.run (conjLadder l).reverse
          (BoundedGate.run [.cx (ancWire n p.2) (addrWire m t)] (BoundedGate.run (conjLadder l) x)) := by
    rw [BoundedGate.run_append, BoundedGate.run_append]
  rw [hrun]
  exact hrest

/-- A nonempty all-true controlled program implements `mcxAllPerm` when auxiliary wires start
false, auxiliary destinations are distinct, and no control is the target. -/
theorem mcxProgramAll_run {n m : ℕ} (l : List (Fin n × Fin m)) (t : Fin n) (x : Reg (n + m))
    (hanc : ∀ a : Fin m, x (ancWire n a) = false)
    (hd : (ancOf l).Nodup)
    (ht : ∀ p ∈ l, p.1 ≠ t) :
    ∀ (tail : List (Fin n × Fin m)) (p : Fin n × Fin m), l = tail ++ [p] →
      BoundedGate.run (mcxProgramAll l t) x = mcxAllPerm l t x := by
  intro tail p hp
  have hlp : lastPair l = some p := by
    rw [hp]
    exact lastPair_append_singleton tail p
  have hprog : mcxProgramAll l t
      = conjLadder l ++ [.cx (ancWire n p.2) (addrWire m t)] ++ (conjLadder l).reverse := by
    simp [mcxProgramAll, hlp]
  have hrun : BoundedGate.run (mcxProgramAll l t) x
      = BoundedGate.run (conjLadder l).reverse
          (BoundedGate.run [.cx (ancWire n p.2) (addrWire m t)] (BoundedGate.run (conjLadder l) x)) := by
    rw [hprog, BoundedGate.run_append, BoundedGate.run_append]
  have hmid : BoundedGate.run (conjLadder l).reverse
        (BoundedGate.run [.cx (ancWire n p.2) (addrWire m t)] (BoundedGate.run (conjLadder l) x))
      = Function.update x (addrWire m t) (x (addrWire m t) ^^ ladderChain l x) := by
    have h1 := mcxMiddle_run l t x hanc hd ht tail p hp
    rw [BoundedGate.run_append, BoundedGate.run_append] at h1
    exact h1
  rw [hrun, hmid]
  have hcond : ladderChain l x = true ↔ ∀ c ∈ l.map (fun q => q.1), x (addrWire m c) := by
    rw [ladderChain_eq_ctrlConjAll]
    simp only [ctrlConjAll, List.all_eq_true]
    constructor
    · intro h c hc
      obtain ⟨q, hq, hq1⟩ : ∃ q ∈ l, q.1 = c := List.mem_map.mp hc
      have hmem : x (addrWire m c) ∈ l.map (fun p => x (addrWire m p.1)) := by
        rw [List.mem_map]
        exact ⟨q, hq, by rw [hq1]⟩
      have hval := h (x (addrWire m c)) hmem
      simpa using! hval
    · intro h y hy
      rw [List.mem_map] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      exact h q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩)
  by_cases hc : ∀ c ∈ l.map (fun q => q.1), x (addrWire m c)
  · have hchain : ladderChain l x = true := (hcond).2 hc
    rw [mcxAllPerm, if_pos hc]
    simp [hchain]
  · have hchain : ladderChain l x = false := by
      have hne : ladderChain l x ≠ true := fun h => hc ((hcond).1 h)
      exact Bool.eq_false_of_not_eq_true hne
    rw [mcxAllPerm, if_neg hc]
    simp [hchain]

/-- A conjunction chain contains exactly one gate per control-destination pair. -/
theorem conjChain_length {n m : ℕ} : ∀ (l : List (Fin n × Fin m)) (prev : Fin m),
    (conjChain prev l).length = l.length := by
  intro l
  induction l with
  | nil => intro prev; rfl
  | cons p rest ih => intro prev; simp [conjChain, ih p.2]

/-- A conjunction ladder contains exactly one gate per control-destination pair. -/
theorem conjLadder_length {n m : ℕ} (l : List (Fin n × Fin m)) :
    (conjLadder l).length = l.length := by
  induction l with
  | nil => rfl
  | cons p rest ih => simp [conjLadder, conjAccum, conjChain_length]

/-- A list of distinct auxiliary indices has length at most the number of available auxiliary
wires. -/
theorem ancOf_length_le {n m : ℕ} (l : List (Fin n × Fin m)) (hd : (ancOf l).Nodup) :
    (ancOf l).length ≤ m := by
  have hcard := List.Nodup.length_le_card hd
  simpa using! hcard

/-- The all-true controlled program uses at most twice the number of control pairs plus one
gate. -/
theorem mcxProgramAll_gate_count {n m : ℕ} (l : List (Fin n × Fin m)) (t : Fin n) :
    (mcxProgramAll l t).length ≤ 2 * l.length + 1 := by
  cases hl : lastPair l with
  | none => simp [mcxProgramAll, hl]
  | some p =>
      simp [mcxProgramAll, hl, conjLadder_length]
      omega

/-- The matrix of the all-true controlled program equals the permutation matrix of its register
action. -/
theorem mcxProgramAll_matrix {n m : ℕ} (l : List (Fin n × Fin m)) (t : Fin n) :
    BoundedGate.wordMatrix (mcxProgramAll l t) = permMatrix (BoundedGate.run (mcxProgramAll l t)) :=
  BoundedGate.wordMatrix_eq_permMatrix _

/-- The address portion of `mcxPerm` agrees with the evaluation of the corresponding
pattern-controlled address gate. -/
theorem mcxPerm_addrGate {n : ℕ} (t : Fin n) (p : Reg n) (x : Reg (n + (n - 1))) :
    ∀ w : Fin n,
      mcxPerm t p x (addrWire (n - 1) w)
        = (Qatlib.Concepts.UniformBqp.Phi3Compile.AddrGate.eval ⟨t, p⟩ (fun w => x (addrWire (n - 1) w))) w := by
  intro w
  have hmatch : Qatlib.Concepts.UniformBqp.Phi3Compile.AddrGate.matches ⟨t, p⟩
        (fun w => x (addrWire (n - 1) w))
      ↔ ∀ w' : Fin n, w' ≠ t → x (addrWire (n - 1) w') = p w' := Iff.rfl
  by_cases h : ∀ w' : Fin n, w' ≠ t → x (addrWire (n - 1) w') = p w'
  · rw [mcxPerm, if_pos h]
    have hpos : Qatlib.Concepts.UniformBqp.Phi3Compile.AddrGate.matches ⟨t, p⟩
        (fun w => x (addrWire (n - 1) w)) := hmatch.mpr h
    rw [Qatlib.Concepts.UniformBqp.Phi3Compile.AddrGate.eval, if_pos hpos]
    by_cases hwt : w = t
    · subst hwt
      simp [Function.update]
    · have hne : addrWire (n - 1) w ≠ addrWire (n - 1) t :=
        fun h => hwt (addrWire_injective h)
      simp [Function.update, hne, hwt]
  · rw [mcxPerm, if_neg h]
    have hneg : ¬ Qatlib.Concepts.UniformBqp.Phi3Compile.AddrGate.matches ⟨t, p⟩
        (fun w => x (addrWire (n - 1) w)) := fun hp => h (hmatch.mp hp)
    rw [Qatlib.Concepts.UniformBqp.Phi3Compile.AddrGate.eval, if_neg hneg]

/-- Filtering a list with no repeated entries preserves the absence of repetitions. -/
theorem nodup_filter_of_nodup {α : Type} (p : α → Bool) :
    ∀ (l : List α), l.Nodup → (l.filter p).Nodup := by
  intro l
  induction l with
  | nil => intro hl; simp
  | cons a l ih =>
      intro hl
      have ha : a ∉ l := (List.nodup_cons.mp hl).1
      have hl' : l.Nodup := (List.nodup_cons.mp hl).2
      by_cases hpa : p a
      · simp only [List.filter_cons, if_pos hpa]
        exact List.nodup_cons.mpr ⟨by simp [ha], ih hl'⟩
      · simp only [List.filter_cons, if_neg hpa]
        exact ih hl'

/-- The list of wires other than a specified target has no repeated entries. -/
theorem otherWires_nodup {n : ℕ} (t : Fin n) : (otherWires t).Nodup := by
  unfold otherWires
  exact (List.nodup_finRange n).erase t

/-- Applying one bit flip at each address in a list without repetitions toggles exactly the
listed address bits. -/
theorem run_x_addr {n m : ℕ} : ∀ (l : List (Fin n)) (x : Reg (n + m)) (w : Fin n),
    l.Nodup →
      (BoundedGate.run (l.map (fun i => BoundedGate.x (addrWire m i))) x) (addrWire m w)
        = (x (addrWire m w) ^^ (if w ∈ l then true else false)) := by
  intro l
  induction l with
  | nil => intro x w hl; simp [BoundedGate.run]
  | cons a rest ih =>
      intro x w hl
      have ha : a ∉ rest := (List.nodup_cons.mp hl).1
      have hrest : rest.Nodup := (List.nodup_cons.mp hl).2
      simp only [List.map_cons, BoundedGate.run]
      rw [ih ((BoundedGate.x (addrWire m a)).act x) w hrest]
      by_cases hwa : w = a
      · subst hwa
        simp [BoundedGate.act, Function.update, ha]
      · have hne : addrWire m a ≠ addrWire m w := by
          intro h
          apply hwa
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp only [addrWire_val] at hv
          exact hv.symm
        have hne' : addrWire m w ≠ addrWire m a := fun h => hne h.symm
        simp [BoundedGate.act, Function.update, hne', hwa]

/-- Pattern preparation toggles exactly the non-target address bits where the prescribed pattern
is false. -/
theorem patternFix_run {n m : ℕ} (p : Reg n) (t : Fin n) (x : Reg (n + m)) (w : Fin n) :
    (BoundedGate.run (patternFix m p t) x) (addrWire m w)
      = (x (addrWire m w) ^^ (if w ∈ otherWires t ∧ p w = false then true else false)) := by
  have hnodup : ((otherWires t).filter (fun w => p w = false)).Nodup :=
    nodup_filter_of_nodup _ (otherWires t) (otherWires_nodup t)
  rw [patternFix, run_x_addr _ x w hnodup]
  simp only [List.mem_filter, decide_eq_true_eq]

/-- Pattern preparation preserves every auxiliary bit. -/
theorem patternFix_preserves_anc {n m : ℕ} (p : Reg n) (t : Fin n) (x : Reg (n + m)) :
    ∀ a : Fin m, (BoundedGate.run (patternFix m p t) x) (ancWire n a) = x (ancWire n a) := by
  intro a
  have hne : ¬ BoundedGate.touches (patternFix m p t) (ancWire n a) := by
    intro hmem
    obtain ⟨g, hg, hs⟩ := hmem
    rw [patternFix] at hg
    simp only [List.mem_map, List.mem_filter] at hg
    obtain ⟨w, hw, rfl⟩ := hg
    simp only [BoundedGate.support, List.mem_singleton] at hs
    exact absurd hs ((addrWire_ne_ancWire n m w a).symm)
  exact BoundedGate.run_untouched (patternFix m p t) x hne

/-- After pattern preparation, each non-target address bit indicates whether its original value
matched the prescribed pattern. -/
theorem patternFix_indicators {n m : ℕ} (p : Reg n) (t : Fin n) (x : Reg (n + m))
    (w : Fin n) (hw : w ≠ t) :
    (BoundedGate.run (patternFix m p t) x) (addrWire m w) = decide (x (addrWire m w) = p w) := by
  rw [patternFix_run]
  have hmem : w ∈ otherWires t := (otherWires_mem t).2 hw
  by_cases hp : p w = false
  · simp [hmem, hp]
  · simp [hmem, hp]

/-- The control-destination pairing for a target contains `n - 1` pairs. -/
theorem mcxPairs_length {n : ℕ} (t : Fin n) : (mcxPairs t).length = n - 1 := by
  simp [mcxPairs, otherWires_length, List.length_zip]

/-- The first components of the control-destination pairing are exactly the non-target address
wires. -/
theorem mcxPairs_map_fst {n : ℕ} (t : Fin n) :
    (mcxPairs t).map Prod.fst = otherWires t := by
  have h1 : (otherWires t).length ≤ (List.finRange (n - 1)).length := by
    simp [otherWires_length]
  have hz : (List.zip (otherWires t) (List.finRange (n - 1))).map Prod.fst = otherWires t :=
    List.map_fst_zip h1
  simpa only [mcxPairs] using! hz

/-- The second components of the control-destination pairing enumerate all `n - 1` auxiliary
wires. -/
theorem mcxPairs_map_snd {n : ℕ} (t : Fin n) :
    (mcxPairs t).map Prod.snd = List.finRange (n - 1) := by
  have h1 : (List.finRange (n - 1)).length ≤ (otherWires t).length := by
    simp [otherWires_length]
  have hz : (List.zip (otherWires t) (List.finRange (n - 1))).map Prod.snd = List.finRange (n - 1) :=
    List.map_snd_zip h1
  simpa only [mcxPairs] using! hz

/-- Extracting auxiliary destinations from a pair list equals mapping its second projection. -/
theorem ancOf_eq_map {n m : ℕ} (l : List (Fin n × Fin m)) :
    ancOf l = l.map Prod.snd := by
  induction l with
  | nil => rfl
  | cons p rest ih => cases p; simp [ancOf, ih]

/-- The auxiliary destinations in the target pairing enumerate `Fin (n - 1)` in order. -/
theorem mcxPairs_ancOf {n : ℕ} (t : Fin n) :
    ancOf (mcxPairs t) = List.finRange (n - 1) := by
  rw [ancOf_eq_map, mcxPairs_map_snd]

/-- The auxiliary destinations in the target pairing have no repetitions. -/
theorem mcxPairs_ancOf_nodup {n : ℕ} (t : Fin n) : (ancOf (mcxPairs t)).Nodup := by
  rw [mcxPairs_ancOf]
  exact List.nodup_finRange _

/-- Every address control in the target pairing differs from the target. -/
theorem mcxPairs_control_ne_target {n : ℕ} (t : Fin n) :
    ∀ p ∈ mcxPairs t, p.1 ≠ t := by
  intro p hp
  have h1 : p.1 ∈ (mcxPairs t).map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [mcxPairs_map_fst] at h1
  exact (otherWires_mem t).1 h1

/-- If a pair is the last pair of a list, the list decomposes as a prefix followed by that pair. -/
theorem exists_append_singleton_of_lastPair {n m : ℕ} :
    ∀ (l : List (Fin n × Fin m)) (p : Fin n × Fin m),
      lastPair l = some p → ∃ tail, l = tail ++ [p] := by
  intro l
  induction l with
  | nil => intro p h; simp [lastPair] at h
  | cons hd tl ih =>
    intro p h
    cases tl with
    | nil =>
        have hp : hd = p := by simpa [lastPair] using! h
        subst hp
        exact ⟨[], rfl⟩
    | cons q rest =>
        cases rest with
        | nil =>
            have hp : q = p := by simpa [lastPair] using! h
            subst hp
            exact ⟨[hd], by simp⟩
        | cons r rest' =>
            have h2 : lastPair (q :: r :: rest') = some p := by simpa [lastPair] using! h
            obtain ⟨tail, htail⟩ := ih p h2
            exact ⟨hd :: tail, by simp [htail]⟩

/-- Every nonempty pair list has a last pair. -/
theorem exists_lastPair_of_ne_nil {n m : ℕ} : ∀ (l : List (Fin n × Fin m)), l ≠ [] →
    ∃ p, lastPair l = some p := by
  intro l
  induction l with
  | nil => intro hl; simp at hl
  | cons hd tl ih =>
    intro hl
    cases tl with
    | nil => exact ⟨hd, rfl⟩
    | cons q rest =>
        obtain ⟨p, hp⟩ := ih (by simp)
        exact ⟨p, by simpa [lastPair] using! hp⟩

/-- Pattern preparation does not touch the target address wire. -/
theorem patternFix_not_touches_target {n m : ℕ} (p : Reg n) (t : Fin n) :
    ¬ BoundedGate.touches (patternFix m p t) (addrWire m t) := by
  intro hmem
  obtain ⟨g, hg, hs⟩ := hmem
  rw [patternFix] at hg
  simp only [List.mem_map, List.mem_filter] at hg
  obtain ⟨w, hw, rfl⟩ := hg
  simp only [BoundedGate.support, List.mem_singleton] at hs
  have hne : addrWire m t ≠ addrWire m w := by
    intro hcon
    have hwt : w = t := (addrWire_injective hcon).symm
    exact ((otherWires_mem t).1 hw.1) hwt
  exact absurd hs hne

/-- Pattern preparation does not touch any auxiliary wire. -/
theorem patternFix_not_touches_anc {n m : ℕ} (p : Reg n) (t : Fin n) (a : Fin m) :
    ¬ BoundedGate.touches (patternFix m p t) (ancWire n a) := by
  intro hmem
  obtain ⟨g, hg, hs⟩ := hmem
  rw [patternFix] at hg
  simp only [List.mem_map, List.mem_filter] at hg
  obtain ⟨w, hw, rfl⟩ := hg
  simp only [BoundedGate.support, List.mem_singleton] at hs
  exact absurd hs ((addrWire_ne_ancWire n m w a).symm)

/-- Every gate used for pattern preparation is well formed. -/
theorem patternFix_wellformed {n m : ℕ} (p : Reg n) (t : Fin n) :
    ∀ g ∈ patternFix m p t, g.wellformed := by
  intro g hg
  rw [patternFix] at hg
  simp only [List.mem_map] at hg
  obtain ⟨w, hw, rfl⟩ := hg
  simp [BoundedGate.wellformed]

/-- Reversing pattern preparation restores the original register except for a possibly changed
target bit. -/
theorem run_patternFix_reverse {n m : ℕ} (p : Reg n) (t : Fin n) (x y : Reg (n + m))
    (hy : ∀ s : Fin (n + m), s ≠ addrWire m t →
        y s = (BoundedGate.run (patternFix m p t) x) s) :
    BoundedGate.run (patternFix m p t).reverse y
      = Function.update x (addrWire m t) (y (addrWire m t)) := by
  have hwell : ∀ g ∈ patternFix m p t, g.wellformed := patternFix_wellformed p t
  have hnotouch : ¬ BoundedGate.touches (patternFix m p t) (addrWire m t) :=
    patternFix_not_touches_target p t
  have hnotouch' : ¬ BoundedGate.touches (patternFix m p t).reverse (addrWire m t) := by
    intro hmem
    exact hnotouch ((BoundedGate.touches_reverse (patternFix m p t) (addrWire m t)).mp hmem)
  have hinv : BoundedGate.run (patternFix m p t).reverse (BoundedGate.run (patternFix m p t) x) = x :=
    BoundedGate.run_reverse (patternFix m p t) x hwell
  funext s
  by_cases hst : s = addrWire m t
  · subst hst
    have h1 := BoundedGate.run_untouched (patternFix m p t).reverse y hnotouch'
    rw [h1]
    simp [Function.update]
  · by_cases htouch : BoundedGate.touches (patternFix m p t).reverse s
    · have hcong : BoundedGate.run (patternFix m p t).reverse y s
          = BoundedGate.run (patternFix m p t).reverse (BoundedGate.run (patternFix m p t) x) s := by
        refine BoundedGate.run_congr_touched (patternFix m p t).reverse ?_ ?_ s htouch
        · intro g hg
          exact hwell g (List.mem_reverse.mp hg)
        · intro g hg s' hs'
          have hne : s' ≠ addrWire m t := by
            intro hne
            exact hnotouch ⟨g, List.mem_reverse.mp hg, hne ▸ hs'⟩
          rw [hy s' hne]
      rw [hcong, hinv]
      simp [Function.update, hst]
    · have h1 := BoundedGate.run_untouched (patternFix m p t).reverse y (by
        intro hmem
        exact htouch hmem)
      rw [h1]
      have hxs : (BoundedGate.run (patternFix m p t) x) s = x s := by
        refine BoundedGate.run_untouched (patternFix m p t) x ?_
        intro hmem
        exact htouch ((BoundedGate.touches_reverse (patternFix m p t) s).mpr hmem)
      rw [hy s hst, hxs]
      simp [Function.update, hst]

/-- After pattern preparation, the conjunction of the non-target controls is true exactly when
every original non-target address bit matched the prescribed pattern. -/
theorem ladderChain_patternFix {n : ℕ} (t : Fin n) (p : Reg n) (x : Reg (n + (n - 1))) :
    ladderChain (mcxPairs t) (BoundedGate.run (patternFix (n - 1) p t) x) = true ↔
      ∀ w : Fin n, w ≠ t → x (addrWire (n - 1) w) = p w := by
  have hchain : ladderChain (mcxPairs t) (BoundedGate.run (patternFix (n - 1) p t) x)
      = ctrlConjAll (mcxPairs t) (BoundedGate.run (patternFix (n - 1) p t) x) :=
    ladderChain_eq_ctrlConjAll _ _
  rw [hchain, ctrlConjAll]
  have hmap : (mcxPairs t).map
        (fun q => (BoundedGate.run (patternFix (n - 1) p t) x) (addrWire (n - 1) q.1))
      = (otherWires t).map
        (fun w => (BoundedGate.run (patternFix (n - 1) p t) x) (addrWire (n - 1) w)) := by
    calc (mcxPairs t).map
          (fun q => (BoundedGate.run (patternFix (n - 1) p t) x) (addrWire (n - 1) q.1))
        = ((mcxPairs t).map (fun q => q.1)).map
            (fun w => (BoundedGate.run (patternFix (n - 1) p t) x) (addrWire (n - 1) w)) := by
            symm
            exact List.map_map
      _ = (otherWires t).map
            (fun w => (BoundedGate.run (patternFix (n - 1) p t) x) (addrWire (n - 1) w)) := by
            rw [mcxPairs_map_fst]
  rw [hmap, List.all_eq_true]
  constructor
  · intro h y hy
    have hmem : y ∈ otherWires t := (otherWires_mem t).2 hy
    have hz : (BoundedGate.run (patternFix (n - 1) p t) x) (addrWire (n - 1) y)
        ∈ (otherWires t).map
            (fun w => (BoundedGate.run (patternFix (n - 1) p t) x) (addrWire (n - 1) w)) :=
      List.mem_map.mpr ⟨y, hmem, rfl⟩
    have hzval := h _ hz
    have hind := patternFix_indicators p t x y hy
    rw [hind] at hzval
    simp at hzval
    exact hzval
  · intro h y hy
    rw [List.mem_map] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    have hne : w ≠ t := (otherWires_mem t).1 hw
    have hval := h w hne
    have hind := patternFix_indicators p t x w hne
    rw [hind]
    simp [hval]

/-- The pattern-controlled permutation preserves every wire other than the target address wire. -/
theorem mcxPerm_target_only {n m : ℕ} (t : Fin n) (p : Reg n) (x : Reg (n + m)) :
    ∀ s : Fin (n + m), s ≠ addrWire m t → mcxPerm t p x s = x s := by
  intro s hs
  rw [mcxPerm]
  split
  · simp [Function.update, hs]
  · rfl

/-- The pattern-controlled program uses at most `4 * (n - 1) + 1` gates. -/
theorem mcxProgram_gate_count {n : ℕ} (t : Fin n) (p : Reg n) :
    (mcxProgram t p).length ≤ 4 * (n - 1) + 1 := by
  have hfix : ((otherWires t).filter (fun w => p w = false)).length ≤ n - 1 := by
    have hle : ((otherWires t).filter (fun w => p w = false)).length
        ≤ (otherWires t).length := List.length_filter_le _ _
    rw [otherWires_length] at hle
    exact hle
  have hlad : (conjLadder (mcxPairs t)).length = n - 1 := by
    rw [conjLadder_length, mcxPairs_length]
  have hfix' : (patternFix (n - 1) p t).length ≤ n - 1 := by
    rw [patternFix, List.length_map]
    exact hfix
  have hlad' : (conjLadder (mcxPairs t)).reverse.length = n - 1 := by
    rw [List.length_reverse, hlad]
  have hfixrev : (patternFix (n - 1) p t).reverse.length = (patternFix (n - 1) p t).length := by
    rw [List.length_reverse]
  cases hl : lastPair (mcxPairs t) with
  | none =>
      simp only [mcxProgram, hl, List.length_cons, List.length_nil]
      omega
  | some a =>
      simp only [mcxProgram, hl, List.length_append, List.length_cons, List.length_nil]
      omega

/-- With initially false auxiliary wires, the pattern-controlled gate program implements
`mcxPerm` exactly. -/
theorem mcxProgram_run {n : ℕ} (t : Fin n) (p : Reg n) (x : Reg (n + (n - 1)))
    (hanc : ∀ a : Fin (n - 1), x (ancWire n a) = false) :
    BoundedGate.run (mcxProgram t p) x = mcxPerm t p x := by
  have hn1 : n = 1 ∨ 2 ≤ n := by
    by_cases h : n = 1
    · exact Or.inl h
    · right
      have hpos : 0 < n := Nat.zero_lt_of_lt t.isLt
      omega
  rcases hn1 with hn1 | hn2
  · rcases hn1 with rfl
    have hmcx : mcxPairs (t : Fin 1) = [] := by
      have hl := mcxPairs_length (t : Fin 1)
      simp only [Nat.sub_self] at hl
      exact List.eq_nil_of_length_eq_zero hl
    have hprog : mcxProgram (t : Fin 1) p = [.x (addrWire 0 t)] := by
      simp [mcxProgram, hmcx, lastPair]
    have hrun1 : BoundedGate.run [.x (addrWire 0 t)] x
        = Function.update x (addrWire 0 t) (x (addrWire 0 t) ^^ true) := by
      simp [BoundedGate.run, BoundedGate.act]
    have hcond : ∀ w : Fin 1, w ≠ (t : Fin 1) → x (addrWire 0 w) = p w := by
      intro w hw
      have hwv : w.val = 0 := by omega
      have htv : (t : Fin 1).val = 0 := by omega
      have hwt : w = t := Fin.ext (by omega)
      exact absurd hw (fun h => h hwt)
    rw [hprog, hrun1, mcxPerm, if_pos hcond]
  · have hne : mcxPairs t ≠ [] := by
      intro hmem
      have hl := mcxPairs_length t
      rw [hmem] at hl
      simp only [List.length_nil] at hl
      omega
    obtain ⟨pl, hlp⟩ := exists_lastPair_of_ne_nil (mcxPairs t) hne
    obtain ⟨tail, hp⟩ := exists_append_singleton_of_lastPair (mcxPairs t) pl hlp
    have hfixanc : ∀ a : Fin (n - 1),
        (BoundedGate.run (patternFix (n - 1) p t) x) (ancWire n a) = false := by
      intro a
      rw [patternFix_preserves_anc]
      exact hanc a
    have hmid : BoundedGate.run (conjLadder (mcxPairs t)).reverse
              (BoundedGate.run [.cx (ancWire n pl.2) (addrWire (n - 1) t)]
                (BoundedGate.run (conjLadder (mcxPairs t))
                  (BoundedGate.run (patternFix (n - 1) p t) x)))
        = Function.update (BoundedGate.run (patternFix (n - 1) p t) x) (addrWire (n - 1) t)
          ((BoundedGate.run (patternFix (n - 1) p t) x) (addrWire (n - 1) t)
            ^^ ladderChain (mcxPairs t) (BoundedGate.run (patternFix (n - 1) p t) x)) := by
      have h1 := mcxMiddle_run (mcxPairs t) t (BoundedGate.run (patternFix (n - 1) p t) x)
        hfixanc (mcxPairs_ancOf_nodup t) (mcxPairs_control_ne_target t) tail pl hp
      rw [BoundedGate.run_append, BoundedGate.run_append] at h1
      exact h1
    have hrun : BoundedGate.run (mcxProgram t p) x
        = BoundedGate.run (patternFix (n - 1) p t).reverse
            (BoundedGate.run (conjLadder (mcxPairs t)).reverse
              (BoundedGate.run [.cx (ancWire n pl.2) (addrWire (n - 1) t)]
                (BoundedGate.run (conjLadder (mcxPairs t))
                  (BoundedGate.run (patternFix (n - 1) p t) x)))) := by
      rw [mcxProgram]
      simp only [hlp]
      rw [BoundedGate.run_append, BoundedGate.run_append, BoundedGate.run_append,
        BoundedGate.run_append]
    have hnotouchfix : ¬ BoundedGate.touches (patternFix (n - 1) p t) (addrWire (n - 1) t) :=
      patternFix_not_touches_target p t
    have hfixtarget : (BoundedGate.run (patternFix (n - 1) p t) x) (addrWire (n - 1) t)
        = x (addrWire (n - 1) t) :=
      BoundedGate.run_untouched (patternFix (n - 1) p t) x hnotouchfix
    have hcomp : BoundedGate.run (mcxProgram t p) x
        = Function.update x (addrWire (n - 1) t)
            (x (addrWire (n - 1) t)
              ^^ ladderChain (mcxPairs t) (BoundedGate.run (patternFix (n - 1) p t) x)) := by
      rw [hrun, hmid]
      have hy : ∀ s : Fin (n + (n - 1)), s ≠ addrWire (n - 1) t →
          (Function.update (BoundedGate.run (patternFix (n - 1) p t) x) (addrWire (n - 1) t)
            ((BoundedGate.run (patternFix (n - 1) p t) x) (addrWire (n - 1) t)
              ^^ ladderChain (mcxPairs t) (BoundedGate.run (patternFix (n - 1) p t) x))) s
            = (BoundedGate.run (patternFix (n - 1) p t) x) s := by
        intro s hs
        simp [Function.update, hs]
      have h1 := run_patternFix_reverse p t x
        (Function.update (BoundedGate.run (patternFix (n - 1) p t) x) (addrWire (n - 1) t)
          ((BoundedGate.run (patternFix (n - 1) p t) x) (addrWire (n - 1) t)
            ^^ ladderChain (mcxPairs t) (BoundedGate.run (patternFix (n - 1) p t) x))) hy
      rw [h1]
      have hyv : (Function.update (BoundedGate.run (patternFix (n - 1) p t) x)
          (addrWire (n - 1) t)
          ((BoundedGate.run (patternFix (n - 1) p t) x) (addrWire (n - 1) t)
            ^^ ladderChain (mcxPairs t) (BoundedGate.run (patternFix (n - 1) p t) x)))
          (addrWire (n - 1) t)
          = (x (addrWire (n - 1) t)
            ^^ ladderChain (mcxPairs t) (BoundedGate.run (patternFix (n - 1) p t) x)) := by
        rw [hfixtarget]
        simp [Function.update]
      rw [hyv]
    rw [hcomp]
    by_cases hpat : ∀ w : Fin n, w ≠ t → x (addrWire (n - 1) w) = p w
    · have hch : ladderChain (mcxPairs t) (BoundedGate.run (patternFix (n - 1) p t) x) = true :=
        (ladderChain_patternFix t p x).2 hpat
      rw [hch, mcxPerm, if_pos hpat]
    · have hch : ladderChain (mcxPairs t) (BoundedGate.run (patternFix (n - 1) p t) x) = false := by
        have hne2 : ladderChain (mcxPairs t) (BoundedGate.run (patternFix (n - 1) p t) x) ≠ true :=
          fun h => hpat ((ladderChain_patternFix t p x).1 h)
        exact Bool.eq_false_of_not_eq_true hne2
      rw [hch, mcxPerm, if_neg hpat]
      funext s
      by_cases hst : s = addrWire (n - 1) t
      · subst hst
        simp [Function.update]
      · simp [Function.update, hst]

open Turing

/-- After `j` steps within the input length, the scan clock is in state zero with its tape head
moved right by `j` cells. -/
theorem scanClock_after (x : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    BitMachineAfter scanClockMachine (x.map some) j =
      some ⟨0, (Turing.Tape.move Turing.Dir.right)^[j] (Turing.Tape.mk₁ (x.map some))⟩ := by
  induction j with
  | zero =>
    have hzero : (Turing.Tape.move Turing.Dir.right)^[0] (Turing.Tape.mk₁ (x.map some)) =
        Turing.Tape.mk₁ (x.map some) := by simp [Function.iterate_zero]
    simp only [BitMachineAfter, Turing.TM0.init]
    rw [hzero]
    rfl
  | succ j ih =>
    have hj' : j ≤ x.length := Nat.le_of_succ_le hj
    have hjl : j < x.length := Nat.lt_of_succ_le hj
    have hhead : ((Turing.Tape.move Turing.Dir.right)^[j]
          (Turing.Tape.mk₁ (x.map some))).head = some x[j] := by
      rw [tape_iterate_move_right_head, List.getI_eq_getElem _ (by simpa using! hjl)]
      simp [List.getElem_map]
    simp only [BitMachineAfter]
    rw [ih hj', Option.bind_some]
    rw [show Turing.TM0.step scanClockMachine ⟨0,
            (Turing.Tape.move Turing.Dir.right)^[j] (Turing.Tape.mk₁ (x.map some))⟩ =
          some ⟨0, ((Turing.Tape.move Turing.Dir.right)^[j]
            (Turing.Tape.mk₁ (x.map some))).move Turing.Dir.right⟩ from
        TM0_step_eq_some scanClockMachine _ _ _ (by
          rw [show (⟨0, (Turing.Tape.move Turing.Dir.right)^[j]
                (Turing.Tape.mk₁ (x.map some))⟩ :
              Turing.TM0.Cfg (Option Bool) (Fin 1)).Tape.head = some x[j] from hhead]
          rfl)]
    congr 1
    rw [Function.iterate_succ_apply']

/-- The scan clock reaches a halting configuration after exactly the input length in steps. -/
theorem scanClock_halts (x : List Bool) :
    ∃ cfg : Turing.TM0.Cfg (Option Bool) (Fin 1),
      BitMachineAfter scanClockMachine (x.map some) x.length = some cfg ∧
        Turing.TM0.step scanClockMachine cfg = none := by
  have hafter := scanClock_after x x.length (le_refl _)
  have hheadN : ((Turing.Tape.move Turing.Dir.right)^[x.length]
        (Turing.Tape.mk₁ (x.map some))).head = none := by
    rw [tape_iterate_move_right_head, List.getI_eq_default _ (by simp)]
    rfl
  refine ⟨⟨0, (Turing.Tape.move Turing.Dir.right)^[x.length]
    (Turing.Tape.mk₁ (x.map some))⟩, hafter, ?_⟩
  rw [TM0_step_eq_none]
  simp [scanClockMachine, hheadN]

/-- Before the input length in steps, the scan clock has a configuration under
`BitMachineAfter`. -/
theorem scanClock_live_before (x : List Bool) (s : ℕ) (hs : s < x.length) :
    BitMachineAfter scanClockMachine (x.map some) s ≠ none := by
  have hafter := scanClock_after x s (Nat.le_of_lt hs)
  have hhead : ((Turing.Tape.move Turing.Dir.right)^[s]
        (Turing.Tape.mk₁ (x.map some))).head = some x[s] := by
    rw [tape_iterate_move_right_head, List.getI_eq_getElem _ (by simpa using! hs)]
    simp [List.getElem_map]
  have hstep : Turing.TM0.step scanClockMachine
      ⟨0, (Turing.Tape.move Turing.Dir.right)^[s] (Turing.Tape.mk₁ (x.map some))⟩ ≠ none := by
    intro h
    rw [TM0_step_eq_none] at h
    simp [scanClockMachine, hhead] at h
  have hnext : BitMachineAfter scanClockMachine (x.map some) (s + 1) ≠ none := by
    intro hn
    rw [BitMachineAfter, hafter, Option.bind_some] at hn
    exact hstep hn
  intro hn
  have hn' : BitMachineAfter scanClockMachine (x.map some) (s + 1) = none := by
    rw [BitMachineAfter, hn]
    rfl
  exact hnext hn'

/-- The scan clock halts within the stated linear bound and has a configuration at every earlier
step below the input length. -/
theorem scanClock_time_constructible (x : List Bool) :
    ∃ s, s ≤ 1 * x.length ^ 1 + 1 ∧
      ∃ cfg : Turing.TM0.Cfg (Option Bool) (Fin 1),
        BitMachineAfter scanClockMachine (x.map some) s = some cfg ∧
          Turing.TM0.step scanClockMachine cfg = none ∧
          ∀ s' < x.length, BitMachineAfter scanClockMachine (x.map some) s' ≠ none := by
  obtain ⟨cfg, hcfg, hstep⟩ := scanClock_halts x
  refine ⟨x.length, ?_, cfg, hcfg, hstep, ?_⟩
  · have hbound : 1 * x.length ^ 1 + 1 = x.length + 1 := by simp
    omega
  · intro s' hs'
    exact scanClock_live_before x s' hs'

/-- Before the deadline, the clocked machine performs the underlying transition and increments
its phase. -/
theorem clockedMachine_at {q m : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (i : Fin (m + 1)) (j : Fin (q + 1)) (γ : Option Bool) (h : i.val < m) :
    clockedMachine M m (clockedLabel (m := m) i j) γ =
      (M j γ).map fun p => (clockedLabel (m := m) ⟨i.val + 1, by omega⟩ p.1, p.2) := by
  simp only [clockedMachine, clockedPhase_label, clockedBase_label]
  split
  · rfl
  · rename_i hcond
    exfalso
    omega

/-- At the deadline phase, the clocked machine has no outgoing transition. -/
theorem clockedMachine_deadline {q m : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (j : Fin (q + 1)) (γ : Option Bool) :
    clockedMachine M m (clockedLabel (m := m) ⟨m, by omega⟩ j) γ = none := by
  simp only [clockedMachine, clockedPhase_label, clockedBase_label]
  split
  · rename_i hcond
    exfalso
    omega
  · rfl

/-- Before the deadline, a clocked configuration steps by applying the underlying instruction
and incrementing the phase. -/
theorem clockedMachine_step {q m : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (i : Fin (m + 1)) (j : Fin (q + 1)) (tape : Turing.Tape (Option Bool)) (h : i.val < m) :
    Turing.TM0.step (clockedMachine M m) ⟨clockedLabel i j, tape⟩ =
      (M j tape.head).map fun p =>
        ⟨clockedLabel ⟨i.val + 1, by omega⟩ p.1, TM0StmtApply tape p.2⟩ := by
  rw [TM0_step_apply, clockedMachine_at M i j tape.head h]
  cases hm : M j tape.head with
  | none => simp
  | some p => simp

/-- Fixing the coin in the clocked coin machine gives the clocked version of the corresponding
underlying machine. -/
theorem clockedCoinMachine_eq {q : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q + 1))) (m : ℕ) (c : Bool) :
    clockedCoinMachine M m c = clockedMachine (M c) m := rfl

/-- Up to the deadline, every successful underlying run lifts to a clocked run with the elapsed
time encoded in its label. -/
theorem clocked_run {q m : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (input : List (Option Bool)) :
    ∀ (s : ℕ) (hs : s ≤ m) (j : Fin (q + 1)) (tape : Turing.Tape (Option Bool)),
      BitMachineAfter M input s = some ⟨j, tape⟩ →
      BitMachineAfter (clockedMachine M m) input s =
        some ⟨clockedLabel ⟨s, by omega⟩ j, tape⟩ := by
  intro s
  induction s with
  | zero =>
    intro _ j tape hj
    have hinit : Turing.TM0.init input = ⟨j, tape⟩ := by
      simpa [BitMachineAfter] using! hj
    have hjval : (default : Fin (q + 1)) = j := by
      have h := congrArg (fun c : Turing.TM0.Cfg (Option Bool) (Fin (q + 1)) => c.q) hinit
      simpa [Turing.TM0.init] using! h
    have htapeval : tape = Turing.Tape.mk₁ input := by
      have h := congrArg (fun c : Turing.TM0.Cfg (Option Bool) (Fin (q + 1)) => c.Tape) hinit
      have h' : Turing.Tape.mk₁ input = tape := by
        simpa [Turing.TM0.init] using! h
      exact h'.symm
    subst hjval
    subst htapeval
    have hdef : (default : Fin (ClockedSize q m)) =
        clockedLabel ⟨0, by omega⟩ (default : Fin (q + 1)) := by
      apply Fin.ext
      simp [clockedLabel_val]
    simp only [BitMachineAfter, Turing.TM0.init]
    rw [hdef]
  | succ s ih =>
    intro hs j tape hj
    have hs' : s < m := by omega
    have hsplit : BitMachineAfter M input (s + 1) =
        (BitMachineAfter M input s).bind (Turing.TM0.step M) := rfl
    have hsome : (BitMachineAfter M input s).bind (Turing.TM0.step M) = some ⟨j, tape⟩ := by
      rw [← hsplit]
      exact hj
    obtain ⟨cfg0, hb, hstep⟩ := Option.bind_eq_some_iff.mp hsome
    have hrun := ih (Nat.le_of_succ_le hs) cfg0.q cfg0.Tape hb
    rw [BitMachineAfter, hrun, Option.bind_some]
    have hsteq : Turing.TM0.step (clockedMachine M m)
        ⟨clockedLabel ⟨s, by omega⟩ cfg0.q, cfg0.Tape⟩ =
        some ⟨clockedLabel ⟨s + 1, by omega⟩ j, tape⟩ := by
      rw [clockedMachine_step M ⟨s, by omega⟩ cfg0.q cfg0.Tape hs']
      rw [TM0_step_apply] at hstep
      obtain ⟨p, hmp, hinj⟩ := Option.map_eq_some_iff.mp hstep
      rw [hmp]
      simp only [Option.map_some]
      have hp1 : p.1 = j := congrArg Turing.TM0.Cfg.q hinj
      have hpt : TM0StmtApply cfg0.Tape p.2 = tape := congrArg Turing.TM0.Cfg.Tape hinj
      rw [hp1, hpt]
    exact hsteq

/-- An optional value distinct from `none` equals `some` value. -/
theorem exists_some_of_ne_none {α : Type} {o : Option α} (h : o ≠ none) :
    ∃ a, o = some a := by
  cases o with
  | none => exact absurd rfl h
  | some a => exact ⟨a, rfl⟩

/-- If `BitMachineAfter` is `none` at a given time, the machine reached a halting configuration
at an earlier time. -/
theorem exists_halt {q : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (input : List (Option Bool)) : ∀ m, BitMachineAfter M input m = none →
    ∃ s < m, ∃ cfg : Turing.TM0.Cfg (Option Bool) (Fin (q + 1)),
      BitMachineAfter M input s = some cfg ∧ Turing.TM0.step M cfg = none := by
  intro m
  induction m with
  | zero =>
    intro h
    exfalso
    simp [BitMachineAfter] at h
  | succ m ih =>
    intro h
    have hsplit : BitMachineAfter M input (m + 1) =
        (BitMachineAfter M input m).bind (Turing.TM0.step M) := rfl
    rw [hsplit] at h
    cases hb : BitMachineAfter M input m with
    | none =>
      obtain ⟨s, hs, cfg, hcfg, hstep⟩ := ih hb
      exact ⟨s, by omega, cfg, hcfg, hstep⟩
    | some cfg0 =>
      rw [hb] at h
      simp only [Option.bind_some] at h
      exact ⟨m, by omega, cfg0, hb, h⟩

/-- Every clocked machine reaches a halting configuration within `m + 1` steps. -/
theorem clocked_always_halts {q m : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (input : List (Option Bool)) :
    ∃ s ≤ m + 1, ∃ cfg : Turing.TM0.Cfg (Option Bool) (Fin (ClockedSize q m)),
      BitMachineAfter (clockedMachine M m) input s = some cfg ∧
        Turing.TM0.step (clockedMachine M m) cfg = none := by
  by_cases hlive : BitMachineAfter M input m = none
  · obtain ⟨s, hs, cfg, hcfg, hstep⟩ := exists_halt M input m hlive
    have hrun := clocked_run M input s (Nat.le_of_lt hs) cfg.q cfg.Tape hcfg
    have hM : M cfg.q cfg.Tape.head = none := by
      simpa using! ((TM0_step_eq_none M cfg).mp hstep)
    refine ⟨s, by omega, ⟨clockedLabel (m := m) ⟨s, by omega⟩ cfg.q, cfg.Tape⟩, hrun, ?_⟩
    rw [TM0_step_eq_none]
    by_cases hsl : s < m
    · rw [clockedMachine_at M ⟨s, by omega⟩ cfg.q cfg.Tape.head (by omega)]
      simp [hM]
    · have hsm : s = m := by omega
      subst hsm
      rw [clockedMachine_deadline M cfg.q cfg.Tape.head]
  · obtain ⟨cfg, hcfg⟩ := exists_some_of_ne_none (α := Turing.TM0.Cfg (Option Bool) (Fin (q + 1)))
      (fun h => hlive h)
    have hrun := clocked_run M input m (le_refl _) cfg.q cfg.Tape hcfg
    refine ⟨m, by omega, ⟨clockedLabel (m := m) ⟨m, by omega⟩ cfg.q, cfg.Tape⟩, hrun, ?_⟩
    rw [TM0_step_eq_none]
    exact clockedMachine_deadline M cfg.q cfg.Tape.head

/-- A halting underlying run within the deadline lifts to a halting clocked run with the same
acceptance label. -/
theorem clocked_halt_preserves {q m : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (accept : Fin (q + 1) → Bool) (input : List (Option Bool))
    (s : ℕ) (hs : s ≤ m) (j : Fin (q + 1)) (tape : Turing.Tape (Option Bool))
    (hcfg : BitMachineAfter M input s = some ⟨j, tape⟩)
    (hstep : Turing.TM0.step M ⟨j, tape⟩ = none) :
    ∃ cfg : Turing.TM0.Cfg (Option Bool) (Fin (ClockedSize q m)),
      BitMachineAfter (clockedMachine M m) input s = some cfg ∧
        Turing.TM0.step (clockedMachine M m) cfg = none ∧
        clockedAccept (m := m) accept cfg.q = accept j := by
  have hrun := clocked_run M input s hs j tape hcfg
  have hM : M j tape.head = none := by
    simpa using! ((TM0_step_eq_none M ⟨j, tape⟩).mp hstep)
  refine ⟨⟨clockedLabel (m := m) ⟨s, by omega⟩ j, tape⟩, hrun, ?_, ?_⟩
  · rw [TM0_step_eq_none]
    by_cases hsl : s < m
    · rw [clockedMachine_at M ⟨s, by omega⟩ j tape.head (by omega)]
      simp [hM]
    · have hsm : s = m := by omega
      subst hsm
      rw [clockedMachine_deadline M j tape.head]
  · simp [clockedAccept, clockedBase_label]

/-- A mapped optional value distinct from `none` equals `some` value. -/
theorem exists_some_of_map_ne_none {α β : Type} {f : α → β} {o : Option α} (h : o.map f ≠ none) :
    ∃ b, o.map f = some b := by
  cases o with
  | none => simp at h
  | some a => exact ⟨f a, by simp⟩

/-- Clocking preserves the agreement of the two coin branches on whether a transition is absent. -/
theorem clockedCoinMachine_shared {q m : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (hshared : ∀ ql γ, (M false ql γ = none) ↔ (M true ql γ = none))
    (l : Fin (ClockedSize q m)) (γ : Option Bool) :
    (clockedCoinMachine M m false l γ = none) ↔ (clockedCoinMachine M m true l γ = none) := by
  simp only [clockedCoinMachine, clockedMachine]
  by_cases hlive : (clockedPhase l).val < m
  · simp [hlive, Option.map_eq_none_iff]
    exact hshared (clockedBase l) γ
  · simp [hlive]

/-- The clocked coin machine satisfies its halting test at the deadline phase. -/
theorem coinHalt_clocked_deadline {q m : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (j : Fin (q + 1)) (tape : Turing.Tape (Option Bool)) :
    coinHalt (clockedCoinMachine M m) ⟨clockedLabel ⟨m, by omega⟩ j, tape⟩ = true := by
  rw [coinHalt]
  simp [clockedCoinMachine, clockedMachine, clockedPhase_label]

/-- Starting at phase `s`, a coin sequence with length plus `s` at least `m + 1` produces a
nonempty result from the clocked coin-run procedure. -/
theorem clockedCoin_aux {q m : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (accept : Fin (q + 1) → Bool) :
    ∀ (coins : List Bool) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (ClockedSize q m)))
      (s : ℕ) (hs : s ≤ m),
      (cfg.q = clockedLabel (m := m) ⟨s, by omega⟩ (clockedBase cfg.q)) →
      coins.length + s ≥ m + 1 →
      (coinTapeRunAux (clockedCoinMachine M m) (clockedCoinAccept accept) coins cfg).1 ≠ none := by
  intro coins
  induction coins with
  | nil =>
    intro cfg s hs hph hlen
    exfalso
    have hlen' : 0 + s ≥ m + 1 := by simpa using! hlen
    omega
  | cons c cs ih =>
    intro cfg s hs hph hlen
    rw [coinTapeRunAux]
    by_cases hh : coinHalt (clockedCoinMachine M m) cfg = true
    · rw [if_pos hh]
      simp
    · rw [if_neg hh]
      have hs' : s < m := by
        by_contra hcon
        have hsm : s = m := by omega
        have h1 : clockedPhase cfg.q = ⟨s, by omega⟩ := by
          have hcongr := congrArg clockedPhase hph
          rw [clockedPhase_label] at hcongr
          exact hcongr
        have h2 : clockedPhase cfg.q = ⟨m, by omega⟩ := by
          rw [h1]
          congr 1
        have hcfgq : cfg.q = clockedLabel (m := m) ⟨m, by omega⟩ (clockedBase cfg.q) := by
          calc cfg.q = clockedLabel (clockedPhase cfg.q) (clockedBase cfg.q) :=
              clockedLabel_decompose cfg.q
            _ = clockedLabel (m := m) ⟨m, by omega⟩ (clockedBase cfg.q) := by rw [h2]
        have hhalt : coinHalt (clockedCoinMachine M m) cfg = true := by
          have hh' := coinHalt_clocked_deadline (m := m) M (clockedBase cfg.q) cfg.Tape
          unfold coinHalt at hh' ⊢
          rw [hcfgq]
          exact hh'
        exact absurd hhalt hh
      have hstepform : Turing.TM0.step (clockedCoinMachine M m c) cfg =
          (M c (clockedBase cfg.q) cfg.Tape.head).map
            (fun p : Fin (q + 1) × Turing.TM0.Stmt (Option Bool) =>
              Turing.TM0.Cfg.mk (clockedLabel (m := m) ⟨s + 1, by omega⟩ p.1)
                (TM0StmtApply cfg.Tape p.2)) := by
        rw [clockedCoinMachine_eq]
        have hcfg : cfg = ⟨clockedLabel (m := m) ⟨s, by omega⟩ (clockedBase cfg.q), cfg.Tape⟩ := by
          cases cfg with
          | mk q' t' =>
            rw [Turing.TM0.Cfg.mk.injEq]
            exact ⟨hph, rfl⟩
        refine Eq.trans (congrArg (fun cf : Turing.TM0.Cfg (Option Bool) (Fin (ClockedSize q m)) =>
          Turing.TM0.step (clockedMachine (M c) m) cf) hcfg) ?_
        exact clockedMachine_step (M c) ⟨s, by omega⟩ (clockedBase cfg.q) cfg.Tape hs'
      have hmap : (M c (clockedBase cfg.q) cfg.Tape.head).map
          (fun p : Fin (q + 1) × Turing.TM0.Stmt (Option Bool) =>
            Turing.TM0.Cfg.mk (clockedLabel (m := m) ⟨s + 1, by omega⟩ p.1)
              (TM0StmtApply cfg.Tape p.2)) = Turing.TM0.step (clockedCoinMachine M m c) cfg :=
        hstepform.symm
      by_cases hnone : (M c (clockedBase cfg.q) cfg.Tape.head).map
          (fun p : Fin (q + 1) × Turing.TM0.Stmt (Option Bool) =>
            Turing.TM0.Cfg.mk (clockedLabel (m := m) ⟨s + 1, by omega⟩ p.1)
              (TM0StmtApply cfg.Tape p.2)) = none
      · have hstepnone : Turing.TM0.step (clockedCoinMachine M m c) cfg = none := by
          rw [← hmap, hnone]
        rw [hstepnone]
        simp
      · obtain ⟨cfg', hcfg'⟩ := exists_some_of_map_ne_none hnone
        have hstep' : Turing.TM0.step (clockedCoinMachine M m c) cfg = some cfg' := by
          rw [← hmap, hcfg']
        rw [hstep']
        obtain ⟨p, hmp, hcfgp⟩ := Option.map_eq_some_iff.mp hcfg'
        have hq' : cfg'.q = clockedLabel (m := m) ⟨s + 1, by omega⟩ p.1 := by
          have h := congrArg Turing.TM0.Cfg.q hcfgp
          simpa using! h.symm
        have hph' : cfg'.q = clockedLabel (m := m) ⟨s + 1, by omega⟩ (clockedBase cfg'.q) := by
          rw [hq']
          simp [clockedBase_label]
        have hlen' : cs.length + (s + 1) ≥ m + 1 := by
          have hlen'' : cs.length + 1 + s ≥ m + 1 := by simpa using! hlen
          omega
        have hrec := ih cfg' (s + 1) (by omega) hph' hlen'
        simpa using! hrec

/-- The clocked coin branches share their halting condition, and every coin sequence of length
at least `m + 1` yields a nonempty decision result. -/
theorem clockedCoin_terminates {q m : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (accept : Fin (q + 1) → Bool)
    (hshared : ∀ ql γ, (M false ql γ = none) ↔ (M true ql γ = none))
    (input : List (Option Bool)) :
    (∀ l γ, (clockedCoinMachine M m false l γ = none) ↔
      (clockedCoinMachine M m true l γ = none)) ∧
      ∀ (t : ℕ) (ω : Fin t → Bool), m + 1 ≤ t →
        (coinTapeRun (clockedCoinMachine M m) (clockedCoinAccept accept) input (List.ofFn ω)).1 ≠ none := by
  refine ⟨clockedCoinMachine_shared M hshared, ?_⟩
  intro t ω ht
  have hinit : (Turing.TM0.init input :
      Turing.TM0.Cfg (Option Bool) (Fin (ClockedSize q m))).q =
      clockedLabel (m := m) ⟨0, by omega⟩ (clockedBase (m := m) (Turing.TM0.init input).q) := by
    apply Fin.ext
    simp [clockedLabel_val, clockedBase, Turing.TM0.init]
  have hcoins : (List.ofFn ω).length + 0 ≥ m + 1 := by
    have hlen : (List.ofFn ω).length = t := by simp
    rw [hlen, add_zero]
    exact ht
  have hrec := clockedCoin_aux M accept (List.ofFn ω) (Turing.TM0.init input) 0
    (by omega) hinit hcoins
  simpa [coinTapeRun] using! hrec

/-- Applying a Boolean function to the acceptance labels maps the optional result of a bounded
tape decision run by that function. -/
theorem tapeDecisionRun_map {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (M : Turing.TM0.Machine Γ Λ) (accept : Λ → Bool) (g : Bool → Bool) :
    ∀ (t : ℕ) (cfg : Turing.TM0.Cfg Γ Λ),
      tapeDecisionRun M (fun l => g (accept l)) t cfg =
        (tapeDecisionRun M accept t cfg).map g := by
  intro t
  induction t with
  | zero =>
    intro cfg
    simp only [tapeDecisionRun]
    by_cases h : Turing.TM0.step M cfg = none
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h]
      rfl
  | succ t ih =>
    intro cfg
    simp only [tapeDecisionRun]
    cases hs : Turing.TM0.step M cfg with
    | none => rfl
    | some cfg' =>
      simp only [ih]

/-- Negating the acceptance labels negates the optional result of a bounded tape decision. -/
theorem tapeDecision_neg {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (M : Turing.TM0.Machine Γ Λ) (accept : Λ → Bool) :
    ∀ (input : List Γ) (t : ℕ),
      tapeDecision M (fun l => !accept l) input t = (tapeDecision M accept input t).map Bool.not := by
  intro input t
  unfold tapeDecision
  exact tapeDecisionRun_map M accept Bool.not t (Turing.TM0.init input)

/-- The class `TapeInP` is closed under complement. -/
theorem tapeInP_complement (L : List Bool → Prop) (hL : TapeInP L) :
    TapeInP (fun x => ¬ L x) := by
  obtain ⟨q, M, accept, c, k, hbound⟩ := hL
  refine ⟨q, M, fun l => !accept l, c, k, ?_⟩
  intro input
  obtain ⟨t, ht, hdec⟩ := hbound input
  refine ⟨t, ht, ?_⟩
  rw [tapeDecision_neg, hdec]
  simp

/-- Validity of a gate operation is equivalent to legality of its local reflection-gate
interpretation. -/
theorem dLambdaValid_iff {n : ℕ} {op : DLambdaOp n} :
    dLambdaValid op ↔ reflectionGateLegal (dLambdaReflection op) := by
  cases op with
  | hGate i =>
      simp [dLambdaValid, dLambdaReflection, reflectionGateLegal, hadamard_unitary]
  | tGate i =>
      simp [dLambdaValid, dLambdaReflection, reflectionGateLegal, tGate_mem_unitary]
  | tGateAdj i =>
      simp [dLambdaValid, dLambdaReflection, reflectionGateLegal, tGateAdj_mem_unitary]
  | cnot c t => simp [dLambdaValid, dLambdaReflection, reflectionGateLegal]

/-- A valid operation list compiles to a unitary circuit with zero queries and exactly one gate
per operation. -/
theorem dLambdaCircuit_counts {n : ℕ} (ops : List (DLambdaOp n))
    (hops : ∀ op ∈ ops, dLambdaValid op) :
    IsUnitaryCircuit (dLambdaCircuit ops) ∧
      QueryCount (dLambdaCircuit ops) = 0 ∧
      GateCount (dLambdaCircuit ops) = ops.length := by
  have hlegal : reflectionLegal (ops.map dLambdaReflection) := by
    intro g hg
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hg
    exact (dLambdaValid_iff).mp (hops op hop)
  obtain ⟨hU, hq, hg⟩ :=
    local_reflection_gate_support_unitarity_counts n (ops.map dLambdaReflection) hlegal
  refine ⟨hU, hq, ?_⟩
  rw [dLambdaCircuit, gateCount_reflectionCompile]
  simp

/-- The size of a compiled operation list equals its length. -/
theorem dLambdaCircuit_size {n : ℕ} (ops : List (DLambdaOp n)) :
    Size (dLambdaCircuit ops) = ops.length := by
  simp [Size, dLambdaCircuit, reflectionCompile, List.length_map]

/-- The reflection-gate interpretation of the Toffoli decomposition equals `toffoliLocalSteps`. -/
theorem dLambdaToffoli_reflection {n : ℕ} (a b t : Fin n) :
    (dLambdaToffoli a b t).map dLambdaReflection = toffoliLocalSteps a b t := by
  rfl

/-- For three distinct wires, the 15-operation decomposition is valid and acts exactly as a
Toffoli gate on every basis ket. -/
theorem dLambdaToffoli_exact {n : ℕ} (a b t : Fin n)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    (dLambdaToffoli a b t).length = 15 ∧
    (∀ op ∈ dLambdaToffoli a b t, dLambdaValid op) ∧
    ∀ x : Reg n,
      Run (1 : Matrix (Reg n) (Reg n) ℂ) (dLambdaCircuit (dLambdaToffoli a b t)) (Qatlib.Foundations.PureStateMath.Ket x)
        = Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (x a && x b))) := by
  obtain ⟨hlen, hlegal, hexact⟩ := local_toffoli_fifteen_exact n a b t hab hat hbt
  refine ⟨hlen, ?_, ?_⟩
  · intro op hop
    have hop' : dLambdaReflection op ∈ toffoliLocalSteps a b t := by
      rw [← dLambdaToffoli_reflection]
      exact List.mem_map.mpr ⟨op, hop, rfl⟩
    exact (dLambdaValid_iff).mpr (hlegal (dLambdaReflection op) hop')
  · intro x
    rw [dLambdaCircuit, dLambdaToffoli_reflection]
    exact hexact x

/-- The fourth power of the T gate, grouped into two pairs, equals the Pauli Z matrix. -/
theorem tGate_four_eq_pauliZ : (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate * Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate) * (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate * Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate) = PauliZ := by
  have hexp : Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) ^ 4 = -1 := by
    rw [← Complex.exp_nat_mul]
    have hcast : (4 : ℕ) * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)
        = ((Real.pi : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hcast, Complex.exp_pi_mul_I]
  unfold Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate Rz PauliZ
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    cases i with
    | false => simp only [Bool.false_eq_true, if_false]; ring
    | true =>
      simp only [if_true]
      calc
        Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
            (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I))
            = Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) ^ 4 := by ring
        _ = -1 := hexp
  · simp [hij]

/-- The reflection interpretation of the NOT decomposition is a Hadamard, four T gates, and a
Hadamard on the chosen wire. -/
theorem dLambdaNot_reflection {n : ℕ} (i : Fin n) :
    (dLambdaNot i).map dLambdaReflection =
      [Sum.inl (i, Hadamard), Sum.inl (i, Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate), Sum.inl (i, Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate),
        Sum.inl (i, Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate), Sum.inl (i, Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate), Sum.inl (i, Hadamard)] := by
  rfl

/-- The matrix of the NOT decomposition is the single-wire Pauli X gate. -/
theorem dLambdaNot_program_matrix {n : ℕ} (i : Fin n) :
    reflectionProgramMatrix ((dLambdaNot i).map dLambdaReflection)
      = wireGate n i PauliX := by
  rw [dLambdaNot_reflection]
  simp only [reflectionProgramMatrix, reflectionGateMatrix, Matrix.one_mul, wireGate_mul]
  congr 1
  calc
    (((((Hadamard * Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate) * Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate) * Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate) * Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate) * Hadamard)
        = (Hadamard * (((Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate * Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate) * Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate) * Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate)) * Hadamard := by
          simp [Matrix.mul_assoc]
    _ = (Hadamard * PauliZ) * Hadamard := by
          rw [show (((Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate * Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate) * Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate) * Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate) = (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate * Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate) * (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate * Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate) by
            simp [Matrix.mul_assoc], tGate_four_eq_pauliZ]
    _ = PauliX := Qatlib.Concepts.GateVocabulary.GateVocab.hadamard_z_conjugation

/-- A Pauli X matrix entry is one exactly when its Boolean indices are opposite, and is zero
otherwise. -/
theorem pauliX_apply (a b : Bool) : PauliX a b = if b = !a then 1 else 0 := by
  cases a <;> cases b <;> rfl

/-- The NOT decomposition flips the chosen bit of every basis ket exactly. -/
theorem dLambdaNot_ket {n : ℕ} (i : Fin n) (x : Reg n) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (dLambdaCircuit (dLambdaNot i)) (Qatlib.Foundations.PureStateMath.Ket x)
      = Qatlib.Foundations.PureStateMath.Ket (Function.update x i (!x i)) := by
  rw [dLambdaCircuit, run_reflectionCompile, dLambdaNot_program_matrix]
  rw [applyGate_wireGate_ket]
  by_cases hx : x i = true
  · have h1 : PauliX false (x i) = 1 := by rw [pauliX_apply]; simp [hx]
    have h2 : PauliX true (x i) = 0 := by rw [pauliX_apply]; simp [hx]
    rw [h1, h2]
    simp [hx]
  · have h1 : PauliX false (x i) = 0 := by rw [pauliX_apply]; simp [hx]
    have h2 : PauliX true (x i) = 1 := by rw [pauliX_apply]; simp [hx]
    rw [h1, h2]
    simp [hx]

open Qatlib
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.QtmSimulation.Phi3Compilation
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.CircuitImpl.Phi3Universal

/-- A general native machine has an exact window circuit with zero queries and at most twice the
square of `generalWindowSize n t` gates, preserving configuration Born probabilities in the
QTM framework of [BernsteinVazirani1997]. -/
theorem generalTheorem2_window {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : GeneralNativeMachine Q A) (n t : ℕ)
    (hn : 0 < n) (ht : 0 < t) :
    ∃ C : Circuit (WReg (generalWindowSize n t) Q A),
      IsUnitaryCircuit C ∧ QueryCount C = 0 ∧
        GateCount C ≤ 2 * generalWindowSize n t * generalWindowSize n t ∧
        ∀ (x : Fin n → A) (c : WindowCfg (generalWindowSize n t) Q A),
          Run (1 : Matrix (WReg (generalWindowSize n t) Q A)
            (WReg (generalWindowSize n t) Q A) ℂ) C
              (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))
            = windowEmbed ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
              Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M.localQTM n x)) ∧
          BornProb (Run (1 : Matrix (WReg (generalWindowSize n t) Q A)
            (WReg (generalWindowSize n t) Q A) ℂ) C
              (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))) (windowEncode c)
            = BornProb ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
              Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M.localQTM n x)) c := by
  obtain ⟨C, hC, hq, hg, hrun⟩ :=
    theorem2QtmCircuitSimulation Q A M.localQTM n (generalWindowSize n t) hn
      (lt_of_lt_of_le ht (generalWindowSize_ge_t n t))
      (generalWindowSize_ge_n n t)
  refine ⟨C, hC, hq, hg, ?_⟩
  intro x c
  exact hrun x c

/-- A general native machine has a unitary Phi3 simulation with zero queries, the stated gate
budget, normalized encoded states, and exact state and Born-probability transport for
`generalWindowSize n t` steps. -/
theorem generalPhi3_cellTable {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : GeneralNativeMachine Q A) (n t : ℕ)
    (hn : 0 < n) (ht : 0 < t) :
    ∃ gs : List (Phi3Gate (generalRegisterWidth Q A n t)),
      IsUnitaryCircuit (phi3Compile gs) ∧ QueryCount (phi3Compile gs) = 0 ∧
      GateCount (phi3Compile gs) = gs.length ∧
      gs.length ≤ generalWindowSize n t *
        ((2 * generalWindowSize n t - 1) * phi3PaddingBudget (3 * cellBasisWidth Q A) +
          (2 * generalWindowSize n t + 1) * phi3PaddingBudget (cellBasisWidth Q A)) ∧
      (∀ (x : Fin n → A) (c : WindowCfg (generalWindowSize n t) Q A),
        Normalized (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A)
          (generalBasisCode Q A) (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))) ∧
        Normalized (Run (1 : Matrix (Reg (generalRegisterWidth Q A n t))
            (Reg (generalRegisterWidth Q A n t)) ℂ) (phi3Compile gs)
          (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A)
            (generalBasisCode Q A) (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x))))) ∧
        Run (1 : Matrix (Reg (generalRegisterWidth Q A n t))
            (Reg (generalRegisterWidth Q A n t)) ℂ) (phi3Compile gs)
          (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A)
            (generalBasisCode Q A) (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))) =
          qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
            (windowEmbed ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
              Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M.localQTM n x))) ∧
        BornProb (Run (1 : Matrix (Reg (generalRegisterWidth Q A n t))
            (Reg (generalRegisterWidth Q A n t)) ℂ) (phi3Compile gs)
          (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A)
            (generalBasisCode Q A) (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))))
            (qtmPhi3Basis (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
              (windowEncode c)) =
          BornProb ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
            Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M.localQTM n x)) c) := by
  obtain ⟨gs, hgs, hq, hc, hlen, hx⟩ :=
    qtmPhi3WindowSimulation Q A M.localQTM (cellBasisWidth Q A) n (generalWindowSize n t)
      (cellBasisWidth_bound Q A) hn
      (lt_of_lt_of_le ht (generalWindowSize_ge_t n t))
      (generalWindowSize_ge_n n t)
  refine ⟨gs, hgs, hq, hc, hlen, ?_⟩
  intro x c
  simpa only [generalBasisCode, cellBasisWidth, generalWindowSize, generalRegisterWidth,
    generalWindowCells] using! hx x c

/-- For each positive input and time parameter, one Phi3 gate word reproduces all configuration
amplitudes after `generalWindowSize n t` machine steps. -/
theorem generalPhi3_uniform {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : GeneralNativeMachine Q A) (n t : ℕ)
    (hn : 0 < n) (ht : 0 < t) :
    ∃ gs : List (Phi3Gate (generalRegisterWidth Q A n t)),
      (∀ (x : Fin n → A) (c : WindowCfg (generalWindowSize n t) Q A),
        (Run (1 : Matrix (Reg (generalRegisterWidth Q A n t))
            (Reg (generalRegisterWidth Q A n t)) ℂ) (phi3Compile gs)
          (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
            (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))))
          (qtmPhi3Basis (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
            (windowEncode c)) =
        ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
          Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M.localQTM n x)) c) := by
  obtain ⟨gs, -, -, -, -, hsim⟩ := generalPhi3_cellTable M n t hn ht
  refine ⟨gs, fun x c => ?_⟩
  rw [(hsim x c).2.2.1]
  exact (qtmPhi3State_apply_basis (generalWindowSize n t) (cellBasisWidth Q A)
    (generalBasisCode Q A) (generalBasisCode_injective Q A) _ (windowEncode c)).trans
    (qtmPhi3_windowEmbed_image _ c)

/-- A Phi3 gate word reproduces every encoded configuration amplitude after `generalWindowSize n
t` steps for all inputs of length `n`. -/
theorem generalPhi3_amplitudeExact {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : GeneralNativeMachine Q A) (n t : ℕ)
    (hn : 0 < n) (ht : 0 < t) :
    ∃ gs : List (Phi3Gate (generalRegisterWidth Q A n t)),
      (∀ (x : Fin n → A) (c : WindowCfg (generalWindowSize n t) Q A),
        (Run (1 : Matrix (Reg (generalRegisterWidth Q A n t))
            (Reg (generalRegisterWidth Q A n t)) ℂ) (phi3Compile gs)
          (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
            (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))))
          (qtmPhi3Basis (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
            (windowEncode c)) =
        ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
          Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M.localQTM n x)) c) := by
  obtain ⟨gs, -, -, -, -, hsim⟩ := generalPhi3_cellTable M n t hn ht
  refine ⟨gs, fun x c => ?_⟩
  rw [(hsim x c).2.2.1]
  exact (qtmPhi3State_apply_basis (generalWindowSize n t) (cellBasisWidth Q A)
    (generalBasisCode Q A) (generalBasisCode_injective Q A) _ (windowEncode c)).trans
    (qtmPhi3_windowEmbed_image _ c)

/-- A Phi3 gate word reproduces every configuration Born probability after `generalWindowSize n
t` steps for all inputs of length `n`. -/
theorem generalPhi3_born {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : GeneralNativeMachine Q A) (n t : ℕ)
    (hn : 0 < n) (ht : 0 < t) :
    ∃ gs : List (Phi3Gate (generalRegisterWidth Q A n t)),
      (∀ (x : Fin n → A) (c : WindowCfg (generalWindowSize n t) Q A),
        BornProb (Run (1 : Matrix (Reg (generalRegisterWidth Q A n t))
            (Reg (generalRegisterWidth Q A n t)) ℂ) (phi3Compile gs)
          (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
            (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))))
            (qtmPhi3Basis (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
              (windowEncode c)) =
        BornProb ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
          Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M.localQTM n x)) c) := by
  obtain ⟨gs, -, -, -, -, hsim⟩ := generalPhi3_cellTable M n t hn ht
  exact ⟨gs, fun x c => (hsim x c).2.2.2⟩

/-- There exists a Phi3 gate word satisfying the stated length bound, together with the formulas
for the window cell count and register width. -/
theorem generalPhi3_resources {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : GeneralNativeMachine Q A) (n t : ℕ)
    (hn : 0 < n) (ht : 0 < t) :
    ∃ gs : List (Phi3Gate (generalRegisterWidth Q A n t)),
      gs.length ≤ generalWindowSize n t *
        ((2 * generalWindowSize n t - 1) * phi3PaddingBudget (3 * cellBasisWidth Q A) +
          (2 * generalWindowSize n t + 1) * phi3PaddingBudget (cellBasisWidth Q A)) ∧
      generalWindowCells n t = 2 * generalWindowSize n t + 1 ∧
      generalRegisterWidth Q A n t = generalWindowCells n t * cellBasisWidth Q A + 3 := by
  obtain ⟨gs, -, -, -, hlen, -⟩ := generalPhi3_cellTable M n t hn ht
  exact ⟨gs, hlen, rfl, rfl⟩

/-- A single Phi3 gate word reproduces both configuration Born probabilities and complex
amplitudes after `generalWindowSize n t` steps. -/
theorem generalPhi3_twoWay {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : GeneralNativeMachine Q A) (n t : ℕ)
    (hn : 0 < n) (ht : 0 < t) :
    ∃ gs : List (Phi3Gate (generalRegisterWidth Q A n t)),
      (∀ (x : Fin n → A) (c : WindowCfg (generalWindowSize n t) Q A),
        BornProb (Run (1 : Matrix (Reg (generalRegisterWidth Q A n t))
            (Reg (generalRegisterWidth Q A n t)) ℂ) (phi3Compile gs)
          (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
            (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))))
            (qtmPhi3Basis (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
              (windowEncode c)) =
        BornProb ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
          Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M.localQTM n x)) c) ∧
      (∀ (x : Fin n → A) (c : WindowCfg (generalWindowSize n t) Q A),
        (Run (1 : Matrix (Reg (generalRegisterWidth Q A n t))
            (Reg (generalRegisterWidth Q A n t)) ℂ) (phi3Compile gs)
          (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
            (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))))
          (qtmPhi3Basis (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
            (windowEncode c)) =
        ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
          Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M.localQTM n x)) c) := by
  obtain ⟨gs, -, -, -, -, hsim⟩ := generalPhi3_cellTable M n t hn ht
  refine ⟨gs, ⟨?_, ?_⟩⟩
  · intro x c
    exact (hsim x c).2.2.2
  · intro x c
    rw [(hsim x c).2.2.1]
    exact (qtmPhi3State_apply_basis (generalWindowSize n t) (cellBasisWidth Q A)
      (generalBasisCode Q A) (generalBasisCode_injective Q A) _ (windowEncode c)).trans
      (qtmPhi3_windowEmbed_image _ c)

/-- Packages the five local QTM conditions and the exact Phi3 state, amplitude, probability, and
resource guarantees for every general native machine. -/
theorem clause1_complete :
    ∀ (Q A : Type) [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
      (M : GeneralNativeMachine Q A),
    LocalQTMFiveConditions M.localQTM ∧
    (∀ (n t : ℕ), 0 < n → 0 < t →
      ∃ gs : List (Phi3Gate (generalRegisterWidth Q A n t)),
        IsUnitaryCircuit (phi3Compile gs) ∧ QueryCount (phi3Compile gs) = 0 ∧
        GateCount (phi3Compile gs) = gs.length ∧
        gs.length ≤ generalWindowSize n t *
          ((2 * generalWindowSize n t - 1) * phi3PaddingBudget (3 * cellBasisWidth Q A) +
            (2 * generalWindowSize n t + 1) * phi3PaddingBudget (cellBasisWidth Q A)) ∧
        (∀ (x : Fin n → A) (c : WindowCfg (generalWindowSize n t) Q A),
          Normalized (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A)
            (generalBasisCode Q A) (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))) ∧
          Normalized (Run (1 : Matrix (Reg (generalRegisterWidth Q A n t))
              (Reg (generalRegisterWidth Q A n t)) ℂ) (phi3Compile gs)
            (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
              (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x))))) ∧
          Run (1 : Matrix (Reg (generalRegisterWidth Q A n t))
              (Reg (generalRegisterWidth Q A n t)) ℂ) (phi3Compile gs)
            (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
              (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))) =
            qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
              (windowEmbed ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
                Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M.localQTM n x))) ∧
          BornProb (Run (1 : Matrix (Reg (generalRegisterWidth Q A n t))
              (Reg (generalRegisterWidth Q A n t)) ℂ) (phi3Compile gs)
            (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
              (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))))
              (qtmPhi3Basis (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
                (windowEncode c)) =
            BornProb ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
              Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M.localQTM n x)) c)) ∧
    (∀ (n t : ℕ), 0 < n → 0 < t →
      ∃ gs : List (Phi3Gate (generalRegisterWidth Q A n t)),
        (∀ (x : Fin n → A) (c : WindowCfg (generalWindowSize n t) Q A),
          BornProb (Run (1 : Matrix (Reg (generalRegisterWidth Q A n t))
              (Reg (generalRegisterWidth Q A n t)) ℂ) (phi3Compile gs)
            (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
              (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))))
              (qtmPhi3Basis (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
                (windowEncode c)) =
            BornProb ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
              Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M.localQTM n x)) c) ∧
        (∀ (x : Fin n → A) (c : WindowCfg (generalWindowSize n t) Q A),
          (Run (1 : Matrix (Reg (generalRegisterWidth Q A n t))
              (Reg (generalRegisterWidth Q A n t)) ℂ) (phi3Compile gs)
            (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
              (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))))
            (qtmPhi3Basis (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
              (windowEncode c)) =
          ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
            Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M.localQTM n x)) c)) ∧
    (∀ (n t : ℕ), 0 < n → 0 < t →
      ∃ gs : List (Phi3Gate (generalRegisterWidth Q A n t)),
        gs.length ≤ generalWindowSize n t *
          ((2 * generalWindowSize n t - 1) * phi3PaddingBudget (3 * cellBasisWidth Q A) +
            (2 * generalWindowSize n t + 1) * phi3PaddingBudget (cellBasisWidth Q A)) ∧
        generalWindowCells n t = 2 * generalWindowSize n t + 1 ∧
        generalRegisterWidth Q A n t = generalWindowCells n t * cellBasisWidth Q A + 3) := by
  intro Q A instQ instDecQ instA instDecA M
  refine ⟨M.fiveConditions, ?_, ?_, ?_⟩
  · intro n t hn ht
    exact generalPhi3_cellTable M n t hn ht
  · intro n t hn ht
    exact generalPhi3_twoWay M n t hn ht
  · intro n t hn ht
    exact generalPhi3_resources M n t hn ht

/-- Packages clocked termination, scan-clock bounds, shared coin halting, polynomial-time
complementation, valid gate compilation, exact Toffoli decomposition, and the failure of
`HeadStaySimulationSpec`. -/
theorem clause2_complete :
    (∀ (q m : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
      (input : List (Option Bool)),
      ∃ s ≤ m + 1, ∃ cfg : Turing.TM0.Cfg (Option Bool) (Fin (ClockedSize q m)),
        BitMachineAfter (clockedMachine M m) input s = some cfg ∧
          Turing.TM0.step (clockedMachine M m) cfg = none) ∧
    (∀ x : List Bool, ∃ s, s ≤ 1 * x.length ^ 1 + 1 ∧
      ∃ cfg : Turing.TM0.Cfg (Option Bool) (Fin 1),
        BitMachineAfter scanClockMachine (x.map some) s = some cfg ∧
          Turing.TM0.step scanClockMachine cfg = none ∧
          ∀ s' < x.length, BitMachineAfter scanClockMachine (x.map some) s' ≠ none) ∧
    (∀ (q m : ℕ) (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
      (hshared : ∀ ql γ, (M false ql γ = none) ↔ (M true ql γ = none))
      (l : Fin (ClockedSize q m)) (γ : Option Bool),
      (clockedCoinMachine M m false l γ = none) ↔
        (clockedCoinMachine M m true l γ = none)) ∧
    (∀ (q m : ℕ) (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
      (j : Fin (q + 1)) (tape : Turing.Tape (Option Bool)),
      coinHalt (clockedCoinMachine M m) ⟨clockedLabel ⟨m, by omega⟩ j, tape⟩ = true) ∧
    (∀ L : List Bool → Prop, TapeInP L → TapeInP (fun x => ¬ L x)) ∧
    (∀ (n : ℕ) (ops : List (DLambdaOp n)), (∀ op ∈ ops, dLambdaValid op) →
      IsUnitaryCircuit (dLambdaCircuit ops) ∧ QueryCount (dLambdaCircuit ops) = 0 ∧
        GateCount (dLambdaCircuit ops) = ops.length) ∧
    (∀ (n : ℕ) (a b t : Fin n), a ≠ b → a ≠ t → b ≠ t →
      (dLambdaToffoli a b t).length = 15 ∧
        (∀ op ∈ dLambdaToffoli a b t, dLambdaValid op) ∧
        ∀ x : Reg n,
          Run (1 : Matrix (Reg n) (Reg n) ℂ) (dLambdaCircuit (dLambdaToffoli a b t)) (Qatlib.Foundations.PureStateMath.Ket x)
            = Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (x a && x b)))) ∧
    ¬ HeadStaySimulationSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, clause1_headStaySimulationSpec_lightCone_false⟩
  · intro q m M input
    exact clocked_always_halts M input
  · intro x
    exact scanClock_time_constructible x
  · intro q m M hshared l γ
    exact clockedCoinMachine_shared M hshared l γ
  · intro q m M j tape
    exact coinHalt_clocked_deadline M j tape
  · intro L hL
    exact tapeInP_complement L hL
  · intro n ops hops
    exact dLambdaCircuit_counts ops hops
  · intro n a b t hab hat hbt
    exact dLambdaToffoli_exact a b t hab hat hbt

/-- The separator-based binary encodings of `(1, 21)` and `(5, 5)` coincide. -/
theorem emitterEncoding_ambiguous :
    (1 : ℕ).bits ++ [false] ++ (21 : ℕ).bits
      = (5 : ℕ).bits ++ [false] ++ (5 : ℕ).bits := by decide

/-- Once a bounded halting run returns a terminal configuration, every larger run budget returns
the same configuration. -/
theorem TM0HaltRun_stable {q : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    {x : Turing.TM0.Cfg (Option Bool) (Fin (q + 1))} {s : ℕ}
    {cfg : Turing.TM0.Cfg (Option Bool) (Fin (q + 1))}
    (h : TM0HaltRun M s x = some cfg) (hstep : Turing.TM0.step M cfg = none) :
    ∀ s' : ℕ, s ≤ s' → TM0HaltRun M s' x = some cfg := by
  induction s generalizing x with
  | zero =>
      intro s' hs'
      cases hstepx : Turing.TM0.step M x with
      | none =>
          have hx' : x = cfg := by simpa [TM0HaltRun, hstepx] using! h
          subst hx'
          clear h hstep
          induction s' with
          | zero => simp [TM0HaltRun, hstepx]
          | succ k ihk => simp [TM0HaltRun, hstepx]
      | some x' =>
          simp [TM0HaltRun, hstepx] at h
  | succ s ih =>
      intro s' hs'
      cases hstepx : Turing.TM0.step M x with
      | none =>
          have hx' : x = cfg := by simpa [TM0HaltRun, hstepx] using! h
          subst hx'
          clear h hstep
          induction s' with
          | zero => simp [TM0HaltRun, hstepx]
          | succ k ihk => simp [TM0HaltRun, hstepx]
      | some x' =>
          have hrec : TM0HaltRun M s x' = some cfg := by simpa [TM0HaltRun, hstepx] using! h
          have hrec' : ∀ s'' : ℕ, s ≤ s'' → TM0HaltRun M s'' x' = some cfg :=
            fun s'' h'' => ih (x := x') hrec s'' h''
          induction s' with
          | zero => omega
          | succ k ihk =>
              by_cases hk : k = s
              · have hk' : k + 1 = s + 1 := by omega
                rw [hk']
                simpa [TM0HaltRun, hstepx] using! hrec
              · have h2 : s ≤ k := by omega
                simp only [TM0HaltRun, hstepx]
                exact hrec' k h2

/-- Boolean lists are equal if their `some`-mapped lists have equal entries at every index when
padded by `none`. -/
private theorem map_some_inj_of_getD {out1 out2 : List Bool}
    (h : ∀ i, (out1.map some).getD i none = (out2.map some).getD i none) : out1 = out2 := by
  induction out1 generalizing out2 with
  | nil =>
      cases out2 with
      | nil => rfl
      | cons b bs =>
          have h0 := h 0
          simp at h0
  | cons a as ih =>
      cases out2 with
      | nil =>
          have h0 := h 0
          simp at h0
      | cons b bs =>
          have h0 := h 0
          have hab : a = b := Option.some.inj h0
          subst hab
          simp only [List.cons.injEq]
          refine ⟨trivial, ?_⟩
          exact ih (fun i => by
              have hh := h (i + 1)
              exact hh)

/-- A fixed deterministic tape machine on a fixed source cannot emit two different output words
under `TM0EmitsPoly`. -/
theorem TM0EmitsPoly_output_unique {q : ℕ}
    (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    {c d : ℕ} {src out1 out2 : List Bool}
    (h1 : TM0EmitsPoly M c d src out1) (h2 : TM0EmitsPoly M c d src out2) :
    out1 = out2 := by
  obtain ⟨s1, cfg1, _, hrun1, hstep1, ht1⟩ := h1
  obtain ⟨s2, cfg2, _, hrun2, hstep2, ht2⟩ := h2
  have hcfg : cfg1 = cfg2 := by
    rcases Nat.le_total s1 s2 with h | h
    · have hstable : TM0HaltRun M s2 (Turing.TM0.init (src.map some)) = some cfg1 :=
        TM0HaltRun_stable M hrun1 hstep1 s2 h
      exact Option.some.inj (hstable.symm.trans hrun2)
    · have hstable : TM0HaltRun M s1 (Turing.TM0.init (src.map some)) = some cfg2 :=
        TM0HaltRun_stable M hrun2 hstep2 s1 h
      exact (Option.some.inj (hstable.symm.trans hrun1)).symm
  subst hcfg
  have hagree : ∀ i : ℕ, (out1.map some).getD i none = (out2.map some).getD i none := by
    intro i
    rw [← ht1 i, ← ht2 i]
  exact map_some_inj_of_getD hagree

/-- Different required gate-count outputs at the colliding parameter pairs rule out the stated
uniform emission property. -/
theorem emitterClause_impossible_of_output_difference
    {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    {w : ℕ} {build : (n t : ℕ) → Circuit (WReg w Q A)}
    {q : ℕ} {emitter : Turing.TM0.Machine (Option Bool) (Fin (q + 1))} {c d : ℕ}
    (hne : (GateCount (build 1 21)).bits ++ [false]
        ≠ (GateCount (build 5 5)).bits ++ [false]) :
    ¬ (∀ (n t : ℕ), 0 < n → 0 < t → n ≤ t →
        TM0EmitsPoly emitter c d (n.bits ++ [false] ++ t.bits)
          ((GateCount (build n t)).bits ++ [false])) := by
  intro h
  have h1 := h 1 21 (by omega) (by omega) (by omega)
  have h2 := h 5 5 (by omega) (by omega) (by omega)
  have h2' : TM0EmitsPoly emitter c d ((1 : ℕ).bits ++ [false] ++ (21 : ℕ).bits)
      ((GateCount (build 5 5)).bits ++ [false]) := by
    rw [emitterEncoding_ambiguous]
    exact h2
  exact hne (TM0EmitsPoly_output_unique emitter h1 h2')

/-- A circuit formed by mapping each list entry to a gate has gate count equal to the list
length. -/
private theorem map_gate_gateCount {I : Type*} {ι : Type*}
    (l : List ι) (f : ι → Matrix I I ℂ) :
    GateCount (l.map (fun i => Step.gate (f i))) = l.length := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

/-- For positive `t`, a reference round has exactly `2 * t` gates. -/
theorem kRoundCircuit_gateCount {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (t : ℕ) (G : Matrix (GWindow Q A) (GWindow Q A) ℂ)
    (ht : 0 < t) : GateCount (kRoundCircuit t G) = 2 * t := by
  have hmap : GateCount ((List.finRange (2 * t - 1)).map (fun k => Step.gate (gUnitFull G k)))
      = 2 * t - 1 := by
    rw [map_gate_gateCount, List.length_finRange]
  simp only [kRoundCircuit, gateCount_append, gateCount_gate, gateCount_nil, hmap]
  omega

/-- For positive `t`, repeating the reference round `t` times has exactly `2 * t * t` gates. -/
theorem kRound_build_gateCount {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (t : ℕ) (G : Matrix (GWindow Q A) (GWindow Q A) ℂ)
    (ht : 0 < t) : GateCount (RepeatCircuit (kRoundCircuit t G) t) = 2 * t * t := by
  rw [gateCount_repeatCircuit, kRoundCircuit_gateCount t G ht]
  ring

/-- No deterministic polynomial emitter can output the reference construction's gate-count word
from the stated separator-based pair encoding for all valid parameter pairs. -/
theorem emitterClause_impossible_for_theorem2_build
    {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    {G : Matrix (GWindow Q A) (GWindow Q A) ℂ}
    {q : ℕ} {emitter : Turing.TM0.Machine (Option Bool) (Fin (q + 1))} {c d : ℕ} :
    ¬ (∀ (n t : ℕ), 0 < n → 0 < t → n ≤ t →
        TM0EmitsPoly emitter c d (n.bits ++ [false] ++ t.bits)
          ((GateCount (RepeatCircuit (kRoundCircuit t G) t)).bits ++ [false])) := by
  intro h
  have h1 := h 1 21 (by omega) (by omega) (by omega)
  have h2 := h 5 5 (by omega) (by omega) (by omega)
  have h2' : TM0EmitsPoly emitter c d ((1 : ℕ).bits ++ [false] ++ (21 : ℕ).bits)
      ((GateCount (RepeatCircuit (kRoundCircuit 5 G) 5)).bits ++ [false]) := by
    rw [emitterEncoding_ambiguous]
    exact h2
  have hout := TM0EmitsPoly_output_unique emitter h1 h2'
  have h1c : GateCount (RepeatCircuit (kRoundCircuit 21 G) 21) = 2 * 21 * 21 :=
    kRound_build_gateCount 21 G (by omega)
  have h2c : GateCount (RepeatCircuit (kRoundCircuit 5 G) 5) = 2 * 5 * 5 :=
    kRound_build_gateCount 5 G (by omega)
  rw [h1c, h2c] at hout
  have hne : (2 * 21 * 21 : ℕ).bits ++ [false] ≠ (2 * 5 * 5 : ℕ).bits ++ [false] := by
    decide
  exact hne hout

end StandardMachine
end Qatlib.Concepts.UniformBqp.Phi3Compile
