/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphConnect03.MainResults.Defs
import Mathlib.Data.List.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.GraphConnect03.MainResults.UpperBounds

open Qatlib.Papers.GraphConnect03.MainResults.Defs

structure DFSState (n : ℕ) where

  visited : Finset (Vertex n)

  stack : List (Vertex n)

  tree : Finset (Vertex n × Vertex n)

def initState {n : ℕ} (root : Vertex n) : DFSState n :=
  { visited := {root}, stack := [root], tree := ∅ }

def StepOk {n : ℕ} (G : Digraph n) (σ : DFSState n → Option (Vertex n))
    (st : DFSState n) : Prop :=
  match st.stack with
  | [] => True
  | u :: _ =>
      match σ st with
      | some v => G.adj u v = true ∧ v ∉ st.visited
      | none => ∀ v : Vertex n, G.adj u v = true → v ∈ st.visited

def dfsStep {n : ℕ} (σ : DFSState n → Option (Vertex n)) (st : DFSState n) :
    DFSState n :=
  match st.stack with
  | [] => st
  | u :: rest =>
      match σ st with
      | some v =>
          { visited := insert v st.visited
            stack := v :: u :: rest
            tree := insert (u, v) st.tree }
      | none => { visited := st.visited, stack := rest, tree := st.tree }

def dfsRun {n : ℕ} (σ : DFSState n → Option (Vertex n)) : ℕ → DFSState n → DFSState n
  | 0, st => st
  | k + 1, st => dfsRun σ k (dfsStep σ st)

def dfsMeasure {n : ℕ} (st : DFSState n) : ℕ :=
  2 * (n - st.visited.card) + st.stack.length

structure DFSInv {n : ℕ} (G : Digraph n) (r : Vertex n) (st : DFSState n) : Prop where

  root_mem : r ∈ st.visited

  reach : ∀ u ∈ st.visited, G.Reach r u

  stack_sub : ∀ u ∈ st.stack, u ∈ st.visited

  tree_edge : ∀ p ∈ st.tree, G.adj p.1 p.2 = true

  tree_ends : ∀ p ∈ st.tree, p.1 ∈ st.visited ∧ p.2 ∈ st.visited

  closed : ∀ u ∈ st.visited, u ∉ st.stack → ∀ v : Vertex n, G.adj u v = true → v ∈ st.visited

namespace DFSInv

variable {n : ℕ} {G : Digraph n} {r : Vertex n} {st : DFSState n}

theorem init {n : ℕ} {G : Digraph n} (r : Vertex n) : DFSInv G r (initState r) := by
  refine ⟨by simp [initState], ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    simp only [initState, Finset.mem_singleton] at hu
    rw [hu]
    exact Digraph.Reach.refl G r
  · intro u hu
    simp only [initState, List.mem_singleton] at hu
    rw [hu]
    simp [initState]
  · intro p hp
    simp [initState] at hp
  · intro p hp
    simp [initState] at hp
  · intro u hu hstack v hv
    simp only [initState, Finset.mem_singleton] at hu
    subst hu

    exact absurd (by simp [initState]) hstack

end DFSInv

theorem dfsStep_nil {n : ℕ} (σ : DFSState n → Option (Vertex n)) {st : DFSState n}
    (h : st.stack = []) : dfsStep σ st = st := by
  simp [dfsStep, h]

theorem dfsStep_stack_cons {n : ℕ} (σ : DFSState n → Option (Vertex n))
    {st : DFSState n} {u : Vertex n} {rest : List (Vertex n)} (h : st.stack = u :: rest)
    {v : Vertex n} (hf : σ st = some v) :
    (dfsStep σ st).stack = v :: u :: rest := by
  simp [dfsStep, h, hf]

theorem dfsStep_stack_pop {n : ℕ} (σ : DFSState n → Option (Vertex n))
    {st : DFSState n} {u : Vertex n} {rest : List (Vertex n)} (h : st.stack = u :: rest)
    (hf : σ st = none) :
    (dfsStep σ st).stack = rest := by
  simp [dfsStep, h, hf]

theorem dfsStep_visited_push {n : ℕ} (σ : DFSState n → Option (Vertex n))
    {st : DFSState n} {u : Vertex n} {rest : List (Vertex n)} (h : st.stack = u :: rest)
    {v : Vertex n} (hf : σ st = some v) :
    (dfsStep σ st).visited = insert v st.visited := by
  simp [dfsStep, h, hf]

theorem dfsStep_visited_pop {n : ℕ} (σ : DFSState n → Option (Vertex n))
    {st : DFSState n} {u : Vertex n} {rest : List (Vertex n)} (h : st.stack = u :: rest)
    (hf : σ st = none) :
    (dfsStep σ st).visited = st.visited := by
  simp [dfsStep, h, hf]

theorem dfsStep_tree_push {n : ℕ} (σ : DFSState n → Option (Vertex n))
    {st : DFSState n} {u : Vertex n} {rest : List (Vertex n)} (h : st.stack = u :: rest)
    {v : Vertex n} (hf : σ st = some v) :
    (dfsStep σ st).tree = insert (u, v) st.tree := by
  simp [dfsStep, h, hf]

theorem dfsStep_tree_pop {n : ℕ} (σ : DFSState n → Option (Vertex n))
    {st : DFSState n} {u : Vertex n} {rest : List (Vertex n)} (h : st.stack = u :: rest)
    (hf : σ st = none) :
    (dfsStep σ st).tree = st.tree := by
  simp [dfsStep, h, hf]

namespace DFSInv

variable {n : ℕ} {G : Digraph n} {r : Vertex n} {st : DFSState n}

theorem step {σ : DFSState n → Option (Vertex n)} (hσ : StepOk G σ st)
    (h : DFSInv G r st) : DFSInv G r (dfsStep σ st) := by
  rcases hs : st.stack with _ | ⟨u, rest⟩
  · simpa [dfsStep_nil σ hs] using h
  · cases hf : σ st with
    | none =>

      have hcu : ∀ w : Vertex n, G.adj u w = true → w ∈ st.visited := by
        have := hσ
        simpa [StepOk, hs, hf] using this
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [dfsStep_visited_pop σ hs hf]
        exact h.root_mem
      · intro w hw
        rw [dfsStep_visited_pop σ hs hf] at hw
        exact h.reach w hw
      · intro w hw
        rw [dfsStep_stack_pop σ hs hf] at hw
        rw [dfsStep_visited_pop σ hs hf]
        exact h.stack_sub w (by rw [hs]; exact List.mem_cons_of_mem u hw)
      · intro p hp
        rw [dfsStep_tree_pop σ hs hf] at hp
        exact h.tree_edge p hp
      · intro p hp
        rw [dfsStep_tree_pop σ hs hf] at hp
        rw [dfsStep_visited_pop σ hs hf]
        exact h.tree_ends p hp
      · intro w hw hnstack x hx
        rw [dfsStep_visited_pop σ hs hf] at hw
        rw [dfsStep_stack_pop σ hs hf] at hnstack
        rw [dfsStep_visited_pop σ hs hf]
        by_cases hwu : w = u
        · subst hwu
          exact hcu x hx
        · have hwstk : w ∉ st.stack := by
            rw [hs]
            intro hmem
            rcases List.mem_cons.mp hmem with h | h
            · exact hwu h
            · exact hnstack h
          exact h.closed w hw hwstk x hx
    | some v =>

      have hpu : G.adj u v = true ∧ v ∉ st.visited := by
        have := hσ
        simpa [StepOk, hs, hf] using this
      obtain ⟨hadj, hvnot⟩ := hpu
      have hu_mem : u ∈ st.visited := h.stack_sub u (by rw [hs]; exact List.mem_cons_self)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [dfsStep_visited_push σ hs hf]
        exact Finset.mem_insert_of_mem h.root_mem
      · intro w hw
        rw [dfsStep_visited_push σ hs hf] at hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Digraph.Reach.trans (h.reach u hu_mem) (Digraph.Reach.edge (G := G) hadj)
        · exact h.reach w hw
      · intro w hw
        rw [dfsStep_stack_cons σ hs hf] at hw
        rw [dfsStep_visited_push σ hs hf]
        rcases List.mem_cons.mp hw with rfl | hw
        · simp
        · rcases List.mem_cons.mp hw with rfl | hw
          · exact Finset.mem_insert_of_mem hu_mem
          · exact Finset.mem_insert_of_mem
              (h.stack_sub w (by rw [hs]; exact List.mem_cons_of_mem u hw))
      · intro p hp
        rw [dfsStep_tree_push σ hs hf] at hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact hadj
        · exact h.tree_edge p hp
      · intro p hp
        rw [dfsStep_tree_push σ hs hf] at hp
        rw [dfsStep_visited_push σ hs hf]
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact ⟨Finset.mem_insert_of_mem hu_mem, Finset.mem_insert_self v st.visited⟩
        · obtain ⟨h1, h2⟩ := h.tree_ends p hp
          exact ⟨Finset.mem_insert_of_mem h1, Finset.mem_insert_of_mem h2⟩
      · intro w hw hnstack x hx
        rw [dfsStep_visited_push σ hs hf] at hw
        rw [dfsStep_stack_cons σ hs hf] at hnstack
        rw [dfsStep_visited_push σ hs hf]
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exfalso
          exact hnstack (List.mem_cons_self)
        · have hwstk : w ∉ st.stack := by
            rw [hs]
            intro hmem
            rcases List.mem_cons.mp hmem with hwu | hwr
            · subst hwu
              exact hnstack (List.mem_cons_of_mem v (List.mem_cons_self))
            · exact hnstack (List.mem_cons_of_mem v (List.mem_cons_of_mem u hwr))
          exact Finset.mem_insert_of_mem (h.closed w hw hwstk x hx)

end DFSInv

theorem dfsRun_eq_self_of_nil {n : ℕ} {σ : DFSState n → Option (Vertex n)}
    {st : DFSState n} (h : st.stack = []) : ∀ k : ℕ, dfsRun σ k st = st := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      show dfsRun σ k (dfsStep σ st) = st
      rw [dfsStep_nil σ h, ih]

namespace DFSInv

variable {n : ℕ} {G : Digraph n} {r : Vertex n} {st : DFSState n}

theorem measure_step {σ : DFSState n → Option (Vertex n)} (hσ : StepOk G σ st)
    (hne : st.stack ≠ []) : dfsMeasure (dfsStep σ st) = dfsMeasure st - 1 := by
  rcases hs : st.stack with _ | ⟨u, rest⟩
  · exact absurd hs hne
  · cases hf : σ st with
    | none =>
      have hlen : rest.length + 1 = (u :: rest).length := rfl
      simp only [dfsMeasure, dfsStep_visited_pop σ hs hf, dfsStep_stack_pop σ hs hf,
        hs, List.length_cons]
      omega
    | some v =>
      have hpu : G.adj u v = true ∧ v ∉ st.visited := by
        have := hσ
        simpa [StepOk, hs, hf] using this
      obtain ⟨hadj, hvnot⟩ := hpu
      have hcard : (insert v st.visited).card = st.visited.card + 1 :=
        Finset.card_insert_of_notMem hvnot
      have hbound : st.visited.card < n := by
        have hle := Finset.card_le_univ (insert v st.visited)
        simp only [Vertex, Fintype.card_fin] at hle
        omega
      simp only [dfsMeasure, dfsStep_visited_push σ hs hf, dfsStep_stack_cons σ hs hf,
        hs, List.length_cons, hcard]
      omega

theorem run {σ : DFSState n → Option (Vertex n)} (hσ : ∀ st, StepOk G σ st) :
    ∀ (k : ℕ) (st : DFSState n), DFSInv G r st → DFSInv G r (dfsRun σ k st) := by
  intro k
  induction k with
  | zero => intro st h; exact h
  | succ k ih =>
      intro st h
      exact ih (dfsStep σ st) (h.step (hσ st))

theorem run_halts_aux {n : ℕ} {G : Digraph n} {r : Vertex n}
    {σ : DFSState n → Option (Vertex n)} (hσ : ∀ st, StepOk G σ st) :
    ∀ (k : ℕ) (st : DFSState n), DFSInv G r st → dfsMeasure st ≤ k →
      (dfsRun σ k st).stack = [] := by
  intro k
  induction k with
  | zero =>
      intro st _ hle
      have h0 : dfsMeasure st = 0 := Nat.le_zero.mp hle
      simp only [dfsMeasure] at h0
      have hsl : st.stack.length = 0 := by omega
      cases hstack : st.stack with
      | nil => simp [dfsRun, hstack]
      | cons a l => simp [hstack] at hsl
  | succ k ih =>
      intro st hinv hle
      by_cases hs : st.stack = []
      · show (dfsRun σ k (dfsStep σ st)).stack = []
        rw [dfsStep_nil σ hs, dfsRun_eq_self_of_nil hs k]
        exact hs
      · have hstep : DFSInv G r (dfsStep σ st) := hinv.step (hσ st)
        have hmeas : dfsMeasure (dfsStep σ st) = dfsMeasure st - 1 :=
          DFSInv.measure_step (st := st) (hσ st) hs
        exact ih (dfsStep σ st) hstep (by omega)

theorem run_halts {σ : DFSState n → Option (Vertex n)} (hσ : ∀ st, StepOk G σ st)
    (root : Vertex n) :
    (dfsRun σ (2 * n) (initState root)).stack = [] := by
  have hn : 0 < n := by have := root.isLt; omega
  have hmeasure : dfsMeasure (initState root) ≤ 2 * n := by
    simp only [dfsMeasure, initState, List.length_cons, List.length_nil]
    have hc : ({root} : Finset (Vertex n)).card = 1 := by simp
    rw [hc]
    omega
  exact run_halts_aux hσ (2 * n) (initState root) (init root) hmeasure

end DFSInv

theorem mem_visited_iff_reach {n : ℕ} {G : Digraph n} {r : Vertex n} {st : DFSState n}
    (hinv : DFSInv G r st) (hst : st.stack = []) (v : Vertex n) :
    v ∈ st.visited ↔ G.Reach r v := by
  constructor
  · intro hv
    exact hinv.reach v hv
  · intro hr
    induction hr with
    | refl => exact hinv.root_mem
    | tail _ hbc ih =>
        exact hinv.closed _ ih (by rw [hst]; simp) _ hbc

theorem connected_of_all_marked {n : ℕ} {M : UndirectedMatrix n} {r : Vertex n}
    {st : DFSState n} (hinv : DFSInv M.toDigraph r st) (hst : st.stack = [])
    (hall : st.visited = Finset.univ) : M.Connected := by
  intro s t
  have hs : M.toDigraph.Reach r s :=
    (mem_visited_iff_reach hinv hst s).mp (by rw [hall]; simp)
  have ht : M.toDigraph.Reach r t :=
    (mem_visited_iff_reach hinv hst t).mp (by rw [hall]; simp)
  exact Digraph.Reach.trans (M.reach_symm hs) ht

theorem not_connected_of_unmarked {n : ℕ} {M : UndirectedMatrix n} {r : Vertex n}
    {st : DFSState n} (hinv : DFSInv M.toDigraph r st) (hst : st.stack = [])
    {v : Vertex n} (hv : v ∉ st.visited) : ¬ M.Connected := by
  intro hc
  exact hv ((mem_visited_iff_reach hinv hst v).mpr (hc r v))

theorem visited_univ_iff_connected {n : ℕ} {M : UndirectedMatrix n}
    {σ : DFSState n → Option (Vertex n)} (hσ : ∀ st, StepOk M.toDigraph σ st)
    (root : Vertex n) :
    (dfsRun σ (2 * n) (initState root)).visited = Finset.univ ↔ M.Connected := by
  constructor
  · intro hall
    exact connected_of_all_marked
      (DFSInv.run (G := M.toDigraph) (r := root) hσ (2 * n) (initState root)
        (DFSInv.init root))
      (DFSInv.run_halts hσ root) hall
  · intro hc
    apply Finset.eq_univ_of_forall
    intro v
    exact (mem_visited_iff_reach
      (G := M.toDigraph) (r := root)
      (DFSInv.run (G := M.toDigraph) (r := root) hσ (2 * n) (initState root)
        (DFSInv.init root))
      (DFSInv.run_halts hσ root) v).mpr (hc root v)

end Qatlib.Papers.GraphConnect03.MainResults.UpperBounds
