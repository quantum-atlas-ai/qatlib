/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ExactSimon97.OracleMachine
public import Qatlib.Papers.ExactSimon97.MainResults.Cor10Assembly
public import Qatlib.Papers.ExactSimon97.MainResults.Defs
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

/-!
# Constructive bounded-depth enumeration of ExactSimon97 oracle machines

For the classical procedure model in [BrassardHoyer1997], Theorem 9: the constructive machine enumeration that is to
feed `Cor10Assembly` with a real `procs`/`covers` source, plus the
execution-derived per-execution query cost as a first instance toward
`ClProc`/the supplied admissibility predicate.

Over the finite instruction-machine interface (`Instr`, `Prog`, `Conf`, `step`, `exec`), the
instruction alphabet is an explicit finite code list (`instrList`, with
`mem_instrList`), so for every depth `d` the programs of length at most `d` form
a finite code list (`progsOfLen`, `boundedProgs`) with a size bound
(`progsOfLen_length_le`, `boundedProgs_length_le`) and finite carrier set
(`bounded_set_finite`). The code list is read as a sequence (`enumProg`) past
whose end a dead default is returned: the empty program, halted at every program
counter, so surplus indices are inert (`enumProg_dead`, `enumProg_dead_inert`).
The covers relation `covered` — which machines the enumeration covers — holds
exactly for the programs of depth at most `d` (`covered_iff_bounded`), the
machine-level statement behind `Cor10Assembly`'s `covers` hypothesis, and every
uniformly depth-bounded machine family decomposes through the per-scale
enumeration (`bounded_family_covered`).

The per-execution query cost `qcount` counts oracle consultations along the
fuel-indexed run: it is bounded by the fuel (`qcount_le`), additive over fuel
splits exactly as `exec` is (`qcount_add`), zero on halting configurations
(`qcount_halted`), and — because this instruction set does not branch — it
depends only on the program counter trace, so in particular it is independent
of the consulted oracle (`step_pc`, `qcount_pc_indep`,
`qcount_oracle_indep`); it equals one on the single-query program
(`qcount_oneQueryProg`). Loading a `ClInput` address vector into the standard
register (`initConf`) lifts a scale-uniform machine family to a cost profile
`machineQueries` whose cube bound (`machineQueries_cube`) matches the budget
premise of `Qatlib.Papers.ExactSimon97.MainResults.ScaleQual.defeat`; `MachineCostValid` records that a raw `ClProc`'s
cost component is execution-derived from a bounded family, and
`machineCostValid_cube_budget` derives that budget premise for such profiles.

Honest non-coverage: no success event is defined and `Qatlib.Papers.ExactSimon97.MainResults.ClProc.success` is
constrained nowhere (`MachineCostValid` governs only the cost component); there
is no probability, no Theorem 9 transcript estimate, no diagonalizing
constructor, and no `QP^O` membership. Per DESIGN §12.8 nothing here is the
original Corollary 10, and the work block is fixed to width zero because
`ClInput` determines only the address width (the scale `n`).

## Main statements

* `covered_iff_bounded`: the depth-`d` enumeration covers exactly the programs
  of depth at most `d` — the constructive `procs`/`covers` source.
* `boundedProgs_length_le` / `bounded_set_finite`: finiteness of the bounded
  program space, with an explicit code-list size bound.
* `enumProg_dead_inert`: indices past the code list decode to the everywhere
  halted dead program — dead code neither moves nor queries.
* `qcount_add` / `qcount_le` / `qcount_oracle_indep`: the per-execution query
  count is a fuel-additive cost bounded by the fuel, independent of the oracle.
* `machineCostValid_cube_budget`: execution-derived profiles satisfy the cube
  budget premise of `Qatlib.Papers.ExactSimon97.MainResults.ScaleQual.defeat`.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CircuitLang.XorOracle
open Qatlib.Papers.ExactSimon97.OracleMachine
open Qatlib.Papers.ExactSimon97.MainResults
open Qatlib.Papers.ExactSimon97.MainResults (BoolVec)

namespace Qatlib.Papers.ExactSimon97.MachineEnum

variable {a w : ℕ}

/-! ## The instruction alphabet as explicit finite code -/

/-- The instruction alphabet as an explicit finite code list: the two nullary
instructions plus one address flip and one work flip per index. -/
def instrList (a w : ℕ) : List (Instr a w) :=
  [Instr.oracle, Instr.halt] ++ (List.finRange a).map Instr.flipA ++
    (List.finRange w).map Instr.flipW

/-- The alphabet is exhaustive: every instruction occurs in the code list. -/
theorem mem_instrList (a w : ℕ) (i : Instr a w) : i ∈ instrList a w := by
  cases i with
  | oracle => simp [instrList]
  | flipA i => simp [instrList, List.mem_map, List.mem_finRange]
  | flipW i => simp [instrList, List.mem_map, List.mem_finRange]
  | halt => simp [instrList]

/-- The alphabet is nonempty: it has at least the two nullary instructions. -/
theorem two_le_length_instrList (a w : ℕ) : 2 ≤ (instrList a w).length := by
  simp [instrList]

/-! ## The bounded program space as a finite code list -/

/-- All programs of exact length `n`, as finite data: one cons layer over the
alphabet per length step. -/
def progsOfLen (a w : ℕ) : ℕ → List (Prog a w)
  | 0 => [[]]
  | n + 1 =>
      (instrList a w).flatMap fun t =>
        (progsOfLen a w n).map (t :: ·)

/-- Membership in `progsOfLen` is exactly length agreement. -/
theorem mem_progsOfLen (a w : ℕ) (n : ℕ) (P : Prog a w) :
    P ∈ progsOfLen a w n ↔ P.length = n := by
  induction n generalizing P with
  | zero =>
      cases P with
      | nil => simp [progsOfLen]
      | cons t Q =>
          constructor
          · intro h
            exact absurd h (by simp [progsOfLen])
          · intro h
            simp only [List.length_cons] at h
            omega
  | succ n ih =>
      constructor
      · intro hmem
        simp only [progsOfLen, List.mem_flatMap, List.mem_map] at hmem
        obtain ⟨t, _ht, Q, hQ, rfl⟩ := hmem
        rw [List.length_cons, (ih Q).1 hQ]
      · intro hlen
        obtain ⟨t, Q, rfl⟩ :
            ∃ (t : Instr a w) (Q : Prog a w), P = t :: Q := by
          cases P with
          | nil => exact absurd hlen (by simp)
          | cons t Q => exact ⟨t, Q, rfl⟩
        refine List.mem_flatMap.2 ⟨t, mem_instrList a w t,
          List.mem_map.2 ⟨Q, (ih Q).2 ?_, rfl⟩⟩
        simp only [List.length_cons] at hlen
        omega

/-- Pointwise bound on flatMap lengths: if every image list has at most `m`
entries, the flatMap has at most `L.length * m` entries. -/
theorem length_flatMap_le {α β : Type} (m : ℕ) :
    ∀ (L : List α) (f : α → List β), (∀ x ∈ L, (f x).length ≤ m) →
      (L.flatMap f).length ≤ L.length * m := by
  intro L
  induction L with
  | nil => intro f _; simp
  | cons y L ih =>
      intro f h
      have hy : (f y).length ≤ m := h y (by simp)
      have hL := ih f fun x hx => h x (by simp [hx])
      show (f y ++ L.flatMap f).length ≤ (y :: L).length * m
      rw [List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- The programs of exact length `n` number at most the alphabet size to the
`n`. -/
theorem progsOfLen_length_le (a w n : ℕ) :
    (progsOfLen a w n).length ≤ (instrList a w).length ^ n := by
  induction n with
  | zero => simp [progsOfLen]
  | succ n ih =>
      have h1 : (progsOfLen a w (n + 1)).length ≤
          (instrList a w).length * (progsOfLen a w n).length :=
        length_flatMap_le (progsOfLen a w n).length (instrList a w)
          (fun t => (progsOfLen a w n).map (t :: ·))
          (fun t _ => Nat.le_of_eq (List.length_map _))
      have h2 : (instrList a w).length * (instrList a w).length ^ n =
          (instrList a w).length ^ (n + 1) := by
        rw [Nat.mul_comm, Nat.pow_succ]
      exact h1.trans ((Nat.mul_le_mul_left _ ih).trans (Nat.le_of_eq h2))

/-- The bounded program space of depth `d`: the finite code list of all
programs of length at most `d`. -/
def boundedProgs (a w d : ℕ) : List (Prog a w) :=
  (List.range (d + 1)).flatMap (progsOfLen a w)

/-- Membership in `boundedProgs` is exactly the depth bound. -/
theorem mem_boundedProgs (a w d : ℕ) (P : Prog a w) :
    P ∈ boundedProgs a w d ↔ P.length ≤ d := by
  simp only [boundedProgs, List.mem_flatMap, List.mem_range, mem_progsOfLen]
  constructor
  · rintro ⟨n, hn, hP⟩
    omega
  · intro h
    exact ⟨P.length, by omega, rfl⟩

/-- Finiteness of the bounded program space with an explicit size bound: the
depth-`d` code list has at most `(d + 1) * c ^ d` entries, where `c` is the
alphabet size. -/
theorem boundedProgs_length_le (a w d : ℕ) :
    (boundedProgs a w d).length ≤ (d + 1) * (instrList a w).length ^ d := by
  have hcpos : 0 < (instrList a w).length := by
    have := two_le_length_instrList a w
    omega
  have h1 : (boundedProgs a w d).length ≤
      (List.range (d + 1)).length * ((instrList a w).length ^ d) :=
    length_flatMap_le ((instrList a w).length ^ d) (List.range (d + 1))
      (progsOfLen a w)
      (fun n hn => (progsOfLen_length_le a w n).trans
        (Nat.pow_le_pow_right hcpos (by
          have := List.mem_range.1 hn
          omega)))
  rw [List.length_range] at h1
  exact h1

/-- The bounded program space is finite as a set. -/
theorem bounded_set_finite (a w d : ℕ) :
    {P : Prog a w | P.length ≤ d}.Finite := by
  refine Set.Finite.ofFinset (boundedProgs a w d).toFinset fun P => ?_
  rw [List.mem_toFinset]
  exact mem_boundedProgs a w d P

/-! ## The enumeration sequence and the covers relation -/

/-- Every element of a list is read back at some index by `getD`. -/
theorem exists_getD_eq_of_mem {α : Type} (dflt : α) :
    ∀ (l : List α) (x : α), x ∈ l → ∃ i : ℕ, l.getD i dflt = x := by
  intro l
  induction l with
  | nil => intro x hx; cases hx
  | cons _y l ih =>
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact ⟨0, rfl⟩
      · obtain ⟨i, hi⟩ := ih x hx'
        exact ⟨i + 1, hi⟩

/-- `getD` reads either the default or an element of the list. -/
theorem getD_mem_or_default {α : Type} (dflt : α) (l : List α) (i : ℕ) :
    l.getD i dflt = dflt ∨ l.getD i dflt ∈ l := by
  induction l generalizing i with
  | nil => exact Or.inl rfl
  | cons y l ih =>
      cases i with
      | zero => exact Or.inr List.mem_cons_self
      | succ i =>
          rcases ih i with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

/-- The i-th program of the depth-`d` enumeration: decode index `i` against the
finite code list, reading the dead default `[]` past its end. -/
def enumProg (a w d i : ℕ) : Prog a w :=
  (boundedProgs a w d).getD i []

/-- Soundness of the enumeration: every program it returns is depth-bounded. -/
theorem enumProg_le (a w d i : ℕ) : (enumProg a w d i).length ≤ d := by
  have h := getD_mem_or_default ([] : Prog a w) (boundedProgs a w d) i
  rcases h with h | h
  · unfold enumProg
    rw [h]
    exact Nat.zero_le d
  · exact (mem_boundedProgs a w d (enumProg a w d i)).1 h

/-- The covers relation: the depth-`d` enumeration covers machine `P` when some
index of the finite code list decodes to `P`. -/
def covered (a w d : ℕ) (P : Prog a w) : Prop :=
  ∃ i : ℕ, enumProg a w d i = P

/-- Completeness and soundness of the covers relation: the depth-`d`
enumeration covers exactly the programs of depth at most `d`. This is the
constructive machine-level source behind `Cor10Assembly`'s `covers`
hypothesis. -/
theorem covered_iff_bounded (a w d : ℕ) (P : Prog a w) :
    covered a w d P ↔ P.length ≤ d := by
  constructor
  · rintro ⟨i, rfl⟩
    exact enumProg_le a w d i
  · intro hlen
    obtain ⟨i, hi⟩ := exists_getD_eq_of_mem ([] : Prog a w)
      (boundedProgs a w d) P ((mem_boundedProgs a w d P).2 hlen)
    exact ⟨i, hi⟩

/-- Existence in the enumeration: the single-query program is covered at
every depth at least two. -/
theorem covered_oneQueryProg (a w d : ℕ) (hd : 2 ≤ d) :
    covered a w d (oneQueryProg : Prog a w) :=
  (covered_iff_bounded a w d _).2 (by simpa [oneQueryProg] using hd)

/-- Dead-code bound: indices past the finite code list decode to the dead
default, the empty program. -/
theorem enumProg_dead (a w d i : ℕ) (hcard : (boundedProgs a w d).length ≤ i) :
    enumProg a w d i = [] :=
  List.getD_eq_default (boundedProgs a w d) ([] : Prog a w) hcard

/-! ## Per-execution query cost -/

/-- Per-execution query count: the number of `oracle` instructions consumed by
the fuel-indexed run. One oracle step contributes one consultation, exactly as
`step` consults the oracle once through `xorInto`. -/
def qcount (f : Addr a → Bool) (P : Prog a w) : ℕ → Conf a w → ℕ
  | 0, _ => 0
  | k + 1, c =>
      (if instrAt P c.pc = Instr.oracle then 1 else 0) + qcount f P k (step f P c)

/-- The query count is bounded by the fuel: a run of `k` steps consults the
oracle at most `k` times. -/
theorem qcount_le (f : Addr a → Bool) (P : Prog a w) (k : ℕ) :
    ∀ c : Conf a w, qcount f P k c ≤ k := by
  induction k with
  | zero => intro c; exact Nat.zero_le _
  | succ k ih =>
      intro c
      have hcnt : (if instrAt P c.pc = Instr.oracle then 1 else 0) ≤ 1 := by
        split <;> omega
      have hrest := ih (step f P c)
      show (if instrAt P c.pc = Instr.oracle then 1 else 0) +
        qcount f P k (step f P c) ≤ k + 1
      omega

/-- The query count is additive over fuel splits, exactly as `exec` is: the
count of a `j + k` step run is the count of the first `j` steps plus the count
of the remaining `k` steps from the reached configuration. -/
theorem qcount_add (f : Addr a → Bool) (P : Prog a w) (j k : ℕ) :
    ∀ c : Conf a w, qcount f P (j + k) c = qcount f P j c + qcount f P k (exec f P j c) := by
  induction j with
  | zero => intro c; simp [qcount, exec]
  | succ j ih =>
      intro c
      have hsplit : j + 1 + k = j + k + 1 := Nat.add_right_comm j 1 k
      have hex : exec f P (j + 1) c = exec f P j (step f P c) := rfl
      rw [hsplit]
      simp only [qcount, hex]
      have h1 := ih (step f P c)
      omega

/-- Halting configurations cost nothing: a halted run consults no oracle. -/
theorem qcount_halted (f : Addr a → Bool) (P : Prog a w) (c : Conf a w)
    (h : halted P c) (k : ℕ) : qcount f P k c = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hh : instrAt P c.pc = Instr.halt := h
      have hif : (if instrAt P c.pc = Instr.oracle then 1 else 0) = 0 := by
        rw [hh]
        simp
      show (if instrAt P c.pc = Instr.oracle then 1 else 0) +
        qcount f P k (step f P c) = 0
      rw [hif, step_halted f P c h]
      omega

/-- The program counter of a step depends only on the instruction read, not on
the oracle or the register data. -/
theorem step_pc (f : Addr a → Bool) (P : Prog a w) (c : Conf a w) :
    (step f P c).pc = if instrAt P c.pc = Instr.halt then c.pc else c.pc + 1 := by
  cases hi : instrAt P c.pc with
  | oracle => rw [step_oracle f P c hi]; simp
  | flipA i => rw [step_flipA f P c hi]; simp
  | flipW i => rw [step_flipW f P c hi]; simp
  | halt => rw [step_halt f P c hi]; simp

/-- The query count depends only on the program counter trace: runs from
configurations with the same program counter, under possibly different oracles,
consult equally often. The instruction set does not branch, so this is the
precise sense in which the per-execution cost is data-independent. -/
theorem qcount_pc_indep (P : Prog a w) (k : ℕ) (f g : Addr a → Bool) :
    ∀ (c c' : Conf a w), c.pc = c'.pc → qcount f P k c = qcount g P k c' := by
  induction k with
  | zero => intro c c' _; rfl
  | succ k ih =>
      intro c c' hpc
      have hpcc : (step f P c).pc = (step g P c').pc := by
        rw [step_pc f P c, step_pc g P c', hpc]
      have hcnt : (if instrAt P c.pc = Instr.oracle then 1 else 0) =
          (if instrAt P c'.pc = Instr.oracle then 1 else 0) := by rw [hpc]
      show (if instrAt P c.pc = Instr.oracle then 1 else 0) +
          qcount f P k (step f P c) =
        (if instrAt P c'.pc = Instr.oracle then 1 else 0) +
          qcount g P k (step g P c')
      rw [hcnt, ih (step f P c) (step g P c') hpcc]

/-- The query count is independent of the consulted oracle. -/
theorem qcount_oracle_indep (P : Prog a w) (k : ℕ) (f g : Addr a → Bool)
    (c : Conf a w) : qcount f P k c = qcount g P k c :=
  qcount_pc_indep P k f g c c rfl

/-- The single-query program really consults once: its two-step run has
query count one. -/
theorem qcount_oneQueryProg (f : Addr a → Bool) (x : OReg a w) :
    qcount f (oneQueryProg : Prog a w) 2 ⟨0, x⟩ = 1 := by
  have h0 : instrAt oneQueryProg 0 = (Instr.oracle : Instr a w) := rfl
  have h1 : instrAt oneQueryProg 1 = (Instr.halt : Instr a w) := rfl
  have hstep : step f oneQueryProg ⟨0, x⟩ = ⟨1, xorInto f x⟩ :=
    step_oracle f oneQueryProg ⟨0, x⟩ h0
  show (if instrAt oneQueryProg 0 = Instr.oracle then 1 else 0) +
    qcount f oneQueryProg 1 (step f oneQueryProg ⟨0, x⟩) = 1
  rw [ite_eq_left h0, hstep]
  show (1 : ℕ) + ((if instrAt oneQueryProg 1 = Instr.oracle then 1 else 0) +
    qcount f oneQueryProg 0 (step f oneQueryProg ⟨1, xorInto f x⟩)) = 1
  rw [ite_eq_right (by rw [h1]; simp)]
  rfl

/-- Dead indices are inert: past the code list the enumeration returns the
empty program, which is halted at every program counter — execution never moves
and the oracle is never consulted. -/
theorem enumProg_dead_inert (a w d i : ℕ) (hcard : (boundedProgs a w d).length ≤ i)
    (f : Addr a → Bool) (k : ℕ) (c : Conf a w) :
    exec f (enumProg a w d i) k c = c ∧ qcount f (enumProg a w d i) k c = 0 := by
  rw [enumProg_dead a w d i hcard]
  have hh : halted ([] : Prog a w) c := rfl
  exact ⟨exec_halted f [] c hh k, qcount_halted f [] c hh k⟩

/-! ## Execution-derived cost semantics toward `ClProc` -/

/-- The initial machine configuration for a classical input: the `BoolVec n`
address vector is loaded into the address block (value `1` read as `true`), the
answer bit starts at `false`, the work block has width zero, and the program
counter starts at zero. -/
def initConf {n : ℕ} (x : BoolVec n) : Conf n 0 :=
  ⟨0, (fun i => decide (x i = 1), false, fun i => Fin.elim0 i)⟩

/-- The execution-derived query cost of a scale-uniform machine family `M`
under uniform fuel budget `k`: on input `x` at scale `n`, run `M n` for `k`
steps from the initial configuration and count oracle consultations. The
consulted oracle is the zero oracle; by `qcount_oracle_indep` the count is
independent of the oracle in this non-branching instruction set, so no oracle
data enters the cost. -/
def machineQueries (M : (n : ℕ) → Prog n 0) (k : ℕ) : ClInput → ℕ
  | ⟨n, x⟩ => qcount (fun _ => false) (M n) k (initConf x)

/-- Uniform fuel bounds the execution-derived cost on every input. -/
theorem machineQueries_le (M : (n : ℕ) → Prog n 0) (k : ℕ) (x : ClInput) :
    machineQueries M k x ≤ k := by
  obtain ⟨n, y⟩ := x
  exact qcount_le (fun _ => false) (M n) k (initConf y)

/-- The cube of the execution-derived cost is bounded by the cube of the fuel
budget. -/
theorem machineQueries_cube (M : (n : ℕ) → Prog n 0) (k : ℕ) (x : ClInput) :
    (machineQueries M k x) ^ 3 ≤ k ^ 3 :=
  Nat.pow_le_pow_left (machineQueries_le M k x) 3

/-- First admissibility instance toward the supplied admissibility predicate: a raw profile is
machine-cost admissible when its query cost is execution-derived from a
uniformly depth-bounded machine family. The success component is deliberately
NOT constrained here — no success semantics is posited in this slice (DESIGN
§12.8). -/
def MachineCostValid (d k : ℕ) (A : ClProc) : Prop :=
  ∃ M : (n : ℕ) → Prog n 0, (∀ n : ℕ, (M n).length ≤ d) ∧ A.queries = machineQueries M k

/-- The cost half of the `Qatlib.Papers.ExactSimon97.MainResults.ScaleQual.defeat` budget premise is execution-derived:
every machine-cost admissible profile satisfies the cube budget at every input
whose scale absorbs `k ^ 3` into `2 ^ scale`. -/
theorem machineCostValid_cube_budget {d k : ℕ} {A : ClProc}
    (hA : MachineCostValid d k A) (x : ClInput) (hk : k ^ 3 ≤ 2 ^ x.1) :
    A.queries x ^ 3 ≤ 2 ^ x.1 := by
  obtain ⟨M, _, hq⟩ := hA
  rw [hq]
  exact (machineQueries_cube M k x).trans hk

/-- The constructive `procs`/`covers` source at the machine level: every
uniformly depth-bounded machine family decomposes through the per-scale bounded
enumeration — for each scale `n`, some index of the depth-`d` code list names
the family's scale-`n` machine. -/
theorem bounded_family_covered (d : ℕ) (M : (n : ℕ) → Prog n 0)
    (hM : ∀ n : ℕ, (M n).length ≤ d) (n : ℕ) :
    ∃ i : ℕ, enumProg n 0 d i = M n :=
  (covered_iff_bounded n 0 d (M n)).2 (hM n)

end Qatlib.Papers.ExactSimon97.MachineEnum
