/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# Frequency moments: shared model of the paper's objects

Paper: Ashley Montanaro, *The quantum complexity of approximating the frequency
moments* (arXiv:1505.00113v3, 4 Aug 2016).  The statements below are quoted from
that fixed version; page numbers refer to the printed arXiv v3 page numbers.

This module fixes the objects shared by all the paper-level claims:

* `Stream n m` — a stream `a_1, …, a_n` with `a_i ∈ [m]`.  The alphabet `[m]` is
  represented by `ZMod m` (a finite set of size `m` for `m ≥ 1`); the map
  `{1,…,m} → ZMod m` is a bijection, so all counting statements are unchanged.
* `freq` (`n_j`), `Fk` (`F_k = ∑_j n_j^k`), `F0` (number of distinct values),
  `Finf` (`F_∞ = max_j n_j`) — printed §1, p. 1.
* `RelErr` — the relative-error predicate `|F̃_k − F_k| ≤ ε F_k` (§1, p. 1).
* `QueryProgram` — the paper's quantum query model (§2, p. 5): an oracle circuit on a
  query/value register with arbitrary fixed workspace and output register, one unitary
  oracle `|i,x⟩ ↦ |i, x + a_i⟩` per stream, and a classical decoding of the measured
  basis state.  The oracle is an honest permutation matrix (unitarty, `streamOracle_unitary`).
* `PassProgram` — the multi-pass quantum streaming model (§3, p. 11): `S` stored qubits,
  a unitary update per arriving value, `T` passes, a decoding of the final state.
* `approxSuccess`, `relSuccess` — the actual Born probability that the decoded output is
  within the stated error, so that resource statements are not vacuous.

The query model's oracle is the standard unitary value oracle; the fixed-workspace and
fixed-basis boundary of this model is recorded in the individual claim modules.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FreqMoments15.MainResults

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

/-! ## Streams and frequency moments -/

/-- A stream of `n` elements over the universe `[m]` (represented by `ZMod m`). -/
abbrev Stream (n m : ℕ) := Fin n → ZMod m

variable {n m : ℕ} [NeZero m]

/-- The multiplicity `n_j` of the value `j` in the stream. -/
noncomputable def freq (a : Stream n m) (j : ZMod m) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => a i = j)).card

/-- The `k`-th frequency moment `F_k = ∑_j n_j^k` (printed p. 1). -/
noncomputable def Fk (a : Stream n m) (k : ℕ) : ℕ := ∑ j, freq a j ^ k

/-- `F_0`, the number of distinct values occurring in the stream (printed p. 1). -/
noncomputable def F0 (a : Stream n m) : ℕ :=
  (Finset.univ.filter (fun j : ZMod m => 0 < freq a j)).card

/-- `F_∞ = max_j n_j` (printed p. 1). -/
noncomputable def Finf (a : Stream n m) : ℕ := Finset.univ.sup (freq a)

/-- Relative-error predicate `|est − actual| ≤ ε · actual`. -/
abbrev RelErr (est actual ε : ℝ) : Prop := |est - actual| ≤ ε * actual

/-- `F_1 = n`: the first frequency moment is the stream length. -/
theorem Fk_one (a : Stream n m) : Fk a 1 = n := by
  unfold Fk freq
  simp only [pow_one]
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (ZMod m)))
    (f := a) (fun i _ => Finset.mem_univ (a i))
  simpa using h.symm

/-- Every frequency is at most `n`. -/
theorem freq_le (a : Stream n m) (j : ZMod m) : freq a j ≤ n := by
  unfold freq
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => a i = j)

/-- `F_∞ ≤ n`. -/
theorem Finf_le (a : Stream n m) : Finf a ≤ n := by
  unfold Finf
  exact (Finset.sup_le_iff.mpr (fun j _ => freq_le a j))

/-! ## The query model (§2, p. 5) -/

/-- The value oracle permutation `|i, x⟩ ↦ |i, x + a_i⟩` on the query/value register,
together with the untouched workspace and output registers. -/
def oraclePerm {n m r out : ℕ} (a : Stream n m) :
    Equiv.Perm ((Fin n × ZMod m) × Fin r × Fin out) where
  toFun p := ((p.1.1, p.1.2 + a p.1.1), p.2)
  invFun p := ((p.1.1, p.1.2 - a p.1.1), p.2)
  left_inv p := by
    simp only [add_sub_cancel_right]
  right_inv p := by
    simp only [sub_add_cancel]

/-- The unitary oracle matrix for the value oracle (a permutation matrix). -/
def streamOracle {n m : ℕ} [NeZero m] (a : Stream n m) (r out : ℕ) :
    Matrix ((Fin n × ZMod m) × Fin r × Fin out) ((Fin n × ZMod m) × Fin r × Fin out) ℂ :=
  (oraclePerm (r := r) (out := out) a).permMatrix ℂ

/-- The stream oracle is unitary: it is a permutation matrix. -/
theorem streamOracle_unitary {n m : ℕ} [NeZero m] (a : Stream n m) (r out : ℕ) :
    streamOracle a r out ∈ Matrix.unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  show (oraclePerm (r := r) (out := out) a).permMatrix ℂ *
      star ((oraclePerm (r := r) (out := out) a).permMatrix ℂ) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul]
  simp

/-- A fixed-workspace unitary query program for a stream problem.  `circuit` runs against
`streamOracle a`; `decode` is the algorithm's classical readout of the measured basis
state.  The initial state and every fixed gate are unitary objects of the quantum model. -/
structure QueryProgram (n m out : ℕ) [NeZero m] where
  /-- number of workspace qubits -/
  r : ℕ
  /-- the oracle circuit, acting on query/value, workspace and output registers -/
  circuit : Circuit ((Fin n × ZMod m) × Fin r × Fin out)
  /-- the fixed start state -/
  initial : QState ((Fin n × ZMod m) × Fin r × Fin out)
  /-- classical decoding of the measured basis state into a real estimate -/
  decode : ((Fin n × ZMod m) × Fin r × Fin out) → ℝ
  /-- every fixed gate is unitary -/
  circuit_unitary : IsUnitaryCircuit circuit
  /-- the start state is normalized -/
  initial_normalized : Normalized initial

/-- The final state of a query program on the stream `a`. -/
def QueryProgram.run {n m out : ℕ} [NeZero m] (P : QueryProgram n m out) (a : Stream n m) :
    QState ((Fin n × ZMod m) × Fin P.r × Fin out) :=
  Run (streamOracle a P.r out) P.circuit P.initial

/-- The probability that the decoded output is within relative error `ε` of `target`. -/
def QueryProgram.relSuccess {n m out : ℕ} [NeZero m] (P : QueryProgram n m out) (a : Stream n m)
    (target ε : ℝ) : ℝ :=
  MeasureProb (P.run a)
    (Finset.univ.filter (fun p => RelErr (P.decode p) target ε))

/-- Success of the `F_0` estimate at relative error `ε`. -/
def QueryProgram.successF0 {n m out : ℕ} [NeZero m] (P : QueryProgram n m out) (a : Stream n m)
    (ε : ℝ) : ℝ :=
  P.relSuccess a (F0 a : ℝ) ε

/-- Success of the `F_k` estimate at relative error `ε`. -/
def QueryProgram.successFk {n m out : ℕ} [NeZero m] (P : QueryProgram n m out) (a : Stream n m)
    (k : ℕ) (ε : ℝ) : ℝ :=
  P.relSuccess a (Fk a k : ℝ) ε

/-- Success of the `F_∞` estimate at relative error `ε`. -/
def QueryProgram.successFinf {n m out : ℕ} [NeZero m] (P : QueryProgram n m out) (a : Stream n m)
    (ε : ℝ) : ℝ :=
  P.relSuccess a (Finf a : ℝ) ε

/-! ## The multi-pass quantum streaming model (§3, p. 11) -/

/-- One pass over the stream: apply the value-dependent update `step` to every element. -/
def onePass {n m S : ℕ} (step : ZMod m → Matrix (Reg S) (Reg S) ℂ)
    (ψ : QState (Reg S)) (a : Stream n m) : QState (Reg S) :=
  (List.ofFn a).foldl (fun ψ v => ApplyGate (step v) ψ) ψ

/-- A multi-pass quantum streaming program: `S` stored qubits, a unitary update per
arriving value, `T` passes over the stream, and a classical decoding of the final state. -/
structure PassProgram (n m : ℕ) where
  /-- number of stored qubits `S` -/
  S : ℕ
  /-- number of passes `T` -/
  T : ℕ
  /-- the update applied to every arriving value -/
  step : ZMod m → Matrix (Reg S) (Reg S) ℂ
  /-- the fixed start state -/
  init : QState (Reg S)
  /-- classical decoding of the measured state into a real estimate -/
  decode : Reg S → ℝ
  /-- every update is unitary -/
  step_unitary : ∀ v, step v ∈ Matrix.unitaryGroup (Reg S) ℂ
  /-- the start state is normalized -/
  init_normalized : Normalized init

/-- The final state of a streaming program on the stream `a`. -/
def PassProgram.run {n m : ℕ} (P : PassProgram n m) (a : Stream n m) : QState (Reg P.S) :=
  (List.finRange P.T).foldl (fun ψ _ => onePass P.step ψ a) P.init

/-- Additive-error success probability of a streaming program. -/
def PassProgram.approxSuccess {n m : ℕ} (P : PassProgram n m) (a : Stream n m)
    (target ε : ℝ) : ℝ :=
  MeasureProb (P.run a) (Finset.univ.filter (fun s => |P.decode s - target| ≤ ε))

/-- Relative-error success probability of a streaming program. -/
def PassProgram.relSuccess {n m : ℕ} (P : PassProgram n m) (a : Stream n m)
    (target ε : ℝ) : ℝ :=
  MeasureProb (P.run a) (Finset.univ.filter (fun s => RelErr (P.decode s) target ε))

/-- Success of the `F_0` estimate at relative error `ε` in the streaming model. -/
def PassProgram.successF0 {n m : ℕ} [NeZero m] (P : PassProgram n m) (a : Stream n m)
    (ε : ℝ) : ℝ :=
  P.relSuccess a (F0 a : ℝ) ε

/-- Success of the `F_2` estimate at relative error `ε` in the streaming model. -/
def PassProgram.successF2 {n m : ℕ} [NeZero m] (P : PassProgram n m) (a : Stream n m)
    (ε : ℝ) : ℝ :=
  P.relSuccess a (Fk a 2 : ℝ) ε

/-- Success of the `F_k` estimate at relative error `ε` in the streaming model. -/
def PassProgram.successFk {n m : ℕ} [NeZero m] (P : PassProgram n m) (a : Stream n m)
    (k : ℕ) (ε : ℝ) : ℝ :=
  P.relSuccess a (Fk a k : ℝ) ε

/-- Exact computation of `F_k` by a streaming program: the decoded value equals `F_k` on
every measurement outcome. -/
def PassProgram.exactFk {n m : ℕ} [NeZero m] (P : PassProgram n m) (a : Stream n m) (k : ℕ) : Prop :=
  ∀ s : Reg P.S, P.decode s = (Fk a k : ℝ)

/-- Exact computation of `F_∞` by a streaming program. -/
def PassProgram.exactFinf {n m : ℕ} [NeZero m] (P : PassProgram n m) (a : Stream n m) : Prop :=
  ∀ s : Reg P.S, P.decode s = (Finf a : ℝ)

end Qatlib.Papers.FreqMoments15.MainResults
