/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TrotterSuzuki15.MainResults.SourceMainTheorem
public import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic

/-!
# Compiling an actual Suzuki word into reflection-oracle calls

The two normalized Hamiltonian terms are `UPU` and `-P+η(1-P)`, with normalized
time `τ=Lt` and penalty `η=δ/L`. The syntax below permits only a call to `U`,
an oracle-independent exponential of `P`, and an oracle-independent exponential
of the second term. A conjugated factor is compiled to exactly two calls to
`U`. The numerical generators are the genuine recursive Suzuki generators;
therefore their proved product-formula error applies to the compiled execution.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Papers.TrotterSuzuki15.MainResults.SourceMainTheorem

namespace Qatlib.Papers.SpectralGap11.MainResults.SimulationWord

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The fixed skew generator of the free ancilla phase gate. -/
def phaseGenerator (P : Matrix I I ℂ) : Matrix I I ℂ := (-Complex.I) • P

/-- The first generator uses the oracle solely by conjugation. -/
def firstGenerator (U P : Matrix I I ℂ) : Matrix I I ℂ := U * phaseGenerator P * U

/-- The second normalized term depends only on the ancilla projector and penalty. -/
def secondGenerator (P : Matrix I I ℂ) (η : ℝ) : Matrix I I ℂ :=
  phaseGenerator (-P + (η : ℂ) • (1 - P))

/-- The actual two-generator Hamiltonian splitting. -/
def generators (U P : Matrix I I ℂ) (η : ℝ) : List (Matrix I I ℂ) :=
  [firstGenerator U P, secondGenerator P η]

/-- Instructions allow only the actual oracle and two specified free gates. -/
inductive Instruction where
  | call
  | phase (s : ℝ)
  | remainder (s : ℝ)

/-- The query count is computed from the instruction list itself. -/
def queryCount : List Instruction → ℕ
  | [] => 0
  | Instruction.call :: rest => 1 + queryCount rest
  | Instruction.phase _ :: rest => queryCount rest
  | Instruction.remainder _ :: rest => queryCount rest

/-- Concatenating programs adds their actual oracle counts. -/
theorem query_append (xs ys : List Instruction) :
    queryCount (xs ++ ys) = queryCount xs + queryCount ys := by
  induction xs with
  | nil => simp [queryCount]
  | cons x xs ih => cases x <;> simp [queryCount, ih, Nat.add_assoc]

/-- Matrix semantics of the restricted instruction set. -/
def gate (U P : Matrix I I ℂ) (η : ℝ) : Instruction → Matrix I I ℂ
  | .call => U
  | .phase s => NormedSpace.exp (s • phaseGenerator P)
  | .remainder s => NormedSpace.exp (s • secondGenerator P η)

/-- Execute the program by multiplying its interpreted instructions in order. -/
def execute (U P : Matrix I I ℂ) (η : ℝ) (program : List Instruction) : Matrix I I ℂ :=
  (program.map (gate U P η)).prod

/-- Program concatenation has the corresponding matrix-product semantics. -/
theorem execute_append (U P : Matrix I I ℂ) (η : ℝ) (xs ys : List Instruction) :
    execute U P η (xs ++ ys) = execute U P η xs * execute U P η ys := by
  simp [execute, List.map_append, List.prod_append]

/-- A generator tag and its signed real Suzuki coefficient. -/
structure Factor where
  first : Bool
  coeff : ℝ

/-- Time scaling changes only the coefficient, never the generator tag. -/
def scale (s : ℝ) (f : Factor) : Factor := ⟨f.first, s * f.coeff⟩

/-- Interpret a tagged factor as its actual scaled matrix generator. -/
def interpret (U P : Matrix I I ℂ) (η : ℝ) (f : Factor) : Matrix I I ℂ :=
  f.coeff • (if f.first then firstGenerator U P else secondGenerator P η)

/-- Scaling the syntax scales the interpreted matrix generator. -/
theorem interpret_scale (U P : Matrix I I ℂ) (η s : ℝ) (f : Factor) :
    interpret U P η (scale s f) = s • interpret U P η f := by
  cases f with
  | mk tag c => cases tag <;> simp [interpret, scale, smul_smul]

/-- The symmetric two-term base formula and its genuine five-block recursion. -/
def factors : ℕ → List Factor
  | 0 => [⟨true, 1 / 2⟩, ⟨false, 1 / 2⟩, ⟨false, 1 / 2⟩, ⟨true, 1 / 2⟩]
  | k + 1 =>
    let xs := factors k
    let u := recursiveSuzukiScale k
    let a := xs.map (scale u)
    let b := xs.map (scale (1 - 4 * u))
    a ++ a ++ b ++ a ++ a

/-- Mapping a scaled factor list commutes with interpreting its generators. -/
theorem interpret_map_scale (U P : Matrix I I ℂ) (η s : ℝ) (xs : List Factor) :
    (xs.map (scale s)).map (interpret U P η) =
      (xs.map (interpret U P η)).map (fun X => s • X) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro f _hf
  exact interpret_scale U P η s f

/-- The tagged recursion is exactly the proved matrix Suzuki recursion. -/
theorem factors_interpret (U P : Matrix I I ℂ) (η : ℝ) (k : ℕ) :
    (factors k).map (interpret U P η) = recursiveSuzukiGenerators (generators U P η) k := by
  induction k with
  | zero => simp [factors, interpret, recursiveSuzukiGenerators, generators]
  | succ k ih =>
    simp only [factors, recursiveSuzukiGenerators, List.map_append,
      interpret_map_scale, ih]

/-- Compile a first-term exponential through two real oracle calls; compile
the second term through its specified oracle-independent gate. -/
def compileFactor (f : Factor) : List Instruction :=
  if f.first then [.call, .phase f.coeff, .call] else [.remainder f.coeff]

/-- Compile a factor list by concatenating its concrete instruction blocks. -/
def compile (xs : List Factor) : List Instruction := xs.flatMap compileFactor

/-- Compilation preserves concatenation of factor lists. -/
theorem compile_append (xs ys : List Factor) :
    compile (xs ++ ys) = compile xs ++ compile ys := by
  simp [compile, List.flatMap_append]

/-- Each first-term factor uses two calls and each second-term factor uses none. -/
theorem query_factor (f : Factor) :
    queryCount (compileFactor f) = if f.first then 2 else 0 := by
  cases f with
  | mk tag c => cases tag <;> simp [compileFactor, queryCount]

/-- Real time scaling does not alter the syntactically determined query count. -/
theorem query_scale (s : ℝ) (xs : List Factor) :
    queryCount (compile (xs.map (scale s))) = queryCount (compile xs) := by
  induction xs with
  | nil => rfl
  | cons f xs ih =>
    simp only [List.map_cons, compile, List.flatMap_cons, query_append,
      query_factor, scale]
    exact congrArg (fun n => (if f.first then 2 else 0) + n) ih

/-- The actual recursion has exactly `4*5^k` reflection-oracle calls per segment. -/
theorem query_factors (k : ℕ) : queryCount (compile (factors k)) = 4 * 5 ^ k := by
  induction k with
  | zero => norm_num [factors, compile, compileFactor, queryCount]
  | succ k ih =>
    simp only [factors, compile_append, query_append, query_scale, ih, pow_succ]
    omega

/-- The source conjugation identity holds for any involutory oracle. -/
theorem conjugate_exp (U X : Matrix I I ℂ) (hU : U * U = 1) :
    NormedSpace.exp (U * X * U) = U * NormedSpace.exp X * U := by
  let unitU : (Matrix I I ℂ)ˣ := ⟨U, U, hU, hU⟩
  exact Matrix.exp_units_conj unitU X

/-- Each compiled factor is exactly its intended matrix exponential. -/
theorem factor_execute (U P : Matrix I I ℂ) (η : ℝ) (hU : U * U = 1) (f : Factor) :
    execute U P η (compileFactor f) = NormedSpace.exp (interpret U P η f) := by
  cases f with
  | mk tag c =>
    cases tag
    · simp [compileFactor, execute, gate, interpret]
    · simp only [compileFactor, ite_true, execute, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one, gate, interpret]
      rw [firstGenerator, ← Matrix.mul_assoc, ← conjugate_exp U (c • phaseGenerator P) hU]
      congr 1
      simp

/-- Compilation of a whole factor list is exactly the product of its exponentials. -/
theorem compile_execute (U P : Matrix I I ℂ) (η : ℝ) (hU : U * U = 1)
    (xs : List Factor) :
    execute U P η (compile xs) = (xs.map (fun f => NormedSpace.exp (interpret U P η f))).prod := by
  induction xs with
  | nil => simp [compile, execute]
  | cons f xs ih =>
    change execute U P η (compileFactor f ++ compile xs) =
      NormedSpace.exp (interpret U P η f) *
        (xs.map (fun g => NormedSpace.exp (interpret U P η g))).prod
    rw [execute_append, factor_execute U P η hU, ih]

/-- The concrete segmented simulation program. -/
def program (k : ℕ) (τ : ℝ) (r : ℕ) : List Instruction :=
  (List.replicate r (compile ((factors k).map (scale (τ / r))))).flatten

/-- Repeating a concrete instruction block multiplies its actual oracle count. -/
theorem query_repeat (r : ℕ) (xs : List Instruction) :
    queryCount (List.replicate r xs).flatten = r * queryCount xs := by
  induction r with
  | zero => simp [queryCount]
  | succ r ih => simp [List.replicate_succ, query_append, ih, Nat.succ_mul, Nat.add_comm]

/-- The total query count is fixed by the compiled recursion and segment count. -/
theorem program_queries (k : ℕ) (τ : ℝ) (r : ℕ) :
    queryCount (program k τ r) = r * (4 * 5 ^ k) := by
  rw [program, query_repeat, query_scale, query_factors]

/-- Repeating an actual program block gives a power of its computed matrix. -/
theorem execute_repeat (U P : Matrix I I ℂ) (η : ℝ) (r : ℕ) (xs : List Instruction) :
    execute U P η (List.replicate r xs).flatten = execute U P η xs ^ r := by
  induction r with
  | zero => simp [execute]
  | succ r ih =>
    simp only [List.replicate_succ, List.flatten_cons, execute_append, ih, pow_succ']

/-- The restricted oracle program realizes exactly the library's actual Suzuki product. -/
theorem program_execute (U P : Matrix I I ℂ) (η : ℝ) (hU : U * U = 1)
    (k : ℕ) (τ : ℝ) (r : ℕ) :
    execute U P η (program k τ r) =
      (recursiveSuzukiWord (generators U P η) k τ r).prod := by
  rw [program, execute_repeat, compile_execute U P η hU]
  have hmap : (((factors k).map (scale (τ / r))).map
      (fun f => NormedSpace.exp (interpret U P η f))) =
      (recursiveSuzukiGenerators (generators U P η) k).map
        (fun X => NormedSpace.exp ((τ / r) • X)) := by
    rw [← factors_interpret U P η k, List.map_map, List.map_map]
    apply List.map_congr_left
    intro f _hf
    simpa only [Function.comp_apply] using
      congrArg NormedSpace.exp (interpret_scale U P η (τ / r) f)
  rw [hmap]
  exact (Qatlib.Concepts.TrotterFormula.GeneralOrder.pf_segment_word_prod
    (recursiveSuzukiGenerators (generators U P η) k) τ r).symm

omit [Fintype I] [DecidableEq I] in
/-- Multiplying a Hermitian matrix by `-i` gives an anti-Hermitian generator. -/
theorem phase_skew (P : Matrix I I ℂ) (hP : Pᴴ = P) :
    (phaseGenerator P)ᴴ = -phaseGenerator P := by
  simp [phaseGenerator, Matrix.conjTranspose_smul, hP]

omit [DecidableEq I] in
/-- Conjugation by a Hermitian reflection preserves anti-Hermiticity. -/
theorem first_skew (U P : Matrix I I ℂ) (hU : Uᴴ = U) (hP : Pᴴ = P) :
    (firstGenerator U P)ᴴ = -firstGenerator U P := by
  simp only [firstGenerator, Matrix.conjTranspose_mul, hU, phase_skew P hP,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

omit [Fintype I] in
/-- The real normalized penalty gives a Hermitian second Hamiltonian term. -/
theorem second_skew (P : Matrix I I ℂ) (η : ℝ) (hP : Pᴴ = P) :
    (secondGenerator P η)ᴴ = -secondGenerator P η := by
  apply phase_skew
  simp [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP]

/-- The actual splitting satisfies the skew-Hermitian hypothesis of the
proved Suzuki product formula. -/
theorem generators_skew (U P : Matrix I I ℂ) (η : ℝ)
    (hU : Uᴴ = U) (hP : Pᴴ = P) :
    ∀ X ∈ generators U P η, Xᴴ = -X := by
  intro X hX
  simp only [generators, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl
  · exact first_skew U P hU hP
  · exact second_skew P η hP

/-- The segment count is chosen by the library's genuine high-order error bound. -/
def segments (U P : Matrix I I ℂ) (η : ℝ) (k : ℕ) (τ ε : ℝ) : ℕ :=
  sourceRecursiveSegments (generators U P η) k τ ε

/-- The selected segment count is always positive, including at zero time. -/
theorem segments_pos (U P : Matrix I I ℂ) (η : ℝ) (k : ℕ) (τ ε : ℝ) :
    0 < segments U P η k τ ε := by
  unfold segments sourceRecursiveSegments
  omega

/-- The compiled restricted program inherits the actual Suzuki error estimate;
its target exponential and query count are both computed, not supplied fields. -/
theorem simulation_error (U P : Matrix I I ℂ) (η : ℝ)
    (hUU : U * U = 1) (hU : Uᴴ = U) (hP : Pᴴ = P)
    (k : ℕ) (τ ε : ℝ) (hε : 0 < ε) :
    ‖execute U P η (program k τ (segments U P η k τ ε)) -
      NormedSpace.exp (τ • (generators U P η).sum)‖ ≤ ε := by
  rw [program_execute U P η hUU]
  exact sourceSegments_error (generators U P η) k τ ε
    (generators_skew U P η hU hP) hε

/-- The same compiled program is unitary, as a consequence of its exact
equality with the actual recursive Suzuki product. -/
theorem simulation_unitary (U P : Matrix I I ℂ) (η : ℝ)
    (hUU : U * U = 1) (hU : Uᴴ = U) (hP : Pᴴ = P)
    (k : ℕ) (τ ε : ℝ) :
    execute U P η (program k τ (segments U P η k τ ε)) ∈ Matrix.unitaryGroup I ℂ := by
  rw [program_execute U P η hUU]
  exact (recursive_suzuki_actual_simulation_and_cost I (generators U P η) k
    (segments U P η k τ ε) τ (generators_skew U P η hU hP)
    (segments_pos U P η k τ ε)).1


end Qatlib.Papers.SpectralGap11.MainResults.SimulationWord
