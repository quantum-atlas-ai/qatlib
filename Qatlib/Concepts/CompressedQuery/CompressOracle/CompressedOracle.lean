/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude

/-!
# Compressed Bernoulli query oracles

This module defines a coherent Bernoulli table, its decompression transform and the conjugated
query operator `compressedOracle`. Theorems relate compressed execution to ordinary phase
queries, establish the reduced state identity, and show that each query changes only the
addressed database bit.

The database support and binomial moment bounds quantify how recorded information grows with the
number of queries. The construction also includes the Hadamard conversion from bit query
circuits to phase query circuits.

The mathematical context is discussed in [NielsenChuang2010].

## Main statements

* `compressed_marginal`: The reduced state equals the Bernoulli average of ordinary oracle
  executions.
* `compressed_oracle_entry`: The exact local query matrix entries with the required locality
  condition.
* `database_support_bound`: Database size is bounded by the number of queries.
* `database_moment_bound`: Binomial database moments are bounded in terms of the query count.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.CompressedQuery.CompressOracle

open Matrix
open scoped ComplexOrder

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The product Bernoulli weight of the Boolean table `x`, with parameter `p` at each address. -/
def bernoulliPmf (p : ℝ) (x : I → Bool) : ℝ := ∏ j, if x j then p else 1 - p

/-- The coherent Boolean table state whose amplitudes are the nonnegative square roots of
`bernoulliPmf p`. -/
def bernoulliState (p : ℝ) : QState (I → Bool) :=
  fun x => Complex.ofReal (Real.sqrt (bernoulliPmf p x))

/-- The one-bit decompression matrix entry, with columns (√(1 − p), √p) and (√p, −√(1 − p)) in
the false/true basis. -/
def decompressEntry (p : ℝ) (b d : Bool) : ℂ :=
  if b then (if d then -Complex.ofReal (Real.sqrt (1 - p)) else Complex.ofReal (Real.sqrt p))
    else (if d then Complex.ofReal (Real.sqrt p) else Complex.ofReal (Real.sqrt (1 - p)))

/-- The product decompression transform on Boolean tables, formed from `decompressEntry` at
every address. -/
def decompressGate (p : ℝ) : Matrix (I → Bool) (I → Bool) ℂ :=
  Matrix.of fun x d => ∏ j, decompressEntry p (x j) (d j)

/-- The one-bit compressed phase query matrix with diagonal entries 1 − 2p and 2p − 1 and
off-diagonal entries 2√(p(1 − p)). -/
def compressedQueryEntry (p : ℝ) (d d' : Bool) : ℂ :=
  if d then
    (if d' then Complex.ofReal (2 * p - 1)
      else Complex.ofReal (2 * Real.sqrt (p * (1 - p))))
  else
    (if d' then Complex.ofReal (2 * Real.sqrt (p * (1 - p)))
      else Complex.ofReal (1 - 2 * p))

/-- The finite set of addresses where the Boolean database is true. -/
def databaseSupport (d : I → Bool) : Finset I := Finset.univ.filter (fun j => d j)

/-- The number of true entries in the Boolean database. -/
def databaseCard (d : I → Bool) : ℕ := (databaseSupport d).card

/-- The phase oracle controlled by the Boolean target register, acting trivially on the
workspace. -/
def workspacePhaseOracle (x : I → Bool) : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ :=
  TensorGate (PhaseOracle fun jb : I × Bool => jb.2 && x jb.1) 1

/-- The diagonal oracle applying a sign when the target bit and the table bit at the query
address are both true. -/
def jointPhaseOracle : Matrix (((I × Bool) × W) × (I → Bool))
    (((I × Bool) × W) × (I → Bool)) ℂ :=
  Matrix.diagonal fun q => if q.1.1.2 && q.2 q.1.1.1 then (-1 : ℂ) else 1

/-- Lift an algorithm step to include a database register by tensoring gates with the identity
and retaining query steps. -/
def tensorLiftStep (s : Step ((I × Bool) × W)) :
    Step (((I × Bool) × W) × (I → Bool)) :=
  match s with
  | Step.gate U => Step.gate (TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ))
  | Step.query => Step.query

/-- Lift each step of a circuit to the joint algorithm and database space. -/
def tensorLiftCircuit (C : Circuit ((I × Bool) × W)) :
    Circuit (((I × Bool) × W) × (I → Bool)) := C.map tensorLiftStep

/-- The joint phase oracle conjugated by decompression on the database register. -/
def compressedOracle (p : ℝ) : Matrix (((I × Bool) × W) × (I → Bool))
    (((I × Bool) × W) × (I → Bool)) ℂ :=
  (TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (decompressGate p)ᴴ) *
    jointPhaseOracle *
    (TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (decompressGate p))

/-- Run the lifted circuit with the compressed oracle, starting from the algorithm state
tensored with the empty database. -/
def compressedRunState (p : ℝ) (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) :
    QState (((I × Bool) × W) × (I → Bool)) :=
  Run (compressedOracle p) (tensorLiftCircuit C) (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)))

/-- The Hadamard gate on the Boolean target register, with identity on the address and workspace
registers. -/
def controlHadamard : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ :=
  TensorGate (TensorGate (1 : Matrix I I ℂ) Hadamard) (1 : Matrix W W ℂ)

/-- Replace a query step by Hadamard, query and Hadamard steps, retaining each ordinary gate. -/
def bitToPhaseStep (s : Step ((I × Bool) × W)) : Circuit ((I × Bool) × W) :=
  match s with
  | Step.gate U => [Step.gate U]
  | Step.query => [Step.gate controlHadamard, Step.query, Step.gate controlHadamard]

/-- The phase query circuit obtained by an initial target Hadamard followed by the stepwise
Hadamard conversion of `C`. -/
def bitToPhaseCircuit (C : Circuit ((I × Bool) × W)) : Circuit ((I × Bool) × W) :=
  Step.gate controlHadamard :: (C.flatMap bitToPhaseStep)

/-- For `p` in [0, 1], the columns of the one-bit decompression matrix are orthonormal. -/
private theorem decompressEntry_gram (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a a' : Bool) :
    ∑ b : Bool, star (decompressEntry p b a) * decompressEntry p b a'
      = if a = a' then 1 else 0 := by
  have h1 : (0 : ℝ) ≤ 1 - p := by linarith
  have hs1 : Real.sqrt (1 - p) * Real.sqrt (1 - p) = 1 - p := Real.mul_self_sqrt h1
  have hs2 : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0
  cases a <;> cases a' <;>
    simp [decompressEntry, Complex.conj_ofReal] <;>
    first
    | rfl
    | simp [mul_comm]
    | (rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, hs1, hs2]; simp)

/-- A sum over Boolean tables of a product of complex coordinate factors equals the product of
the two-term coordinate sums. -/
private theorem sum_prod_swap (g : I → Bool → ℂ) :
    (∑ d : I → Bool, ∏ j, g j (d j)) = ∏ j, ∑ b : Bool, g j b := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- A sum over Boolean tables of a product of real coordinate factors equals the product of the
two-term coordinate sums. -/
private theorem sum_prod_swap_real (g : I → Bool → ℝ) :
    (∑ d : I → Bool, ∏ j, g j (d j)) = ∏ j, ∑ b : Bool, g j b := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- For `p` in [0, 1], the conjugate transpose of the decompression matrix multiplied by that
matrix is the identity. -/
theorem decompressGate_unitary (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (decompressGate (I := I) p)ᴴ * decompressGate p = 1 := by
  ext x x'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, decompressGate, Matrix.of_apply,
    Matrix.one_apply]
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [show (∑ d : I → Bool, ∏ j,
        star (decompressEntry p (d j) (x j)) * decompressEntry p (d j) (x' j))
      = ∏ j, ∑ b : Bool,
        star (decompressEntry p b (x j)) * decompressEntry p b (x' j) by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ],
    Finset.prod_congr rfl fun j _ => decompressEntry_gram p hp0 hp1 (x j) (x' j)]
  by_cases hxx : x = x'
  · subst hxx
    simp
  · obtain ⟨j₀, hj₀⟩ : ∃ j₀, x j₀ ≠ x' j₀ := by
      by_contra hall
      push Not at hall
      exact hxx (funext hall)
    rw [Finset.prod_eq_zero (Finset.mem_univ j₀) (by rw [if_neg hj₀]), if_neg hxx]

/-- The coherent Bernoulli table state is normalized when `p` lies in [0, 1]. -/
theorem bernoulliState_normalized (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Normalized (bernoulliState (I := I) p) := by
  have h1 : (0 : ℝ) ≤ 1 - p := by linarith
  have hnn : ∀ x : I → Bool, 0 ≤ bernoulliPmf p x := by
    intro x
    refine Finset.prod_nonneg fun j _ => ?_
    by_cases hxj : x j = true <;> simp [hxj] <;> linarith
  have hsq : ∀ x : I → Bool,
      ‖(Complex.ofReal (Real.sqrt (bernoulliPmf p x)) : ℂ)‖ ^ 2 = bernoulliPmf p x := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hnn x)]
  have hswap : (∑ d : I → Bool, ∏ j, if d j then p else 1 - p)
      = ∏ j, ∑ b : Bool, if b then p else 1 - p :=
    sum_prod_swap_real (fun _ b => if b then p else 1 - p)
  unfold Normalized bernoulliState
  calc (∑ x : I → Bool, ‖Complex.ofReal (Real.sqrt (bernoulliPmf p x))‖ ^ 2)
      = ∑ x : I → Bool, bernoulliPmf p x := Finset.sum_congr rfl fun x _ => hsq x
    _ = ∏ j, ∑ b : Bool, if b then p else 1 - p := hswap
    _ = 1 := by simp

/-- For `p` in [0, 1], decompression sends the all-false database ket to the coherent Bernoulli
table state. -/
theorem decompressGate_empty_database (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ApplyGate (decompressGate (I := I) p) (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)) = bernoulliState p := by
  have h1 : (0 : ℝ) ≤ 1 - p := by linarith
  funext x
  have hpos : ∀ j : I, 0 ≤ (if x j then p else 1 - p) := by
    intro j
    by_cases hxj : x j = true
    · rw [if_pos hxj]
      linarith
    · rw [if_neg hxj]
      linarith
  have hfactor : ∀ j : I, decompressEntry p (x j) false
      = Complex.ofReal (Real.sqrt (if x j then p else 1 - p)) := by
    intro j
    cases hxj : x j <;> simp [decompressEntry]
  have hprod : ∏ j, Complex.ofReal (Real.sqrt (if x j then p else 1 - p))
      = Complex.ofReal (Real.sqrt (bernoulliPmf p x)) := by
    rw [← Complex.ofReal_prod]
    congr 1
    rw [show bernoulliPmf p x = ∏ j, if x j then p else 1 - p from rfl,
      Real.sqrt_prod _ (fun j _ => hpos j)]
  simp only [ApplyGate, Matrix.mulVec, dotProduct, decompressGate, Matrix.of_apply, Qatlib.Foundations.PureStateMath.Ket,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (fun _ => false), if_pos rfl,
    Finset.prod_congr rfl fun j _ => hfactor j, hprod]
  rfl
  · intro d _ hd
    rw [if_neg (fun h : d = fun _ => false => hd h)]
  · simp

/-- The conversion from bit query circuits to phase query circuits preserves the query count. -/
theorem bitToPhaseCircuit_queryCount (C : Circuit ((I × Bool) × W)) :
    QueryCount (bitToPhaseCircuit C) = QueryCount C := by
  have flat : ∀ C : Circuit ((I × Bool) × W),
      QueryCount (C.flatMap bitToPhaseStep) = QueryCount C := by
    intro C
    induction C with
    | nil => rfl
    | cons s C ih =>
        cases s with
        | gate U =>
            simp only [List.flatMap_cons, bitToPhaseStep, List.cons_append, List.nil_append,
              queryCount_gate]
            exact ih
        | query =>
            simp only [List.flatMap_cons, bitToPhaseStep, List.cons_append, List.nil_append,
              queryCount_gate, queryCount_query]
            omega
  cases C with
  | nil => rfl
  | cons s C =>
      cases s with
      | gate U =>
          simp only [bitToPhaseCircuit, List.flatMap_cons, bitToPhaseStep, List.cons_append,
            List.nil_append, queryCount_gate]
          exact flat C
      | query =>
          simp only [bitToPhaseCircuit, List.flatMap_cons, bitToPhaseStep, List.cons_append,
            List.nil_append, queryCount_gate, queryCount_query]
          have := flat C
          omega

/-- The target Hadamard gate squares to the identity. -/
theorem controlHadamard_mul_self :
    (controlHadamard (I := I) (W := W)) * controlHadamard = 1 := by
  unfold controlHadamard
  rw [tensorGate_mul, tensorGate_mul, Matrix.one_mul, Matrix.one_mul, hadamard_mul_self,
    tensorGate_one, tensorGate_one]

/-- Two finite matrices are equal if their actions on every basis ket agree. -/
private theorem matrix_eq_of_mulVec_ket {H : Type} [Fintype H] [DecidableEq H]
    (M N : Matrix H H ℂ) (h : ∀ i : H, M *ᵥ Qatlib.Foundations.PureStateMath.Ket i = N *ᵥ Qatlib.Foundations.PureStateMath.Ket i) : M = N := by
  ext i j
  simpa [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq'] using congrFun (h j) i

/-- Multiplication by `A * Matrix.diagonal χ` equals multiplication by `A` after scaling each
vector coordinate by `χ`. -/
private theorem mulVec_diag {H : Type} [Fintype H] [DecidableEq H] (A : Matrix H H ℂ)
    (χ : H → ℂ) (v : QState H) :
    (A * Matrix.diagonal χ) *ᵥ v = A *ᵥ (fun r => χ r * v r) := by
  funext p
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite,
    mul_zero, Finset.sum_ite_eq', mul_assoc]

/-- The identity-address tensor Hadamard acts by summing over the Boolean target coordinate at
the fixed address. -/
private theorem tensorGate_one_hadamard_mulVec (g : QState (I × Bool)) (j : I) (b : Bool) :
    ((TensorGate (1 : Matrix I I ℂ) Hadamard) *ᵥ g) (j, b)
      = ∑ c : Bool, Hadamard b c * g (j, c) := by
  simp only [Matrix.mulVec, dotProduct, TensorGate, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro x _ hx
    rw [if_neg (fun h : j = x => hx h.symm)]
    simp
  · simp

/-- Conjugating the controlled phase oracle by the target Hadamard gives the Boolean bit oracle. -/
theorem tensor_hadamard_conj_phase (f : I → Bool) :
    (TensorGate (1 : Matrix I I ℂ) Hadamard) *
        (PhaseOracle fun jb : I × Bool => jb.2 && f jb.1) *
        (TensorGate (1 : Matrix I I ℂ) Hadamard)
      = BitOracleOn f := by
  refine matrix_eq_of_mulVec_ket _ _ fun jb₀ => ?_
  obtain ⟨j₀, b₀⟩ := jb₀
  have step1 : ((TensorGate (1 : Matrix I I ℂ) Hadamard) *ᵥ Qatlib.Foundations.PureStateMath.Ket (j₀, b₀))
      = fun jc : I × Bool => if jc.1 = j₀ then Hadamard jc.2 b₀ else 0 := by
    funext jc
    rw [tensorGate_one_hadamard_mulVec]
    by_cases hj : jc.1 = j₀
    · subst hj
      rw [Finset.sum_eq_single b₀]
      · rw [ket_self, mul_one, if_pos rfl]
      · intro c' _ hc'
        rw [ket_ne (fun h : (jc.1, c') = (jc.1, b₀) => hc' (congrArg Prod.snd h)), mul_zero]
      · simp
    · rw [if_neg hj]
      refine Finset.sum_eq_zero fun c' _ => ?_
      have hket : Qatlib.Foundations.PureStateMath.Ket (j₀, b₀) (jc.1, c') = 0 := by
        rw [Qatlib.Foundations.PureStateMath.Ket,
            if_neg (fun h : (jc.1, c') = (j₀, b₀) => hj (congrArg Prod.fst h))]
      rw [hket, mul_zero]
  have step2 : ((TensorGate (1 : Matrix I I ℂ) Hadamard) *
      (PhaseOracle fun jb : I × Bool => jb.2 && f jb.1) *
      (TensorGate (1 : Matrix I I ℂ) Hadamard)) *ᵥ Qatlib.Foundations.PureStateMath.Ket (j₀, b₀)
      = fun jc : I × Bool => if jc.1 = j₀ then
          ∑ c : Bool, Hadamard jc.2 c *
            ((if c && f jc.1 then (-1 : ℂ) else 1) * Hadamard c b₀) else 0 := by
    have hdiag : (PhaseOracle fun jb : I × Bool => jb.2 && f jb.1)
        = Matrix.diagonal (fun jb : I × Bool => if jb.2 && f jb.1 then (-1 : ℂ) else 1) := rfl
    rw [hdiag, ← Matrix.mulVec_mulVec, mulVec_diag, step1]
    funext jc
    rw [tensorGate_one_hadamard_mulVec]
    by_cases hj : jc.1 = j₀
    · subst hj
      rw [if_pos rfl]
      refine Finset.sum_congr rfl fun c' _ => ?_
      simp
    · rw [if_neg hj]
      refine Finset.sum_eq_zero fun c' _ => ?_
      simp [hj]
  rw [step2, show BitOracleOn f *ᵥ Qatlib.Foundations.PureStateMath.Ket (j₀, b₀)
      = Qatlib.Foundations.PureStateMath.Ket (j₀, b₀ ^^ f j₀) from applyGate_bitOracleOn_ket f j₀ b₀]
  funext jc
  obtain ⟨j₁, b₁⟩ := jc
  by_cases hj : j₁ = j₀
  · subst hj
    rw [if_pos rfl]
    cases hf : f j₁ <;> cases b₁ <;> cases b₀ <;>
      simp [Hadamard, inv_sqrt2_mul_self, Qatlib.Foundations.PureStateMath.Ket,
          Prod.mk.injEq] <;>
      first
      | rfl
      | norm_num
  · rw [if_neg hj]
    have hket : Qatlib.Foundations.PureStateMath.Ket (j₀, b₀ ^^ f j₀) (j₁, b₁) = 0 := by
      rw [Qatlib.Foundations.PureStateMath.Ket,
          if_neg (fun h : (j₁, b₁) = (j₀, b₀ ^^ f j₀) => hj (congrArg Prod.fst h))]
    rw [hket]

/-- Conjugating the workspace phase oracle by the target Hadamard gives the workspace bit
oracle. -/
theorem controlHadamard_mul_phase_mul_controlHadamard (f : I → Bool) :
    (controlHadamard (I := I) (W := W)) * workspacePhaseOracle f * controlHadamard
      = workspaceBitOracle f := by
  unfold controlHadamard workspacePhaseOracle workspaceBitOracle
  rw [tensorGate_mul, tensorGate_mul, Matrix.one_mul, Matrix.one_mul]
  exact congrArg (fun M : Matrix (I × Bool) (I × Bool) ℂ => TensorGate M 1)
    (tensor_hadamard_conj_phase f)

/-- Running the converted circuit with a phase oracle on the Hadamard-transformed input equals
running the original circuit with the bit oracle. -/
theorem run_bitToPhaseCircuit (f : I → Bool) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) :
    Run (workspacePhaseOracle f) (bitToPhaseCircuit C) (ApplyGate controlHadamard ψ)
      = Run (workspaceBitOracle f) C ψ := by
  have key : ∀ (φ : QState ((I × Bool) × W)),
      ApplyGate controlHadamard (ApplyGate (workspacePhaseOracle f)
        (ApplyGate controlHadamard φ)) = ApplyGate (workspaceBitOracle f) φ := by
    intro φ
    rw [← applyGate_mul, ← applyGate_mul,
      controlHadamard_mul_phase_mul_controlHadamard]
  have main : ∀ (C : Circuit ((I × Bool) × W)) (φ : QState ((I × Bool) × W)),
      Run (workspacePhaseOracle f) (C.flatMap bitToPhaseStep) φ
        = Run (workspaceBitOracle f) C φ := by
    intro C
    induction C with
    | nil => intro φ; rfl
    | cons s C ih =>
        intro φ
        cases s with
        | gate U =>
            simp only [List.flatMap_cons, bitToPhaseStep, List.cons_append, List.nil_append,
              run_gate]
            exact ih (ApplyGate U φ)
        | query =>
            simp only [List.flatMap_cons, bitToPhaseStep, List.cons_append, List.nil_append,
              run_gate, run_query]
            rw [key]
            exact ih (ApplyGate (workspaceBitOracle f) φ)
  simp only [bitToPhaseCircuit, run_gate]
  rw [← applyGate_mul, controlHadamard_mul_self, applyGate_one]
  exact main C ψ

/-- An identity tensor gate acts on each fixed left-coordinate slice by its right factor. -/
private theorem tensor_one_right_slice {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (M : Matrix B B ℂ) (v : QState (A × B)) (a : A) (b : B) :
    ApplyGate (TensorGate (1 : Matrix A A ℂ) M) v (a,b)
      = ApplyGate M (fun x => v (a,x)) b := by
  simp [ApplyGate, TensorGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply]

/-- A gate tensored with the identity acts on each fixed right-coordinate slice by its left
factor. -/
private theorem tensor_one_left_slice {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (M : Matrix A A ℂ) (v : QState (A × B)) (a : A) (b : B) :
    ApplyGate (TensorGate M (1 : Matrix B B ℂ)) v (a,b)
      = ApplyGate M (fun x => v (x,b)) a := by
  simp [ApplyGate, TensorGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply]

/-- At a fixed table, the joint phase oracle acts on the algorithm slice as the corresponding
workspace phase oracle. -/
private theorem joint_phase_slice (v : QState (((I × Bool) × W) × (I → Bool)))
    (q : (I × Bool) × W) (x : I → Bool) :
    ApplyGate jointPhaseOracle v (q,x)
      = ApplyGate (workspacePhaseOracle x) (fun r => v (r,x)) q := by
  rw [workspacePhaseOracle, tensor_one_left_slice]
  simp [ApplyGate, jointPhaseOracle, PhaseOracle, Matrix.mulVec_diagonal]

/-- The joint phase oracle applies the table-specific workspace phase oracle to the algorithm
factor while leaving the table ket fixed. -/
theorem joint_phase_oracle_fiber (φ : QState ((I × Bool) × W)) (x : I → Bool) :
    jointPhaseOracle (W := W) *ᵥ TensorState φ (Qatlib.Foundations.PureStateMath.Ket x)
      = TensorState (workspacePhaseOracle (W := W) x *ᵥ φ) (Qatlib.Foundations.PureStateMath.Ket x) := by
  funext qx
  obtain ⟨q,y⟩ := qx
  rw [show jointPhaseOracle *ᵥ _ = ApplyGate jointPhaseOracle _ from rfl, joint_phase_slice]
  by_cases h : y = x
  · subst y
    simp only [TensorState, ket_self, mul_one]
    rfl
  · simp [TensorState, Qatlib.Foundations.PureStateMath.Ket, h, ApplyGate, Matrix.mulVec,
      dotProduct]

/-- Circuit execution commutes with multiplying the initial state by a complex scalar. -/
private theorem compressed_run_scalar {A : Type} [Fintype A] [DecidableEq A]
    (O : Matrix A A ℂ) (C : Circuit A) (c : ℂ) (ψ : QState A) :
    Run O C (fun q => c * ψ q) = fun q => c * Run O C ψ q := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp only [Run]
    all_goals
      rw [show ApplyGate _ (fun q => c * ψ q) = fun q => c * ApplyGate _ ψ q by
        funext q
        simp only [ApplyGate, Matrix.mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring]
      exact ih _

/-- At a fixed table, a lifted circuit run with the joint phase oracle equals the original
circuit run with that table as its phase oracle. -/
private theorem joint_run_slice (C : Circuit ((I × Bool) × W))
    (v : QState (((I × Bool) × W) × (I → Bool))) (x : I → Bool) :
    (fun q => Run jointPhaseOracle (tensorLiftCircuit C) v (q,x))
      = Run (workspacePhaseOracle x) C (fun q => v (q,x)) := by
  induction C generalizing v with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      simp only [tensorLiftCircuit, List.map_cons, tensorLiftStep, run_gate]
      rw [show C.map tensorLiftStep = tensorLiftCircuit C from rfl, ih]
      congr 1
      funext q
      exact tensor_one_left_slice U v q x
    | query =>
      simp only [tensorLiftCircuit, List.map_cons, tensorLiftStep, run_query]
      rw [show C.map tensorLiftStep = tensorLiftCircuit C from rfl, ih]
      congr 1
      funext q
      exact joint_phase_slice v q x

/-- Execution from the coherent Bernoulli table state has amplitude equal to the table amplitude
times the corresponding ordinary phase oracle execution amplitude. -/
theorem joint_run_expansion (p : ℝ) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) (q : (I × Bool) × W) (x : I → Bool) :
    Run (jointPhaseOracle (W := W)) (tensorLiftCircuit C)
        (TensorState ψ (bernoulliState p)) (q,x)
      = bernoulliState p x * Run (workspacePhaseOracle x) C ψ q := by
  have h := congrFun (joint_run_slice C (TensorState ψ (bernoulliState p)) x) q
  rw [show (fun r => TensorState ψ (bernoulliState p) (r,x))
      = fun r => bernoulliState p x * ψ r by funext r; simp [TensorState,mul_comm]] at h
  rw [compressed_run_scalar] at h
  exact h

/-- The decompression matrix belongs to the unitary group for `p` in [0, 1]. -/
private theorem decompressGate_mem_unitary (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    decompressGate (I := I) p ∈ Matrix.unitaryGroup (I → Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact decompressGate_unitary p hp0 hp1

/-- For `p` in [0, 1], applying inverse decompression before a compressed circuit run equals
applying it after the corresponding joint phase oracle run. -/
private theorem compressed_run_conjugate (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (φ : QState (((I × Bool) × W) × (I → Bool))) :
    Run (compressedOracle p) (tensorLiftCircuit C)
        (ApplyGate (TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
          (decompressGate p)ᴴ) φ)
      = ApplyGate (TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
          (decompressGate p)ᴴ) (Run jointPhaseOracle (tensorLiftCircuit C) φ) := by
  have hFF : decompressGate (I := I) p * (decompressGate p)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp (decompressGate_mem_unitary p hp0 hp1)
  have hquery : compressedOracle (I := I) (W := W) p *
      TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (decompressGate p)ᴴ
      = TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (decompressGate p)ᴴ *
        jointPhaseOracle := by
    unfold compressedOracle
    rw [Matrix.mul_assoc, tensorGate_mul, Matrix.one_mul, hFF, tensorGate_one,
      Matrix.mul_one]
  have hgate : ∀ U : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ,
      TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ) *
          TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (decompressGate p)ᴴ
        = TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (decompressGate p)ᴴ *
          TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ) := by
    intro U
    simp only [tensorGate_mul, Matrix.mul_one, Matrix.one_mul]
  induction C generalizing φ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      simp only [tensorLiftCircuit, List.map_cons, tensorLiftStep, run_gate]
      rw [← applyGate_mul, hgate, applyGate_mul]
      exact ih _
    | query =>
      simp only [tensorLiftCircuit, List.map_cons, tensorLiftStep, run_query]
      rw [← applyGate_mul, hquery, applyGate_mul]
      exact ih _

/-- For `p` in [0, 1], compressed execution from the empty database equals inverse decompression
of joint phase oracle execution from the coherent Bernoulli state. -/
theorem compressed_run_from_empty (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) :
    Run (compressedOracle (I := I) (W := W) p) (tensorLiftCircuit C)
        (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)))
      = ApplyGate (TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
          (decompressGate p)ᴴ)
          (Run jointPhaseOracle (tensorLiftCircuit C) (TensorState ψ (bernoulliState p))) := by
  have hinit : ApplyGate (decompressGate (I := I) p)ᴴ (bernoulliState p)
      = Qatlib.Foundations.PureStateMath.Ket (fun _ => false) := by
    rw [← decompressGate_empty_database p hp0 hp1, ← applyGate_mul,
      decompressGate_unitary p hp0 hp1, applyGate_one]
  have h := compressed_run_conjugate p hp0 hp1 C (TensorState ψ (bernoulliState p))
  rwa [applyGate_tensorGate, applyGate_one, hinit] at h

/-- For `p` in [0, 1], tracing out the compressed database gives the Bernoulli-weighted sum of
the algorithm outer products from ordinary phase oracle executions. -/
theorem compressed_marginal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (q q' : (I × Bool) × W) :
    (∑ d : I → Bool, compressedRunState p C ψ (q,d) * star (compressedRunState p C ψ (q',d)))
      = ∑ x : I → Bool, bernoulliPmf p x *
          Run (workspacePhaseOracle x) C ψ q * star (Run (workspacePhaseOracle x) C ψ q') := by
  let v := Run (jointPhaseOracle (I := I) (W := W)) (tensorLiftCircuit C)
    (TensorState ψ (bernoulliState p))
  have hfiber (r : (I × Bool) × W) :
      (fun d => compressedRunState p C ψ (r,d))
        = ApplyGate (decompressGate p)ᴴ (fun x => v (r,x)) := by
    funext d
    rw [compressedRunState, compressed_run_from_empty p hp0 hp1,
      tensor_one_right_slice]
  have hU : (decompressGate (I := I) p)ᴴ ∈ Matrix.unitaryGroup (I → Bool) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp (decompressGate_mem_unitary p hp0 hp1)
  have hinner := inner_applyGate hU (fun x => v (q',x)) (fun x => v (q,x))
  have hgram : (∑ d, compressedRunState p C ψ (q,d) * star (compressedRunState p C ψ (q',d)))
      = ∑ x, v (q,x) * star (v (q',x)) := by
    simpa only [← hfiber q, ← hfiber q', Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, mul_comm]
      using hinner
  rw [hgram]
  apply Finset.sum_congr rfl
  intro x _
  have hnn : 0 ≤ bernoulliPmf p x := by
    apply Finset.prod_nonneg
    intro j _
    split <;> linarith
  have hs : bernoulliState p x * star (bernoulliState p x)
      = (bernoulliPmf p x : ℂ) := by
    simp only [bernoulliState, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hnn]
  change v (q,x) * star (v (q',x)) = _
  simp only [v, joint_run_expansion, star_mul]
  calc _ = (bernoulliState p x * star (bernoulliState p x)) *
        Run (workspacePhaseOracle x) C ψ q * star (Run (workspacePhaseOracle x) C ψ q') := by ring
    _ = _ := by rw [hs]

/-- The one-bit decompression matrix is symmetric. -/
private theorem decompressEntry_symmetric (p : ℝ) (a b : Bool) :
    decompressEntry p a b = decompressEntry p b a := by
  cases a <;> cases b <;> rfl

/-- Every one-bit decompression matrix entry is fixed by complex conjugation. -/
private theorem decompressEntry_star (p : ℝ) (a b : Bool) :
    star (decompressEntry p a b) = decompressEntry p a b := by
  cases a <;> cases b <;> simp [decompressEntry]

/-- The product decompression matrix is equal to its conjugate transpose. -/
private theorem decompressGate_selfadjoint (p : ℝ) :
    (decompressGate (I := I) p)ᴴ = decompressGate p := by
  ext x y
  simp only [Matrix.conjTranspose_apply, decompressGate, Matrix.of_apply, star_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [decompressEntry_star, decompressEntry_symmetric]

/-- The compressed oracle is block diagonal in the algorithm basis, with each database block
given by the conjugated table-dependent phase. -/
private theorem compressed_oracle_block (p : ℝ) (q q' : (I × Bool) × W)
    (d d' : I → Bool) :
    compressedOracle p (q,d) (q',d') =
      if q = q' then ∑ x : I → Bool,
        star (decompressGate p x d) *
          ((if q.1.2 && x q.1.1 then (-1 : ℂ) else 1) * decompressGate p x d')
      else 0 := by
  unfold compressedOracle jointPhaseOracle
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.mul_diagonal, tensorGate_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single q]
  · by_cases h : q = q'
    · subst q'
      simp only [ite_true, one_mul, mul_assoc]
    · simp only [ite_true, if_neg h, zero_mul, mul_zero, Finset.sum_const_zero]
  · intro r _ hr
    simp only [if_neg (Ne.symm hr), zero_mul, Finset.sum_const_zero]
  · simp

/-- A compressed oracle entry is zero when its algorithm basis indices differ. -/
theorem compressed_oracle_offdiag (p : ℝ) (q q' : (I × Bool) × W)
    (d d' : I → Bool) (h : q ≠ q') :
    compressedOracle p (q,d) (q',d') = 0 := by
  rw [compressed_oracle_block, if_neg h]

/-- For `p` in [0, 1], conjugating the one-bit sign phase by decompression gives
`compressedQueryEntry`. -/
private theorem decompressEntry_phase_gram (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a a' : Bool) :
    (∑ b : Bool, star (decompressEntry p b a) *
      ((if b then (-1 : ℂ) else 1) * decompressEntry p b a'))
      = compressedQueryEntry p a a' := by
  have h1 : 0 ≤ 1 - p := by linarith
  have hm : Real.sqrt (p * (1-p)) = Real.sqrt p * Real.sqrt (1-p) :=
    Real.sqrt_mul hp0 _
  have hs0 := Real.mul_self_sqrt hp0
  have hs1 := Real.mul_self_sqrt h1
  cases a <;> cases a' <;>
    simp [decompressEntry, compressedQueryEntry, hm,
      ← Complex.ofReal_mul, ← Complex.ofReal_add]
  all_goals
    first
    | (rw [hs0, hs1]; push_cast; ring)
    | ring

/-- For `p` in [0, 1], an active query uses `compressedQueryEntry` only when the databases agree
away from the addressed bit; an inactive query is the identity on the database. -/
theorem compressed_oracle_entry (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (j : I) (b : Bool) (w : W) (d d' : I → Bool) :
    compressedOracle p (((j,b),w),d) (((j,b),w),d') =
      if b then
        if ∀ k, k ≠ j → d k = d' k then compressedQueryEntry p (d j) (d' j) else 0
      else if d = d' then 1 else 0 := by
  rw [compressed_oracle_block, if_pos rfl]
  cases b with
  | false =>
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, one_mul]
    have h := congrFun (congrFun (decompressGate_unitary p hp0 hp1) d) d'
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  | true =>
    simp only [Bool.true_and, ↓reduceIte]
    have hfactor (x : I → Bool) :
        star (decompressGate p x d) *
            ((if x j then (-1 : ℂ) else 1) * decompressGate p x d')
          = ∏ k, star (decompressEntry p (x k) (d k)) *
              ((if k = j then (if x k then (-1 : ℂ) else 1) else 1) *
                decompressEntry p (x k) (d' k)) := by
      simp only [decompressGate, Matrix.of_apply, star_prod, Finset.prod_mul_distrib,
        Fintype.prod_ite_eq']
    simp_rw [hfactor]
    rw [sum_prod_swap (fun k a => star (decompressEntry p a (d k)) *
      ((if k = j then (if a then (-1 : ℂ) else 1) else 1) *
        decompressEntry p a (d' k)))]
    have hcoord (k : I) :
        (∑ a : Bool, star (decompressEntry p a (d k)) *
          ((if k = j then (if a then (-1 : ℂ) else 1) else 1) *
            decompressEntry p a (d' k)))
          = if k = j then compressedQueryEntry p (d k) (d' k)
            else if d k = d' k then 1 else 0 := by
      by_cases h : k = j
      · simp only [if_pos h]
        exact decompressEntry_phase_gram p hp0 hp1 _ _
      · simp only [if_neg h, one_mul]
        exact decompressEntry_gram p hp0 hp1 _ _
    simp_rw [hcoord]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    simp only [ite_true]
    by_cases h : ∀ k, k ≠ j → d k = d' k
    · rw [if_pos h]
      have he : (∏ k ∈ Finset.univ.erase j,
          if k = j then compressedQueryEntry p (d k) (d' k)
            else if d k = d' k then 1 else 0) = 1 := by
        apply Finset.prod_eq_one
        intro k hk
        have hk' := (Finset.mem_erase.mp hk).1
        simp [hk', h k hk']
      rw [he, mul_one]
    · rw [if_neg h]
      push Not at h
      obtain ⟨k,hkj,hdd⟩ := h
      have he : (∏ k ∈ Finset.univ.erase j,
          if k = j then compressedQueryEntry p (d k) (d' k)
            else if d k = d' k then 1 else 0) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩)
        simp [hkj, hdd]
      rw [he, mul_zero]

/-- For `p` in [0, 1], a compressed oracle entry within an algorithm block is zero unless the
databases agree away from the query address. -/
theorem compressed_oracle_locality (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (q : (I × Bool) × W) (d d' : I → Bool) :
    (∀ k, k ≠ q.1.1 → d k = d' k) ∨ compressedOracle p (q,d) (q,d') = 0 := by
  by_cases h : ∀ k, k ≠ q.1.1 → d k = d' k
  · exact Or.inl h
  · right
    obtain ⟨⟨j,b⟩,w⟩ := q
    rw [compressed_oracle_entry p hp0 hp1]
    cases b
    · have hne : d ≠ d' := by intro he; subst d'; exact h (fun _ _ => rfl)
      simp [hne]
    · simp only [↓reduceIte, if_neg h]

/-- The all-false database has cardinality zero. -/
private theorem databaseCard_empty : databaseCard (I := I) (fun _ => false) = 0 := by
  simp [databaseCard, databaseSupport]

/-- If two Boolean databases agree away from one address, the first cardinality is at most the
second plus one. -/
private theorem databaseCard_le_of_local {d d' : I → Bool} (j : I)
    (h : ∀ k, k ≠ j → d k = d' k) : databaseCard d ≤ databaseCard d' + 1 := by
  have hsub : databaseSupport d ⊆ insert j (databaseSupport d') := by
    intro k hk
    by_cases hkj : k = j
    · simp [hkj]
    · apply Finset.mem_insert_of_mem
      simpa only [databaseSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        h k hkj] using hk
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- A gate acting only on algorithm registers preserves vanishing amplitudes on databases of
cardinality greater than `t`. -/
private theorem tensor_gate_preserves_database_support (U : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
    (v : QState (((I × Bool) × W) × (I → Bool))) (t : ℕ)
    (h : ∀ q d, t < databaseCard d → v (q,d) = 0) :
    ∀ q d, t < databaseCard d →
      ApplyGate (TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ)) v (q,d) = 0 := by
  intro q d hd
  rw [tensor_one_left_slice]
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro r _
  rw [h r d hd, mul_zero]

/-- For `p` in [0, 1], a compressed query maps states supported on databases of size at most `t`
to states supported on databases of size at most `t + 1`. -/
private theorem query_preserves_database_support (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : QState (((I × Bool) × W) × (I → Bool))) (t : ℕ)
    (h : ∀ q d, t < databaseCard d → v (q,d) = 0) :
    ∀ q d, t + 1 < databaseCard d → ApplyGate (compressedOracle p) v (q,d) = 0 := by
  intro q d hd
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro q' _
  apply Finset.sum_eq_zero
  intro d' _
  by_cases hq : q = q'
  · subst q'
    rcases compressed_oracle_locality p hp0 hp1 q d d' with hlocal | hz
    · have hcard := databaseCard_le_of_local q.1.1 hlocal
      rw [h q d' (by omega), mul_zero]
    · rw [hz, zero_mul]
  · rw [compressed_oracle_offdiag p q q' d d' hq, zero_mul]

/-- For `p` in [0, 1], compressed execution from the empty database has zero amplitude on
databases larger than any upper bound `t` on the circuit query count. -/
theorem database_support_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) (t : ℕ)
    (ht : QueryCount C ≤ t) (q : (I × Bool) × W) (d : I → Bool)
    (hd : t < databaseCard d) : compressedRunState p C ψ (q,d) = 0 := by
  have h : ∀ (C : Circuit ((I × Bool) × W)) q d,
      QueryCount C < databaseCard d → compressedRunState p C ψ (q,d) = 0 := by
    intro C
    induction C using List.reverseRecOn with
    | nil =>
      intro q d hd
      have hne : d ≠ fun _ => false := by
        intro he
        rw [he, databaseCard_empty] at hd
        omega
      simp [compressedRunState, tensorLiftCircuit, TensorState,
          Qatlib.Foundations.PureStateMath.Ket, hne]
    | append_singleton C s ih =>
      intro q d hd
      cases s with
      | gate U =>
        simp only [compressedRunState, tensorLiftCircuit, List.map_append,
          List.map_cons, List.map_nil, tensorLiftStep, run_append, run_gate, run_nil]
        change ApplyGate (TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ))
          (compressedRunState p C ψ) (q,d) = 0
        simp only [queryCount_append, queryCount_gate, queryCount_nil, add_zero] at hd
        exact tensor_gate_preserves_database_support U (compressedRunState p C ψ)
          (QueryCount C) ih q d hd
      | query =>
        simp only [compressedRunState, tensorLiftCircuit, List.map_append,
          List.map_cons, List.map_nil, tensorLiftStep, run_append, run_query, run_nil]
        change ApplyGate (compressedOracle p) (compressedRunState p C ψ) (q,d) = 0
        simp only [queryCount_append, queryCount_query, queryCount_nil, zero_add] at hd
        exact query_preserves_database_support p hp0 hp1 (compressedRunState p C ψ)
          (QueryCount C) ih q d hd
  exact h C q d (lt_of_le_of_lt ht hd)

/-- The sum of squared state amplitudes weighted by the `i`th binomial coefficient of the
database cardinality. -/
private def databaseMoment (i : ℕ) (v : QState (((I × Bool) × W) × (I → Bool))) : ℝ :=
  ∑ q, ∑ d, (Nat.choose (databaseCard d) i : ℝ) * ‖v (q,d)‖ ^ 2

/-- If a² + s² = 1, then s(x² − y²) − 2axy is at most x² + y². -/
private theorem two_bit_real_progress (a s x y : ℝ) (hu : a^2+s^2=1) :
    s*(x^2-y^2)-2*a*x*y ≤ x^2+y^2 := by
  have hc : (s*(x^2-y^2)-a*(2*x*y))^2 ≤
      (s^2+a^2)*((x^2-y^2)^2+(2*x*y)^2) := by
    nlinarith [sq_nonneg (a*(x^2-y^2)+s*(2*x*y))]
  have hu' : s^2+a^2=1 := by linarith
  rw [hu'] at hc
  have he : (x^2-y^2)^2+(2*x*y)^2=(x^2+y^2)^2 := by ring
  rw [one_mul,he] at hc
  nlinarith [sq_nonneg x, sq_nonneg y]

/-- The two-coordinate transformation with rows (a, s) and (s, −a) preserves squared complex
Euclidean norm when a² + s² = 1. -/
private theorem two_bit_energy (a s : ℝ) (hu : a^2+s^2=1) (z₀ z₁ : ℂ) :
    ‖(a : ℂ)*z₀+(s : ℂ)*z₁‖^2+‖(s : ℂ)*z₀-(a : ℂ)*z₁‖^2
      = ‖z₀‖^2+‖z₁‖^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
  linear_combination (z₀.re^2+z₀.im^2+z₁.re^2+z₁.im^2)*hu

/-- For nonnegative `s` with a² + s² = 1, the increase in the second-coordinate squared norm
under the two-bit transformation is at most `s` times the original total squared norm. -/
private theorem two_bit_progress (a s : ℝ) (hs : 0 ≤ s) (hu : a^2+s^2=1) (z₀ z₁ : ℂ) :
    ‖(s : ℂ)*z₀-(a : ℂ)*z₁‖^2-‖z₁‖^2 ≤ s*(‖z₀‖^2+‖z₁‖^2) := by
  have hr := two_bit_real_progress a s z₀.re z₁.re hu
  have hi := two_bit_real_progress a s z₀.im z₁.im hu
  have hbound := mul_le_mul_of_nonneg_left (add_le_add hr hi) hs
  have he : ‖(s : ℂ)*z₀-(a : ℂ)*z₁‖^2-‖z₁‖^2 =
      s*((s*(z₀.re^2-z₁.re^2)-2*a*z₀.re*z₁.re)+
        (s*(z₀.im^2-z₁.im^2)-2*a*z₀.im*z₁.im)) := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,add_zero]
    linear_combination (z₁.re^2+z₁.im^2)*hu
  rw [he]
  simp only [Complex.sq_norm,Complex.normSq_apply]
  convert! hbound using 1; ring

/-- Reconstruct a Boolean database from a selected bit at `j` and the values at all other
addresses. -/
private def databaseAt (j : I) (r : {k : I // k ≠ j} → Bool) (b : Bool) : I → Bool :=
  (Equiv.funSplitAt j Bool).symm (b,r)

/-- The reconstructed database has value `b` at the selected address `j`. -/
private theorem databaseAt_self (j : I) (r : {k : I // k ≠ j} → Bool) (b : Bool) :
    databaseAt j r b j = b := by simp [databaseAt,Equiv.funSplitAt,Equiv.piSplitAt]

/-- Away from the selected address, `databaseAt` equals the supplied residual database. -/
private theorem databaseAt_other (j k : I) (hk : k ≠ j)
    (r : {k : I // k ≠ j} → Bool) (b : Bool) : databaseAt j r b k = r ⟨k,hk⟩ := by
  simp [databaseAt,Equiv.funSplitAt,Equiv.piSplitAt,hk]

/-- Two reconstructed databases agree away from the selected address exactly when their residual
databases are equal. -/
private theorem databaseAt_local_iff (j : I) (r r' : {k : I // k ≠ j} → Bool)
    (b b' : Bool) :
    (∀ k, k ≠ j → databaseAt j r b k = databaseAt j r' b' k) ↔ r = r' := by
  constructor
  · intro h
    funext k
    simpa only [databaseAt_other j k.val k.property] using h k.val k.property
  · intro h k hk
    subst r'
    simp only [databaseAt_other j k hk]

/-- Changing the selected reconstructed bit from false to true increases the database
cardinality by one. -/
private theorem databaseAt_card (j : I) (r : {k : I // k ≠ j} → Bool) :
    databaseCard (databaseAt j r true) = databaseCard (databaseAt j r false) + 1 := by
  have he : databaseSupport (databaseAt j r true) = insert j (databaseSupport (databaseAt j r false)) := by
    ext k
    by_cases hk : k = j
    · subst k
      simp [databaseSupport,databaseAt_self]
    · simp [databaseSupport,databaseAt_other j k hk,hk]
  have hn : j ∉ databaseSupport (databaseAt j r false) := by
    simp [databaseSupport,databaseAt_self]
  simp only [databaseCard,he,Finset.card_insert_of_notMem hn]

/-- The compressed oracle acts on a fixed algorithm basis index by summing only over database
indices. -/
private theorem compressed_query_block_apply (p : ℝ)
    (v : QState (((I × Bool) × W) × (I → Bool))) (q : (I × Bool) × W) (d : I → Bool) :
    ApplyGate (compressedOracle p) v (q,d) =
      ∑ d', compressedOracle p (q,d) (q,d') * v (q,d') := by
  simp only [ApplyGate,Matrix.mulVec,dotProduct]
  rw [Fintype.sum_prod_type,Finset.sum_eq_single q]
  · intro q' _ hq
    apply Finset.sum_eq_zero
    intro d' _
    rw [compressed_oracle_offdiag p q q' d d' (Ne.symm hq),zero_mul]
  · simp

/-- For an active target bit and `p` in [0, 1], the query acts on the two databases with a fixed
residual part by `compressedQueryEntry`. -/
private theorem compressed_query_pair (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : QState (((I × Bool) × W) × (I → Bool))) (j : I) (w : W)
    (r : {k : I // k ≠ j} → Bool) (b : Bool) :
    ApplyGate (compressedOracle p) v (((j,true),w),databaseAt j r b) =
      ∑ b' : Bool, compressedQueryEntry p b b' * v (((j,true),w),databaseAt j r b') := by
  rw [compressed_query_block_apply]
  rw [← (Equiv.funSplitAt j Bool).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b' _
  change (∑ r', compressedOracle p (((j,true),w),databaseAt j r b)
    (((j,true),w),databaseAt j r' b') * v (((j,true),w),databaseAt j r' b')) = _
  simp_rw [compressed_oracle_entry p hp0 hp1]
  simp only [↓reduceIte,databaseAt_self,databaseAt_local_iff]
  simp [ite_mul]

/-- For `p` in [0, 1], a compressed query leaves every amplitude with false target bit
unchanged. -/
private theorem compressed_query_idle (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : QState (((I × Bool) × W) × (I → Bool))) (j : I) (w : W) (d : I → Bool) :
    ApplyGate (compressedOracle p) v (((j,false),w),d) = v (((j,false),w),d) := by
  rw [compressed_query_block_apply]
  simp_rw [compressed_oracle_entry p hp0 hp1]
  simp [ite_mul]

/-- For `p` in [0, 1], the squared diagonal parameter (1 − 2p)² and squared coupling (2√(p(1 −
p)))² sum to one. -/
private theorem compressedQuery_parameters (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1-2*p)^2+(2*Real.sqrt (p*(1-p)))^2=1 := by
  have hp : 0 ≤ p*(1-p) := mul_nonneg hp0 (by linarith)
  nlinarith [Real.sq_sqrt hp]

/-- Within one active two-database block, the order-`i + 1` binomial moment after a query is at
most its previous value plus 2√(p(1 − p)) times the order-`i` moment. -/
private theorem compressed_query_pair_moment (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : QState (((I × Bool) × W) × (I → Bool))) (j : I) (w : W)
    (r : {k : I // k ≠ j} → Bool) (i : ℕ) :
    (∑ b : Bool, (Nat.choose (databaseCard (databaseAt j r b)) (i+1) : ℝ) *
        ‖ApplyGate (compressedOracle p) v (((j,true),w),databaseAt j r b)‖^2)
      ≤ (∑ b : Bool, (Nat.choose (databaseCard (databaseAt j r b)) (i+1) : ℝ) *
          ‖v (((j,true),w),databaseAt j r b)‖^2) +
        (2*Real.sqrt (p*(1-p))) *
          (∑ b : Bool, (Nat.choose (databaseCard (databaseAt j r b)) i : ℝ) *
            ‖v (((j,true),w),databaseAt j r b)‖^2) := by
  let a := 1-2*p
  let s := 2*Real.sqrt (p*(1-p))
  let z₀ := v (((j,true),w),databaseAt j r false)
  let z₁ := v (((j,true),w),databaseAt j r true)
  let n := databaseCard (databaseAt j r false)
  have hu : a^2+s^2=1 := compressedQuery_parameters p hp0 hp1
  have hs : 0 ≤ s := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hzero : ApplyGate (compressedOracle p) v (((j,true),w),databaseAt j r false)
      = (a : ℂ)*z₀+(s : ℂ)*z₁ := by
    rw [compressed_query_pair p hp0 hp1]
    simp [compressedQueryEntry,a,s,z₀,z₁,add_comm]
  have hone : ApplyGate (compressedOracle p) v (((j,true),w),databaseAt j r true)
      = (s : ℂ)*z₀-(a : ℂ)*z₁ := by
    rw [compressed_query_pair p hp0 hp1]
    simp [compressedQueryEntry,a,s,z₀,z₁]
    ring
  have he := two_bit_energy a s hu z₀ z₁
  have hp := two_bit_progress a s hs hu z₀ z₁
  have hc : (Nat.choose n i : ℝ) ≤ (Nat.choose (n+1) i : ℝ) := by
    exact_mod_cast Nat.choose_le_succ n i
  have hweight := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (Nat.choose n i))
  have hmono := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖z₁‖)) hs
  simp only [Fintype.sum_bool, hzero,hone,databaseAt_card,Nat.choose_succ_succ',Nat.cast_add]
  dsimp only [n,z₀,z₁,a,s] at he hp hweight hmono ⊢
  nlinarith [hweight,hmono]

/-- For `p` in [0, 1], a compressed query increases the order-`i + 1` database moment by at most
2√(p(1 − p)) times the order-`i` moment. -/
private theorem compressed_query_moment_step (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : QState (((I × Bool) × W) × (I → Bool))) (i : ℕ) :
    databaseMoment (i+1) (ApplyGate (compressedOracle p) v)
      ≤ databaseMoment (i+1) v + (2*Real.sqrt (p*(1-p))) * databaseMoment i v := by
  have hq (q : (I × Bool) × W) :
      (∑ d, (Nat.choose (databaseCard d) (i+1) : ℝ) *
          ‖ApplyGate (compressedOracle p) v (q,d)‖^2)
        ≤ (∑ d, (Nat.choose (databaseCard d) (i+1) : ℝ) * ‖v (q,d)‖^2) +
          (2*Real.sqrt (p*(1-p))) * (∑ d, (Nat.choose (databaseCard d) i : ℝ) * ‖v (q,d)‖^2) := by
    obtain ⟨⟨j,b⟩,w⟩ := q
    cases b with
    | false =>
      simp_rw [compressed_query_idle p hp0 hp1]
      apply le_add_of_nonneg_right
      apply mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    | true =>
      rw [← (Equiv.funSplitAt j Bool).symm.sum_comp,
        ← (Equiv.funSplitAt j Bool).symm.sum_comp,
        ← (Equiv.funSplitAt j Bool).symm.sum_comp]
      simp only [Fintype.sum_prod_type]
      conv_lhs => rw [Finset.sum_comm]
      conv_rhs => arg 1; rw [Finset.sum_comm]
      conv_rhs => arg 2; arg 2; rw [Finset.sum_comm]
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro r _
      exact compressed_query_pair_moment p hp0 hp1 v j w r i
  unfold databaseMoment
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun q _ => hq q)

/-- A finite unitary matrix preserves the sum of squared absolute values of state amplitudes. -/
private theorem unitary_mass {A : Type} [Fintype A] [DecidableEq A]
    (U : Matrix A A ℂ) (hU : U ∈ Matrix.unitaryGroup A ℂ) (ψ : QState A) :
    (∑ q, ‖ApplyGate U ψ q‖^2) = ∑ q, ‖ψ q‖^2 := by
  have h := inner_applyGate hU ψ ψ
  rw [inner_self,inner_self,← Complex.ofReal_sum,← Complex.ofReal_sum] at h
  exact Complex.ofReal_injective h

/-- A unitary gate on the algorithm registers preserves every binomial database moment. -/
private theorem databaseMoment_gate (i : ℕ) (U : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ)
    (v : QState (((I × Bool) × W) × (I → Bool))) :
    databaseMoment i (ApplyGate (TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ)) v)
      = databaseMoment i v := by
  unfold databaseMoment
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp_rw [tensor_one_left_slice]
  rw [← Finset.mul_sum,← Finset.mul_sum,unitary_mass U hU]

/-- The joint phase oracle belongs to the unitary group. -/
private theorem jointPhaseOracle_unitary :
    jointPhaseOracle (I := I) (W := W) ∈
      Matrix.unitaryGroup (((I × Bool) × W) × (I → Bool)) ℂ :=
  phaseOracle_unitary (fun q : (((I × Bool) × W) × (I → Bool)) =>
    q.1.1.2 && q.2 q.1.1.1)

/-- The compressed oracle belongs to the unitary group for `p` in [0, 1]. -/
private theorem compressedOracle_unitary (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    compressedOracle (I := I) (W := W) p ∈
      Matrix.unitaryGroup (((I × Bool) × W) × (I → Bool)) ℂ := by
  have hF := decompressGate_mem_unitary (I := I) p hp0 hp1
  have hF' : (decompressGate (I := I) p)ᴴ ∈ Matrix.unitaryGroup (I → Bool) ℂ := by
    rw [decompressGate_selfadjoint]
    exact hF
  exact Submonoid.mul_mem _
    (Submonoid.mul_mem _ (tensorGate_unitary (Submonoid.one_mem _) hF') jointPhaseOracle_unitary)
    (tensorGate_unitary (Submonoid.one_mem _) hF)

/-- Lifting a unitary algorithm circuit to include the database register preserves circuit
unitarity. -/
private theorem tensorLiftCircuit_unitary (C : Circuit ((I × Bool) × W))
    (hC : IsUnitaryCircuit C) : IsUnitaryCircuit (tensorLiftCircuit C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
    cases s with
    | gate U =>
      obtain ⟨hU,hC⟩ := (isUnitaryCircuit_gate U C).mp hC
      apply (isUnitaryCircuit_gate (TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ))
        (tensorLiftCircuit C)).mpr
      exact ⟨tensorGate_unitary hU (Submonoid.one_mem _),ih hC⟩
    | query =>
      apply (isUnitaryCircuit_query (tensorLiftCircuit C)).mpr
      exact ih ((isUnitaryCircuit_query C).mp hC)

/-- For `p` in [0, 1], compressed execution of a unitary circuit from a normalized algorithm
state is normalized. -/
private theorem compressedRunState_normalized (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (hC : IsUnitaryCircuit C)
    (ψ : QState ((I × Bool) × W)) (hψ : Normalized ψ) :
    Normalized (compressedRunState p C ψ) :=
  normalized_run _ (compressedOracle_unitary p hp0 hp1) _ (tensorLiftCircuit_unitary C hC)
    (normalized_tensorState hψ (normalized_ket _))

/-- The zeroth binomial database moment of a normalized state is one. -/
private theorem databaseMoment_zero (v : QState (((I × Bool) × W) × (I → Bool)))
    (hv : Normalized v) : databaseMoment 0 v = 1 := by
  unfold databaseMoment
  simp only [Nat.choose_zero_right,Nat.cast_one,one_mul]
  have h := hv
  unfold Normalized at h
  rw [Fintype.sum_prod_type] at h
  exact h

/-- For a normalized algorithm state tensored with the empty database, the order-`i` database
moment is `Nat.choose 0 i`. -/
private theorem databaseMoment_empty (ψ : QState ((I × Bool) × W)) (hψ : Normalized ψ)
    (i : ℕ) : databaseMoment i (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket (fun _ => false))) = (Nat.choose 0 i : ℝ) := by
  unfold databaseMoment
  have hd (q : (I × Bool) × W) :
      (∑ d : I → Bool, (Nat.choose (databaseCard d) i : ℝ) *
        ‖TensorState ψ (Qatlib.Foundations.PureStateMath.Ket (fun _ => false)) (q,d)‖^2)
        = (Nat.choose 0 i : ℝ) * ‖ψ q‖^2 := by
    rw [Finset.sum_eq_single (fun _ => false)]
    · simp only [databaseCard_empty,TensorState,ket_self,mul_one]
    · intro d _ hd
      simp [TensorState,Qatlib.Foundations.PureStateMath.Ket,hd]
    · simp
  simp_rw [hd]
  rw [← Finset.mul_sum,hψ,mul_one]

/-- For `p` in [0, 1], a unitary circuit with at most `t` queries started in a normalized state
has order-`i` binomial database moment at most `Nat.choose t i * (2√(p(1 − p)))^i`. -/
theorem database_moment_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (hC : IsUnitaryCircuit C)
    (ψ : QState ((I × Bool) × W)) (hψ : Normalized ψ) (i t : ℕ)
    (ht : QueryCount C ≤ t) :
    (∑ q : (I × Bool) × W, ∑ d : I → Bool,
        (Nat.choose (databaseCard d) i : ℝ) * ‖compressedRunState p C ψ (q,d)‖^2)
      ≤ (Nat.choose t i : ℝ) * (2*Real.sqrt (p*(1-p)))^i := by
  let s := 2*Real.sqrt (p*(1-p))
  have hs : 0 ≤ s := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hmain : ∀ C : Circuit ((I × Bool) × W), IsUnitaryCircuit C → ∀ i : ℕ,
      databaseMoment i (compressedRunState p C ψ) ≤ (Nat.choose (QueryCount C) i : ℝ)*s^i := by
    intro C
    induction C using List.reverseRecOn with
    | nil =>
      intro _ i
      change databaseMoment i
          (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket (fun _ => false))) ≤
          (Nat.choose 0 i : ℝ)*s^i
      rw [databaseMoment_empty ψ hψ]
      cases i <;> simp
    | append_singleton C step ih =>
      intro hvalid i
      obtain ⟨hprefix,hstep⟩ := (isUnitaryCircuit_append C [step]).mp hvalid
      cases step with
      | gate U =>
        have hU : U ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ :=
          hstep U (by simp)
        simp only [compressedRunState,tensorLiftCircuit,List.map_append,List.map_cons,
          List.map_nil,tensorLiftStep,run_append,run_gate,run_nil]
        rw [databaseMoment_gate i U hU]
        simpa only [queryCount_append,queryCount_gate,queryCount_nil,add_zero] using! ih hprefix i
      | query =>
        cases i with
        | zero =>
          rw [databaseMoment_zero _ (compressedRunState_normalized p hp0 hp1 _
            ((isUnitaryCircuit_append C [Step.query]).mpr ⟨hprefix,hstep⟩) ψ hψ)]
          simp
        | succ i =>
          simp only [compressedRunState,tensorLiftCircuit,List.map_append,List.map_cons,
            List.map_nil,tensorLiftStep,run_append,run_query,run_nil]
          change databaseMoment (i+1)
              (ApplyGate (compressedOracle p) (compressedRunState p C ψ)) ≤ _
          calc _ ≤ databaseMoment (i+1) (compressedRunState p C ψ) +
                s * databaseMoment i (compressedRunState p C ψ) :=
              compressed_query_moment_step p hp0 hp1 _ i
            _ ≤ (Nat.choose (QueryCount C) (i+1) : ℝ)*s^(i+1) +
                s*((Nat.choose (QueryCount C) i : ℝ)*s^i) :=
              add_le_add (ih hprefix (i+1)) (mul_le_mul_of_nonneg_left (ih hprefix i) hs)
            _ = _ := by
              simp only [queryCount_append,queryCount_query,queryCount_nil,zero_add,
                Nat.choose_succ_succ',Nat.cast_add,pow_succ]
              ring
  exact (hmain C hC i).trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast Nat.choose_le_choose i ht) (pow_nonneg hs i))

/-- At `p = 0`, the specified entry between two databases differing at an unqueried address is
zero, although the corresponding local `compressedQueryEntry` is one. -/
theorem compressed_oracle_unfiltered_entry_counterexample :
    compressedOracle (I := Bool) (W := Unit) 0
        (((false,true),()),fun _ => false) (((false,true),()),fun k => k) = 0 ∧
      compressedQueryEntry 0 false false = 1 := by
  constructor
  · rw [compressed_oracle_entry 0 (by norm_num) (by norm_num)]
    have h : ¬ (∀ k : Bool, k ≠ false → (false : Bool) = k) := by
      intro h
      simpa using h true (by decide)
    simp only [↓reduceIte,if_neg h]
  · norm_num [compressedQueryEntry]

end Qatlib.Concepts.CompressedQuery.CompressOracle
