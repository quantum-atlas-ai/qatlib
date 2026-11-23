module

public import Qatlib.Papers.QAOASupremacy16.ClauseGates.ClauseSum
public import Qatlib.Papers.QAOASupremacy16.ClauseGates.RepeatedGadget
public import Qatlib.Papers.QAOASupremacy16.Expectation.LocalMarginal

@[expose] public section

/-!
# Consumer regression for the QAOASupremacy16 clause-cost increment

This ordinary-module consumer specializes the new clause-cost results to concrete non-degenerate
instances:

* a two-clause CSP on a two-bit register in which one clause is the first bit and the other is its
  negation has cost exactly one on every string, and the uniform bound is positive;
* the one-edge MAX-CUT instance on two vertices has cut count at most one, its complement
  invariance holds, some string cuts the edge, and the Ising identity specializes to one edge;
* the constant cost three on a one-qubit register has a Hermitian cost operator of L2 operator
  norm three, and the EuclideanSpace norm bound holds;
* three repeated `01` gadget layers have effective cost eighteen, the printed clause count of a
  single gadget is eight while its maximal effective cost is six, and a two-layer word is one
  exponential at total cost eight;
* the two-outcome fiber identity, the one-qubit clause decomposition, the normalized marginal
  total and the uniform expected-cost bound hold on concrete probability weights.
-/

set_option autoImplicit false

namespace QatlibTests.QAOASupremacy16ClauseCostRegression

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QAOASupremacy16.LocalGadget
open Qatlib.Papers.QAOASupremacy16.ClauseGates
open Qatlib.Papers.QAOASupremacy16.Expectation
open MaxCutInstance Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-! ## A concrete two-clause CSP -/

/-- Two clauses on a two-bit register: the first bit and its negation. -/
def twoClauses : CspInstance 2 Bool where
  clause a z := match a with
    | false => z 0
    | true => !z 0

/-- The two opposite clauses are satisfied exactly once on every string. -/
theorem twoClauses_totalCost_eq_one (z : Reg 2) : twoClauses.totalCost z = 1 := by
  unfold CspInstance.totalCost CspInstance.clauseValue
  rw [Fintype.sum_bool]
  cases h : z 0 <;> simp [twoClauses, h]

/-- The concrete instance has the positive uniform bound supplied by the general theorem. -/
theorem twoClauses_uniform_bound :
    ∃ m : ℕ, 0 < m ∧ ∀ z : Reg 2, twoClauses.totalCost z ≤ m :=
  twoClauses.exists_uniform_totalCost_bound

/-- The concrete cost is at most two. -/
theorem twoClauses_cost_le_two (z : Reg 2) : twoClauses.totalCost z ≤ 2 := by
  rw [twoClauses_totalCost_eq_one]
  norm_num

/-! ## The one-edge MAX-CUT instance on two vertices -/

/-- The MAX-CUT instance with the single edge joining the two vertices. -/
def oneEdge : MaxCutInstance 2 Unit where
  fst _ := 0
  snd _ := 1
  loopless _ := by decide
  edge_injective := by
    intro a b _
    exact Subsingleton.elim a b

/-- The one-edge cut count is at most one. -/
theorem oneEdge_cutCost_le_one (z : Reg 2) : oneEdge.cutCost z ≤ 1 :=
  oneEdge.cutCost_le_card z

/-- The one-edge cut count is complement invariant. -/
theorem oneEdge_cutCost_compl (z : Reg 2) :
    oneEdge.cutCost (registerCompl z) = oneEdge.cutCost z :=
  oneEdge.cutCost_compl z

/-- Some string cuts the single edge. -/
theorem oneEdge_exists_pos : ∃ z : Reg 2, 0 < oneEdge.cutCost z :=
  oneEdge.exists_pos_cutCost

/-- The Ising form for the one-edge instance. -/
theorem oneEdge_ising (z : Reg 2) :
    (2 : ℤ) * (oneEdge.cutCost z : ℤ)
      = 1 - spinBit z (0 : Fin 2) * spinBit z (1 : Fin 2) := by
  have h := oneEdge.two_mul_cutCost_eq_ising z
  simpa [oneEdge] using h

/-- The indicator string of the first vertex cuts the edge. -/
theorem oneEdge_indicator_cut :
    oneEdge.cutCost (fun i : Fin 2 => decide (i = 0)) = 1 := by
  decide

/-! ## The diagonal cost operator on one qubit -/

/-- The constant cost three on a one-qubit register. -/
def costThree : Reg 1 → ℕ :=
  fun _ => 3

/-- The cost operator of the constant cost is Hermitian. -/
theorem costThree_isHermitian : (costOperator costThree).IsHermitian :=
  costOperator_isHermitian costThree

/-- Its L2 operator norm is three. -/
theorem costThree_l2_opNorm : ‖costOperator costThree‖ = 3 := by
  rw [costOperator_l2_opNorm]
  rw [show (fun z : Reg 1 => (costThree z : ℂ)) = fun _ => (3 : ℂ) from rfl]
  simp

/-- The true EuclideanSpace norm bound for the constant cost operator. -/
theorem costThree_mulVec_norm_le (ψ : EuclideanSpace ℂ (Reg 1)) :
    ‖(EuclideanSpace.equiv (Reg 1) ℂ).symm ((costOperator costThree) *ᵥ ψ)‖
      ≤ 3 * ‖ψ‖ := by
  have h := costOperator_mulVec_norm_le costThree ψ
  simpa [costThree, pi_norm_const'] using h

/-- The diagonal action multiplies the amplitude by three. -/
theorem costThree_apply (ψ : Reg 1 → ℂ) (z : Reg 1) :
    (costOperator costThree).mulVec ψ z = 3 * ψ z := by
  rw [costOperator_mulVec_apply]
  simp [costThree]

/-! ## Repeated local gadget layers -/

/-- Three repeated `01` layers satisfy the uniform cost bound. -/
theorem three_layers_cost_bound :
    (∑ _i : Fin 3, gadgetCost (false, true).1 (false, true).2) ≤ 6 * 3 :=
  repeatedFinCost_le 3 fun _ => (false, true)

/-- A positive uniform per-layer bound applies to every three-layer word. -/
theorem three_layers_uniform_bound :
    ∃ K : ℕ, 0 < K ∧ ∀ layers : Fin 3 → Bool × Bool,
      (∑ i, gadgetCost (layers i).1 (layers i).2) ≤ K * 3 := by
  obtain ⟨K, hK, h⟩ := exists_uniform_repeated_gadget_cost
  exact ⟨K, hK, h 3 (by decide)⟩

/-- Three repeated `01` layers have effective cost eighteen. -/
theorem three_layers_cost_eq :
    (∑ _i : Fin 3, gadgetCost (false, true).1 (false, true).2) = 18 := by
  rw [repeatedFinCost_zeroOne_attained]

/-- The `01` clause has six copies, the `11` clause has two, and the printed count is eight. -/
theorem clause_copy_accounting :
    gadgetCost false true = 6 ∧ gadgetCost true true = 2 ∧ printedClauseCopies = 8 :=
  ⟨rfl, rfl, rfl⟩

/-- The maximal effective cost six stays below the printed clause count eight. -/
theorem effective_below_printed : gadgetCost false true < printedClauseCopies :=
  gadgetCost_lt_printedClauseCopies false true

/-- The `01` and `11` layers contribute six plus two to the total cost. -/
theorem repeatedCost_pair : repeatedCost [(false, true), (true, true)] = 8 := by
  decide

/-- A two-layer `01`, `11` word is one exponential at total cost eight. -/
theorem repeatedDiag_two_layers :
    repeatedDiag [(false, true), (true, true)]
      = Complex.exp (-((Real.pi / 4) * (8 : ℝ)) * Complex.I) := by
  rw [repeatedDiag_eq_exp, repeatedCost_pair]
  norm_num

/-! ## Local marginals and the expected cost -/

/-- The fiber decomposition on the two-point sample space. -/
theorem two_outcome_fiber_identity :
    (∑ x : Bool, (1 / 2 : ℝ) * (if x = true then 1 else 0))
      = ∑ y : Bool,
          (∑ _x ∈ Finset.univ.filter (fun x : Bool => x = y), (1 / 2 : ℝ)) *
            (if y = true then 1 else 0) :=
  sum_mul_comp_fiberwise (p := fun _ => (1 / 2 : ℝ))
    (q := fun b => if b = true then 1 else 0) (g := id)

/-- The same two-point average equals one half. -/
theorem two_outcome_average :
    (∑ x : Bool, (1 / 2 : ℝ) * (if x = true then 1 else 0)) = 1 / 2 := by
  rw [Fintype.sum_bool]
  norm_num

/-- The single-coordinate support underlying the one-qubit examples. -/
abbrev oneSupport : Finset (Fin 1) := Finset.univ

/-- A one-qubit clause reading the only bit. -/
def oneBitClause (w : oneSupport → Bool) : Bool :=
  w ⟨0, by simp⟩

/-- The clause decomposition on a one-qubit register with the two-point uniform weight. -/
theorem oneBit_localCost_identity :
    (∑ z : Reg 1,
        (1 / 2 : ℝ) * localCost (fun _ : Bool => Finset.univ) (fun _ => oneBitClause) z)
      = ∑ _a : Bool,
          ∑ w : oneSupport → Bool,
            marginal (fun _ => (1 / 2 : ℝ)) Finset.univ w *
              (if oneBitClause w = true then 1 else 0) :=
  expectation_localCost_eq_sum_marginals (fun _ => (1 / 2 : ℝ))
    (fun _ : Bool => Finset.univ) (fun _ => oneBitClause)

/-- The uniform weight on a one-qubit register has total mass one. -/
theorem oneQubit_uniform_mass : (∑ _z : Reg 1, (1 / 2 : ℝ)) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Qatlib.Foundations.PureStateMath.card_reg]
  norm_num

/-- The marginals of the one-qubit uniform weight sum to one. -/
theorem oneQubit_marginal_total :
    (∑ w : oneSupport → Bool,
      marginal (fun _ => (1 / 2 : ℝ)) Finset.univ w) = 1 :=
  sum_marginal_eq_one (fun _ => (1 / 2 : ℝ)) oneQubit_uniform_mass Finset.univ

/-- The uniform expected-cost bound for the one-qubit clause. -/
theorem oneBit_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Reg 1 → ℝ), (∀ z, 0 ≤ p z) → (∑ z, p z = 1) →
      ∑ z, p z * localCost (fun _ : Bool => Finset.univ) (fun _ => oneBitClause) z ≤ C :=
  exists_uniform_expectedCost_bound (fun _ : Bool => Finset.univ) (fun _ => oneBitClause)

end QatlibTests.QAOASupremacy16ClauseCostRegression
