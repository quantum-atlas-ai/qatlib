/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolEvalTree11.MainResults.ScaledCore
public import Qatlib.Papers.BoolEvalTree11.MainResults.ClassicalAudit

@[expose] public section


/-! # Entire old tree-bound interfaces need their missing source couplings

The old tree structure lets its trivial flags ignore witness size. An actual
half-column program then gives cost n^2*4^n on trees declared zero-fault.
The old hard-base predicate is only existence of a tree, not a hard probability
law or a decision-tree computation. Neither counterexample refutes the source.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolEvalTree11.MainResults.TreeAudit
open Models ScaledCore ClassicalAudit

/-- A consistent all-one unary tree whose old labels call every node trivial. -/
def markedTree (n : ℕ) : FaultTree 1 n where
  input := fun _ _ _ => true
  isTrivial := fun _ _ => true
  isStrong := fun _ _ _ => true
  kappa := fun _ _ => 0
  strong_exists := by intro l h; exact ⟨0,rfl⟩
  kappa_leaf := by intro h; rfl
  kappa_step := by intro l hl h; simp

/-- Every literal old fault count is zero in the marked tree. -/
theorem zeroFault (n : ℕ) : (markedTree n).KFault 0 := by
  intro l h
  exact le_refl _

/-- Its old hard-base predicate accepts even a single depth-zero leaf. -/
theorem leafBase : HasHardBaseDistributions 1 0 0 := ⟨markedTree 0,zeroFault 0⟩

/-- Every actual path product is exponential despite those trivial flags. -/
theorem pathValue (n : ℕ) (p : Fin n→Fin 1) :
    pathProduct (scaled (1/2)) bit (markedTree n) p=(4:ℝ)^n := by
  have hh : (scaled (1/2)).witnessSize bit (fun _ => true)=4 := by
    simpa using halfCosts (fun _ => true)
  simp only [pathProduct,markedTree,hh,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- The supremum is over a nonempty set of genuine strong paths. -/
theorem maxValue (n : ℕ) :
    strongPathMaxProduct (scaled (1/2)) bit (markedTree n)=(4:ℝ)^n := by
  have : Nonempty {p : Fin n→Fin 1 // (markedTree n).StrongPath p} :=
    ⟨⟨fun _ => 0,by intro l; rfl⟩⟩
  have he : (fun p : {p : Fin n→Fin 1 // (markedTree n).StrongPath p} =>
      pathProduct (scaled (1/2)) bit (markedTree n) p.val)=fun _ => (4:ℝ)^n := by
    funext p
    exact pathValue n p.val
  unfold strongPathMaxProduct
  rw [he,Set.range_const,csSup_singleton]

/-- The literal proxy query count grows exponentially on these zero-fault trees. -/
theorem queryValue (n : ℕ) : treeQueryCount (scaled (1/2)) bit (markedTree n)=
    (n:ℝ)^2*(4:ℝ)^n := by
  unfold treeQueryCount
  rw [maxValue]

/-- The elementary exponential lower bound needed for every candidate constant. -/
theorem powDepth (n : ℕ) : (n:ℝ)+1≤(4:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    push_cast
    nlinarith [(Nat.cast_nonneg n : (0:ℝ)≤n)]

/-- The complete original quantum proxy upper-bound target is false. -/
theorem upperFalse :
    ¬(∀ {c : ℕ} (sp : DirectSpanProgram c) (f : (Fin c→Bool)→Bool)
      (_hrep : sp.Represents f) (ω : ℝ) (_hωpos : 0<ω)
      (_hω : ∀ x : Fin c→Bool, sp.witnessSize f x≤ω),
      ∃ C : ℝ, 0<C ∧ ∀ (n k : ℕ) (T : FaultTree c n), T.KFault k →
        treeQueryCount sp f T≤C*(n:ℝ)^2*ω^k) := by
  intro h
  obtain ⟨C,_hC,hb⟩ := h (scaled (1/2)) bit (represents (1/2) (by norm_num))
    4 (by norm_num) (by intro x; rw [halfCosts]; split <;> norm_num)
  obtain ⟨n,hn⟩ := exists_nat_gt (max C 1)
  have hcn : C<(n:ℝ) := lt_of_le_of_lt (le_max_left C 1) hn
  have hnp : (0:ℝ)<n := by linarith [le_max_right C 1]
  have hq := hb n 0 (markedTree n) (zeroFault n)
  rw [queryValue] at hq
  simp only [pow_zero,mul_one] at hq
  have hp : (4:ℝ)^n≤C := (mul_le_mul_iff_right₀ (sq_pos_of_pos hnp)).mp
    (by simpa only [mul_comm] using hq)
  linarith [powDepth n]

/-- The whole original hard-distribution theorem fails on the old free-cost record. -/
theorem hardFalse :
    ¬(∀ {c : ℕ} (sp : DirectSpanProgram c) (f : (Fin c→Bool)→Bool)
      (_hrep : sp.Represents f) (_hnc : ¬DirectSpanProgram.IsConstant f)
      (k₀ n₀ : ℕ) (_hbase : HasHardBaseDistributions c k₀ n₀)
      (k n : ℕ) (_hk : 1≤k) (_hn : n₀<n)
      (_hpolylog : (k:ℝ)<(Real.log (n:ℝ))^2)
      (β : ℕ) (_hβ : 1≤β)
      (_hβlo : (β:ℝ)≤Real.log ((n:ℝ)-(n₀:ℝ))/10)
      (_hβhi : Real.log ((n:ℝ)-(n₀:ℝ))/10<(β:ℝ)+1)
      (A : ClassicalTreeAlgorithm) (_hcorrect : (2:ℝ)/3≤A.successProb),
      (β:ℝ)^k≤A.expectedQueriesOnHard) := by
  intro h
  have hh := h (scaled (1/2)) bit (represents (1/2) (by norm_num)) nonconstant
    0 0 leafBase 1 sampleDepth (by norm_num) (by norm_num [sampleDepth])
    (by simp only [Nat.cast_one]
        nlinarith [logRange.1,sq_nonneg (Real.log (sampleDepth:ℝ)-1)])
    1 (by norm_num) (by simp only [Nat.cast_zero,sub_zero,Nat.cast_one]; linarith [logRange.1])
    (by simp only [Nat.cast_zero,sub_zero,Nat.cast_one]; linarith [logRange.2]) freeRecord (by norm_num [freeRecord])
  norm_num [freeRecord] at hh

end Qatlib.Papers.BoolEvalTree11.MainResults.TreeAudit
