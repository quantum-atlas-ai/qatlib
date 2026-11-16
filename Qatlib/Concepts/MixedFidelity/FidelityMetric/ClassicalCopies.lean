/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MixedFidelity.FidelityMetric.ClassicalStates

@[expose] public section


/-! # Independent classical copies and root fidelity

A finite product law on `Fin n → X` is an actual normalized distribution.
Its classical-state fidelity is the nth power of the single-copy coefficient.
This is a statement about classical embeddings, not general mixed tensor powers.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric
open scoped BigOperators
variable {X : Type*} [Fintype X] [DecidableEq X]

/-!
### The sequence law of n independent draws
-/

/-- The joint law of `n` independent draws from `p`, as a distribution on the
sequence type `Fin n → X`: the probability of a sequence `x` is the product
`∏ i, p (x i)`.  This is the distribution-level N-copy model: the joint outcome law
of `n` nonadaptive single-copy observations, with no tensor-power state involved. -/
def seqDist (p : ProbDistribution X) (n : ℕ) : ProbDistribution (Fin n → X) :=
  .mk' (fun x ↦ ∏ i, (p (x i) : ℝ))
    (fun _ ↦ Finset.prod_nonneg fun i _ ↦ Prob.zero_le_coe)
    (by
      have h := Finset.prod_univ_sum (t := fun _ : Fin n ↦ Finset.univ)
        (f := fun _ j ↦ (p j : ℝ))
      rw [Fintype.piFinset_univ] at h
      show ∑ x : Fin n → X, ∏ i, (p (x i) : ℝ) = 1
      rw [← h]
      simp)

omit [DecidableEq X] in
/-- The probability of a sequence under `seqDist` is the product of the per-draw
probabilities (definitional unfolding of the `mk'` construction). -/
@[simp]
theorem seqDist_apply (p : ProbDistribution X) (n : ℕ) (x : Fin n → X) :
    (seqDist p n x : ℝ) = ∏ i, (p (x i) : ℝ) :=
  rfl

omit [DecidableEq X] in
/-- Normalization of the sequence law, stated standalone: summing the product
`∏ i, p (x i)` over all sequences gives `1`, because the sum factorizes
(`Finset.prod_univ_sum`) and each factor is a normalized distribution. -/
theorem seqDist_sum_eq_one (p : ProbDistribution X) (n : ℕ) :
    ∑ x : Fin n → X, ∏ i, (p (x i) : ℝ) = 1 := by
  simpa [seqDist_apply] using (seqDist p n).normalized

omit [DecidableEq X] in
/-- The empty sequence has probability one: the degenerate base case of the product
law. -/
theorem seqDist_zero_apply (p : ProbDistribution X) (x : Fin 0 → X) :
    (seqDist p 0 x : ℝ) = 1 := by
  simp [seqDist_apply]

omit [DecidableEq X] in
/-- Product decomposition of the sequence law: the law of `n + 1` draws splits into
the law of the first `n` draws (the prefix, embedded by `Fin.castSucc`) times the
fresh last draw — the recursion that makes `seqDist` an honest product law. -/
theorem seqDist_succ_apply (p : ProbDistribution X) (n : ℕ) (x : Fin (n + 1) → X) :
    (seqDist p (n + 1) x : ℝ)
      = (seqDist p n (x ∘ Fin.castSucc) : ℝ) * (p (x (Fin.last n)) : ℝ) := by
  simp only [seqDist_apply, Function.comp_apply, Fin.prod_univ_castSucc]

omit [DecidableEq X] in
/-- At one copy the sequence law is the original distribution read at the single
coordinate: the N-copy model degenerates to the one-copy model of `Basic.lean`. -/
theorem seqDist_one_apply (p : ProbDistribution X) (x : Fin 1 → X) :
    (seqDist p 1 x : ℝ) = (p (x 0) : ℝ) := by
  simp [seqDist_apply]

omit [DecidableEq X] in
/-- **Bhattacharyya product law.**  The Bhattacharyya coefficient of the sequence
laws `p^n`, `q^n` is exactly the `n`-th power of the one-copy coefficient: entrywise
`√(p·q)` products factorize under the same product–sum exchange as normalization
(`Finset.prod_univ_sum`, then `Fin.prod_const`). -/
theorem bhattacharyya_seqDist_eq_pow (p q : ProbDistribution X) (n : ℕ) :
    (∑ x : Fin n → X, ∏ i, Real.sqrt ((p (x i) : ℝ) * (q (x i) : ℝ)))
      = (∑ z, Real.sqrt ((p z : ℝ) * (q z : ℝ))) ^ n := by
  have h := Finset.prod_univ_sum (t := fun _ : Fin n ↦ Finset.univ)
    (f := fun _ j ↦ Real.sqrt ((p j : ℝ) * (q j : ℝ)))
  rw [Fintype.piFinset_univ] at h
  rw [← h, Fin.prod_const]

/-- **Fidelity decay of N classical copies.**  Through the classical Bhattacharyya
connection (instantiated at the sequence type `Fin n → X`), the root fidelity of the
embedded classical N-copy states is exactly `B(p, q)^n`: geometric decay at rate
equal to the one-copy Bhattacharyya coefficient.  Classical hard families (`B` close
to `1`) thus remain hard at every N in exactly the same exponential way, which is
the quantitative seed for the card's mixed-likelihood route. -/
theorem fidelity_ofClassical_seqDist (p q : ProbDistribution X) (n : ℕ) :
    MState.fidelity (MState.ofClassical (seqDist p n)) (MState.ofClassical (seqDist q n))
      = (∑ z, Real.sqrt ((p z : ℝ) * (q z : ℝ))) ^ n := by
  rw [fidelity_ofClassical_eq_bhattacharyya]
  simp only [seqDist_apply]
  rw [← bhattacharyya_seqDist_eq_pow]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← Finset.prod_mul_distrib,
    Real.sqrt_prod _ fun i _ ↦ mul_nonneg (Prob.zero_le_coe (p := p (x i))) (Prob.zero_le_coe (p := q (x i)))]

end Qatlib.Concepts.MixedFidelity.FidelityMetric
