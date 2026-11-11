/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExpSpeedup10.MainResults.Model.SourceDesign

set_option backward.isDefEq.respectTransparency false

/-!
# ExpSpeedup10 — complexity and design-law source model

Brandão–Horodecki, *Exponential Quantum Speed-ups are Generic*,
fixed arXiv:1010.3654**v2** (16 Apr 2013).

This file records the complexity-theoretic and design-law objects used by
Theorems I–VI, Proposition II.1, Lemma III.1 and Proposition IV.3:

* `sourceQuantumQueryCost` — the explicit quantum algorithm of Section II A
  (query `f`, apply `U`, query `g`): four queries.
* `sourcePostselectedLowerBound` — the Section IV lower bound `2^{C(U)/7}`
  on the postselected classical query complexity (proof of Theorem I).
* `sourceIndependentQueryLowerBound` / `sourceIndependentQueryUpperBound` —
  the two sides of Theorem V in the independent query model.
* `sourceSparseQueryBound` — the polynomial query bound of Section V
  (Van den Nest simulation) used in Theorem VI.
* `SourceDesignEnsembleOn` — a probability law on `d × d` unitaries together
  with its twirl residual, i.e. the Def. II.4 ensemble used in Lemma III.1
  and Theorem II(ii).
* `IsAlmostKWiseIndependent` (already in `SourceDesign`) and the concrete
  Gaussian mass `sourceCorrelatedMass` of `SourceCore` are the objects of
  Proposition IV.3.

Boundary: definitions only; the per-claim statements live in their own files.
-/

set_option autoImplicit false
noncomputable section

open Matrix BigOperators
open scoped Classical

namespace Qatlib.Papers.ExpSpeedup10.MainResults
namespace Model

/-- The explicit quantum algorithm for `U`-circuit checking of Section II A
(initialise `|+⟩^{⊗n}`, query `f`, apply `U`, query `g`, Hadamard-measure)
uses four oracle queries. -/
def sourceQuantumQueryCost : ℕ := 4

/-- Section IV (proof of Theorem I): Proposition IV.3 together with
Proposition IV.1 yields the lower bound `2^{C(U)/7}` on the postselected
classical query complexity of `U`-circuit checking. -/
noncomputable def sourcePostselectedLowerBound {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (2 : ℝ) ^ (sourceC U / 7)

/-- Section V (Theorem V, lower side): the postselected lower bound is also a
lower bound for the independent-query randomized classical complexity. -/
noncomputable def sourceIndependentQueryLowerBound {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (2 : ℝ) ^ (sourceC U / 7)

/-- Section V (Theorem V, upper side): the estimator
`E_N = (1/N) ∑ᵣ fᵣ(i) gᵣ(j)` with `N = ⌈4·2^{C(U)} log(1/ε)⌉` independent
oracle realisations decides `U`-circuit checking with failure probability at
most `ε`.  Recorded as the explicit query budget. -/
noncomputable def sourceIndependentQueryUpperBound {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (ε : ℝ) : ℝ :=
  (2 : ℝ) ^ (sourceC U + 2) * Real.log (1 / ε)

/-- Section V (proof of Theorem VI): Van den Nest's simulation gives a
classical algorithm with a polynomial number of oracle queries.  A concrete
polynomial witness in the dimension `n` of the qubit register and the row
sparsity `s`. -/
noncomputable def sourceSparseQueryBound (n s : ℕ) : ℝ :=
  ((s : ℝ) + 1) * ((n : ℝ) + 1) ^ 2

/-- A probability law on `d × d` unitaries together with its twirl residual
(Def. II.4).  The law is supported on the finite index set `ι`, `unit i` is the
`i`-th unitary and `prob i` its mass; `residual` is the 2→2 norm of
`G_{μ,t} − G_{H,t}` (Eq. (15)-(17)). -/
structure SourceDesignEnsembleOn (ι : Type*) [Fintype ι] (d t : ℕ) where
  unit : ι → Matrix (Fin d) (Fin d) ℂ
  prob : ι → ℝ
  prob_nonneg : ∀ i, 0 ≤ prob i
  total_prob : ∑ i, prob i = 1
  residual : ℝ

/-- A `2^{-3tn}`-approximate unitary `t`-design on `n` qubits: a
`SourceDesignEnsembleOn ι (2^n) t` whose residual is at most `2^{-3tn}`. -/
def IsThreeTnApproximateDesign (ι : Type*) [Fintype ι] (n t : ℕ)
    (E : SourceDesignEnsembleOn ι (2 ^ n) t) : Prop :=
  E.residual ≤ (2 : ℝ) ^ (-(3 * (t : ℝ) * (n : ℝ)))

end Model
end Qatlib.Papers.ExpSpeedup10.MainResults
