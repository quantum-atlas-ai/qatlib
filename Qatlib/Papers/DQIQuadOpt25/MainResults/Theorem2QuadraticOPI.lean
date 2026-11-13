/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DQIQuadOpt25.MainResults.Theorem1StatePrep
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# DQIQuadOpt25 — Theorem 2 (quadratic OPI as max-QUADSAT)

Fixed arXiv:2510.08061v2, Theorem 2, p.4; Definitions 3–4, p.4; proof,
pp.10–11.

The paper proves: quadratic OPI (Definition 4: OPI with the coefficients of the
optimal polynomial required to be quadratic residues) is a special case of
max-QUADSAT, and the corresponding DQI state is efficiently prepared by
Algorithm 1 with `ℓ = ⌊(n+1)/2⌋`.

The proof embeds an OPI instance into a max-QUADSAT instance as follows: for a
primitive root `γ` of `F_p`, set

* `(C_i)_{jj} = γ^{i·j}` (`i = 0, …, p−2`, `j = 0, …, n−1`), all `b_i = 0`;
* `f_i(x) = +1` if `x ∈ F_{γ^i}` and `−1` otherwise.

Then `qᵀ C_i q = ∑_j γ^{ij} q_j² = Q*(γ^i)`, where `Q*` is the polynomial whose
coefficients are `q_j²`, so the max-QUADSAT objective verifies
`f_QUADSAT(q) = 2·f_OPI(Q*) − (p−1)`.  Finally the Reed–Solomon code of
distance `n+1` satisfies the hypotheses of Theorem 1 with `ℓ = ⌊(n+1)/2⌋`.

Formalisation scope.

* The embedding and the two algebraic identities (`qᵀ C_i q = Q*(γ^i)` and
  `f_QUADSAT = 2·f_OPI − (p−1)`) are proved here, by direct proofs.
* The reduction hypothesis — that the diagonal matrix family has an efficient
  decoder with parameter `ℓ = ⌊(n+1)/2⌋` — is an explicit hypothesis
  `hdec : HasEfficientDecoder …`, exactly the condition used by Theorem 1.
  The paper justifies it by the Reed–Solomon code of distance `n+1`.
* The preparation conclusion is the explicit hypothesis `hprep`, returned
  unchanged. The statement-only preparation definition is not used as a proof.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.DQIQuadOpt25.MainResults

open Qatlib.Papers.DQIQuadOpt25.MainResults.Source

/-- A quadratic-OPI instance (Definitions 3–4): a primitive root `γ` and the
target subsets `F_{γ^i}` for `i = 0, …, p−2`.  A feasible solution is a
coefficient vector `q : Fin n → F_p`; the polynomial it defines is
`Q*(y) = ∑_j q_j² y^j` (the paper's quadratic-residue requirement). -/
structure QuadraticOPI (p n : ℕ) where
  /-- A primitive root `γ` of `F_p`. -/
  gamma : ZMod p
  /-- The target subsets `F_{γ^i}` for `i = 0, …, p−2`. -/
  code : Fin (p - 1) → Finset (ZMod p)

/-- The polynomial `Q*(γ^i) = ∑_j q_j² γ^{ij}` defined by a coefficient vector
`q` (proof of Theorem 2, p.10). -/
def quadraticOPIValue {p n : ℕ} (inst : QuadraticOPI p n)
    (q : Fin n → ZMod p) (i : Fin (p - 1)) : ZMod p :=
  ∑ j, q j ^ 2 * inst.gamma ^ (i.val * j.val)

/-- The OPI objective `f_OPI(Q*) = #{i : Q*(γ^i) ∈ F_{γ^i}}` (Definition 3). -/
def quadraticOPIScore {p n : ℕ} (inst : QuadraticOPI p n) (q : Fin n → ZMod p) : ℕ :=
  (Finset.univ.filter fun i => quadraticOPIValue inst q i ∈ inst.code i).card

/-- The quadratic-OPI objective in `±1` form, `∑_i f_i(Q*(γ^i))`. -/
def quadraticOPIObjective {p n : ℕ} (inst : QuadraticOPI p n)
    (q : Fin n → ZMod p) : ℤ :=
  ∑ i, if quadraticOPIValue inst q i ∈ inst.code i then 1 else -1

/-- The quadratic-OPI → max-QUADSAT embedding of the proof of Theorem 2
(p.10): `(C_i)_{jj} = γ^{ij}`, `b_i = 0`, and the constraint function is the
indicator of `F_{γ^i}`. -/
def quadraticOPIAsQUADSAT {p n : ℕ} (inst : QuadraticOPI p n) :
    QUADSATInstance p n (p - 1) where
  f i x := if x ∈ inst.code i then 1 else -1
  b _ _ := 0
  C i := Matrix.diagonal (fun j => inst.gamma ^ (i.val * j.val))

/-- The embedding is a diagonal instance with no linear terms. -/
theorem quadraticOPIAsQUADSAT_isDiagonal {p n : ℕ} (inst : QuadraticOPI p n) :
    IsDiagonalInstance (quadraticOPIAsQUADSAT inst) := by
  refine ⟨fun i j => rfl, fun i j k hjk => ?_⟩
  exact Matrix.diagonal_apply_ne (fun j => inst.gamma ^ (i.val * j.val)) hjk

/-- The constraint argument of the embedded instance is `Q*(γ^i)`
(proof of Theorem 2, p.10: `qᵀC_iq = ∑_j γ^{ij} q_j²`). -/
theorem quadraticOPI_constraintArg {p n : ℕ} (inst : QuadraticOPI p n)
    (q : Fin n → ZMod p) (i : Fin (p - 1)) :
    constraintArg (quadraticOPIAsQUADSAT inst) q i = quadraticOPIValue inst q i := by
  rw [constraintArg_diagonal _ (quadraticOPIAsQUADSAT_isDiagonal inst)]
  unfold quadraticOPIValue
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [quadraticOPIAsQUADSAT, Matrix.diagonal_apply_eq]
  ring

/-- The number of satisfied constraints of the embedded instance equals the
quadratic-OPI score. -/
theorem quadraticOPI_satCount {p n : ℕ} (inst : QuadraticOPI p n)
    (q : Fin n → ZMod p) :
    satCount (quadraticOPIAsQUADSAT inst) q = quadraticOPIScore inst q := by
  unfold satCount quadraticOPIScore
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [quadraticOPI_constraintArg]
  by_cases h : quadraticOPIValue inst q i ∈ inst.code i <;>
    simp [quadraticOPIAsQUADSAT, h]

/-- **Special-case identity of Theorem 2 (p.10).**  The max-QUADSAT objective
of the embedded instance is `2·f_OPI(Q*) − (p−1)`: the embedding maximises
exactly the OPI objective (with coefficients the squares of `q`). -/
theorem quadraticOPI_objective {p n : ℕ} (inst : QuadraticOPI p n)
    (q : Fin n → ZMod p) :
    objective (quadraticOPIAsQUADSAT inst) q
      = 2 * (quadraticOPIScore inst q : ℤ) - ((p - 1 : ℕ) : ℤ) := by
  rw [objective_eq_two_satCount_sub _ (fun i y => by
    simp only [quadraticOPIAsQUADSAT]
    split_ifs <;> simp), quadraticOPI_satCount]

/-- **Theorem 2 of arXiv:2510.08061v2 (p.4).**

Quadratic OPI is a special case of max-QUADSAT: the embedding
`quadraticOPIAsQUADSAT` is diagonal with no linear terms and its objective is
`2·f_OPI(Q*) − (p−1)`.  Moreover, when the embedded diagonal family has the
efficient decoder required by Theorem 1 at degree `ℓ = ⌊(n+1)/2⌋`, the
preparation contract is returned only under the separate `hprep` hypothesis.
It counts explicit two-level operations; no Algorithm 1 circuit is derived.

The decoder hypothesis is the formal counterpart of the paper's statement that
"all conditions of Theorem 1 hold, with the code being a Reed–Solomon code of
distance `n+1`" (pp.10–11); the Reed–Solomon decoding construction itself is
not instantiated here.  The state-preparation conclusion is consumed as the
explicit hypothesis `hprep`, because the paper's Theorem 1/Algorithm 1 Step 7
is acknowledged to be flawed; the embedding and objective identity below are
proved unconditionally. -/
theorem theorem2_quadraticOPI
    {p n : ℕ} [Fact p.Prime] (inst : QuadraticOPI p n)
    (hdec : HasEfficientDecoder (m := p - 1) (n := n) (ℓ := (n + 1) / 2)
      (diagVector (quadraticOPIAsQUADSAT inst)))
    (P : Polynomial ℂ) (hdeg : P.natDegree ≤ (n + 1) / 2)
    (hprep : ∃ c : ℕ, PreparesIn (dqiAmplitude (quadraticOPIAsQUADSAT inst) P)
      (((p - 1) + n + p) ^ c + 1)) :
    IsDiagonalInstance (quadraticOPIAsQUADSAT inst) ∧
    (∀ q : Fin n → ZMod p,
      objective (quadraticOPIAsQUADSAT inst) q
        = 2 * (quadraticOPIScore inst q : ℤ) - ((p - 1 : ℕ) : ℤ)) ∧
    (∃ c : ℕ, PreparesIn (dqiAmplitude (quadraticOPIAsQUADSAT inst) P)
      (((p - 1) + n + p) ^ c + 1)) := by
  exact ⟨quadraticOPIAsQUADSAT_isDiagonal inst,
    fun q => quadraticOPI_objective inst q, hprep⟩

end Qatlib.Papers.DQIQuadOpt25.MainResults
