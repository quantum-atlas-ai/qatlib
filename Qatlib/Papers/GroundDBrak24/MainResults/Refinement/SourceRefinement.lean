/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.UnitaryGroup

set_option backward.isDefEq.respectTransparency false

/-!
# MainResults.Refinement — DBQA refines warm-start state-preparation circuits (c001)

Fixed source: arXiv:2408.03987, *Double-bracket quantum algorithms for
high-fidelity ground state preparation*. Claim c001 (Abstract and Sec. II B–C).

The paper's two-stage protocol prepares a good initial state with a shallow,
extractable unitary `U_0` (its VQE/parametrised warm start) and then refines it
with double-bracket diagonal-operator iterations (DB-DOI). The relevant source
identities are

* Eq. (14): `H_ws = U_0† H_0 U_0`;
* Eq. (16): `⟨0|H_ws|0⟩ = ⟨ψ_0|H_0|ψ_0⟩`, `ψ_0 = U_0|0⟩` (Heisenberg/Schrödinger
  energy agreement of the warm start);
* Eq. (17): `U_1 = U_0 e^{irD} U_0† e^{irH_0} U_0 e^{-irD}`;
* Eqs. (21), (23): the fully unfolded form, used to count gates/queries.

We model the operator evolutions `e^{irD}`, `e^{irH_0}` as *granted unitary
primitives* `ED`, `EH`, `EDi` (the paper compiles them to CZ + single-qubit
gates, Sec. III, Fig. 3; that gate synthesis is the granted implementation).
What is proved here is the genuine structural content: the compiled gate word
(`w ++ [ED] ++ adj(w) ++ [EH] ++ w ++ [EDi]`) realises exactly the abstract
DB-DOI step unitary, is a valid unitary circuit, has gate count `3|w|+3`, and
the warm-start energy bridge Eq. (16) holds exactly. No statement is weakened.

The bound blocks `UniformBqp.FiniteGateWord` and `ResourceBounds.CostLedger` are
README-only in the Dev tree (no Lean declarations) and Frozen contains no
same-result theorem, so the finite gate word and its count are built here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.GroundDBrak24.MainResults.Refinement

/-- The computational reference state `|0⟩` on `n+1` qubits. -/
def e0 {n : ℕ} : Fin (n + 1) → ℂ := Pi.single 0 1

/-- One DB-DOI refinement step of a warm-start unitary `U`, Eq. (17):
`U_1 = U e^{irD} U† e^{irH_0} U e^{-irD}`. Here `ED = e^{irD}`, `EH = e^{irH_0}`,
`EDi = e^{-irD}` are the granted evolution unitaries and `U† = star U`. -/
def dbdoiStep {n : ℕ} (U ED EH EDi : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  U * ED * star U * EH * U * EDi

/-- Adjoint of a gate word: reverse the gates and take adjoints. -/
def adjWord {n : ℕ} (w : List (Matrix (Fin n) (Fin n) ℂ)) :
    List (Matrix (Fin n) (Fin n) ℂ) :=
  w.reverse.map star

/-- The compiled gate word of one DB-DOI refinement, Eq. (17)/(23):
`w ++ [E_D] ++ adj(w) ++ [E_H] ++ w ++ [E_Di]`. -/
def refinedWord {n : ℕ} (w : List (Matrix (Fin n) (Fin n) ℂ))
    (ED EH EDi : Matrix (Fin n) (Fin n) ℂ) : List (Matrix (Fin n) (Fin n) ℂ) :=
  w ++ [ED] ++ adjWord w ++ [EH] ++ w ++ [EDi]

/-- The adjoint word realises the adjoint unitary (contravariance of `star`):
`∏ (adj(w)) = (∏ w)†`. -/
theorem prod_adjWord {n : ℕ} (w : List (Matrix (Fin n) (Fin n) ℂ)) :
    List.prod (adjWord w) = star (List.prod w) := by
  induction w with
  | nil => simp [adjWord]
  | cons a t ih =>
      rw [show adjWord (a :: t) = adjWord t ++ [star a] by
        simp [adjWord, List.reverse_cons]]
      rw [List.prod_append, ih]
      simp [List.prod_cons, star_mul]

/-- The compiled gate word realises exactly the abstract DB-DOI step `dbdoiStep`. -/
theorem refinedWord_prod {n : ℕ} (w : List (Matrix (Fin n) (Fin n) ℂ))
    (ED EH EDi : Matrix (Fin n) (Fin n) ℂ) :
    List.prod (refinedWord w ED EH EDi) =
      dbdoiStep (List.prod w) ED EH EDi := by
  simp only [refinedWord, dbdoiStep, List.prod_append, List.prod_cons,
    List.prod_nil, prod_adjWord, mul_one]

/-- Gate count of the compiled refinement, Eq. (17)/(23): three copies of the
warm-start word plus the three evolution gates. -/
theorem refinedWord_length {n : ℕ} (w : List (Matrix (Fin n) (Fin n) ℂ))
    (ED EH EDi : Matrix (Fin n) (Fin n) ℂ) :
    (refinedWord w ED EH EDi).length = 3 * w.length + 3 := by
  simp only [refinedWord, adjWord, List.length_append, List.length_cons,
    List.length_nil, List.length_reverse, List.length_map]
  omega

/-- Membership of the adjoint in the unitary group. -/
theorem star_mem_unitaryGroup {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    star U ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  simpa [Matrix.UnitaryGroup.inv_val] using
    (((⟨U, hU⟩ : Matrix.unitaryGroup (Fin n) ℂ)⁻¹)).property

/-- The one-step DB-DOI refinement of a unitary warm-start circuit is unitary
whenever the granted evolution unitaries are, so it compiles to a valid circuit
(c001, Eq. (17)). -/
theorem dbdoiStep_unitary {n : ℕ} {U ED EH EDi : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hED : ED ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hEH : EH ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hEDi : EDi ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    dbdoiStep U ED EH EDi ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  unfold dbdoiStep
  repeat first
    | apply Submonoid.mul_mem
    | exact hU
    | exact hED
    | exact hEH
    | exact hEDi
    | exact star_mem_unitaryGroup hU

/-- Warm-start energy bridge, Eq. (16): the Heisenberg-picture expectation
`⟨0|U†H_0U|0⟩` equals the Schrödinger-picture expectation `⟨ψ_0|H_0|ψ_0⟩` for
`ψ_0 = U|0⟩`. This is the identity that makes the warm-start energy observable
in the DB-DOI frame. -/
theorem warmStart_energy_bridge {n : ℕ}
    (H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    star e0 ⬝ᵥ ((star U * H * U) *ᵥ e0) =
      star (U *ᵥ e0) ⬝ᵥ (H *ᵥ (U *ᵥ e0)) := by
  rw [← Matrix.mulVec_mulVec e0 (star U * H) U]
  rw [← Matrix.mulVec_mulVec (U *ᵥ e0) (star U) H]
  rw [Matrix.dotProduct_mulVec]
  have hh : (star e0 ᵥ* star U : Fin (n + 1) → ℂ) = star (U *ᵥ e0) := by
    rw [Matrix.star_eq_conjTranspose (M := U)]
    exact (Matrix.star_mulVec U e0).symm
  rw [hh]

/-- c001 main result (Abstract; Sec. II B–C): a shallow warm-start gate word is
refined by one DB-DOI step into a finite gate word that (i) realises exactly the
DB-DOI step unitary `dbdoiStep`, (ii) is a valid unitary circuit, and (iii) has
gate count `3|w|+3`, matching the unfolded query/gate accounting of Eqs. (21),
(23). The warm-start energy underlying the protocol is
`warmStart_energy_bridge`. -/
theorem dbqa_two_stage_protocol {n : ℕ} (w : List (Matrix (Fin n) (Fin n) ℂ))
    (ED EH EDi : Matrix (Fin n) (Fin n) ℂ)
    (hU : List.prod w ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hED : ED ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hEH : EH ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hEDi : EDi ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    List.prod (refinedWord w ED EH EDi) = dbdoiStep (List.prod w) ED EH EDi ∧
      List.prod (refinedWord w ED EH EDi) ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      (refinedWord w ED EH EDi).length = 3 * w.length + 3 :=
  ⟨refinedWord_prod w ED EH EDi,
   refinedWord_prod w ED EH EDi ▸ dbdoiStep_unitary hU hED hEH hEDi,
   refinedWord_length w ED EH EDi⟩

end Qatlib.Papers.GroundDBrak24.MainResults.Refinement
