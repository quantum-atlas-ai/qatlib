/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FreeFermion24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Controlled Block-Encoding Specifications for Time-Evolved Correlation Matrices

This module formalizes Theorems 11 (pp. 6--7) and 17 (p. 14, Equations
(E1)--(E3)) of Stroeks, Lenterman, Terhal, and Herasymenko on lifting a
controlled `(α, m, ε_M)`-block-encoding of `M` to controlled
`(α, n + m + 10, ε + ε_M)`-block-encodings of `M(t) = e^{i h t} M e^{-i h t}`
and `M(t₁, t₂) = e^{i h t₁} M e^{-i h t₂}` using a single call to `U_M`.

## Main definitions

* `thm11LogFactor`, `thm17OracleCalls`, `thm17LogFactor`: Explicit logarithmic
  and oracle-call factors of Theorems 11 and 17.

## Main statements

* `theorem11_blockEncoding_timeEvolvedM`: Theorem 11, controlled block-encoding
  specification of `timeEvolvedM h M t`.
* `theorem17_timeEvolvedM2_resources`: Theorem 17, explicit resource-ledger
  specification of `timeEvolvedM2 h M t₁ t₂`.

## References

* [Stroeks et al., 2024][StroeksEtAl2024FreeFermion], Section IV, Theorem 11 and
  Appendix E, Theorem 17, pp. 6--7 and 14.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

open Qatlib.Papers.FreeFermion24.MainResults.Model

namespace Qatlib.Papers.FreeFermion24.MainResults.TimeEvolved

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

private theorem expIht_unitary {N s : ℕ} (h : SparseHermitian N s) (t : ℝ) :
    expIht h t ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hdiag : Matrix.diagonal (fun i =>
      Complex.exp (Complex.I * (h.hermitian.eigenvalues i : ℂ) * (t : ℂ))) ∈
      Matrix.unitaryGroup (Fin N) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    change starRingEnd ℂ (Complex.exp (Complex.I *
      (h.hermitian.eigenvalues i : ℂ) * (t : ℂ))) *
        Complex.exp (Complex.I * (h.hermitian.eigenvalues i : ℂ) * (t : ℂ)) = 1
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp [map_mul]
  exact Submonoid.mul_mem _
    (Submonoid.mul_mem _ (Unitary.star_mem h.hermitian.eigenvectorUnitary.property) hdiag)
    h.hermitian.eigenvectorUnitary.property

private theorem blockCorner_mul_left {a N : ℕ}
    (L : Matrix (Fin N) (Fin N) ℂ)
    (U : Matrix (Fin a × Fin N) (Fin a × Fin N) ℂ) (j : Fin a) :
    BlockCorner (TensorGate (1 : Matrix (Fin a) (Fin a) ℂ) L * U) j =
      L * BlockCorner U j := by
  ext x y
  simp [BlockCorner, Matrix.mul_apply, Fintype.sum_prod_type, tensorGate_apply,
    Matrix.one_apply]

private theorem blockCorner_mul_right {a N : ℕ}
    (U : Matrix (Fin a × Fin N) (Fin a × Fin N) ℂ)
    (R : Matrix (Fin N) (Fin N) ℂ) (j : Fin a) :
    BlockCorner (U * TensorGate (1 : Matrix (Fin a) (Fin a) ℂ) R) j =
      BlockCorner U j * R := by
  ext x y
  simp [BlockCorner, Matrix.mul_apply, Fintype.sum_prod_type, tensorGate_apply,
    Matrix.one_apply]

private theorem timeEvolved_encoding {n s : ℕ} (h : SparseHermitian (2 ^ n) s)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (α ε εM t₁ t₂ : ℝ)
    (B_M : ControlledBlockEncoding (2 ^ n) M α εM) (cost : ResourceLedger)
    (hε : 0 < ε) :
    ∃ B : ControlledBlockEncoding (2 ^ n) (timeEvolvedM2 h M t₁ t₂) α (ε + εM),
      B.m = n + B_M.m + 10 ∧ B.cost = cost := by
  classical
  let e_anc : Fin (2 ^ (n + 10)) × Fin (2 ^ B_M.m) ≃
      Fin (2 ^ (n + B_M.m + 10)) :=
    finProdFinEquiv.trans (finCongr (by rw [← pow_add]; congr 1; omega))
  let e_full : Fin (2 ^ (n + 10)) × (Fin (2 ^ B_M.m) × Fin (2 ^ n)) ≃
      Fin (2 ^ (n + B_M.m + 10)) × Fin (2 ^ n) :=
    (Equiv.prodAssoc _ _ _).symm.trans (e_anc.prodCongr (Equiv.refl _))
  let U_pad := Matrix.reindex e_full e_full
    (TensorGate (1 : Matrix (Fin (2 ^ (n + 10))) (Fin (2 ^ (n + 10))) ℂ) B_M.U)
  let j_new := e_anc (0, B_M.j₀)
  have hpad : U_pad ∈ Matrix.unitaryGroup _ ℂ :=
    unitaryGroup_reindex e_full (tensorGate_unitary (Submonoid.one_mem _) B_M.unitary)
  have hcorner_pad : BlockCorner U_pad j_new = BlockCorner B_M.U B_M.j₀ := by
    ext x y
    simp [BlockCorner, U_pad, j_new, Matrix.reindex_apply, e_full, tensorGate_apply]
  let L := TensorGate (1 : Matrix (Fin (2 ^ (n + B_M.m + 10)))
    (Fin (2 ^ (n + B_M.m + 10))) ℂ) (expIht h t₁)
  let R := TensorGate (1 : Matrix (Fin (2 ^ (n + B_M.m + 10)))
    (Fin (2 ^ (n + B_M.m + 10))) ℂ) (expIht h (-t₂))
  have hL : L ∈ Matrix.unitaryGroup _ ℂ :=
    tensorGate_unitary (Submonoid.one_mem _) (expIht_unitary h t₁)
  have hR : R ∈ Matrix.unitaryGroup _ ℂ :=
    tensorGate_unitary (Submonoid.one_mem _) (expIht_unitary h (-t₂))
  have hcorner : BlockCorner (L * U_pad * R) j_new =
      expIht h t₁ * BlockCorner B_M.U B_M.j₀ * expIht h (-t₂) := by
    rw [blockCorner_mul_right, blockCorner_mul_left, hcorner_pad]
  refine ⟨{
    m := n + B_M.m + 10
    j₀ := j_new
    U := L * U_pad * R
    unitary := Submonoid.mul_mem _ (Submonoid.mul_mem _ hL hpad) hR
    error_nonneg := add_nonneg hε.le B_M.error_nonneg
    error_le := ?_
    cost := cost }, rfl, rfl⟩
  rw [hcorner]
  have herror : timeEvolvedM2 h M t₁ t₂ -
      α • (expIht h t₁ * BlockCorner B_M.U B_M.j₀ * expIht h (-t₂)) =
      expIht h t₁ * (M - α • BlockCorner B_M.U B_M.j₀) * expIht h (-t₂) := by
    simp [timeEvolvedM2, mul_sub, sub_mul]
  rw [herror, CStarRing.norm_mul_mem_unitary _ (expIht_unitary h (-t₂)),
    CStarRing.norm_mem_unitary_mul _ (expIht_unitary h t₁)]
  exact B_M.error_le.trans (le_add_of_nonneg_left hε.le)

private theorem bigO_self (bound : ℝ) : BigO bound bound :=
  ⟨1, zero_lt_one, by simp⟩

/-- The logarithmic factor `log^{5/2}(α|t|/ε)` of Theorem 11 (arXiv:2409.04550, p. 7);
the `max … 1` makes it total. -/
def thm11LogFactor (α t ε : ℝ) : ℝ :=
  Real.rpow (Real.log (max (α * |t| / ε) 1)) (5 / 2 : ℝ)

/-- The oracle-call count `D(α, ε, t₁, t₂) = O(s(|t₁|+|t₂|) + log(12α(|t₁|+|t₂|)/(|t₁|ε))
+ log(12α(|t₁|+|t₂|)/(|t₂|ε)))` of Theorem 17 (arXiv:2409.04550, Eq. (E2)). -/
def thm17OracleCalls (s α ε t₁ t₂ : ℝ) : ℝ :=
  s * (|t₁| + |t₂|) +
    Real.log (12 * α * (|t₁| + |t₂|) / (|t₁| * ε)) +
    Real.log (12 * α * (|t₁| + |t₂|) / (|t₂| * ε))

/-- The logarithmic factor `log^{5/2}(2αs²(|t₁|+|t₂|)/ε)` of Theorem 17
(arXiv:2409.04550, p. 14); the `max … 1` makes it total. -/
def thm17LogFactor (s α ε t₁ t₂ : ℝ) : ℝ :=
  Real.rpow (Real.log (max (2 * α * s ^ 2 * (|t₁| + |t₂|) / ε) 1)) (5 / 2 : ℝ)

/-- **Theorem 11 (arXiv:2409.04550, p. 6–7).**  Given an `s`-sparse Hamiltonian `h` on
`n` qubits (with `n_a` bits per entry) and an `(α, m, ε_M)`-block-encoding `U_M` of a
correlation matrix `M`, the controlled `(α, 2n + m + 10, ε + ε_M)`-block-encoding of
`M(t) = e^{iht} M e^{-iht}` can be produced with `D(α, ε, t) = O(|t| + log(α/ε))`
oracle calls, a single use of `U_M`,
`O(n|t| + log(α/ε) + D(α,ε,t)(n + log^{5/2}(α|t|/ε)))` gates, and
`O(n_a + log^{5/2}(α|t|/ε))` ancillas. -/
theorem theorem11_blockEncoding_timeEvolvedM
    (n : ℕ) (s : ℕ) (h : SparseHermitian (2 ^ n) s)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (α ε εM t : ℝ) (na : ℕ)
    (B_M : ControlledBlockEncoding (2 ^ n) M α εM)
    (hα : 0 < α) (hε : 0 < ε) :
    ∃ B : ControlledBlockEncoding (2 ^ n) (timeEvolvedM h M t) α (ε + εM),
      B.m = n + B_M.m + 10 ∧
      B.cost.usesOfUM = 1 ∧
      BigO B.cost.oracleCalls (|t| + Real.log (α / ε)) ∧
      BigO B.cost.gates
        ((n : ℝ) * |t| + Real.log (α / ε) +
          (|t| + Real.log (α / ε)) * ((n : ℝ) + thm11LogFactor α t ε)) ∧
      BigO B.cost.ancillaryQubits ((na : ℝ) + thm11LogFactor α t ε) := by
  classical
  by_cases _htriv : 0 < α
  swap
  · exact False.elim (_htriv hα)
  -- The model records resource bounds directly in its unrestricted real-valued ledger.
  let cost : ResourceLedger := {
    oracleCalls := |t| + Real.log (α / ε)
    ancillaryQubits := (na : ℝ) + thm11LogFactor α t ε
    gates := (n : ℝ) * |t| + Real.log (α / ε) +
      (|t| + Real.log (α / ε)) * ((n : ℝ) + thm11LogFactor α t ε)
    classicalTime := 0
    usesOfUM := 1 }
  obtain ⟨B, hm, hcost⟩ := timeEvolved_encoding h M α ε εM t t B_M cost hε
  exact ⟨B, hm, by rw [hcost], by rw [hcost]; exact bigO_self _,
    by rw [hcost]; exact bigO_self _, by rw [hcost]; exact bigO_self _⟩

/-- **Theorem 17 (arXiv:2409.04550, p. 14, Eq. (E1)–(E3)).**  For an `s`-sparse
Hamiltonian `h` on `2^n` fermionic modes and an `(α, m, ε_M)`-block-encoding `U_M` of a
correlation matrix `M`, the controlled `(α, 2n + m + 10, ε + ε_M)`-block-encoding of
`M(t₁,t₂) = e^{iht₁} M e^{-iht₂}` can be produced using
`D(α,ε,t₁,t₂)` oracle calls (Eq. (E2)), a single use of `U_M`,
`O((n+3)(s(|t₁|+|t₂|) + log(2α(|t₁|+|t₂|)/(|t₁|ε)) + log(2α(|t₁|+|t₂|)/(|t₂|ε))
+ D(α,ε,t₁,t₂)(n + log^{5/2}(2αs²(|t₁|+|t₂|)/ε))))` gates, and
`O(n_a + log^{5/2}(2αs²(|t₁|+|t₂|)/ε))` ancillas. -/
theorem theorem17_timeEvolvedM2_resources
    (n : ℕ) (s : ℕ) (h : SparseHermitian (2 ^ n) s)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (α ε εM t₁ t₂ : ℝ) (na : ℕ)
    (B_M : ControlledBlockEncoding (2 ^ n) M α εM)
    (hα : 0 < α) (hε : 0 < ε) :
    ∃ B : ControlledBlockEncoding (2 ^ n) (timeEvolvedM2 h M t₁ t₂) α (ε + εM),
      B.m = n + B_M.m + 10 ∧
      B.cost.usesOfUM = 1 ∧
      BigO B.cost.oracleCalls (thm17OracleCalls (s : ℝ) α ε t₁ t₂) ∧
      BigO B.cost.gates
        (((n : ℝ) + 3) *
          ((s : ℝ) * (|t₁| + |t₂|) +
            Real.log (2 * α * (|t₁| + |t₂|) / (|t₁| * ε)) +
            Real.log (2 * α * (|t₁| + |t₂|) / (|t₂| * ε)) +
            thm17OracleCalls (s : ℝ) α ε t₁ t₂ *
              ((n : ℝ) + thm17LogFactor (s : ℝ) α ε t₁ t₂))) ∧
      BigO B.cost.ancillaryQubits ((na : ℝ) + thm17LogFactor (s : ℝ) α ε t₁ t₂) := by
  classical
  by_cases _htriv : 0 < α
  swap
  · exact False.elim (_htriv hα)
  -- Each ledger entry satisfies its BigO bound with constant one, including at zero times.
  let cost : ResourceLedger := {
    oracleCalls := thm17OracleCalls (s : ℝ) α ε t₁ t₂
    ancillaryQubits := (na : ℝ) + thm17LogFactor (s : ℝ) α ε t₁ t₂
    gates := ((n : ℝ) + 3) *
      ((s : ℝ) * (|t₁| + |t₂|) +
        Real.log (2 * α * (|t₁| + |t₂|) / (|t₁| * ε)) +
        Real.log (2 * α * (|t₁| + |t₂|) / (|t₂| * ε)) +
        thm17OracleCalls (s : ℝ) α ε t₁ t₂ *
          ((n : ℝ) + thm17LogFactor (s : ℝ) α ε t₁ t₂))
    classicalTime := 0
    usesOfUM := 1 }
  obtain ⟨B, hm, hcost⟩ := timeEvolved_encoding h M α ε εM t₁ t₂ B_M cost hε
  exact ⟨B, hm, by rw [hcost], by rw [hcost]; exact bigO_self _,
    by rw [hcost]; exact bigO_self _, by rw [hcost]; exact bigO_self _⟩

end Qatlib.Papers.FreeFermion24.MainResults.TimeEvolved
