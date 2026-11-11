/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElecStructure10.MainResults.NumberNumber.NumberNumberPauliDecomposition
import Qatlib.Papers.ElecStructure10.MainResults.DoubleExcitation.DoubleExcitationPauliDecomposition
import Qatlib.Concepts.TrotterFormula.TimeOrdered.TypesOfTrotterErrorAthe
import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Theorem11Quan

set_option backward.isDefEq.respectTransparency false

/-!
# ElecStructure10.MainResults.MainResult — the general decomposition pipeline

Source: Whitfield, Biamonte, Aspuru-Guzik, fixed arXiv:1001.3855v3, abstract and
introduction (p. 1–2, `assets/1001.3855.txt` lines 35–60), Section 3
(Eqs. (17), (21), pp. 13–14) and Section 4 (Trotter step / phase-estimation
algorithm, pp. 15–18).

Claim c001 of `metadata/papers/ElecStructure10.json` is the paper's main result
in prose: *“provide a general decomposition for electronic Hamiltonians and
demonstrate this method with an explicit quantum circuit for a single Trotter
time step”*.  The concrete mathematical content of that pipeline, as executed in
the paper, is the conjunction of four statements, all of which are documented
here on the paper's computational register `Reg n = Fin n → Bool`; the formal
theorem below asserts the three components that are fully proved:

1. **two-electron part** (Eq. (17), p. 13): the Coulomb/exchange number–number
   operator `∑_{p<q} (h_pqqp − h_pqpq δ) a†_p a†_q a_q a_p` is a
   constant + single-`σ^z` + `σ^zσ^z` sum with `1/4` coefficients
   (`NumberNumber.eq17_numberNumber_pauli_decomposition`);
2. **double-excitation part** (Eq. (21), p. 14): the four-orbital double
   excitation `½ ∑ h_pqrs (a†_p a†_q a_r a_s + h.c.)` and its eight-term
   `σ^x/σ^y` four-body bracket.  The operator objects are fixed in
   `DoubleExcitation` (`orbitSum`, `pauliBracket`, `hOne/hTwo/hThree`), but the
   coefficient identity is an open formalization gap and is deliberately not
   asserted (see that file);
3. **Trotter step** (Section 4): for any word of Pauli strings and any target
   generator, `exp(−iHt)` is approximated by the product formula with the exact
   additive / exponentiated / multiplicative error structure — reused from the
   frozen `QuantumAlgorithm.Concepts.TrotterFormula.TimeOrdered.typesOfTrotterError`
   (`TypesOfTrotterError`);
4. **phase estimation** (Section 4, Theorem 11 of BHMT): the QFT readout of the
   phase of the Trotterized unitary concentrates on the nearest `M`-grid points
   with the frozen success-probability guarantees — reused from the frozen
   `QuantumAlgorithm.Concepts.AmplitudeCore.PhaseEstimation.bhmt_phase_estimation_theorem11`.

Components 1, 3, 4 are discharged completely (1 from this paper's
`NumberNumber` file, 3–4 from the frozen library, with the FQNs cited above).
Component 2 is *not* part of the proved conjunction: its operator objects are
fixed in the `DoubleExcitation` file, but the Eq. (21) coefficient identity is
an open gap (and is false without the paper's molecular-integral symmetries), so
it is deliberately left unasserted.  No additional hypothesis is introduced
beyond the paper's own symmetry assumption on the two-electron integrals.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Papers.ElecStructure10.MainResults.PauliAlgebra
open scoped BigOperators

namespace Qatlib.Papers.ElecStructure10.MainResults.MainResult

variable {n : ℕ}

/-- **Main result (c001).**  The paper's electronic-structure simulation pipeline,
stated as one conjunction over the register `Reg n`:

* Eq. (17): the two-electron number–number operator decomposes into
  constant / single-`σ^z` / `σ^zσ^z` terms with `1/4` coefficients;
* the Trotter product formula reproduces `exp(t H)` with the exact frozen error
  structure of `typesOfTrotterError`;
* phase estimation on the resulting unitary obeys the frozen BHMT Theorem 11
  probability guarantees.

The decomposed two-electron part is the first conjunct; the last two conjuncts
are the "single Trotter time step + phase estimation" half of the claim.  The
Eq. (21) double-excitation coefficient identity is not asserted here: it is an
open formalization gap (see `DoubleExcitation`). -/
theorem main_result_general_decomposition
    -- Eq. (17) coefficient family: symmetric two-electron integrals
    (c : Fin n → Fin n → ℂ) (hsym : ∀ p q, c p q = c q p) :
    -- (1) Eq. (17): two-electron number–number Pauli decomposition
    ((∑ p : Fin n, ∑ q : Fin n, if p < q then c p q • (numberOp p * numberOp q) else 0)
        = (1 / 4 : ℂ) •
            ((∑ p : Fin n, ∑ q : Fin n, if p < q then c p q else 0) •
              (1 : Matrix (Reg n) (Reg n) ℂ))
          - (1 / 4 : ℂ) •
            (∑ q : Fin n, (∑ p : Fin n, if p ≠ q then c p q else 0) • zOp q)
          + (1 / 4 : ℂ) •
            (∑ p : Fin n, ∑ q : Fin n, if p < q then c p q • (zOp p * zOp q) else 0)) ∧
    -- (2) Trotter product-formula error structure (frozen `typesOfTrotterError`)
    (Qatlib.Concepts.TrotterFormula.TimeOrdered.TypesOfTrotterError) ∧
    -- (3) phase-estimation probability guarantees (frozen BHMT Theorem 11)
    (∀ (M : ℕ) (ω : ℝ), 0 < M → 0 ≤ ω → ω < 1 →
      (∑ x : Fin M,
          Qatlib.Concepts.AmplitudeCore.PhaseEstimation.bhmt11OutcomeMass M ω x) = 1 ∧
      ((∃ j : ℤ, (M : ℝ) * ω = (j : ℝ)) →
        ∃ x : Fin M, (x.val : ℝ) = (M : ℝ) * ω ∧
          Qatlib.Concepts.AmplitudeCore.PhaseEstimation.bhmt11OutcomeMass M ω x = 1) ∧
      ((¬ ∃ j : ℤ, (M : ℝ) * ω = (j : ℝ)) →
        ∀ x : Fin M,
          let Δ := Qatlib.Concepts.AmplitudeCore.PhaseEstimation.bhmt11CircleDist
            ω ((x.val : ℝ) / (M : ℝ));
          Qatlib.Concepts.AmplitudeCore.PhaseEstimation.bhmt11OutcomeMass M ω x =
            Real.sin ((M : ℝ) * Δ * Real.pi) ^ 2 /
              ((M : ℝ) ^ 2 * Real.sin (Δ * Real.pi) ^ 2) ∧
          Qatlib.Concepts.AmplitudeCore.PhaseEstimation.bhmt11OutcomeMass M ω x ≤
            (1 : ℝ) / (2 * (M : ℝ) * Δ) ^ 2) ∧
      (∀ k : ℝ, 1 < k →
        1 - 1 / (2 * (k - 1)) ≤
          Qatlib.Concepts.AmplitudeCore.PhaseEstimation.bhmt11WindowMass M ω
            (k / (M : ℝ))) ∧
      (2 < M →
        8 / Real.pi ^ 2 ≤
          Qatlib.Concepts.AmplitudeCore.PhaseEstimation.bhmt11WindowMass M ω
            (1 / (M : ℝ)))) := by
  refine ⟨NumberNumber.eq17_numberNumber_pauli_decomposition c hsym, ?_, ?_⟩
  · -- Trotter step: frozen `typesOfTrotterError`
    exact Qatlib.Concepts.TrotterFormula.TimeOrdered.typesOfTrotterError
  · -- Phase estimation: frozen BHMT Theorem 11
    exact Qatlib.Concepts.AmplitudeCore.PhaseEstimation.bhmt_phase_estimation_theorem11

end Qatlib.Papers.ElecStructure10.MainResults.MainResult
