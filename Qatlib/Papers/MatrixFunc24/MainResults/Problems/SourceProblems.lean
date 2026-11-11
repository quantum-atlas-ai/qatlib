/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.RingTheory.Polynomial.Chebyshev
import Qatlib.Papers.MatrixFunc24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# MatrixFunc24 — the paper's matrix-function problems (Section 2 and Section 4)

Cifuentes, Wang, Silva, Berta, Aolita, *Quantum computational complexity of matrix
functions*, fixed arXiv:2410.13937v2.

This module fixes the concrete problem objects that the paper's claims speak
about: the four function families of Table 1 (monomial, Chebyshev, inverse, time
evolution), the two access models, the two norm normalizations, and the two
problem variants (matrix entry, Problem I; local measurement, Problem II).  The
classification statements of the sibling modules are statements about these
objects.

Every problem carries its two promise sets as parameters.  These are the paper's
YES/NO promise sets for the corresponding problem (the encoding of a matrix
instance into a finite bit string is fixed by the paper's input conventions);
the definitions here do not depend on the concrete encoding, only the theorems
that assert membership/hardness do.

Boundary: this is a vocabulary module.  It asserts no complexity classification;
those live in `ClassicalAlgorithms` and `Complexity`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix
open Polynomial

namespace Qatlib.Papers.MatrixFunc24.MainResults.Problems

open Qatlib.Papers.MatrixFunc24.MainResults.SourceModel

/-! ## 1. The four function families of Table 1 -/

/-- Table 1, monomial family: `f_m(x) = x^m` (Problem I/II of Section 4.1). -/
def monomialFamily : FunctionFamily := fun m x => x ^ m

/-- Table 1, Chebyshev family: `f_m(x) = T_m(x)`, the Chebyshev polynomial of
the first kind (Section 4.2). -/
def chebyshevFamily : FunctionFamily := fun m x =>
  Polynomial.eval x (Polynomial.Chebyshev.T ℂ (m : ℤ))

/-- Table 1, inverse family: `f(x) = 1/x` (Section 4.3). -/
def inverseFamily : FunctionFamily := fun _ x => x⁻¹

/-- Table 1, time-evolution family: `f_t(x) = e^{i t x}` (Section 4.4). -/
def timeEvolutionFamily (t : ℝ) : FunctionFamily :=
  fun _ x => Complex.exp (Complex.I * (t : ℂ) * x)

/-- A degree-`deg` polynomial family `f_m(x) = Σ_{r=0}^{deg} α_r x^r`, the form
used in Lemma 20 and Lemma 17 (`f(x) = Σ_r α_r x^r`). -/
def polynomialFamily (coeff : ℕ → ℂ) (deg : ℕ) : FunctionFamily :=
  fun _ x => ∑ r ∈ Finset.range (deg + 1), coeff r * x ^ r

/-- The `ℓ¹` norm of the coefficient vector of `f`, evaluated at scale `R`:
`∑_r ‖α_r‖ R^r`.  This is `‖f(‖A‖₁ x)‖_{ℓ¹}` of Lemma 20 with `R = ‖A‖₁`. -/
def coeffL1 (coeff : ℕ → ℂ) (deg : ℕ) (R : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (deg + 1), ‖coeff r‖ * R ^ r

/-! ## 2. Problem constructors -/

/-- Build a `MatrixProblem` from its descriptive data and its two promise sets. -/
def mkProblem (name : String) (kind : ProblemKind) (family : FunctionFamily)
    (access : AccessModel) (normKind : NormKind) (bound : ℝ)
    (yes no : Set (List Bool)) : MatrixProblem :=
  { name := name, kind := kind, family := family, access := access,
    normKind := normKind, bound := bound, yes := yes, no := no }

/-! ### Monomial problems (Section 4.1) -/

/-- `MonomialSparseAccess_{‖A‖}` (Theorem 21). -/
def monomialSparseProblem (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "MonomialSparseAccess_‖A‖" ProblemKind.matrixEntry monomialFamily
    AccessModel.sparse NormKind.spectral 1 yes no

/-- `MonomialPauliAccess_{‖A‖}` (Proposition 23). -/
def monomialPauliProblem (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "MonomialPauliAccess_‖A‖" ProblemKind.matrixEntry monomialFamily
    AccessModel.pauli NormKind.spectral 1 yes no

/-- `LM-MonomialSparseAccess_{‖A‖}` (Proposition 24). -/
def lmMonomialSparseProblem (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "LM-MonomialSparseAccess_‖A‖" ProblemKind.localMeasurement monomialFamily
    AccessModel.sparse NormKind.spectral 1 yes no

/-- `LM-MonomialPauliAccess_{‖A‖}` (Proposition 24). -/
def lmMonomialPauliProblem (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "LM-MonomialPauliAccess_‖A‖" ProblemKind.localMeasurement monomialFamily
    AccessModel.pauli NormKind.spectral 1 yes no

/-- `Normalized-LM-MonomialSparseAccess_{‖A‖}` (Proposition 62). -/
def normalizedLMMonomialSparseProblem (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "Normalized-LM-MonomialSparseAccess_‖A‖" ProblemKind.localMeasurement
    monomialFamily AccessModel.sparse NormKind.spectral 1 yes no

/-- `Normalized-LM-MonomialPauliAccess_{‖A‖}` (Proposition 62). -/
def normalizedLMMonomialPauliProblem (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "Normalized-LM-MonomialPauliAccess_‖A‖" ProblemKind.localMeasurement
    monomialFamily AccessModel.pauli NormKind.spectral 1 yes no

/-- The super-sparse monomial problem of Proposition 29 (the access model lists
all `k` non-zero entries as triples `{a_ij, i, j}`). -/
def monomialSuperSparseProblem (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "MonomialSuperSparseAccess_‖A‖" ProblemKind.matrixEntry monomialFamily
    AccessModel.sparse NormKind.spectral 1 yes no

/-! ### Chebyshev problems (Section 4.2) -/

/-- `ChebyshevSparseAccess_{‖A‖}` (Theorem 31). -/
def chebyshevSparseProblem (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "ChebyshevSparseAccess_‖A‖" ProblemKind.matrixEntry chebyshevFamily
    AccessModel.sparse NormKind.spectral 1 yes no

/-- `ChebyshevPauliAccess_{‖A‖}` (Theorem 31). -/
def chebyshevPauliProblem (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "ChebyshevPauliAccess_‖A‖" ProblemKind.matrixEntry chebyshevFamily
    AccessModel.pauli NormKind.spectral 1 yes no

/-- `LM-ChebyshevSparseAccess_{‖A‖}` (Proposition 32). -/
def lmChebyshevSparseProblem (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "LM-ChebyshevSparseAccess_‖A‖" ProblemKind.localMeasurement chebyshevFamily
    AccessModel.sparse NormKind.spectral 1 yes no

/-- `LM-ChebyshevPauliAccess_{‖A‖}` (Proposition 32). -/
def lmChebyshevPauliProblem (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "LM-ChebyshevPauliAccess_‖A‖" ProblemKind.localMeasurement chebyshevFamily
    AccessModel.pauli NormKind.spectral 1 yes no

/-! ### Inverse problems (Section 4.3) -/

/-- `InverseSparseAccess_{‖A‖₁}` (Theorem 36). -/
def inverseSparseProblem (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "InverseSparseAccess_‖A‖₁" ProblemKind.matrixEntry inverseFamily
    AccessModel.sparse NormKind.inducedOne 1 yes no

/-- `InversePauliAccess_{λ_A}` (Theorem 36). -/
def inversePauliProblem (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "InversePauliAccess_λA" ProblemKind.matrixEntry inverseFamily
    AccessModel.pauli NormKind.pauli 1 yes no

/-- `LM-InverseSparseAccess_{‖A‖₁}` (Proposition 37). -/
def lmInverseSparseProblem (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "LM-InverseSparseAccess_‖A‖₁" ProblemKind.localMeasurement inverseFamily
    AccessModel.sparse NormKind.inducedOne 1 yes no

/-- `LM-InversePauliAccess_{λ_A}` (Proposition 37/63). -/
def lmInversePauliProblem (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "LM-InversePauliAccess_λA" ProblemKind.localMeasurement inverseFamily
    AccessModel.pauli NormKind.pauli 1 yes no

/-! ### Time-evolution problems (Section 4.4) -/

/-- `TimeEvolutionSparseAccess_{‖A‖₁}` for evolution time `t` (Proposition 39). -/
def timeEvolutionSparseProblem (t : ℝ) (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "TimeEvolutionSparseAccess_‖A‖₁" ProblemKind.matrixEntry
    (timeEvolutionFamily t) AccessModel.sparse NormKind.inducedOne 1 yes no

/-- `TimeEvolutionPauliAccess_{λ_A}` for evolution time `t` (Proposition 39). -/
def timeEvolutionPauliProblem (t : ℝ) (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "TimeEvolutionPauliAccess_λA" ProblemKind.matrixEntry
    (timeEvolutionFamily t) AccessModel.pauli NormKind.pauli 1 yes no

/-- `LM-TimeEvolutionSparseAccess_{‖A‖₁}` for evolution time `t` (Proposition 40). -/
def lmTimeEvolutionSparseProblem (t : ℝ) (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "LM-TimeEvolutionSparseAccess_‖A‖₁" ProblemKind.localMeasurement
    (timeEvolutionFamily t) AccessModel.sparse NormKind.inducedOne 1 yes no

/-- `LM-TimeEvolutionPauliAccess_{λ_A}` for evolution time `t` (Proposition 40). -/
def lmTimeEvolutionPauliProblem (t : ℝ) (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "LM-TimeEvolutionPauliAccess_λA" ProblemKind.localMeasurement
    (timeEvolutionFamily t) AccessModel.pauli NormKind.pauli 1 yes no

/-! ### Generic entry-estimation problems used by Theorems 45 and 46 -/

/-- The entry-estimation problem for an arbitrary function family under Pauli
access (Theorem 45). -/
def pauliEntryProblem (family : FunctionFamily) (bound : ℝ)
    (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "EntryEstimationPauli" ProblemKind.matrixEntry family
    AccessModel.pauli NormKind.pauli bound yes no

/-- The entry-estimation problem for an arbitrary function family under sparse
access (Theorem 45). -/
def sparseEntryProblem (family : FunctionFamily) (bound : ℝ)
    (yes no : Set (List Bool)) : MatrixProblem :=
  mkProblem "EntryEstimationSparse" ProblemKind.matrixEntry family
    AccessModel.sparse NormKind.inducedOne bound yes no

/-! ## 3. The classical-solvability predicate

The paper's algorithm claims have the form "problem `P` can be solved classically
in time `T(parameters)`".  The shared library has no operational cost model for
classical computation, so a claim is recorded as: (i) `P` has a correct classical
decider on the promise, and (ii) the paper's running-time expression `T` (a real
function of the input length that also mentions the parameters `m, s, ε, δ, η`)
is non-negative.  This keeps the paper's exact bound in the statement (rather
than replacing it by an unspecified polynomial) while being explicit that the
bound is *recorded*, not discharged against a machine model. -/

/-- `ClassicallySolvable P T` — the promise problem `P` admits a correct
classical decider, and `T` is the paper's stated running-time bound (recorded as
a real-valued function of the input bit length). -/
def ClassicallySolvable (P : MatrixProblem) (T : ℕ → ℝ) : Prop :=
  (∃ decide : List Bool → Bool,
      (∀ x, x ∈ P.yes → decide x = true) ∧
      (∀ x, x ∈ P.no → decide x = false)) ∧
    (∀ n, 0 ≤ T n)

/-- Membership of a problem's promise in `BQP`. -/
def InBQP (P : MatrixProblem) : Prop := P.promise ∈ BQP

/-- `BPP`, the classical bounded-error polynomial-time class, modeled on the same
promise-problem carrier as `BQP` by the existence of a correct classical decider
on the promise.  The polynomial-time cost bound is not modeled (the shared
library has no classical cost semantics); this is the form in which the paper's
`BPP = BQP` statement (Proposition 33) is recorded. -/
def BPP : Set PromiseProblem :=
  {L | ∃ decide : List Bool → Bool,
      (∀ x, x ∈ L.1 → decide x = true) ∧
      (∀ x, x ∈ L.2 → decide x = false)}

/-! ## 4. Basic sanity lemmas -/

/-- The monomial family is the identity at `m = 1`. -/
theorem monomialFamily_one (x : ℂ) : monomialFamily 1 x = x := by
  simp [monomialFamily]

/-- The polynomial family of degree `deg` is a polynomial in `x`. -/
theorem polynomialFamily_apply (coeff : ℕ → ℂ) (deg : ℕ) (m : ℕ) (x : ℂ) :
    polynomialFamily coeff deg m x =
      ∑ r ∈ Finset.range (deg + 1), coeff r * x ^ r := rfl

end Qatlib.Papers.MatrixFunc24.MainResults.Problems
