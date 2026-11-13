/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Papers.LowEnergySim23.MainResults.Framework.Core
import Qatlib.Foundations.PureStateMath.Qubit

set_option backward.isDefEq.respectTransparency false

/-!
# Paper-layer algorithmic models for Theorems 1--4

Fixed paper version: arXiv:2312.08867v3 (Quantum **8**, 1409 (2024)).

The paper's Theorems 1--4 give explicit Trotter-number upper bounds (Eqs. (1), (2),
(4), (5), (6), (8), (9)) for randomly compiled product formulas in the low-energy
subspace.  This module provides paper-layer models of the algorithms so that the
claims can be stated faithfully:

* `HamModel D` — the paper's data for an `n`-qubit `k`-local Hamiltonian
  `H = Σ_{l=1}^L H_l` with parameters `M, J, d` (and `LMJ = O(n)`);
* `qdriftWeight`, `qdriftFactor`, `qdriftProduct`, `qdriftExpectedUnitary`,
  `qdriftExpectedError`, `qdriftFailureProb` — the qDRIFT scheme of Theorem 1;
* `randomPermutationProduct/…` — the random-permutation scheme of Theorem 2;
* `doublingOrderProduct/…` — the symmetric (doubling-order) composition of
  Corollary 1;
* `twirlUnitary`, `symmetryProtectedProduct/…` — the symmetry-protection
  scheme of Theorem 3 (group averaging over the symmetry group of `H`);
* `PowerLawModel` — the power-law Hamiltonian of Theorem 4;
* `BigOtildePlusBigO` — the formal meaning of `Õ(·) + O(·)` used throughout;
* `thm1…`, `thm2…`, `cor1…`, `thm3…`, `thm4…` — the explicit bounds displayed in
  the paper, transcribed literally into Lean.

The models are deliberately conservative: a randomized product formula is
represented by the finite average over its random choices, so the paper's
"expected error" is a literal finite sum, and the failure probabilities are
literal tail masses.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.LowEnergySim23.MainResults.Framework

/-! ## The paper's `Õ + O` notation -/

/-- Formal reading of the paper's `Õ(X) + O(Y)`: `r ≤ C·X·(log(2+X)+2)^C + C·Y`
for a single universal constant `C`.  The polylogarithmic factor of `Õ` is
absorbed into the power `C`. -/
def BigOtildePlusBigO (r X Y : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ r ≤ C * X * Real.rpow (Real.log (2 + X) + 2) C + C * Y

/-! ## Hamiltonian data (paper §2, Theorems 1--4) -/

/-- The paper's data for an `n`-qubit `k`-local Hamiltonian `H = Σ_{l<L} H_l`
with parameters `M, J, d` and `LMJ = O(n)` (§2, p.4). -/
structure HamModel (D : ℕ) where
  /-- number of qubits -/
  n : ℕ
  /-- ambient dimension `D = 2^n` -/
  D_eq : D = 2 ^ n
  /-- number of local terms -/
  L : ℕ
  /-- the local terms -/
  terms : Fin L → Op D
  /-- the Hamiltonian -/
  H : Op D
  /-- `H = Σ_l H_l` -/
  sum_eq : (∑ l, terms l) = H
  /-- Hermiticity of `H` -/
  hermitian : H.IsHermitian
  /-- interaction strength -/
  J : ℝ
  J_nonneg : 0 ≤ J
  /-- maximal interaction parameter `M` -/
  M : ℝ
  M_nonneg : 0 ≤ M
  /-- locality `k` -/
  k : ℕ
  /-- spatial dimension `d` -/
  d : ℝ
  d_nonneg : 0 ≤ d
  /-- per-term strength bound -/
  term_norm_le : ∀ l, ‖terms l‖ ≤ J
  /-- the paper's standing assumption `LMJ = O(n)` -/
  LMJ_bound : ∃ C : ℝ, 0 < C ∧ (L : ℝ) * M * J ≤ C * (n : ℝ)

/-! ## qDRIFT (Theorem 1) -/

/-- qDRIFT sampling weight `p_l = ‖H_l‖ / Σ_k ‖H_k‖` (§2). -/
def qdriftWeight {D : ℕ} (Hd : HamModel D) (l : Fin Hd.L) : ℝ :=
  ‖Hd.terms l‖ / ∑ k, ‖Hd.terms k‖

/-- One qDRIFT factor `e^{-i (t/r) H_l / p_l}`. -/
def qdriftFactor {D : ℕ} (Hd : HamModel D) (t : ℝ) (r : ℕ) (l : Fin Hd.L) : Op D :=
  HamiltonianEvolution (Hd.terms l) (t / ((r : ℝ) * qdriftWeight Hd l))

/-- A single qDRIFT product `∏_{j<r} e^{-i (t/r) H_{σ_j}/p_{σ_j}}`. -/
def qdriftProduct {D : ℕ} (Hd : HamModel D) (t : ℝ) (r : ℕ)
    (σ : Fin r → Fin Hd.L) : Op D :=
  (List.ofFn fun j : Fin r => qdriftFactor Hd t r (σ j)).prod

/-- The qDRIFT expected unitary: finite average over all `L^r` sequences. -/
def qdriftExpectedUnitary {D : ℕ} (Hd : HamModel D) (t : ℝ) (r : ℕ) : Op D :=
  ∑ σ : Fin r → Fin Hd.L,
    (∏ j : Fin r, qdriftWeight Hd (σ j)) • qdriftProduct Hd t r σ

/-- Expected simulation error in the low-energy subspace: the paper's
`‖(V - E[U])Π_{≤Δ}‖` in Theorem 1 (p.5, Eq. (1)). -/
def qdriftExpectedError {D : ℕ} (Hd : HamModel D) (Δ t : ℝ) (r : ℕ) : ℝ :=
  ‖(HamiltonianEvolution Hd.H t - qdriftExpectedUnitary Hd t r) *
    lowEnergyProjector Hd.H Hd.hermitian Δ‖

/-- Error of a single sampled qDRIFT product. -/
def qdriftProductError {D : ℕ} (Hd : HamModel D) (Δ t : ℝ) (r : ℕ)
    (σ : Fin r → Fin Hd.L) : ℝ :=
  ‖(HamiltonianEvolution Hd.H t - qdriftProduct Hd t r σ) *
    lowEnergyProjector Hd.H Hd.hermitian Δ‖

/-- Probability (mass of sequences) that a single product exceeds error `ε`. -/
def qdriftFailureProb {D : ℕ} (Hd : HamModel D) (Δ t ε : ℝ) (r : ℕ) : ℝ :=
  ∑ σ : Fin r → Fin Hd.L,
    if ε < qdriftProductError Hd Δ t r σ
    then ∏ j : Fin r, qdriftWeight Hd (σ j) else 0

/-! ## Random permutation (Theorem 2) -/

/-- One random-permutation product: `r` blocks, each an ordered product of all
`L` terms with time step `t/(rL)`. -/
def randomPermutationProduct {D : ℕ} (Hd : HamModel D) (t : ℝ) (r : ℕ)
    (π : Fin r → Equiv.Perm (Fin Hd.L)) : Op D :=
  (List.ofFn fun s : Fin r =>
    (List.ofFn fun j : Fin Hd.L =>
      HamiltonianEvolution (Hd.terms ((π s) j)) (t / ((r : ℝ) * (Hd.L : ℝ)))).prod).prod

/-- Expected unitary of the random-permutation scheme. -/
def randomPermutationExpectedUnitary {D : ℕ} (Hd : HamModel D) (t : ℝ) (r : ℕ) : Op D :=
  (1 / ((Nat.factorial Hd.L : ℝ) ^ r)) •
    ∑ π : Fin r → Equiv.Perm (Fin Hd.L), randomPermutationProduct Hd t r π

/-- Expected error in the low-energy subspace (Theorem 2, Eq. (4)). -/
def randomPermutationExpectedError {D : ℕ} (Hd : HamModel D) (Δ t : ℝ) (r : ℕ) : ℝ :=
  ‖(HamiltonianEvolution Hd.H t - randomPermutationExpectedUnitary Hd t r) *
    lowEnergyProjector Hd.H Hd.hermitian Δ‖

/-- Error of a single sampled random permutation. -/
def randomPermutationProductError {D : ℕ} (Hd : HamModel D) (Δ t : ℝ) (r : ℕ)
    (π : Fin r → Equiv.Perm (Fin Hd.L)) : ℝ :=
  ‖(HamiltonianEvolution Hd.H t - randomPermutationProduct Hd t r π) *
    lowEnergyProjector Hd.H Hd.hermitian Δ‖

/-- Failure mass over the uniform distribution on permutations (Theorem 2, Eq. (5)). -/
def randomPermutationFailureProb {D : ℕ} (Hd : HamModel D) (Δ t ε : ℝ) (r : ℕ) : ℝ :=
  (1 / ((Nat.factorial Hd.L : ℝ) ^ r)) *
    ∑ π : Fin r → Equiv.Perm (Fin Hd.L),
      if ε < randomPermutationProductError Hd Δ t r π then 1 else 0

/-! ## Doubling order (Corollary 1) -/

/-- The doubling-order (symmetric) composition: the `r` permutation blocks are
played forward and then in reverse order with half time steps, the standard
second-order symmetrization used by the doubling-order construction of
Corollary 1 (p.7). -/
def doublingOrderProduct {D : ℕ} (Hd : HamModel D) (t : ℝ) (r : ℕ)
    (π : Fin r → Equiv.Perm (Fin Hd.L)) : Op D :=
  let block : Fin r → Op D := fun s =>
    (List.ofFn fun j : Fin Hd.L =>
      HamiltonianEvolution (Hd.terms ((π s) j)) (t / (2 * (r : ℝ) * (Hd.L : ℝ)))).prod
  (List.ofFn block).prod * (List.ofFn fun s : Fin r => block (Fin.rev s)).prod

/-- Expected unitary of the doubling-order scheme. -/
def doublingOrderExpectedUnitary {D : ℕ} (Hd : HamModel D) (t : ℝ) (r : ℕ) : Op D :=
  (1 / ((Nat.factorial Hd.L : ℝ) ^ r)) •
    ∑ π : Fin r → Equiv.Perm (Fin Hd.L), doublingOrderProduct Hd t r π

/-- Expected error of the doubling-order scheme (Corollary 1, Eq. (6)). -/
def doublingOrderExpectedError {D : ℕ} (Hd : HamModel D) (Δ t : ℝ) (r : ℕ) : ℝ :=
  ‖(HamiltonianEvolution Hd.H t - doublingOrderExpectedUnitary Hd t r) *
    lowEnergyProjector Hd.H Hd.hermitian Δ‖

/-- Failure mass of the doubling-order scheme. -/
def doublingOrderFailureProb {D : ℕ} (Hd : HamModel D) (Δ t ε : ℝ) (r : ℕ) : ℝ :=
  (1 / ((Nat.factorial Hd.L : ℝ) ^ r)) *
    ∑ π : Fin r → Equiv.Perm (Fin Hd.L),
      if ε < ‖(HamiltonianEvolution Hd.H t - doublingOrderProduct Hd t r π) *
        lowEnergyProjector Hd.H Hd.hermitian Δ‖ then 1 else 0

/-! ## Symmetry protection (Theorem 3) -/

/-- A finite subgroup of the unitary group, recorded as a `Finset` closed under
multiplication, star and containing `1`. -/
structure FiniteUnitaryGroup (D : ℕ) where
  carrier : Finset (Matrix.unitaryGroup (Fin D) ℂ)
  one_mem : 1 ∈ carrier
  mul_mem : ∀ a b, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  star_mem : ∀ a, a ∈ carrier → star a ∈ carrier
  card_pos : 0 < carrier.card

/-- Group averaging (twirl) of an operator over a finite unitary subgroup, the
symmetry-protection step of Theorem 3 (p.8). -/
def twirlUnitary {D : ℕ} (G : FiniteUnitaryGroup D) (V : Op D) : Op D :=
  (1 / (G.carrier.card : ℝ)) •
    ∑ g ∈ G.carrier, (g : Op D) * V * star (g : Op D)

/-- A symmetry-protected product: a base product formula averaged over the
symmetry group. -/
def symmetryProtectedProduct {D : ℕ} (Hd : HamModel D) (G : FiniteUnitaryGroup D)
    (t : ℝ) (r : ℕ) (π : Fin r → Equiv.Perm (Fin Hd.L)) : Op D :=
  twirlUnitary G (randomPermutationProduct Hd t r π)

/-- Expected error of the symmetry-protected scheme (Theorem 3, Eq. (8)). -/
def symmetryProtectedExpectedError {D : ℕ} (Hd : HamModel D) (G : FiniteUnitaryGroup D)
    (Δ t : ℝ) (r : ℕ) : ℝ :=
  ‖(HamiltonianEvolution Hd.H t -
      (1 / ((Nat.factorial Hd.L : ℝ) ^ r)) •
        ∑ π : Fin r → Equiv.Perm (Fin Hd.L), symmetryProtectedProduct Hd G t r π) *
    lowEnergyProjector Hd.H Hd.hermitian Δ‖

/-- Failure mass of the symmetry-protected scheme. -/
def symmetryProtectedFailureProb {D : ℕ} (Hd : HamModel D) (G : FiniteUnitaryGroup D)
    (Δ t ε : ℝ) (r : ℕ) : ℝ :=
  (1 / ((Nat.factorial Hd.L : ℝ) ^ r)) *
    ∑ π : Fin r → Equiv.Perm (Fin Hd.L),
      if ε < ‖(HamiltonianEvolution Hd.H t - symmetryProtectedProduct Hd G t r π) *
        lowEnergyProjector Hd.H Hd.hermitian Δ‖ then 1 else 0

/-! ## Power-law Hamiltonians (Theorem 4) -/

/-- The paper's `D`-dimensional power-law Hamiltonian data of Theorem 4 (p.8):
interaction strength `g`, `q` sites per dimension, each `H_l` containing at most
`M` interaction terms. -/
structure PowerLawModel (D : ℕ) extends HamModel D where
  /-- interaction strength `g` -/
  g : ℝ
  g_nonneg : 0 ≤ g
  /-- number `q` of sites per dimension -/
  q : ℕ
  q_pos : 0 < q
  /-- each term's strength is bounded by `g` -/
  term_strength_le : ∀ l, ‖terms l‖ ≤ g

/-- Trotter error of the power-law product formula. -/
def powerLawExpectedError {D : ℕ} (P : PowerLawModel D) (Δ t : ℝ) (r : ℕ) : ℝ :=
  qdriftExpectedError P.toHamModel Δ t r

/-! ## The explicit bounds displayed in the paper -/

/-- Theorem 1, Eq. (1) main term `L²(Δ+dkJ)²t²/ε`. -/
def thm1RExpMain (L : ℕ) (Δ d kJ t ε : ℝ) : ℝ :=
  (L : ℝ) ^ 2 * (Δ + d * kJ) ^ 2 * t ^ 2 / ε

/-- Theorem 1, Eq. (1) sub term `(LJ)^{4/3} M^{2/3} t^{4/3}/ε^{1/3}`. -/
def thm1RExpSub (L : ℕ) (J M t ε : ℝ) : ℝ :=
  Real.rpow ((L : ℝ) * J) (4 / 3) * Real.rpow M (2 / 3) * Real.rpow t (4 / 3) /
    Real.rpow ε (1 / 3)

/-- Theorem 1, Eq. (2) main term. -/
def thm1RProbMain (L n : ℕ) (Δ d kJ t ε χ : ℝ) : ℝ :=
  (L : ℝ) ^ 2 * (Δ + d * kJ) ^ 2 * t ^ 2 / ε ^ 2 * ((n : ℝ) + Real.log (1 / χ))

/-- Theorem 1, Eq. (2) sub term. -/
def thm1RProbSub (L n : ℕ) (J M t ε χ : ℝ) : ℝ :=
  Real.rpow ((L : ℝ) * J) (4 / 3) * Real.rpow M (2 / 3) * Real.rpow t (4 / 3) /
    Real.rpow ε (2 / 3) * Real.rpow ((n : ℝ) + Real.log (1 / χ)) (1 / 3)

/-- Theorem 2, Eq. (4) main term `L t^{1+1/p}(Δ+dkJ)^{1+1/p}/ε^{1/p}`. -/
def thm2RExpMain (L : ℕ) (p : ℝ) (Δ d kJ t ε : ℝ) : ℝ :=
  (L : ℝ) * Real.rpow t (1 + 1 / p) * Real.rpow (Δ + d * kJ) (1 + 1 / p) /
    Real.rpow ε (1 / p)

/-- Theorem 2, Eq. (4) sub term. -/
def thm2RExpSub (L : ℕ) (p : ℝ) (d kJ M J t ε : ℝ) : ℝ :=
  (L : ℝ) * Real.rpow t (1 + 1 / (2 * p + 1)) *
    Real.rpow (d * kJ * M * J ^ 2) (1 / 2 + 1 / (4 * p + 2)) /
    Real.rpow ε (1 / (2 * p + 1))

/-- Theorem 2, Eq. (5) main term. -/
def thm2RProbMain (L n : ℕ) (p : ℝ) (Δ d kJ t ε χ : ℝ) : ℝ :=
  Real.rpow ((L : ℝ) * t * (Δ + d * kJ)) ((2 * p + 2) / (2 * p + 1)) *
    Real.rpow ((n : ℝ) + Real.log (1 / χ)) (1 / (2 * p + 1)) /
    Real.rpow ε (2 / (2 * p + 1))

/-- Theorem 2, Eq. (5) sub term. -/
def thm2RProbSub (L n : ℕ) (p : ℝ) (d kJ M J t ε χ : ℝ) : ℝ :=
  Real.rpow ((L : ℝ) ^ 2 * t ^ 2 * d * kJ * M * J ^ 2) ((2 * p + 2) / (4 * p + 3)) *
    Real.rpow ((n : ℝ) + Real.log (1 / χ)) (1 / (4 * p + 3)) /
    Real.rpow ε (2 / (4 * p + 3))

/-- Corollary 1, Eq. (6) main term. -/
def cor1RExpMain (L : ℕ) (p : ℝ) (Δ d kJ t ε : ℝ) : ℝ :=
  Real.rpow ((L : ℝ) * t) (1 + 1 / (2 * p + 1)) *
    Real.rpow (Δ + d * kJ) (1 + 1 / (2 * p + 1)) /
    Real.rpow ε (1 / (2 * p + 1))

/-- Corollary 1, Eq. (6) sub term. -/
def cor1RExpSub (L : ℕ) (p : ℝ) (d kJ M J t ε : ℝ) : ℝ :=
  Real.rpow ((L : ℝ) * t) (1 + 1 / (4 * p + 3)) *
    Real.rpow (d * kJ * M * J ^ 2) ((2 * p + 2) / (4 * p + 3)) /
    Real.rpow ε (1 / (4 * p + 3))

/-- Theorem 3, Eq. (8): the full `Õ(·)` argument (sum of the four displayed
terms). -/
def thm3RMain (L : ℕ) (θ : ℝ) (Δ d kJ M J t ε : ℝ) : ℝ :=
  Real.rpow ((L : ℝ) * (Δ + J * d * kJ * (L : ℝ)) * t ^ 2 / ε) (1 / (1 + θ)) +
    Real.rpow ((L : ℝ) ^ 2 * M * J * d * kJ * t ^ 3 / ε) (1 / (2 + θ)) +
    (L : ℝ) * (Δ + J * d * kJ * (L : ℝ)) * Real.rpow t (3 / 2) /
      Real.rpow ε (1 / 2) +
    Real.rpow t (5 / 4) * (L : ℝ) * Real.rpow (J * d * kJ * M) (1 / 2) /
      Real.rpow ε (1 / 4)

/-- Theorem 4, Eq. (9) main term for the Trotter number. -/
def thm4RMain (L : ℕ) (p : ℝ) (Δ g q : ℝ) (t ε : ℝ) : ℝ :=
  Real.rpow t (1 + 1 / p) * Real.rpow (L : ℝ) (1 / p) *
    Real.rpow (Δ + g * q * Real.log q) (1 + 1 / p) / Real.rpow ε (1 / p)

/-- Theorem 4, Eq. (9) sub term for the Trotter number. -/
def thm4RSub (L : ℕ) (p : ℝ) (M g : ℝ) (t ε : ℝ) : ℝ :=
  Real.rpow t (1 + 1 / (2 * p + 1)) / Real.rpow ε (1 / (2 * p + 1)) *
    Real.rpow ((L : ℝ) * M * g) (1 / 2 + 1 / (4 * p + 2))

/-- Theorem 4, Eq. (9) main term for the gate complexity. -/
def thm4GMain (L : ℕ) (p : ℝ) (Δ g q : ℝ) (t ε : ℝ) : ℝ :=
  Real.rpow t (1 + 1 / p) * Real.rpow (L : ℝ) (1 / p + 1) *
    Real.rpow (Δ + g * q * Real.log q) (1 + 1 / p) / Real.rpow ε (1 / p)

/-- Theorem 4, Eq. (9) sub term for the gate complexity. -/
def thm4GSub (L : ℕ) (p : ℝ) (M g : ℝ) (t ε : ℝ) : ℝ :=
  (L : ℝ) * Real.rpow t (1 + 1 / (2 * p + 1)) / Real.rpow ε (1 / (2 * p + 1)) *
    Real.rpow ((L : ℝ) * M * g) (1 / 2 + 1 / (4 * p + 2))

end Qatlib.Papers.LowEnergySim23.MainResults.Framework
