/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.HamDecodedQI25.MainResults.TannerSyndrome
import Qatlib.Papers.HamDecodedQI25.MainResults.BellBasis

set_option backward.isDefEq.respectTransparency false

/-! Statement bank for
"Hamiltonian Decoded Quantum Interferometry"
(arXiv:2510.07913v1, 2025).

This file records faithful `Prop` statements for the claims whose full
formalisation meets substantive obstacles. Three cores are proved in
this block: `TannerSyndrome.mulVec_eq_card_inter` and
`TannerSyndrome.syndrome_nonzero_of_unique_neighbor` (c034, Lemma 52
and c035, Corollary 53), and `BellBasis.bell_orthonormal` with its
entry/inner-product lemmas (c030, Lemma 46; c032, Lemma 48 shares the
same shape for the Weyl family over `𝔽_p`).

The remaining claims are recorded as abstract statements:
- c001 (Theorem 1, HDQI prepares `ρ_f(H)` for nearly independent
  Hamiltonians): the density normalization core plus constant logical
  dimension and polynomial time; the circuit semantics of HDQI are
  abstracted away.
- c002 (Theorem 2, classical stabilizer sampling): `ρ_f(H)` admits a
  convex decomposition into stabilizer states in time `2^k·m²`; the
  stabilizer formalism is abstracted to given state matrices.
- c003 (Theorem 3, Gibbs state preparation): existence of a polynomial
  of degree `≤ 1.12β‖H‖ + 0.648 ln(12/ε)` whose normalized square
  approximates the Gibbs state; the trace distance is abstracted as a
  functional.
- c004 (Theorem 4, semicircle law): convergence of the optimal energy
  density to the semicircle value under `2ℓ+1 < d⊥`; the random-code
  ensemble and the variational optimization are abstracted away.
- c008/c014 (Theorems 12/22, main reductions): single-oracle-call
  polynomial-time reductions to the decoding oracle, commuting and
  general case.
- c022 (Theorem 31, MPS pilot-state preparation): time
  `poly(n)·2^{O(ℳ)}` for component size `ℳ`.
- c025 (Corollary 35, spin-glass Gibbs sampling): the
  `n^{O(log n)} + poly(n)` algorithmic shape with `exp(-Ω(n))`
  accuracy at constant temperature.
- c031 (Theorem 47, coherent Bell measurement): a unitary mapping the
  Bell expansion onto symplectic labels; the Clifford synthesis and
  gate count are abstracted away.
- c032 (Lemma 48, Weyl–Bell orthonormality): the exact shape of the
  proved `bell_orthonormal` with the Weyl Frobenius orthogonality as a
  hypothesis (the Weyl trace calculation is the abstracted part).
- c042 (Theorem 64, polynomial approximation of the exponential):
  existence of a degree-`m` polynomial with relative error `≤ ε/6` on
  `[-1, 1]` once `m ≥ 1.12βK + 0.648 ln(12/ε)`.

The LCHS/QSVT query-machine group (c039, c040, c041), the spin-glass
threshold group (c005, c024, c026), the symmetric-function and
representation-theory group (c006, c011, c013, c015–c021, c023,
c043–c050) and the coding-theory expansion group (c036–c038) are
documented in the PR; they need machinery absent from Mathlib and this
repository (quantum query models, polymer models, representation
rings, expander mixing).

No axiom, no `admit`, no `native_decide`.
-/
set_option autoImplicit false

open Filter Topology
open scoped Matrix

namespace Qatlib.Papers.HamDecodedQI25.MainResults

/-! ## Claim statements -/

/-- **c001 (Theorem 1, nearly independent Hamiltonians), shape**: for a
commuting Pauli Hamiltonian with nonnegative spectrum functional `f`,
the density matrix `ρ_f(H) = f(H)/Tr[f(H)]` has well-defined
normalization (eigenvalue weights summing to one), the logical
(symplectic) dimension is bounded by a constant `K`, and the HDQI
preparation time is polynomial in `n`. The circuit semantics of HDQI
are abstracted away. -/
def c001_statement {d : ℕ} (spec : Fin d → ℝ) (f : ℝ → ℝ)
    (logical time : ℕ → ℕ) : Prop :=
  (∀ i, 0 ≤ f (spec i)) → 0 < ∑ i, f (spec i) →
    ∑ i, f (spec i) / ∑ j, f (spec j) = 1 ∧
      ∃ K c : ℕ, (∀ n, logical n ≤ K) ∧ (∀ n, 1 ≤ n → time n ≤ n ^ c)

/-- **c002 (Theorem 2, classical sampling), shape**: the density matrix
`ρ_f(H)` of a nearly independent Hamiltonian admits a convex
decomposition into at most as many stabilizer states as indexed, with
sampling time `O(2^k m²)` where `k` is the number of logical bits and
`m` the number of terms. The stabilizer formalism enters only through
the given state matrices `σ`. -/
def c002_statement {d ι : ℕ} (σ : Fin ι → Matrix (Fin d) (Fin d) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (k m time : ℕ) : Prop :=
  ∃ p : Fin ι → ℝ, (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1 ∧
    ρ = ∑ a, p a • σ a ∧ time ≤ 2 ^ k * m ^ 2

/-- **c003 (Theorem 3, Gibbs state preparation), shape**: there exists a
real polynomial `P` of degree at most
`1.12 β ‖H‖ + 0.648 ln(12/ε)` whose squared-normalized Hamiltonian
state approximates the Gibbs state to error `ε`; the trace distance to
the Gibbs state is abstracted as the functional `tdist`. -/
def c003_statement (β hnorm ε : ℝ) (tdist : Polynomial ℝ → ℝ) : Prop :=
  0 < ε →
    ∃ P : Polynomial ℝ,
      P.natDegree ≤ 1.12 * β * hnorm + 0.648 * Real.log (12 / ε) ∧ tdist P ≤ ε

/-- **c004 (Theorem 4, semicircle law for HDQI), shape**: for degree `ℓ`
with `2ℓ + 1 < d⊥` (the symplectic minimum distance), the optimal
energy density of the polynomial Hamiltonian state converges, as
`m → ∞` with `ℓ/m` fixed, to the semicircle-distribution value
`limit`; the random-code ensemble and the variational optimization are
abstracted away. -/
def c004_statement (energy : ℕ → ℝ) (limit : ℝ) (ell dperp : ℕ) : Prop :=
  2 * ell + 1 < dperp ∧ Tendsto energy atTop (𝓝 limit)

/-- **c008 (Theorem 12, main reduction, commuting case), shape**: given a
weight-`ℓ` decoding oracle, Algorithm 1 prepares `ρ_P(H)` for any
polynomial of degree `≤ ℓ` with a single oracle call in polynomial
time; the algorithm semantics are abstracted to the time bound and
call count. -/
def c008_statement (time : ℕ → ℕ) (calls deg ell : ℕ) : Prop :=
  deg ≤ ell ∧ calls = 1 ∧ ∃ c : ℕ, ∀ n, 1 ≤ n → time n ≤ n ^ c

/-- **c014 (Theorem 22, main reduction, general case), shape**: given a
weight-`ℓ` decoding oracle and an MPS pilot state for the
anticommutation graph, the general-case reduction prepares `ρ_P(H)`
for any degree-`ℓ` polynomial with a single oracle call in polynomial
time. -/
def c014_statement (time : ℕ → ℕ) (calls deg ell : ℕ) (pilot : Prop) : Prop :=
  pilot ∧ deg ≤ ell ∧ calls = 1 ∧ ∃ c : ℕ, ∀ n, 1 ≤ n → time n ≤ n ^ c

/-- **c022 (Theorem 31, MPS pilot-state preparation), shape**: if every
connected component of the anticommutation graph has at most `M`
vertices, the pilot state is preparable in time `poly(n)·2^{O(M)}`. -/
def c022_statement (time : ℕ → ℕ) (M : ℕ) : Prop :=
  ∃ c C : ℕ, ∀ n, 1 ≤ n → time n ≤ n ^ c * 2 ^ (C * M)

/-- **c025 (Corollary 35, Gibbs sampling of semiclassical spin glasses),
shape**: for a `p`-semiclassical spin glass with `p < 1/K²`, there is a
constant threshold `β*` below which a classical preprocessing of
`n^{O(log n)}` plus `poly(n)` quantum time prepares the Gibbs state to
accuracy `exp(-Ω(n))`. -/
def c025_statement (p K : ℝ) (timePrep quantumTime tdist : ℕ → ℝ) : Prop :=
  (0 < p ∧ 0 < K ∧ p < 1 / K ^ 2) →
    ∃ βstar : ℝ, 0 < βstar ∧
      ∃ c d C c' : ℝ, 0 < C ∧ 0 < c ∧ 0 < c' ∧
        ∀ n : ℕ, 1 ≤ n →
          timePrep n ≤ n ^ (d * Real.log n) ∧ quantumTime n ≤ n ^ c ∧
            tdist n ≤ C * Real.exp (-(c' * n))

/-- **c031 (Theorem 47, coherent Bell measurement), shape**: there is a
unitary `U` mapping the Bell expansion
`∑_P c_P (P ⊗ I)|Φ^n⟩` onto the symplectic-label register
`∑_P c_P |symp(P)⟩` with the same coefficients; the Clifford synthesis
of `U` from `H, CX` gates and its `poly(n)` gate count are abstracted
away. -/
def c031_statement {d : ℕ} (v w : Fin d → ℂ) : Prop :=
  ∃ U : Matrix (Fin d) (Fin d) ℂ, U * Uᴴ = 1 ∧ U.mulVec v = w

/-- **c032 (Lemma 48, Weyl–Bell basis is orthonormal), shape**: the
Weyl operators `W(u)` over `𝔽_p^{2n}` satisfy the Frobenius
orthogonality `⟨W(a), W(b)⟩_HS = d δ_{a,b}`, hence (by
`BellBasis.bell_orthonormal`) the Weyl–Bell states
`(W(a) ⊗ I)|Φ⟩` form an orthonormal family; the Weyl-specific trace
calculation is the hypothesis `hW` and is abstracted. -/
def c032_statement {d : ℕ} {ι : Type} [DecidableEq ι] [Fintype ι]
    (W : ι → Matrix (Fin d) (Fin d) ℂ)
    (_hW : ∀ a b, ∑ p : Fin d × Fin d, starRingEnd ℂ (W a p.1 p.2) * W b p.1 p.2
      = if a = b then (d : ℂ) else 0) (a b : ι) : Prop :=
  ∀ _hd : d ≠ 0, ∑ p : Fin d × Fin d,
      starRingEnd ℂ (BellBasis.bellState d (W a) p) * BellBasis.bellState d (W b) p = if a = b then 1 else 0

/-- **c042 (Theorem 64, polynomial approximation of the exponential),
shape**: for `K, β ∈ ℝ₊` and rate `a ≤ βK`, once
`m ≥ 1.12βK + 0.648 ln(12/ε)` there is a real polynomial of degree at
most `m` approximating `e^{-au}` on `[-1, 1]` to relative error
`ε/6`. -/
def c042_statement (K β ε a : ℝ) (m : ℕ) : Prop :=
  (0 < K ∧ 0 < β ∧ 0 < ε ∧ 0 < a ∧ a ≤ β * K) →
    (1.12 * β * K + 0.648 * Real.log (12 / ε) ≤ m →
      ∃ P : Polynomial ℝ, P.natDegree ≤ m ∧
        ∀ u : ℝ, -1 ≤ u → u ≤ 1 →
          |P.eval u - Real.exp (-(a * u))| ≤ (ε / 6) * Real.exp (-(a * u)))

end Qatlib.Papers.HamDecodedQI25.MainResults
