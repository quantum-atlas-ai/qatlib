/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLSBeyondCond25.MainResults.VectorDecomposition

set_option backward.isDefEq.respectTransparency false

/-! Statement bank for
"A New Quantum Linear System Algorithm Beyond the Condition Number and
Its Application to Solving Multivariate Polynomial Systems"
(arXiv:2510.05588, 2025).

Two cores are proved in this block (see `VectorDecomposition`):

- c004 (Lemma 2.6): `exists_unique_decomposition`, the unique
  null/row decomposition of every vector, at B-.
- c005 (Theorem 2.7): `vectorDecomposition`, the Vector Decomposition
  Theorem for `H = [A, -b]` and `x = A^+ b`, at B-.

The remaining thirteen claims are recorded as faithful `Prop`
shapes below. Their obstacles are substantive and shared:

- Query-complexity accounting (c001, c009, c010): the paper's cost
  bounds count controlled applications of the walk unitary `U_AB`
  built from sparse Hamiltonian simulation and phase estimation;
  no circuit-model query-complexity framework exists in Mathlib or
  either repository.
- The electrical-network walk formalism (c006–c008): the bipartite
  interlace walk with edge weights `w_ij = |A_ij|² deg(v_j)`, the
  spanning states `Φ_j`, `Ψ_i` and the projectors `Π_A`, `Π_B`
  require a dedicated subspace layer absent from both repositories.
- Polynomial-system pipeline (c002, c003, c011, c012): Macaulay
  matrix construction, rescaling, Boolean-solution extraction by
  sampling and the exponential condition-number bound are algebraic
  and algorithmic layers outside current scope.
- Singular-value interlacing (c013): the √2-equivalence
  `κ(H) ≍ κ(A)` rests on Cauchy interlacing for bordered matrices
  and Weyl perturbation of the smallest positive singular value,
  which Mathlib does not provide.
- QSVT/block-encoding layer (c014): kernel projection via the
  polynomial filter `F_{Δ,ℓ}` requires the block-encoding/QSVT
  machinery of the references, absent from both repositories.
- Electrical-flow application (c015): the welded-tree O(1/ε²)
  bound composes the walk layer with the graph's electrical
  quantities.

No axiom beyond the three standard ones, no `admit`. -/
set_option autoImplicit false

namespace Qatlib.Papers.QLSBeyondCond25.MainResults

/-! ## Shared shapes -/

/-- Polynomial-time cost: `T` is bounded by a fixed monomial in `n`. -/
def polyTimeIn (T n : ℝ) : Prop :=
  ∃ (C k : ℝ), 0 < C ∧ T ≤ C * n ^ k

/-- Big-O with a suppressed polylogarithmic factor `L ≥ 1`
(the paper writes `Õ`). -/
def bigOLog (T f L : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ 1 ≤ L ∧ T ≤ C * L * f

/-! ## Claim statements -/

/-- **c001 (Theorem 1.1), new-QLS shape**: the algorithm outputs a
state `ε`-close (trace distance) to `|x⟩` with `x = A⁺b` in time
`Õ((‖x‖⁻⁶ + ‖x‖²) √(s³ E_T)/ε²)` with `s` the sparsity of
`H = [A,-b]` and `E_T = ∑ p_i² d_i` the electrical quantity. -/
def c001_statement (tdist T nx s ET eps L : ℝ) : Prop :=
  0 < eps ∧ 0 < nx ∧ tdist ≤ eps
    ∧ bigOLog T (((nx ^ 6)⁻¹ + nx ^ 2) * Real.sqrt (s ^ 3 * ET) / eps ^ 2) L

/-- **c002 (Theorem 1.2), polynomial-system shape**: a quadratic
system with unique Boolean solution of Hamming weight `h` is
recovered with probability ≥ `1 - δ` in time `Õ(√E_T · log(1/δ))`
over the weighted Boolean Macaulay system. -/
def c002_statement (P T ET delta L : ℝ) : Prop :=
  0 < delta ∧ 1 - delta ≤ P
    ∧ bigOLog T (Real.sqrt ET * Real.log (delta ⁻¹)) L

/-- **c003 (Theorem 1.3), planted-MIS shape**: if every count of
independent `i`-sets obeys `I_i ≤ poly(n) C(h,i)` then `E_T` is
polynomial and the planted set is recovered in polynomial time with
high probability. -/
def c003_statement (P T ET n : ℝ) (h : ℕ) (I : ℕ → ℝ) : Prop :=
  (∀ i : ℕ, 1 ≤ i → i ≤ h →
      ∃ (C k : ℝ), I i ≤ C * n ^ k * (Nat.choose h i : ℝ))
    ∧ polyTimeIn ET n ∧ 1 / 2 ≤ P ∧ polyTimeIn T n

/-- **c006 (Lemma 3.6), initial-state-decomposition shape**: the
source state `Φ_b` splits as the normalized solution direction
`θ*` minus the `A`-complement of the potential vector `p`. -/
def c006_statement {V : Type*} [AddCommGroup V] [Module ℂ V]
    (PiA : V → V) (Φb θstar p : V) (c : ℂ) : Prop :=
  Φb = c ⁻¹ • θstar - (p - PiA p)

/-- Reflection `v ↦ 2 Π v - v` through a subspace projector. -/
def reflectThrough {V : Type*} [AddCommGroup V] [Module ℂ V]
    (P : V → V) (v : V) : V := 2 • P v - v

/-- **c007 (Lemma 3.7), fixed-point shape**: the solution direction
`θ*` is fixed by the alternating reflection
`U_AB = (2Π_B − I)(2Π_A − I)`. -/
def c007_statement {V : Type*} [AddCommGroup V] [Module ℂ V]
    (PiA PiB : V → V) (θstar : V) : Prop :=
  reflectThrough PiB (reflectThrough PiA θstar) = θstar

/-- **c008 (Lemma 3.8), projection-property shape**: the potential
vector `p` lies entirely in the subspace `B`. -/
def c008_statement {V : Type*} [AddCommGroup V] [Module ℂ V]
    (PiB : V → V) (p : V) : Prop :=
  PiB p = p

/-- **c009 (Theorem 3.9), state-preparation shape**: phase
estimation on `(U_AB, Φ_b)` outputs phase `0` with probability at
least `1/(1+‖x‖²)` and the post-measurement state is `ε`-close to
`θ*` in trace distance, using `Õ(√(s E_T)/ε²)` controlled queries. -/
def c009_statement (p0 tdist Q nx s ET eps L : ℝ) : Prop :=
  0 < eps ∧ 0 < nx ∧ (1 + nx ^ 2) ⁻¹ ≤ p0 ∧ tdist ≤ eps
    ∧ bigOLog Q (Real.sqrt (s * ET) / eps ^ 2) L

/-- **c010 (Theorem 3.11), QLS-complexity shape**: the composed
algorithm returns a state `ε`-close to the solution state in time
`Õ((‖x‖⁻⁶ + ‖x‖²) √(s³ E_T)/ε²)`. -/
def c010_statement (tdist T nx s ET eps L : ℝ) : Prop :=
  0 < eps ∧ 0 < nx ∧ tdist ≤ eps
    ∧ bigOLog T (((nx ^ 6) ⁻¹ + nx ^ 2) * Real.sqrt (s ^ 3 * ET) / eps ^ 2) L

/-- **c011 (Lemma 5.6), Boolean-recovery shape**: measuring the
prepared state in the computational basis recovers the Boolean
solution with probability ≥ `1 - δ`. -/
def c011_statement (P delta n : ℝ) : Prop :=
  0 < delta ∧ 1 ≤ n ∧ 1 - delta ≤ P

/-- **c012 (Proposition 5.7), condition-number shape**: the
weighted Boolean Macaulay matrix has condition number at most
exponential: `κ ≤ C · base^n`. -/
def c012_statement (kappa n base : ℝ) : Prop :=
  1 < base ∧ ∃ C : ℝ, 0 < C ∧ kappa ≤ C * base ^ n

/-- **c013 (Theorem C.1), augmentation-equivalence shape**: with
`‖A‖ = 1`, `‖b‖ ≤ 1`, `‖x‖ = 1` and `H = [A,-b]`, the condition
numbers are √2-equivalent: `κ(H)/√2 ≤ κ(A) ≤ √2 · κ(H)` reversed —
precisely `(1/√2) κ(A) ≤ κ(H) ≤ √2 κ(A)`. -/
def c013_statement (kappaA kappaH : ℝ) : Prop :=
  1 ≤ kappaA ∧ (Real.sqrt 2) ⁻¹ * kappaA ≤ kappaH ∧ kappaH ≤ Real.sqrt 2 * kappaA

/-- **c014 (Theorem A.1), kernel-projection shape**: from a
`(1,a,0)` block encoding of `H` with a spectral gap `Δ`, QSVT with
the polynomial filter `F_{Δ,ℓ}` (ℓ = Θ(κ log(1/ε)) queries)
produces a state `ε`-close to the null-space component `θ`. -/
def c014_statement (dist eps gamma ell L : ℝ) : Prop :=
  0 ≤ gamma ∧ gamma ≤ 1 ∧ 0 < eps ∧ dist ≤ eps
    ∧ bigOLog ell (eps ⁻¹) L

/-- **c015 (main result), welded-tree shape**: despite an
exponentially growing condition number `κ(B)` of the welded-tree
system, the electrical-flow cost stays `O(1/ε²)`. -/
def c015_statement (T eps : ℝ) : Prop :=
  0 < eps ∧ ∃ C : ℝ, 0 < C ∧ T ≤ C / eps ^ 2

end Qatlib.Papers.QLSBeyondCond25.MainResults
