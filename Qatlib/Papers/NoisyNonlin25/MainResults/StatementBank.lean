/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Qatlib.Papers.NoisyNonlin25.MainResults.CommutatorBounds

set_option backward.isDefEq.respectTransparency false

/-! Statement bank for
"Quantum simulation of a noisy classical nonlinear dynamics"
(arXiv:2507.06198, 2025).

Two cores are proved in this block (see `CommutatorBounds`):

- c006 (Corollary 1): `commutator_bound_kappa1`, the Young/AM-GM
  reduction of the square-root commutator bound to
  `⟨ψ|[A,B+C]|ψ⟩ ≤ α₂ + κ₁ α₁`, at B-.
- c019 (Proposition 4): `diagonal_dominance_psd`, hermitian
  diagonal dominance `Y − X ⪰ 0` by the paper's ordered double-sum
  AM-GM argument, at B-.

The remaining eighteen claims are recorded below as faithful `Prop`
shapes. Their obstacles are substantive and shared:

- Fock-space second quantization (c003, c004, c005, c007, c008,
  c018, c020): the number-conserving sector `F₀`, the diagonal
  dissipation operator `A` in the occupation basis, and the
  creation/annihilation algebra `a†`, `a` with the cubic coupling
  `c_ijk` have no layer in Mathlib or either repository; the
  anticommutation/normal-order identities behind Lemma 1 and
  Propositions 3/5 are exactly this missing algebra.
- Kolmogorov evolution and analysis (c009–c016): existence and
  differentiability of the trajectory `ψ(t)`, moment bounds
  `f_p(t)`, spectral cutoffs `Π_k`, and the convergence of the
  truncated trajectories require an infinite-dimensional
  ODE/SDE regularity layer absent from both repositories.
- Quantum runtime accounting (c001, c002): the algorithm of
  Theorem 1 and the circuit-encoding SDE of Theorem 2 count
  block-encodings, amplitude estimation, and truncated-operator
  simulation; no circuit-model query-complexity framework exists.
- Sparse-matrix structure (c017): the row/column sparsity
  `4 s k λ₁⁻¹` of `B_k + C_k` is Fock-basis combinatorics on top
  of the missing second-quantization layer.

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false

namespace Qatlib.Papers.NoisyNonlin25.MainResults

/-! ## Shared shapes -/

/-- Polynomial-time cost: `T` is bounded by a fixed monomial in `n`. -/
def polyTimeIn (T n : ℝ) : Prop :=
  ∃ (C k : ℝ), 0 < C ∧ T ≤ C * n ^ k

/-- Exponential cost: `T` is bounded by `exp (C · e)`; the paper's
runtime is exponential in `q⁻¹‖x‖²_λ`. -/
def expIn (T e : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ T ≤ Real.exp (C * e)

/-! ## Claim statements -/

/-- **c001 (Theorem 1), simulation shape**: a quantum algorithm
outputs `out` within additive error `err` of the expected value
`v(t,x)` of the observable `u₀`, with runtime polynomial in
`polyvar = log N · t · err⁻¹ · J · s · λ₁⁻¹ · q` and exponential
in `expovar = q⁻¹‖x‖²_λ`. -/
def c001_statement (out v err runtime polyvar expovar : ℝ) : Prop :=
  0 < err ∧ |out - v| ≤ err
    ∧ polyTimeIn runtime polyvar ∧ expIn runtime expovar

/-- **c002 (Theorem 2), circuit-encoding shape**: for an n-qubit
circuit `U` with `m` gates, the encoded linear divergence-free SDE
has `N = (m+1)·2ⁿ` variables, drift strength `J = O(m)`, and the
amplitude `⟨0ⁿ|U|0ⁿ⟩` is approximated by `v(1,x)` to `1/10`; the
initial vector has a single nonzero and `q⁻¹‖x‖²_λ = 1`. -/
def c002_statement (amp v : ℝ) (n m : ℕ) (N J qnorm : ℝ) : Prop :=
  |amp - v| ≤ 1 / 10 ∧ N = (m + 1) * (2 : ℝ) ^ n
    ∧ (∃ C : ℝ, 0 < C ∧ J ≤ C * m) ∧ qnorm = 1

/-- **c003 (Lemma 1), anti-hermiticity shape**: divergence-freeness
of the drift makes `B` and `C` anti-hermitian; the paper's Eq. (22)
normal form `C = (q/2)^{1/2} Σ (λᵢλⱼλₖ)^{-1/2} λᵢ c_ijk
(aⱼ†aₖ†aᵢ − aᵢ†aₖaⱼ)` is the missing Fock-space layer. -/
def c003_statement {I : Type*} [Fintype I] (B C : Matrix I I ℂ) : Prop :=
  Matrix.conjTranspose B = -B ∧ Matrix.conjTranspose C = -C

/-- **c004 (Lemma 2), off-diagonal bound shape**: for all
`ψ, φ ∈ F₀`, `|⟨φ|B+C|ψ⟩| ≤ γ √(⟨ψ|A|ψ⟩ ⟨φ|A²|φ⟩)` with
`γ = 2 q^{1/2} s J λ₁⁻² (1 + λ₁^{1/2} q^{-1/2})`. -/
def c004_statement (phiBpsi psiA phiA2 q s J lam1 : ℝ) : Prop :=
  0 < q ∧ 0 < lam1
    ∧ |phiBpsi| ≤ 2 * Real.sqrt q * s * J / lam1 ^ 2
        * (1 + Real.sqrt lam1 / Real.sqrt q) * Real.sqrt (psiA * phiA2)

/-- **c005 (Lemma 3), square-root commutator shape**:
`⟨ψ|[A,B+C]|ψ⟩ ≤ 2 J s λ₁^{-1/2}(1 + 4 √q λ₁^{-1/2})
√(⟨ψ|A|ψ⟩ ⟨ψ|A²|ψ⟩)`; this is exactly the hypothesis consumed by
`CommutatorBounds.commutator_bound_kappa1` (c006). -/
def c005_statement (x psiA psiA2 J s lam1 q : ℝ) : Prop :=
  x ≤ 2 * J * s / Real.sqrt lam1 * (1 + 4 * Real.sqrt q / Real.sqrt lam1)
      * Real.sqrt (psiA * psiA2)

/-- **c007 (Lemma 4), order-p commutator shape**: for every integer
`p ≥ 2` there is `κ_p ≤ poly(s, J, λ₁⁻¹, λ_N)` with
`⟨ψ|[A^p,B+C]|ψ⟩ ≤ ⟨ψ|A^{p+1}|ψ⟩ + κ_p ⟨ψ|A^p|ψ⟩`. -/
def c007_statement (p comm ap ap1 polybound : ℝ) : Prop :=
  2 ≤ p ∧ 0 ≤ polybound ∧ 0 ≤ ap
    ∧ ∃ κ : ℝ, κ ≤ polybound ∧ comm ≤ ap1 + κ * ap

/-- **c008 (Lemma 5), relative-bound shape**: there is
`ω_p < ∞` (depending on `p, N, J, λ₁, λ_N`) with
`‖A^p (B+C) ψ‖ ≤ ω_p ‖A^{p+3/2} ψ‖` for all `ψ ∈ F₀`. -/
def c008_statement (lhs rhs : ℝ) : Prop :=
  ∃ ω : ℝ, 0 ≤ ω ∧ lhs ≤ ω * rhs

/-- **c009 (Theorem 3), regularization shape**: for `ψ₀` with finite
`A⁸`-moment there is a differentiable trajectory `ψ` with
`ψ(0) = ψ₀` solving the Kolmogorov equation `dψ/dt = (−A+B+C)ψ`
(`rhs t` abstracts the generator applied at `ψ(t)`); the
`A³`-moment finiteness and truncation clauses ride on the same
analytic layer. -/
def c009_statement (psi0 : ℝ) (psi rhs : ℝ → ℝ) : Prop :=
  psi 0 = psi0 ∧ ∀ t : ℝ, 0 ≤ t → HasDerivAt psi (rhs t) t

/-- **c010 (Lemma 6), moment-bound shape**: `f_p(t)` obeys Eq. (31)
`f_p(t) ≤ max(f_p(0), (κ_p)^p f_0(0))` and the integral recursion
Eq. (32), abstracted here as `int ≤ intbound`. -/
def c010_statement (fpt fp0 kappow f00 int intbound : ℝ) : Prop :=
  fpt ≤ max fp0 (kappow * f00) ∧ int ≤ intbound

/-- **c011 (Corollary 2), projection-error shape**:
`‖(I − Π_k) ψ_ℓ(t)‖² ≤ (⟨ψ(0)|A|ψ(0)⟩ + κ₁⟨ψ(0)|ψ(0)⟩)/k`. -/
def c011_statement (projErr2 a0 n0 kap1 k : ℝ) : Prop :=
  0 < k ∧ projErr2 ≤ (a0 + kap1 * n0) / k

/-- **c012 (Lemma 7), truncated-moment shape**: `h_0(t)` obeys
Eq. (38) `h_0(t) ≤ 12 γ k^{-1/2}(⟨ψ(0)|A|ψ(0)⟩ + κ₁⟨ψ(0)|ψ(0)⟩)`,
and for `p ≥ 1`, `h_p(t) ≤ e^{2κ_p t} k^{-1/2}
poly(s,J,λ₁⁻¹,λ_N) · max_{p'≤2p+2}⟨ψ(0)|A^{p'}|ψ(0)⟩` (Eq. (39),
with the polynomial and the maximum moment abstracted). -/
def c012_statement (h0t a0 n0 gamma k hp kap t polyterm maxmoment : ℝ) : Prop :=
  0 < k ∧ 0 ≤ t
    ∧ h0t ≤ 12 * gamma / Real.sqrt k * (a0 + n0)
    ∧ hp ≤ Real.exp (2 * kap * t) / Real.sqrt k * polyterm * maxmoment

/-- **c013 (Corollary 3), convergence shape**: for `p ≥ 1` with all
`A^{p'}`-moments finite (`p' ≤ 2p+2`), the truncated trajectories
converge: `maxnorm k = max_{τ∈[0,t]}‖A^{p/2}(ψ_k(τ) − ψ(τ))‖ → 0`,
and the pointwise error obeys the Eq. (46) bound
`‖ψ_k(t) − ψ(t)‖² ≤ 12 γ k^{-1/2}(⟨ψ(0)|A|ψ(0)⟩ +
κ₁⟨ψ(0)|ψ(0)⟩)`. -/
def c013_statement (maxnorm : ℕ → ℝ) (err2 a0 n0 gamma k : ℝ) : Prop :=
  Filter.Tendsto maxnorm Filter.atTop (nhds 0)
    ∧ 0 < k ∧ err2 ≤ 12 * gamma / Real.sqrt k * (a0 + n0)

/-- **c014 (Lemma 8), differentiability shape**: the trajectory
`ψ` of Corollary 3 is differentiable and solves the Kolmogorov
equation `dψ/dt = (−A+B+C)ψ` for all `t ≥ 0` (`rhs t` abstracts
the generator applied at `ψ(t)`). -/
def c014_statement (psi rhs : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → HasDerivAt psi (rhs t) t

/-- **c015 (Proposition 1), generator-convergence shape**:
`(−A+B+C)ψ(t) = lim_k (−A+B+C)ψ_k(t)`, i.e. the generator applied
to the truncated trajectories converges to its value on `ψ(t)`. -/
def c015_statement (val : ℝ) (seq : ℕ → ℝ) : Prop :=
  Filter.Tendsto seq Filter.atTop (nhds val)

/-- **c016 (Proposition 2), truncation-commutator shape**:
`lim_k ‖(B+C)ψ_k(t) − Π_k(B+C)Π_k ψ_k(t)‖ = 0`, with `seq k`
the normed commutator defect of the truncated evolution. -/
def c016_statement (seq : ℕ → ℝ) : Prop :=
  Filter.Tendsto seq Filter.atTop (nhds 0)

/-- **c017 (Lemma 9), sparsity shape**: the matrix of `B_k + C_k`
has at most `nnz ≤ 4 s k λ₁⁻¹` nonzeros in every row and column,
and `‖B_k + C_k‖ ≤ γ k^{3/2}` (Eq. (71)). -/
def c017_statement (nnz k s lam1 normop gamma : ℝ) : Prop :=
  0 < k ∧ 0 < lam1
    ∧ nnz ≤ 4 * s * k / lam1 ∧ normop ≤ gamma * k * Real.sqrt k

/-- **c018 (Proposition 3), coupling bound shape**: for any triple
of distinct indices, `|c_ijk| λ_i^{1/2}(λ_jλ_k)^{-1/2}
|λ_j + λ_k − λ_i| ≤ 4 J λ₁⁻¹ (λ_iλ_jλₖ)^{1/2}` (Eq. (111)). -/
def c018_statement (cijk li lj lk J lam1 : ℝ) : Prop :=
  0 < lam1 ∧ 0 < li ∧ 0 < lj ∧ 0 < lk
    ∧ |cijk| * Real.sqrt li / Real.sqrt (lj * lk) * |lj + lk - li|
        ≤ 4 * J / lam1 * Real.sqrt (li * lj * lk)

/-- **c020 (Proposition 5), dilation-order shape**: for the
hermitian pair `g = γ(aⱼ†aₖ†aᵢ + aᵢ†aₖaⱼ)` and
`h = λᵢ aᵢ†aᵢ + λⱼ aⱼ†aⱼ + λₖ aₖ†aₖ` and every `β > 0`,
`g ≤_d ½|γ| λ₁^{-3/2}(β h² + β⁻¹ h)` in the quadratic-form order
(the finite-dimensional shadow of the paper's `≤_d`). -/
def c020_statement {I : Type*} [Fintype I] (g h : Matrix I I ℂ)
    (gam lam1 beta : ℝ) : Prop :=
  0 < beta ∧ 0 < lam1
    ∧ ∀ v : I → ℂ, 0 ≤ (∑ m, star (v m)
        * Matrix.mulVec (g - ((1 / 2 * |gam| / (lam1 * Real.sqrt lam1)) •
            ((beta • (h * h)) + (beta⁻¹ • h)))) v m).re

end Qatlib.Papers.NoisyNonlin25.MainResults
