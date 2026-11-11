/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OneDimSim15.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# OneDimSim15 — Section V and Appendices C/D: eigenstate preparation

Claims `c004`-`c006`, `c019`-`c021` of the fixed source arXiv:1503.06319v2:

* Lemma 9 (p. 12, Eq. (C2)): the Gaussian state approximates `|psi_0^d>`;
* Theorem 4 (p. 9, Eq. (36)): a polynomial-size circuit prepares the ground
  state;
* Lemma 10 (p. 10, Eq. (D1)): the JC states `|gamma_{n,pm}^d>` are approximate
  eigenstates of `H_JC^d`;
* Theorem 5 (p. 10, Eq. (41)): one JC evolution step transfers
  `|phi_n^d>|0>` to `|phi_{n+1}^d>|1>`;
* Lemma 11 (p. 11, Eq. (45)): the JC word `W(s)` is a second-order accurate
  approximation of `e^{-iH_JC^d s}`;
* Theorem 6 (p. 10, Eq. (46)): the `n`-step circuit prepares `|phi_n^d>|0>`.

The eigenstates `|phi_n^d>` of `H^d` are not explicitly diagonalized in this
model; every statement that consumes them carries the paper's spectral
certificate as `ApproxEigenstate` (norm one plus a small `H^d`-residual), which
is what the paper's own estimates (Corollary 2, Lemma 10) provide.
The six statements are recorded below as `Prop`-valued definitions; their
proofs are not formalised.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OneDimSim15.MainResults.Eigenstate

open Qatlib.Papers.OneDimSim15.MainResults
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The Euclidean norm of a complex vector indexed by an arbitrary finite type
(the JC vectors live on `Fin N × Fin 2`). -/
def vNormGen {α : Type*} [Fintype α] (v : α → ℂ) : ℝ :=
  Real.sqrt (Finset.sum Finset.univ (fun i => Complex.normSq (v i)))

/-- Fixed arXiv:1503.06319v2, Lemma 9 (p. 12, Eq. (C2)): there is `lambda > 0`
and `C > 0` such that for every `N >= 2` and `delta > 0`, with
`sigma^2 = delta pi / N`, `t = sqrt(sigma^2 (2 - 4 sigma^2))/2`,
`t' = 1/(4t + 4 sigma^4/t)`, there is a global phase `alpha` with
`|| |psi_0^d> - e^{-i alpha} e^{i (x^d)^2 t'} e^{i (p^d)^2 t} |phi^d> || <=
C exp(-lambda delta)`, where `|phi^d>` is the Gaussian state of Eq. (C1)
(normalized here; the paper's `1/sqrt(kappa)` normalization is absorbed). -/
def lemma9_gaussian_ground_state : Prop :=
    ∃ lam C : ℝ, 0 < lam ∧ 0 < C ∧
      ∀ (N : ℕ) (δ : ℝ), 2 ≤ N → 0 < δ →
        (let σ2 : ℝ := δ * Real.pi / (N : ℝ)
         let tt : ℝ := Real.sqrt (σ2 * (2 - 4 * σ2)) / 2
         let tt' : ℝ := 1 / (4 * tt + 4 * σ2 ^ 2 / tt)
         ∃ α : ℝ,
          vNorm (normalize (psiVec N 0) -
            (Complex.exp (-Complex.I * (α : ℂ)) •
              ((NormedSpace.exp ((Complex.I * (tt' : ℂ)) • (posOp N) ^ 2)).mulVec
                ((NormedSpace.exp ((Complex.I * (tt : ℂ)) • (momOp N) ^ 2)).mulVec
                  (normalize (gaussVec N δ)))))) ≤ C * Real.exp (-lam * δ))

/-- Fixed arXiv:1503.06319v2, Theorem 4 (p. 9, Eq. (36)): there are constants
`C > 0`, `N_0 >= 1` and `m : ℕ` such that for every `eps > 0`, every
`N >= N_0`, there is a compiled unitary `W` with
`|| |phi_0^d> - W |0> || <= C eps` and gate count
`O((log(N/eps))^m)`, where `|phi_0^d>` is a normalized approximate ground
state of `H^d` (eigenvalue within `C eps` of `1/2`, residual at most
`C eps`). -/
def theorem4_ground_state_preparation : Prop :=
    ∃ C N₀ : ℝ, 0 < C ∧ 1 ≤ N₀ ∧ ∃ m : ℕ,
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
        ∀ (N : ℕ), N₀ ≤ (N : ℝ) →
          ∃ (W : CompiledUnitary N) (φ0 : Fin N → ℂ) (E : ℝ),
            |E - 1 / 2| ≤ C * ε ∧
            vNorm ((hamOp N).mulVec φ0 - (E : ℂ) • φ0) ≤ C * ε ∧
            vNorm (φ0 - W.mat.mulVec (if h : 0 < N then basisVec (⟨0, h⟩ : Fin N) else 0)) ≤
              C * ε ∧
            W.gateCount ≤ C * (Real.log ((N : ℝ) / ε)) ^ m

/-- Fixed arXiv:1503.06319v2, Lemma 10 (p. 10, Eq. (D1)): there is `c > 0`
and `beta > 0` such that for all `N >= 2`, `n <= c N`, and all normalized
approximate eigenstates `phi_n, phi_{n+1}` of `H^d` with residuals
`exp(-beta N)`, the JC states `|gamma_{n,pm}^d>` satisfy
`||(H_JC^d ∓ sqrt(n+1)) |gamma_{n,pm}^d>|| <= exp(-beta N)`. -/
def lemma10_jc_approximate_eigenstates : Prop :=
    ∃ c β : ℝ, 0 < c ∧ 0 < β ∧
      ∀ (N n : ℕ), 2 ≤ N → (n : ℝ) ≤ c * (N : ℝ) →
        ∀ (φn φn1 : Fin N → ℂ),
          ApproxEigenstate N n φn (Real.exp (-β * (N : ℝ))) →
          ApproxEigenstate N (n + 1) φn1 (Real.exp (-β * (N : ℝ))) →
            vNormGen ((jcHam N - ((((Real.sqrt ((n : ℝ) + 1) : ℝ)) : ℂ)) •
                (1 : Matrix (Fin N × Fin 2) (Fin N × Fin 2) ℂ)).mulVec
                (gammaVec φn φn1 1)) ≤ Real.exp (-β * (N : ℝ)) ∧
            vNormGen ((jcHam N - (((-(Real.sqrt ((n : ℝ) + 1)) : ℝ)) : ℂ) •
                (1 : Matrix (Fin N × Fin 2) (Fin N × Fin 2) ℂ)).mulVec
                (gammaVec φn φn1 (-1))) ≤ Real.exp (-β * (N : ℝ))

/-- Fixed arXiv:1503.06319v2, Theorem 5 (p. 10, Eq. (41)): there are constants
`C > 0`, `N_0 >= 1` and `beta > 0` such that for every `eps > 0` and every
`N'` there is `N = O(log(1/eps) + N')` with `N' <= C N` for which, for all
`n <= N'` and all approximate eigenstates `phi_n, phi_{n+1}` of `H^d`
(residual `exp(-beta N)`),
`|| e^{-i H_JC^d t_n} |phi_n>|0> + i |phi_{n+1}>|1> || <= C eps`, where
`t_n = pi/(2 sqrt(n+1))`. -/
def theorem5_jc_eigenstate_step : Prop :=
    ∃ C N₀ β : ℝ, 0 < C ∧ 1 ≤ N₀ ∧ 0 < β ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
        ∀ (N' : ℕ),
          ∃ N : ℕ, N₀ ≤ (N : ℝ) ∧ (N' : ℝ) ≤ C * (N : ℝ) ∧
            (N : ℝ) ≤ C * (Real.log (1 / ε) + (N' : ℝ)) ∧
            ∀ n : ℕ, n ≤ N' →
              ∀ (φn φn1 : Fin N → ℂ),
                ApproxEigenstate N n φn (Real.exp (-β * (N : ℝ))) →
                ApproxEigenstate N (n + 1) φn1 (Real.exp (-β * (N : ℝ))) →
                  vNormGen ((jcEvolve N (Real.pi / (2 * Real.sqrt ((n : ℝ) + 1)))).mulVec
                    (tensorVec φn qubit0) + Complex.I • tensorVec φn1 qubit1) ≤ C * ε

/-- Fixed arXiv:1503.06319v2, Lemma 11 (p. 11, Eq. (45)): there are constants
`c > 0`, `K > 0`, `beta > 0` such that for `N >= 2`, `n <= c N`, every
`eps in (0, 1/2]` and every `|s| <= C eps/sqrt(n+1)`, the JC word
`W(s) = e^{-i(x^d⊗sigma_x)s/sqrt 2} e^{i(p^d⊗sigma_y)s/sqrt 2}` differs from
`e^{-iH_JC^d s}` on the approximate eigenstates `|gamma_{n,pm}^d>` by at most
`K eps^2`. -/
def lemma11_jc_word_error : Prop :=
    ∃ c K β : ℝ, 0 < c ∧ 0 < K ∧ 0 < β ∧
      ∀ (N n : ℕ), 2 ≤ N → (n : ℝ) ≤ c * (N : ℝ) →
        ∀ (s ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
          |s| ≤ K * ε / Real.sqrt ((n : ℝ) + 1) →
          ∀ (φn φn1 : Fin N → ℂ),
            ApproxEigenstate N n φn (Real.exp (-β * (N : ℝ))) →
            ApproxEigenstate N (n + 1) φn1 (Real.exp (-β * (N : ℝ))) →
              vNormGen ((jcWord N s - jcEvolve N s).mulVec (gammaVec φn φn1 1)) ≤ K * ε ^ 2 ∧
              vNormGen ((jcWord N s - jcEvolve N s).mulVec (gammaVec φn φn1 (-1))) ≤ K * ε ^ 2

/-- Fixed arXiv:1503.06319v2, Theorem 6 (p. 10, Eq. (46)): there are constants
`C > 0`, `c > 0`, `beta > 0` such that for every `eps in (0, 1/2]`, every
`N >= 2` and every `n <= c N`, and every pair of normalized approximate
eigenstates `phi_0, phi_n` of `H^d` (residual `exp(-beta N)`), there is a
circuit `Q` with gate count `O((n^2/eps) polylog(N/eps))` and
`|Q.amplitude - 1| <= C eps`, i.e. `W^d |phi_0>|0> = |phi_n>|0> + O(eps)`. -/
def theorem6_eigenstate_circuit : Prop :=
    ∃ C c β : ℝ, 0 < C ∧ 0 < c ∧ 0 < β ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
        ∀ (N n : ℕ), 2 ≤ N → (n : ℝ) ≤ c * (N : ℝ) →
          ∀ (φ0 φn : Fin N → ℂ),
            ApproxEigenstate N 0 φ0 (Real.exp (-β * (N : ℝ))) →
            ApproxEigenstate N n φn (Real.exp (-β * (N : ℝ))) →
              ∃ Q : PaperCircuit,
                Q.gateCount ≤ C * (((n : ℝ) ^ 2) / ε) * (Real.log ((N : ℝ) / ε)) ^ 4 ∧
                ‖Q.amplitude - 1‖ ≤ C * ε

end Qatlib.Papers.OneDimSim15.MainResults.Eigenstate
