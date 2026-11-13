/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OneDimSim15.MainResults.Model.SourceModel
import Mathlib.Logic.Function.Iterate

set_option backward.isDefEq.respectTransparency false

/-!
# OneDimSim15 — Appendix B: Trotter-Suzuki errors and complexity

Claims `c014`-`c018` of the fixed source arXiv:1503.06319v2:

* Lemma 5 (p. 19, Eq. B5): state-dependent Trotter error of `U_p(s)`;
* Lemma 6 (p. 19, Eq. B15): exponential count for error `eps`;
* Lemma 7 (p. 21, Eq. B22/B32): discrete versus CV word diagonal;
* Corollary 3 (p. 21, Eq. B34): choice of `N` in terms of `eps`;
* Lemma 8 (p. 22, Eq. B37): Trotter state error with the chosen `N, p, s`.

Lemma 5 and Lemma 7 are paper statements about the continuous-variable word
`U_p(s)`; as documented in `Model/SourceModel.lean`, this layer transcribes
them using the paper's own discrete replacement `x-hat -> x^d`,
`p-hat -> p^d` (the form Appendix B actually consumes).  For Lemma 7 the
continuous-variable side is made explicit as the truncated Taylor word
`cvWordDiag` on the Hermite coefficient space, built from the exact ladder
actions of `x-hat^2` and `p-hat^2`, matching the truncation argument of
Appendix B (Eq. B23-B31); the corresponding discrete word is the truncated
matrix word `discWordTrunc`.
The five statements are recorded below as `Prop`-valued definitions; their
proofs are not formalised.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OneDimSim15.MainResults.Trotter

open Qatlib.Papers.OneDimSim15.MainResults
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

/-! ## CV Hermite-coefficient space (for Lemma 7) -/

/-- The `n`-th Hermite basis vector `|psi_n>` in coefficient space. -/
def hermBasis (n : ℕ) : ℕ → ℂ := fun m => if m = n then (1 : ℂ) else 0

/-- The exact action of `x-hat^2` on Hermite coefficients,
`x-hat^2 psi_n = (1/2)(sqrt(n(n-1)) psi_{n-2} + (2n+1) psi_n +
sqrt((n+1)(n+2)) psi_{n+2})`. -/
def xSqAct (v : ℕ → ℂ) : ℕ → ℂ := fun m =>
  (1 / 2 : ℂ) * (Real.sqrt (((m : ℝ) + 1) * ((m : ℝ) + 2)) : ℂ) * v (m + 2) +
    (1 / 2 : ℂ) * (((2 : ℝ) * (m : ℝ) + 1 : ℝ) : ℂ) * v m +
      (1 / 2 : ℂ) * (Real.sqrt ((m : ℝ) * ((m : ℝ) - 1)) : ℂ) * v (m - 2)

/-- The exact action of `p-hat^2` on Hermite coefficients,
`p-hat^2 psi_n = (1/2)(-sqrt(n(n-1)) psi_{n-2} + (2n+1) psi_n -
sqrt((n+1)(n+2)) psi_{n+2})`. -/
def pSqAct (v : ℕ → ℂ) : ℕ → ℂ := fun m =>
  (1 / 2 : ℂ) * (Real.sqrt (((m : ℝ) + 1) * ((m : ℝ) + 2)) : ℂ) * v (m + 2) -
    (1 / 2 : ℂ) * (((2 : ℝ) * (m : ℝ) + 1 : ℝ) : ℂ) * v m -
      (1 / 2 : ℂ) * (Real.sqrt ((m : ℝ) * ((m : ℝ) - 1)) : ℂ) * v (m - 2)

/-- The order-`l` Taylor truncation of `exp(c A)`, Eq. (B23). -/
def taylorExpAct (A : (ℕ → ℂ) → (ℕ → ℂ)) (l : ℕ) (c : ℂ) : (ℕ → ℂ) → (ℕ → ℂ) :=
  fun v => Finset.sum (Finset.range (l + 1))
    (fun j => (c ^ j / (j.factorial : ℂ)) • ((A^[j]) v))

/-- The truncated base word `U_1(s) = e^{-is x^2/4} e^{-is p^2/2} e^{-is x^2/4}`
in coefficient space. -/
def cvBaseAct (l : ℕ) (s : ℝ) : (ℕ → ℂ) → (ℕ → ℂ) :=
  fun v =>
    taylorExpAct xSqAct l (-Complex.I * (s : ℂ) / 4)
      (taylorExpAct pSqAct l (-Complex.I * (s : ℂ) / 2)
        (taylorExpAct xSqAct l (-Complex.I * (s : ℂ) / 4) v))

/-- The truncated `p`-th order symmetric word `U_p(s)` in coefficient space. -/
def cvWordAct : (p : ℕ) → (l : ℕ) → ℝ → (ℕ → ℂ) → (ℕ → ℂ)
  | 0, _, _, v => v
  | 1, l, s, v => cvBaseAct l s v
  | (p + 2), l, s, v =>
      let sp := suzukiStep (p + 2) s
      let U := cvWordAct (p + 1) l sp
      let V := cvWordAct (p + 1) l (s - 4 * sp)
      U (U (V (U (U v))))

/-- The continuous-variable word diagonal
`<psi_n|U_p(s)|psi_n>` used in Lemma 7 (Eq. B31/B32). -/
def cvWordDiag (l p : ℕ) (s : ℝ) (n : ℕ) : ℂ :=
  cvWordAct p l s (hermBasis n) n

/-! ## Truncated discrete word (for Lemma 7) -/

/-- The order-`l` Taylor truncation of a matrix exponential, Eq. (B23). -/
def truncExpMat {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (l : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Finset.sum (Finset.range (l + 1)) (fun j => ((j.factorial : ℂ)⁻¹) • A ^ j)

/-- The truncated base word `U_1^d(s)`. -/
def discBaseTrunc (N l : ℕ) (s : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  truncExpMat ((-Complex.I * (s : ℂ) / 4) • (posOp N) ^ 2) l *
    truncExpMat ((-Complex.I * (s : ℂ) / 2) • (momOp N) ^ 2) l *
      truncExpMat ((-Complex.I * (s : ℂ) / 4) • (posOp N) ^ 2) l

/-- The truncated `p`-th order discrete word. -/
def discWordTrunc : (p : ℕ) → (N : ℕ) → (l : ℕ) → ℝ → Matrix (Fin N) (Fin N) ℂ
  | 0, _, _, _ => 1
  | 1, N, l, s => discBaseTrunc N l s
  | (p + 2), N, l, s =>
      let sp := suzukiStep (p + 2) s
      let U := discWordTrunc (p + 1) N l
      U sp * U sp * U (s - 4 * sp) * U sp * U sp

/-! ## The claims -/

/-- **Statement only — not proved in Qatlib.** Fixed arXiv:1503.06319v2, Lemma 5 (p. 19, Eq. (B5)), transcribed with the
paper's discrete replacement `x-hat -> x^d`, `p-hat -> p^d`: there are
constants `d >= 1` and `C > 0` such that for `|s| < 1/d` and `p >= 1`,
`||epsilon_p(s) |psi_n^d>|| <= C (n+2) |s|^{2p+1}` for every `n`.  (The
original continuous-variable statement is Eq. (B5).) -/
def lemma5_trotter_error_state_statement : Prop :=
    ∃ d C : ℝ, 1 ≤ d ∧ 0 < C ∧
      ∀ (N p : ℕ) (s : ℝ), |s| < 1 / d → 1 ≤ p → ∀ n : ℕ,
        vNorm ((trotterEps N p s).mulVec (psiVec N n)) ≤
          C * ((n : ℝ) + 2) * |s| ^ (2 * p + 1)

/-- **Statement only — not proved in Qatlib.** Fixed arXiv:1503.06319v2, Lemma 6 (p. 19, Eq. (B15)): for any target
error `eps` there are `N, p, k, s` with `k s = t`, `p = Theta(sqrt(log(w/eps)))`,
and the total exponential count `3 * 5^{p-1} k` is
`Theta(|t| exp(gamma sqrt(log((n+2)|t|/eps))))`, while the `k`-th power of the
word approximates `U^d(t) |psi_n^d>` to `eps`. -/
def lemma6_exponential_count_statement : Prop :=
    ∃ γ c₁ c₂ : ℝ, 0 < γ ∧ 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (n : ℕ) (t ε : ℝ), 1 ≤ |t| → 0 < ε → ε ≤ 1 / 2 →
        ∃ (N p k : ℕ) (s : ℝ), 1 ≤ p ∧ 1 ≤ k ∧ (k : ℝ) * s = t ∧
          c₁ * |t| * Real.exp (γ * Real.sqrt (Real.log (((n : ℝ) + 2) * |t| / ε))) ≤
            (trotterCount p : ℝ) * (k : ℝ) ∧
          (trotterCount p : ℝ) * (k : ℝ) ≤
            c₂ * |t| * Real.exp (γ * Real.sqrt (Real.log (((n : ℝ) + 2) * |t| / ε))) ∧
          vNorm (((trotterWord p N s) ^ k).mulVec (psiVec N n) -
            (evolveOp N t).mulVec (psiVec N n)) ≤ ε

/-- **Statement only — not proved in Qatlib.** Fixed arXiv:1503.06319v2, Lemma 7 (p. 21, Eqs. (B22), (B31), (B32)):
the truncated discrete word diagonal and the truncated continuous-variable
word diagonal differ by `O(5^p nu_1(N)^{|s|})` for low-energy `n <= c N`. -/
def lemma7_discrete_vs_cv_word_diagonal_statement : Prop :=
    ∃ c β C : ℝ, 0 < c ∧ 0 < β ∧ 0 < C ∧
      ∀ (N n p : ℕ) (s : ℝ), 2 ≤ N → (n : ℝ) ≤ c * (N : ℝ) → 1 ≤ p → |s| ≤ C →
        ∃ l : ℕ,
          ‖vInner (psiVec N n) ((discWordTrunc p N l s).mulVec (psiVec N n)) -
              cvWordDiag l p s n‖ ≤
            (5 : ℝ) ^ p * Real.exp (-β * (N : ℝ) * |s|)

/-- **Statement only — not proved in Qatlib.** Fixed arXiv:1503.06319v2, Corollary 3 (p. 21, Eq. (B34)): with
`N = Theta(exp(delta sqrt(log(N' |t| / eps))) + N'/c)` and
`p = Theta(sqrt(log(N' |t| / eps)))`, the truncated word diagonal is within
`O(eps |s/t|)` of the continuous-variable word diagonal. -/
def corollary3_jc_trotter_diagonal_error_statement : Prop :=
    ∃ c δ C : ℝ, 0 < c ∧ 0 < δ ∧ 0 < C ∧
      ∀ (N' n p : ℕ) (t ε : ℝ), 1 ≤ N' → 0 < ε → ε ≤ 1 / 2 → 1 ≤ |t| → 1 ≤ p →
        (n : ℝ) ≤ c * (N' : ℝ) →
        ∃ (N l : ℕ) (s : ℝ), 2 ≤ N ∧ (N' : ℝ) ≤ c * (N : ℝ) ∧
          (N : ℝ) ≤ Real.exp (δ * Real.sqrt (Real.log ((N' : ℝ) * |t| / ε))) +
            (N' : ℝ) / c + 1 ∧
          |s| ≤ C * (5 : ℝ) ^ (-(p : ℝ)) ∧
          ‖vInner (psiVec N n) ((discWordTrunc p N l s).mulVec (psiVec N n)) -
              cvWordDiag l p s n‖ ≤ C * ε * |s / t|

/-- **Statement only — not proved in Qatlib.** Fixed arXiv:1503.06319v2, Lemma 8 (p. 22, Eq. (B37)): for every `N'`,
`t`, `eps` there are `N, p, k, s` with `ks = t`, `N = O(exp(delta
sqrt(log(N'|t|/eps))) + N'/c')`, `p = Theta(sqrt(log(N'|t|/eps)))` such that
the `k`-th power of `U_p^d(s)` approximates `U^d(t)` on every low-energy
`|psi_n^d>`, `n <= N'`, to `eps`, using `O(|t| 5^{2p})` exponentials. -/
def lemma8_trotter_state_error_statement : Prop :=
    ∃ c' δ C : ℝ, 0 < c' ∧ 0 < δ ∧ 0 < C ∧
      ∀ (N' : ℕ) (t ε : ℝ), 1 ≤ N' → 1 ≤ |t| → 0 < ε → ε ≤ 1 / 2 →
        ∃ (N p k : ℕ) (s : ℝ), 2 ≤ N ∧ 1 ≤ p ∧ 1 ≤ k ∧ (k : ℝ) * s = t ∧
          (N' : ℝ) ≤ c' * (N : ℝ) ∧
          (N : ℝ) ≤ Real.exp (δ * Real.sqrt (Real.log ((N' : ℝ) * |t| / ε))) +
            (N' : ℝ) / c' + 1 ∧
          (trotterCount p : ℝ) * (k : ℝ) ≤ C * |t| * (5 : ℝ) ^ (2 * p) ∧
          ∀ n : ℕ, n ≤ N' →
            vNorm (((trotterWord p N s) ^ k).mulVec (psiVec N n) -
              (evolveOp N t).mulVec (psiVec N n)) ≤ C * ε

end Qatlib.Papers.OneDimSim15.MainResults.Trotter
