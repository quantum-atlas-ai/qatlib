/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 2 — second-order expansion of time correlations of near-identity operators

Fixed source: arXiv:2505.07929v2, Lemma 2, Appendix VI, PDF pp. 37–38, eqs. (B51)–(B66).

For `q` unitaries `V_1, …, V_q` on a finite-dimensional Hilbert space, `q + 1` bounded
operators `O_1, …, O_{q+1}` and a state `|ψ⟩`, the expectation

  `⟨ψ| e^{i O_{q+1}/√D} (∏←_{t=1}^{q} V_t e^{i O_t/√D}) |ψ⟩`

admits the second-order expansion (eq. (B65))

  `= μ^(0) + (i/√D) ∑_l μ^(1)_l - (1/(2D)) ∑_{l,m} μ^(2)_{l,m} + O(D^{-3/2})`,

with the zero-, first- and second-order moments of eqs. (B57)–(B64), where the constant in
the `O(D^{-3/2})` depends only on `q` and the operator norms `‖O_t‖`.

The operators are indexed `0, …, q` in `Fin (q+1)` here (the paper's `1, …, q+1`), and the
unitaries `0, …, q-1` (the paper's `1, …, q`); the ordered product is written as a left
fold over `List.finRange q`.
The expansion (B65) is not formalized: it needs a uniform second-order Taylor remainder for
operator exponentials and the combinatorial expansion of the ordered product of `q + 1`
perturbed layers.  The moment and perturbed-expectation definitions are kept.

-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.SpinBosonQAOA26.MainResults.SecondOrderExpansion

/-- The expansion parameter `θ_D = i/√D` of eqs. (B54), (B65). -/
def theta (D : ℕ) : ℂ := Complex.I / ((Real.sqrt D : ℝ) : ℂ)

/-- The ordered product `(∏←_{t=1}^{q} V_t) = V_q ⋯ V_1` of eq. (B58), restricted to the
layers `s ≤ k.val < e`.  (`prodSlice V 0 q` is the full product.) -/
def prodSlice {B : Type*} [AddCommGroup B] [Module ℂ B] {q : ℕ}
    (V : Fin q → B → B) (s e : ℕ) (b : B) : B :=
  ((List.finRange q).filter (fun k => decide (s ≤ k.val ∧ k.val < e))).foldl
    (fun b k => V k b) b

/-- The zero-order moment `μ^(0) = ⟨ψ| V_q ⋯ V_1 |ψ⟩` of eqs. (B57)–(B58). -/
def moment0 {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] {q : ℕ}
    (V : Fin q → B → B) (ψ : B) : ℂ :=
  inner ℂ ψ (prodSlice V 0 q ψ)

/-- The first-order moment `μ^(1)_l` of eqs. (B59)–(B61): `O_l` is inserted after the
first `l` layers (`l : Fin (q+1)`; the paper indexes `l ∈ [q+1]`, shifted by one). -/
def moment1 {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] {q : ℕ}
    (V : Fin q → B → B) (O : Fin (q + 1) → B → B) (l : Fin (q + 1)) (ψ : B) : ℂ :=
  inner ℂ ψ (prodSlice V l.val q (O l (prodSlice V 0 l.val ψ)))

/-- The second-order moment `μ^(2)_{l,m}` of eqs. (B62)–(B64) for `l ≤ m`: `O_l` is
inserted after the first `l` layers and `O_m` after the first `m` layers.  (The lower
triangle is completed by symmetry in the paper; here the definition is given for all
`l, m`, and only the upper triangle is used by the expansion.) -/
def moment2 {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] {q : ℕ}
    (V : Fin q → B → B) (O : Fin (q + 1) → B → B) (l m : Fin (q + 1)) (ψ : B) : ℂ :=
  inner ℂ ψ
    (prodSlice V (m.val + 1) q
      (O m (prodSlice V l.val m.val (O l (prodSlice V 0 l.val ψ)))))

/-- The perturbed expectation of eq. (B54)/(B56): the ordered product
`e^{θ O_{q+1}} V_q e^{θ O_q} ⋯ V_1 e^{θ O_1}` sandwiched between `ψ` (the innermost
operator is `e^{θ O_1}`). -/
def perturbedExpectation {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] {q : ℕ}
    (V : Fin q → B → B) (O : Fin (q + 1) → B →L[ℂ] B) (θ : ℂ) (ψ : B) : ℂ :=
  inner ℂ ψ
    ((((List.finRange q).flatMap (fun k =>
          [fun b => NormedSpace.exp (θ • O k.castSucc) b,
           fun b => V k b])) ++
        [fun b => NormedSpace.exp (θ • O (Fin.last q)) b]).foldl
      (fun b f => f b) ψ)


end Qatlib.Papers.SpinBosonQAOA26.MainResults.SecondOrderExpansion
