/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MixednessTest26.MainResults.Model.SourceModel
public import Qatlib.Papers.MixednessTest26.PauliShadow.KrawtchoukTester

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Correctness of `KrawtCheck` (Theorem 2.4, §2.2 and Appendix A.2)

Paper: arXiv:2608.18839v3, Theorem 2.4 (page 7 of the PDF) and its proof in
Appendix A.2.  For the class `P^{(Δ,k,β)}` of `(Δ,k,β)`-wise correlated cube
distributions, Algorithm 2 (`KrawtCheck`) distinguishes `p = u` from
`p ∈ P^{(Δ,k,β)}` with probability at least `1 - δ`, using
`M ≥ ⌈16 ln(1/δ)⌉` independent blocks of `2n` samples with
`n ≥ ⌈400 √(2·C(N,k))/(βΔ)⌉` (the constants `400`, `16` and the derived `50`
are the paper's explicit constants).

The fixed public library proves the two-sided correctness statement with the explicit
integer thresholds `krawtCheckHalfCount` and `krawtCheckBlockCount`, using
the real product-sample mass model `krawtCheckMass`, so the paper-layer
declaration is a verified bridge to that FQN.  Note that this bridge does
**not** cover the bit-complexity content of Corollary 2.5 (see
`Krawtchouk/ComputationalEfficiency.lean`).
-/

set_option autoImplicit false

namespace Qatlib.Papers.MixednessTest26.MainResults.Krawtchouk
open Qatlib.Papers.MixednessTest26.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.BooleanCubeFourier
open Qatlib.Papers.MixednessTest26.PauliShadow
open scoped BigOperators

open scoped Classical in
/-- Paper Theorem 2.4: `KrawtChk` accepts the uniform distribution with mass at
most `δ` and accepts every `(Δ,k,β)`-wise correlated distribution with mass at
most `δ` (i.e. rejects it with probability at least `1 - δ`), at the paper's
explicit sample and block thresholds.  Reuses the fixed FQN
`MixedStateCert.PauliShadow.BooleanCube.krawtchouk_tester_correct`. -/
theorem krawtchouk_tester_correct {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N)
    {Δ β δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (hn : krawtCheckHalfCount N k Δ β ≤ n) (M : ℕ)
    (hM : krawtCheckBlockCount δ ≤ M) (p : FinDist (Reg N)) :
    (p = cubeUniformDist N →
      (∑ s ∈ Finset.univ.filter (fun s => krawtCheckAccepts k n M Δ β s),
          krawtCheckMass p n M s) ≤ δ) ∧
    (IsCorrelationConcentrated p Δ k β →
      (∑ s ∈ Finset.univ.filter (fun s => ¬ krawtCheckAccepts k n M Δ β s),
          krawtCheckMass p n M s) ≤ δ) :=
  Qatlib.Papers.MixednessTest26.PauliShadow.BooleanCube.krawtchouk_tester_correct
    hk hkN hΔ hΔ1 hβ hβ1 hδ hδ1 n hn M hM p

end Qatlib.Papers.MixednessTest26.MainResults.Krawtchouk
