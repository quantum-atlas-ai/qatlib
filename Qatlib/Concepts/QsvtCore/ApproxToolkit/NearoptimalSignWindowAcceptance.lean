/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignWindow
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignWindow

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord

def SignConstructionClaim : Prop :=
  (∀ (δ ε : ℝ), 0<δ → δ≤2 → 0<ε → ε<1/2 →
    NearOptimalSignApproximation 12000 δ ε (nearOptimalPolynomial δ ε)) ∧
  (∀ (δ ε : ℚ) (_hδ : 0<δ) (_hδ2 : δ≤2) (hε : 0<ε) (hε2 : ε<1/2),
    NearOptimalSignApproximation 12000 (δ:ℝ) (ε:ℝ)
      (realTarget (nativeSignCoefficients δ ε hε hε2))) ∧
  (∀ (δ ε η : ℚ) (_hδ : 0<δ) (_hδ2 : δ≤2) (hε : 0<ε) (hε2 : ε<1/2),
    0≤η → ∀ b : ℕ,
    ((2:ℝ)^(nativeSignCoefficients δ ε hε hε2).length-1)/(2:ℝ)^(b+1) ≤ (η:ℝ) →
    (∀ x : ℝ, |x|≤2 →
      |(realTarget (nativeRoundedNormalized (nativeSignCoefficients δ ε hε hε2) b η)).eval x|≤1) ∧
    (∀ x : ℝ, |x|≤2 → (δ:ℝ)≤|x| →
      |(realTarget (nativeRoundedNormalized (nativeSignCoefficients δ ε hε hε2) b η)).eval x-
        Real.sign x|≤(ε:ℝ)+2*(η:ℝ))) ∧
  (∀ (δ ε : ℝ), 2<δ → 0<ε → ε<1/2 →
    NearOptimalSignApproximation 12000 δ ε (0 : Polynomial ℝ))

theorem signConstruction : SignConstructionClaim :=
  ⟨@nearOptimalPolynomial_spec,@nativeSignCoefficients_spec,@nativeRoundedSign_bounds,@sign_vacuous⟩

def RectangleConstructionClaim : Prop :=
  (∀ (δ ε t : ℝ), 0<δ → δ≤2 → 0<ε → ε<1/2 → t≤1 →
    PrintedRectangleBand (nearOptimalRectangle δ ε t) ε δ t ∧
    (∀ x, (nearOptimalRectangle δ ε t).eval (-x)=(nearOptimalRectangle δ ε t).eval x) ∧
    ((nearOptimalRectangle δ ε t).natDegree:ℝ)≤36000*(1+(1/δ)*Real.log (1/ε))) ∧
  (∀ (δ ε t : ℚ) (_hδ : 0<δ) (_hδ2 : δ≤2) (hε : 0<ε) (hε2 : ε<1/2), t≤1 →
    PrintedRectangleBand (realTarget (nativeRectangleCoefficients δ ε t hε hε2)) (ε:ℝ) (δ:ℝ) (t:ℝ) ∧
    (∀ x, (realTarget (nativeRectangleCoefficients δ ε t hε hε2)).eval (-x)=
      (realTarget (nativeRectangleCoefficients δ ε t hε hε2)).eval x) ∧
    ((realTarget (nativeRectangleCoefficients δ ε t hε hε2)).natDegree:ℝ)≤
      36000*(1+(1/(δ:ℝ))*Real.log (1/(ε:ℝ))))

theorem rectangleConstruction : RectangleConstructionClaim := by
  constructor
  · intro δ ε t hδ hδ2 hε hε2 ht
    have h :=
        Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignWindow.frontier1 hδ hδ2 hε hε2 ht
    exact ⟨h.2.1,h.2.2.1,h.2.2.2⟩
  · intro δ ε t hδ hδ2 hε hε2 ht
    exact ⟨nativeRectangleCoefficients_spec hδ hδ2 hε hε2 ht,
      nativeRectangleCoefficients_even δ ε t hε hε2,
      nativeRectangleCoefficients_degree hδ hδ2 hε hε2 t⟩

end Qatlib.Concepts.QsvtCore.ApproxToolkit
