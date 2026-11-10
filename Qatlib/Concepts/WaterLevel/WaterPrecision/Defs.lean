/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WaterLevel.WaterPrecision.CoherentReweightingDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.WaterLevel.WaterPrecision
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib.Concepts.WaterLevel.WaterPrecision

def TableBound {m : ℕ} (p s : Fin m→ℝ) (B : ℝ) : Prop := ∀ i, 0≤p i ∧ p i≤B ∧ 0≤s i ∧ s i≤B

def inputError {m : ℕ} (p s p' s' : Fin m→ℝ) (δ : ℝ) : Prop := ∀ i, |p i-p' i|≤δ ∧ |s i-s' i|≤δ

noncomputable def fillError (L δ : ℝ) : ℝ := (1+L)*δ
noncomputable def massError (m : ℕ) (B L δ : ℝ) : ℝ := 2*(m:ℝ)*B*fillError L δ
noncomputable def dotError (m : ℕ) (B L δ : ℝ) : ℝ := (m:ℝ)*B*(fillError L δ+δ)
noncomputable def residual {m : ℕ} (p s : Fin m→ℝ) (γ a : ℝ) : ℝ := realDot p s γ^2-a*realMass p s γ

def residualRat {m : ℕ} (p s : Fin m→ℚ) (γ a : ℚ) : ℚ :=
  (∑ i, s i*min (p i) (γ*s i))^2-a*∑ i, (min (p i) (γ*s i))^2

def residualError (m : ℕ) (B L δ a : ℚ) : ℚ :=
  2*(m:ℚ)*B^2*((m:ℚ)*B*((1+L)*δ+δ))+|a| * (2*(m:ℚ)*B*((1+L)*δ))

def decideResidual (q e : ℚ) : Option Bool :=
    if e<q then some true else if q < -e then some false else none

end Qatlib.Concepts.WaterLevel.WaterPrecision
