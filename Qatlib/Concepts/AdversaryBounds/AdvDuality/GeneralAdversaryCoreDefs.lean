/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
import Qatlib.Concepts.AdversaryBounds.OptimizedAdv
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value
import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21RealizedWitnessStat
import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21StrictSeparationStat
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006
open Qatlib.Concepts.AdversaryBounds.OptimizedAdv
open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
open Qatlib.Concepts.GramQueryCore.GammaDuality

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

noncomputable def phaseOracle {q n : ℕ} [NeZero q] {W : Type}
    (input : Fin n → Fin q) : Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ :=
  Matrix.of fun p p' =>
    if p = p' then
      Complex.exp ((2 * Real.pi * Complex.I) *
        (((input p.1.1).val : ℝ) * ((p.1.2.val : ℝ) / (q : ℝ))))
    else 0

def IsPovm {H Y : Type} [Fintype H] [Fintype Y] (out : Y → Matrix H H ℂ) : Prop :=
  (∀ y, Matrix.PosSemidef (out y)) ∧ (∑ y, out y) = 1

noncomputable def povmProb {H Y : Type} [Fintype H] (out : Y → Matrix H H ℂ)
    (y : Y) (ψ : QState H) : ℝ :=
  (Inner ψ (out y *ᵥ ψ)).re

def IsBoundedErrorRun {X W Y : Type} [Fintype W] [Fintype Y] {q n : ℕ} [NeZero q]
    (input : X → Fin n → Fin q) (f : X → Y)
    (C : Circuit ((Fin n × Fin q) × W)) (psi : QState ((Fin n × Fin q) × W))
    (out : Y → Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ) (eps : ℝ) : Prop :=
  IsUnitaryCircuit C ∧ Normalized psi ∧ IsPovm out ∧ 0 ≤ eps ∧ eps ≤ 1 / 2 ∧
    ∀ x, 1 - eps ≤ povmProb out (f x) (Run (phaseOracle (W := W) (input x)) C psi)

def genAdvFilter {X κ A γ : Type} [Zero γ] [DecidableEq A]
    (input : X → κ → A) (Γ : Matrix X X γ) (i : κ) : Matrix X X γ :=
  fun x y => if input x i ≠ input y i then Γ x y else 0

noncomputable def maxFilterNorm {X κ A : Type} [Fintype X] [DecidableEq X] [Fintype κ]
    [DecidableEq A] (input : X → κ → A) (Γ : Matrix X X ℂ) : ℝ :=
  ⨆ i : κ, ‖genAdvFilter input Γ i‖

noncomputable def maxFilterNormR {X κ A : Type} [Fintype X] [DecidableEq X] [Fintype κ]
    [DecidableEq A] (input : X → κ → A) (Γ : Matrix X X ℝ) : ℝ :=
  ⨆ i : κ, ‖genAdvFilter input Γ i‖

noncomputable def advPmWitnessValue {X κ A : Type} [Fintype X] [DecidableEq X] [Fintype κ]
    [DecidableEq A] (input : X → κ → A) (Γ : Matrix X X ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖Γ‖ / ENNReal.ofReal (maxFilterNorm input Γ)

noncomputable def advPmValue {X Y κ A : Type} [Fintype X] [DecidableEq X] [Fintype κ]
    [DecidableEq A] (input : X → κ → A) (f : X → Y) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℂ // Γ.IsHermitian ∧ (∀ x y, f x = f y → Γ x y = 0) ∧ Γ ≠ 0},
    advPmWitnessValue input Γ.1

noncomputable def advAlphaWitnessR {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (α : κ → ℝ) (Γ : Matrix X X ℝ) : ℝ≥0∞ :=
  ⨅ i : κ, ENNReal.ofReal (α i) * ENNReal.ofReal ‖Γ‖ / ENNReal.ofReal ‖genAdvFilter input Γ i‖

noncomputable def advAlphaPmWitness {X κ : Type} [Fintype X] [DecidableEq X]
    [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (β : κ → ℝ≥0∞) (Γ : Matrix X X ℂ) : ℝ≥0∞ :=
  ⨅ i : κ, β i * ENNReal.ofReal ‖Γ‖ / ENNReal.ofReal ‖genAdvFilter input Γ i‖

noncomputable def advAlphaENNWitness {X κ : Type} [Fintype X] [DecidableEq X]
    [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (β : κ → ℝ≥0∞) (Γ : Matrix X X ℝ) : ℝ≥0∞ :=
  ⨅ i : κ, β i * ENNReal.ofReal ‖Γ‖ / ENNReal.ofReal ‖genAdvFilter input Γ i‖

noncomputable def advAlphaR {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (α : κ → ℝ) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℝ // Γ.IsSymm ∧ (∀ x y, 0 ≤ Γ x y) ∧
      (∀ x y, g x = g y → Γ x y = 0) ∧ Γ ≠ 0},
    advAlphaWitnessR input α Γ.1

noncomputable def advAlphaPmENN {X κ : Type} [Fintype X] [DecidableEq X]
    [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (β : κ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℂ // Γ.IsHermitian ∧ (∀ x y, g x = g y → Γ x y = 0) ∧ Γ ≠ 0},
    (⨅ i : κ, β i * ENNReal.ofReal ‖Γ.1‖ / ENNReal.ofReal ‖genAdvFilter input Γ.1 i‖)

noncomputable def advAlphaENN {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (β : κ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℝ // Γ.IsSymm ∧ (∀ x y, 0 ≤ Γ x y) ∧
      (∀ x y, g x = g y → Γ x y = 0) ∧ Γ ≠ 0},
    (⨅ i : κ, β i * ENNReal.ofReal ‖Γ.1‖ / ENNReal.ofReal ‖genAdvFilter input Γ.1 i‖)

noncomputable def advValue {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) : ℝ≥0∞ :=
  advAlphaR input g (fun _ => 1)

def IsProbabilityFamily {X κ : Type} [Fintype X] [Fintype κ] [DecidableEq κ]
    (p : X → κ → ℝ) : Prop :=
  (∀ x i, 0 ≤ p x i) ∧ (∀ x, ∑ i, p x i = 1)

noncomputable def minimaxWitnessValue {X κ : Type} [Fintype X] [DecidableEq X]
    [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (α : κ → ℝ) (p : X → κ → ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal
    (⨅ xy : {xy : X × X // g xy.1 ≠ g xy.2},
      Qatlib.Concepts.AdversaryBounds.OptimizedAdv.advMinimaxTerm input α p xy.val.1 xy.val.2))⁻¹

def IsMinimaxOptimal {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (α : κ → ℝ) (p : X → κ → ℝ) : Prop :=
  IsProbabilityFamily p ∧ minimaxWitnessValue input g α p =
    Qatlib.Concepts.AdversaryBounds.OptimizedAdv.minimaxAlpha input g α

def composeMinimaxWitness {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    (g : ∀ i, X i → Bool)
    (pf : (Fin k → Bool) → Fin k → ℝ) (pg : ∀ i, X i → Fin (n i) → ℝ) :
    ((i : Fin k) → X i) → ((i : Fin k) × Fin (n i)) → ℝ :=
  fun x c => pf (fun i => g i (x i)) c.1 * pg c.1 (x c.1) c.2

noncomputable def blockCosts {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (gin : ∀ i, X i → Fin (n i) → Bool) (g : ∀ i, X i → Bool)
    (α : ((i : Fin k) × Fin (n i)) → ℝ) : Fin k → ℝ≥0∞ :=
  fun i => advAlphaENN (gin i) (g i) (fun j => ENNReal.ofReal (α ⟨i, j⟩))

noncomputable def blockCostsPm {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (gin : ∀ i, X i → Fin (n i) → Bool) (g : ∀ i, X i → Bool)
    (α : ((i : Fin k) × Fin (n i)) → ℝ) : Fin k → ℝ≥0∞ :=
  fun i => advAlphaPmENN (gin i) (g i) (fun j => ENNReal.ofReal (α ⟨i, j⟩))

abbrev composedInput {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    (gin : ∀ i, X i → Fin (n i) → Bool) :
    ((i : Fin k) → X i) → ((i : Fin k) × Fin (n i)) → Bool :=
  Qatlib.Concepts.AdversaryBounds.WeightedAdvComp.weightedAdvInput gin

def composedFunction {k : ℕ} {X : Fin k → Type}
    (g : ∀ i, X i → Bool) (f : (Fin k → Bool) → Bool) :
    ((i : Fin k) → X i) → Bool :=
  fun x => f (fun i => g i (x i))

noncomputable def composedAdversary {k : ℕ} {X : Fin k → Type} [∀ i, Fintype (X i)]
    [∀ i, DecidableEq (X i)]
    (g : ∀ i, X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i, Matrix (X i) (X i) ℂ) :
    Matrix ((i : Fin k) → X i) ((i : Fin k) → X i) ℂ :=
  Qatlib.Concepts.AdversaryBounds.WeightedAdvComp.weightedAdvGamma g f Gf Gg

def GeneratedCompositionWitness {k : ℕ} {X : Fin k → Type} [∀ i, Fintype (X i)]
    [∀ i, DecidableEq (X i)]
    (g : ∀ i, X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i, Matrix (X i) (X i) ℂ) : Prop :=
  Gf.IsHermitian ∧ (∀ u v, f u = f v → Gf u v = 0) ∧ Gf ≠ 0 ∧
    (∀ i, (Gg i).IsHermitian) ∧ (∀ i u v, g i u = g i v → Gg i u v = 0) ∧ (∀ i, Gg i ≠ 0) ∧
    (composedAdversary g f Gf Gg).IsHermitian ∧
    (∀ x y, composedFunction g f x = composedFunction g f y →
      composedAdversary g f Gf Gg x y = 0) ∧
    composedAdversary g f Gf Gg ≠ 0

noncomputable def sixBitF (w : Fin 6 → Bool) : Option Bool :=
  if Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006.kushilevitzWeightOf w = 3
  then some (Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006.kushilevitzIsOneWord w)
  else none

noncomputable def monotoneSixBitG (w : Fin 6 → Bool) : Bool :=
  Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006.kushilevitzMonotone w

def ambainisSorted4 (w : Fin 4 → Bool) : Bool :=
  ((!w 0 || w 1) && (!w 1 || w 2) && (!w 2 || w 3)) ||
    ((!w 1 || w 0) && (!w 2 || w 1) && (!w 3 || w 2))

def hamming {m : ℕ} (x y : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin m => x i ≠ y i).card

def IsCertificate {m : ℕ} (h : (Fin m → Bool) → Bool) (x : Fin m → Bool)
    (S : Finset (Fin m)) : Prop :=
  ∀ y, (∀ i ∈ S, y i = x i) → h y = h x

noncomputable def minCertSize {m : ℕ} (h : (Fin m → Bool) → Bool)
    (x : Fin m → Bool) : WithTop ℕ :=
  ⨅ S : Finset (Fin m), if IsCertificate h x S then (S.card : WithTop ℕ) else ⊤

noncomputable def certComplexity {m : ℕ} (h : (Fin m → Bool) → Bool) (b : Bool) : WithTop ℕ :=
  ⨆ x : Fin m → Bool, if h x = b then minCertSize h x else 0

noncomputable def relativeHamming {m : ℕ} (h : (Fin m → Bool) → Option Bool) : ℝ :=
  if m = 0 then 0
  else
    (⨅ w : {w : (Fin m → Bool) × (Fin m → Bool) //
        h w.1 = some false ∧ h w.2 = some true},
      ((hamming w.val.1 w.val.2 : ℕ) : ℝ)) / (m : ℝ)

def powIndexSplit (n d : ℕ) : Fin (n^(d+1)) ≃ Fin (n^d) × Fin n :=
  (Equiv.cast (congrArg Fin (Nat.pow_succ n d))).trans (finProdFinEquiv (m := n^d) (n := n)).symm

def forceAll {n : ℕ} (bs : Fin n → Option Bool) : Option (Fin n → Bool) :=
  if h : ∀ i, (bs i).isSome then some (fun i => Option.get _ (h i)) else none

def iterateFlat {n : ℕ} (f : (Fin n → Bool) → Option Bool) :
    (d : ℕ) → (Fin (n^d) → Bool) → Option Bool
  | 0, w => some (w ⟨0, by rw [Nat.pow_zero]; exact Nat.one_pos⟩)
  | d + 1, w =>
    (forceAll fun i : Fin n =>
      iterateFlat f d (fun j : Fin (n^d) => w ((powIndexSplit n d).symm (j, i)))) >>= f

noncomputable def iterateTotal {n : ℕ} (g : (Fin n → Bool) → Bool) (d : ℕ) :
    (Fin (n^d) → Bool) → Bool :=
  fun w => (iterateFlat (fun v => some (g v)) d w).getD false

noncomputable def domValue {m : ℕ} (h : (Fin m → Bool) → Option Bool)
    (w : {w : Fin m → Bool // h w ≠ none}) : Bool :=
  (h w.val).getD false

def genFilterDelta {X κ A : Type} [DecidableEq A]
    (input : X → κ → A) : κ → Matrix X X ℂ :=
  fun j x y => if input x j = input y j then (0 : ℂ) else 1

noncomputable def stateQueryDistance {X A : Type} [Fintype X] [DecidableEq X] [DecidableEq A]
    {n : ℕ} (input : X → Fin n → A) (ρ σ : Matrix X X ℂ) : ℝ≥0∞ :=
  filteredGamma2 (ρ - σ) (genFilterDelta input)

noncomputable def CoherentConverts {X H : Type} [Fintype H]
    (fin σ : X → QState H) (eps : ℝ) : Prop :=
  ∀ x, Real.sqrt (1 - eps) ≤ (Inner (fin x) (σ x)).re

def SourceValueNondegenerate (v : ℝ≥0∞) : Prop := 0 < v ∧ v < ⊤

end Qatlib.Concepts.AdversaryBounds.AdvDuality
