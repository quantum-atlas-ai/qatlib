/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryCoreDefs
import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary
import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21RealizedWitnessNega

/-!
# General adversary bounds and Boolean examples

This module states the general adversary, minimax, composition, separation, and state conversion
propositions `clause16Prop` through `clause20Prop`. It also provides an engine deriving the
query bound from explicit progress estimates, in the setting of negative weight adversaries
[HoyerLeeSpalek2007]. These proposition definitions specify mathematical claims without
themselves proving the entire collection.

The concrete results include a lower bound for the six bit Kushilevitz example, its relative
Hamming distance, and exact certificate complexities for a monotone extension. Certificate
terminology is also used in [AmbainisEtAl2009].

## Main statements

* `clause16_engine_of_obligations`: combine initial, final, and per query progress bounds.
* `advPmValue_kushilevitz_ge`: a concrete general adversary lower bound.
* `relativeHamming_sixBitF`: the partial function's relative Hamming distance is `1 / 3`.
* `certComplexity_monotoneSixBitG_eq_three`: both output certificate complexities equal three.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
* [Ambainis et al., 2009][AmbainisEtAl2009]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdversaryBounds.OptimizedAdv
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

set_option autoImplicit false
set_option maxRecDepth 4096

open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006
open scoped Matrix.Norms.L2Operator ComplexOrder ENNReal
open Classical BigOperators

/-- The proposition asserting general adversary query lower bounds for bounded error phase
oracle runs, including the sharper binary output constant [HoyerLeeSpalek2007]. -/
def clause16Prop : Prop :=
  ∀ (q n : ℕ) [NeZero q] (X W Y : Type) [Fintype X] [DecidableEq X] [Fintype W] [Fintype Y]
    (input : X → Fin n → Fin q) (f : X → Y)
    (Γ : Matrix X X ℂ) (C : Circuit ((Fin n × Fin q) × W))
    (psi : QState ((Fin n × Fin q) × W))
    (out : Y → Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ) (eps : ℝ),
    Γ.IsHermitian →
    (∀ x y, f x = f y → Γ x y = 0) →
    IsBoundedErrorRun input f C psi out eps →
    (1 - 2 * Real.sqrt (eps * (1 - eps)) - 2 * eps) * ‖Γ‖ ≤
      2 * (QueryCount C) * maxFilterNorm input Γ ∧
    ENNReal.ofReal ((1 - 2 * Real.sqrt (eps * (1 - eps)) - 2 * eps) / 2) *
      advPmValue input f ≤ ((QueryCount C : ℕ) : ℝ≥0∞) ∧
    (Fintype.card Y = 2 →
      (1 - 2 * Real.sqrt (eps * (1 - eps))) * ‖Γ‖ ≤
        2 * (QueryCount C) * maxFilterNorm input Γ ∧
      ENNReal.ofReal ((1 - 2 * Real.sqrt (eps * (1 - eps))) / 2) *
        advPmValue input f ≤ ((QueryCount C : ℕ) : ℝ≥0∞))

/-- The proposition asserting equality of the positive cost nonnegative adversary and minimax
values, with witnesses attaining both optima. -/
def clause17Prop : Prop :=
  ∀ (X κ : Type) [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (α : κ → ℝ),
    (∃ x y, g x ≠ g y) →
    (∀ i, 0 < α i) →
    advAlphaR input g α = minimaxAlpha input g α ∧
    (∃ Γ : Matrix X X ℝ,
      Γ.IsSymm ∧ (∀ x y, 0 ≤ Γ x y) ∧ (∀ x y, g x = g y → Γ x y = 0) ∧ Γ ≠ 0 ∧
      advAlphaWitnessR input α Γ = advAlphaR input g α) ∧
    (∃ p : X → κ → ℝ, IsMinimaxOptimal input g α p)

/-- The proposition asserting a weighted composition upper bound together with attaining
component adversaries and composed minimax witnesses. -/
def clause18Prop : Prop :=
  ∀ (k : ℕ) (X : Fin k → Type) (n : Fin k → ℕ) [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (gin : ∀ i, X i → Fin (n i) → Bool) (g : ∀ i, X i → Bool) (f : (Fin k → Bool) → Bool)
    (α : ((i : Fin k) × Fin (n i)) → ℝ),
    (∀ c, 0 < α c) →
    (∃ u v : Fin k → Bool, f u ≠ f v) →
    (∀ i, blockCosts gin g α i < ⊤) →
    advAlphaENN (composedInput gin) (composedFunction g f)
        (fun c => ENNReal.ofReal (α c)) ≤
      advAlphaENN (fun u : Fin k → Bool => u) f (blockCosts gin g α) ∧
    (∃ (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ) (Gg : ∀ i, Matrix (X i) (X i) ℂ),
      GeneratedCompositionWitness g f Gf Gg ∧
      advAlphaPmWitness (fun u : Fin k → Bool => u) (blockCostsPm gin g α) Gf =
        advAlphaPmENN (fun u : Fin k → Bool => u) f (blockCostsPm gin g α) ∧
      (∀ i, advAlphaPmWitness (gin i)
          (fun j => ENNReal.ofReal (α ⟨i, j⟩)) (Gg i) =
        advAlphaPmENN (gin i) (g i) (fun j => ENNReal.ofReal (α ⟨i, j⟩))) ∧
      advAlphaPmWitness (composedInput gin)
          (fun c => ENNReal.ofReal (α c)) (composedAdversary g f Gf Gg) ≥
        advAlphaPmWitness (fun u : Fin k → Bool => u) (blockCostsPm gin g α) Gf) ∧
    (∃ (pf : (Fin k → Bool) → Fin k → ℝ) (pg : ∀ i, X i → Fin (n i) → ℝ),
      IsMinimaxOptimal (fun u : Fin k → Bool => u) f
          (fun i => (blockCosts gin g α i).toReal) pf ∧
      (∀ i, IsMinimaxOptimal (gin i) (g i) (fun j => α ⟨i, j⟩) (pg i)) ∧
      IsProbabilityFamily (composeMinimaxWitness g pf pg) ∧
      minimaxWitnessValue (composedInput gin) (composedFunction g f) α
          (composeMinimaxWitness g pf pg) ≤
        minimaxWitnessValue (fun u : Fin k → Bool => u) f
          (fun i => (blockCosts gin g α i).toReal) pf)

/-- The proposition collecting explicit adversary separations, relative Hamming bounds, and
certificate complexity formulas for Boolean examples and their iterates
[HoyerLeeSpalek2007]. -/
def clause19Prop : Prop :=
  ENNReal.ofReal (2.5135) ≤
      advPmValue (fun w : Fin 4 → Bool => w) ambainisSorted4 ∧
  relativeHamming sixBitF = 1 / 3 ∧
  ENNReal.ofReal ((1 / relativeHamming sixBitF) ^ (1.098 : ℝ)) ≤
    advPmValue kushilevitzInputW kushilevitzFunW ∧
  (∀ d : ℕ, 1 ≤ d →
    ENNReal.ofReal ((1 / relativeHamming (iterateFlat sixBitF d)) ^ (1.098 : ℝ)) ≤
      advPmValue
        (fun w : {w : Fin (6^d) → Bool // iterateFlat sixBitF d w ≠ none} => w.val)
        (domValue (iterateFlat sixBitF d))) ∧
  (∀ d : ℕ, 1 ≤ d →
    ENNReal.ofReal ((2 + 3 * Real.sqrt 5 / 5) ^ d) ≤
      advPmValue (fun w : Fin (6^d) → Bool => w) (iterateTotal monotoneSixBitG d)) ∧
  (∀ d : ℕ, 1 ≤ d →
    advPmValue (fun w : Fin 6 → Bool => w) monotoneSixBitG ^ d ≤
      advPmValue (fun w : Fin (6^d) → Bool => w) (iterateTotal monotoneSixBitG d)) ∧
  certComplexity monotoneSixBitG false = 3 ∧
  certComplexity monotoneSixBitG true = 3 ∧
  (∀ d : ℕ, 1 ≤ d →
    certComplexity (iterateTotal monotoneSixBitG d) false = (3 ^ d : WithTop ℕ) ∧
    certComplexity (iterateTotal monotoneSixBitG d) true = (3 ^ d : WithTop ℕ)) ∧
  (∀ d : ℕ, 1 ≤ d →
    ENNReal.ofReal ((((3 ^ d * 3 ^ d : ℕ) : ℝ)) ^ (0.549 : ℝ)) ≤
      advPmValue (fun w : Fin (6^d) → Bool => w) (iterateTotal monotoneSixBitG d)) ∧
  (∀ d : ℕ, 1 ≤ d →
    ENNReal.ofReal ((((3 * 3 : ℕ) : ℝ)) ^ (0.549 : ℝ)) ≤
      advPmValue (fun w : Fin (6^d) → Bool => w) (iterateTotal monotoneSixBitG d)) ∧
  (∀ d : ℕ, 1 ≤ d →
    ENNReal.ofReal ((advValue (fun w : Fin (6^d) → Bool => w)
        (iterateTotal monotoneSixBitG d)).toReal ^ (1.098 : ℝ)) ≤
      advPmValue (fun w : Fin (6^d) → Bool => w) (iterateTotal monotoneSixBitG d))

/-- The proposition asserting coherent state conversion with a query bound controlled by a
positive finite filtered Gram distance and the error tolerance. -/
def clause20Prop : Prop :=
  ∀ (q n : ℕ) [NeZero q] (X W : Type) [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
    (input : X → Fin n → Fin q)
    (rho sigma : X → QState ((Fin n × Fin q) × W)),
    let γ := stateQueryDistance input (gramStateMatrix rho) (gramStateMatrix sigma);
    SourceValueNondegenerate γ →
    ∃ c : ℝ, 0 < c ∧ c < 100 ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 → ENNReal.ofReal eps < γ →
        ∃ (T : ℕ) (C : Circuit ((Fin n × Fin q) × W)),
          IsUnitaryCircuit C ∧ QueryCount C = T ∧
          CoherentConverts (fun x => Run (phaseOracle (W := W) (input x)) C (rho x))
            sigma eps ∧
          (T : ℝ) ≤ c * γ.toReal * Real.log (1 / eps) / eps ^ 2

/-- A bounded error run uses a unitary circuit. -/
theorem isBoundedErrorRun_isUnitary {X W Y : Type} [Fintype W] [Fintype Y] {q n : ℕ} [NeZero q]
    (input : X → Fin n → Fin q) (f : X → Y)
    (C : Circuit ((Fin n × Fin q) × W)) (psi : QState ((Fin n × Fin q) × W))
    (out : Y → Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ) (eps : ℝ)
    (hrun : IsBoundedErrorRun input f C psi out eps) : IsUnitaryCircuit C :=
  hrun.1

/-- The initial state of a bounded error run is normalized. -/
theorem isBoundedErrorRun_normalized {X W Y : Type} [Fintype W] [Fintype Y] {q n : ℕ} [NeZero q]
    (input : X → Fin n → Fin q) (f : X → Y)
    (C : Circuit ((Fin n × Fin q) × W)) (psi : QState ((Fin n × Fin q) × W))
    (out : Y → Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ) (eps : ℝ)
    (hrun : IsBoundedErrorRun input f C psi out eps) : Normalized psi :=
  hrun.2.1

/-- The output operators of a bounded error run form a POVM. -/
theorem isBoundedErrorRun_isPovm {X W Y : Type} [Fintype W] [Fintype Y] {q n : ℕ} [NeZero q]
    (input : X → Fin n → Fin q) (f : X → Y)
    (C : Circuit ((Fin n × Fin q) × W)) (psi : QState ((Fin n × Fin q) × W))
    (out : Y → Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ) (eps : ℝ)
    (hrun : IsBoundedErrorRun input f C psi out eps) : IsPovm out :=
  hrun.2.2.1

/-- The error parameter of a bounded error run lies between zero and one half. -/
theorem isBoundedErrorRun_eps {X W Y : Type} [Fintype W] [Fintype Y] {q n : ℕ} [NeZero q]
    (input : X → Fin n → Fin q) (f : X → Y)
    (C : Circuit ((Fin n × Fin q) × W)) (psi : QState ((Fin n × Fin q) × W))
    (out : Y → Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ) (eps : ℝ)
    (hrun : IsBoundedErrorRun input f C psi out eps) : 0 ≤ eps ∧ eps ≤ 1 / 2 :=
  ⟨hrun.2.2.2.1, hrun.2.2.2.2.1⟩

/-- A bounded error run returns the correct output with probability at least one minus its error
parameter on every input. -/
theorem isBoundedErrorRun_success {X W Y : Type} [Fintype W] [Fintype Y] {q n : ℕ} [NeZero q]
    (input : X → Fin n → Fin q) (f : X → Y)
    (C : Circuit ((Fin n × Fin q) × W)) (psi : QState ((Fin n × Fin q) × W))
    (out : Y → Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ) (eps : ℝ)
    (hrun : IsBoundedErrorRun input f C psi out eps) :
    ∀ x, 1 - eps ≤ povmProb out (f x) (Run (phaseOracle (W := W) (input x)) C psi) :=
  hrun.2.2.2.2.2

/-- Each coordinate filtered adversary norm is bounded by the supremum of the filter norms. -/
theorem genAdvFilter_le_maxFilterNorm {X κ A : Type} [Fintype X] [DecidableEq X] [Fintype κ]
    [DecidableEq A] (input : X → κ → A) (Γ : Matrix X X ℂ) (i : κ) :
    ‖genAdvFilter input Γ i‖ ≤ maxFilterNorm input Γ :=
  le_ciSup (Set.Finite.bddAbove (Set.finite_range fun j : κ => ‖genAdvFilter input Γ j‖)) i

/-- The supremum of the coordinate filtered adversary norms is nonnegative. -/
theorem maxFilterNorm_nonneg {X κ A : Type} [Fintype X] [DecidableEq X] [Fintype κ]
    [DecidableEq A] (input : X → κ → A) (Γ : Matrix X X ℂ) :
    0 ≤ maxFilterNorm input Γ :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- A matrix indexed by an empty type has operator norm zero. -/
theorem norm_eq_zero_of_isEmpty {X : Type} [Fintype X] [DecidableEq X] [IsEmpty X]
    (Γ : Matrix X X ℂ) : ‖Γ‖ = 0 := by
  have h : Γ = 0 := Subsingleton.elim _ _
  rw [h, norm_zero]

/-- The predicate asserting a total progress change bound of twice the query count times the
maximum filtered norm. -/
def PhaseOracleProgressRunBound {q n : ℕ} [NeZero q] {X W : Type} [Fintype X] [DecidableEq X]
    [Fintype W] (input : X → Fin n → Fin q) (Γ : Matrix X X ℂ) : Prop :=
  ∀ (weight : QState X) (C : Circuit ((Fin n × Fin q) × W))
    (states : X → QState ((Fin n × Fin q) × W)),
    Normalized weight → IsUnitaryCircuit C → (∀ x, Normalized (states x)) →
    |advProgress Γ weight (fun x => Run (phaseOracle (W := W) (input x)) C (states x))
      - advProgress Γ weight states| ≤
      2 * (QueryCount C) * maxFilterNorm input Γ

/-- The predicate bounding final adversary progress for successful normalized POVM outputs, with
an improved bound for two outputs. -/
def PovmFinalProgressBound {X H Y : Type} [Fintype X] [DecidableEq X] [Fintype H] [Fintype Y]
    (Γ : Matrix X X ℂ) (f : X → Y) (out : Y → Matrix H H ℂ) (eps : ℝ) : Prop :=
  ∀ (weight : QState X) (states : X → QState H),
    Γ.IsHermitian → Normalized weight → (∀ x, Normalized (states x)) →
    (∀ x y, f x = f y → Γ x y = 0) → 0 ≤ eps → eps ≤ 1 / 2 → IsPovm out →
    (∀ x, 1 - eps ≤ povmProb out (f x) (states x)) →
    |advProgress Γ weight states| ≤ (2 * Real.sqrt (eps * (1 - eps)) + 2 * eps) * ‖Γ‖

/-- A complex exponential with real phase multiplied by `2πi` has norm one. -/
theorem complex_exp_phase_norm (x : ℝ) :
    ‖Complex.exp ((2 * Real.pi * Complex.I) * (x : ℂ))‖ = 1 := by
  have h : (2 * Real.pi * Complex.I) * (x : ℂ) = ((2 * Real.pi * x : ℝ) * Complex.I) := by
    push_cast; ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The phase oracle is the diagonal matrix of its input dependent complex phases. -/
theorem phaseOracle_eq_diagonal {q n : ℕ} [NeZero q] {W : Type}
    (input : Fin n → Fin q) :
    phaseOracle (W := W) input =
      Matrix.diagonal fun p : (Fin n × Fin q) × W =>
        Complex.exp ((2 * Real.pi * Complex.I) *
          (((input p.1.1).val : ℝ) * ((p.1.2.val : ℝ) / (q : ℝ)))) := by
  ext p p'
  by_cases h : p = p'
  · subst h
    simp [phaseOracle, Matrix.diagonal]
  · simp [phaseOracle, Matrix.diagonal, h]

/-- For a bounded error run with normalized final states, the assumed progress and POVM
estimates imply the general witness norm query bound [HoyerLeeSpalek2007]. -/
theorem clause16_engine_of_obligations
    (q n : ℕ) [NeZero q] (X W Y : Type) [Fintype X] [DecidableEq X] [Fintype W] [Fintype Y]
    (input : X → Fin n → Fin q) (f : X → Y)
    (Γ : Matrix X X ℂ) (C : Circuit ((Fin n × Fin q) × W))
    (psi : QState ((Fin n × Fin q) × W))
    (out : Y → Matrix ((Fin n × Fin q) × W) ((Fin n × Fin q) × W) ℂ) (eps : ℝ)
    (hG : Γ.IsHermitian) (hz : ∀ x y, f x = f y → Γ x y = 0)
    (hrun : IsBoundedErrorRun input f C psi out eps)
    (H1 : PhaseOracleProgressRunBound (W := W) input Γ)
    (H2 : PovmFinalProgressBound Γ f out eps)
    (Hnorm : ∀ x, Normalized (Run (phaseOracle (W := W) (input x)) C psi)) :
    (1 - 2 * Real.sqrt (eps * (1 - eps)) - 2 * eps) * ‖Γ‖ ≤
      2 * (QueryCount C) * maxFilterNorm input Γ := by
  have hC : IsUnitaryCircuit C := hrun.1
  have hpsi : Normalized psi := hrun.2.1
  have hpovm : IsPovm out := hrun.2.2.1
  have he0 : 0 ≤ eps := hrun.2.2.2.1
  have he1 : eps ≤ 1 / 2 := hrun.2.2.2.2.1
  have hsuccess : ∀ x, 1 - eps ≤
      povmProb out (f x) (Run (phaseOracle (W := W) (input x)) C psi) :=
    hrun.2.2.2.2.2
  by_cases hem : IsEmpty X
  · have hg0 : ‖Γ‖ = 0 := norm_eq_zero_of_isEmpty Γ
    rw [hg0, mul_zero]
    have hnn : (0 : ℝ) ≤ 2 * (QueryCount C) * maxFilterNorm input Γ :=
      mul_nonneg (by positivity) (maxFilterNorm_nonneg input Γ)
    exact hnn
  · have hne : Nonempty X := not_isEmpty_iff.mp hem
    haveI := hne
    obtain ⟨weight, lam, hw, hlam, _, hstart⟩ :=
      negative_adversary_extreme_eigenvector_and_start X _ Γ psi hG hpsi
    have hrunProg : |advProgress Γ weight (fun x =>
        Run (phaseOracle (W := W) (input x)) C psi) - lam| ≤
        2 * (QueryCount C) * maxFilterNorm input Γ := by
      have h := H1 weight C (fun _ => psi) hw hC (fun _ => hpsi)
      rw [hstart] at h
      exact h
    have hfin : |advProgress Γ weight (fun x =>
        Run (phaseOracle (W := W) (input x)) C psi)| ≤
        (2 * Real.sqrt (eps * (1 - eps)) + 2 * eps) * ‖Γ‖ :=
      H2 weight (fun x => Run (phaseOracle (W := W) (input x)) C psi)
        hG hw Hnorm hz he0 he1 hpovm hsuccess
    have htri := abs_sub_le lam
      (advProgress Γ weight (fun x => Run (phaseOracle (W := W) (input x)) C psi)) 0
    rw [sub_zero, sub_zero, abs_sub_comm lam] at htri
    rw [hlam] at htri
    nlinarith

/-- For Boolean inputs, the general coordinate filter equals `advFilter`. -/
theorem genAdvFilter_eq_advFilter {X : Type} {n : ℕ}
    (input : X → Fin n → Bool) (Γ : Matrix X X ℂ) (i : Fin n) :
    genAdvFilter input Γ i = advFilter input Γ i :=
  rfl

/-- Each Boolean coordinate filter norm is bounded by `advFilterBound`. -/
theorem advFilter_le_advFilterBound {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (input : X → Fin n → Bool) (Γ : Matrix X X ℂ) (i : Fin n) :
    ‖advFilter input Γ i‖ ≤ advFilterBound input Γ := by
  unfold advFilterBound
  have hmem : ‖advFilter input Γ i‖ ∈ List.ofFn (fun j : Fin n => ‖advFilter input Γ j‖) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  have helper : ∀ (l : List ℝ) (a z : ℝ), a ∈ l → a ≤ l.foldl max z := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih =>
      intro a z ha
      rcases List.mem_cons.mp ha with rfl | ha
      · have hm : ∀ (l : List ℝ) (z : ℝ), z ≤ l.foldl max z := by
          intro l
          induction l with
          | nil => intro z; exact le_rfl
          | cons b l ih => intro z; exact (le_max_left _ _).trans (ih _)
        exact (le_max_right z a).trans (hm l _)
      · exact ih a (max z b) ha
  exact helper _ _ _ hmem

/-- The supremum of the general Boolean filter norms is bounded by `advFilterBound`. -/
theorem maxFilterNorm_le_advFilterBound {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (input : X → Fin n → Bool) (Γ : Matrix X X ℂ) :
    maxFilterNorm input Γ ≤ advFilterBound input Γ := by
  have h : ∀ i : Fin n, ‖genAdvFilter input Γ i‖ ≤ advFilterBound input Γ := by
    intro i
    rw [genAdvFilter_eq_advFilter]
    exact advFilter_le_advFilterBound input Γ i
  have hge0 : (0:ℝ) ≤ advFilterBound input Γ := by
    have hm : ∀ (l : List ℝ) (z : ℝ), z ≤ l.foldl max z := by
      intro l; induction l with
      | nil => intro z; exact le_rfl
      | cons b l ih => intro z; exact (le_max_left _ _).trans (ih _)
    unfold advFilterBound
    exact hm _ _
  exact Real.iSup_le h hge0

/-- The Kushilevitz example has general adversary value at least `2 + 3 * sqrt 5 / 5`
[HoyerLeeSpalek2007]. -/
theorem advPmValue_kushilevitz_ge :
    ENNReal.ofReal (2 + 3 * Real.sqrt 5 / 5) ≤
      advPmValue kushilevitzInputW kushilevitzFunW := by
  obtain ⟨hHerm, hZero, hFB, hNorm⟩ := theorem21RealizedWitness
  have hc : (0:ℝ) ≤ 2 + 3 * Real.sqrt 5 / 5 := by nlinarith [Real.sqrt_nonneg 5]
  have hN : maxFilterNorm kushilevitzInputW kushilevitzGammaW ≤ 1 :=
    (maxFilterNorm_le_advFilterBound kushilevitzInputW kushilevitzGammaW).trans hFB
  have hNneg : (0:ℝ) ≤ maxFilterNorm kushilevitzInputW kushilevitzGammaW :=
    maxFilterNorm_nonneg _ _
  have hΓpos : (0:ℝ) < ‖kushilevitzGammaW‖ := by
    have := hNorm; nlinarith [Real.sqrt_nonneg 5]
  have hne : kushilevitzGammaW ≠ 0 := by
    intro hz
    have hbad : (2 + 3 * Real.sqrt 5 / 5:ℝ) ≤ 0 := by simpa [hz, norm_zero] using! hNorm
    nlinarith [Real.sqrt_nonneg 5]
  have hval : ENNReal.ofReal (2 + 3 * Real.sqrt 5 / 5) ≤
      advPmWitnessValue kushilevitzInputW kushilevitzGammaW := by
    unfold advPmWitnessValue
    by_cases hN0 : maxFilterNorm kushilevitzInputW kushilevitzGammaW = 0
    · have hΓne : ENNReal.ofReal ‖kushilevitzGammaW‖ ≠ 0 :=
        ENNReal.ofReal_ne_zero_iff.mpr hΓpos
      rw [hN0, ENNReal.ofReal_zero, ENNReal.div_zero hΓne]
      exact le_top
    · have hNne : ENNReal.ofReal (maxFilterNorm kushilevitzInputW kushilevitzGammaW) ≠ 0 :=
        ENNReal.ofReal_ne_zero_iff.mpr (lt_of_le_of_ne hNneg (Ne.symm hN0))
      have hΓne : ENNReal.ofReal ‖kushilevitzGammaW‖ ≠ 0 :=
        ENNReal.ofReal_ne_zero_iff.mpr hΓpos
      rw [ENNReal.le_div_iff_mul_le (Or.inr hΓne) (Or.inl ENNReal.ofReal_ne_top)]
      rw [← ENNReal.ofReal_mul hc]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [hNorm, hN, hc, Real.sqrt_nonneg 5]
  refine le_trans hval ?_
  exact le_iSup
    (fun Γ : {Γ : Matrix (Fin 20) (Fin 20) ℂ // Γ.IsHermitian ∧
      (∀ x y, kushilevitzFunW x = kushilevitzFunW y → Γ x y = 0) ∧ Γ ≠ 0} =>
      advPmWitnessValue kushilevitzInputW Γ.1) ⟨kushilevitzGammaW, hHerm, hZero, hne⟩

/-- The number of coordinates at which both six bit words are true. -/
private def commonBits (x y : Fin 6 → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i && y i).card

/-- Two distinct six bit words of weight three have Hamming distance at least two. -/
lemma hamming_two_le {x y : Fin 6 → Bool}
    (hx : kushilevitzWeightOf x = 3) (hy : kushilevitzWeightOf y = 3) (hxy : x ≠ y) :
    2 ≤ hamming x y := by
  classical
  have hpt : ∀ i : Fin 6,
      (if x i then (1:ℕ) else 0) + (if y i then 1 else 0) =
        (if x i ≠ y i then 1 else 0) + 2 * (if x i && y i then 1 else 0) := by
    intro i
    by_cases hx : x i <;> by_cases hy : y i <;> simp [hx, hy]
  have hsum := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hpt i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  rw [← Finset.mul_sum] at hsum
  have hwx : kushilevitzWeightOf x = ∑ i : Fin 6, (if x i then (1:ℕ) else 0) := by
    show (Finset.univ.filter fun i => x i).card = _
    exact (Finset.sum_boole (fun i => x i) Finset.univ).symm
  have hwy : kushilevitzWeightOf y = ∑ i : Fin 6, (if y i then (1:ℕ) else 0) := by
    show (Finset.univ.filter fun i => y i).card = _
    exact (Finset.sum_boole (fun i => y i) Finset.univ).symm
  have hh : hamming x y = ∑ i : Fin 6, (if x i ≠ y i then (1:ℕ) else 0) := by
    show (Finset.univ.filter fun i => x i ≠ y i).card = _
    exact (Finset.sum_boole (fun i => x i ≠ y i) Finset.univ).symm
  have hc : commonBits x y = ∑ i : Fin 6, (if x i && y i then (1:ℕ) else 0) := by
    show (Finset.univ.filter fun i => x i && y i).card = _
    exact (Finset.sum_boole (fun i => x i && y i) Finset.univ).symm
  have h6 : hamming x y + 2 * commonBits x y = 6 := by
    rw [hh, hc, ← hsum, ← hwx, ← hwy, hx, hy]
  have hne : hamming x y ≠ 0 := by
    intro h0
    have hall : ∀ i : Fin 6, x i = y i := by
      intro i
      by_contra hne'
      have hi : i ∈ Finset.univ.filter (fun j => x j ≠ y j) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hne'
      have h1 : (1:ℕ) ≤ hamming x y := by
        show (1:ℕ) ≤ (Finset.univ.filter fun j => x j ≠ y j).card
        exact Finset.one_le_card.mpr ⟨i, hi⟩
      omega
    exact hxy (funext hall)
  have hc2 : commonBits x y ≤ 2 := by
    by_contra hc'
    have h3 : (3:ℕ) ≤ commonBits x y := by omega
    have hge : hamming x y + 2 * 3 ≤ hamming x y + 2 * commonBits x y := by omega
    rw [h6] at hge
    have : hamming x y = 0 := by omega
    exact hne this
  omega

/-- Every input where `sixBitF` returns a Boolean has weight three. -/
lemma sixBitF_weight {w : Fin 6 → Bool} {b : Bool} (h : sixBitF w = some b) :
    kushilevitzWeightOf w = 3 := by
  by_contra hc
  have hnone : sixBitF w = none := by
    unfold sixBitF
    simp only [hc, if_false]
  rw [hnone] at h
  simp at h

/-- The infimum Hamming distance between false and true inputs of `sixBitF` is two. -/
lemma sixBitF_hamming_iInf :
    (⨅ w : {w : (Fin 6 → Bool) × (Fin 6 → Bool) //
        sixBitF w.1 = some false ∧ sixBitF w.2 = some true},
      ((hamming w.val.1 w.val.2 : ℕ) : ℝ)) = ((2:ℕ) : ℝ) := by
  haveI hneS : Nonempty {w : (Fin 6 → Bool) × (Fin 6 → Bool) //
      sixBitF w.1 = some false ∧ sixBitF w.2 = some true} :=
    ⟨⟨(kushilevitzInputW 0, kushilevitzInputW 17), by decide, by decide⟩⟩
  have hge : ((2:ℕ) : ℝ) ≤
      ⨅ w : {w : (Fin 6 → Bool) × (Fin 6 → Bool) //
          sixBitF w.1 = some false ∧ sixBitF w.2 = some true},
        ((hamming w.val.1 w.val.2 : ℕ) : ℝ) := by
    refine le_ciInf ?_
    intro w
    have hw1 : kushilevitzWeightOf w.val.1 = 3 := sixBitF_weight w.property.1
    have hw2 : kushilevitzWeightOf w.val.2 = 3 := sixBitF_weight w.property.2
    have hne : w.val.1 ≠ w.val.2 := by
      intro h
      have e := w.property.1
      rw [h] at e
      exact absurd (e.symm.trans w.property.2) (by simp)
    exact_mod_cast hamming_two_le hw1 hw2 hne
  have hbd : BddBelow
      (Set.range fun w : {w : (Fin 6 → Bool) × (Fin 6 → Bool) //
          sixBitF w.1 = some false ∧ sixBitF w.2 = some true} =>
        ((hamming w.val.1 w.val.2 : ℕ) : ℝ)) := by
    refine ⟨0, ?_⟩
    intro x hx
    obtain ⟨w, rfl⟩ := hx
    exact Nat.cast_nonneg _
  have hle : (⨅ w : {w : (Fin 6 → Bool) × (Fin 6 → Bool) //
      sixBitF w.1 = some false ∧ sixBitF w.2 = some true},
        ((hamming w.val.1 w.val.2 : ℕ) : ℝ))
      ≤ ((hamming (kushilevitzInputW 0) (kushilevitzInputW 17) : ℕ) : ℝ) := by
    refine ciInf_le hbd ⟨(kushilevitzInputW 0, kushilevitzInputW 17), by decide, by decide⟩
  have hp : hamming (kushilevitzInputW 0) (kushilevitzInputW 17) = 2 := by decide
  rw [hp] at hle
  exact le_antisymm hle hge

/-- The relative Hamming distance of `sixBitF` equals one third. -/
theorem relativeHamming_sixBitF : relativeHamming sixBitF = 1/3 := by
  unfold relativeHamming
  simp only [if_neg (by norm_num : ¬(6:ℕ) = 0)]
  rw [sixBitF_hamming_iInf]
  norm_num

/-- The real power `3 ^ 1.098` is at most `2 + 3 * sqrt 5 / 5`. -/
lemma three_rpow_1098_le : (3:ℝ) ^ (1.098:ℝ) ≤ 2 + 3 * Real.sqrt 5 / 5 := by
  have hE1lo : 2.7182812 ≤ Real.exp 1 := by
    have h := Real.exp_bound (x := 1) (by norm_num) (n := 10) (by norm_num)
    have h3 := (abs_sub_le_iff.1 h).2
    have hE : |(1:ℝ)| ^ 10 * (((Nat.succ 10:ℕ):ℝ) / (((Nat.factorial 10:ℕ):ℝ) * ((10:ℕ):ℝ)))
        = (11:ℝ)/36288000 := by norm_num [Nat.factorial]
    rw [hE] at h3
    have h4 : (2.7182812:ℝ) + (11:ℝ)/36288000 ≤
        ∑ m ∈ Finset.range 10, (1:ℝ)^m / m.factorial := by
      repeat rw [Finset.sum_range_succ]
      norm_num [Nat.factorial]
    linarith
  have hE3lo : 1.1037349 ≤ Real.exp 0.0987 := by
    have h := Real.exp_bound (x := 0.0987) (by norm_num) (n := 5) (by norm_num)
    have h3 := (abs_sub_le_iff.1 h).2
    have hE : |(0.0987:ℝ)| ^ 5 * (((Nat.succ 5:ℕ):ℝ) / (((Nat.factorial 5:ℕ):ℝ) * ((5:ℕ):ℝ)))
        = 936668172433707 / 10^22 := by norm_num [Nat.factorial]
    rw [hE] at h3
    have h4 : (1.1037349:ℝ) + 936668172433707 / 10^22 ≤
        ∑ m ∈ Finset.range 5, (0.0987:ℝ)^m / m.factorial := by
      repeat rw [Finset.sum_range_succ]
      norm_num [Nat.factorial]
    linarith
  have hE1hi : Real.exp 1 ≤ 2.7182819 := by
    refine le_trans
      (Real.exp_bound' (x := 1) (by norm_num) (by norm_num) (n := 10) (by norm_num)) ?_
    repeat rw [Finset.sum_range_succ]
    norm_num [Nat.factorial]
  have hE2hi : Real.exp 0.2063726 ≤ 1.229212 := by
    refine le_trans
      (Real.exp_bound' (x := 0.2063726) (by norm_num) (by norm_num) (n := 5) (by norm_num)) ?_
    repeat rw [Finset.sum_range_succ]
    norm_num [Nat.factorial]
  have hs5 : (2.2360679:ℝ) ≤ Real.sqrt 5 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hexpL : (3:ℝ) ≤ Real.exp 1.0987 := by
    have hsplit : (1.0987:ℝ) = 1 + 0.0987 := by norm_num
    rw [hsplit, Real.exp_add]
    have hprod : (2.7182812:ℝ) * 1.1037349 ≤ Real.exp 1 * Real.exp 0.0987 :=
      mul_le_mul hE1lo hE3lo (by norm_num) (Real.exp_pos _).le
    have hnum : (3:ℝ) ≤ 2.7182812 * 1.1037349 := by norm_num
    exact le_trans hnum hprod
  have hlog3 : Real.log 3 ≤ 1.0987 := (Real.log_le_iff_le_exp (by norm_num)).mpr hexpL
  have hrpow : (3:ℝ) ^ (1.098:ℝ) = Real.exp (Real.log 3 * 1.098) :=
    Real.rpow_def_of_pos (by norm_num) _
  rw [hrpow]
  have hyle : Real.log 3 * 1.098 ≤ 1.2063726 := by
    have h := mul_le_mul_of_nonneg_right hlog3 (by norm_num : (0:ℝ) ≤ 1.098)
    have hnum : (1.0987:ℝ) * 1.098 = 1.2063726 := by norm_num
    rw [hnum] at h
    exact h
  refine le_trans (Real.exp_le_exp.mpr hyle) ?_
  have hsplit2 : (1.2063726:ℝ) = 1 + 0.2063726 := by norm_num
  rw [hsplit2, Real.exp_add]
  have hprod2 : Real.exp 1 * Real.exp 0.2063726 ≤ 2.7182819 * 1.229212 :=
    mul_le_mul hE1hi hE2hi (Real.exp_pos _).le (by norm_num)
  refine le_trans hprod2 ?_
  have hA : (2.7182819:ℝ) * 1.229212 ≤ 2 + 3 * (2.2360679:ℝ) / 5 := by norm_num
  refine le_trans hA ?_
  gcongr

/-- The Kushilevitz adversary value is at least the inverse relative Hamming distance of
`sixBitF` raised to `1.098`. -/
theorem advPmValue_kushilevitz_rate :
    ENNReal.ofReal ((1 / relativeHamming sixBitF) ^ (1.098 : ℝ)) ≤
      advPmValue kushilevitzInputW kushilevitzFunW := by
  have hbase : (1 / relativeHamming sixBitF) = (3:ℝ) := by
    rw [relativeHamming_sixBitF]
    norm_num
  rw [hbase]
  exact le_trans (ENNReal.ofReal_le_ofReal three_rpow_1098_le) advPmValue_kushilevitz_ge

/-- An if expression is independent of the chosen decision procedure for its proposition. -/
lemma ite_eq_ite_of_decidable {p : Prop} {d1 d2 : Decidable p} {α : Sort*} {a b : α} :
    @ite α p d1 a b = @ite α p d2 a b := by
  cases d1 with
  | isTrue h => cases d2 with
    | isTrue h' => rfl
    | isFalse h' => exact absurd h h'
  | isFalse h => cases d2 with
    | isTrue h' => exact absurd h' h
    | isFalse h' => rfl

/-- A set is a certificate exactly when every input either has the same output or fails to agree
on that set. -/
lemma IsCertificate_iff {m : ℕ} {h : (Fin m → Bool) → Bool} {x : Fin m → Bool}
    (S : Finset (Fin m)) :
    IsCertificate h x S ↔ ∀ y, h y = h x ∨ ¬(∀ i ∈ S, y i = x i) := by
  unfold IsCertificate
  constructor
  · intro H y
    by_cases hh : ∀ i ∈ S, y i = x i
    · exact Or.inl (H y hh)
    · exact Or.inr hh
  · intro H y hy
    cases H y with
    | inl e => exact e
    | inr nh => exact absurd hy nh

instance instDecidableIsCertificate {m : ℕ} (h : (Fin m → Bool) → Bool) (x : Fin m → Bool)
    (S : Finset (Fin m)) : Decidable (IsCertificate h x S) :=
  decidable_of_iff _ (IsCertificate_iff S).symm

/-- The minimum certificate size is the infimum of certificate cardinalities, assigning top to
sets that are not certificates. -/
lemma minCertSize_eq_iInf {m : ℕ} {h : (Fin m → Bool) → Bool} {x : Fin m → Bool} :
    minCertSize h x = ⨅ T : Finset (Fin m),
      (if IsCertificate h x T then (T.card : WithTop ℕ) else ⊤) := by
  unfold minCertSize
  exact congrArg iInf (funext fun T => ite_eq_ite_of_decidable)

/-- The minimum certificate size is at most the cardinality of any certificate. -/
lemma minCertSize_le_card {m : ℕ} {h : (Fin m → Bool) → Bool} {x : Fin m → Bool}
    {S : Finset (Fin m)} (hc : IsCertificate h x S) : minCertSize h x ≤ S.card := by
  rw [minCertSize_eq_iInf]
  refine le_trans (iInf_le (fun T : Finset (Fin m) =>
      if IsCertificate h x T then (T.card : WithTop ℕ) else ⊤) S) ?_
  simp [hc]

/-- A natural number bounding every certificate cardinality from below also bounds the minimum
certificate size from below. -/
lemma le_minCertSize {m : ℕ} {h : (Fin m → Bool) → Bool} {x : Fin m → Bool} {n : ℕ}
    (H : ∀ S : Finset (Fin m), IsCertificate h x S → n ≤ S.card) :
    (n : WithTop ℕ) ≤ minCertSize h x := by
  rw [minCertSize_eq_iInf]
  refine le_iInf ?_
  intro T
  by_cases hT : IsCertificate h x T
  · simp [hT]
    exact_mod_cast H T hT
  · simp [hT]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in

/-- Every input of `monotoneSixBitG` has a certificate of cardinality at most three. -/
lemma exists_cert_le_three : ∀ x : Fin 6 → Bool, ∃ S : Finset (Fin 6),
    S.card ≤ 3 ∧ IsCertificate monotoneSixBitG x S := by decide

/-- The minimum certificate size of `monotoneSixBitG` is at most three at every input. -/
lemma minCertSize_le_three (x : Fin 6 → Bool) :
    minCertSize monotoneSixBitG x ≤ 3 := by
  obtain ⟨S, hS, hc⟩ := exists_cert_le_three x
  have := minCertSize_le_card hc
  have hcast : (S.card : WithTop ℕ) ≤ 3 := by exact_mod_cast hS
  exact le_trans this hcast

/-- The six bit word with every bit false. -/
def allZeros : Fin 6 → Bool := fun _ => false

/-- The six bit word with every bit true. -/
def allOnes : Fin 6 → Bool := fun _ => true

/-- The monotone six bit function returns false on the all zero word. -/
lemma allZeros_g : monotoneSixBitG allZeros = false := by decide

/-- The monotone six bit function returns true on the all one word. -/
lemma allOnes_g : monotoneSixBitG allOnes = true := by decide

/-- The Kushilevitz word weight equals the number of true coordinates. -/
lemma kushilevitzWeightOf_eq_card (w : Fin 6 → Bool) :
    kushilevitzWeightOf w = (Finset.univ.filter fun i => w i).card := rfl

/-- Every certificate of the all zero input for `monotoneSixBitG` needs at least three
coordinates. -/
lemma three_le_minCertSize_allZeros : (3 : WithTop ℕ) ≤ minCertSize monotoneSixBitG allZeros := by
  refine le_minCertSize (n := 3) ?_
  intro S hc
  by_contra hlt
  have hS2 : S.card ≤ 2 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hlt)
  let y : Fin 6 → Bool := fun i => if i ∈ S then false else true
  have hyS : ∀ i ∈ S, y i = allZeros i := by
    intro i hi
    simp [y, allZeros, hi]
  have hcon := hc y hyS
  have hcard : kushilevitzWeightOf y = 6 - S.card := by
    have h1 : (Finset.univ.filter fun i => y i) = (Sᶜ : Finset (Fin 6)) := by
      ext i
      simp [y, Finset.mem_compl]
    rw [kushilevitzWeightOf_eq_card, h1, Finset.card_compl, Fintype.card_fin]
  have h4 : 4 ≤ kushilevitzWeightOf y := by omega
  have hyg : monotoneSixBitG y = true := by
    unfold monotoneSixBitG
    show (if 4 ≤ kushilevitzWeightOf y then true
      else if kushilevitzWeightOf y = 3 then kushilevitzIsOneWord y else false) = true
    simp [h4]
  rw [hyg, allZeros_g] at hcon
  exact absurd hcon (by simp)

/-- Every certificate of the all one input for `monotoneSixBitG` needs at least three
coordinates. -/
lemma three_le_minCertSize_allOnes : (3 : WithTop ℕ) ≤ minCertSize monotoneSixBitG allOnes := by
  refine le_minCertSize (n := 3) ?_
  intro S hc
  by_contra hlt
  have hS2 : S.card ≤ 2 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hlt)
  let y : Fin 6 → Bool := fun i => if i ∈ S then true else false
  have hyS : ∀ i ∈ S, y i = allOnes i := by
    intro i hi
    simp [y, allOnes, hi]
  have hcon := hc y hyS
  have hcard : kushilevitzWeightOf y = S.card := by
    have h1 : (Finset.univ.filter fun i => y i) = S := by
      ext i
      simp [y]
    rw [kushilevitzWeightOf_eq_card, h1]
  have h2 : kushilevitzWeightOf y ≤ 2 := by omega
  have hyg : monotoneSixBitG y = false := by
    unfold monotoneSixBitG
    show (if 4 ≤ kushilevitzWeightOf y then true
      else if kushilevitzWeightOf y = 3 then kushilevitzIsOneWord y else false) = false
    have hnot4 : ¬(4 ≤ kushilevitzWeightOf y) := by omega
    have hne3 : kushilevitzWeightOf y ≠ 3 := by omega
    simp [hnot4, hne3]
  rw [hyg, allOnes_g] at hcon
  exact absurd hcon (by simp)

/-- Output specific certificate complexity is the supremum of minimum certificate sizes, with
zero for inputs of the other output. -/
lemma certComplexity_eq_iSup {m : ℕ} {h : (Fin m → Bool) → Bool} {b : Bool} :
    certComplexity h b = ⨆ x : Fin m → Bool,
      (if h x = b then minCertSize h x else 0) := by
  unfold certComplexity
  exact congrArg iSup (funext fun x => ite_eq_ite_of_decidable)

/-- The false and true certificate complexities of `monotoneSixBitG` both equal three. -/
theorem certComplexity_monotoneSixBitG_eq_three :
    certComplexity monotoneSixBitG false = 3 ∧
    certComplexity monotoneSixBitG true = 3 := by
  constructor
  · have hle : certComplexity monotoneSixBitG false ≤ 3 := by
      rw [certComplexity_eq_iSup]
      refine iSup_le ?_
      intro x
      by_cases hx : monotoneSixBitG x = false
      · simp [hx]
        exact minCertSize_le_three x
      · simp [hx]
    have hge : (3 : WithTop ℕ) ≤ certComplexity monotoneSixBitG false := by
      rw [certComplexity_eq_iSup]
      refine le_trans three_le_minCertSize_allZeros ?_
      have hbridge : minCertSize monotoneSixBitG allZeros ≤
          (if monotoneSixBitG allZeros = false then minCertSize monotoneSixBitG allZeros else 0) := by
        simp [allZeros_g]
      exact le_trans hbridge (le_iSup
        (fun x : Fin 6 → Bool => if monotoneSixBitG x = false then minCertSize monotoneSixBitG x else 0)
        allZeros)
    exact le_antisymm hle hge
  · have hle : certComplexity monotoneSixBitG true ≤ 3 := by
      rw [certComplexity_eq_iSup]
      refine iSup_le ?_
      intro x
      by_cases hx : monotoneSixBitG x = true
      · simp [hx]
        exact minCertSize_le_three x
      · simp [hx]
    have hge : (3 : WithTop ℕ) ≤ certComplexity monotoneSixBitG true := by
      rw [certComplexity_eq_iSup]
      refine le_trans three_le_minCertSize_allOnes ?_
      have hbridge : minCertSize monotoneSixBitG allOnes ≤
          (if monotoneSixBitG allOnes = true then minCertSize monotoneSixBitG allOnes else 0) := by
        simp [allOnes_g]
      exact le_trans hbridge (le_iSup
        (fun x : Fin 6 → Bool => if monotoneSixBitG x = true then minCertSize monotoneSixBitG x else 0)
        allOnes)
    exact le_antisymm hle hge

end Qatlib.Concepts.AdversaryBounds.AdvDuality
