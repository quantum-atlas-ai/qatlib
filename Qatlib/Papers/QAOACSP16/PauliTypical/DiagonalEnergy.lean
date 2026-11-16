/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAOACSP16.PredicateFour.Typicality.SourceTypicality
public import Qatlib.Papers.QAOACSP16.TypicalQaoa.Concentration.SourceCSPConcentration
public import Qatlib.Papers.QAOACSP16.PredicateFour.FamilySupport
public import Mathlib.Tactic

@[expose] public section


/-! Finite diagonal Hamiltonians and their reduction to Boolean satisfaction values. -/
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Papers.QAOACSP16.PredicateFour.CSPModel
open Qatlib.Papers.QAOACSP16.PredicateFour.CSPFamily
open Qatlib.Papers.QAOACSP16.TypicalQaoa.QaoaState
open Qatlib.Papers.QAOACSP16.PredicateFour.Typicality
open Qatlib.Papers.QAOACSP16.PredicateFour.FamilySupport
open scoped BigOperators

namespace Qatlib.Papers.QAOACSP16.PauliTypical.DiagonalEnergy
variable {V : Type} [Fintype V] [DecidableEq V]
variable {P : Type} [Fintype P] [DecidableEq P]

/-- A traceless `Z`-diagonal `k`-local Hamiltonian with random zero-mean
weights of `Θ(1)` size.  Tracelessness is automatic: every scope is nonempty,
so the uniform assignment mean of every term vanishes. -/
structure ZHamiltonian (V : Type) (P : Type) [Fintype V] [Fintype P] [DecidableEq P] where
  /-- Number of Pauli terms. -/
  m : ℕ
  /-- Nonempty Hamiltonian. -/
  hm : 0 < m
  /-- The scope (support) of every Pauli term. -/
  scope : Fin m → Finset V
  /-- Every term has nonempty support. -/
  scope_nonempty : ∀ l, (scope l).Nonempty
  /-- The random weight of every term. -/
  weight : Fin m → P → ℝ
  /-- Independence law of the weights (product law below). -/
  law : FinDist P
  /-- Zero mean (Corollary 7's hypothesis). -/
  weight_zero_mean : ∀ l, law.expect (weight l) = 0
  /-- `Θ(1)` weights, normalised to `[-1,1]`. -/
  weight_mem : ∀ l p, weight l p ∈ Set.Icc (-1 : ℝ) 1

/-- The energy (Rayleigh quotient of the product basis state `|z⟩`) of the
sampled Hamiltonian: `⟨z|H_ω|z⟩ = ∑_l w_l χ_{S_l}(z)`. -/
def ZHamiltonian.energy (H : ZHamiltonian V P) (ω : Fin H.m → P) (z : V → Bool) : ℝ :=
  ∑ l : Fin H.m, H.weight l (ω l) * charFun (H.scope l) z

/-- The smallest eigenvalue of the diagonal Hamiltonian: the minimum of its
energy over computational-basis states.  For a `Z`-diagonal matrix on the cube
this is `λmin(H_ω)`. -/
def ZHamiltonian.lambdaMin (H : ZHamiltonian V P) (ω : Fin H.m → P) : ℝ :=
  sInf (Set.range (H.energy ω))

omit [DecidableEq V] in
/-- Every computational-basis product state has Rayleigh quotient at least
`λmin` (the elementary variational bound). -/
theorem ZHamiltonian.lambdaMin_le (H : ZHamiltonian V P) (ω : Fin H.m → P)
    (z : V → Bool) : H.lambdaMin ω ≤ H.energy ω z :=
  csInf_le (Set.finite_range (H.energy ω)).bddBelow ⟨z, rfl⟩

/-- The CSP predicate `ψ_l(z) = (1 - w_l χ_{S_l}(z))/2` associated with a
Hamiltonian term.  Maximising satisfaction minimises energy. -/
def ZHamiltonian.pred (H : ZHamiltonian V P) (l : Fin H.m) (p : P) : Predicate V where
  scope := H.scope l
  val := fun z => (1 - H.weight l p * charFun (H.scope l) z) / 2
  locality := by
    intro z z' h
    have hχ : charFun (H.scope l) z = charFun (H.scope l) z' := by
      unfold charFun
      apply Finset.prod_congr rfl
      intro v hv
      rw [h v hv]
    rw [hχ]

/-- The associated CSP family. -/
def ZHamiltonian.toFamily (H : ZHamiltonian V P) : CSPFamily V P where
  m := H.m
  hm := H.hm
  scope := H.scope
  pred := H.pred
  pred_scope := fun _ _ => rfl
  law := H.law

/-- The uniform mean of `ψ_l` is `1/2` (the character has zero uniform mean). -/
theorem ZHamiltonian.constraintMean_pred (H : ZHamiltonian V P) (l : Fin H.m) (p : P) :
    constraintMean (H.pred l p) = 1 / 2 := by
  have hS : (H.scope l).Nonempty := H.scope_nonempty l
  simp only [ZHamiltonian.pred, constraintMean, uniformExpect]
  have hsum : (∑ z : V → Bool, (1 - H.weight l p * charFun (H.scope l) z))
      = (Fintype.card (V → Bool) : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, sum_charFun_eq_zero hS]
    ring
  have h1 : (∑ z : V → Bool, (1 - H.weight l p * charFun (H.scope l) z) / 2)
      = (∑ z, (1 - H.weight l p * charFun (H.scope l) z)) / 2 := by
    rw [Finset.sum_div]
  calc (∑ z : V → Bool, (1 - H.weight l p * charFun (H.scope l) z) / 2)
        / (Fintype.card (V → Bool) : ℝ)
      = ((∑ z, (1 - H.weight l p * charFun (H.scope l) z)) / 2)
          / (Fintype.card (V → Bool) : ℝ) := by rw [h1]
    _ = ((Fintype.card (V → Bool) : ℝ) / 2) / (Fintype.card (V → Bool) : ℝ) := by rw [hsum]
    _ = 1 / 2 := by
      have hpos : (0 : ℝ) < (Fintype.card (V → Bool) : ℝ) := by positivity
      field_simp [hpos.ne']

/-- The associated CSP is typical: the weight has zero mean. -/
theorem ZHamiltonian.toFamily_typical (H : ZHamiltonian V P) : H.toFamily.Typical := by
  intro l z
  have hfun : (fun p : P => (H.pred l p).val z - constraintMean (H.pred l p))
      = fun p => (-(charFun (H.scope l) z / 2)) * H.weight l p := by
    funext p
    rw [H.constraintMean_pred l p]
    show (1 - H.weight l p * charFun (H.scope l) z) / 2 - 1 / 2
        = -(charFun (H.scope l) z / 2) * H.weight l p
    ring
  show H.law.expect (fun p : P =>
      (H.pred l p).val z - constraintMean (H.pred l p)) = 0
  rw [hfun, expect_const_mul, H.weight_zero_mean l, mul_zero]

/-- Predicates associated with `Θ(1)` weights take values in `[0,1]`. -/
theorem ZHamiltonian.pred_mem (H : ZHamiltonian V P) (l : Fin H.m) (p : P) (z : V → Bool) :
    (H.pred l p).val z ∈ Set.Icc (0 : ℝ) 1 := by
  have hw := H.weight_mem l p
  have hχ := charFun_eq_one_or_neg_one (H.scope l) z
  show (1 - H.weight l p * charFun (H.scope l) z) / 2 ∈ Set.Icc (0 : ℝ) 1
  rcases hχ with h | h <;> rw [h] <;> constructor <;> nlinarith [hw.1, hw.2]

/-- The associated CSP has Boolean-range predicates. -/
theorem ZHamiltonian.booleanValues (H : ZHamiltonian V P) : H.toFamily.BooleanValues := by
  intro l p z
  exact H.pred_mem l p z

/-- `μ = 1/2` for the associated CSP. -/
theorem ZHamiltonian.muFamily_eq_half (H : ZHamiltonian V P) :
    H.toFamily.muFamily = 1 / 2 := by
  unfold CSPFamily.muFamily
  show (∑ l : Fin H.m, H.toFamily.law.expect
        (fun p : P => constraintMean (H.toFamily.pred l p))) / (H.m : ℝ) = 1 / 2
  have hone : ∀ l : Fin H.m,
      H.toFamily.law.expect (fun p : P => constraintMean (H.toFamily.pred l p)) = 1 / 2 := by
    intro l
    have hfun : (fun p : P => constraintMean (H.toFamily.pred l p)) = fun _ => (1 / 2 : ℝ) := by
      funext p
      exact H.constraintMean_pred l p
    rw [hfun, expect_const]
  have hsum : (∑ l : Fin H.m, H.toFamily.law.expect
        (fun p : P => constraintMean (H.toFamily.pred l p)))
      = ∑ _l : Fin H.m, (1 / 2 : ℝ) :=
    Finset.sum_congr rfl fun l _ => hone l
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmR : (0 : ℝ) < (H.m : ℝ) := by exact_mod_cast H.hm
  field_simp [hmR.ne']

omit [DecidableEq V] in
/-- Rewriting the satisfied count in terms of the energy:
`satValue = m/2 - energy/2`. -/
theorem ZHamiltonian.satValue_eq (H : ZHamiltonian V P) (ω : Fin H.m → P)
    (z : V → Bool) :
    satValue (H.toFamily.instance ω) z = (H.m : ℝ) / 2 - (1 / 2) * H.energy ω z := by
  unfold satValue ZHamiltonian.energy
  show (∑ x : Fin H.m, (1 - H.weight x (ω x) * charFun (H.scope x) z) / 2)
      = (H.m : ℝ) / 2 - (1 / 2) * ∑ l : Fin H.m,
          H.weight l (ω l) * charFun (H.scope l) z
  have hterm : ∀ l : Fin H.m, (1 - H.weight l (ω l) * charFun (H.scope l) z) / 2
      = 1 / 2 - (1 / 2) * (H.weight l (ω l) * charFun (H.scope l) z) := by
    intro l; ring
  have hsumc : (∑ x : Fin H.m, (1 - H.weight x (ω x) * charFun (H.scope x) z) / 2)
      = ∑ x : Fin H.m,
          (1 / 2 - (1 / 2) * (H.weight x (ω x) * charFun (H.scope x) z)) :=
    Finset.sum_congr rfl fun l _ => hterm l
  rw [hsumc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

omit [DecidableEq V] in
/-- If the satisfied fraction exceeds `1/2 + c/(2√l)`, the energy is below
`-c m/√l`. -/
theorem ZHamiltonian.energy_le_of_satFraction (H : ZHamiltonian V P) (c : ℝ)
    (D : ℕ) (hD : 0 < D) (ω : Fin H.m → P) (z : V → Bool)
    (h : (1 / 2 : ℝ) + c / (2 * Real.sqrt (D : ℝ))
        ≤ satFraction (H.toFamily.instance ω) z) :
    H.energy ω z ≤ -c * (H.m : ℝ) / Real.sqrt (D : ℝ) := by
  have hmR : (0 : ℝ) < (H.m : ℝ) := by exact_mod_cast H.hm
  have hsqrt : (0 : ℝ) < Real.sqrt (D : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hD)
  have hmul : ((1 / 2 : ℝ) + c / (2 * Real.sqrt (D : ℝ))) * (H.m : ℝ)
      ≤ satValue (H.toFamily.instance ω) z := by
    rw [satFraction] at h
    exact (le_div_iff₀ hmR).mp h
  rw [H.satValue_eq ω z] at hmul
  have heq : ((1 / 2 : ℝ) + c / (2 * Real.sqrt (D : ℝ))) * (H.m : ℝ)
      = (H.m : ℝ) / 2 + c * (H.m : ℝ) / (2 * Real.sqrt (D : ℝ)) := by
    ring
  rw [heq] at hmul
  have hB : c * (H.m : ℝ) / (2 * Real.sqrt (D : ℝ))
      ≤ -(1 / 2) * H.energy ω z := by linarith
  have hE : H.energy ω z
      ≤ -2 * (c * (H.m : ℝ) / (2 * Real.sqrt (D : ℝ))) := by linarith
  have hfin : -2 * (c * (H.m : ℝ) / (2 * Real.sqrt (D : ℝ)))
      = -c * (H.m : ℝ) / Real.sqrt (D : ℝ) := by
    field_simp [hsqrt.ne']
  linarith [hE, hfin]


end Qatlib.Papers.QAOACSP16.PauliTypical.DiagonalEnergy
