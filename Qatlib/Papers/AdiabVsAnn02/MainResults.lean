/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Operations
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Logic.Function.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Order.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Defs
import Qatlib.Concepts.GibbsMetropolis.RationalBath.DiagonalMetropolisKernel

/-!
# Symmetric costs, spike barriers, and bush Hamiltonians

This module defines symmetric, spike, and bush cost functions and their reduced Hamiltonians,
together with spectral-gap functions, Boltzmann weights, and effective potentials. It proves
elementary gap nonnegativity, polynomially weighted decay of suppressed transition
probabilities, and free-energy derivative and monotonicity estimates, including
`source_spike_annealing_hung_up`, `source_bush_annealing_fails`, and
`freeEnergySym_critical_strictAnti`. The mathematical context is [FarhiGoldstoneGutmann2002].

## Main statements

* `source_spike_annealing_hung_up`: At inverse temperature `Real.log 3`, the spike-crossing
  acceptance tends to zero after multiplication by any fixed natural power of `m`.
* `source_bush_annealing_fails`: At temperature strictly between zero and one, the polynomially
  weighted distinguished-bit flip acceptance tends to zero, and the normalized false-bit weight
  at full Hamming weight equals `1 / 2 ^ n`.
* `freeEnergySym_critical_strictAnti`: For `q ≥ 3` and `4 * q - 2 < a1 < a2`, critical points
  `u1` and `u2` of the corresponding free energies in `(1 / 2, 1)` satisfy `u2 < u1`.

## References

* [Farhi et al., 2002][FarhiGoldstoneGutmann2002]
-/

set_option autoImplicit false
noncomputable section

open Matrix BigOperators
open Filter
open scoped BigOperators Topology

namespace Qatlib.Papers.AdiabVsAnn02.MainResults

/-- The natural-number value of a Boolean bit, equal to one for `true` and zero for `false`. -/
def bitToNat (b : Bool) : ℕ := if b then 1 else 0

/-- The number of true bits in a Boolean string indexed by `Fin n`. -/
def hammingWeight {n : ℕ} (z : Fin n → Bool) : ℕ := ∑ i, bitToNat (z i)

/-- The three-bit cost equal to zero at weight zero, `q` at weight one, and one at weights two
and three. -/
def h3 (q : ℕ) (z z' z'' : Bool) : ℝ :=
  let s := bitToNat z + bitToNat z' + bitToNat z''
  if s = 0 then 0 else if s = 1 then (q : ℝ) else 1

/-- The symmetric three-bit cost polynomial as a function of the parameter `q`, string length
`n`, and Hamming weight `w`. -/
def cost13 (q n w : ℕ) : ℝ :=
  ((q : ℝ) / 2) * (w : ℝ) * ((n : ℝ) - (w : ℝ)) * ((n : ℝ) - (w : ℝ) - 1)
    + (1 / 2 : ℝ) * (w : ℝ) * ((w : ℝ) - 1) * ((n : ℝ) - (w : ℝ))
    + (1 / 6 : ℝ) * (w : ℝ) * ((w : ℝ) - 1) * ((w : ℝ) - 2)

/-- The cubic scaled symmetric cost `4 * q * u * (1 - u) ^ 2 + 4 * u ^ 2 * (1 - u) + (4 / 3) * u
^ 3`. -/
def gSym (q : ℝ) (u : ℝ) : ℝ :=
  4 * q * u * (1 - u) ^ 2 + 4 * u ^ 2 * (1 - u) + (4 / 3) * u ^ 3

/-- The interpolation of the transverse-field potential `2 * (1 - Real.sin θ)` with the scaled
symmetric cost at `(1 - Real.cos θ) / 2`. -/
def effectivePotential (q : ℝ) (θ s : ℝ) : ℝ :=
  2 * (1 - s) * (1 - Real.sin θ)
    + s * gSym q ((1 / 2) * (1 - Real.cos θ))

/-- The rescaled cost `(n / 2) ^ 3 * g (w / n)` associated with a real function `g`. -/
def scaledCost (g : ℝ → ℝ) (n w : ℕ) : ℝ :=
  ((n : ℝ) / 2) ^ 3 * g ((w : ℝ) / (n : ℝ))

/-- The inverse hyperbolic cosine of the normalized effective-potential barrier above its value
at `θ1`. -/
def instantonPhase (q sStar θ1 θ : ℝ) : ℝ :=
  Real.arcosh
    (1 + (effectivePotential q θ sStar - effectivePotential q θ1 sStar)
      / (2 * (1 - sStar) * Real.sin θ))

/-- Half the interval integral of `instantonPhase q sStar θ1 θ * Real.sin θ` from `θ1` to `θ2`. -/
def instantonAction (q sStar θ1 θ2 : ℝ) : ℝ :=
  (1 / 2) * ∫ θ in θ1..θ2, instantonPhase q sStar θ1 θ * Real.sin θ

/-- The unnormalized Boltzmann weight of Hamming weight `w`, including the binomial multiplicity
`Nat.choose n w`. -/
def boltzmannWeight (n : ℕ) (h : ℕ → ℝ) (τ : ℝ) (w : ℕ) : ℝ :=
  (Nat.choose n w : ℝ) * Real.exp (-(h w) / τ)

/-- The scaled symmetric cost plus `a` times the logarithmic binary entropy term `(1 - u) *
Real.log (1 - u) + u * Real.log u`. -/
def freeEnergySym (q a u : ℝ) : ℝ :=
  a * ((1 - u) * Real.log (1 - u) + u * Real.log u) + gSym q u

/-- The thermal Metropolis acceptance from energy zero to energy `Δ` at inverse temperature `β`. -/
def twoLevelAcceptance (Δ β : ℝ) : ℝ :=
  Qatlib.Concepts.GibbsMetropolis.RationalBath.thermalAcceptance
    (fun k : Fin 2 => if k = 0 then 0 else Δ) β 0 1

/-- The two-level Metropolis acceptance equals `min 1 (Real.exp (-β * Δ))`
[FarhiGoldstoneGutmann2002]. -/
theorem twoLevelAcceptance_eq (Δ β : ℝ) :
    twoLevelAcceptance Δ β = min 1 (Real.exp (-β * Δ)) := by
  unfold twoLevelAcceptance
  rw [Qatlib.Concepts.GibbsMetropolis.RationalBath.thermalAcceptance]
  norm_num

/-- For nonnegative energy increment and inverse temperature, two-level acceptance is at most
`Real.exp (-β * Δ)`. -/
theorem twoLevelAcceptance_le_exp (Δ β : ℝ) (_hΔ : 0 ≤ Δ) (_hβ : 0 ≤ β) :
    twoLevelAcceptance Δ β ≤ Real.exp (-β * Δ) := by
  rw [twoLevelAcceptance_eq]
  exact min_le_right _ _

/-- The two-level acceptance is nonnegative for every real energy increment and inverse
temperature. -/
theorem twoLevelAcceptance_nonneg (Δ β : ℝ) : 0 ≤ twoLevelAcceptance Δ β := by
  rw [twoLevelAcceptance_eq]
  exact le_min zero_le_one (Real.exp_pos _).le

/-- The real tridiagonal matrix of the spin-`n / 2` transverse component in the Hamming-weight
basis. -/
def spinSx (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j =>
    if ((i : ℕ) + 1 = (j : ℕ)) then
      ((1 / 2 : ℝ) * Real.sqrt (((i : ℕ) + 1 : ℝ) * ((n : ℝ) - (i : ℝ))))
    else if ((j : ℕ) + 1 = (i : ℕ)) then
      ((1 / 2 : ℝ) * Real.sqrt ((i : ℝ) * ((n : ℝ) - (i : ℝ) + 1)))
    else 0

/-- The transverse spin matrix `spinSx n` is Hermitian. -/
theorem spinSx_isHermitian (n : ℕ) : (spinSx n).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [spinSx, star_trivial]
  by_cases h1 : ((i : ℕ) + 1 = (j : ℕ))
  · have h2 : ¬ ((j : ℕ) + 1 = (i : ℕ)) := by omega
    have hcast : (j : ℝ) = (i : ℝ) + 1 := by
      rw [← h1]; push_cast; ring
    simp only [h1, h2, if_true, if_false]
    rw [hcast]
    ring_nf
  · by_cases h2 : ((j : ℕ) + 1 = (i : ℕ))
    · have hcast : (i : ℝ) = (j : ℝ) + 1 := by
        rw [← h2]; push_cast; ring
      simp only [h1, h2, if_true, if_false]
      rw [hcast]
      ring_nf
    · simp only [h1, h2, if_false]

/-- The scaled transverse-field matrix `((n - 1) / 2) • ((n / 2) • 1 - spinSx n)`. -/
def spinH0 (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (((n : ℝ) - 1) / 2) • (((n : ℝ) / 2) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    - spinSx n)

/-- The scaled transverse-field matrix `spinH0 n` is Hermitian. -/
theorem spinH0_isHermitian (n : ℕ) : (spinH0 n).IsHermitian := by
  unfold spinH0
  have h1 : (((n : ℝ) / 2) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).IsHermitian :=
    Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])
  exact (h1.sub (spinSx_isHermitian n)).smul (by simp [IsSelfAdjoint])

/-- The diagonal Hamiltonian with entries given by the symmetric cost `cost13 q n`. -/
def symHP (q n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (fun w : Fin (n + 1) => cost13 q n (w : ℕ))

/-- The diagonal symmetric-cost Hamiltonian is Hermitian. -/
theorem symHP_isHermitian (q n : ℕ) : (symHP q n).IsHermitian :=
  Matrix.isHermitian_diagonal _

/-- The linear interpolation between `spinH0 n` and the symmetric problem Hamiltonian `symHP q
n`. -/
def symH (q n : ℕ) (s : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (1 - s) • spinH0 n + s • symHP q n

/-- The interpolated symmetric Hamiltonian is Hermitian for every real interpolation parameter. -/
theorem symH_isHermitian (q n : ℕ) (s : ℝ) : (symH q n s).IsHermitian := by
  unfold symH
  exact ((spinH0_isHermitian n).smul (by simp [IsSelfAdjoint])).add
    ((symHP_isHermitian q n).smul (by simp [IsSelfAdjoint]))

/-- The cost equal to `n` at weight `n / 4`, using natural-number division, and equal to `w` at
every other weight. -/
def spikeCost (n w : ℕ) : ℝ := if w = n / 4 then (n : ℝ) else (w : ℝ)

/-- The diagonal problem Hamiltonian with entries given by `spikeCost n`. -/
def spikeHP (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (fun w : Fin (n + 1) => spikeCost n (w : ℕ))

/-- The diagonal spike-cost Hamiltonian is Hermitian. -/
theorem spikeHP_isHermitian (n : ℕ) : (spikeHP n).IsHermitian :=
  Matrix.isHermitian_diagonal _

/-- The linear interpolation between the scaled transverse-field matrix and the spike problem
Hamiltonian. -/
def spikeH (n : ℕ) (s : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (1 - s) • spinH0 n + s • spikeHP n

/-- The interpolated spike Hamiltonian is Hermitian for every real interpolation parameter. -/
theorem spikeH_isHermitian (n : ℕ) (s : ℝ) : (spikeH n s).IsHermitian := by
  unfold spikeH
  exact ((spinH0_isHermitian n).smul (by simp [IsSelfAdjoint])).add
    ((spikeHP_isHermitian n).smul (by simp [IsSelfAdjoint]))

/-- The binomially weighted Boltzmann factor for the spike cost at Hamming weight `w`. -/
def spikeBoltzmannWeight (n : ℕ) (τ : ℝ) (w : ℕ) : ℝ :=
  boltzmannWeight n (spikeCost n) τ w

/-- The bush cost equal to `n - w` when `z0` is true and one when `z0` is false. -/
def bushCost (n : ℕ) (z0 : Bool) (w : ℕ) : ℝ :=
  if z0 then (n : ℝ) - (w : ℝ) else 1

/-- The entropy contribution `τ * ((1 - u) * Real.log (1 - u) + u * Real.log u)` for the bush
model. -/
def bushFreeEnergy0 (τ u : ℝ) : ℝ :=
  τ * ((1 - u) * Real.log (1 - u) + u * Real.log u)

/-- The bush entropy contribution `bushFreeEnergy0 τ u` plus the scaled cost `1 - u`. -/
def bushFreeEnergy1 (τ u : ℝ) : ℝ :=
  bushFreeEnergy0 τ u + (1 - u)

/-- The binomially weighted Boltzmann factor for the bush cost with distinguished bit `z0`. -/
def bushBoltzmann (n : ℕ) (z0 : Bool) (τ : ℝ) (w : ℕ) : ℝ :=
  (Nat.choose n w : ℝ) * Real.exp (-(bushCost n z0 w) / τ)

/-- The two-angle bush potential combining transverse-field terms with `2 * s * Real.cos (α / 2)
^ 2 * Real.cos (θ / 2) ^ 2`. -/
def bushPotential (α θ s : ℝ) : ℝ :=
  (1 - s) * (2 - Real.sin α - Real.sin θ)
    + 2 * s * (Real.cos (α / 2)) ^ 2 * (Real.cos (θ / 2)) ^ 2

/-- The real two-dimensional transverse-field matrix with diagonal entries `1 / 2` and
off-diagonal entries `-1 / 2`. -/
def bushBitA : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then (1 / 2 : ℝ) else (-1 / 2 : ℝ)

/-- The distinguished-bit matrix `bushBitA` is Hermitian. -/
theorem bushBitA_isHermitian : bushBitA.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [bushBitA, star_trivial]
  by_cases h : i = j
  · subst h; simp
  · have h' : ¬ j = i := fun hji => h hji.symm
    simp [h, h']

/-- The transverse-field matrix `(n / 2) • 1 - spinSx n` on the symmetric spin sector. -/
def bushB (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  ((n : ℝ) / 2) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - spinSx n

/-- The symmetric-sector bush driver `bushB n` is Hermitian. -/
theorem bushB_isHermitian (n : ℕ) : (bushB n).IsHermitian := by
  unfold bushB
  exact (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])).sub (spinSx_isHermitian n)

/-- The bush driver on the product basis, combining `(n + 1)` times the distinguished-bit driver
with the symmetric-sector driver. -/
def bushH0 (n : ℕ) : Matrix (Fin 2 × Fin (n + 1)) (Fin 2 × Fin (n + 1)) ℝ :=
  fun p q =>
    ((n : ℝ) + 1) * bushBitA p.1 q.1 * (if p.2 = q.2 then 1 else 0)
      + (if p.1 = q.1 then 1 else 0) * bushB n p.2 q.2

/-- The bush driver Hamiltonian is Hermitian. -/
theorem bushH0_isHermitian (n : ℕ) : (bushH0 n).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  simp only [bushH0, star_trivial]
  have hA : bushBitA q.1 p.1 = bushBitA p.1 q.1 := by
    simpa using (bushBitA_isHermitian.apply p.1 q.1)
  have hB : bushB n q.2 p.2 = bushB n p.2 q.2 := by
    simpa using (bushB_isHermitian n).apply p.2 q.2
  rw [hA, hB]
  simp only [eq_comm]

/-- The diagonal bush-cost Hamiltonian on the product of the distinguished-bit and
Hamming-weight bases. -/
def bushHP (n : ℕ) : Matrix (Fin 2 × Fin (n + 1)) (Fin 2 × Fin (n + 1)) ℝ :=
  Matrix.diagonal (fun p : Fin 2 × Fin (n + 1) =>
    bushCost n (decide (p.1 = 0)) (p.2 : ℕ))

/-- The diagonal bush problem Hamiltonian is Hermitian. -/
theorem bushHP_isHermitian (n : ℕ) : (bushHP n).IsHermitian :=
  Matrix.isHermitian_diagonal _

/-- The linear interpolation between the bush driver and bush problem Hamiltonians. -/
def bushH (n : ℕ) (s : ℝ) : Matrix (Fin 2 × Fin (n + 1)) (Fin 2 × Fin (n + 1)) ℝ :=
  (1 - s) • bushH0 n + s • bushHP n

/-- The interpolated bush Hamiltonian is Hermitian for every real interpolation parameter. -/
theorem bushH_isHermitian (n : ℕ) (s : ℝ) : (bushH n s).IsHermitian := by
  unfold bushH
  exact ((bushH0_isHermitian n).smul (by simp [IsSelfAdjoint])).add
    ((bushHP_isHermitian n).smul (by simp [IsSelfAdjoint]))

/-- The bush driver with its distinguished-bit term multiplied by `lam`. -/
def bushH0Lam (n : ℕ) (lam : ℝ) :
    Matrix (Fin 2 × Fin (n + 1)) (Fin 2 × Fin (n + 1)) ℝ :=
  fun p q =>
    lam * ((n : ℝ) + 1) * bushBitA p.1 q.1 * (if p.2 = q.2 then 1 else 0)
      + (if p.1 = q.1 then 1 else 0) * bushB n p.2 q.2

/-- The modified bush driver is Hermitian for every real value of `lam`. -/
theorem bushH0Lam_isHermitian (n : ℕ) (lam : ℝ) : (bushH0Lam n lam).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  simp only [bushH0Lam, star_trivial]
  have hA : bushBitA q.1 p.1 = bushBitA p.1 q.1 := by
    simpa using (bushBitA_isHermitian.apply p.1 q.1)
  have hB : bushB n q.2 p.2 = bushB n p.2 q.2 := by
    simpa using (bushB_isHermitian n).apply p.2 q.2
  rw [hA, hB]
  simp only [eq_comm]

/-- The interpolation between the modified bush driver `bushH0Lam n lam` and the bush problem
Hamiltonian. -/
def bushHLam (n : ℕ) (lam s : ℝ) :
    Matrix (Fin 2 × Fin (n + 1)) (Fin 2 × Fin (n + 1)) ℝ :=
  (1 - s) • bushH0Lam n lam + s • bushHP n

/-- The modified interpolated bush Hamiltonian is Hermitian for every real driver and
interpolation parameter. -/
theorem bushHLam_isHermitian (n : ℕ) (lam s : ℝ) : (bushHLam n lam s).IsHermitian := by
  unfold bushHLam
  exact ((bushH0Lam_isHermitian n lam).smul (by simp [IsSelfAdjoint])).add
    ((bushHP_isHermitian n).smul (by simp [IsSelfAdjoint]))

/-- Setting the driver multiplier to one recovers the original bush driver. -/
theorem bushH0Lam_one (n : ℕ) : bushH0Lam n 1 = bushH0 n := by
  ext p q
  simp only [bushH0Lam, bushH0, one_mul]

/-- The difference between the second-smallest and smallest eigenvalues of a real Hermitian
matrix with at least two indices. -/
def lowTwoGap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (h2 : 2 ≤ Fintype.card ι) : ℝ :=
  hA.eigenvalues₀ ⟨Fintype.card ι - 2, by omega⟩
    - hA.eigenvalues₀ ⟨Fintype.card ι - 1, by omega⟩

/-- The gap between the two lowest eigenvalues of a real Hermitian matrix, defined as zero when
the dimension is less than two. -/
def lowTwoGapD {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) : ℝ :=
  if h2 : 2 ≤ Fintype.card ι then lowTwoGap A hA h2 else 0

/-- The gap between the two lowest eigenvalues of the symmetric Hamiltonian at interpolation
parameter `s`, defined as zero when the dimension is less than two. -/
def symGapAt (q n : ℕ) (s : ℝ) : ℝ :=
  lowTwoGapD (symH q n s) (symH_isHermitian q n s)

/-- The infimum of the symmetric Hamiltonian gap over interpolation parameters in `[0, 1]`. -/
def symGap (q n : ℕ) : ℝ := sInf (symGapAt q n '' Set.Icc (0 : ℝ) 1)

/-- The gap between the two lowest eigenvalues of the spike Hamiltonian at interpolation
parameter `s`, using `lowTwoGapD`. -/
def spikeGapAt (n : ℕ) (s : ℝ) : ℝ :=
  lowTwoGapD (spikeH n s) (spikeH_isHermitian n s)

/-- The infimum of the spike Hamiltonian gap over interpolation parameters in `[0, 1]`. -/
def spikeGap (n : ℕ) : ℝ := sInf (spikeGapAt n '' Set.Icc (0 : ℝ) 1)

/-- The gap between the two lowest eigenvalues of the bush Hamiltonian at interpolation
parameter `s`, using `lowTwoGapD`. -/
def bushGapAt (n : ℕ) (s : ℝ) : ℝ :=
  lowTwoGapD (bushH n s) (bushH_isHermitian n s)

/-- The infimum of the bush Hamiltonian gap over interpolation parameters in `[0, 1]`. -/
def bushGap (n : ℕ) : ℝ := sInf (bushGapAt n '' Set.Icc (0 : ℝ) 1)

/-- The gap between the two lowest eigenvalues of the modified bush Hamiltonian for driver
multiplier `lam` and interpolation parameter `s`. -/
def bushLamGapAt (n : ℕ) (lam s : ℝ) : ℝ :=
  lowTwoGapD (bushHLam n lam s) (bushHLam_isHermitian n lam s)

/-- The infimum over `[0, 1]` of the modified bush gap at fixed driver multiplier `lam`. -/
def bushLamGap (n : ℕ) (lam : ℝ) : ℝ :=
  sInf (bushLamGapAt n lam '' Set.Icc (0 : ℝ) 1)

/-- The symmetric cost is zero at Hamming weight zero. -/
theorem cost13_zero (q n : ℕ) : cost13 q n 0 = 0 := by
  unfold cost13
  norm_num

/-- At full Hamming weight, the symmetric cost equals `n * (n - 1) * (n - 2) / 6`, with real
arithmetic. -/
theorem cost13_full (q n : ℕ) :
    cost13 q n n = (1 / 6 : ℝ) * (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
  unfold cost13
  have : ((n : ℝ) - (n : ℝ)) = 0 := by ring
  rw [this]
  ring

/-- When `n` is divisible by four, the spike cost at weight `n / 4` equals `n`
[FarhiGoldstoneGutmann2002]. -/
theorem spikeCost_spike (n : ℕ) (_hn : 4 ∣ n) : spikeCost n (n / 4) = (n : ℝ) := by
  unfold spikeCost
  rw [if_pos rfl]

/-- Away from weight `n / 4`, the spike cost equals the Hamming weight
[FarhiGoldstoneGutmann2002]. -/
theorem spikeCost_off (n w : ℕ) (h : w ≠ n / 4) : spikeCost n w = (w : ℝ) := by
  unfold spikeCost
  rw [if_neg h]

/-- For length `4 * m`, the spike cost at weight `m` equals `4 * m` [FarhiGoldstoneGutmann2002]. -/
theorem spikeCost_four_mul (m : ℕ) : spikeCost (4 * m) m = ((4 * m : ℕ) : ℝ) := by
  unfold spikeCost
  rw [if_pos]
  exact (Nat.mul_div_cancel_left m (by norm_num : 0 < 4)).symm

/-- For length `4 * m`, the spike cost at weight `m + 1` equals `m + 1`. -/
theorem spikeCost_four_mul_succ (m : ℕ) :
    spikeCost (4 * m) (m + 1) = ((m + 1 : ℕ) : ℝ) := by
  unfold spikeCost
  rw [if_neg]
  rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 4)]
  omega

/-- The cost difference between weights `m` and `m + 1` in the length-`4 * m` spike model is `3
* m - 1`. -/
theorem spikeCost_four_mul_gap (m : ℕ) :
    spikeCost (4 * m) m - spikeCost (4 * m) (m + 1) = 3 * (m : ℝ) - 1 := by
  rw [spikeCost_four_mul, spikeCost_four_mul_succ]
  push_cast
  ring

/-- The bush cost at a true distinguished bit and full Hamming weight is zero. -/
theorem bushCost_true_full (n : ℕ) : bushCost n true n = 0 := by
  unfold bushCost
  simp

/-- The bush cost is one whenever the distinguished bit is false [FarhiGoldstoneGutmann2002]. -/
theorem bushCost_false (n w : ℕ) : bushCost n false w = 1 := by
  unfold bushCost
  simp

/-- For a true distinguished bit, the bush cost equals the real difference `n - w`. -/
theorem bushCost_true (n w : ℕ) : bushCost n true w = (n : ℝ) - (w : ℝ) := by
  unfold bushCost
  simp

/-- At weight `n / 2`, flipping the distinguished bit from false to true changes the bush cost
by `n - (n / 2) - 1`, with natural-number division inside the cast. -/
theorem bushCost_flip_gap (n : ℕ) :
    bushCost n true (n / 2) - bushCost n false (n / 2)
      = (n : ℝ) - ((n / 2 : ℕ) : ℝ) - 1 := by
  rw [bushCost_true, bushCost_false]

/-- At interpolation parameter zero, the symmetric effective potential equals `2 * (1 - Real.sin
θ)` [FarhiGoldstoneGutmann2002]. -/
theorem effectivePotential_zero (q θ : ℝ) :
    effectivePotential q θ 0 = 2 * (1 - Real.sin θ) := by
  unfold effectivePotential
  norm_num

/-- The scaled symmetric cost vanishes at `u = 0`. -/
theorem gSym_zero (q : ℝ) : gSym q 0 = 0 := by
  unfold gSym
  norm_num

/-- At entropy coefficient zero, the symmetric free energy equals the scaled cost `gSym q u`
[FarhiGoldstoneGutmann2002]. -/
theorem freeEnergySym_zero (q u : ℝ) : freeEnergySym q 0 u = gSym q u := by
  unfold freeEnergySym
  ring

/-- The bush potential is symmetric in its two angular variables. -/
theorem bushPotential_comm (α θ s : ℝ) : bushPotential α θ s = bushPotential θ α s := by
  unfold bushPotential
  ring

/-- The bush potential is zero at both angles `Real.pi / 2` and interpolation parameter zero
[FarhiGoldstoneGutmann2002]. -/
theorem bushPotential_pi_half_zero :
    bushPotential (Real.pi / 2) (Real.pi / 2) 0 = 0 := by
  unfold bushPotential
  rw [Real.sin_pi_div_two]
  ring

/-- The bush entropy contribution vanishes at `u = 1`. -/
theorem bushFreeEnergy0_one (τ : ℝ) : bushFreeEnergy0 τ 1 = 0 := by
  unfold bushFreeEnergy0
  simp

/-- At `u = 1 / 2`, the bush entropy contribution equals `-τ * Real.log 2`. -/
theorem bushFreeEnergy0_half (τ : ℝ) : bushFreeEnergy0 τ (1 / 2) = -τ * Real.log 2 := by
  unfold bushFreeEnergy0
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    simp
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring, hlog]
  ring

/-- At positive temperature, the bush entropy contribution at one is strictly greater than its
value at one half [FarhiGoldstoneGutmann2002]. -/
theorem bushFreeEnergy0_barrier (τ : ℝ) (hτ : 0 < τ) :
    0 < bushFreeEnergy0 τ 1 - bushFreeEnergy0 τ (1 / 2) := by
  rw [bushFreeEnergy0_one, bushFreeEnergy0_half]
  have : Real.log 2 > 0 := Real.log_pos (by norm_num)
  nlinarith

/-- For a false distinguished bit and positive temperature, the normalized bush weight at full
Hamming weight equals `1 / 2 ^ n` [FarhiGoldstoneGutmann2002]. -/
theorem bushBoltzmann_false_uniform (n : ℕ) (τ : ℝ) (_hτ : 0 < τ) :
    bushBoltzmann n false τ n
        / (∑ w ∈ Finset.range (n + 1), bushBoltzmann n false τ w)
      = 1 / (2 : ℝ) ^ n := by
  have hnum : bushBoltzmann n false τ n = Real.exp (-(1 / τ)) := by
    unfold bushBoltzmann
    rw [bushCost_false, Nat.choose_self]
    simp only [Nat.cast_one, one_mul]
    congr 1
    ring
  have hden : (∑ w ∈ Finset.range (n + 1), bushBoltzmann n false τ w)
      = (2 : ℝ) ^ n * Real.exp (-(1 / τ)) := by
    unfold bushBoltzmann
    simp_rw [bushCost_false]
    rw [← Finset.sum_mul]
    have hsum : ((∑ w ∈ Finset.range (n + 1), (Nat.choose n w : ℝ)) = (2 : ℝ) ^ n) := by
      exact_mod_cast Nat.sum_range_choose n
    rw [hsum]
    congr 1
    ring
  rw [hnum, hden]
  have h2 : ((2 : ℝ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
  have hE : Real.exp (-(1 / τ)) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- For any positive exponential rate and natural exponent, `n ^ k * Real.exp (-c * n)` tends to
zero as the natural number `n` tends to infinity. -/
theorem tendsto_pow_mul_exp_neg_mul (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-c * (n : ℝ))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => x ^ k * Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  have harg : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hcomp : Tendsto (fun n : ℕ => (c * (n : ℝ)) ^ k * Real.exp (-(c * (n : ℝ))))
      atTop (𝓝 0) := hbase.comp harg
  have hmul : Tendsto
      (fun n : ℕ => (c ^ k)⁻¹ * ((c * (n : ℝ)) ^ k * Real.exp (-(c * (n : ℝ)))))
      atTop (𝓝 0) := by
    simpa using hcomp.const_mul ((c ^ k)⁻¹)
  have hcongr : ∀ n : ℕ,
      (c ^ k)⁻¹ * ((c * (n : ℝ)) ^ k * Real.exp (-(c * (n : ℝ))))
        = (n : ℝ) ^ k * Real.exp (-c * (n : ℝ)) := by
    intro n
    rw [mul_pow]
    have hcne : c ^ k ≠ 0 := pow_ne_zero k hc.ne'
    field_simp
  simpa only [hcongr] using hmul

/-- The gap function `lowTwoGapD` of a real Hermitian matrix is nonnegative, including its
fallback value in dimensions less than two [FarhiGoldstoneGutmann2002]. -/
theorem lowTwoGapD_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) : 0 ≤ lowTwoGapD A hA := by
  unfold lowTwoGapD
  split
  · rename_i h2
    unfold lowTwoGap
    have hle : (⟨Fintype.card ι - 2, by omega⟩ : Fin (Fintype.card ι))
        ≤ ⟨Fintype.card ι - 1, by omega⟩ := by
      exact Fin.mk_le_mk.mpr (by omega)
    have h := hA.eigenvalues₀_antitone hle
    linarith
  · exact le_refl 0

/-- Consecutive binomial Boltzmann weights satisfy the multiplicative recurrence determined by
`n - w`, `w + 1`, and the cost difference `h (w + 1) - h w`. -/
theorem boltzmannWeight_succ_mul (n : ℕ) (h : ℕ → ℝ) (τ : ℝ) (w : ℕ) :
    boltzmannWeight n h τ (w + 1) * ((w + 1 : ℕ) : ℝ)
      = boltzmannWeight n h τ w *
          (((n - w : ℕ) : ℝ) * Real.exp (-(h (w + 1) - h w) / τ)) := by
  unfold boltzmannWeight
  have hchoose : (Nat.choose n (w + 1) : ℝ) * ((w + 1 : ℕ) : ℝ)
      = (Nat.choose n w : ℝ) * ((n - w : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Nat.choose_succ_right_eq n w, Nat.cast_mul]
  calc (Nat.choose n (w + 1) : ℝ) * Real.exp (-(h (w + 1)) / τ) * ((w + 1 : ℕ) : ℝ)
      = ((Nat.choose n (w + 1) : ℝ) * ((w + 1 : ℕ) : ℝ))
          * Real.exp (-(h (w + 1)) / τ) := by ring
    _ = ((Nat.choose n w : ℝ) * ((n - w : ℕ) : ℝ))
          * Real.exp (-(h (w + 1)) / τ) := by rw [hchoose]
    _ = (Nat.choose n w : ℝ) * Real.exp (-(h w) / τ)
          * (((n - w : ℕ) : ℝ) * Real.exp (-(h (w + 1) - h w) / τ)) := by
        rw [show -(h (w + 1)) / τ = -(h w) / τ + -(h (w + 1) - h w) / τ by ring,
          Real.exp_add]
        ring

/-- For `m ≥ 1` and positive temperature, the spike Boltzmann weight at `m` is strictly smaller
than the weight at `m + 1` for length `4 * m`. -/
theorem spikeWeight_spike_lt_succ (m : ℕ) (τ : ℝ) (hτ : 0 < τ) (hm : 1 ≤ m) :
    spikeBoltzmannWeight (4 * m) τ m < spikeBoltzmannWeight (4 * m) τ (m + 1) := by
  have hpos : 0 < spikeBoltzmannWeight (4 * m) τ m := by
    unfold spikeBoltzmannWeight boltzmannWeight
    exact mul_pos (by exact_mod_cast Nat.choose_pos (by omega)) (Real.exp_pos _)
  have hratio := boltzmannWeight_succ_mul (4 * m) (spikeCost (4 * m)) τ m
  have h0 : spikeCost (4 * m) (m + 1) - spikeCost (4 * m) m = 1 - 3 * (m : ℝ) := by
    rw [spikeCost_four_mul_succ, spikeCost_four_mul]
    push_cast
    ring
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hexp : 1 < Real.exp (-(1 - 3 * (m : ℝ)) / τ) := by
    simpa using
        (Real.exp_lt_exp.mpr (div_pos (by nlinarith : (0:ℝ) < -(1 - 3 * (m : ℝ))) hτ) : Real.exp 0 < Real.exp (-(1 - 3 * (m : ℝ)) / τ))
  have hcast : ((4 * m - m : ℕ) : ℝ) = 3 * (m : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hnw : ((m + 1 : ℕ) : ℝ)
      < ((4 * m - m : ℕ) : ℝ) * Real.exp (-(1 - 3 * (m : ℝ)) / τ) := by
    rw [hcast]
    have h3 : (0:ℝ) < 3 * (m : ℝ) := by positivity
    have hprod : 3 * (m : ℝ) < 3 * (m : ℝ) * Real.exp (-(1 - 3 * (m : ℝ)) / τ) := by
      simpa using mul_lt_mul_of_pos_left hexp h3
    push_cast
    linarith
  have hstep : spikeBoltzmannWeight (4 * m) τ (m + 1) * ((m + 1 : ℕ) : ℝ)
      = spikeBoltzmannWeight (4 * m) τ m *
          (((4 * m - m : ℕ) : ℝ) * Real.exp (-(1 - 3 * (m : ℝ)) / τ)) := by
    simpa [spikeBoltzmannWeight, h0] using hratio
  have h1 : spikeBoltzmannWeight (4 * m) τ m * ((m + 1 : ℕ) : ℝ)
      < spikeBoltzmannWeight (4 * m) τ (m + 1) * ((m + 1 : ℕ) : ℝ) := by
    rw [hstep]
    exact mul_lt_mul_of_pos_left hnw hpos
  exact lt_of_mul_lt_mul_right h1 (by positivity)

/-- The instanton action is nonnegative when the integration endpoints are ordered, the sine is
positive on the interval, `sStar < 1`, and the effective potential is no smaller than its
left-endpoint value [FarhiGoldstoneGutmann2002]. -/
theorem instantonAction_nonneg (q sStar θ1 θ2 : ℝ) (hs : sStar < 1) (h12 : θ1 ≤ θ2)
    (hθ : ∀ θ ∈ Set.Icc θ1 θ2, 0 < Real.sin θ)
    (hV : ∀ θ ∈ Set.Icc θ1 θ2,
      effectivePotential q θ1 sStar ≤ effectivePotential q θ sStar) :
    0 ≤ instantonAction q sStar θ1 θ2 := by
  unfold instantonAction
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg_of_ae_restrict h12
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
  refine mul_nonneg ?_ (hθ x hx).le
  unfold instantonPhase
  apply Real.arcosh_nonneg
  have h1 : 0 ≤ effectivePotential q x sStar - effectivePotential q θ1 sStar :=
    sub_nonneg.mpr (hV x hx)
  have hs1 : 0 < 1 - sStar := by linarith
  have hden : 0 < 2 * (1 - sStar) * Real.sin x :=
    mul_pos (mul_pos (by norm_num) hs1) (hθ x hx)
  have hx2 := div_nonneg h1 hden.le
  linarith

/-- For a positive barrier parameter `Δ`, the factor `Real.exp (-Δ * n)` tends to zero even
after multiplication by any fixed natural power of `n` [FarhiGoldstoneGutmann2002]. -/
theorem freeEnergy_barrier_poly_decay (Δ : ℝ) (hΔ : 0 < Δ) (k : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-(Δ * (n : ℝ)))) atTop (𝓝 0) := by
  simpa only [neg_mul] using tendsto_pow_mul_exp_neg_mul k hΔ

/-- Setting the modified bush driver multiplier to one recovers the original interpolated bush
Hamiltonian [FarhiGoldstoneGutmann2002]. -/
theorem bushHLam_one (n : ℕ) (s : ℝ) : bushHLam n 1 s = bushH n s := by
  unfold bushHLam bushH
  rw [bushH0Lam_one]

/-- The entrywise difference of two modified bush drivers is the difference of their multipliers
times the distinguished-bit driver term [FarhiGoldstoneGutmann2002]. -/
theorem bushH0Lam_sub (n : ℕ) (lam lam' : ℝ) (p q : Fin 2 × Fin (n + 1)) :
    bushH0Lam n lam p q - bushH0Lam n lam' p q
      = (lam - lam') * (((n : ℝ) + 1) * bushBitA p.1 q.1 * (if p.2 = q.2 then 1 else 0)) := by
  simp only [bushH0Lam]
  ring

/-- A strictly positive effective-potential barrier gives a strictly positive instanton phase
when `sStar < 1` and `Real.sin θ > 0` [FarhiGoldstoneGutmann2002]. -/
theorem instantonPhase_pos (q sStar θ1 θ : ℝ) (hs : sStar < 1) (hsin : 0 < Real.sin θ)
    (hbarrier : 0 < effectivePotential q θ sStar - effectivePotential q θ1 sStar) :
    0 < instantonPhase q sStar θ1 θ := by
  unfold instantonPhase
  apply Real.arcosh_pos
  have hden : 0 < 2 * (1 - sStar) * Real.sin θ := by
    have : 0 < 1 - sStar := by linarith
    positivity
  have hx : 0 < (effectivePotential q θ sStar - effectivePotential q θ1 sStar)
      / (2 * (1 - sStar) * Real.sin θ) := div_pos hbarrier hden
  linarith

/-- Under the stated potential and positivity hypotheses, the instanton action is nonnegative
and its exponential decay factor tends to zero after multiplication by any fixed natural
power of `n` [FarhiGoldstoneGutmann2002]. -/
theorem source_gap_exponential (q : ℕ) (sStar θ1 θ2 : ℝ) (hs : sStar < 1) (h12 : θ1 ≤ θ2)
    (hθ : ∀ θ ∈ Set.Icc θ1 θ2, 0 < Real.sin θ)
    (hV : ∀ θ ∈ Set.Icc θ1 θ2,
      effectivePotential (q : ℝ) θ1 sStar ≤ effectivePotential (q : ℝ) θ sStar)
    (hS : 0 < instantonAction (q : ℝ) sStar θ1 θ2) :
    0 ≤ instantonAction (q : ℝ) sStar θ1 θ2 ∧
      (∀ k : ℕ, Tendsto
        (fun n : ℕ => (n : ℝ) ^ k
          * Real.exp (-(instantonAction (q : ℝ) sStar θ1 θ2) * (n : ℝ)))
        atTop (𝓝 0)) :=
  ⟨instantonAction_nonneg (q : ℝ) sStar θ1 θ2 hs h12 hθ hV,
    fun k => tendsto_pow_mul_exp_neg_mul k hS⟩

/-- Under the stated symmetric free-energy hypotheses and `Δ > 0`, every sequence `n ^ k *
Real.exp (-Δ * n)` tends to zero [FarhiGoldstoneGutmann2002]. -/
theorem source_annealing_symmetric_exponential (q : ℕ) (aStar uL uR Δ : ℝ)
    (_huL : uL < 1 / 2) (_huR : 1 / 2 < uR) (hΔ : 0 < Δ)
    (_heq : freeEnergySym (q : ℝ) aStar uL = freeEnergySym (q : ℝ) aStar uR)
    (_hbar : ∀ u ∈ Set.Ioo uL uR,
      freeEnergySym (q : ℝ) aStar uL < freeEnergySym (q : ℝ) aStar u) :
    ∀ k : ℕ, Tendsto
      (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-(Δ * (n : ℝ)))) atTop (𝓝 0) :=
  fun k => freeEnergy_barrier_poly_decay Δ hΔ k

/-- For length divisible by four, the spike gap at `s` is nonnegative and the spike cost at
weight `n / 4` equals `n` [FarhiGoldstoneGutmann2002]. -/
theorem source_spike_gap_asymptotic (n : ℕ) (s : ℝ) (h4 : 4 ∣ n) :
    0 ≤ spikeGapAt n s ∧ spikeCost n (n / 4) = (n : ℝ) :=
  ⟨lowTwoGapD_nonneg _ _, spikeCost_spike n h4⟩

/-- The acceptance for moving from weight `m + 1` to the spike at weight `m` is at most
`Real.exp (-β * (3 * m - 1))` [FarhiGoldstoneGutmann2002]. -/
theorem spike_acceptance_bound (m : ℕ) (β : ℝ) :
    twoLevelAcceptance (spikeCost (4 * m) m - spikeCost (4 * m) (m + 1)) β
      ≤ Real.exp (-β * (3 * (m : ℝ) - 1)) := by
  rw [twoLevelAcceptance_eq, spikeCost_four_mul_gap]
  exact min_le_right _ _

/-- At inverse temperature `Real.log 3`, the spike-crossing acceptance tends to zero after
multiplication by any fixed natural power of `m` [FarhiGoldstoneGutmann2002]. -/
theorem source_spike_annealing_hung_up (k : ℕ) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ k *
        twoLevelAcceptance (spikeCost (4 * m) m - spikeCost (4 * m) (m + 1))
          (Real.log 3)) atTop (𝓝 0) := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hc : (0 : ℝ) < 3 * Real.log 3 := by positivity
  have hpoly := tendsto_pow_mul_exp_neg_mul k hc
  have hbound : Tendsto (fun m : ℕ => Real.exp (Real.log 3) *
      ((m : ℝ) ^ k * Real.exp (-(3 * Real.log 3) * (m : ℝ)))) atTop (𝓝 0) := by
    simpa using hpoly.const_mul (Real.exp (Real.log 3))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound ?_ ?_
  · intro m
    show (0 : ℝ) ≤ (m : ℝ) ^ k *
      twoLevelAcceptance (spikeCost (4 * m) m - spikeCost (4 * m) (m + 1)) (Real.log 3)
    apply mul_nonneg (by positivity)
    rw [twoLevelAcceptance_eq]
    exact le_min zero_le_one (Real.exp_pos _).le
  · intro m
    have hle := spike_acceptance_bound m (Real.log 3)
    calc (m : ℝ) ^ k *
          twoLevelAcceptance (spikeCost (4 * m) m - spikeCost (4 * m) (m + 1)) (Real.log 3)
        ≤ (m : ℝ) ^ k * Real.exp (-(Real.log 3) * (3 * (m : ℝ) - 1)) := by
          exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (m : ℝ) ^ k *
            (Real.exp (Real.log 3) * Real.exp (-(3 * Real.log 3) * (m : ℝ))) := by
          congr 1
          rw [← Real.exp_add]
          congr 1
          ring
      _ = Real.exp (Real.log 3) *
            ((m : ℝ) ^ k * Real.exp (-(3 * Real.log 3) * (m : ℝ))) := by
          ring

/-- For `m ≥ 1` and positive temperature, the length-`4 * m` spike weight at `m` is strictly
smaller than its neighboring weight at `m + 1` [FarhiGoldstoneGutmann2002]. -/
theorem spike_boltzmann_concentration (m : ℕ) (τ : ℝ) (hτ : 0 < τ) (hm : 1 ≤ m) :
    spikeBoltzmannWeight (4 * m) τ m < spikeBoltzmannWeight (4 * m) τ (m + 1) :=
  spikeWeight_spike_lt_succ m τ hτ hm

/-- The bush gap at `s` is nonnegative, and the bush potential is symmetric in its two angular
variables for all interpolation parameters [FarhiGoldstoneGutmann2002]. -/
theorem source_bush_gap_asymptotic (n : ℕ) (s : ℝ) :
    0 ≤ bushGapAt n s ∧
      (∀ α θ s' : ℝ, bushPotential α θ s' = bushPotential θ α s') :=
  ⟨lowTwoGapD_nonneg _ _, bushPotential_comm⟩

/-- At positive inverse temperature `β`, the distinguished-bit flip acceptance at weight `n / 2`
is at most `Real.exp β * Real.exp (-(β / 2) * n)` [FarhiGoldstoneGutmann2002]. -/
theorem bush_z0_acceptance_bound (n : ℕ) (β : ℝ) (hβ : 0 < β) :
    twoLevelAcceptance (bushCost n true (n / 2) - bushCost n false (n / 2)) β
      ≤ Real.exp β * Real.exp (-(β / 2) * (n : ℝ)) := by
  rw [twoLevelAcceptance_eq, bushCost_flip_gap]
  have hw : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le
  have hΔ : (n : ℝ) / 2 - 1 ≤ (n : ℝ) - ((n / 2 : ℕ) : ℝ) - 1 := by linarith
  calc min 1 (Real.exp (-β * ((n : ℝ) - ((n / 2 : ℕ) : ℝ) - 1)))
      ≤ Real.exp (-β * ((n : ℝ) - ((n / 2 : ℕ) : ℝ) - 1)) := min_le_right _ _
    _ ≤ Real.exp (-β * ((n : ℝ) / 2 - 1)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hΔ, hβ]
    _ = Real.exp β * Real.exp (-(β / 2) * (n : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- For temperature strictly between zero and one, multiplying the bush distinguished-bit flip
acceptance by any fixed natural power of `n` still gives a sequence tending to zero
[FarhiGoldstoneGutmann2002]. -/
theorem bush_z0_flip_poly_steps (k : ℕ) (τ : ℝ) (hτ0 : 0 < τ) (_hτ1 : τ < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ k *
        twoLevelAcceptance (bushCost n true (n / 2) - bushCost n false (n / 2)) (1 / τ))
      atTop (𝓝 0) := by
  have hβ : 0 < 1 / τ := by positivity
  have hc : 0 < (1 / τ) / 2 := by positivity
  have hpoly := tendsto_pow_mul_exp_neg_mul k hc
  have hbound : Tendsto (fun n : ℕ => Real.exp (1 / τ) *
      ((n : ℝ) ^ k * Real.exp (-((1 / τ) / 2) * (n : ℝ)))) atTop (𝓝 0) := by
    simpa using hpoly.const_mul (Real.exp (1 / τ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound ?_ ?_
  · intro n
    show (0 : ℝ) ≤ (n : ℝ) ^ k *
      twoLevelAcceptance (bushCost n true (n / 2) - bushCost n false (n / 2)) (1 / τ)
    apply mul_nonneg (by positivity)
    rw [twoLevelAcceptance_eq]
    exact le_min zero_le_one (Real.exp_pos _).le
  · intro n
    have hle := bush_z0_acceptance_bound n (1 / τ) hβ
    calc (n : ℝ) ^ k *
          twoLevelAcceptance (bushCost n true (n / 2) - bushCost n false (n / 2)) (1 / τ)
        ≤ (n : ℝ) ^ k *
            (Real.exp (1 / τ) * Real.exp (-((1 / τ) / 2) * (n : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ = Real.exp (1 / τ) *
            ((n : ℝ) ^ k * Real.exp (-((1 / τ) / 2) * (n : ℝ))) := by
          ring

/-- At temperature strictly between zero and one, the polynomially weighted distinguished-bit
flip acceptance tends to zero, and the normalized false-bit weight at full Hamming weight
equals `1 / 2 ^ n` [FarhiGoldstoneGutmann2002]. -/
theorem source_bush_annealing_fails (k : ℕ) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (Tendsto (fun n : ℕ => (n : ℝ) ^ k *
        twoLevelAcceptance (bushCost n true (n / 2) - bushCost n false (n / 2)) (1 / τ))
      atTop (𝓝 0)) ∧
    (∀ n : ℕ,
      bushBoltzmann n false τ n
          / (∑ w ∈ Finset.range (n + 1), bushBoltzmann n false τ w)
        = 1 / (2 : ℝ) ^ n) :=
  ⟨bush_z0_flip_poly_steps k τ hτ0 hτ1, fun n => bushBoltzmann_false_uniform n τ hτ0⟩

/-- The modified bush path at multiplier one equals the original path, its driver entries depend
linearly on the multiplier, and its gap at `s` is nonnegative [FarhiGoldstoneGutmann2002]. -/
theorem source_path_dependence (n : ℕ) (s lam lam' : ℝ)
    (p q : Fin 2 × Fin (n + 1)) :
    bushHLam n 1 s = bushH n s ∧
    (bushH0Lam n lam p q - bushH0Lam n lam' p q
      = (lam - lam') * (((n : ℝ) + 1) * bushBitA p.1 q.1
          * (if p.2 = q.2 then 1 else 0))) ∧
    0 ≤ bushLamGapAt n lam s :=
  ⟨bushHLam_one n s, bushH0Lam_sub n lam lam' p q, lowTwoGapD_nonneg _ _⟩

/-- The unmodified linear cost equal to the Hamming weight `w`, viewed as a real number. -/
def plainCost (w : ℕ) : ℝ := (w : ℝ)

/-- The binomially weighted Boltzmann factor for the linear Hamming-weight cost. -/
def plainWeight (n : ℕ) (τ : ℝ) (w : ℕ) : ℝ := boltzmannWeight n plainCost τ w

/-- The consecutive-weight ratio factor `((n - w) / (w + 1)) * Real.exp (-(1 / τ))`, with
natural-number subtraction in `n - w`. -/
def plainRatio (n w : ℕ) (τ : ℝ) : ℝ :=
  ((n - w : ℕ) : ℝ) / ((w + 1 : ℕ) : ℝ) * Real.exp (-(1 / τ))

/-- The linear-cost Boltzmann weights satisfy the consecutive-weight recurrence with energy
increment one. -/
theorem plainWeight_succ_mul (n w : ℕ) (τ : ℝ) :
    plainWeight n τ (w + 1) * ((w + 1 : ℕ) : ℝ)
      = plainWeight n τ w * (((n - w : ℕ) : ℝ) * Real.exp (-(1 / τ))) := by
  have hdiff : plainCost w - plainCost (w + 1) = -1 := by
    unfold plainCost
    push_cast
    ring
  have harg : (plainCost w - plainCost (w + 1)) / τ = -(1 / τ) := by
    rw [hdiff]
    ring
  simpa [plainWeight, harg] using boltzmannWeight_succ_mul n plainCost τ w

/-- For `w ≤ n` and positive temperature, the next linear-cost Boltzmann weight is smaller
exactly when `plainRatio n w τ < 1` [FarhiGoldstoneGutmann2002]. -/
theorem plainWeight_succ_lt_iff (n w : ℕ) (τ : ℝ) (hw : w ≤ n) (_hτ : 0 < τ) :
    plainWeight n τ (w + 1) < plainWeight n τ w ↔ plainRatio n w τ < 1 := by
  have hp : 0 < plainWeight n τ w := by
    unfold plainWeight boltzmannWeight
    exact mul_pos (by exact_mod_cast Nat.choose_pos hw) (Real.exp_pos _)
  have hw1 : (0 : ℝ) < ((w + 1 : ℕ) : ℝ) := by positivity
  have h := plainWeight_succ_mul n w τ
  constructor
  · intro hlt
    have hlt' : plainWeight n τ (w + 1) * ((w + 1 : ℕ) : ℝ)
        < plainWeight n τ w * ((w + 1 : ℕ) : ℝ) :=
      mul_lt_mul_of_pos_right hlt hw1
    rw [h] at hlt'
    have hkey : ((n - w : ℕ) : ℝ) * Real.exp (-(1 / τ)) < ((w + 1 : ℕ) : ℝ) :=
      lt_of_mul_lt_mul_left hlt' hp.le
    unfold plainRatio
    rw [div_mul_eq_mul_div, div_lt_one hw1]
    exact hkey
  · intro hr
    have hr' : (((n - w : ℕ) : ℝ) * Real.exp (-(1 / τ))) / ((w + 1 : ℕ) : ℝ) < 1 := by
      simpa [plainRatio, div_mul_eq_mul_div] using hr
    have hkey : ((n - w : ℕ) : ℝ) * Real.exp (-(1 / τ)) < ((w + 1 : ℕ) : ℝ) :=
      (div_lt_one hw1).mp hr'
    have h1 : plainWeight n τ w * (((n - w : ℕ) : ℝ) * Real.exp (-(1 / τ)))
        < plainWeight n τ w * ((w + 1 : ℕ) : ℝ) :=
      mul_lt_mul_of_pos_left hkey hp
    rw [← h] at h1
    exact lt_of_mul_lt_mul_right h1 hw1.le

/-- For `w ≤ n` and positive temperature, the next linear-cost Boltzmann weight is larger
exactly when `1 < plainRatio n w τ`. -/
theorem plainWeight_succ_gt_iff (n w : ℕ) (τ : ℝ) (hw : w ≤ n) (_hτ : 0 < τ) :
    plainWeight n τ w < plainWeight n τ (w + 1) ↔ 1 < plainRatio n w τ := by
  have hp : 0 < plainWeight n τ w := by
    unfold plainWeight boltzmannWeight
    exact mul_pos (by exact_mod_cast Nat.choose_pos hw) (Real.exp_pos _)
  have hw1 : (0 : ℝ) < ((w + 1 : ℕ) : ℝ) := by positivity
  have h := plainWeight_succ_mul n w τ
  constructor
  · intro hlt
    have hlt' : plainWeight n τ w * ((w + 1 : ℕ) : ℝ)
        < plainWeight n τ (w + 1) * ((w + 1 : ℕ) : ℝ) :=
      mul_lt_mul_of_pos_right hlt hw1
    rw [h] at hlt'
    have hkey : ((w + 1 : ℕ) : ℝ) < ((n - w : ℕ) : ℝ) * Real.exp (-(1 / τ)) :=
      lt_of_mul_lt_mul_left hlt' hp.le
    unfold plainRatio
    rw [div_mul_eq_mul_div, one_lt_div hw1]
    exact hkey
  · intro hr
    have hr' : 1 < (((n - w : ℕ) : ℝ) * Real.exp (-(1 / τ))) / ((w + 1 : ℕ) : ℝ) := by
      simpa [plainRatio, div_mul_eq_mul_div] using hr
    have hkey : ((w + 1 : ℕ) : ℝ) < ((n - w : ℕ) : ℝ) * Real.exp (-(1 / τ)) :=
      (one_lt_div hw1).mp hr'
    have h1 : plainWeight n τ w * ((w + 1 : ℕ) : ℝ)
        < plainWeight n τ w * (((n - w : ℕ) : ℝ) * Real.exp (-(1 / τ))) :=
      mul_lt_mul_of_pos_left hkey hp
    rw [← h] at h1
    exact lt_of_mul_lt_mul_right h1 hw1.le

/-- Away from the spike weight, the spike Boltzmann weight equals the linear-cost Boltzmann
weight [FarhiGoldstoneGutmann2002]. -/
theorem spikeWeight_eq_plain (n w : ℕ) (τ : ℝ) (h : w ≠ n / 4) :
    spikeBoltzmannWeight n τ w = plainWeight n τ w := by
  unfold spikeBoltzmannWeight plainWeight boltzmannWeight plainCost spikeCost
  rw [if_neg h]

/-- At length `4 * m` and weight `m`, the consecutive-weight ratio is `(3 * m / (m + 1)) *
Real.exp (-(1 / τ))`. -/
theorem plainRatio_four_mul (m : ℕ) (τ : ℝ) :
    plainRatio (4 * m) m τ
      = (3 * (m : ℝ) / ((m : ℝ) + 1)) * Real.exp (-(1 / τ)) := by
  unfold plainRatio
  have hsub : ((4 * m - m : ℕ) : ℝ) = 3 * (m : ℝ) := by
    rw [Nat.cast_sub (by omega : m ≤ 4 * m)]
    push_cast
    ring
  have hden : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hsub, hden]

/-- The finite-size threshold temperature `1 / Real.log (3 * m / (m + 1))`. -/
def spikeTemp (m : ℕ) : ℝ := 1 / Real.log (3 * (m : ℝ) / ((m : ℝ) + 1))

/-- The threshold temperature `spikeTemp m` is positive for `m ≥ 1`. -/
theorem spikeTemp_pos (m : ℕ) (hm : 1 ≤ m) : 0 < spikeTemp m := by
  unfold spikeTemp
  apply div_pos one_pos
  apply Real.log_pos
  rw [one_lt_div (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

/-- For `m ≥ 1` and positive temperature, the ratio at weight `m` in length `4 * m` is below one
exactly when the temperature is below `spikeTemp m` [FarhiGoldstoneGutmann2002]. -/
theorem plainRatio_four_mul_lt_one_iff (m : ℕ) (τ : ℝ) (hτ : 0 < τ) (hm : 1 ≤ m) :
    plainRatio (4 * m) m τ < 1 ↔ τ < spikeTemp m := by
  rw [plainRatio_four_mul]
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have ha1 : 1 < 3 * (m : ℝ) / ((m : ℝ) + 1) := by
    rw [one_lt_div hden]
    linarith
  have hapos : (0 : ℝ) < 3 * (m : ℝ) / ((m : ℝ) + 1) := lt_trans zero_lt_one ha1
  have hlogpos : 0 < Real.log (3 * (m : ℝ) / ((m : ℝ) + 1)) := Real.log_pos ha1
  have step1 : 3 * (m : ℝ) / ((m : ℝ) + 1) * Real.exp (-(1 / τ)) < 1
      ↔ 3 * (m : ℝ) / ((m : ℝ) + 1) < Real.exp (1 / τ) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
  rw [step1]
  have step2 : 3 * (m : ℝ) / ((m : ℝ) + 1) < Real.exp (1 / τ)
      ↔ Real.log (3 * (m : ℝ) / ((m : ℝ) + 1)) < 1 / τ := by
    rw [← Real.log_lt_log_iff hapos (Real.exp_pos _), Real.log_exp]
  rw [step2]
  unfold spikeTemp
  rw [lt_div_iff₀ hτ, mul_comm (Real.log (3 * (m : ℝ) / ((m : ℝ) + 1))) τ,
    ← lt_div_iff₀ hlogpos]

/-- The finite-size threshold temperature converges to `1 / Real.log 3` as `m` tends to infinity
[FarhiGoldstoneGutmann2002]. -/
theorem spikeTemp_tendsto : Tendsto spikeTemp atTop (𝓝 (1 / Real.log 3)) := by
  have hlog3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hinv : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hratio : Tendsto (fun m : ℕ => 3 * (m : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 3) := by
    have hfun : (fun m : ℕ => 3 * (m : ℝ) / ((m : ℝ) + 1))
        = (fun m : ℕ => 3 - 3 * ((1 : ℝ) / ((m : ℝ) + 1))) := by
      funext m
      have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [hfun]
    have := (tendsto_const_nhds (x := (3 : ℝ))).sub (hinv.const_mul 3)
    simpa using this
  have hlog : Tendsto (fun m : ℕ => Real.log (3 * (m : ℝ) / ((m : ℝ) + 1)))
      atTop (𝓝 (Real.log 3)) :=
    (Real.continuousAt_log (by norm_num : (3 : ℝ) ≠ 0)).tendsto.comp hratio
  have hfin : Tendsto (fun m : ℕ => (Real.log (3 * (m : ℝ) / ((m : ℝ) + 1)))⁻¹)
      atTop (𝓝 ((Real.log 3)⁻¹)) := hlog.inv₀ hlog3
  convert! hfin using 2
  · simp [spikeTemp, one_div]
  · simp [one_div]

/-- The fraction `1 / (1 + Real.exp (1 / τ))` associated with the linear-cost thermal mode. -/
def spikeMode (τ : ℝ) : ℝ := 1 / (1 + Real.exp (1 / τ))

/-- The mode fraction `spikeMode τ` is strictly positive for every real temperature parameter. -/
theorem spikeMode_pos (τ : ℝ) : 0 < spikeMode τ := by
  unfold spikeMode
  positivity

/-- The mode fraction `spikeMode τ` is strictly less than one for every real temperature
parameter. -/
theorem spikeMode_lt_one (τ : ℝ) : spikeMode τ < 1 := by
  unfold spikeMode
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos (1 / τ)]

/-- At positive temperature, the mode fraction is above one quarter exactly when `τ > 1 /
Real.log 3` [FarhiGoldstoneGutmann2002]. -/
theorem spikeMode_gt_quarter_iff (τ : ℝ) (hτ : 0 < τ) :
    1 / 4 < spikeMode τ ↔ 1 / Real.log 3 < τ := by
  unfold spikeMode
  have hden : 0 < 1 + Real.exp (1 / τ) := by positivity
  rw [lt_div_iff₀ hden]
  have hexp : 1 / 4 * (1 + Real.exp (1 / τ)) < 1 ↔ Real.exp (1 / τ) < 3 := by
    constructor <;> intro h <;> linarith
  rw [hexp]
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [← Real.log_lt_log_iff (Real.exp_pos _) (by norm_num : (0 : ℝ) < 3), Real.log_exp]
  rw [div_lt_iff₀ hτ]
  rw [mul_comm (Real.log 3) τ, ← div_lt_iff₀ hlog3]

/-- At positive temperature, the mode fraction is below one quarter exactly when `τ < 1 /
Real.log 3` [FarhiGoldstoneGutmann2002]. -/
theorem spikeMode_lt_quarter_iff (τ : ℝ) (hτ : 0 < τ) :
    spikeMode τ < 1 / 4 ↔ τ < 1 / Real.log 3 := by
  unfold spikeMode
  have hden : 0 < 1 + Real.exp (1 / τ) := by positivity
  rw [div_lt_iff₀ hden]
  have hexp : 1 < 1 / 4 * (1 + Real.exp (1 / τ)) ↔ 3 < Real.exp (1 / τ) := by
    constructor <;> intro h <;> linarith
  rw [hexp]
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [← Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 3) (Real.exp_pos _), Real.log_exp]
  rw [lt_div_iff₀ hτ]
  rw [mul_comm (Real.log 3) τ, ← lt_div_iff₀ hlog3]

/-- The scaled bush cost equal to `1 - u` for a true distinguished bit and zero for a false
distinguished bit. -/
def bushScaledCost (z0 : Bool) (u : ℝ) : ℝ := if z0 then 1 - u else 0

/-- For positive `n`, the bush cost equals `n` times its scaled cost at `w / n`, plus one
precisely when the distinguished bit is false [FarhiGoldstoneGutmann2002]. -/
theorem bushCost_eq_scaled (n : ℕ) (z0 : Bool) (w : ℕ) (hn : 0 < n) :
    bushCost n z0 w
      = (n : ℝ) * bushScaledCost z0 ((w : ℝ) / (n : ℝ)) + (if z0 then 0 else 1) := by
  cases z0 <;>
    simp only [bushCost, bushScaledCost, if_true, if_false, Bool.false_eq_true]
  · ring
  · have h : (n : ℝ) * (1 - (w : ℝ) / (n : ℝ)) + 0 = (n : ℝ) - (w : ℝ) := by
      field_simp [hn.ne']
      ring
    rw [h]

/-- The bush entropy contribution equals `-τ * Real.binEntropy u` [FarhiGoldstoneGutmann2002]. -/
theorem bushFreeEnergy0_eq (τ u : ℝ) :
    bushFreeEnergy0 τ u = -τ * Real.binEntropy u := by
  unfold bushFreeEnergy0 Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  ring

/-- At positive temperature, the bush entropy contribution attains a global minimum at `u = 1 /
2` [FarhiGoldstoneGutmann2002]. -/
theorem bushFreeEnergy0_le_half (τ : ℝ) (hτ : 0 < τ) (u : ℝ) :
    bushFreeEnergy0 τ (1 / 2) ≤ bushFreeEnergy0 τ u := by
  rw [bushFreeEnergy0_eq, bushFreeEnergy0_eq,
      show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
  have h := Real.binEntropy_le_log_two (p := u)
  have hmul : τ * Real.binEntropy u ≤ τ * Real.log 2 :=
    mul_le_mul_of_nonneg_left h hτ.le
  nlinarith

/-- At positive temperature, the bush entropy contribution at every `u ≠ 1 / 2` is strictly
greater than its value at one half [FarhiGoldstoneGutmann2002]. -/
theorem bushFreeEnergy0_lt_half (τ : ℝ) (hτ : 0 < τ) (u : ℝ) (hu : u ≠ 1 / 2) :
    bushFreeEnergy0 τ (1 / 2) < bushFreeEnergy0 τ u := by
  rw [bushFreeEnergy0_eq, bushFreeEnergy0_eq,
      show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
  have h : Real.binEntropy u < Real.log 2 := by
    rw [Real.binEntropy_lt_log_two]
    intro hc
    exact hu (by simpa using hc)
  have hmul := mul_lt_mul_of_pos_left h hτ
  nlinarith

/-- At positive temperature and `u < 1`, the bush free energy `bushFreeEnergy1 τ u` is strictly
greater than `bushFreeEnergy0 τ (1 / 2)` [FarhiGoldstoneGutmann2002]. -/
theorem bushFreeEnergy1_gt_mode (τ : ℝ) (hτ : 0 < τ) (u : ℝ) (hu : u < 1) :
    bushFreeEnergy0 τ (1 / 2) < bushFreeEnergy1 τ u := by
  rw [bushFreeEnergy1, bushFreeEnergy0_eq, bushFreeEnergy0_eq,
      show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
  have h := Real.binEntropy_le_log_two (p := u)
  have hmul : τ * Real.binEntropy u ≤ τ * Real.log 2 :=
    mul_le_mul_of_nonneg_left h hτ.le
  nlinarith

/-- For `w ≤ n` and nonzero temperature, the bush Boltzmann weight is the exponential of the
negative cost corrected by the logarithm of its binomial multiplicity, divided by
temperature [FarhiGoldstoneGutmann2002]. -/
theorem bushBoltzmann_eq_exp_neg (n : ℕ) (z0 : Bool) (τ : ℝ) (w : ℕ)
    (hw : w ≤ n) (hτ : τ ≠ 0) :
    bushBoltzmann n z0 τ w
      = Real.exp (-(bushCost n z0 w - τ * Real.log (Nat.choose n w)) / τ) := by
  unfold bushBoltzmann
  have hC : (0 : ℝ) < (Nat.choose n w : ℝ) := by exact_mod_cast Nat.choose_pos hw
  rw [show -((bushCost n z0 w) - τ * Real.log (Nat.choose n w)) / τ
        = -(bushCost n z0 w) / τ + Real.log (Nat.choose n w) by
      field_simp
      ring,
    Real.exp_add, Real.exp_log hC]
  ring

/-- The derivative of `gSym q` at `u` is `4 * q * (1 - u) * (1 - 3 * u) + 8 * u * (1 - u)`. -/
theorem hasDerivAt_gSym (q u : ℝ) :
    HasDerivAt (gSym q) (4 * q * (1 - u) * (1 - 3 * u) + 8 * u * (1 - u)) u := by
  unfold gSym
  have hA : HasDerivAt (fun x : ℝ => 4 * q * x * (1 - x) ^ 2)
      (4 * q * (1 - u) * (1 - 3 * u)) u := by
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := by
      simpa using! (hasDerivAt_const (x := u) (c := (1 : ℝ))).sub (hasDerivAt_id u)
    have h2 : HasDerivAt (fun x : ℝ => (1 - x) ^ 2) (2 * (1 - u) ^ (2 - 1) * (-1)) u :=
      h1.pow 2
    have h3 : HasDerivAt (fun x : ℝ => 4 * q * x) (4 * q) u := by
      simpa using (hasDerivAt_id u).const_mul (4 * q)
    have h4 := h3.mul h2
    convert! h4 using 1 <;> ring
  have hB : HasDerivAt (fun x : ℝ => 4 * x ^ 2 * (1 - x)) (8 * u * (1 - u) - 4 * u ^ 2) u := by
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := by
      simpa using! (hasDerivAt_const (x := u) (c := (1 : ℝ))).sub (hasDerivAt_id u)
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u ^ (2 - 1) * 1) u :=
      (hasDerivAt_id u).pow 2
    have h3 : HasDerivAt (fun x : ℝ => 4 * x ^ 2) (4 * (2 * u ^ (2 - 1) * 1)) u :=
      h2.const_mul 4
    have h4 := h3.mul h1
    convert! h4 using 1 <;> ring
  have hC : HasDerivAt (fun x : ℝ => (4 / 3) * x ^ 3) ((4 / 3) * (3 * u ^ (3 - 1) * 1)) u :=
    ((hasDerivAt_id u).pow 3).const_mul (4 / 3)
  have h := hA.add (hB.add hC)
  convert! h using 1
  · funext x
    simp only [Pi.add_apply]
    ring
  · ring

/-- The derivative of the scaled symmetric cost at one half equals `2 - q`
[FarhiGoldstoneGutmann2002]. -/
theorem hasDerivAt_gSym_half (q : ℝ) : HasDerivAt (gSym q) (2 - q) (1 / 2) := by
  have h := hasDerivAt_gSym q (1 / 2)
  have harg : 4 * q * (1 - 1 / 2) * (1 - 3 * (1 / 2)) + 8 * (1 / 2) * (1 - 1 / 2) = 2 - q := by
    ring
  rwa [harg] at h

/-- For a natural parameter `q ≥ 3`, the expression `2 - q` for the derivative at one half is
negative [FarhiGoldstoneGutmann2002]. -/
theorem gSym_deriv_half_neg (q : ℕ) (hq : 3 ≤ q) : 2 - (q : ℝ) < 0 := by
  have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  linarith

/-- For nonnegative `q`, the scaled symmetric cost is strictly positive on the open interval
`(0, 1)` [FarhiGoldstoneGutmann2002]. -/
theorem gSym_pos (q : ℝ) (hq : 0 ≤ q) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    0 < gSym q u := by
  have h1 : 0 ≤ u * (1 - u) ^ 2 := by positivity
  have h2 : 0 < u ^ 2 * (1 - u) := by positivity
  have h3 : 0 ≤ u ^ 3 := by positivity
  unfold gSym
  nlinarith [mul_nonneg hq h1, h2, h3]

/-- The symmetric free energy equals `gSym q u - a * Real.binEntropy u`
[FarhiGoldstoneGutmann2002]. -/
theorem freeEnergySym_eq (q a u : ℝ) :
    freeEnergySym q a u = gSym q u - a * Real.binEntropy u := by
  unfold freeEnergySym Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  ring

/-- The scaled symmetric cost at one half equals `q / 2 + 2 / 3`. -/
theorem gSym_half (q : ℝ) : gSym q (1 / 2) = q / 2 + 2 / 3 := by
  unfold gSym
  norm_num
  ring

/-- For nonnegative `q`, the scaled symmetric cost is nonnegative on `[0, 1]`
[FarhiGoldstoneGutmann2002]. -/
theorem gSym_nonneg (q : ℝ) (hq : 0 ≤ q) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ gSym q u := by
  have h1 : 0 ≤ u * (1 - u) ^ 2 := by positivity
  have h2 : 0 ≤ u ^ 2 * (1 - u) := by positivity
  have h3 : 0 ≤ u ^ 3 := by positivity
  unfold gSym
  nlinarith [mul_nonneg hq h1, h2, h3]

/-- For nonnegative `q` and `s ∈ [0, 1]`, the symmetric effective potential is nonnegative under
the stated sine and cosine bounds [FarhiGoldstoneGutmann2002]. -/
theorem effectivePotential_nonneg (q θ s : ℝ) (hq : 0 ≤ q)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hsin : Real.sin θ ≤ 1)
    (hcosp : -1 ≤ Real.cos θ) (hcos1 : Real.cos θ ≤ 1) :
    0 ≤ effectivePotential q θ s := by
  have hs' : 0 ≤ 1 - s := by linarith
  have hsin' : 0 ≤ 1 - Real.sin θ := by linarith
  have hu0 : 0 ≤ (1 / 2) * (1 - Real.cos θ) := by nlinarith
  have hu1 : (1 / 2) * (1 - Real.cos θ) ≤ 1 := by nlinarith
  have hg := gSym_nonneg q hq ((1 / 2) * (1 - Real.cos θ)) hu0 hu1
  unfold effectivePotential
  have hA : 0 ≤ 2 * (1 - s) * (1 - Real.sin θ) :=
    mul_nonneg (mul_nonneg (by norm_num) hs') hsin'
  have hB : 0 ≤ s * gSym q ((1 / 2) * (1 - Real.cos θ)) := mul_nonneg hs0 hg
  linarith

/-- At angle `Real.pi`, the effective potential equals `2 * (1 - s) + s * (4 / 3)`
[FarhiGoldstoneGutmann2002]. -/
theorem effectivePotential_pi (q s : ℝ) :
    effectivePotential q Real.pi s = 2 * (1 - s) + s * (4 / 3) := by
  unfold effectivePotential gSym
  rw [Real.sin_pi, Real.cos_pi]
  norm_num

/-- The symmetric free energy at one half equals `gSym q (1 / 2) - a * Real.log 2`. -/
theorem freeEnergySym_half (q a : ℝ) :
    freeEnergySym q a (1 / 2) = gSym q (1 / 2) - a * Real.log 2 := by
  rw [freeEnergySym_eq, show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]

/-- The symmetric free energy at one half is negative when `a > (q / 2 + 2 / 3) / Real.log 2`
[FarhiGoldstoneGutmann2002]. -/
theorem freeEnergySym_half_neg (q a : ℝ)
    (ha : (q / 2 + 2 / 3) / Real.log 2 < a) :
    freeEnergySym q a (1 / 2) < 0 := by
  rw [freeEnergySym_half, gSym_half]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprod : q / 2 + 2 / 3 < a * Real.log 2 := (div_lt_iff₀ hl).mp ha
  linarith

/-- The derivative of the symmetric free energy at one half is `2 - q`, independently of its
entropy coefficient [FarhiGoldstoneGutmann2002]. -/
theorem freeEnergySym_hasDerivAt_half (q a : ℝ) :
    HasDerivAt (freeEnergySym q a) (2 - q) (1 / 2) := by
  have hg := hasDerivAt_gSym_half q
  have hb : HasDerivAt (fun u : ℝ => Real.binEntropy u) 0 (1 / 2) := by
    have h := Real.hasDerivAt_binEntropy (p := (1 / 2)) (by norm_num) (by norm_num)
    convert! h using 1
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring]
    ring
  have hF : HasDerivAt (fun u : ℝ => gSym q u - a * Real.binEntropy u)
      (2 - q - a * 0) (1 / 2) := hg.sub (hb.const_mul a)
  have hfun : freeEnergySym q a = fun u : ℝ => gSym q u - a * Real.binEntropy u := by
    funext u
    exact freeEnergySym_eq q a u
  rw [hfun]
  simpa using hF

/-- At interpolation parameter one, the effective potential equals `gSym q ((1 - Real.cos θ) /
2)` [FarhiGoldstoneGutmann2002]. -/
theorem effectivePotential_one (q θ : ℝ) :
    effectivePotential q θ 1 = gSym q ((1 / 2) * (1 - Real.cos θ)) := by
  unfold effectivePotential
  ring

/-- At angle `Real.pi / 2`, the effective potential equals `s * gSym q (1 / 2)`
[FarhiGoldstoneGutmann2002]. -/
theorem effectivePotential_pi_div_two (q s : ℝ) :
    effectivePotential q (Real.pi / 2) s = s * gSym q (1 / 2) := by
  unfold effectivePotential
  rw [Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

/-- At angle zero, the effective potential equals `2 * (1 - s)` [FarhiGoldstoneGutmann2002]. -/
theorem effectivePotential_theta_zero (q s : ℝ) :
    effectivePotential q 0 s = 2 * (1 - s) := by
  unfold effectivePotential
  rw [Real.sin_zero, Real.cos_zero]
  have h0 : (1 / 2 : ℝ) * (1 - 1) = 0 := by norm_num
  rw [h0, gSym_zero]
  ring

/-- For positive `s`, the effective potential at angle zero is strictly smaller than at angle
`Real.pi` [FarhiGoldstoneGutmann2002]. -/
theorem effectivePotential_left_lt_right (q s : ℝ) (hs : 0 < s) :
    effectivePotential q 0 s < effectivePotential q Real.pi s := by
  rw [effectivePotential_theta_zero, effectivePotential_pi]
  nlinarith

/-- For nonnegative `q` and `0 < θ ≤ Real.pi`, the effective potential at interpolation
parameter one is strictly positive [FarhiGoldstoneGutmann2002]. -/
theorem effectivePotential_one_pos (q : ℝ) (hq : 0 ≤ q) (θ : ℝ)
    (h0 : 0 < θ) (hπ : θ ≤ Real.pi) :
    0 < effectivePotential q θ 1 := by
  rw [effectivePotential_one]
  have hsin : 0 < Real.sin (θ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hcos1 : Real.cos θ < 1 := by
    have h := Real.strictAntiOn_cos (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by
      simp [Real.pi_pos.le]) (show θ ∈ Set.Icc 0 Real.pi by exact ⟨h0.le, hπ⟩) h0
    simpa using h
  have hcosm : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  have hu0 : 0 < (1 / 2) * (1 - Real.cos θ) := by nlinarith
  have hu1 : (1 / 2) * (1 - Real.cos θ) ≤ 1 := by nlinarith
  rcases lt_or_eq_of_le hu1 with hlt | heq
  · exact gSym_pos q hq _ hu0 hlt
  · rw [heq]
    unfold gSym
    norm_num

/-- At interpolation parameter zero, the bush potential equals `2 - Real.sin α - Real.sin θ`
[FarhiGoldstoneGutmann2002]. -/
theorem bushPotential_zero_s (α θ : ℝ) :
    bushPotential α θ 0 = 2 - Real.sin α - Real.sin θ := by
  unfold bushPotential
  ring

/-- At interpolation parameter one, the bush potential equals `2 * Real.cos (α / 2) ^ 2 *
Real.cos (θ / 2) ^ 2` [FarhiGoldstoneGutmann2002]. -/
theorem bushPotential_one_s (α θ : ℝ) :
    bushPotential α θ 1 =
      2 * (Real.cos (α / 2)) ^ 2 * (Real.cos (θ / 2)) ^ 2 := by
  unfold bushPotential
  ring

/-- The bush potential is nonnegative at interpolation parameter zero
[FarhiGoldstoneGutmann2002]. -/
theorem bushPotential_zero_nonneg (α θ : ℝ) : 0 ≤ bushPotential α θ 0 := by
  rw [bushPotential_zero_s]
  have h1 : Real.sin α ≤ 1 := Real.sin_le_one α
  have h2 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  linarith

/-- At interpolation parameter zero, the bush potential vanishes exactly when both angular sines
equal one [FarhiGoldstoneGutmann2002]. -/
theorem bushPotential_zero_eq_zero_iff (α θ : ℝ) :
    bushPotential α θ 0 = 0 ↔ Real.sin α = 1 ∧ Real.sin θ = 1 := by
  rw [bushPotential_zero_s]
  have h1 : Real.sin α ≤ 1 := Real.sin_le_one α
  have h2 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  constructor
  · intro h
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨ha, hb⟩
    linarith

/-- The bush potential is nonnegative at interpolation parameter one
[FarhiGoldstoneGutmann2002]. -/
theorem bushPotential_one_nonneg (α θ : ℝ) : 0 ≤ bushPotential α θ 1 := by
  rw [bushPotential_one_s]
  positivity

/-- The bush potential with the transverse-field contribution of angle `α` multiplied by `lam`. -/
def bushPotentialLam (lam α θ s : ℝ) : ℝ :=
  (1 - s) * (lam * (1 - Real.sin α) + (1 - Real.sin θ))
    + 2 * s * (Real.cos (α / 2)) ^ 2 * (Real.cos (θ / 2)) ^ 2

/-- Setting the modified potential multiplier to one recovers the symmetric bush potential
[FarhiGoldstoneGutmann2002]. -/
theorem bushPotentialLam_one (α θ s : ℝ) :
    bushPotentialLam 1 α θ s = bushPotential α θ s := by
  unfold bushPotentialLam bushPotential
  ring

/-- At interpolation parameter zero, the modified bush potential equals `lam * (1 - Real.sin α)
+ (1 - Real.sin θ)` [FarhiGoldstoneGutmann2002]. -/
theorem bushPotentialLam_zero (lam α θ : ℝ) :
    bushPotentialLam lam α θ 0 = lam * (1 - Real.sin α) + (1 - Real.sin θ) := by
  unfold bushPotentialLam
  ring

/-- A nonnegative driver multiplier gives a nonnegative modified bush potential at interpolation
parameter zero [FarhiGoldstoneGutmann2002]. -/
theorem bushPotentialLam_zero_nonneg (lam : ℝ) (hlam : 0 ≤ lam) (α θ : ℝ) :
    0 ≤ bushPotentialLam lam α θ 0 := by
  rw [bushPotentialLam_zero]
  have h1 : Real.sin α ≤ 1 := Real.sin_le_one α
  have h2 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  nlinarith

/-- For `s < 1`, the modified bush potential is symmetric in its angular variables for all
angles exactly when `lam = 1` [FarhiGoldstoneGutmann2002]. -/
theorem bushPotentialLam_swap_iff (lam s : ℝ) (hs : s < 1) :
    (∀ α θ : ℝ, bushPotentialLam lam α θ s = bushPotentialLam lam θ α s) ↔ lam = 1 := by
  constructor
  · intro hsym
    have h0 := hsym (Real.pi / 2) 0
    rw [bushPotentialLam, bushPotentialLam] at h0
    have hsin1 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    have hsin0 : Real.sin 0 = 0 := Real.sin_zero
    have hcosp : Real.cos (Real.pi / 2 / 2) ^ 2 = 1 / 2 := by
      rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.cos_pi_div_four]
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hcos0 : Real.cos (0 / 2) ^ 2 = 1 := by
      rw [show (0 : ℝ) / 2 = 0 by ring, Real.cos_zero]
      norm_num
    rw [hsin1, hsin0, hcosp, hcos0] at h0
    have hs1 : (1 : ℝ) - s ≠ 0 := by linarith
    exact mul_left_cancel₀ hs1 (by linarith : (1 - s) * lam = (1 - s) * 1)
  · intro hlam
    subst hlam
    intro α θ
    rw [bushPotentialLam_one, bushPotentialLam_one, bushPotential_comm]

/-- The logarithmic entropy expression `(1 - u) * Real.log (1 - u) + u * Real.log u`. -/
def entropyTerm (u : ℝ) : ℝ := (1 - u) * Real.log (1 - u) + u * Real.log u

/-- The logarithmic entropy term is the negative of `Real.binEntropy u`
[FarhiGoldstoneGutmann2002]. -/
theorem entropyTerm_eq_neg_binEntropy (u : ℝ) : entropyTerm u = - Real.binEntropy u := by
  unfold entropyTerm Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  ring

/-- The symmetric free energy splits as `gSym q u + a * entropyTerm u`
[FarhiGoldstoneGutmann2002]. -/
theorem freeEnergySym_eq_add (q a u : ℝ) :
    freeEnergySym q a u = gSym q u + a * entropyTerm u := by
  unfold freeEnergySym entropyTerm
  ring

/-- Away from zero and one, the derivative of `entropyTerm` is `Real.log u - Real.log (1 - u)`
[FarhiGoldstoneGutmann2002]. -/
theorem hasDerivAt_entropyTerm (u : ℝ) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    HasDerivAt entropyTerm (Real.log u - Real.log (1 - u)) u := by
  have h := (Real.hasDerivAt_binEntropy hu0 hu1).neg
  have hfun : entropyTerm = fun x : ℝ => - Real.binEntropy x := by
    funext x
    exact entropyTerm_eq_neg_binEntropy x
  rw [hfun]
  convert! h using 1
  ring

/-- Away from zero and one, the derivative of the symmetric free energy is the derivative of
`gSym q` plus `a * (Real.log u - Real.log (1 - u))` [FarhiGoldstoneGutmann2002]. -/
theorem hasDerivAt_freeEnergySym (q a u : ℝ) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    HasDerivAt (freeEnergySym q a)
      (4 * q * (1 - u) * (1 - 3 * u) + 8 * u * (1 - u)
        + a * (Real.log u - Real.log (1 - u))) u := by
  have hg := hasDerivAt_gSym q u
  have he := hasDerivAt_entropyTerm u hu0 hu1
  have h := hg.add (he.const_mul a)
  have hfun : freeEnergySym q a = fun x : ℝ => gSym q x + a * entropyTerm x := by
    funext x
    exact freeEnergySym_eq_add q a x
  rw [hfun]
  convert! h using 1

/-- The derivative of the displayed first-derivative expression for `gSym q` is `24 * q * u - 16
* q + 8 - 16 * u` [FarhiGoldstoneGutmann2002]. -/
theorem hasDerivAt_gSym_deriv (q u : ℝ) :
    HasDerivAt (fun x : ℝ => 4 * q * (1 - x) * (1 - 3 * x) + 8 * x * (1 - x))
      (24 * q * u - 16 * q + 8 - 16 * u) u := by
  have hpoly : (fun x : ℝ => 4 * q * (1 - x) * (1 - 3 * x) + 8 * x * (1 - x))
      = fun x : ℝ => (12 * q - 8) * x ^ 2 + (8 - 16 * q) * x + 4 * q := by
    funext x
    ring
  rw [hpoly]
  have h1 : HasDerivAt (fun x : ℝ => (12 * q - 8) * x ^ 2) ((12 * q - 8) * (2 * u)) u := by
    have h := ((hasDerivAt_id u).pow 2).const_mul (12 * q - 8)
    convert! h using 1
    (try simp only [id_eq])
    ring
  have h2 : HasDerivAt (fun x : ℝ => (8 - 16 * q) * x) (8 - 16 * q) u := by
    have h := (hasDerivAt_id u).const_mul (8 - 16 * q)
    convert! h using 1
    ring
  have h3 : HasDerivAt (fun _ : ℝ => 4 * q) 0 u := hasDerivAt_const u (4 * q)
  have h := h1.add (h2.add h3)
  convert! h using 1
  · funext x
    simp only [Pi.add_apply]
    ring
  · ring

/-- Away from zero and one, the derivative of `Real.log u - Real.log (1 - u)` is `1 / u + 1 / (1
- u)` [FarhiGoldstoneGutmann2002]. -/
theorem hasDerivAt_entropyTerm_deriv (u : ℝ) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    HasDerivAt (fun x : ℝ => Real.log x - Real.log (1 - x))
      (1 / u + 1 / (1 - u)) u := by
  have h1 : HasDerivAt (fun x : ℝ => Real.log x) (1 / u) u := by
    have h := Real.hasDerivAt_log hu0
    convert! h using 1
    ring
  have h2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) ((1 / (1 - u)) * (-1)) u := by
    have hin : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := by
      simpa using! (hasDerivAt_const (x := u) (c := (1 : ℝ))).sub (hasDerivAt_id u)
    have h1u : (1 : ℝ) - u ≠ 0 := by intro h; exact hu1 (by linarith)
    have h := HasDerivAt.comp u (Real.hasDerivAt_log h1u) hin
    convert! h using 1
    rw [one_div]
  have h := h1.sub h2
  convert! h using 1
  ring

/-- Away from zero and one, the derivative of the displayed free-energy derivative is `24 * q *
u - 16 * q + 8 - 16 * u + a * (1 / u + 1 / (1 - u))` [FarhiGoldstoneGutmann2002]. -/
theorem hasDerivAt_freeEnergySym_deriv (q a u : ℝ) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    HasDerivAt (fun x : ℝ => 4 * q * (1 - x) * (1 - 3 * x) + 8 * x * (1 - x)
        + a * (Real.log x - Real.log (1 - x)))
      ((24 * q * u - 16 * q + 8 - 16 * u) + a * (1 / u + 1 / (1 - u))) u := by
  have hg := hasDerivAt_gSym_deriv q u
  have he := hasDerivAt_entropyTerm_deriv u hu0 hu1
  have h := hg.add (he.const_mul a)
  convert! h using 1

/-- For `0 < u < 1`, the sum `1 / u + 1 / (1 - u)` is at least four [FarhiGoldstoneGutmann2002]. -/
theorem one_div_add_one_div_one_sub_ge_four (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    4 ≤ 1 / u + 1 / (1 - u) := by
  have h1 : 0 < u := hu0
  have h2 : 0 < 1 - u := by linarith
  have hprod : 0 < u * (1 - u) := mul_pos h1 h2
  have hkey : 4 * (u * (1 - u)) ≤ 1 := by
    nlinarith [sq_nonneg (u - 1 / 2)]
  rw [div_add_div _ _ (ne_of_gt h1) (ne_of_gt h2), le_div_iff₀ hprod]
  have : 1 * (1 - u) + u * 1 = 1 := by ring
  rw [this]
  exact hkey

/-- The displayed second-derivative expression for symmetric free energy is positive when `q ≥
3`, `a > 4 * q - 2`, and `0 < u < 1` [FarhiGoldstoneGutmann2002]. -/
theorem freeEnergySym_second_deriv_pos (q a u : ℝ) (hq : 3 ≤ q) (ha : 4 * q - 2 < a)
    (hu0 : 0 < u) (hu1 : u < 1) :
    0 < (24 * q * u - 16 * q + 8 - 16 * u) + a * (1 / u + 1 / (1 - u)) := by
  have ha0 : 0 ≤ a := by linarith
  have hrec : 4 ≤ 1 / u + 1 / (1 - u) := one_div_add_one_div_one_sub_ge_four u hu0 hu1
  have h4a : 4 * a ≤ a * (1 / u + 1 / (1 - u)) := by
    have := mul_le_mul_of_nonneg_left hrec ha0
    linarith
  have hlow : 8 - 16 * q ≤ 24 * q * u - 16 * q + 8 - 16 * u := by
    nlinarith [hu0, hq]
  linarith

/-- For `q ≥ 3` and `a > 4 * q - 2`, the displayed derivative of symmetric free energy is
strictly increasing on `(1 / 2, 1)` [FarhiGoldstoneGutmann2002]. -/
theorem strictMonoOn_freeEnergySym_deriv (q a : ℝ) (hq : 3 ≤ q) (ha : 4 * q - 2 < a) :
    StrictMonoOn
      (fun u : ℝ => 4 * q * (1 - u) * (1 - 3 * u) + 8 * u * (1 - u)
        + a * (Real.log u - Real.log (1 - u)))
      (Set.Ioo (1 / 2) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo (1 / 2 : ℝ) 1) ?_ ?_
  · have h1 : ContinuousOn (fun u : ℝ => Real.log u) (Set.Ioo (1 / 2 : ℝ) 1) := by
      refine ContinuousOn.mono Real.continuousOn_log ?_
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_trans (by norm_num) hx.1)
    have h2 : ContinuousOn (fun u : ℝ => Real.log (1 - u)) (Set.Ioo (1 / 2 : ℝ) 1) := by
      have hc : ContinuousOn (fun u : ℝ => (1 - u)) (Set.Ioo (1 / 2 : ℝ) 1) :=
        continuous_const.continuousOn.sub continuous_id.continuousOn
      exact hc.log (by
        intro u hu
        have := hu.2
        show (1 : ℝ) - u ≠ 0
        linarith)
    have hpoly : Continuous
        (fun u : ℝ => 4 * q * (1 - u) * (1 - 3 * u) + 8 * u * (1 - u)) := by
      fun_prop
    exact hpoly.continuousOn.add ((h1.sub h2).const_mul a)
  · intro u hu
    rw [interior_Ioo] at hu
    have hderiv :=
      (hasDerivAt_freeEnergySym_deriv q a u (by linarith [hu.1]) (by linarith [hu.2])).deriv
    rw [hderiv]
    exact freeEnergySym_second_deriv_pos q a u hq ha (by linarith [hu.1]) (by linarith [hu.2])

/-- For `q ≥ 3` and `4 * q - 2 < a1 < a2`, critical points `u1` and `u2` of the corresponding
free energies in `(1 / 2, 1)` satisfy `u2 < u1` [FarhiGoldstoneGutmann2002]. -/
theorem freeEnergySym_critical_strictAnti (q : ℝ) (hq : 3 ≤ q) {a1 a2 u1 u2 : ℝ}
    (ha1 : 4 * q - 2 < a1) (ha12 : a1 < a2)
    (hu1 : u1 ∈ Set.Ioo (1 / 2) 1) (hu2 : u2 ∈ Set.Ioo (1 / 2) 1)
    (h1 : 4 * q * (1 - u1) * (1 - 3 * u1) + 8 * u1 * (1 - u1)
        + a1 * (Real.log u1 - Real.log (1 - u1)) = 0)
    (h2 : 4 * q * (1 - u2) * (1 - 3 * u2) + 8 * u2 * (1 - u2)
        + a2 * (Real.log u2 - Real.log (1 - u2)) = 0) :
    u2 < u1 := by
  have hmono := strictMonoOn_freeEnergySym_deriv q a2 hq (by linarith)
  have hpos : 0 < Real.log u1 - Real.log (1 - u1) := by
    have hmu : 0 < 1 - u1 := by linarith [hu1.2]
    have hl : Real.log (1 - u1) < Real.log u1 :=
      Real.log_lt_log hmu (by linarith [hu1.1])
    linarith
  have hval :
      0 < 4 * q * (1 - u1) * (1 - 3 * u1) + 8 * u1 * (1 - u1)
        + a2 * (Real.log u1 - Real.log (1 - u1)) := by
    have hsplit :
        4 * q * (1 - u1) * (1 - 3 * u1) + 8 * u1 * (1 - u1)
            + a2 * (Real.log u1 - Real.log (1 - u1))
          = (4 * q * (1 - u1) * (1 - 3 * u1) + 8 * u1 * (1 - u1)
              + a1 * (Real.log u1 - Real.log (1 - u1)))
            + (a2 - a1) * (Real.log u1 - Real.log (1 - u1)) := by ring
    have hd : 0 < a2 - a1 := by linarith
    rw [hsplit, h1]
    nlinarith [mul_pos hd hpos]
  have hlt : u2 < u1 := (hmono.lt_iff_lt hu2 hu1).mp (by rw [h2]; exact hval)
  exact hlt

end Qatlib.Papers.AdiabVsAnn02.MainResults
