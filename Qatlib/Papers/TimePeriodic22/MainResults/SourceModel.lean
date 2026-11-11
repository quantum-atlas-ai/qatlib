/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.CStarAlgebra.Matrix
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Source model for *Optimal Hamiltonian simulation for time-periodic systems*

Fixed source: K. Mizuta and K. Fujii, arXiv:2209.05048v3 (accepted in Quantum
2023-03-16).  PDF: `2209.05048.pdf`, extracted text: `2209.05048.txt`.
Section and equation numbers below refer to the v3 numbering.

This file fixes the objects shared by the claim statements of the paper block:

* the Fourier coefficients `Hm` of a time-periodic Hamiltonian with cutoff
  `mmax` (Eq. (15)) and the interaction-picture scale `γ` (Eq. (23));
* the truncation window `D_lmax` (Eq. (17)), the truncated effective Hamiltonian
  `Heff^{lmax}` (Eq. (18)) and the Floquet evolution `e^{-i Heff^{lmax} t}`
  used for the transition amplitudes (Eq. (19));
* the exact time-ordered propagator as a field of `TimePeriodicModel` (Eq. (7));
* the periodic-boundary-condition refined effective Hamiltonian of Eq. (101) and
  the two amplification unitaries of Eqs. (72), (102), (103);
* the resource ledger `SimulationResources` used by Theorems 1 and 2, and the
  truncation order of Eq. (59).

All matrices are finite `Matrix H H ℂ` over the physical register `H`; the
Fourier register is `Fin (2*lmax)` (window `D_lmax`) or `Fin (8*lmax)`
(window `D_{4lmax}`).  The exponential of a matrix is the ordinary power series
`∑ n, (n!)⁻¹ • A^n`; on the finite register it agrees with `NormedSpace.exp`
with respect to any chosen matrix norm.

Boundary: the exact propagator `exactEvolution` is *not* derived from an ODE
here (no differentiability of `H(t)` is assumed); it is a required field, so a
theorem about it is a statement about any time-ordered propagator, not a
construction.  No claim below is proved in this file.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TimePeriodic22.MainResults

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

variable {H : Type*} [Fintype H] [DecidableEq H]

/-! ## The Fourier window and its indices -/

/-- Fourier index `l` of the `j`-th slot of the window
`D_lmax = {-lmax+1, ..., lmax}` of Eq. (17). -/
def fourierIndex (lmax : ℕ) (j : Fin (2 * lmax)) : ℤ :=
  ((j : ℕ) : ℤ) - ((lmax : ℕ) : ℤ) + 1

/-- The slot of the window `D_lmax` carrying Fourier index `0`. -/
def zeroIndex (lmax : ℕ) (h : 1 ≤ lmax) : Fin (2 * lmax) :=
  ⟨lmax - 1, by omega⟩

/-- The designated slot `zeroIndex` carries Fourier index `0`. -/
lemma zeroIndex_spec (lmax : ℕ) (h : 1 ≤ lmax) : fourierIndex lmax (zeroIndex lmax h) = 0 := by
  simp only [fourierIndex, zeroIndex]
  omega

/-- Embedding `D_lmax ↪ D_{4lmax}` mapping a Fourier index to itself. -/
def embed4 (lmax : ℕ) (j : Fin (2 * lmax)) : Fin (2 * (4 * lmax)) :=
  ⟨j.val + 3 * lmax, by
    have := j.isLt
    omega⟩

/-- The embedding of `D_lmax` into `D_{4lmax}` preserves the Fourier index. -/
lemma fourierIndex_embed4 (lmax : ℕ) (j : Fin (2 * lmax)) :
    fourierIndex (4 * lmax) (embed4 lmax j) = fourierIndex lmax j := by
  simp only [fourierIndex, embed4]
  omega

/-- Representative in `D_{4lmax}` of the difference `d` modulo `8*lmax`
(the `l ⊖ l'` of Eq. (163)).  Its value lies in `[-4*lmax+1, 4*lmax]`, the
range of `fourierIndex (4*lmax) ·`. -/
def cyclicShiftRep (lmax : ℕ) (d : ℤ) : ℤ :=
  let r := d % (8 * (lmax : ℤ))
  if r ≤ 4 * (lmax : ℤ) then r else r - 8 * (lmax : ℤ)

/-- The difference `l ⊖ l'` of Eq. (163): the slot of `D_{4lmax}` whose Fourier
index is congruent to `d` modulo `8*lmax`. -/
def cyclicSub (lmax : ℕ) (hpos : 1 ≤ lmax) (d : ℤ) : Fin (2 * (4 * lmax)) :=
  ⟨Int.toNat ((d + 4 * (lmax : ℤ) - 1) % (8 * (lmax : ℤ))), by
    have h8 : (0 : ℤ) < 8 * (lmax : ℤ) := by
      have : (1 : ℤ) ≤ (lmax : ℤ) := by exact_mod_cast hpos
      nlinarith
    have hnn : 0 ≤ (d + 4 * (lmax : ℤ) - 1) % (8 * (lmax : ℤ)) :=
      Int.emod_nonneg _ (ne_of_gt h8)
    have hlt := Int.emod_lt_of_pos (d + 4 * (lmax : ℤ) - 1) h8
    rw [Int.toNat_lt hnn]
    have hcast : ((2 * (4 * lmax) : ℕ) : ℤ) = 8 * (lmax : ℤ) := by
      push_cast
      ring
    rw [hcast]
    exact hlt⟩

/-- The Fourier index of `l ⊖ l'` is congruent to `d` modulo `8*lmax`. -/
lemma fourierIndex_cyclicSub (lmax : ℕ) (hpos : 1 ≤ lmax) (d : ℤ) :
    fourierIndex (4 * lmax) (cyclicSub lmax hpos d)
      = (d + 4 * (lmax : ℤ) - 1) % (8 * (lmax : ℤ)) - 4 * (lmax : ℤ) + 1 := by
  have h8 : (0 : ℤ) < 8 * (lmax : ℤ) := by
    have : (1 : ℤ) ≤ (lmax : ℤ) := by exact_mod_cast hpos
    nlinarith
  have h1 : 0 ≤ (d + 4 * (lmax : ℤ) - 1) % (8 * (lmax : ℤ)) :=
    Int.emod_nonneg _ (ne_of_gt h8)
  simp only [fourierIndex, cyclicSub, Fin.val_mk, Int.toNat_of_nonneg h1]
  push_cast
  ring

/-! ## Periodicity data, Eq. (15) and the scale `γ` of Eq. (23) -/

/-- A time-periodic Hamiltonian with the cutoff of Eq. (15): the Fourier
component `Hm` vanishes for `|m| > mmax`. -/
structure PeriodicHamiltonian (H : Type*) [Fintype H] [DecidableEq H] where
  /-- Frequency `ω = 2π/T`. -/
  ω : ℝ
  /-- Cut-off `mmax` of Eq. (15). -/
  mmax : ℕ
  /-- Fourier coefficients `H_m`. -/
  Hm : ℤ → Matrix H H ℂ
  /-- Eq. (15): `H_m = 0` for `|m| > mmax`. -/
  cutoff : ∀ m : ℤ, ((mmax : ℕ) : ℤ) < |m| → Hm m = 0

/-- A time-periodic Hamiltonian whose Fourier components decay exponentially,
`‖H_m‖ ≤ h e^{-|m|/ζ}` (Appendix C). -/
structure DecayingHamiltonian (H : Type*) [Fintype H] [DecidableEq H] where
  /-- Frequency `ω = 2π/T`. -/
  ω : ℝ
  /-- Prefactor `h` of the decay bound. -/
  h : ℝ
  /-- Decay length `ζ`. -/
  ζ : ℝ
  /-- Fourier coefficients. -/
  Hm : ℤ → Matrix H H ℂ
  /-- Positivity of `h`. -/
  hh : 0 < h
  /-- Positivity of `ζ`. -/
  hζ : 0 < ζ
  /-- Decay bound `‖H_m‖ ≤ h e^{-|m|/ζ}`. -/
  decay : ∀ m : ℤ, ‖Hm m‖ ≤ h * Real.exp (-((m.natAbs : ℝ) / ζ))

/-- The Hamiltonian value `H(t) = H_0 + ∑_{m≠0} e^{i m ω t} H_m` of periodic data. -/
def periodicHamiltonianAt (P : PeriodicHamiltonian H) (t : ℝ) : Matrix H H ℂ :=
  P.Hm 0 + ∑ m ∈ Finset.Icc (-((P.mmax : ℕ) : ℤ)) ((P.mmax : ℕ) : ℤ),
    (Complex.exp (Complex.I * (m : ℂ) * (P.ω : ℂ) * (t : ℂ))) • P.Hm m

/-- The interaction-picture scale `γ = sup_t ‖H(t) - H_0‖` of Eq. (23). -/
def periodicGamma (P : PeriodicHamiltonian H) : ℝ :=
  sSup {x : ℝ | ∃ t : ℝ, x = ‖periodicHamiltonianAt P t - P.Hm 0‖}

/-- Exact time-ordered propagator data.  `exactEvolution t` is the operator
`U(t)` of Eq. (7) at time `t`; no equation of motion is imposed in the model. -/
structure TimePeriodicModel (H : Type*) [Fintype H] [DecidableEq H] where
  /-- Underlying periodic Hamiltonian. -/
  ham : PeriodicHamiltonian H
  /-- The exact time-ordered propagator `U(t)`. -/
  exactEvolution : ℝ → Matrix H H ℂ

/-! ## The truncated effective Hamiltonian, Eqs. (17)-(19) -/

/-- Block `⟨l| Heff^{lmax} |l'⟩` of Eq. (18): `H_0 - lω` on the diagonal and
`H_{l-l'}` off the diagonal. -/
def effBlock (ω : ℝ) (Hm : ℤ → Matrix H H ℂ) (l l' : ℤ) : Matrix H H ℂ :=
  if l = l' then Hm 0 - (((l : ℝ) * ω : ℝ) : ℂ) • (1 : Matrix H H ℂ) else Hm (l - l')

/-- The truncated effective Hamiltonian `Heff^{lmax}` of Eq. (18), as a matrix on
`D_lmax ⊗ H`. -/
def floquetHamiltonian (ω : ℝ) (Hm : ℤ → Matrix H H ℂ) (lmax : ℕ) :
    Matrix (Fin (2 * lmax) × H) (Fin (2 * lmax) × H) ℂ :=
  fun p q => effBlock ω Hm (fourierIndex lmax p.1) (fourierIndex lmax q.1) p.2 q.2

/-- The matrix exponential as the power series `∑ n, (n!)⁻¹ • A^n`. -/
def matrixExponential {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑' n : ℕ, ((n.factorial : ℂ)⁻¹) • A ^ n

/-- The evolution `e^{-i Heff^{lmax} t}` of the truncated Hamiltonian. -/
def evolutionOf (ω : ℝ) (Hm : ℤ → Matrix H H ℂ) (lmax : ℕ) (t : ℝ) :
    Matrix (Fin (2 * lmax) × H) (Fin (2 * lmax) × H) ℂ :=
  matrixExponential ((-(Complex.I * (t : ℂ))) • floquetHamiltonian ω Hm lmax)

/-- Transition amplitude `⟨l| e^{-i Heff^{lmax} t} |l'⟩` as a matrix on `H`. -/
def transitionAmplitude (ω : ℝ) (Hm : ℤ → Matrix H H ℂ) (lmax : ℕ)
    (l l' : Fin (2 * lmax)) (t : ℝ) : Matrix H H ℂ :=
  fun h h' => evolutionOf ω Hm lmax t (l, h) (l', h')

/-- The truncated time-evolved state `|ψ^{lmax}(t)⟩` of Eq. (19), for abstract
Fourier data `(ω, Hm)` (used both in the cut-off and in the decaying case). -/
def truncatedStateOf (ω : ℝ) (Hm : ℤ → Matrix H H ℂ) (lmax : ℕ) (h : 1 ≤ lmax)
    (t : ℝ) (ψ0 : H → ℂ) : H → ℂ :=
  ∑ j : Fin (2 * lmax),
    (Complex.exp (-(Complex.I * ((((fourierIndex lmax j : ℤ) : ℝ) * ω * t : ℝ) : ℂ)))) •
      (transitionAmplitude ω Hm lmax j (zeroIndex lmax h) t *ᵥ ψ0)

/-- The truncated time-evolved state of Eq. (19). -/
def truncatedState (P : PeriodicHamiltonian H) (lmax : ℕ) (h : 1 ≤ lmax)
    (t : ℝ) (ψ0 : H → ℂ) : H → ℂ :=
  truncatedStateOf P.ω P.Hm lmax h t ψ0

/-- The exact time-evolved state `U(t) |ψ(0)⟩`. -/
def exactState (M : TimePeriodicModel H) (t : ℝ) (ψ0 : H → ℂ) : H → ℂ :=
  M.exactEvolution t *ᵥ ψ0

/-! ## Norms of states -/

/-- Euclidean norm of a complex vector on a finite index type; the Hilbert-space
norm used in every state-distance bound of the paper. -/
def vecNorm {ι : Type*} [Fintype ι] (ψ : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖ψ i‖ ^ 2)

/-- Euclidean norm of a state on the physical register. -/
def stateNorm (ψ : H → ℂ) : ℝ := vecNorm ψ

/-- The vector `|0⟩ |ψ⟩` of the extended space `C^{8lmax} ⊗ H`, where `|0⟩` is
the slot `h0` of the ancilla register. -/
def ancillaZeroState (lmax : ℕ) (h0 : Fin (2 * (4 * lmax))) (ψ : H → ℂ) :
    Fin (2 * (4 * lmax)) × H → ℂ :=
  fun p => if p.1 = h0 then ψ p.2 else 0

/-! ## Periodic-boundary-condition refinement, Eq. (101) -/

/-- Block of the refined effective Hamiltonian `Heff,pbc^{4lmax}` of Eq. (101):
off-diagonal blocks use the cyclic representative modulo `8*lmax`. -/
def pbcBlock (ω : ℝ) (Hm : ℤ → Matrix H H ℂ) (lmax : ℕ) (l l' : ℤ) : Matrix H H ℂ :=
  if l = l' then Hm 0 - (((l : ℝ) * ω : ℝ) : ℂ) • (1 : Matrix H H ℂ)
  else Hm (cyclicShiftRep lmax (l - l'))

/-- The refined effective Hamiltonian `Heff,pbc^{4lmax}` of Eq. (101) on
`D_{4lmax} ⊗ H`. -/
def floquetHamiltonianPbc (ω : ℝ) (Hm : ℤ → Matrix H H ℂ) (lmax : ℕ) :
    Matrix (Fin (2 * (4 * lmax)) × H) (Fin (2 * (4 * lmax)) × H) ℂ :=
  fun p q => pbcBlock ω Hm lmax (fourierIndex (4 * lmax) p.1) (fourierIndex (4 * lmax) q.1) p.2 q.2

/-- The refined evolution `e^{-i Heff,pbc^{4lmax} t}`. -/
def pbcEvolution (ω : ℝ) (Hm : ℤ → Matrix H H ℂ) (lmax : ℕ) (t : ℝ) :
    Matrix (Fin (2 * (4 * lmax)) × H) (Fin (2 * (4 * lmax)) × H) ℂ :=
  matrixExponential ((-(Complex.I * (t : ℂ))) • floquetHamiltonianPbc ω Hm lmax)

/-- Transition amplitude of the refined Hamiltonian. -/
def pbcTransitionAmplitude (ω : ℝ) (Hm : ℤ → Matrix H H ℂ) (lmax : ℕ)
    (l l' : Fin (2 * (4 * lmax))) (t : ℝ) : Matrix H H ℂ :=
  fun h h' => pbcEvolution ω Hm lmax t (l, h) (l', h')

/-! ## The two amplification unitaries of Eqs. (72), (102), (103) -/

/-- Ancilla basis vector `|i⟩` on the extended window `D_{4lmax}`. -/
def ancillaUnit (lmax : ℕ) (i : Fin (2 * (4 * lmax))) : Fin (2 * (4 * lmax)) → ℂ :=
  fun j => if j = i then 1 else 0

/-- The uniform state `|a_{4lmax}⟩` over the whole window `D_{4lmax}`. -/
def uniformAll (lmax : ℕ) : Fin (2 * (4 * lmax)) → ℂ :=
  fun _ => (((Real.sqrt (8 * (lmax : ℝ)))⁻¹ : ℝ) : ℂ)

/-- The uniform state `|a_{lmax}⟩` of Eq. (21), embedded in `D_{4lmax}`. -/
def uniformL (lmax : ℕ) : Fin (2 * (4 * lmax)) → ℂ :=
  fun j => ∑ j' : Fin (2 * lmax),
    if embed4 lmax j' = j then (((Real.sqrt (2 * (lmax : ℝ)))⁻¹ : ℝ) : ℂ) else 0

/-- A pair of state-preparation unitaries `Uini^{lmax}` and `Uini^{4lmax}` of
Eqs. (66)-(67): each is unitary and maps `|0⟩` to the corresponding uniform
ancilla state. -/
structure AmplificationUnitary (lmax : ℕ) where
  /-- The window is nonempty. -/
  hpos : 1 ≤ lmax
  /-- `Uini^{lmax}` on the extended window. -/
  UiniL : Matrix (Fin (2 * (4 * lmax))) (Fin (2 * (4 * lmax))) ℂ
  /-- `Uini^{4lmax}` on the extended window. -/
  Uini4 : Matrix (Fin (2 * (4 * lmax))) (Fin (2 * (4 * lmax))) ℂ
  /-- `Uini^{lmax}` is unitary. -/
  unitaryL : UiniL * UiniLᴴ = 1 ∧ UiniLᴴ * UiniL = 1
  /-- `Uini^{4lmax}` is unitary. -/
  unitary4 : Uini4 * Uini4ᴴ = 1 ∧ Uini4ᴴ * Uini4 = 1
  /-- `Uini^{lmax} |0⟩ = |a_{lmax}⟩`. -/
  preparesL : UiniL *ᵥ ancillaUnit lmax (embed4 lmax (zeroIndex lmax hpos)) = uniformL lmax
  /-- `Uini^{4lmax} |0⟩ = |a_{4lmax}⟩`. -/
  prepares4 : Uini4 *ᵥ ancillaUnit lmax (embed4 lmax (zeroIndex lmax hpos)) = uniformAll lmax

/-- Lift an ancilla matrix to `D_{4lmax} ⊗ H` by tensoring with the identity. -/
def liftA (lmax : ℕ) (A : Matrix (Fin (2 * (4 * lmax))) (Fin (2 * (4 * lmax))) ℂ) :
    Matrix (Fin (2 * (4 * lmax)) × H) (Fin (2 * (4 * lmax)) × H) ℂ :=
  fun p q => A p.1 q.1 * (if p.2 = q.2 then 1 else 0)

/-- The phase `e^{-i t ∑_l lω |l⟩⟨l|}` of Eq. (72). -/
def phaseDiagonal (ω : ℝ) (lmax : ℕ) (t : ℝ) : Matrix (Fin (2 * (4 * lmax)) × H) (Fin (2 * (4 * lmax)) × H) ℂ :=
  liftA lmax (diagonal (fun j : Fin (2 * (4 * lmax)) =>
    Complex.exp (-(Complex.I * ((((fourierIndex (4 * lmax) j : ℤ) : ℝ) * ω * t : ℝ) : ℂ)))))

/-- The reflection `R = 2|0⟩⟨0| - 1` on the ancilla, used by Eq. (103). -/
def reflectionA (lmax : ℕ) (h0 : Fin (2 * (4 * lmax))) :
    Matrix (Fin (2 * (4 * lmax)) × H) (Fin (2 * (4 * lmax)) × H) ℂ :=
  liftA lmax (diagonal (fun j => if j = h0 then 1 else -1))

/-- The `⟨0| · |0⟩` block of a matrix on the extended space. -/
def zeroBlock (lmax : ℕ) (h0 : Fin (2 * (4 * lmax)))
    (U : Matrix (Fin (2 * (4 * lmax)) × H) (Fin (2 * (4 * lmax)) × H) ℂ) : Matrix H H ℂ :=
  fun h h' => U (h0, h) (h0, h')

/-- `Uamp1` of Eq. (72) in the truncated (non-refined) space, with
`Heff^{4lmax}` (window `D_{4lmax}`). -/
def amp1Full (ω : ℝ) (Hm : ℤ → Matrix H H ℂ) (lmax : ℕ) (A : AmplificationUnitary lmax)
    (t : ℝ) : Matrix (Fin (2 * (4 * lmax)) × H) (Fin (2 * (4 * lmax)) × H) ℂ :=
  (liftA lmax A.Uini4)ᴴ * phaseDiagonal ω lmax t * evolutionOf ω Hm (4 * lmax) t * liftA lmax A.UiniL

/-- `Uamp1,pbc` of Eq. (102) with the refined Hamiltonian. -/
def amp1PbcFull (ω : ℝ) (Hm : ℤ → Matrix H H ℂ) (lmax : ℕ) (A : AmplificationUnitary lmax)
    (t : ℝ) : Matrix (Fin (2 * (4 * lmax)) × H) (Fin (2 * (4 * lmax)) × H) ℂ :=
  (liftA lmax A.Uini4)ᴴ * phaseDiagonal ω lmax t * pbcEvolution ω Hm lmax t * liftA lmax A.UiniL

/-- `Uamp2,pbc = -Uamp1 R Uamp1† R Uamp1` of Eq. (103). -/
def amp2PbcFull (ω : ℝ) (Hm : ℤ → Matrix H H ℂ) (lmax : ℕ) (A : AmplificationUnitary lmax)
    (t : ℝ) (h0 : Fin (2 * (4 * lmax))) : Matrix (Fin (2 * (4 * lmax)) × H) (Fin (2 * (4 * lmax)) × H) ℂ :=
  -(amp1PbcFull ω Hm lmax A t) * reflectionA (H := H) lmax h0 *
    (amp1PbcFull ω Hm lmax A t)ᴴ * reflectionA (H := H) lmax h0 *
    amp1PbcFull ω Hm lmax A t

/-- The `⟨0| Uamp1 |0⟩` block of Eq. (74). -/
def amp1Block (P : PeriodicHamiltonian H) (lmax : ℕ) (A : AmplificationUnitary lmax) (t : ℝ) :
    Matrix H H ℂ :=
  zeroBlock lmax (embed4 lmax (zeroIndex lmax A.hpos)) (amp1Full P.ω P.Hm lmax A t)

/-- The `⟨0| Uamp1,pbc |0⟩` block of Eq. (105). -/
def amp1PbcBlock (P : PeriodicHamiltonian H) (lmax : ℕ) (A : AmplificationUnitary lmax) (t : ℝ) :
    Matrix H H ℂ :=
  zeroBlock lmax (embed4 lmax (zeroIndex lmax A.hpos)) (amp1PbcFull P.ω P.Hm lmax A t)

/-- The `⟨0| Uamp2,pbc |0⟩` block of Eq. (106). -/
def amp2PbcBlock (P : PeriodicHamiltonian H) (lmax : ℕ) (A : AmplificationUnitary lmax) (t : ℝ) :
    Matrix H H ℂ :=
  zeroBlock lmax (embed4 lmax (zeroIndex lmax A.hpos))
    (amp2PbcFull P.ω P.Hm lmax A t (embed4 lmax (zeroIndex lmax A.hpos)))

/-! ## Exponentially-decaying Fourier components (Appendix C) -/

/-- Exact propagator data for an exponentially-decaying periodic Hamiltonian:
the decay data of Eq. (191) together with the time-ordered propagator `U(t)`. -/
structure DecayingModel (H : Type*) [Fintype H] [DecidableEq H] where
  /-- Decay data `‖H_m‖ ≤ h e^{-|m|/ζ}` of Eq. (191). -/
  decay : DecayingHamiltonian H
  /-- The exact time-ordered propagator. -/
  exactEvolution : ℝ → Matrix H H ℂ

/-- The exact time-evolved state of a decaying periodic Hamiltonian. -/
def exactStateDec (M : DecayingModel H) (t : ℝ) (ψ0 : H → ℂ) : H → ℂ :=
  M.exactEvolution t *ᵥ ψ0

/-- The truncated state of Eq. (19) for decaying Fourier components. -/
def truncatedStateDec (M : DecayingModel H) (lmax : ℕ) (h : 1 ≤ lmax)
    (t : ℝ) (ψ0 : H → ℂ) : H → ℂ :=
  truncatedStateOf M.decay.ω M.decay.Hm lmax h t ψ0

/-- The constant `β = (1 - e^{-1/ζ})⁻¹` of Eq. (193). -/
def betaOf (D : DecayingHamiltonian H) : ℝ := (1 - Real.exp (-(1 / D.ζ)))⁻¹

/-- The constant `ζ' = (1/ζ - 1 + e^{-1/ζ})⁻¹` of Eq. (193). -/
def zetaPrimeOf (D : DecayingHamiltonian H) : ℝ :=
  (1 / D.ζ - 1 + Real.exp (-(1 / D.ζ)))⁻¹

/-- Truncation order `lmax` of Eq. (210). -/
def decayingTruncationOrder (D : DecayingHamiltonian H) (t ε : ℝ) : ℕ :=
  Nat.ceil (2 * betaOf D * zetaPrimeOf D * D.h * t + zetaPrimeOf D * Real.log (1 / ε)
    + zetaPrimeOf D * Real.log (4 * zetaPrimeOf D) + 2 * zetaPrimeOf D / betaOf D + 1)

/-! ## Truncation order `lmax` of Eq. (59) -/

def truncationOrder (P : PeriodicHamiltonian H) (t ε : ℝ) : ℕ :=
  P.mmax + Nat.ceil
    (((Real.exp 1) ^ 2 * (P.mmax : ℝ) * periodicGamma P * t) +
      4 * (P.mmax : ℝ) * Real.log (10 * (P.mmax : ℝ) / ε) /
        Real.log (Real.exp 1 + (Real.exp 1 * periodicGamma P * t)⁻¹ *
          Real.log (10 * (P.mmax : ℝ) / ε)))

/-! ## Resource ledger for Theorems 1 and 2 -/

/-- Resource accounting of a time-periodic simulation protocol: number of
ancillary qubits, query complexity, additional gates per query, and the
achieved simulation error and failure probability. -/
structure SimulationResources where
  /-- Number of ancillary qubits. -/
  ancillas : ℝ
  /-- Query complexity (number of oracle queries). -/
  queries : ℝ
  /-- Additional gates per query. -/
  gatesPerQuery : ℝ
  /-- Achieved simulation error. -/
  error : ℝ
  /-- Failure probability. -/
  failureProbability : ℝ

end Qatlib.Papers.TimePeriodic22.MainResults
