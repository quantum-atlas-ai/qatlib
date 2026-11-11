/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabEquiv04.MainResults.Model.AdiabaticDefs

/-!
# Circuit history states and Hamiltonians

This module defines circuit prefixes, unary clock configurations, and the vectors `gamma` and
`historyState` used in the circuit-to-adiabatic construction of [AharonovEtAl2007Adiabatic]. It
builds Hermitian clock, input, and propagation matrices, their interpolating Hamiltonians, and
the associated reduced clock and legal-clock compressions.

## Main statements

* `historyState`: the scaled sum of computational states paired with legal clock configurations.
* `Hinit`, `Hfinal`, and `Hpath`: the initial, final, and interpolating Hamiltonians.
* `Hpath3` and `HS0`: the alternative propagation path and reduced clock model.

## References

* [Aharonov et al., 2007][AharonovEtAl2007Adiabatic]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.AdiabEquiv04.MainResults.Model

/-- Computational basis configurations of `n` binary sites. -/
abbrev CompBasis (n : ℕ) := Fin n → Fin 2

/-- Binary clock configurations on `L` sites. -/
abbrev ClockBasis (L : ℕ) := Fin L → Fin 2

/-- The product of the computational and clock basis types. -/
abbrev TotalBasis (n L : ℕ) := CompBasis n × ClockBasis L

/-- Two distinct qubit positions together with a unitary matrix on their two-qubit basis. -/
structure TwoQubitGate (n : ℕ) where

  i : Fin n

  j : Fin n

  hij : i ≠ j

  W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

  unitary : W ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ

/-- The matrix applying `g.W` at the two selected qubits, with zero entries when the
configurations differ at another qubit. -/
def gateMatrix {n : ℕ} (g : TwoQubitGate n) : Matrix (CompBasis n) (CompBasis n) ℂ :=
  fun x y =>
    if ∀ k : Fin n, k ≠ g.i → k ≠ g.j → x k = y k then
      g.W (x g.i, x g.j) (y g.i, y g.j)
    else 0

/-- A sequence of two-qubit gates indexed by the natural numbers. -/
abbrev GateSeq (n : ℕ) := ℕ → TwoQubitGate n

/-- The product of the first `ℓ` gate matrices, formed by successively multiplying each gate on
the left starting from the identity. -/
def prefixU {n : ℕ} (gates : GateSeq n) (ℓ : ℕ) : Matrix (CompBasis n) (CompBasis n) ℂ :=
  (List.finRange ℓ).foldl (fun M i => gateMatrix (gates i) * M) 1

/-- The computational basis vector supported on the all-zero configuration. -/
def zeroBasis (n : ℕ) : Vector (CompBasis n) :=
  fun x => if x = (fun _ => 0) then 1 else 0

/-- The computational vector obtained by applying the first `ℓ` gates to `zeroBasis n`. -/
def alpha {n : ℕ} (gates : GateSeq n) (ℓ : ℕ) : Vector (CompBasis n) :=
  prefixU gates ℓ *ᵥ zeroBasis n

/-- The unary clock configuration with ones at indices below `ℓ` and zeros at the remaining
indices. -/
def legalClock (L ℓ : ℕ) : ClockBasis L :=
  fun i => if i.val < ℓ then 1 else 0

/-- The vector `alpha gates ℓ` paired with the unary clock configuration at time `ℓ`. -/
def gamma {n L : ℕ} (gates : GateSeq n) (ℓ : Fin (L + 1)) : Vector (TotalBasis n L) :=
  fun p => if p.2 = legalClock L ℓ.val then alpha gates ℓ.val p.1 else 0

/-- The sum of the vectors `gamma gates ℓ`, scaled by the inverse square root of `L + 1`. -/
def historyState {n L : ℕ} (gates : GateSeq n) : Vector (TotalBasis n L) :=
  ((Real.sqrt ((L : ℝ) + 1))⁻¹ : ℂ) •
    (∑ ℓ : Fin (L + 1), gamma (L := L) gates ℓ)

/-- The coordinate projection associated with a decidable predicate is Hermitian. -/
theorem basisProj_isHermitian {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι → Prop) [DecidablePred P] : (basisProj P).IsHermitian := by
  unfold basisProj Matrix.IsHermitian
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hP : P i <;> simp [hP]
  · have hji : ¬ (j = i) := fun h => hij h.symm
    simp [hij, hji]

/-- A finite sum of Hermitian matrices is Hermitian. -/
theorem matSum_isHermitian {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (f : κ → Matrix ι ι ℂ) (h : ∀ k, (f k).IsHermitian) :
    (∑ k : κ, f k).IsHermitian := by
  classical
  have key : ∀ s : Finset κ, (∀ k ∈ s, (f k).IsHermitian) →
      (∑ k ∈ s, f k).IsHermitian := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
        intro hs
        rw [Finset.sum_insert ha]
        exact (hs a (Finset.mem_insert_self a s)).add
          (ih (fun k hk => hs k (Finset.mem_insert_of_mem hk)))
  simpa using key Finset.univ (fun k _ => h k)

/-- The complex number `1 / 2` is self-adjoint. -/
theorem half_isSelfAdjoint : IsSelfAdjoint (1 / 2 : ℂ) := by
  rw [IsSelfAdjoint, Complex.star_def,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]

/-- The sum of coordinate projections penalizing adjacent clock bits of the form `01`. -/
def Hclock (n L : ℕ) (hL2 : 2 ≤ L) : Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  ∑ i : Fin (L - 1),
    basisProj (fun p : TotalBasis n L =>
      p.2 ⟨i.val, by omega⟩ = 0 ∧ p.2 ⟨i.val + 1, by omega⟩ = 1)

/-- The sum of coordinate projections penalizing a computational one when the first clock bit is
zero. -/
def Hinput (n L : ℕ) (hL2 : 2 ≤ L) : Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  ∑ q : Fin n,
    basisProj (fun p : TotalBasis n L =>
      p.1 q = 1 ∧ p.2 ⟨0, by omega⟩ = 0)

/-- The coordinate projection onto configurations whose first clock bit is one. -/
def Hclockinit (n L : ℕ) (hL2 : 2 ≤ L) : Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  basisProj (fun p : TotalBasis n L => p.2 ⟨0, by omega⟩ = 1)

/-- The clock penalty matrix is Hermitian. -/
theorem Hclock_isHermitian (n L : ℕ) (hL2 : 2 ≤ L) :
    (Hclock n L hL2).IsHermitian :=
  matSum_isHermitian _ (fun _ => basisProj_isHermitian _)

/-- The input penalty matrix is Hermitian. -/
theorem Hinput_isHermitian (n L : ℕ) (hL2 : 2 ≤ L) :
    (Hinput n L hL2).IsHermitian :=
  matSum_isHermitian _ (fun _ => basisProj_isHermitian _)

/-- The initial-clock penalty matrix is Hermitian. -/
theorem Hclockinit_isHermitian (n L : ℕ) (hL2 : 2 ≤ L) :
    (Hclockinit n L hL2).IsHermitian :=
  basisProj_isHermitian _

/-- The local clock predicate selecting the pattern before propagation step `l`, with separate
boundary cases. -/
def prevPattern (n L : ℕ) (hL2 : 2 ≤ L) (l : Fin L) : ClockBasis L → Prop :=
  if h0 : l.val = 0 then
    (fun p => p ⟨0, by omega⟩ = 0 ∧ p ⟨1, by omega⟩ = 0)
  else if hL : l.val = L - 1 then
    (fun p => p ⟨L - 2, by omega⟩ = 1 ∧ p ⟨L - 1, by omega⟩ = 0)
  else
    (fun p => p ⟨l.val - 1, by omega⟩ = 1 ∧ p l = 0 ∧ p ⟨l.val + 1, by omega⟩ = 0)

/-- The local clock predicate selecting the pattern after propagation step `l`, with separate
boundary cases. -/
def nextPattern (n L : ℕ) (hL2 : 2 ≤ L) (l : Fin L) : ClockBasis L → Prop :=
  if h0 : l.val = 0 then
    (fun p => p ⟨0, by omega⟩ = 1 ∧ p ⟨1, by omega⟩ = 0)
  else if hL : l.val = L - 1 then
    (fun p => p ⟨L - 2, by omega⟩ = 1 ∧ p ⟨L - 1, by omega⟩ = 1)
  else
    (fun p => p ⟨l.val - 1, by omega⟩ = 1 ∧ p l = 1 ∧ p ⟨l.val + 1, by omega⟩ = 0)

instance prevPattern_decidable (n L : ℕ) (hL2 : 2 ≤ L) (l : Fin L) :
    DecidablePred (prevPattern n L hL2 l) := fun _ => Classical.dec _

instance nextPattern_decidable (n L : ℕ) (hL2 : 2 ≤ L) (l : Fin L) :
    DecidablePred (nextPattern n L hL2 l) := fun _ => Classical.dec _

/-- The predicate on total configurations obtained by applying `P` to their clock component. -/
def liftClock (n L : ℕ) (P : ClockBasis L → Prop) : TotalBasis n L → Prop :=
  fun x => P x.2

instance liftClock_decidable (n L : ℕ) (P : ClockBasis L → Prop) [d : DecidablePred P] :
    DecidablePred (liftClock n L P) := fun x => d x.2

/-- The matrix with computational entries from `U` when the row clock satisfies `pBr` and the
column clock satisfies `pKet`, and zero otherwise. -/
def clockPairOp {n L : ℕ} (pBr pKet : ClockBasis L → Prop)
    [DecidablePred pBr] [DecidablePred pKet]
    (U : Matrix (CompBasis n) (CompBasis n) ℂ) :
    Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  fun x y => if pBr x.2 ∧ pKet y.2 then U x.1 y.1 else 0

/-- Conjugate transposition of `clockPairOp` swaps its clock predicates and conjugate-transposes
its computational matrix. -/
theorem clockPairOp_conjTranspose {n L : ℕ} (pBr pKet : ClockBasis L → Prop)
    [DecidablePred pBr] [DecidablePred pKet]
    (U : Matrix (CompBasis n) (CompBasis n) ℂ) :
    (clockPairOp pBr pKet U)ᴴ = clockPairOp pKet pBr Uᴴ := by
  ext x y
  rw [Matrix.conjTranspose_apply]
  unfold clockPairOp
  by_cases h : pBr y.2 ∧ pKet x.2
  · have h' : pKet x.2 ∧ pBr y.2 := ⟨h.2, h.1⟩
    rw [if_pos h, if_pos h', Matrix.conjTranspose_apply]
  · have h' : ¬ (pKet x.2 ∧ pBr y.2) := fun hc => h ⟨hc.2, hc.1⟩
    rw [if_neg h, if_neg h']
    simp

/-- The propagation matrix formed from the previous and next clock projections minus the forward
and reverse clock-pair operators. -/
def Hprop (n L : ℕ) (hL2 : 2 ≤ L) (U : Matrix (CompBasis n) (CompBasis n) ℂ)
    (l : Fin L) : Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  basisProj (liftClock n L (prevPattern n L hL2 l)) +
    basisProj (liftClock n L (nextPattern n L hL2 l)) -
    clockPairOp (nextPattern n L hL2 l) (prevPattern n L hL2 l) U -
    clockPairOp (prevPattern n L hL2 l) (nextPattern n L hL2 l) Uᴴ

/-- The propagation matrix `Hprop` is Hermitian for every computational matrix `U`. -/
theorem Hprop_isHermitian (n L : ℕ) (hL2 : 2 ≤ L)
    (U : Matrix (CompBasis n) (CompBasis n) ℂ) (l : Fin L) :
    (Hprop n L hL2 U l).IsHermitian := by
  have hp := basisProj_isHermitian (liftClock n L (prevPattern n L hL2 l))
  have hn := basisProj_isHermitian (liftClock n L (nextPattern n L hL2 l))
  have hB : (clockPairOp (nextPattern n L hL2 l) (prevPattern n L hL2 l) U +
      clockPairOp (prevPattern n L hL2 l) (nextPattern n L hL2 l) Uᴴ).IsHermitian := by
    simpa [clockPairOp_conjTranspose] using
      Matrix.isHermitian_add_transpose_self
        (clockPairOp (nextPattern n L hL2 l) (prevPattern n L hL2 l) U)
  unfold Hprop
  rw [sub_sub]
  show ((basisProj (liftClock n L (prevPattern n L hL2 l)) +
      basisProj (liftClock n L (nextPattern n L hL2 l))) -
    (clockPairOp (nextPattern n L hL2 l) (prevPattern n L hL2 l) U +
     clockPairOp (prevPattern n L hL2 l) (nextPattern n L hL2 l) Uᴴ)).IsHermitian
  exact (hp.add hn).sub hB

/-- The initial Hamiltonian formed by summing the initial-clock, input, and clock penalties. -/
def Hinit (n L : ℕ) (hL2 : 2 ≤ L) : Hamiltonian (TotalBasis n L) :=
  ⟨Hclockinit n L hL2 + Hinput n L hL2 + Hclock n L hL2,
    ((Hclockinit_isHermitian n L hL2).add
      (Hinput_isHermitian n L hL2)).add (Hclock_isHermitian n L hL2)⟩

/-- The final Hamiltonian formed by adding half the sum of propagation matrices to the input and
clock penalties. -/
def Hfinal (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) :
    Hamiltonian (TotalBasis n L) :=
  ⟨(1 / 2 : ℂ) • (∑ l : Fin L, Hprop n L hL2 (gateMatrix (gates l)) l) +
      Hinput n L hL2 + Hclock n L hL2, by
    have hsum : (∑ l : Fin L, Hprop n L hL2 (gateMatrix (gates l)) l).IsHermitian :=
      matSum_isHermitian _ (fun l => Hprop_isHermitian n L hL2 _ l)
    exact ((hsum.smul half_isSelfAdjoint).add
      (Hinput_isHermitian n L hL2)).add (Hclock_isHermitian n L hL2)⟩

/-- The affine Hamiltonian path from `Hinit` to `Hfinal`. -/
def Hpath (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) (s : ℝ) :
    Hamiltonian (TotalBasis n L) :=
  Hamiltonian.path (Hinit n L hL2) (Hfinal n L hL2 gates) s

/-- At parameter zero, the matrix of `Hpath` equals the matrix of `Hinit`. -/
theorem Hpath_zero (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) :
    (Hpath n L hL2 gates 0).mat = (Hinit n L hL2).mat := by
  unfold Hpath Hamiltonian.path Hamiltonian.add Hamiltonian.realSmul
  simp

/-- At parameter one, the matrix of `Hpath` equals the matrix of `Hfinal`. -/
theorem Hpath_one (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) :
    (Hpath n L hL2 gates 1).mat = (Hfinal n L hL2 gates).mat := by
  unfold Hpath Hamiltonian.path Hamiltonian.add Hamiltonian.realSmul
  simp

/-- The matrix with computational entries from `U` when the row clock bit at `l` is one and the
column clock bit there is zero, and zero otherwise. -/
def transitionOp {n L : ℕ} (U : Matrix (CompBasis n) (CompBasis n) ℂ)
    (l : Fin L) : Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  fun x y => if x.2 l = 1 ∧ y.2 l = 0 then U x.1 y.1 else 0

/-- The alternative propagation matrix formed from the two clock-pattern projections minus
`transitionOp U l` and its conjugate transpose. -/
def Hprop3 (n L : ℕ) (hL2 : 2 ≤ L) (U : Matrix (CompBasis n) (CompBasis n) ℂ)
    (l : Fin L) : Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  basisProj (liftClock n L (prevPattern n L hL2 l)) +
    basisProj (liftClock n L (nextPattern n L hL2 l)) -
    transitionOp U l - (transitionOp U l)ᴴ

/-- The alternative propagation matrix `Hprop3` is Hermitian. -/
theorem Hprop3_isHermitian (n L : ℕ) (hL2 : 2 ≤ L)
    (U : Matrix (CompBasis n) (CompBasis n) ℂ) (l : Fin L) :
    (Hprop3 n L hL2 U l).IsHermitian := by
  have hp := basisProj_isHermitian (liftClock n L (prevPattern n L hL2 l))
  have hn := basisProj_isHermitian (liftClock n L (nextPattern n L hL2 l))
  have hB : (transitionOp U l + (transitionOp U l)ᴴ).IsHermitian :=
    Matrix.isHermitian_add_transpose_self _
  unfold Hprop3
  rw [sub_sub]
  show ((basisProj (liftClock n L (prevPattern n L hL2 l)) +
      basisProj (liftClock n L (nextPattern n L hL2 l))) -
    (transitionOp U l + (transitionOp U l)ᴴ)).IsHermitian
  exact (hp.add hn).sub hB

/-- The Hamiltonian obtained by scaling the clock penalty by the real parameter `J`. -/
def Jclock (n L : ℕ) (hL2 : 2 ≤ L) (J : ℝ) : Hamiltonian (TotalBasis n L) :=
  Hamiltonian.realSmul J ⟨Hclock n L hL2, Hclock_isHermitian n L hL2⟩

/-- The initial Hamiltonian with initial-clock and input penalties and clock penalty scaled by
`J`. -/
def Hinit3 (n L : ℕ) (hL2 : 2 ≤ L) (J : ℝ) : Hamiltonian (TotalBasis n L) :=
  (⟨Hclockinit n L hL2, Hclockinit_isHermitian n L hL2⟩ : Hamiltonian (TotalBasis n L)).add
    ((⟨Hinput n L hL2, Hinput_isHermitian n L hL2⟩ : Hamiltonian (TotalBasis n L)).add
      (Jclock n L hL2 J))

/-- The final Hamiltonian with half the sum of `Hprop3` terms, the input penalty, and the clock
penalty scaled by `J`. -/
def Hfinal3 (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) (J : ℝ) :
    Hamiltonian (TotalBasis n L) :=
  ⟨(1 / 2 : ℂ) • (∑ l : Fin L, Hprop3 n L hL2 (gateMatrix (gates l)) l) +
      Hinput n L hL2 + J • Hclock n L hL2, by
    have hsum : (∑ l : Fin L, Hprop3 n L hL2 (gateMatrix (gates l)) l).IsHermitian :=
      matSum_isHermitian _ (fun l => Hprop3_isHermitian n L hL2 _ l)
    have hJ : (J • Hclock n L hL2).IsHermitian :=
      (Hclock_isHermitian n L hL2).smul (by
        show star J = J
        exact star_trivial J)
    exact ((hsum.smul half_isSelfAdjoint).add
      (Hinput_isHermitian n L hL2)).add hJ⟩

/-- The affine Hamiltonian path from `Hinit3` to `Hfinal3`. -/
def Hpath3 (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) (J : ℝ) (s : ℝ) :
    Hamiltonian (TotalBasis n L) :=
  Hamiltonian.path (Hinit3 n L hL2 J) (Hfinal3 n L hL2 gates J) s

/-- The diagonal clock matrix with entry zero at index zero and entry one at every other index. -/
def S0Init (L : ℕ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℂ :=
  fun i j => if i = j then (if i.val = 0 then 0 else 1) else 0

/-- The tridiagonal clock matrix with diagonal value `1/2` at the endpoints, value one in the
interior, and value `-1/2` on adjacent off-diagonal entries. -/
def S0Final (L : ℕ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℂ :=
  fun i j =>
    if i = j then (if i.val = 0 ∨ i.val = L then 1 / 2 else 1)
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -(1 / 2)
    else 0

/-- The reduced initial clock matrix `S0Init L` is Hermitian. -/
theorem S0Init_isHermitian (L : ℕ) : (S0Init L).IsHermitian := by
  unfold S0Init Matrix.IsHermitian
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hij : i = j
  · subst hij
    by_cases h0 : i.val = 0 <;> simp [h0]
  · have hji : ¬ (j = i) := fun h => hij h.symm
    simp [hij, hji]

/-- The reduced final clock matrix `S0Final L` is Hermitian. -/
theorem S0Final_isHermitian (L : ℕ) : (S0Final L).IsHermitian := by
  unfold S0Final Matrix.IsHermitian
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hij : i = j
  · subst hij
    by_cases h0 : i.val = 0
    · simp [h0]
    · by_cases hL : i.val = L <;> simp [h0, hL]
  · have hji : ¬ (j = i) := fun h => hij h.symm
    by_cases h1 : i.val + 1 = j.val
    · have h2 : ¬ (j.val + 1 = i.val) := by omega
      simp [hij, hji, h1, h2]
    · by_cases h2 : j.val + 1 = i.val
      · simp [hij, hji, h1, h2]
      · simp [hij, hji, h1, h2]

/-- The Hamiltonian obtained by affine interpolation between `S0Init L` and `S0Final L`. -/
def HS0 (L : ℕ) (s : ℝ) : Hamiltonian (Fin (L + 1)) :=
  Hamiltonian.path ⟨S0Init L, S0Init_isHermitian L⟩
    ⟨S0Final L, S0Final_isHermitian L⟩ s

/-- The condition that a total configuration has a unary clock configuration `legalClock L ℓ`
for some `ℓ ≤ L`. -/
def legalClockProp (n L : ℕ) (p : TotalBasis n L) : Prop :=
  ∃ ℓ : Fin (L + 1), p.2 = legalClock L ℓ.val

instance legalClockProp_decidable (n L : ℕ) : DecidablePred (legalClockProp n L) :=
  fun p => Classical.dec _

/-- The coordinate projection onto total configurations with a legal unary clock. -/
def legalClockProj (n L : ℕ) : Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  basisProj (legalClockProp n L)

/-- The legal-clock coordinate projection is Hermitian. -/
theorem legalClockProj_isHermitian (n L : ℕ) : (legalClockProj n L).IsHermitian :=
  basisProj_isHermitian _

/-- The Hamiltonian obtained by compressing `Hpath` to the legal-clock coordinates. -/
def HS (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) (s : ℝ) :
    Hamiltonian (TotalBasis n L) :=
  ⟨compress (legalClockProp n L) (Hpath n L hL2 gates s),
    compress_isHermitian _ _⟩

end Qatlib.Papers.AdiabEquiv04.MainResults.Model
