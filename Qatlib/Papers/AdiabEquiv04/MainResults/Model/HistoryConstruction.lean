/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabEquiv04.MainResults.Model.AdiabaticDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.AdiabEquiv04.MainResults.Model

abbrev CompBasis (n : ℕ) := Fin n → Fin 2

abbrev ClockBasis (L : ℕ) := Fin L → Fin 2

abbrev TotalBasis (n L : ℕ) := CompBasis n × ClockBasis L

structure TwoQubitGate (n : ℕ) where

  i : Fin n

  j : Fin n

  hij : i ≠ j

  W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

  unitary : W ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ

def gateMatrix {n : ℕ} (g : TwoQubitGate n) : Matrix (CompBasis n) (CompBasis n) ℂ :=
  fun x y =>
    if ∀ k : Fin n, k ≠ g.i → k ≠ g.j → x k = y k then
      g.W (x g.i, x g.j) (y g.i, y g.j)
    else 0

abbrev GateSeq (n : ℕ) := ℕ → TwoQubitGate n

def prefixU {n : ℕ} (gates : GateSeq n) (ℓ : ℕ) : Matrix (CompBasis n) (CompBasis n) ℂ :=
  (List.finRange ℓ).foldl (fun M i => gateMatrix (gates i) * M) 1

def zeroBasis (n : ℕ) : Vector (CompBasis n) :=
  fun x => if x = (fun _ => 0) then 1 else 0

def alpha {n : ℕ} (gates : GateSeq n) (ℓ : ℕ) : Vector (CompBasis n) :=
  prefixU gates ℓ *ᵥ zeroBasis n

def legalClock (L ℓ : ℕ) : ClockBasis L :=
  fun i => if i.val < ℓ then 1 else 0

def gamma {n L : ℕ} (gates : GateSeq n) (ℓ : Fin (L + 1)) : Vector (TotalBasis n L) :=
  fun p => if p.2 = legalClock L ℓ.val then alpha gates ℓ.val p.1 else 0

def historyState {n L : ℕ} (gates : GateSeq n) : Vector (TotalBasis n L) :=
  ((Real.sqrt ((L : ℝ) + 1))⁻¹ : ℂ) •
    (∑ ℓ : Fin (L + 1), gamma (L := L) gates ℓ)

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

theorem half_isSelfAdjoint : IsSelfAdjoint (1 / 2 : ℂ) := by
  rw [IsSelfAdjoint, Complex.star_def,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]

def Hclock (n L : ℕ) (hL2 : 2 ≤ L) : Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  ∑ i : Fin (L - 1),
    basisProj (fun p : TotalBasis n L =>
      p.2 ⟨i.val, by omega⟩ = 0 ∧ p.2 ⟨i.val + 1, by omega⟩ = 1)

def Hinput (n L : ℕ) (hL2 : 2 ≤ L) : Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  ∑ q : Fin n,
    basisProj (fun p : TotalBasis n L =>
      p.1 q = 1 ∧ p.2 ⟨0, by omega⟩ = 0)

def Hclockinit (n L : ℕ) (hL2 : 2 ≤ L) : Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  basisProj (fun p : TotalBasis n L => p.2 ⟨0, by omega⟩ = 1)

theorem Hclock_isHermitian (n L : ℕ) (hL2 : 2 ≤ L) :
    (Hclock n L hL2).IsHermitian :=
  matSum_isHermitian _ (fun _ => basisProj_isHermitian _)

theorem Hinput_isHermitian (n L : ℕ) (hL2 : 2 ≤ L) :
    (Hinput n L hL2).IsHermitian :=
  matSum_isHermitian _ (fun _ => basisProj_isHermitian _)

theorem Hclockinit_isHermitian (n L : ℕ) (hL2 : 2 ≤ L) :
    (Hclockinit n L hL2).IsHermitian :=
  basisProj_isHermitian _

def prevPattern (n L : ℕ) (hL2 : 2 ≤ L) (l : Fin L) : ClockBasis L → Prop :=
  if h0 : l.val = 0 then
    (fun p => p ⟨0, by omega⟩ = 0 ∧ p ⟨1, by omega⟩ = 0)
  else if hL : l.val = L - 1 then
    (fun p => p ⟨L - 2, by omega⟩ = 1 ∧ p ⟨L - 1, by omega⟩ = 0)
  else
    (fun p => p ⟨l.val - 1, by omega⟩ = 1 ∧ p l = 0 ∧ p ⟨l.val + 1, by omega⟩ = 0)

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

def liftClock (n L : ℕ) (P : ClockBasis L → Prop) : TotalBasis n L → Prop :=
  fun x => P x.2

instance liftClock_decidable (n L : ℕ) (P : ClockBasis L → Prop) [d : DecidablePred P] :
    DecidablePred (liftClock n L P) := fun x => d x.2

def clockPairOp {n L : ℕ} (pBr pKet : ClockBasis L → Prop)
    [DecidablePred pBr] [DecidablePred pKet]
    (U : Matrix (CompBasis n) (CompBasis n) ℂ) :
    Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  fun x y => if pBr x.2 ∧ pKet y.2 then U x.1 y.1 else 0

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

def Hprop (n L : ℕ) (hL2 : 2 ≤ L) (U : Matrix (CompBasis n) (CompBasis n) ℂ)
    (l : Fin L) : Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  basisProj (liftClock n L (prevPattern n L hL2 l)) +
    basisProj (liftClock n L (nextPattern n L hL2 l)) -
    clockPairOp (nextPattern n L hL2 l) (prevPattern n L hL2 l) U -
    clockPairOp (prevPattern n L hL2 l) (nextPattern n L hL2 l) Uᴴ

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

def Hinit (n L : ℕ) (hL2 : 2 ≤ L) : Hamiltonian (TotalBasis n L) :=
  ⟨Hclockinit n L hL2 + Hinput n L hL2 + Hclock n L hL2,
    ((Hclockinit_isHermitian n L hL2).add
      (Hinput_isHermitian n L hL2)).add (Hclock_isHermitian n L hL2)⟩

def Hfinal (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) :
    Hamiltonian (TotalBasis n L) :=
  ⟨(1 / 2 : ℂ) • (∑ l : Fin L, Hprop n L hL2 (gateMatrix (gates l)) l) +
      Hinput n L hL2 + Hclock n L hL2, by
    have hsum : (∑ l : Fin L, Hprop n L hL2 (gateMatrix (gates l)) l).IsHermitian :=
      matSum_isHermitian _ (fun l => Hprop_isHermitian n L hL2 _ l)
    exact ((hsum.smul half_isSelfAdjoint).add
      (Hinput_isHermitian n L hL2)).add (Hclock_isHermitian n L hL2)⟩

def Hpath (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) (s : ℝ) :
    Hamiltonian (TotalBasis n L) :=
  Hamiltonian.path (Hinit n L hL2) (Hfinal n L hL2 gates) s

theorem Hpath_zero (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) :
    (Hpath n L hL2 gates 0).mat = (Hinit n L hL2).mat := by
  unfold Hpath Hamiltonian.path Hamiltonian.add Hamiltonian.realSmul
  simp

theorem Hpath_one (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) :
    (Hpath n L hL2 gates 1).mat = (Hfinal n L hL2 gates).mat := by
  unfold Hpath Hamiltonian.path Hamiltonian.add Hamiltonian.realSmul
  simp

def transitionOp {n L : ℕ} (U : Matrix (CompBasis n) (CompBasis n) ℂ)
    (l : Fin L) : Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  fun x y => if x.2 l = 1 ∧ y.2 l = 0 then U x.1 y.1 else 0

def Hprop3 (n L : ℕ) (hL2 : 2 ≤ L) (U : Matrix (CompBasis n) (CompBasis n) ℂ)
    (l : Fin L) : Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  basisProj (liftClock n L (prevPattern n L hL2 l)) +
    basisProj (liftClock n L (nextPattern n L hL2 l)) -
    transitionOp U l - (transitionOp U l)ᴴ

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

def Jclock (n L : ℕ) (hL2 : 2 ≤ L) (J : ℝ) : Hamiltonian (TotalBasis n L) :=
  Hamiltonian.realSmul J ⟨Hclock n L hL2, Hclock_isHermitian n L hL2⟩

def Hinit3 (n L : ℕ) (hL2 : 2 ≤ L) (J : ℝ) : Hamiltonian (TotalBasis n L) :=
  (⟨Hclockinit n L hL2, Hclockinit_isHermitian n L hL2⟩ : Hamiltonian (TotalBasis n L)).add
    ((⟨Hinput n L hL2, Hinput_isHermitian n L hL2⟩ : Hamiltonian (TotalBasis n L)).add
      (Jclock n L hL2 J))

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

def Hpath3 (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) (J : ℝ) (s : ℝ) :
    Hamiltonian (TotalBasis n L) :=
  Hamiltonian.path (Hinit3 n L hL2 J) (Hfinal3 n L hL2 gates J) s

def S0Init (L : ℕ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℂ :=
  fun i j => if i = j then (if i.val = 0 then 0 else 1) else 0

def S0Final (L : ℕ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℂ :=
  fun i j =>
    if i = j then (if i.val = 0 ∨ i.val = L then 1 / 2 else 1)
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -(1 / 2)
    else 0

theorem S0Init_isHermitian (L : ℕ) : (S0Init L).IsHermitian := by
  unfold S0Init Matrix.IsHermitian
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hij : i = j
  · subst hij
    by_cases h0 : i.val = 0 <;> simp [h0]
  · have hji : ¬ (j = i) := fun h => hij h.symm
    simp [hij, hji]

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

def HS0 (L : ℕ) (s : ℝ) : Hamiltonian (Fin (L + 1)) :=
  Hamiltonian.path ⟨S0Init L, S0Init_isHermitian L⟩
    ⟨S0Final L, S0Final_isHermitian L⟩ s

def legalClockProp (n L : ℕ) (p : TotalBasis n L) : Prop :=
  ∃ ℓ : Fin (L + 1), p.2 = legalClock L ℓ.val

instance legalClockProp_decidable (n L : ℕ) : DecidablePred (legalClockProp n L) :=
  fun p => Classical.dec _

def legalClockProj (n L : ℕ) : Matrix (TotalBasis n L) (TotalBasis n L) ℂ :=
  basisProj (legalClockProp n L)

theorem legalClockProj_isHermitian (n L : ℕ) : (legalClockProj n L).IsHermitian :=
  basisProj_isHermitian _

def HS (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) (s : ℝ) :
    Hamiltonian (TotalBasis n L) :=
  ⟨compress (legalClockProp n L) (Hpath n L hL2 gates s),
    compress_isHermitian _ _⟩

end Qatlib.Papers.AdiabEquiv04.MainResults.Model
