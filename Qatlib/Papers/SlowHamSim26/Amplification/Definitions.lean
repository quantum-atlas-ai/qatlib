/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SlowHamSim26.FourierTrunc.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# SlowHamSim26 / Amplification — protocol operators of §5

Fixed source: arXiv:2608.17653v1, §5 (pp. 27–30).  This file fixes the
operators used by Lemma 5.1 and Theorems 5.2–5.4:

* `diagPhase T L t = Σ_l e^{-ilωt}|l⟩⟨l|` (the free phase of (5.2));
* `Uamp1` is the symmetry-amplification operator (5.2),
  `Uini† e^{-it Σ lω|l⟩⟨l|} e^{-iH_eff^L t} Uini`, acting on `D^L ⊗ ℂ^d`;
* `Rmat i0 = 2|0⟩⟨0| − I` and `Uamp2` is the oblivious amplification (5.9)–(5.10);
* `HtildeB` / `HeffPbc` are the refined effective Hamiltonian (5.12)/(5.16)
  with the boundary hopping term over `∂F̃`;
* `ancillaVec i0 ψ = |0⟩|ψ⟩` and `floquetBlock` give the paper's matrix
  elements.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SlowHamSim26.Amplification

open scoped Matrix.Norms.L2Operator
open Matrix
open Qatlib.Papers.SlowHamSim26.FourierTrunc

/-- Fixed arXiv:2608.17653v1, Eq. (5.2): the free phase
`Σ_l e^{-ilωt}|l⟩⟨l|` on the truncated Floquet ancilla. -/
def diagPhase {L : ℕ} (T : ℝ) (t : ℝ) : Matrix (Fin (2 * L)) (Fin (2 * L)) ℂ :=
  Matrix.diagonal fun i =>
    Complex.exp (-(Complex.I * (floquetIndexVal L i : ℂ) * (omega T : ℂ) * (t : ℂ)))

/-- The operator `A ⊗ I_d` on `D^L ⊗ ℂ^d` induced by an ancilla operator `A`. -/
def ancillaOp {d L : ℕ} (A : Matrix (Fin (2 * L)) (Fin (2 * L)) ℂ) :
    Matrix (Fin (2 * L) × Fin d) (Fin (2 * L) × Fin d) ℂ :=
  fun p q => A p.1 q.1 * (if p.2 = q.2 then (1 : ℂ) else 0)

/-- Fixed arXiv:2608.17653v1, Eq. (5.2): the symmetry-amplification operator
`U_amp1(t) = U_ini† e^{-it Σ_l lω|l⟩⟨l|} e^{-iH_eff^L t} U_ini` on the
truncated Floquet space `D^L ⊗ ℂ^d`. -/
def Uamp1 {d L : ℕ} (T : ℝ) (Hm : ℤ → Matrix (Fin d) (Fin d) ℂ)
    (Uini : Matrix (Fin (2 * L)) (Fin (2 * L)) ℂ) (t : ℝ) :
    Matrix (Fin (2 * L) × Fin d) (Fin (2 * L) × Fin d) ℂ :=
  ancillaOp (Matrix.conjTranspose Uini * diagPhase (L := L) T t * Uini) *
    timeEvol (Heff T L Hm) t

/-- Fixed arXiv:2608.17653v1, Eq. (5.9): `R = (2|0⟩⟨0| − I) ⊗ I` on the
ancilla, with `i0` the index of `|0⟩`. -/
def Rmat {L : ℕ} (i0 : Fin (2 * L)) : Matrix (Fin (2 * L)) (Fin (2 * L)) ℂ :=
  fun i j => if i = j then (if i = i0 then 1 else -1) else 0

/-- Fixed arXiv:2608.17653v1, Eq. (5.10): the oblivious-amplification operator
`U_amp2(t) = −U_amp1(t) R [U_amp1(t)]† R U_amp1(t)`. -/
def Uamp2 {d L : ℕ} (T : ℝ) (Hm : ℤ → Matrix (Fin d) (Fin d) ℂ)
    (Uini : Matrix (Fin (2 * L)) (Fin (2 * L)) ℂ) (i0 : Fin (2 * L)) (t : ℝ) :
    Matrix (Fin (2 * L) × Fin d) (Fin (2 * L) × Fin d) ℂ :=
  - (Uamp1 T Hm Uini t * ancillaOp (Rmat i0) * Matrix.conjTranspose (Uamp1 T Hm Uini t) *
      ancillaOp (Rmat i0) * Uamp1 T Hm Uini t)

/-- Fixed arXiv:2608.17653v1, Eq. (5.12): the boundary hopping term
`H̃_b = Σ_{(l,m)∈∂F̃} |l⟩⟨l⊕m| ⊗ H̃_m + (·)†`, where the modulo-`2L` charge
`m` of the `(row,column)` block determines whether it lies in the boundary
window `2L − l + 1 ≤ m ≤ 2L − 1`. -/
def HtildeB {d L : ℕ} (Hm : ℤ → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (2 * L) × Fin d) (Fin (2 * L) × Fin d) ℂ :=
  fun p q =>
    let n : ℤ := 2 * (L : ℤ)
    let l : ℤ := floquetIndexVal L p.1
    let l' : ℤ := floquetIndexVal L q.1
    let m : ℤ := (l' - l) % n
    let m' : ℤ := (l - l') % n
    if n - l + 1 ≤ m ∧ m ≤ n - 1 then
      Hm m p.2 q.2
    else if n - l' + 1 ≤ m' ∧ m' ≤ n - 1 then
      (Matrix.conjTranspose (Hm m')) p.2 q.2
    else 0

/-- Fixed arXiv:2608.17653v1, Eq. (5.16): the refined effective Hamiltonian
`H_eff,pbc^L = H_eff^L + H̃_b`. -/
def HeffPbc {d L : ℕ} (T : ℝ) (Hm : ℤ → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (2 * L) × Fin d) (Fin (2 * L) × Fin d) ℂ :=
  Heff T L Hm + HtildeB Hm

/-- Fixed arXiv:2608.17653v1, Eq. (5.2) with the refined Hamiltonian (5.16):
`U_amp1,pbc(t) = U_ini† e^{-it Σ lω|l⟩⟨l|} e^{-iH_eff,pbc^L t} U_ini`. -/
def Uamp1Pbc {d L : ℕ} (T : ℝ) (Hm : ℤ → Matrix (Fin d) (Fin d) ℂ)
    (Uini : Matrix (Fin (2 * L)) (Fin (2 * L)) ℂ) (t : ℝ) :
    Matrix (Fin (2 * L) × Fin d) (Fin (2 * L) × Fin d) ℂ :=
  ancillaOp (Matrix.conjTranspose Uini * diagPhase (L := L) T t * Uini) *
    timeEvol (HeffPbc T Hm) t

/-- Fixed arXiv:2608.17653v1, Eq. (5.10) with the refined Hamiltonian:
`U_amp2,pbc(t) = −U_amp1,pbc(t) R [U_amp1,pbc(t)]† R U_amp1,pbc(t)`. -/
def Uamp2Pbc {d L : ℕ} (T : ℝ) (Hm : ℤ → Matrix (Fin d) (Fin d) ℂ)
    (Uini : Matrix (Fin (2 * L)) (Fin (2 * L)) ℂ) (i0 : Fin (2 * L)) (t : ℝ) :
    Matrix (Fin (2 * L) × Fin d) (Fin (2 * L) × Fin d) ℂ :=
  - (Uamp1Pbc T Hm Uini t * ancillaOp (Rmat i0) *
      Matrix.conjTranspose (Uamp1Pbc T Hm Uini t) * ancillaOp (Rmat i0) * Uamp1Pbc T Hm Uini t)

/-- The vector `|0⟩|ψ⟩` on `D^L ⊗ ℂ^d`. -/
def ancillaVec {d L : ℕ} (i0 : Fin (2 * L)) (ψ : Vec d) :
    Fin (2 * L) × Fin d → ℂ :=
  fun p => if p.1 = i0 then ψ p.2 else 0

/-- The Euclidean norm of an amplitude vector on an arbitrary finite index
type, `‖ψ‖ = √(Σ_i ‖ψ_i‖²)` (used for the joint Floquet–system space). -/
def l2normIdx {ι : Type*} [Fintype ι] (ψ : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖ψ i‖ ^ 2)

/-- The embedding `D^{lmax} ↪ D^{4lmax}` (used in Lemma 5.1, where
`l' ∈ D^{lmax} ⊂ D^{4lmax}`). -/
def embedIndex (lmax : ℕ) (j : Fin (2 * lmax)) : Fin (2 * (4 * lmax)) :=
  ⟨(j : ℕ) + 3 * lmax, by
    have h := j.isLt
    omega⟩

end Qatlib.Papers.SlowHamSim26.Amplification
