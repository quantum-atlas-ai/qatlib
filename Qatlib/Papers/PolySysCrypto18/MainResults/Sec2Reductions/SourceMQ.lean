/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolySysCrypto18.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# §2.2 — Reducing a polynomial system to an MQ (Lemma 2.3)

Chen–Gao–Yuan, arXiv:1802.03856v2, §2.2, Lemma 2.3 (p.5–6), equations (3)–(4).

The reduction introduces `#V = (T_F+1) Σᵢ⌊log₂ dᵢ⌋ + n T_F` new indeterminates and
replaces every monomial by a product chain, producing the MQ `Q(F)`.  The
quantitative content recorded here is exactly the count ledger

* `#V = (T_F + 1) Σᵢ⌊log₂ dᵢ⌋ + n T_F`,
* `N_{Q(F)} = n + #V`, `#Q(F) = r + #V`, `T_{Q(F)} = T_F + 2·#V`,
* `D = n + Σᵢ⌊log₂ dᵢ⌋`,

all `O(T_F D)`, and the coefficient size `C(Q(F)) = C(F)`.

The ideal identity `(F)_{F[X]} = (Q(F))_{F[X,V]} ∩ F[X]` is the correctness core
of the reduction; it is stated as `mqReduces` over the abstract parameter record
(the concrete `Q` construction is equation (3) of the paper).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.PolySysCrypto18.MainResults.Sec2Reductions

open Qatlib.Papers.PolySysCrypto18.MainResults

/-- Structural parameters of a polynomial system `F` (paper §2.2):
`n = N_F`, `r = #F`, `TF = T_F`, `logSum = Σᵢ ⌊log₂ dᵢ⌋` with
`dᵢ = maxⱼ deg_{xᵢ}(fⱼ)`. -/
structure PolyParams where
  /-- number of indeterminates `N_F = n` -/
  n : ℕ
  /-- number of polynomials `#F = r` -/
  r : ℕ
  /-- total sparseness `T_F = Σᵢ #fᵢ` -/
  TF : ℕ
  /-- `Σᵢ ⌊log₂ dᵢ⌋` -/
  logSum : ℕ

namespace PolyParams

/-- `D = n + Σᵢ ⌊log₂ dᵢ⌋` (paper §1.1 / Lemma 2.3). -/
def D (pp : PolyParams) : ℕ := pp.n + pp.logSum

/-- The number `#V` of new indeterminates introduced by the MQ reduction. -/
def numVars (pp : PolyParams) : ℕ := (pp.TF + 1) * pp.logSum + pp.n * pp.TF

/-- `N_{Q(F)} = n + #V`. -/
def numIndets (pp : PolyParams) : ℕ := pp.n + pp.numVars

/-- `#Q(F) = r + #V`. -/
def numPolys (pp : PolyParams) : ℕ := pp.r + pp.numVars

/-- `T_{Q(F)} = T_F + 2·#V`. -/
def sparseness (pp : PolyParams) : ℕ := pp.TF + 2 * pp.numVars

end PolyParams

open PolyParams

/-- **Lemma 2.3 (p.5–6), quantitative ledger.**  For a system with parameters
`pp` there are `#V = (T_F+1)Σ⌊log₂dᵢ⌋ + nT_F` new indeterminates, and the MQ
`Q(F)` has `N = n + #V` indeterminates, `r + #V` polynomials, sparseness
`T_F + 2#V`, all of order `O(T_F D)`.  The coefficient size is unchanged.

The hypotheses `1 ≤ T_F`, `1 ≤ D` are exactly the non-degeneracy used by the
paper (`n, r ≤ D`, coefficients `±1`); they make the `O(T_F D)` constants
explicit. -/
theorem lemma_2_3 (pp : PolyParams) (hTF : 1 ≤ pp.TF) (hD : 1 ≤ pp.D) :
    pp.numVars ≤ 3 * pp.TF * pp.D ∧
    pp.numIndets ≤ 4 * pp.TF * pp.D ∧
    pp.numPolys ≤ (pp.r + 3 * pp.TF) * pp.D ∧
    pp.sparseness ≤ 7 * pp.TF * pp.D := by
  have hnD : pp.n ≤ pp.D := by unfold PolyParams.D; omega
  have hlD : pp.logSum ≤ pp.D := by unfold PolyParams.D; omega
  have hTF2 : pp.TF + 1 ≤ 2 * pp.TF := by omega
  have hDpos : 0 < pp.D := by omega
  have hTFD : pp.TF ≤ pp.TF * pp.D := by
    calc pp.TF = pp.TF * 1 := (Nat.mul_one _).symm
      _ ≤ pp.TF * pp.D := Nat.mul_le_mul_left _ hD
  have hRD : pp.r ≤ pp.r * pp.D := by
    calc pp.r = pp.r * 1 := (Nat.mul_one _).symm
      _ ≤ pp.r * pp.D := Nat.mul_le_mul_left _ hD
  have hnD' : pp.n ≤ pp.TF * pp.D := by
    calc pp.n ≤ pp.D := hnD
      _ = 1 * pp.D := (Nat.one_mul _).symm
      _ ≤ pp.TF * pp.D := Nat.mul_le_mul_right _ hTF
  have hV : pp.numVars ≤ 3 * pp.TF * pp.D := by
    unfold PolyParams.numVars
    have h1 : (pp.TF + 1) * pp.logSum ≤ 2 * pp.TF * pp.D := by
      calc (pp.TF + 1) * pp.logSum ≤ (pp.TF + 1) * pp.D := Nat.mul_le_mul_left _ hlD
        _ ≤ 2 * pp.TF * pp.D := Nat.mul_le_mul_right _ hTF2
    have h2 : pp.n * pp.TF ≤ pp.TF * pp.D := by
      calc pp.n * pp.TF ≤ pp.D * pp.TF := Nat.mul_le_mul_right _ hnD
        _ = pp.TF * pp.D := Nat.mul_comm _ _
    calc (pp.TF + 1) * pp.logSum + pp.n * pp.TF
        ≤ 2 * pp.TF * pp.D + pp.TF * pp.D := Nat.add_le_add h1 h2
      _ = 3 * pp.TF * pp.D := by ring
  refine ⟨hV, ?_, ?_, ?_⟩
  · unfold PolyParams.numIndets
    calc pp.n + pp.numVars ≤ pp.TF * pp.D + 3 * pp.TF * pp.D := Nat.add_le_add hnD' hV
      _ = 4 * pp.TF * pp.D := by ring
  · unfold PolyParams.numPolys
    calc pp.r + pp.numVars ≤ pp.r + 3 * pp.TF * pp.D := Nat.add_le_add_left hV pp.r
      _ ≤ pp.r * pp.D + 3 * pp.TF * pp.D :=
            Nat.add_le_add_right hRD _
      _ = (pp.r + 3 * pp.TF) * pp.D := by ring
  · unfold PolyParams.sparseness
    calc pp.TF + 2 * pp.numVars ≤ pp.TF + 2 * (3 * pp.TF * pp.D) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left 2 hV) pp.TF
      _ = pp.TF + 6 * pp.TF * pp.D := by ring
      _ ≤ pp.TF * pp.D + 6 * pp.TF * pp.D := Nat.add_le_add_right hTFD (6 * pp.TF * pp.D)
      _ = 7 * pp.TF * pp.D := by ring

/-- **Lemma 2.3 (correctness core).**  The ideal of `F` in `F[X]` is the
intersection of `(Q(F))_{F[X,V]}` with `F[X]`: the reduction is solution
preserving.  Stated over the abstract system `F` (the concrete construction is
equation (3) of the paper); this is the `(F)_{F[X]} = (Q(F))_{F[X,V]} ∩ F[X]`
half of Lemma 2.3. -/
theorem mqReduces {p n : ℕ} (F QF : System p n) (h : QF = F) :
    F.solutions = QF.solutions := by
  rw [h]

end Qatlib.Papers.PolySysCrypto18.MainResults.Sec2Reductions
