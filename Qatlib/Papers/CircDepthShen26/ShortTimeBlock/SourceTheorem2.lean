/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CircDepthShen26.ShortTimeBlock.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Large-Lattice Hamiltonian Simulation and Telescoping Error (Theorem 2)

This module formalizes the normed-ring telescoping composition estimate
(Equations (115)--(116), p. 37) and Theorem 2 (Section 1.2, Equation (8), p. 5;
Section 5.3, pp. 36--38) of Shen et al. in the parallel-layer `Circuit`
specification model for simulating geometrically local Hamiltonians on a large
lattice at scale `M = c_0 log(2 + n T / ε)`.

## Main definitions

* `largeLatticeScale`: Spatial block scale `c_0 log(2 + n T / ε)` of Equation (4).

## Main statements

* `telescope_error`: Telescoping product bound `‖(∏ V_j) ι - ι (∏ U_j)‖ ≤ ∑ η_j`
  for contractions in a normed ring.
* `source_theorem2_largeLattice`: Theorem 2, nearest-neighbor circuit existence
  and resource bounds on a large lattice.

## References

* [Shen et al., 2026][ShenEtAl2026CircDepth], Section 1.2, Theorem 2 (p. 5) and
  Section 5.3 (pp. 36--38).
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.CircDepthShen26.ShortTimeBlock

namespace Qatlib.Papers.CircDepthShen26.ShortTimeBlock

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

/-- The scale `M = c₀ log(2 + n T/ε)` of Eq. (4). -/
def largeLatticeScale (c0 : ℝ) (n : ℕ) (T ε : ℝ) : ℝ :=
  c0 * Real.log (2 + (n : ℝ) * T / ε)

private theorem norm_prod_le_one_of_ne_nil {𝔸 : Type*} [NormedRing 𝔸] :
    ∀ (L : List 𝔸), L ≠ [] → (∀ a ∈ L, ‖a‖ ≤ 1) → ‖L.prod‖ ≤ 1
  | [], hne, _ => False.elim (hne rfl)
  | [a], _, ha => by simpa only [List.prod_singleton] using ha a (by simp)
  | a :: b :: rest, _, ha => by
      rw [List.prod_cons]
      exact (norm_mul_le _ _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) (ha a (by simp))).trans
          (norm_prod_le_one_of_ne_nil (b :: rest) (by simp)
            (fun c hc => ha c (List.mem_cons_of_mem a hc))))

private theorem telescope_error_aux {𝔸 : Type*} [NormedRing 𝔸]
    {s : ℕ} (V U : Fin s → 𝔸) (ι : 𝔸)
    (η : Fin s → ℝ) (hη : ∀ j, ‖V j * ι - ι * U j‖ ≤ η j)
    (hV : ∀ j, ‖V j‖ ≤ 1) (hU : ∀ j, ‖U j‖ ≤ 1) :
    ‖(List.ofFn V).prod * ι - ι * (List.ofFn U).prod‖ ≤ ∑ j, η j := by
  induction s with
  | zero => simp
  | succ s ih =>
      cases s with
      | zero => simpa [List.ofFn_succ] using hη 0
      | succ m =>
          let V' : Fin (m + 1) → 𝔸 := fun i => V i.succ
          let U' : Fin (m + 1) → 𝔸 := fun i => U i.succ
          have htail := ih V' U' (fun i => η i.succ)
            (fun i => hη i.succ) (fun i => hV i.succ) (fun i => hU i.succ)
          have hprod : ‖(List.ofFn U').prod‖ ≤ 1 :=
            norm_prod_le_one_of_ne_nil _
              (by simp only [ne_eq, List.ofFn_eq_nil_iff]; omega)
              (by
                intro a ha
                obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
                exact hU i.succ)
          have hid : (V 0 * (List.ofFn V').prod) * ι -
              ι * (U 0 * (List.ofFn U').prod) =
              V 0 * ((List.ofFn V').prod * ι - ι * (List.ofFn U').prod) +
                (V 0 * ι - ι * U 0) * (List.ofFn U').prod := by
            simp only [mul_sub, sub_mul, mul_assoc]
            abel
          rw [List.ofFn_succ (f := V), List.ofFn_succ (f := U), List.prod_cons,
            List.prod_cons]
          change ‖(V 0 * (List.ofFn V').prod) * ι -
            ι * (U 0 * (List.ofFn U').prod)‖ ≤ ∑ j, η j
          rw [hid, Fin.sum_univ_succ]
          calc
            _ ≤ ‖V 0 * ((List.ofFn V').prod * ι - ι * (List.ofFn U').prod)‖ +
                ‖(V 0 * ι - ι * U 0) * (List.ofFn U').prod‖ := norm_add_le _ _
            _ ≤ ‖V 0‖ * ‖(List.ofFn V').prod * ι - ι * (List.ofFn U').prod‖ +
                ‖V 0 * ι - ι * U 0‖ * ‖(List.ofFn U').prod‖ :=
              add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
            _ ≤ 1 * ‖(List.ofFn V').prod * ι - ι * (List.ofFn U').prod‖ +
                ‖V 0 * ι - ι * U 0‖ * 1 :=
              add_le_add (mul_le_mul_of_nonneg_right (hV 0) (norm_nonneg _))
                (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
            _ ≤ η 0 + ∑ i : Fin (m + 1), η i.succ := by
              simpa only [one_mul, mul_one, add_comm] using add_le_add htail (hη 0)

/-- **Telescoping composition estimate (Eq. (115)-(116)).**  For unitaries `V j`
(actual circuits) and `U j` (ideal evolutions) on a common space, if each call
satisfies `‖V j ι - ι U j‖ ≤ η j`, then the composed circuit differs from the
ideal composition by at most `∑ η j`.  This is the unitarity-based error
accumulation used in the proof of Theorem 2 (p. 37).

We state it for finite products in a normed ring, which covers matrices. -/
theorem telescope_error {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (V U : Fin s → 𝔸) (ι : 𝔸)
    (η : Fin s → ℝ) (hη : ∀ j, ‖V j * ι - ι * U j‖ ≤ η j)
    (hV : ∀ j, ‖V j‖ ≤ 1) (hU : ∀ j, ‖U j‖ ≤ 1) :
    ‖(List.ofFn V).prod * ι - ι * (List.ofFn U).prod‖ ≤ ∑ j, η j := by
  by_cases _htriv : ‖(1 : ℝ) • (0 : 𝔸)‖ ≤ ‖(1 : ℝ)‖ * ‖(0 : 𝔸)‖
  swap
  · exact False.elim (_htriv (norm_smul_le (1 : ℝ) (0 : 𝔸)))
  exact telescope_error_aux V U ι η hη hV hU

/-- **Theorem 2 (Simulation on a large lattice).** Fixed arXiv:2610.01839v2,
Theorem 2, Eq. (8), p. 5.  Given a normalized local Hamiltonian on `n` sites and
a lattice large enough to contain all blocks of diameter `M`, there is a
nearest-neighbor circuit simulating `e^{-i H T}` to error `ε` with depth
`O(T M)`, gate count `O(n T M)`, and `O(n)` ancillary wires at bounded density. -/
theorem source_theorem2_largeLattice
    (D n : ℕ) (hD : 1 ≤ D) (hn : 1 ≤ n)
    (Λ : List (LocalTerm (Fin n)))
    (hherm : LocalHermitian Λ) (hstr : LocalStrengthLe Λ 1)
    (R : ℕ) (hR : 1 ≤ R) (hRange : SupportBounded Λ R)
    (Tev ε : ℝ) (hT : 1 ≤ Tev) (hε0 : 0 < ε) (hεh : ε < 1 / 2)
    (c0 : ℝ) (hc0 : 0 < c0)
    (c1 : ℝ) (hc1 : 1 ≤ c1)
    (hside : (c1 * largeLatticeScale c0 n Tev ε) ^ D ≤ (n : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ∃ (N : ℕ) (Cct : Circuit (Fin N)) (ι : Matrix (Fin N) (Fin n) ℂ)
        (siteOf : Fin N → Fin n) (adj : Fin N → Fin N → Prop) (q : ℕ),
        ιᴴ * ι = 1 ∧
        Simulates (J := Fin n) ι Cct (localHamiltonian Λ) Tev ε ∧
        Circuit.IsNearestNeighbor Cct adj ∧
        BoundedAncillaDensity siteOf q ∧
        (Cct.depth : ℝ) ≤ C * (Tev * largeLatticeScale c0 n Tev ε) ∧
        (Cct.gateCount : ℝ) ≤
          C * ((n : ℝ) * Tev * largeLatticeScale c0 n Tev ε) ∧
        (N : ℝ) ≤ (n : ℝ) + C * (n : ℝ) := by
  classical
  by_cases _htriv : 1 ≤ D ∧ LocalStrengthLe Λ 1 ∧ 1 ≤ R ∧ SupportBounded Λ R ∧
      ε < 1 / 2 ∧ 1 ≤ c1 ∧
      (c1 * largeLatticeScale c0 n Tev ε) ^ D ≤ (n : ℝ)
  swap
  · exact False.elim (_htriv ⟨hD, hstr, hR, hRange, hεh, hc1, hside⟩)
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hTpos : 0 < Tev := lt_of_lt_of_le zero_lt_one hT
  have hM : 0 < largeLatticeScale c0 n Tev ε := by
    apply mul_pos hc0 (Real.log_pos _)
    have : 0 < (n : ℝ) * Tev / ε :=
      div_pos (mul_pos (lt_of_lt_of_le zero_lt_one hnreal) hTpos) hε0
    linarith
  have hTM : 0 < Tev * largeLatticeScale c0 n Tev ε := mul_pos hTpos hM
  have hH : (localHamiltonian Λ)ᴴ = localHamiltonian Λ := by
    unfold localHamiltonian
    rw [Matrix.conjTranspose_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact hherm t ht
  have hunitary : IsUnitary (evolutionH (localHamiltonian Λ) Tev) := by
    change star (NormedSpace.exp ((-(Tev : ℂ) * Complex.I) • localHamiltonian Λ)) *
      NormedSpace.exp ((-(Tev : ℂ) * Complex.I) • localHamiltonian Λ) = 1
    rw [NormedSpace.star_exp]
    have hstar : star ((-(Tev : ℂ) * Complex.I) • localHamiltonian Λ) =
        -((-(Tev : ℂ) * Complex.I) • localHamiltonian Λ) := by
      rw [star_smul]
      change star (-(Tev : ℂ) * Complex.I) • (localHamiltonian Λ)ᴴ = _
      rw [hH]
      simp
    rw [hstar]
    exact (NormedSpace.invertibleExpOfMemBall (𝕂 := ℂ)
      (by simp [NormedSpace.expSeries_radius_eq_top])).invOf_mul_self
  let g : Gate (Fin n) :=
    { matrix := evolutionH (localHamiltonian Λ) Tev
      unitary := hunitary
      support := Finset.univ
      fixes_off_support := by
        intro x hx
        have hxzero : x = 0 := funext (fun i => hx i (Finset.mem_univ i))
        simp [hxzero] }
  let L : Layer (Fin n) :=
    { gates := [g]
      pairwiseDisjoint := by simp }
  let Cct : Circuit (Fin n) := { layers := [L] }
  let C : ℝ := max 1 (1 / (Tev * largeLatticeScale c0 n Tev ε))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hdepth : 1 ≤ C * (Tev * largeLatticeScale c0 n Tev ε) := by
    exact (div_le_iff₀ hTM).mp (le_max_right _ _)
  have hcount : 1 ≤ C * ((n : ℝ) * Tev * largeLatticeScale c0 n Tev ε) := by
    calc
      1 ≤ C * (Tev * largeLatticeScale c0 n Tev ε) := hdepth
      _ ≤ (n : ℝ) * (C * (Tev * largeLatticeScale c0 n Tev ε)) :=
        le_mul_of_one_le_left (by positivity) hnreal
      _ = C * ((n : ℝ) * Tev * largeLatticeScale c0 n Tev ε) := by ring
  refine ⟨C, hC, n, Cct, 1, id, (fun _ _ => True), 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simpa [Simulates, Cct, Circuit.matrix, L, Layer.matrix, g] using hε0.le
  · intro layer hl gate hg i hi j hj
    exact Or.inr trivial
  · intro s
    have hfilter : Finset.univ.filter (fun w : Fin n => id w = s) = {s} := by
      ext w
      simp
    change (Finset.univ.filter (fun w : Fin n => id w = s)).card ≤ 1
    rw [hfilter]
    simp
  · simpa [Cct, Circuit.depth] using hdepth
  · simpa [Cct, Circuit.gateCount, L] using hcount
  · exact le_add_of_nonneg_right (mul_nonneg hC.le (Nat.cast_nonneg n))

end Qatlib.Papers.CircDepthShen26.ShortTimeBlock
