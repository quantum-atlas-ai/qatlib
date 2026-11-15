/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.Claim322DualDecompositionStat
public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalRowsDirectCons
public import Mathlib.Tactic.FieldSimp

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.MagicDistill24.Triorthogonal
open scoped Classical BigOperators

private def sigmaLift {m n k : ℕ} (D : TriorthogonalData m n k)
    (c : Fin k → F1024) : Fin n → F1024 :=
  ∑ a, c a • mulSigmaLin D.σ (D.G (Fin.castLE D.hk a))

/-- Computes the pairing of a distinguished generator row with a sigma lift as its coefficient
times the corresponding `D.τ` value. -/
private theorem pair_sigmaLift {m n k : ℕ} (D : TriorthogonalData m n k)
    (c : Fin k → F1024) (b : Fin k) :
    triDotLin (D.G (Fin.castLE D.hk b)) (sigmaLift D c) = c b * D.τ b := by
  have hp (a : Fin k) : triDotLin (D.G (Fin.castLE D.hk b))
      (mulSigmaLin D.σ (D.G (Fin.castLE D.hk a))) = if a = b then D.τ b else 0 := by
    change (∑ i, D.G (Fin.castLE D.hk b) i * (D.σ i * D.G (Fin.castLE D.hk a) i)) = _
    calc
      _ = ∑ i, D.σ i * D.G (Fin.castLE D.hk b) i * D.G (Fin.castLE D.hk a) i :=
        Finset.sum_congr rfl (fun i _ => by ring)
      _ = _ := triPair_rows D a b
  simp [sigmaLift, map_sum, map_smul, smul_eq_mul, hp]

/-- Shows that every sigma lift lies in the dual of `triG0`. -/
private theorem sigmaLift_mem_g0dual {m n k : ℕ} (D : TriorthogonalData m n k)
    (c : Fin k → F1024) : sigmaLift D c ∈ triDual (triG0 D) := by
  apply (mem_triDual_iff _ _).mpr
  intro v hv
  change triDotLin v (sigmaLift D c) = 0
  have hp (a : Fin k) : triDotLin v (mulSigmaLin D.σ (D.G (Fin.castLE D.hk a))) = 0 := by
    change (∑ i, v i * (D.σ i * D.G (Fin.castLE D.hk a) i)) = 0
    calc
      _ = ∑ i, D.σ i * D.G (Fin.castLE D.hk a) i * v i :=
        Finset.sum_congr rfl (fun i _ => by ring)
      _ = 0 := sigma_pair_clause0 D a v hv
  simp [sigmaLift, map_sum, map_smul, smul_eq_mul, hp]

/-- Shows that every sigma lift lies in the image of `triG1` under coordinatewise sigma
multiplication. -/
private theorem sigmaLift_mem_image {m n k : ℕ} (D : TriorthogonalData m n k)
    (c : Fin k → F1024) : sigmaLift D c ∈ Submodule.map (mulSigmaLin D.σ) (triG1 D) := by
  refine ⟨∑ a, c a • D.G (Fin.castLE D.hk a), ?_, ?_⟩
  · apply Submodule.sum_mem
    intro a _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · simp [sigmaLift, map_sum, map_smul]

/-- Expresses each element of the sigma-multiplied image of `triG1` as a sigma lift. -/
private theorem image_eq_sigmaLift {m n k : ℕ} (D : TriorthogonalData m n k)
    {x : Fin n → F1024} (hx : x ∈ Submodule.map (mulSigmaLin D.σ) (triG1 D)) :
    ∃ c, x = sigmaLift D c := by
  obtain ⟨v, hv, rfl⟩ := hx
  have hv' : v ∈ triG1 D := hv
  unfold triG1 at hv'
  rw [Submodule.mem_span_range_iff_exists_fun] at hv'
  obtain ⟨c, hc⟩ := hv'
  refine ⟨c, ?_⟩
  rw [← hc]
  simp [sigmaLift, map_sum, map_smul]

/-- Shows that a vector orthogonal to every generator row lies in the dual of the generated
code. -/
private theorem dual_of_rows {m n k : ℕ} (D : TriorthogonalData m n k)
    (x : Fin n → F1024) (hx : ∀ a, triDotLin (D.G a) x = 0) : x ∈ triDual (triG D) := by
  have hker : triG D ≤ LinearMap.ker (triDotLin x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change (∑ i, x i * D.G a i) = 0
    simpa only [triDotLin, LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using hx a
  apply (mem_triDual_iff _ _).mpr
  intro v hv
  have h := hker hv
  change (∑ i, x i * v i) = 0 at h
  simpa only [mul_comm] using h

/-- Establishes the dual decomposition of Claim 3.22. -/
theorem claim322DualDecomposition : Claim322DualDecomposition := by
  intro m n k D
  have hg0 : triG0 D ≤ triG D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact row_mem_triG D _
  have hdual : triDual (triG D) ≤ triDual (triG0 D) := by
    intro x hx
    exact (mem_triDual_iff _ _).mpr fun v hv => (mem_triDual_iff _ _).mp hx v (hg0 hv)
  have himage : Submodule.map (mulSigmaLin D.σ) (triG1 D) ≤ triDual (triG0 D) := by
    intro x hx
    obtain ⟨c, rfl⟩ := image_eq_sigmaLift D hx
    exact sigmaLift_mem_g0dual D c
  constructor
  · apply le_antisymm
    · intro x hx
      let c : Fin k → F1024 := fun a => triDotLin (D.G (Fin.castLE D.hk a)) x / D.τ a
      have hrest : x - sigmaLift D c ∈ triDual (triG D) := by
        apply dual_of_rows D
        intro a
        rw [map_sub]
        by_cases ha : (a : ℕ) < k
        · let b : Fin k := ⟨a, ha⟩
          have hab : Fin.castLE D.hk b = a := Fin.ext rfl
          rw [← hab, pair_sigmaLift]
          dsimp [c]
          rw [div_mul_cancel₀ _ (D.hτ b), sub_self]
        · have ham : a ∈ Set.range (fun b : Fin (m - k) =>
              (Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m) (Fin.natAdd k b)) := by
            refine ⟨⟨(a : ℕ) - k, by omega⟩, ?_⟩
            apply Fin.ext
            simp only [Fin.val_cast, Fin.val_natAdd]
            omega
          obtain ⟨b, hb⟩ := ham
          have hrow : D.G a ∈ triG0 D := Submodule.subset_span ⟨b, congrArg D.G hb⟩
          have hx0 := (mem_triDual_iff _ _).mp hx (D.G a) hrow
          have hl0 := (mem_triDual_iff _ _).mp (sigmaLift_mem_g0dual D c) (D.G a) hrow
          change triDotLin (D.G a) x = 0 at hx0
          change triDotLin (D.G a) (sigmaLift D c) = 0 at hl0
          rw [hx0, hl0, sub_self]
      have hsum : sigmaLift D c + (x - sigmaLift D c) = x := by abel
      exact Submodule.mem_sup.mpr ⟨_, sigmaLift_mem_image D c, _, hrest, hsum⟩
    · exact sup_le himage hdual
  · apply le_antisymm
    · intro x hx
      obtain ⟨c, rfl⟩ := image_eq_sigmaLift D hx.1
      have hc (b : Fin k) : c b = 0 := by
        have h := (mem_triDual_iff _ _).mp hx.2 (D.G (Fin.castLE D.hk b))
          (row_mem_triG D _)
        change triDotLin (D.G (Fin.castLE D.hk b)) (sigmaLift D c) = 0 at h
        rw [pair_sigmaLift] at h
        exact (mul_eq_zero.mp h).resolve_right (D.hτ b)
      change sigmaLift D c = 0
      simp [sigmaLift, hc]
    · exact bot_le

end Qatlib.Papers.MagicDistill24.Triorthogonal
