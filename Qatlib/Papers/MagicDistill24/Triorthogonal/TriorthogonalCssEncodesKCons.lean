/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalRowsDirectCons
public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalCssEncodesKStat

@[expose] public section

namespace Qatlib.Papers.MagicDistill24.Triorthogonal

open Matrix

/-- Shows that every element of `F1024` added to itself is zero. -/
private theorem char2_add_self (a : F1024) : a + a = 0 := by
  have h : (2 : F1024) = 0 := CharTwo.two_eq_zero
  linear_combination h * a

/-- Cancels two occurrences of the same summand in `F1024`. -/
private theorem char2_add_add_cancel (a b : F1024) : a + (b + a) = b := by
  have h : (2 : F1024) = 0 := CharTwo.two_eq_zero
  linear_combination h * a

/-- Shows that two elements of `F1024` summing to zero are equal. -/
private theorem char2_eq_of_add_eq_zero {a b : F1024} (h : a + b = 0) : b = a := by
  have hba : b + a = 0 := by rw [add_comm]; exact h
  calc b = 0 + b := (zero_add b).symm
    _ = (b + a) + b := by rw [hba]
    _ = a + (b + b) := by ring
    _ = a + 0 := by rw [char2_add_self]
    _ = a := add_zero a

/-- Shows that translating a vector twice by the same vector gives the original vector. -/
private theorem char2_shift_shift {n : ℕ} (x v : Fin n → F1024) :
    (x + v) + v = x := by
  funext i
  rw [Pi.add_apply, Pi.add_apply, add_assoc, char2_add_self (v i), add_zero]

/-- Shows that every element of `ZMod 2` is zero or one. -/
private theorem zmod2_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  have hlt : b.val < 2 := b.isLt
  have h : b.val = 0 ∨ b.val = 1 := by omega
  rcases h with h | h
  · left
    have h0 : b.val = (0 : ZMod 2).val := by rw [ZMod.val_zero]; exact h
    exact ZMod.val_injective 2 h0
  · right
    have h0 : b.val = (1 : ZMod 2).val := by rw [ZMod.val_one]; exact h
    exact ZMod.val_injective 2 h0

/-- Produces an element of `F1024` with trace one. -/
private theorem exists_trace_one : ∃ t₀ : F1024, f1024Trace t₀ = 1 := by
  by_contra hcon
  have hzero : ∀ b : F1024, f1024Trace b = 0 := by
    intro b
    rcases zmod2_cases (f1024Trace b) with h | h
    · exact h
    · exact absurd h (fun hc => hcon ⟨b, hc⟩)
  have h1 : (1 : F1024) = 0 :=
    (traceForm_nondegenerate (ZMod 2) F1024).1 1 (fun y => by
      rw [Algebra.traceForm_apply, one_mul]
      exact hzero y)
  exact one_ne_zero h1

private noncomputable def toDualMap {n : ℕ} (S : Submodule F1024 (Fin n → F1024)) :
    (Fin n → F1024) →ₗ[F1024] (S →ₗ[F1024] F1024) where
  toFun y := (triDotLin y).comp (Submodule.subtype S)
  map_add' y z := by
    ext s
    show (∑ x, (y x + z x) * (s : Fin n → F1024) x)
        = (∑ i, y i * (s : Fin n → F1024) i) + ∑ i, z i * (s : Fin n → F1024) i
    rw [← Finset.sum_add_distrib (M := F1024)]
    exact Finset.sum_congr (M := F1024) rfl fun i _ => by ring
  map_smul' c y := by
    ext s
    show (∑ x, c * y x * (s : Fin n → F1024) x)
        = c * (∑ i, y i * (s : Fin n → F1024) i)
    rw [Finset.sum_congr (M := F1024) rfl fun i _ =>
        mul_assoc c (y i) ((s : Fin n → F1024) i), ← Finset.mul_sum (R := F1024)]

/-- Identifies the kernel of `toDualMap` with the orthogonal dual submodule. -/
private theorem ker_toDualMap {n : ℕ} (S : Submodule F1024 (Fin n → F1024)) :
    LinearMap.ker (toDualMap S) = triDual S := by
  apply Submodule.ext
  intro y
  rw [LinearMap.mem_ker, mem_triDual_iff]
  constructor
  · intro h x hx
    have h1 := congrArg (fun (T : S →ₗ[F1024] F1024) => T ⟨x, hx⟩) h
    simp only [LinearMap.zero_apply] at h1
    have h2 : (∑ i, y i * x i) = 0 := h1
    rw [Finset.sum_congr (M := F1024) rfl fun i _ => mul_comm (x i) (y i)]
    exact h2
  · intro h
    ext s
    show (∑ i, y i * (s : Fin n → F1024) i) = (0 : F1024)
    rw [Finset.sum_congr (M := F1024) rfl fun i _ => mul_comm (y i) ((s : Fin n → F1024) i)]
    exact h (s : Fin n → F1024) s.2

/-- Shows that `toDualMap` is surjective. -/
private theorem toDualMap_surjective {n : ℕ} (S : Submodule F1024 (Fin n → F1024)) :
    Function.Surjective (toDualMap S) := by
  intro φ
  obtain ⟨g, hg⟩ := LinearMap.exists_extend φ
  refine ⟨fun i => g (fun j => if i = j then (1 : F1024) else 0), ?_⟩
  ext s
  have hexp : (s : Fin n → F1024)
      = ∑ i, (s : Fin n → F1024) i • (fun j => if i = j then (1 : F1024) else 0) :=
    pi_eq_sum_univ (s : Fin n → F1024)
  have hL : ∑ i, (g (fun j => if i = j then (1 : F1024) else 0))
        * (s : Fin n → F1024) i
      = g (s : Fin n → F1024) := by
    rw [show g (s : Fin n → F1024)
        = g (∑ i, (s : Fin n → F1024) i • (fun j => if i = j then (1 : F1024) else 0))
        from congrArg g hexp, map_sum]
    refine Finset.sum_congr (M := F1024) rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  show ∑ i, (g (fun j => if i = j then (1 : F1024) else 0))
      * (s : Fin n → F1024) i = φ s
  rw [hL]
  have hgs := LinearMap.congr_fun hg s
  simp only [LinearMap.comp_apply, Submodule.coe_subtype] at hgs
  exact hgs

/-- Shows that a submodule's dimension plus its orthogonal dual's dimension equals the ambient
dimension. -/
private theorem finrank_add_finrank_dual {n : ℕ}
    (S : Submodule F1024 (Fin n → F1024)) :
    Module.finrank F1024 ↥S + Module.finrank F1024 (triDual S) = n := by
  have hrange := LinearMap.finrank_range_add_finrank_ker (toDualMap S)
  have hdim : Module.finrank F1024 (Fin n → F1024) = n := Module.finrank_fin_fun F1024
  have hker := ker_toDualMap S
  rw [hdim, hker] at hrange
  have hsurj : LinearMap.range (toDualMap S) = ⊤ :=
    LinearMap.range_eq_top.2 (toDualMap_surjective S)
  rw [hsurj] at hrange
  rw [finrank_top, Subspace.dual_finrank_eq] at hrange
  exact hrange

/-- Shows that a submodule is contained in its double orthogonal dual. -/
private theorem le_dual_dual {n : ℕ} (S : Submodule F1024 (Fin n → F1024)) :
    S ≤ triDual (triDual S) := by
  intro x hx
  rw [mem_triDual_iff]
  intro y hy
  have h0 : ∀ z ∈ S, ∑ i, z i * y i = 0 := mem_triDual_iff S y |>.mp hy
  rw [Finset.sum_congr (M := F1024) rfl fun i _ => mul_comm (y i) (x i)]
  exact h0 x hx

/-- Shows that taking the orthogonal dual twice recovers the submodule. -/
private theorem dual_dual_eq {n : ℕ} (S : Submodule F1024 (Fin n → F1024)) :
    triDual (triDual S) = S := by
  refine (Submodule.eq_of_le_of_finrank_eq (le_dual_dual S) ?_).symm
  have h1 := finrank_add_finrank_dual S
  have h2 := finrank_add_finrank_dual (triDual S)
  omega

/-- Separates a vector outside a submodule by a dual vector whose pairing has trace one. -/
private theorem exists_dual_trace_one {n : ℕ} (S : Submodule F1024 (Fin n → F1024))
    {x : Fin n → F1024} (hx : x ∉ S) :
    ∃ w ∈ triDual S, f1024Trace (∑ i, w i * x i) = 1 := by
  obtain ⟨t₀, ht₀⟩ := exists_trace_one
  have hnd : x ∉ triDual (triDual S) := by
    intro hcon
    apply hx
    rw [← dual_dual_eq S]
    exact hcon
  obtain ⟨y, hydual, hne⟩ : ∃ y ∈ triDual S, ∑ i, y i * x i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hnd (mem_triDual_iff (triDual S) x |>.mpr hcon)
  refine ⟨(((∑ i, y i * x i)⁻¹) * t₀) • y, Submodule.smul_mem _ _ hydual, ?_⟩
  have hsum : ∑ i, (((∑ i, y i * x i)⁻¹ * t₀) • y) i * x i
      = (∑ i, y i * x i)⁻¹ * t₀ * ∑ i, y i * x i := by
    have h1 : ∀ i : Fin n, (((∑ i, y i * x i)⁻¹ * t₀) • y) i * x i
        = (∑ i, y i * x i)⁻¹ * t₀ * (y i * x i) := by
      intro i
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr (M := F1024) rfl fun i _ => h1 i, ← Finset.mul_sum (R := F1024)]
  rw [hsum, show (∑ i, y i * x i)⁻¹ * t₀ * ∑ i, y i * x i = t₀ from by
      rw [mul_assoc, mul_comm t₀, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]]
  exact ht₀

/-- Computes the action of a vector qudit X operator as translation of state coordinates. -/
private theorem xVec_mulVec {n : ℕ} (v : Fin n → F1024)
    (ψ : (Fin n → F1024) → ℂ) (x : Fin n → F1024) :
    (quditXVec v *ᵥ ψ) x = ψ (x + v) := by
  have hterm : ∀ y : Fin n → F1024,
      (if x = y + v then (1 : ℂ) else 0) * ψ y
        = if y = x + v then ψ y else 0 := by
    intro y
    by_cases hy : y = x + v
    · rw [ite_eq_left (by rw [hy, char2_shift_shift]), ite_eq_left hy]
      ring
    · rw [ite_eq_right (fun hc => hy (by
          have h2 : y + v = x := by rw [← hc]
          calc y = (y + v) + v := (char2_shift_shift y v).symm
            _ = x + v := by rw [h2]
        )), ite_eq_right hy]
      ring
  simp only [Matrix.mulVec, dotProduct, quditXVec, Matrix.of_apply]
  rw [Finset.sum_congr (M := ℂ) rfl fun y _ => hterm y]
  simp

/-- Computes the action of a vector qudit Z operator as multiplication by its trace phase. -/
private theorem zVec_mulVec {n : ℕ} (w : Fin n → F1024)
    (ψ : (Fin n → F1024) → ℂ) (x : Fin n → F1024) :
    (quditZVec w *ᵥ ψ) x = qPhase (∑ i, f1024Trace (w i * x i)) * ψ x := by
  simp only [Matrix.mulVec, dotProduct, quditZVec,
    Matrix.diagonal_apply]
  rw [Finset.sum_eq_single x]
  · rw [ite_eq_left rfl]
  · intro y _ hyx
    rw [ite_eq_right (fun hc => hyx hc.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- Characterizes codespace membership by invariance under the specified X and Z stabilizers. -/
private theorem mem_codespace_iff {m n k : ℕ} (D : TriorthogonalData m n k)
    (ψ : (Fin n → F1024) → ℂ) :
    ψ ∈ triCodespace D ↔ ((∀ v ∈ triG0 D, (quditXVec v).mulVecLin ψ = ψ)
      ∧ ∀ w ∈ triDual (triG D), (quditZVec w).mulVecLin ψ = ψ) := by
  simp only [triCodespace, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  exact ⟨fun h => ⟨fun v hv => sub_eq_zero.mp (h.1 v hv),
      fun w hw => sub_eq_zero.mp (h.2 w hw)⟩,
    fun h => ⟨fun v hv => sub_eq_zero.mpr (h.1 v hv),
      fun w hw => sub_eq_zero.mpr (h.2 w hw)⟩⟩

private noncomputable def rVec {m n k : ℕ} (D : TriorthogonalData m n k)
    (u : Fin k → F1024) : Fin n → F1024 :=
  fun i => ∑ a, u a * D.G (Fin.castLE D.hk a) i

/-- Characterizes coset membership by translation into `triG0` using the logical representative. -/
private theorem mem_triCoset_iff' {m n k : ℕ} (D : TriorthogonalData m n k)
    (u : Fin k → F1024) (x : Fin n → F1024) :
    x ∈ triCoset D u ↔ x + rVec D u ∈ triG0 D := by
  constructor
  · rintro ⟨g, hg, hxg⟩
    have hfun : x + rVec D u = g := by
      funext i
      have h2 : x i = (∑ a, u a * D.G (Fin.castLE D.hk a) i) + g i := by
        have hbeta := congrFun hxg i
        simp only at hbeta
        exact hbeta.symm
      simp only [Pi.add_apply, rVec, h2]
      calc (∑ a, u a * D.G (Fin.castLE D.hk a) i) + g i
            + (∑ a, u a * D.G (Fin.castLE D.hk a) i)
          = (∑ a, u a * D.G (Fin.castLE D.hk a) i)
              + (g i + ∑ a, u a * D.G (Fin.castLE D.hk a) i) := add_assoc _ _ _
        _ = g i := char2_add_add_cancel _ _
    rw [hfun]
    exact hg
  · intro h
    refine ⟨x + rVec D u, h, ?_⟩
    funext i
    simp only [Pi.add_apply, rVec]
    calc (∑ a, u a * D.G (Fin.castLE D.hk a) i) + (x i
            + ∑ a, u a * D.G (Fin.castLE D.hk a) i)
        = x i + ((∑ a, u a * D.G (Fin.castLE D.hk a) i)
            + ∑ a, u a * D.G (Fin.castLE D.hk a) i) := by ring
      _ = x i + 0 := by rw [char2_add_self]
      _ = x i := add_zero _

/-- Exchanges the coordinate pairing with a finite linear combination of rows. -/
private theorem swap_dot {n : ℕ} {ι : Type} [Fintype ι] (w : Fin n → F1024)
    (c : ι → F1024) (R : ι → Fin n → F1024) :
    (∑ i, w i * (∑ t, c t * R t i)) = ∑ t, c t * (∑ i, w i * R t i) := by
  have h1 : ∀ i : Fin n, w i * (∑ t, c t * R t i)
      = ∑ t, w i * (c t * R t i) := by
    intro i
    rw [Finset.mul_sum (R := F1024)]
  rw [Finset.sum_congr (M := F1024) rfl fun i _ => h1 i,
    Finset.sum_comm (β := F1024)]
  exact Finset.sum_congr (M := F1024) rfl fun t _ => by
    rw [Finset.mul_sum (R := F1024)]
    exact Finset.sum_congr (M := F1024) rfl fun i _ => by ring

/-- Shows that every triorthogonal codeword belongs to the codespace. -/
private theorem codeword_mem_codespace {m n k : ℕ} (D : TriorthogonalData m n k)
    (u : Fin k → F1024) :
    triCodeword D u ∈ triCodespace D := by
  rw [mem_codespace_iff]
  constructor
  · intro v hv
    funext x
    show (quditXVec v *ᵥ triCodeword D u) x = triCodeword D u x
    rw [xVec_mulVec]
    by_cases hx : x ∈ triCoset D u
    · have hv' : x + v ∈ triCoset D u := by
        rw [mem_triCoset_iff']
        have h0 : x + rVec D u + v ∈ triG0 D :=
          Submodule.add_mem _ (mem_triCoset_iff' D u x |>.mp hx) hv
        have hcomm : x + v + rVec D u = x + rVec D u + v := by
          funext i
          simp only [Pi.add_apply]
          ring
        rw [hcomm]
        exact h0
      rw [triCodeword, Set.indicator_of_mem hx, Set.indicator_of_mem hv']
    · have hv' : x + v ∉ triCoset D u := by
        intro hcon
        apply hx
        rw [mem_triCoset_iff']
        have hc : x + v + rVec D u ∈ triG0 D := mem_triCoset_iff' D u (x + v) |>.mp hcon
        have h0 : x + rVec D u + v ∈ triG0 D := by
          rw [show x + rVec D u + v = x + v + rVec D u from by
            funext i
            simp only [Pi.add_apply]
            ring]
          exact hc
        have hshift : (x + rVec D u + v) + v = x + rVec D u := by
          funext i
          simp only [Pi.add_apply]
          rw [add_assoc, char2_add_self (v i), add_zero]
        have hmem2 : (x + rVec D u + v) + v ∈ triG0 D := Submodule.add_mem _ h0 hv
        rw [← hshift]
        exact hmem2
      rw [triCodeword, Set.indicator, ite_eq_right hv', Set.indicator, ite_eq_right hx]
  · intro w hw
    funext x
    show (quditZVec w *ᵥ triCodeword D u) x = triCodeword D u x
    rw [zVec_mulVec]
    by_cases hx : x ∈ triCoset D u
    · rw [triCodeword, Set.indicator_of_mem hx, mul_one]
      obtain ⟨d, hd⟩ := mem_triG0_iff D (x + rVec D u) |>.mp
        (mem_triCoset_iff' D u x |>.mp hx)
      have hdec : ∀ i : Fin n, x i = rVec D u i
          + ∑ a', d a' * clause0Row D a' i := by
        intro i
        have h1 := hd i
        simp only [Pi.add_apply, rVec] at h1
        rw [← h1]
        exact (char2_add_add_cancel _ (x i)).symm
      have hdot : ∑ i, w i * x i = 0 := by
        rw [Finset.sum_congr (M := F1024) rfl fun i _ => by
          rw [hdec i, mul_add], Finset.sum_add_distrib (M := F1024)]
        simp only [rVec]
        have hg0 : ∀ a' : Fin (m - k), clause0Row D a' ∈ triG D := fun a' =>
          Submodule.subset_span ⟨(Fin.cast (by have hk := D.hk; omega) :
            Fin (k + (m - k)) → Fin m) (Fin.natAdd k a'), rfl⟩
        have hA : (∑ i : Fin n, w i * ∑ a : Fin k, u a * D.G (Fin.castLE D.hk a) i)
            = 0 := by
          rw [swap_dot]
          exact Finset.sum_eq_zero fun a _ => by
            rw [Finset.sum_congr (M := F1024) rfl fun i _ => mul_comm (w i)
                (D.G (Fin.castLE D.hk a) i),
              dot_eq_zero_of_mem_dual D hw (row_mem_triG D (Fin.castLE D.hk a)), mul_zero]
        have hB : (∑ i : Fin n, w i * ∑ a' : Fin (m - k), d a' * clause0Row D a' i) = 0 := by
          rw [swap_dot]
          exact Finset.sum_eq_zero fun a' _ => by
            rw [Finset.sum_congr (M := F1024) rfl fun i _ => mul_comm (w i) (clause0Row D a' i),
              dot_eq_zero_of_mem_dual D hw (hg0 a'), mul_zero]
        rw [hA, hB, add_zero]
      have hphase : ∑ i, f1024Trace (w i * x i) = 0 := by
        have h1 : ∑ i, f1024Trace (w i * x i) = f1024Trace (∑ i, w i * x i) :=
          (map_sum (Algebra.trace (ZMod 2) F1024) (fun i => w i * x i) Finset.univ).symm
        rw [h1, hdot]
        exact map_zero (Algebra.trace (ZMod 2) F1024)
      rw [hphase, qPhase_zero]
    · rw [triCodeword, Set.indicator, ite_eq_right hx, mul_zero]

/-- Shows that a codespace state vanishes outside `triG`. -/
private theorem support_in_G {m n k : ℕ} (D : TriorthogonalData m n k)
    (ψ : (Fin n → F1024) → ℂ) (hψ : ψ ∈ triCodespace D)
    {x : Fin n → F1024} (hx : x ∉ triG D) : ψ x = 0 := by
  rw [mem_codespace_iff] at hψ
  obtain ⟨w, hw, htr⟩ := exists_dual_trace_one (triG D) hx
  have hmem : quditZVec w *ᵥ ψ = ψ := hψ.2 w hw
  have hval := congrFun hmem x
  rw [zVec_mulVec] at hval
  have h1 : ∑ i, f1024Trace (w i * x i) = 1 := by
    have h2 : ∑ i, f1024Trace (w i * x i) = f1024Trace (∑ i, w i * x i) :=
      (map_sum (Algebra.trace (ZMod 2) F1024) (fun i => w i * x i) Finset.univ).symm
    rw [h2]
    exact htr
  rw [h1, qPhase_one] at hval
  have h2 : ψ x + ψ x = 0 := by linear_combination -hval
  have h3 : (2 : ℂ) * ψ x = 0 := by rw [two_mul]; exact h2
  exact (mul_eq_zero.mp h3).resolve_left (by norm_num)

/-- Expresses `triG` as the sum of its distinguished-row and clause-zero subspaces. -/
private theorem triG_eq_sup {m n k : ℕ} (D : TriorthogonalData m n k) :
    triG D = triG1 D ⊔ triG0 D := by
  refine le_antisymm ?_ ?_
  · rw [triG, triRowSpace]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨t, rfl⟩
    rcases Nat.lt_or_ge (t : ℕ) k with hlt | hge
    · refine Submodule.mem_sup_left ?_
      have he : Fin.castLE D.hk ⟨(t : ℕ), hlt⟩ = t := Fin.ext rfl
      exact Submodule.subset_span ⟨(⟨(t : ℕ), hlt⟩ : Fin k), congrArg D.G he⟩
    · refine Submodule.mem_sup_right ?_
      have he : (Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
          (Fin.natAdd k ⟨(t : ℕ) - k, by omega⟩) = t :=
        Fin.ext (by simp only [Fin.val_natAdd, Fin.val_cast]; omega)
      exact Submodule.subset_span ⟨(⟨(t : ℕ) - k, by omega⟩ : Fin (m - k)),
        congrArg D.G he⟩
  · refine sup_le ?_ ?_
    · unfold triG1 triG
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨Fin.castLE D.hk a, rfl⟩
    · unfold triG0 triG
      rw [Submodule.span_le]
      rintro _ ⟨a', rfl⟩
      exact Submodule.subset_span ⟨(Fin.cast (by have hk := D.hk; omega) :
        Fin (k + (m - k)) → Fin m) (Fin.natAdd k a'), rfl⟩

/-- Characterizes membership in `triG1` by a linear combination of its distinguished generator
rows. -/
private theorem mem_triG1_iff' {m n k : ℕ} (D : TriorthogonalData m n k)
    (v : Fin n → F1024) :
    v ∈ triG1 D ↔ ∃ c : Fin k → F1024,
      ∀ i, v i = ∑ a, c a * D.G (Fin.castLE D.hk a) i := by
  constructor
  · intro hv
    have h := hv
    unfold triG1 at h
    rw [Submodule.mem_span_range_iff_exists_fun] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, fun i => by
      have hci := congrFun hc i
      simpa [Finset.sum_apply] using hci.symm⟩
  · rintro ⟨c, hc⟩
    unfold triG1
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨c, funext fun i => ?_⟩
    have := hc i
    simpa [Finset.sum_apply] using this.symm

/-- Shows that every element of `triG` belongs to a logical coset. -/
private theorem exists_coset {m n k : ℕ} (D : TriorthogonalData m n k)
    {x : Fin n → F1024} (hx : x ∈ triG D) :
    ∃ u : Fin k → F1024, x ∈ triCoset D u := by
  rw [triG_eq_sup D] at hx
  obtain ⟨g1, hg1, g0, hg0, hfg⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc⟩ := (mem_triG1_iff' D g1).mp hg1
  refine ⟨c, mem_triCoset_iff' D c x |>.mpr ?_⟩
  have hgoal0 := hg0
  have hr : rVec D c = g1 := by
    funext i
    simp only [rVec]
    exact (hc i).symm
  have hgoal : x + g1 = g0 := by
    funext i
    have hfgi := congrFun hfg i
    simp only [Pi.add_apply] at hfgi
    simp only [Pi.add_apply]
    rw [← hfgi, add_assoc]
    exact char2_add_add_cancel _ _
  rw [hr, hgoal]
  exact hg0

/-- Shows that logical coset labels are unique for a common member. -/
private theorem coset_unique {m n k : ℕ} (D : TriorthogonalData m n k)
    {x : Fin n → F1024} {u u' : Fin k → F1024}
    (h : x ∈ triCoset D u) (h' : x ∈ triCoset D u') : u = u' := by
  have h1 : x + rVec D u ∈ triG0 D := mem_triCoset_iff' D u x |>.mp h
  have h2 : x + rVec D u' ∈ triG0 D := mem_triCoset_iff' D u' x |>.mp h'
  have hsum : rVec D u + rVec D u' ∈ triG0 D := by
    have hEq : (x + rVec D u) + (x + rVec D u') = rVec D u + rVec D u' := by
      funext i
      simp only [Pi.add_apply]
      have h2 : (2 : F1024) = 0 := CharTwo.two_eq_zero
      linear_combination h2 * x i
    rw [← hEq]
    exact Submodule.add_mem _ h1 h2
  have hmem1 : rVec D u + rVec D u' ∈ triG1 D := by
    have m1 : rVec D u ∈ triG1 D := mem_triG1_iff' D (rVec D u) |>.mpr ⟨u, fun _ => rfl⟩
    have m2 : rVec D u' ∈ triG1 D := mem_triG1_iff' D (rVec D u') |>.mpr ⟨u', fun _ => rfl⟩
    exact Submodule.add_mem _ m1 m2
  have h0 : rVec D u + rVec D u' = 0 := by
    have hinf : rVec D u + rVec D u' ∈ triG1 D ⊓ triG0 D :=
      Submodule.mem_inf.mpr ⟨hmem1, hsum⟩
    rw [clause1_inf_clause0 D, Submodule.mem_bot] at hinf
    exact hinf
  have hfun : (∑ a, (u a + u' a) • D.G (Fin.castLE D.hk a)) = 0 := by
    funext i
    have h0i := congrFun h0 i
    simp only [Pi.add_apply, rVec] at h0i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc (∑ a, (u a + u' a) * D.G (Fin.castLE D.hk a) i)
        = (∑ a, u a * D.G (Fin.castLE D.hk a) i)
            + ∑ a, u' a * D.G (Fin.castLE D.hk a) i := by
          rw [← Finset.sum_add_distrib (M := F1024)]
          exact Finset.sum_congr (M := F1024) rfl fun a _ => by ring
      _ = 0 := h0i
  have hu0 := clause1_rows_indep D (fun a => u a + u' a) hfun
  funext a
  exact (char2_eq_of_add_eq_zero (hu0 a)).symm

/-- Shows that each logical coset is contained in `triG`. -/
private theorem coset_subset_G {m n k : ℕ} (D : TriorthogonalData m n k)
    {u : Fin k → F1024} {x : Fin n → F1024} (h : x ∈ triCoset D u) :
    x ∈ triG D := by
  have hG1 : triG1 D ≤ triG D := by rw [triG_eq_sup D]; exact le_sup_left
  have hG0 : triG0 D ≤ triG D := by rw [triG_eq_sup D]; exact le_sup_right
  have h1 : x + rVec D u ∈ triG0 D := mem_triCoset_iff' D u x |>.mp h
  obtain ⟨d, hd⟩ := (mem_triG0_iff D (x + rVec D u)).mp h1
  have hdec : ∀ i : Fin n, x i = rVec D u i + ∑ a', d a' * clause0Row D a' i := by
    intro i
    have h1i := hd i
    simp only [Pi.add_apply, rVec] at h1i
    rw [← h1i]
    exact (char2_add_add_cancel _ (x i)).symm
  have hrG : rVec D u ∈ triG D := hG1 (mem_triG1_iff' D (rVec D u) |>.mpr ⟨u, fun _ => rfl⟩)
  have hvG : (fun i => ∑ a', d a' * clause0Row D a' i) ∈ triG D := by
    refine hG0 ?_
    rw [mem_triG0_iff]
    exact ⟨d, fun i => rfl⟩
  have : x = rVec D u + (fun i => ∑ a', d a' * clause0Row D a' i) := by
    funext i
    simp only [Pi.add_apply]
    rw [hdec i]
  rw [this]
  exact Submodule.add_mem _ hrG hvG

/-- Identifies the codespace with the complex span of its logical codewords. -/
private theorem codespace_eq_span {m n k : ℕ} (D : TriorthogonalData m n k) :
    triCodespace D = Submodule.span ℂ (Set.range (triCodeword D)) := by
  apply le_antisymm
  · intro ψ hψ
    have hψ' := mem_codespace_iff D ψ |>.mp hψ
    obtain ⟨hX, hZ⟩ := hψ'
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun u => ψ (rVec D u), ?_⟩
    funext x
    by_cases hx : x ∈ triG D
    · obtain ⟨u, hu⟩ := exists_coset D hx
      have hxi : x + rVec D u ∈ triG0 D := mem_triCoset_iff' D u x |>.mp hu
      have hxr : x = rVec D u + (x + rVec D u) := by
        funext i
        simp only [Pi.add_apply]
        exact (char2_add_add_cancel (rVec D u i) (x i)).symm
      have hψr : ψ (rVec D u) = ψ x := by
        have hv : quditXVec (x + rVec D u) *ᵥ ψ = ψ := hX (x + rVec D u) hxi
        have hvx := congrFun hv x
        rw [xVec_mulVec] at hvx
        have hsimp : x + (x + rVec D u) = rVec D u := by
          funext i
          simp only [Pi.add_apply]
          rw [← add_assoc, char2_add_self (x i), zero_add]
        rw [← hvx, hsimp]
      have hmem : rVec D u ∈ triCoset D u := by
        rw [mem_triCoset_iff']
        have hz : rVec D u + rVec D u = 0 := by
          funext i
          simp only [Pi.add_apply]
          exact char2_add_self _
        rw [hz]
        exact Submodule.zero_mem _
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single u]
      · show ψ (rVec D u) * ((triCoset D u).indicator (fun _ => (1 : ℂ)) x) = ψ x
        rw [Set.indicator_of_mem hu, mul_one, hψr]
      · intro u' _ huu
        show ψ (rVec D u') * ((triCoset D u').indicator (fun _ => (1 : ℂ)) x) = 0
        rw [Set.indicator_of_notMem (fun hc => huu (coset_unique D hc hu)), mul_zero]
      · intro hcon
        exact absurd (Finset.mem_univ u) hcon
    · rw [support_in_G D ψ hψ hx]
      have hzero : ∀ u : Fin k → F1024,
          ((fun u => ψ (rVec D u)) u • triCodeword D u) x = 0 := by
        intro u
        show ψ (rVec D u) * ((triCoset D u).indicator (fun _ => (1 : ℂ)) x) = 0
        rw [Set.indicator_of_notMem (fun hcon => hx (coset_subset_G D hcon)), mul_zero]
      calc (∑ u, (fun u => ψ (rVec D u)) u • triCodeword D u) x
          = ∑ u, ((fun u => ψ (rVec D u)) u • triCodeword D u) x := Finset.sum_apply _ _ _
        _ = 0 := Finset.sum_eq_zero fun u _ => hzero u
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨u, rfl⟩
    exact codeword_mem_codespace D u

/-- Shows that the logical codewords are linearly independent over the complex numbers. -/
private theorem linearIndependent_codeword {m n k : ℕ}
    (D : TriorthogonalData m n k) :
    LinearIndependent ℂ (triCodeword D) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg u₀
  have hmem : rVec D u₀ ∈ triCoset D u₀ := by
    rw [mem_triCoset_iff']
    have hz : rVec D u₀ + rVec D u₀ = 0 := by
      funext i
      simp only [Pi.add_apply]
      exact char2_add_self _
    rw [hz]
    exact Submodule.zero_mem _
  have hval := congrFun hg (rVec D u₀)
  rw [Finset.sum_apply] at hval
  rw [Finset.sum_eq_single u₀] at hval
  · rw [show (g u₀ • triCodeword D u₀) (rVec D u₀)
        = g u₀ * ((triCoset D u₀).indicator (fun _ => (1 : ℂ)) (rVec D u₀)) from by
        rw [triCodeword, Pi.smul_apply, smul_eq_mul],
      Set.indicator_of_mem hmem, mul_one] at hval
    exact hval
  · intro u _ huu
    show g u * ((triCoset D u).indicator (fun _ => (1 : ℂ)) (rVec D u₀)) = (0 : ℂ)
    rw [Set.indicator_of_notMem (fun hc => huu (coset_unique D hc hmem)), mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ u₀) hcon

/-- Establishes that the triorthogonal CSS construction encodes the prescribed `k` logical
qudits. -/
theorem triorthogonalCssEncodesK : TriorthogonalCssEncodesK := by
  intro m n k D
  rw [codespace_eq_span D,
    finrank_span_eq_card (linearIndependent_codeword D),
    Fintype.card_pi, Finset.prod_const, card_F1024, Finset.card_univ, Fintype.card_fin]

end Qatlib.Papers.MagicDistill24.Triorthogonal
