/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.QuditF1024

@[expose] public section

namespace Qatlib.Papers.MagicDistill24.Triorthogonal

open Matrix

noncomputable section

def TriTripleOrth {m n : ℕ} (G : Matrix (Fin m) (Fin n) F1024) (k : ℕ) : Prop :=
  ∀ a b c : Fin m,
    ∑ i, (G a i) ^ 4 * (G b i) ^ 2 * (G c i)
      = if (a : ℕ) = (b : ℕ) ∧ (b : ℕ) = (c : ℕ) ∧ (a : ℕ) < k then 1 else 0

def TriPairOrth {m n : ℕ} (G : Matrix (Fin m) (Fin n) F1024) (k : ℕ)
    (σ : Fin n → F1024) (τ : Fin k → F1024) : Prop :=
  ∀ a b : Fin m,
    ∑ i, σ i * G a i * G b i
      = if h : (a : ℕ) = (b : ℕ) ∧ (a : ℕ) < k then τ ⟨(a : ℕ), h.2⟩ else 0

structure TriorthogonalData (m n k : ℕ) where
  hk : k ≤ m
  G : Matrix (Fin m) (Fin n) F1024
  σ : Fin n → F1024
  τ : Fin k → F1024
  hσ : ∀ i, σ i ≠ 0
  hτ : ∀ a, τ a ≠ 0
  triTriple : TriTripleOrth G k
  triPair : TriPairOrth G k σ τ

def triRowSpace {ι κ : Type*} (M : Matrix ι κ F1024) :
    Submodule F1024 (κ → F1024) :=
  Submodule.span F1024 (Set.range fun a : ι => M a)

def triDotLin {n : ℕ} (x : Fin n → F1024) : (Fin n → F1024) →ₗ[F1024] F1024 where
  toFun y := ∑ i, x i * y i
  map_add' y z := by
    simp only [Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

def triDual {n : ℕ} (S : Submodule F1024 (Fin n → F1024)) :
    Submodule F1024 (Fin n → F1024) :=
  ⨅ x ∈ S, LinearMap.ker (triDotLin x)

def triG {m n k : ℕ} (D : TriorthogonalData m n k) : Submodule F1024 (Fin n → F1024) :=
  triRowSpace D.G

def triG1 {m n k : ℕ} (D : TriorthogonalData m n k) :
    Submodule F1024 (Fin n → F1024) :=
  Submodule.span F1024 (Set.range fun a : Fin k => D.G (Fin.castLE D.hk a))

def triG0 {m n k : ℕ} (D : TriorthogonalData m n k) :
    Submodule F1024 (Fin n → F1024) :=
  Submodule.span F1024
    (Set.range fun a : Fin (m - k) =>
      D.G ((Fin.cast (by have hk := D.hk; omega) : Fin (k + (m - k)) → Fin m)
        (Fin.natAdd k a)))

def triCodespace {m n k : ℕ} (D : TriorthogonalData m n k) :
    Submodule ℂ ((Fin n → F1024) → ℂ) :=
  (⨅ v ∈ triG0 D, LinearMap.ker ((quditXVec v).mulVecLin - LinearMap.id))
    ⊓ (⨅ w ∈ triDual (triG D), LinearMap.ker ((quditZVec w).mulVecLin - LinearMap.id))

def triCoset {m n k : ℕ} (D : TriorthogonalData m n k) (u : Fin k → F1024) :
    Set (Fin n → F1024) :=
  (fun g i => ∑ a, u a * D.G (Fin.castLE D.hk a) i + g i) '' (triG0 D : Set (Fin n → F1024))

noncomputable def triCodeword {m n k : ℕ} (D : TriorthogonalData m n k)
    (u : Fin k → F1024) : (Fin n → F1024) → ℂ :=
  (triCoset D u).indicator fun _ => 1

def triHammingWeight {n : ℕ} (f : Fin n → F1024) : ℕ :=
  (Finset.univ.filter fun i => f i ≠ 0).card

def triDistanceX {m n k : ℕ} (D : TriorthogonalData m n k) : ℕ∞ :=
  sInf {w : ℕ∞ | ∃ f, f ∈ triG D ∧ f ∉ triG0 D ∧ (triHammingWeight f : ℕ∞) = w}

def triDistanceZ {m n k : ℕ} (D : TriorthogonalData m n k) : ℕ∞ :=
  sInf {w : ℕ∞ | ∃ f, f ∈ triDual (triG0 D) ∧ f ∉ triDual (triG D)
    ∧ (triHammingWeight f : ℕ∞) = w}

def triGhat {m n k : ℕ} (D : TriorthogonalData m n k) (a : Fin k) : Fin n → F1024 :=
  fun i => (D.τ a)⁻¹ * D.σ i * D.G (Fin.castLE D.hk a) i

def triStdGen {k m' n : ℕ} (G₁ : Matrix (Fin k) (Fin n) F1024)
    (G₀ : Matrix (Fin m') (Fin n) F1024) :
    Matrix (Fin k ⊕ Fin m') (Fin k ⊕ Fin n) F1024 :=
  Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) F1024) G₁ 0 G₀

def triPuncture {k m' n : ℕ} (G₁ : Matrix (Fin k) (Fin n) F1024)
    (G₀ : Matrix (Fin m') (Fin n) F1024) :
    Matrix (Fin (k + m')) (Fin n) F1024 :=
  (triStdGen G₁ G₀).submatrix finSumFinEquiv.symm Sum.inr

end

end Qatlib.Papers.MagicDistill24.Triorthogonal
