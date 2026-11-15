/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalCss

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.MagicDistill24.Triorthogonal

def TriorthogonalFromSevenfoldCode : Prop :=
  ∀ (k m' n : ℕ) (G₁ : Matrix (Fin k) (Fin n) F1024) (G₀ : Matrix (Fin m') (Fin n) F1024)
    (w : Fin k ⊕ Fin n → F1024) (_hw : ∀ j, w j ≠ 0),
    (∀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : Fin k ⊕ Fin n → F1024,
      y₁ ∈ triRowSpace (triStdGen G₁ G₀) → y₂ ∈ triRowSpace (triStdGen G₁ G₀) →
      y₃ ∈ triRowSpace (triStdGen G₁ G₀) → y₄ ∈ triRowSpace (triStdGen G₁ G₀) →
      y₅ ∈ triRowSpace (triStdGen G₁ G₀) → y₆ ∈ triRowSpace (triStdGen G₁ G₀) →
      y₇ ∈ triRowSpace (triStdGen G₁ G₀) →
        ∑ i, y₁ i * y₂ i * y₃ i * y₄ i * y₅ i * y₆ i * y₇ i = 0) →
    (∀ y₁ y₂ : Fin k ⊕ Fin n → F1024,
      y₁ ∈ triRowSpace (triStdGen G₁ G₀) → y₂ ∈ triRowSpace (triStdGen G₁ G₀) →
        ∑ i, (w i) ^ 5 * y₁ i * y₂ i = 0) →
    TriTripleOrth (triPuncture G₁ G₀) k
      ∧ TriPairOrth (triPuncture G₁ G₀) k
          (fun i => (w (Sum.inr i)) ^ 5) (fun a => (w (Sum.inl a)) ^ 5)

end Qatlib.Papers.MagicDistill24.Triorthogonal
