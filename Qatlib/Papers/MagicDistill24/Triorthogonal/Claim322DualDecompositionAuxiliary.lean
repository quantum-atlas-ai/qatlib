/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalCss

@[expose] public section
set_option backward.isDefEq.respectTransparency false

open Matrix

namespace Qatlib.Papers.MagicDistill24.Triorthogonal
noncomputable section

def mulSigmaLin {n : ℕ} (σ : Fin n → F1024) : (Fin n → F1024) →ₗ[F1024] (Fin n → F1024) where
  toFun f := fun i => σ i * f i
  map_add' f g := by
    ext i
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
end
end Qatlib.Papers.MagicDistill24.Triorthogonal
