/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalCss
public import Qatlib.Papers.MagicDistill24.Triorthogonal.Claim322DualDecompositionAuxiliary

@[expose] public section

namespace Qatlib.Papers.MagicDistill24.Triorthogonal

open Matrix

noncomputable section

def Claim322DualDecomposition : Prop :=
  ∀ (m n k : ℕ) (D : TriorthogonalData m n k),
    triDual (triG0 D)
      = Submodule.map (mulSigmaLin D.σ) (triG1 D) ⊔ triDual (triG D)
      ∧ Submodule.map (mulSigmaLin D.σ) (triG1 D) ⊓ triDual (triG D) = ⊥

end

end Qatlib.Papers.MagicDistill24.Triorthogonal
