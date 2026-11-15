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

def TriorthogonalCssEncodesK : Prop :=
  ∀ (m n k : ℕ) (D : TriorthogonalData m n k),
    Module.finrank ℂ (triCodespace D) = (Fintype.card F1024) ^ k

end Qatlib.Papers.MagicDistill24.Triorthogonal
