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

def TriorthogonalCssZDistance : Prop :=
  ∀ (m n k : ℕ) (D : TriorthogonalData m n k),
    triDistanceZ D ≤ triDistanceX D

end Qatlib.Papers.MagicDistill24.Triorthogonal
