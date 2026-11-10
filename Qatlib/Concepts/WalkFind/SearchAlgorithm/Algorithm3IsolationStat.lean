/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
namespace Qatlib.Concepts.WalkFind.SearchAlgorithm

def Algorithm3Isolation : Prop := Algorithm3IsolationContract
end Qatlib.Concepts.WalkFind.SearchAlgorithm
