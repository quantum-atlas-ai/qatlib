/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGAdderData
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

def booleanNodeRename {n k : ℕ} (r : Fin n → Fin k) : BooleanNode n → BooleanNode k
  | .constant b => .constant b
  | .neg a => .neg (r a)
  | .xor a b => .xor (r a) (r b)
  | .conj a b => .conj (r a) (r b)

def booleanSpliceSource {M K m n : ℕ} (r : Fin m → Fin (M+K))
    (i : Fin (m+n)) : Fin (M+(K+n)) :=
  if h : i.val < m then Fin.castLE (by omega) (r ⟨i.val,h⟩)
  else ⟨M+K+(i.val-m),by have := i.isLt; omega⟩

def booleanDAGSplice {M K m : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) : {n : ℕ} → BooleanDAG m n → BooleanDAG M (K+n)
  | _, .nil => g
  | _, .snoc h node =>
    (booleanDAGSplice g r h).snoc (booleanNodeRename (booleanSpliceSource r) node)

def booleanDAGAppendAdder {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (a b : Fin w → Fin (M+K)) : BooleanDAG M (K+(5*w+1)) :=
  booleanDAGSplice g (fun i : Fin (2*w) =>
    if hi : i.val < w then a ⟨i.val,hi⟩ else b ⟨i.val-w,by omega⟩)
    (booleanWordAdderDAG w)

def booleanDAGAppendAdderSelect {M K : ℕ} (w : ℕ)
    (a b : Fin w → Fin (M+K)) : Fin (w+1) → Fin (M+(K+(5*w+1))) :=
  fun j => booleanSpliceSource (fun i : Fin (2*w) =>
    if hi : i.val < w then a ⟨i.val,hi⟩ else b ⟨i.val-w,by omega⟩)
    (booleanWordAdderSelect w j)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
