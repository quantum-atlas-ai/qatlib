/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.Model.AmplitudeDamping

set_option backward.isDefEq.respectTransparency false

/-!
# ReducedBlocks — the charge-block reductions of Sections 4 and Appendices E, F

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1.

After the identity-target output twirl (Lemma 3.1, Eq. (38), p. 10) and the
fixed-order charge-block reduction (Lemma E.1, Eq. (172)-(175), p. 36), an
`A ≺ B` MISC point is described by the block tuple

```
S00 = [[a,0,u,0],[0,b,0,-u],[u,0,g,0],[0,-u,0,h]]
S0,-1 = [[b,-u],[-u,h]],   S-1,0 = diag(m0,n0),   C00 symmetric with zero diagonal
g + h = m0 + n0,   a + b + m0 + n0 = 1,
x_c = v^T C00 v + 2 ε s (r + t),   v = (1, s, s, s^2).
```

The block matrices `S00 ± C00`, `S0,-1 ± K(r)`, `S-1,0 ± K(t)` are the
principal blocks of `S ± Tc` (Lemma E.1), and their positive semidefiniteness is
the primal feasibility used in the certificate identity (Lemma E.4, p. 39).

**Modelling boundary.**  This file works with these reduced block tuples
directly.  The raw 16x16 operator-valued SDP and the finite linear system that
produces the normal form are *not* re-derived here; the theorem
`Foundations/FixedOrder/SourceLemmaE1.lean` records that reduction as a source
claim.  The optimum `muSeq` below is therefore the supremum of the *reduced*
feasible set.

The parallel class is the sub-family with `u = 0` and `S-1,0 = diag(g,h)`
(Eq. (76), p. 15).  The general-process class is modelled by its one-parameter
achievable family `x_c(t)` (Eq. (80), p. 16), whose optimality is the content of
the Section F certificate.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.Model

open Matrix

/-! ## Fixed-order (`A ≺ B`) reduced blocks -/

/-- Reduced `A ≺ B` block tuple of Lemma E.1, Eq. (172)-(175), p. 36. -/
structure SeqBlock where
  a : ℝ
  b : ℝ
  g : ℝ
  h : ℝ
  m0 : ℝ
  n0 : ℝ
  u : ℝ
  r : ℝ
  t : ℝ
  c01 : ℝ
  c02 : ℝ
  c03 : ℝ
  c12 : ℝ
  c13 : ℝ
  c23 : ℝ

/-- The `2x2` off-diagonal block `K(q) = [[0,q],[q,0]]` (Eq. (174), p. 36). -/
def Kmat (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, q; q, 0]

/-- The `S00` principal block, Eq. (172), p. 36. -/
def seqS00 (B : SeqBlock) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![B.a, 0, B.u, 0;
     0, B.b, 0, -B.u;
     B.u, 0, B.g, 0;
     0, -B.u, 0, B.h]

/-- The `S0,-1` principal block, Eq. (172), p. 36. -/
def seqS0m1 (B : SeqBlock) : Matrix (Fin 2) (Fin 2) ℝ := !![B.b, -B.u; -B.u, B.h]

/-- The `S-1,0` principal block, Eq. (172), p. 36. -/
def seqSm10 (B : SeqBlock) : Matrix (Fin 2) (Fin 2) ℝ := !![B.m0, 0; 0, B.n0]

/-- The `C00` coherence block: real symmetric with zero diagonal, Eq. (174), p. 36. -/
def seqC00 (B : SeqBlock) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, B.c01, B.c02, B.c03;
     B.c01, 0, B.c12, B.c13;
     B.c02, B.c12, 0, B.c23;
     B.c03, B.c13, B.c23, 0]

/-- The vector `v = (1, s, s, s^2)^T` of Eq. (175), p. 36. -/
def vvec (ε : ℝ) : Fin 4 → ℝ := ![1, s ε, s ε, (s ε) ^ 2]

/-- Quadratic form `v^T M v`. -/
def quadForm (v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∑ i, ∑ j, v i * M i j * v j

/-- The reduced fixed-order coherence coefficient, Eq. (175), p. 36:
`x_c = v^T C00 v + 2 ε s (r + t)`. -/
def seqXc (ε : ℝ) (B : SeqBlock) : ℝ :=
  quadForm (vvec ε) (seqC00 B) + 2 * ε * s ε * (B.r + B.t)

/-- Primal feasibility of a reduced fixed-order block tuple: the normalization
equations (173) and positive semidefiniteness of the principal blocks
`S00`, `S0,-1 ± K(r)`, `S-1,0 ± K(t)` and `S00 ± C00` (Lemma E.1, p. 36). -/
def SeqFeasible (ε : ℝ) (B : SeqBlock) : Prop :=
  B.g + B.h = B.m0 + B.n0 ∧
  B.a + B.b + B.m0 + B.n0 = 1 ∧
  (seqS00 B).PosSemidef ∧
  (seqS0m1 B + Kmat B.r).PosSemidef ∧
  (seqS0m1 B - Kmat B.r).PosSemidef ∧
  (seqSm10 B + Kmat B.t).PosSemidef ∧
  (seqSm10 B - Kmat B.t).PosSemidef ∧
  (seqS00 B + seqC00 B).PosSemidef ∧
  (seqS00 B - seqC00 B).PosSemidef

/-- Coherence values attainable by reduced fixed-order MISC points. -/
def seqAchievable (ε : ℝ) : Set ℝ :=
  {x | ∃ B : SeqBlock, SeqFeasible ε B ∧ seqXc ε B = x}

/-- The fixed-order MISC optimum `mu_MISC,Seq`, Eq. (54), p. 13, as the
supremum of the reduced feasible coherence values. -/
def muSeq (ε : ℝ) : ℝ := sSup (seqAchievable ε)

/-! ## Parallel reduced blocks (Eq. (76), p. 15) -/

/-- Reduced parallel block tuple: `S00 = diag(a,b,g,h)`,
`S0,-1 = diag(b,h)`, `S-1,0 = diag(g,h)` (Eq. (76), p. 15). -/
structure ParBlock where
  a : ℝ
  b : ℝ
  g : ℝ
  h : ℝ
  r : ℝ
  t : ℝ
  c01 : ℝ
  c02 : ℝ
  c03 : ℝ
  c12 : ℝ
  c13 : ℝ
  c23 : ℝ

/-- The diagonal four-dimensional parallel block in Eq. (76). -/
def parS00 (B : ParBlock) : Matrix (Fin 4) (Fin 4) ℝ := diagonal ![B.a, B.b, B.g, B.h]

/-- The diagonal parallel block indexed by zero and minus one. -/
def parS0m1 (B : ParBlock) : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![B.b, B.h]

/-- The diagonal parallel block indexed by minus one and zero. -/
def parSm10 (B : ParBlock) : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![B.g, B.h]

/-- The symmetric coherence matrix of a reduced parallel block. -/
def parC00 (B : ParBlock) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, B.c01, B.c02, B.c03;
     B.c01, 0, B.c12, B.c13;
     B.c02, B.c12, 0, B.c23;
     B.c03, B.c13, B.c23, 0]

/-- Reduced parallel coherence coefficient (same contraction as Eq. (175) with
the parallel normalization). -/
def parXc (ε : ℝ) (B : ParBlock) : ℝ :=
  quadForm (vvec ε) (parC00 B) + 2 * ε * s ε * (B.r + B.t)

/-- Parallel feasibility: normalization `a + b + g + h = 1` together with the
principal-block positivity conditions. -/
def ParFeasible (ε : ℝ) (B : ParBlock) : Prop :=
  B.a + B.b + B.g + B.h = 1 ∧
  (parS00 B).PosSemidef ∧
  (parS0m1 B + Kmat B.r).PosSemidef ∧
  (parS0m1 B - Kmat B.r).PosSemidef ∧
  (parSm10 B + Kmat B.t).PosSemidef ∧
  (parSm10 B - Kmat B.t).PosSemidef ∧
  (parS00 B + parC00 B).PosSemidef ∧
  (parS00 B - parC00 B).PosSemidef

/-- Coherence values realized by feasible reduced parallel blocks. -/
def parAchievable (ε : ℝ) : Set ℝ :=
  {x | ∃ B : ParBlock, ParFeasible ε B ∧ parXc ε B = x}

/-- The parallel MISC optimum `mu_MISC,Par`. -/
def muPar (ε : ℝ) : ℝ := sSup (parAchievable ε)

/-! ## General-process optimum (Eq. (80), p. 16) -/

/-- Coherence values of the general-process one-parameter family, Eq. (80), p. 16. -/
def genAchievable (ε : ℝ) : Set ℝ := genXc ε '' Set.Icc (0 : ℝ) 1

/-- The general-process MISC optimum `mu_MISC,Gen`, as the supremum over the
achievable family.  Optimality of this value (no feasible point exceeds it) is
the Section F certificate, recorded as source claim `c014`/`c021`. -/
def muGen (ε : ℝ) : ℝ := sSup (genAchievable ε)

/-! ## Errors (Eq. (44), p. 11)

Proposition 3.2 gives `D^H (N,N;I) = (1 - mu^H)/2`.  The diamond norm is not
rebuilt; the reduced error is defined by this identity, exactly as in the paper.
-/

/-- Reduced fixed-order MISC error, Eq. (44) with `mu = muSeq`. -/
def Dseq (ε : ℝ) : ℝ := (1 - muSeq ε) / 2

/-- Reduced parallel MISC error. -/
def Dpar (ε : ℝ) : ℝ := (1 - muPar ε) / 2

/-- Reduced general-process MISC error. -/
def Dgen (ε : ℝ) : ℝ := (1 - muGen ε) / 2

/-! ## Causal classes and free classes -/

/-- The three causal classes compared in the paper (Table 1, p. 5). -/
inductive CausalClass
  | Par
  | Seq
  | Gen
  deriving DecidableEq, Repr

/-- The two free-operation classes of Definition 2.1. -/
inductive FreeClass
  | MISC
  | DISC
  deriving DecidableEq, Repr

/-- The MISC optimum for each causal class. -/
def muMisc : CausalClass → ℝ → ℝ
  | .Par, ε => muPar ε
  | .Seq, ε => muSeq ε
  | .Gen, ε => muGen ε

/-- The MISC reduced error for each causal class. -/
def errorMisc (H : CausalClass) (ε : ℝ) : ℝ := (1 - muMisc H ε) / 2

end Qatlib.Papers.CausalHier26.MiscHierarchy.Model
