module

public import Qatlib.Papers.GraphConnect03.MainResults.LowerBounds.Theorem5MatrixConnectivity
public import Qatlib.Papers.GraphConnect03.RelationBound.ChangedCoordinateBound
public import Qatlib.Papers.GraphConnect03.ParityReduce.ParityOrbitPeriod

@[expose] public section

/-!
# Graph connectivity — concrete consumers

Concrete non-degenerate consumers for the Dev theorems on the Figure 3
2-switch (Theorem 5), the changed-coordinate adversary value (Theorem 3),
and the parity cycle structure (Lemma 2) of
Dürr--Mhalla--Lei, arXiv:quant-ph/0303169v3.

The graph instances are a 4-cycle and its 2-switch partner, and two
disjoint triangles on six vertices; the parity instances are the strings
`100` (odd) and `000` (even) over `ZMod 3`.
-/

set_option autoImplicit false

namespace QatlibTests.GraphConnect03ConnectivityRegression

open Classical
open Qatlib.Papers.GraphConnect03.MainResults.Model
open Qatlib.Papers.GraphConnect03.MainResults.LowerBounds
open Qatlib.Papers.GraphConnect03.RelationBound
open Qatlib.Papers.GraphConnect03.ParityReduce
open Qatlib.Papers.GraphConnect03.MainResults.LowerBounds
open Qatlib.Papers.GraphConnect03.ParityReduce

attribute [local instance] Classical.propDecidable

/-! ## The 4-cycle and its Figure 3 2-switch partner -/

/-- Adjacency of the 4-cycle `0-1-2-3-0`. -/
def cycle4Adj (u v : Fin 4) : Bool :=
  decide ((u.val + 1) % 4 = v.val ∨ (v.val + 1) % 4 = u.val)

/-- The 4-cycle as an undirected matrix. -/
def cycle4 : UndirectedMatrix 4 :=
  ⟨cycle4Adj, by
    intro u v
    fin_cases u <;> fin_cases v <;> rfl, by
    intro u
    fin_cases u <;> rfl⟩

/-- Adjacency after the 2-switch removing `(0,1), (2,3)` and inserting
`(0,2), (1,3)`: the pairs are `02, 12, 13, 30`. -/
def swap4Adj (u v : Fin 4) : Bool :=
  decide ((u.val, v.val) ∈
    [(0, 2), (2, 0), (1, 2), (2, 1), (1, 3), (3, 1), (3, 0), (0, 3)])

/-- The 2-switch partner of the 4-cycle. -/
def swap4 : UndirectedMatrix 4 :=
  ⟨swap4Adj, by
    intro u v
    fin_cases u <;> fin_cases v <;> rfl, by
    intro u
    fin_cases u <;> rfl⟩

/-- The concrete Figure 3 relation between the 4-cycle and its partner. -/
theorem cycle4_swap4_rel : MatrixEdgeSwapRel cycle4 swap4 := by
  refine ⟨0, 1, 2, 3, by decide, by decide, by decide, by decide,
    by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | simp_all

/-- The 4-cycle is 2-regular, checked vertex by vertex. -/
theorem cycle4_twoRegular : TwoRegular cycle4 := by
  intro v
  fin_cases v
  · have hset : (Finset.univ.filter (fun w => cycle4.adj (0 : Fin 4) w = true)) =
        {1, 3} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      fin_cases w <;> decide
    show (Finset.univ.filter (fun w => cycle4.adj (0 : Fin 4) w = true)).card = 2
    rw [hset]
    decide
  · have hset : (Finset.univ.filter (fun w => cycle4.adj (1 : Fin 4) w = true)) =
        {0, 2} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      fin_cases w <;> decide
    show (Finset.univ.filter (fun w => cycle4.adj (1 : Fin 4) w = true)).card = 2
    rw [hset]
    decide
  · have hset : (Finset.univ.filter (fun w => cycle4.adj (2 : Fin 4) w = true)) =
        {1, 3} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      fin_cases w <;> decide
    show (Finset.univ.filter (fun w => cycle4.adj (2 : Fin 4) w = true)).card = 2
    rw [hset]
    decide
  · have hset : (Finset.univ.filter (fun w => cycle4.adj (3 : Fin 4) w = true)) =
        {2, 0} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      fin_cases w <;> decide
    show (Finset.univ.filter (fun w => cycle4.adj (3 : Fin 4) w = true)).card = 2
    rw [hset]
    decide

/- The 2-switch partner is again 2-regular, by degree preservation, and
the relation also holds in the symmetric direction. -/
example : TwoRegular swap4 :=
  matrixEdgeSwapRel_twoRegular cycle4_swap4_rel cycle4_twoRegular

example : MatrixEdgeSwapRel swap4 cycle4 :=
  matrixEdgeSwapRel_symm cycle4_swap4_rel

example : cycle4 ≠ swap4 :=
  matrixEdgeSwapRel_ne cycle4_swap4_rel

example : UniqueCycle cycle4 → TwoRegular swap4 :=
  fun h => matrixEdgeSwapRel_twoRegular cycle4_swap4_rel h.1

/-! ## Two disjoint triangles: the balanced two-cycle side -/

/-- Adjacency of two disjoint triangles `{0,1,2}` and `{3,4,5}`. -/
def twoTriAdj (u v : Fin 6) : Bool :=
  decide ((u.val, v.val) ∈
    [(0, 1), (1, 0), (1, 2), (2, 1), (2, 0), (0, 2),
     (3, 4), (4, 3), (4, 5), (5, 4), (5, 3), (3, 5)])

/-- Two disjoint triangles as an undirected matrix on six vertices. -/
def twoTri : UndirectedMatrix 6 :=
  ⟨twoTriAdj, by
    intro u v
    fin_cases u <;> fin_cases v <;> rfl, by
    intro u
    fin_cases u <;> rfl⟩

/-- Every edge of the two-triangle graph stays in one triangle. -/
private theorem twoTri_same_side {u v : Fin 6}
    (h : twoTri.toDigraph.adj u v = true) : u.val < 3 ↔ v.val < 3 := by
  fin_cases u <;> fin_cases v <;> revert h <;> decide

/-- Reachability from `0` in the two-triangle graph stays in the first
triangle. -/
theorem twoTri_reach_zero_val_lt {u : Fin 6}
    (h : twoTri.toDigraph.Reach 0 u) : u.val < 3 := by
  induction h with
  | refl => decide
  | tail _ hbc ih => exact (twoTri_same_side hbc).mp ih

/-- Reachability from `3` in the two-triangle graph stays in the second
triangle. -/
theorem twoTri_reach_three_val_ge {u : Fin 6}
    (h : twoTri.toDigraph.Reach 3 u) : 3 ≤ u.val := by
  induction h with
  | refl => decide
  | tail _ hbc ih =>
      exact Nat.le_of_not_gt (fun hc => Nat.not_lt_of_ge ih ((twoTri_same_side hbc).mpr hc))

/-- The component of `0` in the two-triangle graph is `{0,1,2}`. -/
theorem twoTri_component_zero :
    (Finset.univ.filter (fun u => twoTri.toDigraph.Reach (0 : Fin 6) u)) =
      {0, 1, 2} := by
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  fin_cases u
  · exact ⟨fun _ => by decide, fun _ => Digraph.Reach.refl _ _⟩
  · exact ⟨fun _ => by decide,
      fun _ => Digraph.Reach.edge (by decide)⟩
  · exact ⟨fun _ => by decide,
      fun _ => Digraph.Reach.edge (by decide : twoTri.toDigraph.adj (0 : Fin 6) 2 = true)⟩
  · exact ⟨fun h => absurd (twoTri_reach_zero_val_lt h) (by decide),
      fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd (twoTri_reach_zero_val_lt h) (by decide),
      fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd (twoTri_reach_zero_val_lt h) (by decide),
      fun h => absurd h (by decide)⟩

/-- The component of `3` in the two-triangle graph is `{3,4,5}`. -/
theorem twoTri_component_three :
    (Finset.univ.filter (fun u => twoTri.toDigraph.Reach (3 : Fin 6) u)) =
      {3, 4, 5} := by
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  fin_cases u
  · exact ⟨fun h => absurd (twoTri_reach_three_val_ge h) (by decide),
      fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd (twoTri_reach_three_val_ge h) (by decide),
      fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd (twoTri_reach_three_val_ge h) (by decide),
      fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => by decide, fun _ => Digraph.Reach.refl _ _⟩
  · exact ⟨fun _ => by decide,
      fun _ => Digraph.Reach.edge (by decide)⟩
  · exact ⟨fun _ => by decide,
      fun _ => Digraph.Reach.edge (by decide : twoTri.toDigraph.adj (3 : Fin 6) 5 = true)⟩

/-- Two disjoint triangles form a balanced two-cycle input on six
vertices. -/
theorem twoTri_twoCycles : TwoCycles twoTri := by
  have hreg : TwoRegular twoTri := by
    intro v
    fin_cases v
    · have hset : (Finset.univ.filter (fun w => twoTri.adj (0 : Fin 6) w = true)) =
          {1, 2} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        fin_cases w <;> decide
      show (Finset.univ.filter (fun w => twoTri.adj (0 : Fin 6) w = true)).card = 2
      rw [hset]
      decide
    · have hset : (Finset.univ.filter (fun w => twoTri.adj (1 : Fin 6) w = true)) =
          {0, 2} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        fin_cases w <;> decide
      show (Finset.univ.filter (fun w => twoTri.adj (1 : Fin 6) w = true)).card = 2
      rw [hset]
      decide
    · have hset : (Finset.univ.filter (fun w => twoTri.adj (2 : Fin 6) w = true)) =
          {0, 1} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        fin_cases w <;> decide
      show (Finset.univ.filter (fun w => twoTri.adj (2 : Fin 6) w = true)).card = 2
      rw [hset]
      decide
    · have hset : (Finset.univ.filter (fun w => twoTri.adj (3 : Fin 6) w = true)) =
          {4, 5} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        fin_cases w <;> decide
      show (Finset.univ.filter (fun w => twoTri.adj (3 : Fin 6) w = true)).card = 2
      rw [hset]
      decide
    · have hset : (Finset.univ.filter (fun w => twoTri.adj (4 : Fin 6) w = true)) =
          {3, 5} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        fin_cases w <;> decide
      show (Finset.univ.filter (fun w => twoTri.adj (4 : Fin 6) w = true)).card = 2
      rw [hset]
      decide
    · have hset : (Finset.univ.filter (fun w => twoTri.adj (5 : Fin 6) w = true)) =
          {3, 4} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        fin_cases w <;> decide
      show (Finset.univ.filter (fun w => twoTri.adj (5 : Fin 6) w = true)).card = 2
      rw [hset]
      decide
  have hnotreach : ¬ twoTri.toDigraph.Reach (0 : Fin 6) 3 :=
    fun h => absurd (twoTri_reach_zero_val_lt h) (by decide)
  refine ⟨hreg, ?_, 0, 3, hnotreach, ?_, ?_, ?_, ?_, ?_⟩
  · intro hconn
    exact hnotreach (hconn 0 3)
  · intro u
    fin_cases u
    · exact Or.inl (Digraph.Reach.refl _ _)
    · exact Or.inl (Digraph.Reach.edge (by decide))
    · exact Or.inl (Digraph.Reach.edge
        (by decide : twoTri.toDigraph.adj (0 : Fin 6) 2 = true))
    · exact Or.inr (Digraph.Reach.refl _ _)
    · exact Or.inr (Digraph.Reach.edge (by decide))
    · exact Or.inr (Digraph.Reach.edge
        (by decide : twoTri.toDigraph.adj (3 : Fin 6) 5 = true))
  · have hc : componentSize twoTri (0 : Fin 6) = 3 := by
      unfold componentSize
      rw [twoTri_component_zero]
      decide
    omega
  · have hc : componentSize twoTri (0 : Fin 6) = 3 := by
      unfold componentSize
      rw [twoTri_component_zero]
      decide
    omega
  · have hc : componentSize twoTri (3 : Fin 6) = 3 := by
      unfold componentSize
      rw [twoTri_component_three]
      decide
    omega
  · have hc : componentSize twoTri (3 : Fin 6) = 3 := by
      unfold componentSize
      rw [twoTri_component_three]
      decide
    omega

/- The two triangle components add up to all six vertices, and the
two-cycle input is not a unique cycle. -/
example : ∃ v w : Fin 6, ¬ twoTri.toDigraph.Reach v w ∧
    componentSize twoTri v + componentSize twoTri w = 6 ∧
    3 * componentSize twoTri v ≥ 6 ∧ 3 * componentSize twoTri v ≤ 2 * 6 ∧
    3 * componentSize twoTri w ≥ 6 ∧ 3 * componentSize twoTri w ≤ 2 * 6 :=
  twoCycles_componentSize_add twoTri_twoCycles

example : ¬ UniqueCycle twoTri :=
  twoCycles_not_uniqueCycle twoTri_twoCycles

example (M : UndirectedMatrix 0) : ¬ UniqueCycle M :=
  fun h => Nat.lt_irrefl 0 h.2.1

/-! ## The parity encoding on three columns -/

/-- The odd-parity string `100` over `ZMod 3`. -/
def xOdd : ZMod 3 → Bool := fun i => decide (i = 0)

/-- The even-parity string `000` over `ZMod 3`. -/
def xEven : ZMod 3 → Bool := fun _ => false

example : parityOf xOdd = true := by decide

example : parityOf xEven = false := by decide

/- Odd parity: three steps swap the track, so `(0,false)` reaches
`(0,true)` in one full round. -/
example : (parityEquiv xOdd)^[3] ((0 : ZMod 3), false) = ((0 : ZMod 3), true) :=
  parityEquiv_iterate_p_of_odd xOdd (by decide) 0 false

/- Even parity: three steps are the identity on each track. -/
example : (parityEquiv xEven)^[3] ((1 : ZMod 3), true) = ((1 : ZMod 3), true) :=
  parityEquiv_iterate_p_of_even xEven (by decide) (1, true)

/- Six steps are always the identity. -/
example : (parityEquiv xOdd)^[6] ((2 : ZMod 3), true) = ((2 : ZMod 3), true) :=
  parityEquiv_iterate_two_p xOdd (2, true)

/- Every parity vertex has exactly one successor and one predecessor. -/
example : (Finset.univ.filter
    (fun v => parityStep xOdd ((0 : ZMod 3), false) = v)).card = 1 :=
  parityEdge_out_card xOdd (0, false)

example : (Finset.univ.filter
    (fun u => parityStep xOdd u = ((0 : ZMod 3), true))).card = 1 :=
  parityEdge_in_card xOdd (0, true)

/-! ## Theorem 3 neighborhood counts and adversary value -/

/-- A relation with a single edge between the two one-bit inputs. -/
noncomputable def oneBitRelation : AmbainisRelation 1 where
  X := {fun _ => false}
  Y := {fun _ => true}
  R := fun _ _ => True
  m := 1
  m' := 1
  lmax := 1
  m_spec := by simp
  m'_spec := by simp
  l_spec := by
    intro x hx y hy _ i
    simp only [Finset.mem_singleton] at hx hy
    subst x y
    simp [Finset.filter_singleton]

example :
    (oneBitRelation.Y.filter (fun y => oneBitRelation.R (fun _ => false) y ∧
      y 0 = false)).card *
    (oneBitRelation.X.filter (fun x => oneBitRelation.R x (fun _ => true) ∧
      x 0 = true)).card ≤ oneBitRelation.lmax :=
  ambainisRelation_unchangedLoad_le oneBitRelation
    (x := fun _ => false) (y := fun _ => true) (i := 0)
    (by simp [oneBitRelation]) (by simp [oneBitRelation]) trivial (by decide)

example :
    (oneBitRelation.Y.filter (fun y => oneBitRelation.R (fun _ => false) y ∧
      y 0 ≠ false)).card = 1 ∧
    (oneBitRelation.X.filter (fun x => oneBitRelation.R x (fun _ => true) ∧
      x 0 ≠ true)).card = 1 := by
  obtain ⟨hY, hX⟩ := ambainisRelation_sourceChangedLoad_eq oneBitRelation
    (x := fun _ => false) (y := fun _ => true) (i := 0) (by decide)
  rw [hY, hX]
  simp [oneBitRelation, Finset.filter_singleton]

example : adversaryValue (6 ^ 2) (6 ^ 2) 6 = (6 : ℝ) * Real.sqrt (6 : ℝ) :=
  adversaryValue_matrix 6 (by norm_num)

example : (6 : ℝ) ≤ adversaryValue (6 ^ 2) (6 ^ 2) 6 :=
  adversaryValue_matrix_ge 6 (by norm_num)

example : adversaryValue 4 9 8 ≤ adversaryValue 9 16 4 :=
  adversaryValue_mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : 0 < adversaryValue 4 9 8 :=
  adversaryValue_pos (by norm_num) (by norm_num) (by norm_num)

end QatlibTests.GraphConnect03ConnectivityRegression
