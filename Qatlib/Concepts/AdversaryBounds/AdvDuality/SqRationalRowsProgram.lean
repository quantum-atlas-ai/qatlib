/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalRowProgram
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Batched Gaussian-rational row programs

`batchPlan` concatenates exact Gaussian-rational row computations and assigns output indices to
each job. Its execution theorem preserves the initial cache and identifies every selected row
output under explicit job-validity conditions.

`matrixJobs` and `matrixInputs` specialize the construction to rectangular matrix data and query
vectors, with exact source-read, arithmetic, and row-build counts. These routines supply
arithmetic components for matrix-based adversary computations; see [HoyerLeeSpalek2007].

## Main statements

* `batchPlan_run`: executes valid row jobs and identifies their outputs.
* `matrixJobs_valid`: verifies the indices of jobs generated from matrix rows.
* `batchPlan_output`: realizes a selected batch output or a preserved fallback entry.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2500000
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat
open Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
universe u

/-- A successful cache program extends its initial cache by appending a list of entries. -/
theorem cacheRun_suffix (sourceCount : ℕ) (p : List CacheOp) (cs cs' : List GaussianCode)
    (hr : cacheRun sourceCount p cs=some cs') : ∃ tail,cs'=cs++tail := by
  induction p generalizing cs with
  | nil =>
    simp only [cacheRun,Option.some.injEq] at hr
    subst cs'
    exact ⟨[],by simp⟩
  | cons op rest ih =>
    by_cases hv : op.Valid sourceCount cs.length
    · have ht : cacheRun sourceCount rest (cs++[op.eval cs])=some cs' := by
        simpa only [cacheRun,CacheOp.step,if_pos hv,Option.bind_some] using! hr
      obtain ⟨tail,he⟩ := ih _ ht
      exact ⟨op.eval cs::tail,by simpa [List.append_assoc] using! he⟩
    · simp only [cacheRun,CacheOp.step,if_neg hv,Option.bind_none,reduceCtorEq] at hr

/-- Appending cache entries preserves a selected row value when all relevant indices lie in the
original cache and the choice is valid. -/
theorem rowValue_append (n source weight acc : ℕ) (cs tail : List GaussianCode) (choice : Option ℕ)
    (hs : source+n ≤ cs.length) (hw : weight+n ≤ cs.length) (ha : acc < cs.length)
    (hc : choice.elim True (fun j => j < n)) :
    rowValue n source weight acc (cs++tail) choice=rowValue n source weight acc cs choice := by
  cases choice with
  | none =>
    simp only [rowValue]
    rw [List.getD_append cs tail GaussianCode.zero acc ha,dotSpec_append _ _ _ _ _ _ hs hw]
  | some j =>
    simp only [Option.elim] at hc
    simp only [rowValue]
    rw [List.getD_append cs tail GaussianCode.zero (source+j) (by omega),
      List.getD_append cs tail GaussianCode.zero acc ha,dotSpec_append _ _ _ _ _ _ hs hw]

/-- The source, weight, and accumulator indices specifying one row computation. -/
structure RowJob where
  source : ℕ
  weight : ℕ
  acc : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The source-range, weight-range, and accumulator-index bounds required for a row job of width
`n`. -/
def RowJob.Valid (sourceCount n len : ℕ) (j : RowJob) : Prop :=
  j.source+n ≤ sourceCount ∧ sourceCount ≤ j.weight ∧ j.weight+n ≤ len ∧
    sourceCount ≤ j.acc ∧ j.acc < len

/-- Concatenate row plans for the jobs, advancing the cache base by `5 * n + 1` after each job. -/
def batchPlan (n : ℕ) : ℕ → List RowJob → List CacheOp
  | _,[] => []
  | base,job::rest => rowPlan n base job.source job.weight job.acc++batchPlan n (base+5*n+1) rest

/-- The cache index of a selected output from the `k`th row job. -/
def batchOutput (n base k : ℕ) (choice : Option ℕ) : ℕ := rowOutput n (base+(5*n+1)*k) choice

/-- A batch plan contains exactly `(5 * n + 1) * jobs.length` cache operations. -/
theorem batchPlan_length (n base : ℕ) (jobs : List RowJob) :
    (batchPlan n base jobs).length=(5*n+1)*jobs.length := by
  induction jobs generalizing base with
  | nil => simp [batchPlan]
  | cons job rest ih => simp only [batchPlan,List.length_append,rowPlan_length,ih,List.length_cons]; ring

/-- If every job is valid in the initial cache, the batch plan executes successfully and stores
every valid selected row value at its prescribed output index. -/
theorem batchPlan_run (sourceCount n : ℕ) (jobs : List RowJob) (cs : List GaussianCode)
    (hs : ∀ k,k < jobs.length → (jobs.getD k default).Valid sourceCount n cs.length) :
    ∃ cf,cacheRun sourceCount (batchPlan n cs.length jobs) cs=some cf ∧
      ∀ k,k < jobs.length → ∀ choice,choice.elim True (fun j => j < n) →
      cf.getD (batchOutput n cs.length k choice) GaussianCode.zero=
        rowValue n (jobs.getD k default).source (jobs.getD k default).weight (jobs.getD k default).acc cs choice := by
  induction jobs generalizing cs with
  | nil => exact ⟨cs,rfl,by intro k hk; simp at hk⟩
  | cons job rest ih =>
    have hj : job.Valid sourceCount n cs.length := by simpa using! hs 0 (by simp)
    obtain ⟨hsource,hw,hwb,ha,hab⟩ := hj
    obtain ⟨cd,hD,hDot,hV⟩ :=
        rowPlan_run sourceCount n job.source job.weight job.acc cs hsource hw hwb ha hab
    have hdl : cd.length=cs.length+5*n+1 := by
      have hh := cacheRun_length sourceCount _ cs cd hD
      rw [rowPlan_length] at hh
      omega
    have hrest : ∀ k,k < rest.length → (rest.getD k default).Valid sourceCount n cd.length := by
      intro k hk
      have hh : (rest.getD k default).Valid sourceCount n cs.length := by
        simpa only [List.getD_cons_succ] using! hs (k+1) (by simp; omega)
      obtain ⟨hsource,hw,hwb,ha,hab⟩ := hh
      exact ⟨hsource,hw,by omega,ha,by omega⟩
    obtain ⟨cf,hR,hRV⟩ := ih cd hrest
    have hR' : cacheRun sourceCount (batchPlan n (cs.length+5*n+1) rest) cd=some cf := by
      simpa only [hdl] using! hR
    obtain ⟨tail,heq⟩ := cacheRun_suffix sourceCount _ cs cd hD
    refine ⟨cf,?_,?_⟩
    · rw [batchPlan,cacheRun_append,hD,Option.bind_some,hR']
    · intro k hk choice hc
      cases k with
      | zero =>
        simp only [batchOutput,Nat.mul_zero,Nat.add_zero,List.getD_cons_zero]
        have hout : rowOutput n cs.length choice < cd.length := by
          rw [hdl]
          cases choice with
          | none => simp only [rowOutput]; omega
          | some j => simp only [Option.elim] at hc; simp only [rowOutput]; omega
        rw [cacheRun_preserves sourceCount _ cd cf hR _ hout]
        cases choice with
        | none => exact hDot
        | some j => exact hV j hc
      | succ k =>
        have hv := hRV k (by simp at hk; omega) choice hc
        have hi : batchOutput n cd.length k choice=batchOutput n cs.length (k+1) choice := by
          unfold batchOutput
          congr 1
          rw [hdl,Nat.mul_add,Nat.mul_one]
          omega
        rw [hi] at hv
        rw [hv,List.getD_cons_succ,heq]
        have hj : (rest.getD k default).Valid sourceCount n cs.length := by
          simpa only [List.getD_cons_succ] using! hs (k+1) (by simp at hk ⊢; omega)
        obtain ⟨hsource,hw,hwb,ha,hab⟩ := hj
        apply rowValue_append
        · omega
        · exact hwb
        · exact hab
        · exact hc

/-- A batch of width-`n` row jobs performs exactly `n * jobs.length` source reads. -/
theorem batchPlan_source_reads (n base : ℕ) (jobs : List RowJob) :
    cacheSourceReads (batchPlan n base jobs)=n*jobs.length := by
  induction jobs generalizing base with
  | nil => simp [batchPlan,cacheSourceReads]
  | cons job rest ih =>
    have ht := ih (base+5*n+1)
    have hr := rowPlan_source_reads n base job.source job.weight job.acc
    simp only [cacheSourceReads] at ht hr
    simp only [batchPlan,cacheSourceReads,List.map_append,List.sum_append,List.length_cons]
    rw [hr,ht]
    ring

/-- A batch of width-`n` row jobs performs exactly `2 * n * jobs.length` cache multiplications. -/
theorem batchPlan_multiplies (n base : ℕ) (jobs : List RowJob) :
    cacheMultiplies (batchPlan n base jobs)=2*n*jobs.length := by
  induction jobs generalizing base with
  | nil => simp [batchPlan,cacheMultiplies]
  | cons job rest ih =>
    have ht := ih (base+5*n+1)
    have hr := rowPlan_multiplies n base job.source job.weight job.acc
    simp only [cacheMultiplies] at ht hr
    simp only [batchPlan,cacheMultiplies,List.map_append,List.sum_append,List.length_cons]
    rw [hr,ht]
    ring

/-- A batch of width-`n` row jobs performs exactly `n * jobs.length` cache additions. -/
theorem batchPlan_adds (n base : ℕ) (jobs : List RowJob) :
    cacheAdds (batchPlan n base jobs)=n*jobs.length := by
  induction jobs generalizing base with
  | nil => simp [batchPlan,cacheAdds]
  | cons job rest ih =>
    have ht := ih (base+5*n+1)
    have hr := rowPlan_adds n base job.source job.weight job.acc
    simp only [cacheAdds] at ht hr
    simp only [batchPlan,cacheAdds,List.map_append,List.sum_append,List.length_cons]
    rw [hr,ht]
    ring

/-- Count copy operations in a cache program, which mark the row-output copies used by row
plans. -/
def cacheRowBuilds (p : List CacheOp) : ℕ :=
  (p.map (fun op => match op with | .copy _ => 1 | _ => 0)).sum

/-- A dot-product plan contains no row-build copy operations. -/
theorem dotPlan_row_builds (n base source weight acc : ℕ) :
    cacheRowBuilds (dotPlan n base source weight acc)=0 := by
  induction n generalizing base source weight acc with
  | zero => rfl
  | succ n ih =>
    have hh := ih (base+3) (source+1) (weight+1) (base+2)
    simp only [cacheRowBuilds] at hh
    simp only [dotPlan,cacheRowBuilds,List.map_append,List.sum_append]
    rw [hh]
    simp

/-- A scaling plan contains no row-build copy operations. -/
theorem scalePlan_row_builds (n base sourceCache dot : ℕ) :
    cacheRowBuilds (scalePlan n base sourceCache dot)=0 := by
  induction n generalizing base sourceCache dot with
  | zero => rfl
  | succ n ih =>
    have hh := ih (base+2) (sourceCache+3) dot
    simp only [cacheRowBuilds] at hh
    simp only [scalePlan,cacheRowBuilds,List.map_append,List.sum_append]
    rw [hh]
    simp

/-- A row plan contains exactly one row-build copy operation. -/
theorem rowPlan_row_builds (n base source weight acc : ℕ) :
    cacheRowBuilds (rowPlan n base source weight acc)=1 := by
  have hd := dotPlan_row_builds n base source weight acc
  have hs := scalePlan_row_builds n (base+3*n+1) base (base+3*n)
  simp only [cacheRowBuilds] at hd hs
  simp only [rowPlan,cacheRowBuilds,List.map_append,List.sum_append]
  rw [hd,hs]
  rfl

/-- A batch plan contains exactly one row-build copy operation per job. -/
theorem batchPlan_row_builds (n base : ℕ) (jobs : List RowJob) :
    cacheRowBuilds (batchPlan n base jobs)=jobs.length := by
  induction jobs generalizing base with
  | nil => rfl
  | cons job rest ih =>
    have ht := ih (base+5*n+1)
    have hr := rowPlan_row_builds n base job.source job.weight job.acc
    simp only [cacheRowBuilds] at ht hr
    simp only [batchPlan,cacheRowBuilds,List.map_append,List.sum_append,List.length_cons]
    rw [hr,ht]
    omega

/-- Compiling a batch plan produces exactly `43 * n * jobs.length` natural-number multiplication
instructions. -/
theorem batchPlan_natural_multiplies (n base : ℕ) (jobs : List RowJob) :
    (compileCache (batchPlan n base jobs)).count .multiply=43*n*jobs.length := by
  rw [compileCache_natural_multiplies,batchPlan_adds,batchPlan_multiplies]
  ring

/-- Compiling a batch plan produces exactly `28 * n * jobs.length` natural-number addition
instructions. -/
theorem batchPlan_natural_adds (n base : ℕ) (jobs : List RowJob) :
    (compileCache (batchPlan n base jobs)).count .add=28*n*jobs.length := by
  rw [compileCache_natural_adds,batchPlan_adds,batchPlan_multiplies]
  ring

/-- Construct a row job using a selected matrix row, the `i`th query vector, and the common
zero-accumulator slot. -/
def matrixRowJob (matrixRows n q r : ℕ) (rows : Fin q → Fin r → Fin matrixRows)
    (i : Fin q) (j : Fin r) : RowJob :=
  ⟨(rows i j).val*n,matrixRows*n+i.val*n,matrixRows*n+q*n⟩

/-- Every matrix-generated row job satisfies the validity bounds for the prescribed matrix and
query input layout. -/
theorem matrixRowJob_valid (matrixRows n q r : ℕ) (rows : Fin q → Fin r → Fin matrixRows)
    (i : Fin q) (j : Fin r) :
    (matrixRowJob matrixRows n q r rows i j).Valid (matrixRows*n) n (matrixRows*n+q*n+1) := by
  have hs := Nat.mul_le_mul_right n (show (rows i j).val+1 ≤ matrixRows by omega)
  have hw := Nat.mul_le_mul_right n (show i.val+1 ≤ q by omega)
  rw [Nat.add_mul,Nat.one_mul] at hs hw
  dsimp [matrixRowJob,RowJob.Valid]
  exact ⟨hs,by omega,by omega,by omega,by omega⟩

/-- Validity of an optional batch selection, requiring an in-range job index and, when present,
an in-range row-component index. -/
def batchChoiceValid (n size : ℕ) : Option (ℕ × Option ℕ) → Prop
  | none => True
  | some (k,choice) => k < size ∧ choice.elim True (fun j => j < n)

/-- Select a batch output index, using the supplied fallback index when no job is chosen. -/
def batchChoiceOutput (n base fallback : ℕ) : Option (ℕ × Option ℕ) → ℕ
  | none => fallback
  | some (k,choice) => batchOutput n base k choice

/-- Select an encoded row value from the batch specification, or the initial cache's fallback
entry. -/
def batchValue (n fallback : ℕ) (jobs : List RowJob) (cs : List GaussianCode) :
    Option (ℕ × Option ℕ) → GaussianCode
  | none => cs.getD fallback GaussianCode.zero
  | some (k,choice) =>
      let j := jobs.getD k default
      rowValue n j.source j.weight j.acc cs choice

/-- Select a Gaussian-rational row value from the batch specification, or the initial cache's
fallback entry. -/
def batchRatValue (n fallback : ℕ) (jobs : List RowJob) (cs : List GaussianRat) :
    Option (ℕ × Option ℕ) → GaussianRat
  | none => cs.getD fallback GaussianRat.zero
  | some (k,choice) =>
      let j := jobs.getD k default
      rowRatValue n j.source j.weight j.acc cs choice

/-- For valid initial cache entries, decoding a selected batch value agrees with selecting the
corresponding Gaussian-rational batch value. -/
theorem batchValue_decode (n fallback : ℕ) (jobs : List RowJob) (cs : List GaussianCode)
    (choice : Option (ℕ × Option ℕ)) (hcs : ∀ z∈cs,z.Valid) :
    (batchValue n fallback jobs cs choice).decode=batchRatValue n fallback jobs (cs.map GaussianCode.decode) choice := by
  cases choice with
  | none => exact code_decode_getD cs fallback
  | some x => exact rowValue_decode n _ _ _ cs x.2 hcs

/-- A valid output choice from an in-range job lies below the end of the batch's allocated cache
region. -/
theorem batchOutput_lt (n base size k : ℕ) (choice : Option ℕ)
    (hk : k < size) (hc : choice.elim True (fun j => j < n)) :
    batchOutput n base k choice < base+(5*n+1)*size := by
  have hh := Nat.mul_le_mul_left (5*n+1) (show k+1 ≤ size by omega)
  rw [Nat.mul_add,Nat.mul_one] at hh
  cases choice with
  | none => simp only [batchOutput,rowOutput]; omega
  | some j => simp only [Option.elim] at hc; simp only [batchOutput,rowOutput]; omega

/-- Flatten a finite rectangular family into a list in row-major order. -/
def rectangularData {α : Type u} {q r : ℕ} (make : Fin q → Fin r → α) : List α :=
  (List.ofFn (fun i : Fin q => List.ofFn (make i))).flatten

/-- Flattening a `q` by `r` rectangular family produces a list of length `q * r`. -/
theorem rectangularData_length {α : Type u} {q r : ℕ} (make : Fin q → Fin r → α) :
    (rectangularData make).length = q*r := by
  simp [rectangularData,Function.comp_def]

/-- A property holding for every entry of a rectangular family holds for every in-range default
lookup in its flattened list. -/
theorem rectangularData_getD_property {α : Type u} {q r : ℕ} (make : Fin q → Fin r → α)
    (fallback : α) (P : α → Prop) (h : ∀ i j, P (make i j))
    (k : ℕ) (hk : k < (rectangularData make).length) : P ((rectangularData make).getD k fallback) := by
  have hm : (rectangularData make).getD k fallback ∈ rectangularData make := by
    rw [List.getD_eq_getElem (rectangularData make) fallback hk]
    exact List.getElem_mem hk
  obtain ⟨row,hrow,hentry⟩ := List.mem_flatten.mp hm
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hentry
  exact hj ▸ h i j

/-- Default lookup at index `i.val * r + j.val` in the flattened rectangular family returns
`make i j`. -/
theorem rectangularData_getD_exact {α : Type u} {q r : ℕ} (make : Fin q → Fin r → α)
    (fallback : α) (i : Fin q) (j : Fin r) :
    (rectangularData make).getD (i.val*r+j.val) fallback = make i j := by
  let f : Fin (q*r) → α := fun k => make (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have hbound (i : Fin q) (j : Fin r) : i.val*r+j.val < q*r := by
    calc
      _ < i.val*r+r := Nat.add_lt_add_left j.isLt _
      _ = (i.val+1)*r := by simp [Nat.add_mul]
      _ ≤ q*r := Nat.mul_le_mul_right _ i.isLt
  have hindex (i : Fin q) (j : Fin r) :
      (⟨i.val*r+j.val,hbound i j⟩ : Fin (q*r)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*r+j.val = j.val+r*i.val
    ac_rfl
  have hFn : rectangularData make = List.ofFn f := by
    symm
    rw [List.ofFn_mul]
    unfold rectangularData
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext a
    apply congrArg List.ofFn
    funext b
    change f (⟨a.val*r+b.val,hbound a b⟩ : Fin (q*r)) = make a b
    rw [hindex]
    dsimp only [f]
    rw [Equiv.symm_apply_apply]
  rw [hFn]
  have hk : i.val*r+j.val < (List.ofFn f).length := by
    simpa only [List.length_ofFn] using! hbound i j
  rw [List.getD_eq_getElem _ fallback hk,List.getElem_ofFn]
  change f (⟨i.val*r+j.val,hbound i j⟩ : Fin (q*r)) = make i j
  rw [hindex]
  dsimp only [f]
  rw [Equiv.symm_apply_apply]

/-- The row-major list of row jobs generated from all query and selected-row indices. -/
def matrixJobs (matrixRows n q r : ℕ) (rows : Fin q → Fin r → Fin matrixRows) : List RowJob :=
  rectangularData (matrixRowJob matrixRows n q r rows)

/-- The matrix-generated job list has length `q * r`. -/
theorem matrixJobs_length (matrixRows n q r : ℕ) (rows : Fin q → Fin r → Fin matrixRows) :
    (matrixJobs matrixRows n q r rows).length=q*r := rectangularData_length _

/-- Every in-range entry of the matrix-generated job list is valid for the prescribed
input-cache layout. -/
theorem matrixJobs_valid (matrixRows n q r : ℕ) (rows : Fin q → Fin r → Fin matrixRows)
    (k : ℕ) (hk : k < (matrixJobs matrixRows n q r rows).length) :
    ((matrixJobs matrixRows n q r rows).getD k default).Valid (matrixRows*n) n (matrixRows*n+q*n+1) :=
  rectangularData_getD_property _ default _ (matrixRowJob_valid matrixRows n q r rows) k hk

/-- The batch of matrix-generated jobs performs exactly `q * n * r` source reads. -/
theorem matrixJobs_reads (matrixRows n q r base : ℕ) (rows : Fin q → Fin r → Fin matrixRows) :
    cacheSourceReads (batchPlan n base (matrixJobs matrixRows n q r rows))=q*n*r := by
  rw [batchPlan_source_reads,matrixJobs_length]
  ring

/-- The batch of matrix-generated jobs performs exactly `q * 2 * n * r` cache multiplications. -/
theorem matrixJobs_multiplies (matrixRows n q r base : ℕ) (rows : Fin q → Fin r → Fin matrixRows) :
    cacheMultiplies (batchPlan n base (matrixJobs matrixRows n q r rows))=q*2*n*r := by
  rw [batchPlan_multiplies,matrixJobs_length]
  ring

/-- The batch of matrix-generated jobs performs exactly `q * r` row builds. -/
theorem matrixJobs_row_builds (matrixRows n q r base : ℕ) (rows : Fin q → Fin r → Fin matrixRows) :
    cacheRowBuilds (batchPlan n base (matrixJobs matrixRows n q r rows))=q*r := by
  rw [batchPlan_row_builds,matrixJobs_length]

/-- The input cache containing flattened matrix entries, flattened query vectors, and one final
zero accumulator. -/
def matrixInputs {matrixRows n q : ℕ} (A : Fin matrixRows → Fin n → GaussianCode)
    (X : Fin q → Fin n → GaussianCode) : List GaussianCode :=
  rectangularData A++(rectangularData X++[GaussianCode.zero])

/-- The matrix input cache has length `matrixRows * n + q * n + 1`. -/
theorem matrixInputs_length {matrixRows n q : ℕ} (A : Fin matrixRows → Fin n → GaussianCode)
    (X : Fin q → Fin n → GaussianCode) :
    (matrixInputs A X).length=matrixRows*n+q*n+1 := by
  simp only [matrixInputs,List.length_append,List.length_cons,List.length_nil,rectangularData_length]
  omega

/-- The source portion of the matrix input cache contains `A i j` at index `i.val * n + j.val`. -/
theorem matrixInputs_source {matrixRows n q : ℕ} (A : Fin matrixRows → Fin n → GaussianCode)
    (X : Fin q → Fin n → GaussianCode) (i : Fin matrixRows) (j : Fin n) :
    (matrixInputs A X).getD (i.val*n+j.val) GaussianCode.zero=A i j := by
  have hb : i.val*n+j.val < matrixRows*n := by
    calc
      _ < i.val*n+n := Nat.add_lt_add_left j.isLt _
      _ = (i.val+1)*n := by simp [Nat.add_mul]
      _ ≤ matrixRows*n := Nat.mul_le_mul_right _ i.isLt
  rw [matrixInputs,List.getD_append _ _ _ _ (by simpa only [rectangularData_length] using! hb)]
  exact rectangularData_getD_exact A GaussianCode.zero i j

/-- The query portion of the matrix input cache contains `X i j` at index `matrixRows * n +
i.val * n + j.val`. -/
theorem matrixInputs_query {matrixRows n q : ℕ} (A : Fin matrixRows → Fin n → GaussianCode)
    (X : Fin q → Fin n → GaussianCode) (i : Fin q) (j : Fin n) :
    (matrixInputs A X).getD (matrixRows*n+i.val*n+j.val) GaussianCode.zero=X i j := by
  have hb : i.val*n+j.val < q*n := by
    calc
      _ < i.val*n+n := Nat.add_lt_add_left j.isLt _
      _ = (i.val+1)*n := by simp [Nat.add_mul]
      _ ≤ q*n := Nat.mul_le_mul_right _ i.isLt
  rw [matrixInputs,List.getD_append_right _ _ _ _ (by rw [rectangularData_length]; omega)]
  rw [show matrixRows*n+i.val*n+j.val-(rectangularData A).length=i.val*n+j.val from by rw [rectangularData_length]; omega]
  rw [List.getD_append _ _ _ _ (by simpa only [rectangularData_length] using! hb)]
  exact rectangularData_getD_exact X GaussianCode.zero i j

/-- The final entry of the matrix input cache is the zero Gaussian code. -/
theorem matrixInputs_zero {matrixRows n q : ℕ} (A : Fin matrixRows → Fin n → GaussianCode)
    (X : Fin q → Fin n → GaussianCode) :
    (matrixInputs A X).getD (matrixRows*n+q*n) GaussianCode.zero=GaussianCode.zero := by
  rw [matrixInputs,List.getD_append_right _ _ _ _ (by rw [rectangularData_length]; omega)]
  rw [show matrixRows*n+q*n-(rectangularData A).length=q*n from by rw [rectangularData_length]; omega]
  rw [List.getD_append_right _ _ _ _ (by rw [rectangularData_length])]
  simp [rectangularData_length]

/-- Valid jobs and a valid output choice yield a successful batch execution whose selected
output equals `batchValue`, including a preserved in-range fallback entry. -/
theorem batchPlan_output (sourceCount n : ℕ) (jobs : List RowJob) (cs : List GaussianCode)
    (fallback : ℕ) (choice : Option (ℕ × Option ℕ))
    (hs : ∀ k,k < jobs.length → (jobs.getD k default).Valid sourceCount n cs.length)
    (hf : sourceCount ≤ fallback) (hfb : fallback < cs.length)
    (hc : batchChoiceValid n jobs.length choice) :
    ∃ cf,cacheRun sourceCount (batchPlan n cs.length jobs) cs=some cf ∧
      cf.getD (batchChoiceOutput n cs.length fallback choice) GaussianCode.zero=batchValue n fallback jobs cs choice ∧
      batchChoiceOutput n cs.length fallback choice < cf.length ∧
      sourceCount ≤ batchChoiceOutput n cs.length fallback choice := by
  obtain ⟨cf,hR,hV⟩ := batchPlan_run sourceCount n jobs cs hs
  have hl : cf.length=cs.length+(5*n+1)*jobs.length := by
    have hh := cacheRun_length sourceCount (batchPlan n cs.length jobs) cs cf hR
    simpa only [batchPlan_length] using! hh
  refine ⟨cf,hR,?_,?_,?_⟩
  · cases choice with
    | none => exact cacheRun_preserves sourceCount _ cs cf hR fallback hfb
    | some x => exact hV x.1 hc.1 x.2 hc.2
  · cases choice with
    | none => simp only [batchChoiceOutput]; omega
    | some x =>
      change batchOutput n cs.length x.1 x.2 < cf.length
      rw [hl]
      exact batchOutput_lt n cs.length jobs.length x.1 x.2 hc.1 hc.2
  · cases choice with
    | none => exact hf
    | some x =>
      cases hh : x.2 <;> simp only [batchChoiceOutput,batchOutput,rowOutput,hh] <;> omega

/-- A property holding for every entry of a rectangular family holds for every member of its
flattened list. -/
theorem rectangularData_mem_property {α : Type u} {q r : ℕ} (make : Fin q → Fin r → α)
    (P : α → Prop) (h : ∀ i j,P (make i j)) (x : α) (hx : x∈rectangularData make) : P x := by
  obtain ⟨row,hrow,hentry⟩ := List.mem_flatten.mp hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hentry
  exact hj ▸ h i j

/-- If every matrix and query entry is a valid Gaussian code, every entry of the matrix input
cache is valid. -/
theorem matrixInputs_valid {matrixRows n q : ℕ} (A : Fin matrixRows → Fin n → GaussianCode)
    (X : Fin q → Fin n → GaussianCode) (hA : ∀ i j,(A i j).Valid) (hX : ∀ i j,(X i j).Valid) :
    ∀ z∈matrixInputs A X,z.Valid := by
  intro z hz
  simp only [matrixInputs,List.mem_append,List.mem_singleton] at hz
  rcases hz with h | h | h
  · exact rectangularData_mem_property A GaussianCode.Valid hA z h
  · exact rectangularData_mem_property X GaussianCode.Valid hX z h
  · subst z
    simp [GaussianCode.Valid,GaussianCode.zero]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
