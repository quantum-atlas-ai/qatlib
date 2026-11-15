/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalCss
public import Qatlib.Papers.MagicDistill24.Triorthogonal.U1SeventhExactThirdLevelStat

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.MagicDistill24.Triorthogonal

open Matrix

/-- Shows that every element of `ZMod 2` is zero or one. -/
private theorem zmod2_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  have hlt : b.val < 2 := b.isLt
  have h : b.val = 0 ∨ b.val = 1 := by omega
  rcases h with h | h
  · left
    have h0 : b.val = (0 : ZMod 2).val := by rw [ZMod.val_zero]; exact h
    exact ZMod.val_injective 2 h0
  · right
    have h0 : b.val = (1 : ZMod 2).val := by rw [ZMod.val_one]; exact h
    exact ZMod.val_injective 2 h0

/-- Shows that `qPhase` converts addition modulo two into multiplication of phases. -/
private theorem qPhase_add (a b : ZMod 2) : qPhase (a + b) = qPhase a * qPhase b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [qPhase, show (1 : ZMod 2) + 1 = 0 from by decide]

/-- Shows that binary phases are fixed by complex conjugation. -/
private theorem qPhase_conj (b : ZMod 2) : star (qPhase b) = qPhase b := by
  rcases zmod2_cases b with rfl | rfl <;> simp [qPhase]

/-- Shows that every binary phase is nonzero. -/
private theorem qPhase_ne_zero (b : ZMod 2) : qPhase b ≠ 0 := by
  rcases zmod2_cases b with rfl | rfl <;> simp [qPhase]

/-- Shows that equality of binary phases implies equality of their arguments. -/
private theorem qPhase_inj {a b : ZMod 2} (h : qPhase a = qPhase b) : a = b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · rfl
  · norm_num [qPhase] at h
  · norm_num [qPhase] at h
  · rfl

/-- Shows that two is zero in `F1024`. -/
private theorem char2_zero : (2 : F1024) = 0 := CharTwo.two_eq_zero

/-- Shows that every element of `F1024` added to itself is zero. -/
private theorem char2_add_self (a : F1024) : a + a = 0 := by
  linear_combination char2_zero * a

/-- Shows that raising an element of `F1024` to the field cardinality leaves it unchanged. -/
private theorem pow_card_eq (x : F1024) : x ^ (2 ^ 10) = x := by
  have h := FiniteField.pow_card (K := F1024) x
  rwa [card_F1024] at h

/-- Shows that the field trace is additive. -/
private theorem tr_add (a b : F1024) :
    f1024Trace (a + b) = f1024Trace a + f1024Trace b := map_add _ _ _

/-- Shows that the field trace of zero is zero. -/
private theorem tr_zero : f1024Trace 0 = 0 := map_zero (Algebra.trace (ZMod 2) F1024)

/-- Shows that squaring is additive in `F1024`. -/
private theorem add_pow_two (a b : F1024) : (a + b) ^ 2 = a ^ 2 + b ^ 2 :=
  add_pow_expChar (p := 2) a b

/-- Shows that taking fourth powers is additive in `F1024`. -/
private theorem add_pow_four (a b : F1024) : (a + b) ^ 4 = a ^ 4 + b ^ 4 := by
  have h1 : (a + b) ^ 4 = ((a + b) ^ 2) ^ 2 := by rw [← pow_mul]
  have h2 : ((a + b) ^ 2) ^ 2 = (a ^ 2 + b ^ 2) ^ 2 := by rw [add_pow_two]
  have h3 : (a ^ 2 + b ^ 2) ^ 2 = (a ^ 2) ^ 2 + (b ^ 2) ^ 2 := add_pow_two _ _
  have h4 : (a ^ 2) ^ 2 = a ^ 4 := by rw [← pow_mul]
  have h5 : (b ^ 2) ^ 2 = b ^ 4 := by rw [← pow_mul]
  rw [h1, h2, h3, h4, h5]

/-- Expands the seventh power of a sum in `F1024` with all binomial coefficients equal to one. -/
private theorem add_pow_seven (x y : F1024) : (x + y) ^ 7
    = x ^ 7 + x ^ 6 * y + x ^ 5 * y ^ 2 + x ^ 4 * y ^ 3 + x ^ 3 * y ^ 4
      + x ^ 2 * y ^ 5 + x * y ^ 6 + y ^ 7 := by
  have h : (x + y) ^ 7 = (x + y) ^ 4 * ((x + y) ^ 2 * (x + y)) := by ring
  rw [h, add_pow_four, add_pow_two]
  ring

/-- Expands the fifth power of a sum in `F1024` into its four surviving terms. -/
private theorem add_pow_five (x y : F1024) : (x + y) ^ 5
    = x ^ 5 + x ^ 4 * y + x * y ^ 4 + y ^ 5 := by
  have h : (x + y) ^ 5 = (x + y) ^ 4 * (x + y) := by ring
  rw [h, add_pow_four]
  ring

/-- Simplifies the square of the specified Frobenius-twisted cubic expression using the field
cardinality relation. -/
private theorem fold_sq6 (β x : F1024) :
    (β ^ (2 ^ 9) * x ^ 3) ^ 2 = x ^ 6 * β := by
  rw [mul_pow]
  have hβ : (β ^ (2 ^ 9)) ^ 2 = β := by
    rw [← pow_mul, show 2 ^ 9 * 2 = 2 ^ 10 from by ring, pow_card_eq]
  have hx : (x ^ 3) ^ 2 = x ^ 6 := by rw [← pow_mul]
  rw [hβ, hx]
  ring

/-- Simplifies the fourth power of the specified Frobenius-twisted linear expression using the
field cardinality relation. -/
private theorem fold_four43 (β x : F1024) :
    (β ^ (3 * 2 ^ 8) * x) ^ 4 = x ^ 4 * β ^ 3 := by
  rw [mul_pow]
  have hβ : (β ^ (3 * 2 ^ 8)) ^ 4 = β ^ 3 := by
    rw [← pow_mul, show 3 * 2 ^ 8 * 4 = 3 * 2 ^ 10 from by ring, pow_mul, pow_card_eq]
  rw [hβ]
  ring

/-- Simplifies the square of the specified Frobenius-twisted linear expression using the field
cardinality relation. -/
private theorem fold_sq25 (β x : F1024) :
    (β ^ (5 * 2 ^ 9) * x) ^ 2 = x ^ 2 * β ^ 5 := by
  rw [mul_pow]
  have hβ : (β ^ (5 * 2 ^ 9)) ^ 2 = β ^ 5 := by
    rw [← pow_mul, show 5 * 2 ^ 9 * 2 = 5 * 2 ^ 10 from by ring, pow_mul, pow_card_eq]
  rw [hβ]
  ring

/-- Evaluates the complex exponential at pi times the imaginary unit as minus one. -/
private theorem expIpi_one : Complex.exp (Complex.I * Real.pi * (1 : ℝ)) = -1 := by
  have h : Complex.I * Real.pi * (1 : ℝ) = Real.pi * Complex.I := by
    norm_num [mul_comm]
  rw [h, Complex.exp_mul_I, Complex.cos_pi, Complex.sin_pi]
  norm_num

/-- Identifies the exponential of pi times a binary representative times the imaginary unit with
`qPhase`. -/
private theorem expIpi_eq_qPhase (b : ZMod 2) :
    Complex.exp (Complex.I * Real.pi * ((b.val : ℕ) : ℝ)) = qPhase b := by
  rcases zmod2_cases b with rfl | rfl
  · simp [qPhase]
  · rw [ZMod.val_one, Nat.cast_one, expIpi_one]
    simp [qPhase]

/-- Shows that the qudit X operator with zero displacement is the identity. -/
private theorem x_zero : quditX 0 = 1 := by
  ext i j
  rw [quditX, Matrix.of_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

/-- Computes the matrix entries of a qudit X operator followed by a qudit Z operator. -/
private theorem xz_entry (β γ : F1024) (i j : F1024) :
    (quditX β * quditZ γ) i j
      = if i = j + β then qPhase (f1024Trace (γ * j)) else 0 := by
  have hexp : (quditX β * quditZ γ) i j
      = ∑ k : F1024, (if i = k + β then (1 : ℂ) else 0)
          * (if k = j then qPhase (f1024Trace (γ * k)) else 0) := rfl
  rw [hexp]
  by_cases h : i = j + β
  · rw [Finset.sum_eq_single j]
    · show ((if i = j + β then (1 : ℂ) else 0)
          * (if j = j then qPhase (f1024Trace (γ * j)) else 0))
        = (if i = j + β then qPhase (f1024Trace (γ * j)) else 0)
      rw [ite_eq_left h, ite_eq_left rfl, one_mul, ite_eq_left h]
    · intro k _ hk
      rw [ite_eq_right (fun hc => hk (by
          exact add_right_cancel (a := k) (b := β) (c := j) (by rw [← hc, ← h]))),
        zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  · rw [Finset.sum_eq_zero]
    · show (0 : ℂ) = (if i = j + β then qPhase (f1024Trace (γ * j)) else 0)
      rw [ite_eq_right h]
    · intro k _
      by_cases hk : k = j
      · rw [ite_eq_right (fun hc => h (by rw [hc, hk])), zero_mul]
      · rw [ite_eq_right hk, mul_zero]

/-- Shows that the field trace is invariant under squaring. -/
private theorem tr_pow_two (x : F1024) : f1024Trace (x^2) = f1024Trace x := by
  simpa only [f1024Trace,FiniteField.coe_frobeniusAlgEquivOfAlgebraic,ZMod.card]
    using Algebra.trace_eq_of_algEquiv
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F1024) x

/-- Shows that the field trace is invariant under taking fourth powers. -/
private theorem tr_pow_four (x : F1024) : f1024Trace (x^4) = f1024Trace x := by
  rw [show x^4 = (x^2)^2 by ring,tr_pow_two,tr_pow_two]

/-- Moves a square from the variable to a Frobenius power of its coefficient inside the trace. -/
private theorem tr_mul_sq (a x : F1024) :
    f1024Trace (a*x^2) = f1024Trace (a^(2^9)*x) := by
  have he : (a^(2^9)*x)^2 = a*x^2 := by
    rw [mul_pow,← pow_mul]
    rw [show 2^9*2 = 2^10 by ring,pow_card_eq]
  rw [← he,tr_pow_two]

/-- Moves a fourth power from the variable to a Frobenius power of its coefficient inside the
trace. -/
private theorem tr_mul_four (a x : F1024) :
    f1024Trace (a*x^4) = f1024Trace (a^(2^8)*x) := by
  have he : (a^(2^8)*x)^4 = a*x^4 := by
    rw [mul_pow,← pow_mul]
    rw [show 2^8*4 = 2^10 by ring,pow_card_eq]
  rw [← he,tr_pow_four]

/-- Expresses a binary phase as a power of the imaginary unit. -/
private theorem qPhase_i_pow (d : ZMod 2) : qPhase d = Complex.I^(2*d.val) := by
  rcases zmod2_cases d with rfl | rfl
  · simp [qPhase]
  · rw [qPhase_one,ZMod.val_one]
    norm_num [Complex.I_sq]

/-- Shows that adding the same displacement twice in `F1024` returns the original element. -/
private theorem shift_twice (x b : F1024) : (x+b)+b = x := by
  rw [add_assoc,char2_add_self,add_zero]

private noncomputable def signedShift (b : F1024) (f : F1024 → ZMod 2) :
    Matrix F1024 F1024 ℂ := quditX b * Matrix.diagonal (fun x => qPhase (f x))

/-- Computes the entries of a signed shift as a phase on its translated diagonal and zero
elsewhere. -/
private theorem signedShift_entry (b : F1024) (f : F1024 → ZMod 2) (i j : F1024) :
    signedShift b f i j = if i=j+b then qPhase (f j) else 0 := by
  simp [signedShift,Matrix.mul_diagonal,quditX,ite_mul]

/-- Expresses a product of signed shifts as the combined shift with the appropriately translated
phase function. -/
private theorem signedShift_mul (b c : F1024) (f g : F1024 → ZMod 2) :
    signedShift b f * signedShift c g =
      signedShift (b+c) (fun x => f (x+c)+g x) := by
  ext i j
  simp only [Matrix.mul_apply,signedShift_entry]
  rw [Finset.sum_eq_single (j+c)]
  · by_cases h : i=j+(b+c)
    · have he : i=(j+c)+b := by rw [h]; abel
      rw [ite_eq_left he,ite_eq_left rfl,ite_eq_left h,qPhase_add]
    · have he : i≠(j+c)+b := by
        intro he
        apply h
        rw [he]
        abel
      rw [ite_eq_right he,ite_eq_right h,zero_mul]
  · intro k _ hk
    rw [ite_eq_right hk,mul_zero]
  · simp

/-- Computes the conjugate transpose of a signed shift by translating its phase function. -/
private theorem signedShift_conjTranspose (b : F1024) (f : F1024 → ZMod 2) :
    (signedShift b f)ᴴ = signedShift b (fun x => f (x+b)) := by
  ext i j
  simp only [Matrix.conjTranspose_apply,signedShift_entry]
  by_cases h : i=j+b
  · subst i
    simp [shift_twice,qPhase_conj]
  · have he : j≠i+b := by
      intro he
      apply h
      rw [he,shift_twice]
    simp [h,he]

/-- Identifies a signed shift with zero displacement as a diagonal phase matrix. -/
private theorem signedShift_zero (f : F1024 → ZMod 2) :
    signedShift 0 f = Matrix.diagonal (fun x => qPhase (f x)) := by
  rw [signedShift,x_zero,Matrix.one_mul]

/-- Shows that a signed shift with affine trace phase, multiplied by a power of the imaginary
unit, is a qudit Pauli. -/
private theorem ipow_signedShift_pauli (a : ℕ) (b c : F1024) (d : ZMod 2)
    (f : F1024 → ZMod 2) (hf : ∀ x, f x = f1024Trace (c*x)+d) :
    IsQuditPauli (Complex.I^a • signedShift b f) := by
  refine ⟨a+2*d.val,b,c,?_⟩
  ext i j
  simp only [Matrix.smul_apply,smul_eq_mul,signedShift_entry,xz_entry,pow_add]
  by_cases h : i=j+b
  · simp only [ite_eq_left h,hf,qPhase_add,← qPhase_i_pow]
    ring
  · simp [h]

private def AffineDerivative (f : F1024 → ZMod 2) : Prop :=
  ∀ t, ∃ c d, ∀ x, f (x+t)+f x = f1024Trace (c*x)+d

/-- Shows that a signed shift whose phase has affine derivatives is a qudit Clifford. -/
private theorem signedShift_clifford (b : F1024) (f : F1024 → ZMod 2)
    (hf : AffineDerivative f) : IsQuditClifford (signedShift b f) := by
  intro P hP
  rcases hP with ⟨a,t,eta,rfl⟩
  change IsQuditPauli (signedShift b f *
    (Complex.I^a • signedShift t (fun x => f1024Trace (eta*x))) * (signedShift b f)ᴴ)
  rw [Matrix.mul_smul,Matrix.smul_mul,signedShift_conjTranspose,signedShift_mul,
    signedShift_mul]
  have hb : b+t+b = t := by
    calc _ = (t+b)+b := by abel
         _ = t := shift_twice t b
  rw [hb]
  obtain ⟨c,d,h⟩ := hf t
  apply ipow_signedShift_pauli a t (c+eta) (d+f1024Trace ((c+eta)*b))
  intro x
  have hh := h (x+b)
  calc f (x+b+t) + f1024Trace (eta*(x+b)) + f (x+b)
      = (f (x+b+t)+f (x+b)) + f1024Trace (eta*(x+b)) := by abel
    _ = (f1024Trace (c*(x+b))+d) + f1024Trace (eta*(x+b)) := by rw [hh]
    _ = f1024Trace ((c+eta)*x) + (d+f1024Trace ((c+eta)*b)) := by
      simp only [mul_add,add_mul,tr_add]
      abel

/-- Shows that multiplying a qudit Clifford by a power of the imaginary unit preserves the
Clifford property. -/
private theorem ipow_smul_clifford (a : ℕ) {U : Matrix F1024 F1024 ℂ}
    (hU : IsQuditClifford U) : IsQuditClifford (Complex.I^a • U) := by
  intro P hP
  have hc : Complex.I^a * star (Complex.I^a) = 1 := by
    rw [star_pow,← mul_pow]
    simp
  have he : (Complex.I^a • U) * P * (Complex.I^a • U)ᴴ = U*P*Uᴴ := by
    simp only [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    rw [mul_comm (star (Complex.I^a)) (Complex.I^a),hc,one_smul]
  rw [he]
  exact hU P hP

/-- Shows that every element of `ZMod 2` added to itself is zero. -/
private theorem zmod_add_self (a : ZMod 2) : a+a=0 := by
  have h2 : (2 : ZMod 2)=0 := by decide
  linear_combination h2*a

/-- Cancels a repeated trace term from the trace of a sum. -/
private theorem trace_double_cancel (a b : F1024) :
    f1024Trace (a+b)+f1024Trace a = f1024Trace b := by
  rw [tr_add]
  calc _ = (f1024Trace a+f1024Trace a)+f1024Trace b := by abel
       _ = f1024Trace b := by rw [zmod_add_self,zero_add]

/-- Expands the cube of a sum in `F1024` with all binomial coefficients equal to one. -/
private theorem add_pow_three (x y : F1024) :
    (x+y)^3 = x^3+x^2*y+x*y^2+y^3 := by
  rw [show (x+y)^3 = (x+y)^2*(x+y) by ring,add_pow_two]
  ring

private noncomputable def quadTrace (a b c d : F1024) (x : F1024) : ZMod 2 :=
  f1024Trace (a*x^5+b*x^3+c*x+d)

/-- Shows that `quadTrace` has affine derivatives. -/
private theorem quadTrace_affineDerivative (a b c d : F1024) :
    AffineDerivative (quadTrace a b c d) := by
  intro t
  refine ⟨(a*t)^(2^8)+(b*t)^(2^9)+a*t^4+b*t^2,
    f1024Trace (a*t^5+b*t^3+c*t),?_⟩
  intro x
  have he : a*(x+t)^5+b*(x+t)^3+c*(x+t)+d =
      (a*x^5+b*x^3+c*x+d) +
      ((a*t)*x^4+(b*t)*x^2+(a*t^4+b*t^2)*x+(a*t^5+b*t^3+c*t)) := by
    rw [add_pow_five,add_pow_three]
    ring
  unfold quadTrace
  rw [he,trace_double_cancel]
  simp only [tr_add,tr_mul_four,tr_mul_sq,add_mul]
  abel

/-- Expresses the derivative of the seventh-power trace as the specified quadratic trace
function. -/
private theorem seventh_trace_derivative (b x : F1024) :
    f1024Trace ((x+b)^7)+f1024Trace (x^7) =
      quadTrace (b^2) (b^(2^9)+b^4) (b^(3*2^8)+b^(5*2^9)+b^6) (b^7) x := by
  have he : (x+b)^7 = x^7+
      (x^6*b+x^5*b^2+x^4*b^3+x^3*b^4+x^2*b^5+x*b^6+b^7) := by
    rw [add_pow_seven]
    ring
  rw [he,trace_double_cancel]
  simp only [tr_add]
  rw [← fold_sq6 b x,← fold_four43 b x,← fold_sq25 b x,tr_pow_two,tr_pow_four,
    tr_pow_two]
  simp only [quadTrace,add_mul,tr_add]
  rw [mul_comm (x^5) (b^2),mul_comm (x^3) (b^4),mul_comm x (b^6)]
  abel

/-- Computes conjugation of a phased signed shift by a diagonal signed shift. -/
private theorem signedDiagonal_conj (a : ℕ) (b eta : F1024) (f : F1024 → ZMod 2) :
    signedShift 0 f * (Complex.I^a • signedShift b (fun x => f1024Trace (eta*x))) *
      (signedShift 0 f)ᴴ =
    Complex.I^a • signedShift b (fun x => f (x+b)+f1024Trace (eta*x)+f x) := by
  rw [Matrix.mul_smul,Matrix.smul_mul,signedShift_conjTranspose,signedShift_mul,
    signedShift_mul]
  simp only [zero_add,add_zero]

/-- Expresses `u1Seventh` as the diagonal signed shift defined by the seventh-power trace. -/
private theorem u1Seventh_signed :
    u1Seventh = signedShift 0 (fun x => f1024Trace (x^7)) := by
  rw [signedShift_zero]
  unfold u1Seventh
  congr 1
  funext x
  exact expIpi_eq_qPhase (f1024Trace (x^7))

/-- Shows that `u1Seventh` belongs to the third level of the qudit Clifford hierarchy. -/
private theorem seventh_third_level : InQuditThirdLevel u1Seventh := by
  intro P hP
  rcases hP with ⟨a,b,eta,rfl⟩
  rw [u1Seventh_signed]
  change IsQuditClifford (signedShift 0 (fun x => f1024Trace (x^7)) *
    (Complex.I^a • signedShift b (fun x => f1024Trace (eta*x))) *
    (signedShift 0 (fun x => f1024Trace (x^7)))ᴴ)
  rw [signedDiagonal_conj]
  apply ipow_smul_clifford
  apply signedShift_clifford
  have he : (fun x => f1024Trace ((x+b)^7)+f1024Trace (eta*x)+f1024Trace (x^7)) =
      quadTrace (b^2) (b^(2^9)+b^4) (b^(3*2^8)+b^(5*2^9)+b^6+eta) (b^7) := by
    funext x
    calc _ = (f1024Trace ((x+b)^7)+f1024Trace (x^7))+f1024Trace (eta*x) := by abel
         _ = _ := by
           rw [seventh_trace_derivative]
           simp only [quadTrace,add_mul,tr_add]
           abel
  rw [he]
  exact quadTrace_affineDerivative _ _ _ _

/-- Shows that the phase function of a signed shift that is a qudit Pauli is an affine trace
function. -/
private theorem signedShift_pauli_affine {b : F1024} {f : F1024 → ZMod 2}
    (hP : IsQuditPauli (signedShift b f)) :
    ∃ c d, ∀ x, f x = f1024Trace (c*x)+d := by
  rcases hP with ⟨a,c,eta,he⟩
  have hc : c=b := by
    by_contra hn
    have hh := congrArg (fun M : Matrix F1024 F1024 ℂ => M b 0) he
    have hh0 : qPhase (f 0)=0 := by
      simpa [signedShift_entry,xz_entry,Ne.symm hn] using hh
    exact qPhase_ne_zero (f 0) hh0
  subst c
  have he0 : qPhase (f 0)=Complex.I^a := by
    have hh := congrArg (fun M : Matrix F1024 F1024 ℂ => M b 0) he
    simpa [signedShift_entry,xz_entry,f1024Trace,qPhase_zero] using hh
  refine ⟨eta,f 0,?_⟩
  intro x
  apply qPhase_inj
  have hh := congrArg (fun M : Matrix F1024 F1024 ℂ => M (x+b) x) he
  have hhx : qPhase (f x)=Complex.I^a*qPhase (f1024Trace (eta*x)) := by
    simpa only [Matrix.smul_apply,smul_eq_mul,signedShift_entry,xz_entry,ite_eq_left rfl] using! hh
  rw [qPhase_add,hhx,← he0]
  exact mul_comm _ _

/-- Produces a field element whose indicated Frobenius and fourth powers have nonzero sum. -/
private theorem exists_fourth_trace_polarizer : ∃ y : F1024, y^(2^8)+y^4≠0 := by
  classical
  by_contra! hf
  let p : Polynomial F1024 := Polynomial.X^256+Polynomial.X^4
  have hdegree : p.natDegree ≤ 256 := by
    have hg := Polynomial.natDegree_add_le
      (Polynomial.X^256 : Polynomial F1024) (Polynomial.X^4 : Polynomial F1024)
    simp only [Polynomial.natDegree_X_pow] at hg
    exact hg.trans (by norm_num)
  have hp : p=0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    Function.injective_id (fun x => by simpa [p] using hf x)
    (by rw [card_F1024]; exact hdegree.trans_lt (by norm_num))
  have hh := congrArg (fun q : Polynomial F1024 => q.coeff 256) hp
  norm_num [p] at hh

/-- Shows that the trace of `x^5 + x + 1` cannot be represented as an affine trace function. -/
private theorem fifth_trace_not_affine :
    ¬ (∃ c d, ∀ x : F1024, f1024Trace (x^5+x+1)=f1024Trace (c*x)+d) := by
  intro ⟨c,d,h⟩
  have hpolar (x y : F1024) : f1024Trace (x^4*y+x*y^4)=0 := by
    have he : (x+y)^5+(x+y)+1 =
        (x^5+x+1)+(y^5+y+1)+(0^5+0+1)+(x^4*y+x*y^4) := by
      rw [add_pow_five]
      linear_combination -char2_zero
    have ht : f1024Trace ((x+y)^5+(x+y)+1) =
        f1024Trace (x^5+x+1)+f1024Trace (y^5+y+1)+f1024Trace (0^5+0+1)+
        f1024Trace (x^4*y+x*y^4) := by
      rw [he,tr_add,tr_add,tr_add]
    rw [h (x+y),h x,h y,h 0] at ht
    rw [mul_add,tr_add] at ht
    simp only [mul_zero,tr_zero,zero_add] at ht
    have h2 : (2 : ZMod 2)=0 := by decide
    linear_combination -ht - h2*d
  obtain ⟨y,hy⟩ := exists_fourth_trace_polarizer
  apply hy
  apply (traceForm_nondegenerate (ZMod 2) F1024).1
  intro x
  rw [Algebra.traceForm_apply]
  change f1024Trace ((y^(2^8)+y^4)*x)=0
  calc _ = f1024Trace (x^4*y+x*y^4) := by
         rw [add_mul,tr_add,← tr_mul_four y x,← tr_add]
         congr 1
         ring
       _ = 0 := hpolar x y

/-- Shows that `u1Seventh` is not a qudit Clifford. -/
private theorem seventh_non_clifford : ¬IsQuditClifford u1Seventh := by
  intro hU
  let f : F1024 → ZMod 2 := fun x => f1024Trace (x^7)
  have hp := hU (Complex.I^0 • signedShift 1 (fun x => f1024Trace (0*x)))
    ⟨0,1,0,rfl⟩
  rw [u1Seventh_signed,signedDiagonal_conj] at hp
  simp only [pow_zero,one_smul,zero_mul,tr_zero,add_zero] at hp
  obtain ⟨c,d,h⟩ := signedShift_pauli_affine hp
  apply fifth_trace_not_affine
  refine ⟨c,d,?_⟩
  intro x
  have he := seventh_trace_derivative 1 x
  simp only [one_pow,char2_add_self,zero_add,quadTrace,one_mul,zero_mul,add_zero] at he
  exact he.symm.trans (h x)

/-- Establishes that `u1Seventh` lies exactly at the third level of the qudit Clifford
hierarchy. -/
theorem u1SeventhExactThirdLevel : U1SeventhExactThirdLevel :=
  ⟨seventh_third_level,seventh_non_clifford⟩

end Qatlib.Papers.MagicDistill24.Triorthogonal
