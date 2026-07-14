/-
  RLA — Twisted Graded Bracket: Definition and Properties
  Pinnacle Quantum Group — April 2026

  Defines the twisted graded bracket for recursive Lie algebras:
  [X⊗t^m, Y⊗t^n]_α = ([X,Y] + n·ι_X(α)·Y - m·ι_Y(α)·X) ⊗ t^{m+n}
  following the Leibniz expansion of README Appendices D/E.

  NOTE: the boxed README §4 Definition 1 contains a typo — its final term
  reads (n·ι_X(α) - m·ι_Y(α))·Y, with the last factor Y instead of X.
  That formula is NOT antisymmetric; `readme_defn1_not_antisymmetric`
  below exhibits a concrete counterexample, and the definition here uses
  the corrected form derived in the README's own Appendices D and E.

  Proves: vec-level antisymmetry, additivity of the bracket in each
  vector argument, degree additivity, and recovery of the plain Lie
  bracket when α = 0 or when both grades vanish.
  Reference: RLA README §4, Definition 1 (as corrected by Appendices D/E)
-/
import Mathlib

noncomputable section

namespace RLA.TwistedBracket

/-! ## 1. Graded Vector Space Elements -/

structure GradedElement (V : Type*) [AddCommGroup V] where
  vec : V
  grade : ℤ

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ## 2. Abstract α-Twist Model
    We model ι_X(α) as a linear functional V → ℝ -/

structure TwistedBracketData (V : Type*) [AddCommGroup V] [Module ℝ V] where
  liebracket : V → V → V
  alpha : V → ℝ
  lie_antisymm : ∀ X Y, liebracket X Y = -liebracket Y X
  lie_bilinear_l : ∀ X Y Z, liebracket (X + Y) Z = liebracket X Z + liebracket Y Z
  alpha_linear : ∀ X Y, alpha (X + Y) = alpha X + alpha Y

/-- Additivity of the underlying bracket in its second argument, derived
    from antisymmetry together with left additivity. -/
theorem lie_add_right (d : TwistedBracketData V) (X Y Z : V) :
    d.liebracket X (Y + Z) = d.liebracket X Y + d.liebracket X Z := by
  rw [d.lie_antisymm X (Y + Z), d.lie_bilinear_l, d.lie_antisymm Y X,
    d.lie_antisymm Z X]
  abel

/-! ## 3. Twisted Bracket Definition
    Corrected form (README Appendices D/E):
    vec = [X,Y] + n·α(X)·Y - m·α(Y)·X  for grades m = deg X, n = deg Y. -/

def twistedBracket (d : TwistedBracketData V)
    (X : GradedElement V) (Y : GradedElement V) : GradedElement V where
  vec := d.liebracket X.vec Y.vec +
    (↑Y.grade * d.alpha X.vec) • Y.vec - (↑X.grade * d.alpha Y.vec) • X.vec
  grade := X.grade + Y.grade

/-! ## 4. Degree Additivity -/

theorem degree_additive (d : TwistedBracketData V)
    (X Y : GradedElement V) :
    (twistedBracket d X Y).grade = X.grade + Y.grade := rfl

/-! ## 5. Recovery When α = 0 -/

theorem zeroAlpha (d : TwistedBracketData V)
    (hα : ∀ X, d.alpha X = 0) (X Y : GradedElement V) :
    (twistedBracket d X Y).vec = d.liebracket X.vec Y.vec := by
  unfold twistedBracket
  simp [hα X.vec, hα Y.vec]

/-! ## 6. Antisymmetry -/

/-- Genuine antisymmetry of the twisted bracket at the level of vector
    components: swapping the arguments negates the bracket.  This holds
    for the corrected definition with no extra hypotheses; it fails for
    the boxed README Definition 1 (see
    `readme_defn1_not_antisymmetric`). -/
theorem twisted_antisymmetry (d : TwistedBracketData V)
    (X Y : GradedElement V) :
    (twistedBracket d X Y).vec = -(twistedBracket d Y X).vec := by
  simp only [twistedBracket]
  rw [d.lie_antisymm X.vec Y.vec]
  abel

/-- The grade of the twisted bracket is symmetric in its arguments
    (m + n = n + m); the vector component is anti-symmetric
    (`twisted_antisymmetry`). -/
theorem grade_commutative (d : TwistedBracketData V)
    (X Y : GradedElement V) :
    (twistedBracket d X Y).grade = (twistedBracket d Y X).grade := by
  simp [twistedBracket, add_comm]

/-! ## 7. Additivity in Each Vector Argument -/

/-- The twisted bracket is additive in the first vector argument
    (at fixed grades). -/
theorem twisted_add_left (d : TwistedBracketData V)
    (X₁ X₂ Y : V) (m n : ℤ) :
    (twistedBracket d ⟨X₁ + X₂, m⟩ ⟨Y, n⟩).vec =
      (twistedBracket d ⟨X₁, m⟩ ⟨Y, n⟩).vec +
        (twistedBracket d ⟨X₂, m⟩ ⟨Y, n⟩).vec := by
  simp only [twistedBracket, d.lie_bilinear_l, d.alpha_linear, mul_add,
    add_smul, smul_add]
  abel

/-- The twisted bracket is additive in the second vector argument
    (at fixed grades). -/
theorem twisted_add_right (d : TwistedBracketData V)
    (X Y₁ Y₂ : V) (m n : ℤ) :
    (twistedBracket d ⟨X, m⟩ ⟨Y₁ + Y₂, n⟩).vec =
      (twistedBracket d ⟨X, m⟩ ⟨Y₁, n⟩).vec +
        (twistedBracket d ⟨X, m⟩ ⟨Y₂, n⟩).vec := by
  simp only [twistedBracket, lie_add_right, d.alpha_linear, mul_add,
    add_smul, smul_add]
  abel

/-! ## 8. Zero Grade Recovery -/

theorem zero_grade_is_lie (d : TwistedBracketData V)
    (X Y : V) :
    (twistedBracket d ⟨X, 0⟩ ⟨Y, 0⟩).vec = d.liebracket X Y := by
  unfold twistedBracket
  simp

theorem zero_grade_preserves (d : TwistedBracketData V)
    (X Y : V) :
    (twistedBracket d ⟨X, 0⟩ ⟨Y, 0⟩).grade = 0 := by
  unfold twistedBracket; simp

/-! ## 9. The Boxed README Definition 1 Is Not Antisymmetric
    The formula as boxed in README §4 Definition 1 ends in ·Y where the
    Leibniz expansion of Appendices D/E produces ·X.  We record that the
    boxed transcription cannot be a Lie bracket: it fails antisymmetry. -/

/-- The vector part of the bracket exactly as boxed in README §4
    Definition 1: `[X,Y] + (n·ι_X(α) - m·ι_Y(α))·Y`.  This transcription
    (final factor `Y` rather than `X`) is a typo. -/
def readmeDefn1Vec (d : TwistedBracketData V) (X Y : GradedElement V) : V :=
  d.liebracket X.vec Y.vec +
    (↑Y.grade * d.alpha X.vec - ↑X.grade * d.alpha Y.vec) • Y.vec

/-- Witness data for the counterexample: V = ℝ with the zero bracket and
    α the identity functional. -/
def flatLineData : TwistedBracketData ℝ where
  liebracket := fun _ _ => 0
  alpha := id
  lie_antisymm := fun _ _ => neg_zero.symm
  lie_bilinear_l := fun _ _ _ => (add_zero (0 : ℝ)).symm
  alpha_linear := fun _ _ => rfl

/-- The boxed README Definition 1 formula is NOT antisymmetric: with
    V = ℝ, zero bracket, α = id, X = 1⊗t⁰ and Y = 2⊗t¹ it evaluates to
    2 in one order and -1 in the other.  The corrected definition
    `twistedBracket` (with final term m·ι_Y(α)·X) is antisymmetric —
    see `twisted_antisymmetry`. -/
theorem readme_defn1_not_antisymmetric :
    ∃ (d : TwistedBracketData ℝ) (X Y : GradedElement ℝ),
      readmeDefn1Vec d X Y ≠ -readmeDefn1Vec d Y X := by
  refine ⟨flatLineData, ⟨1, 0⟩, ⟨2, 1⟩, ?_⟩
  simp only [readmeDefn1Vec, flatLineData, id_eq, smul_eq_mul,
    Int.cast_zero, Int.cast_one]
  norm_num

end RLA.TwistedBracket
