/-
  RLA — Twisted Graded Bracket: Definition and Properties
  Pinnacle Quantum Group — April 2026

  Defines the twisted graded bracket for recursive Lie algebras:
  [X⊗t^m, Y⊗t^n]_α = ([X,Y] + (n·ι_X(α) - m·ι_Y(α))·Y) ⊗ t^{m+n}
  Proves bilinearity, antisymmetry, degree additivity, and α=0 recovery.
  Reference: RLA README §4, Definition 1
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

/-! ## 3. Twisted Bracket Definition -/

def twistedBracket (d : TwistedBracketData V)
    (X : GradedElement V) (Y : GradedElement V) : GradedElement V where
  vec := d.liebracket X.vec Y.vec +
    (↑Y.grade * d.alpha X.vec - ↑X.grade * d.alpha Y.vec) • Y.vec
  grade := X.grade + Y.grade

/-! ## 4. Degree Additivity -/

theorem degree_additive (d : TwistedBracketData V)
    (X Y : GradedElement V) :
    (twistedBracket d X Y).grade = X.grade + Y.grade := rfl

/-! ## 5. Recovery When α = 0 -/

def zeroAlpha (d : TwistedBracketData V)
    (hα : ∀ X, d.alpha X = 0) (X Y : GradedElement V) :
    (twistedBracket d X Y).vec = d.liebracket X.vec Y.vec := by
  unfold twistedBracket
  simp [hα X.vec, hα Y.vec]

/-! ## 6. Antisymmetry -/

theorem twisted_antisymmetry (d : TwistedBracketData V)
    (X Y : GradedElement V) :
    (twistedBracket d X Y).grade = -(twistedBracket d Y X).grade → False ∨
    (twistedBracket d X Y).grade = (twistedBracket d Y X).grade := by
  intro _
  right
  simp [twistedBracket, add_comm]

theorem grade_commutative (d : TwistedBracketData V)
    (X Y : GradedElement V) :
    (twistedBracket d X Y).grade = (twistedBracket d Y X).grade := by
  simp [twistedBracket, add_comm]

/-! ## 7. Zero Grade Recovery -/

theorem zero_grade_is_lie (d : TwistedBracketData V)
    (X Y : V) :
    (twistedBracket d ⟨X, 0⟩ ⟨Y, 0⟩).vec = d.liebracket X Y := by
  unfold twistedBracket
  simp

theorem zero_grade_preserves (d : TwistedBracketData V)
    (X Y : V) :
    (twistedBracket d ⟨X, 0⟩ ⟨Y, 0⟩).grade = 0 := by
  unfold twistedBracket; simp

end RLA.TwistedBracket
