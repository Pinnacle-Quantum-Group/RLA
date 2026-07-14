/-
  RLA — Jacobi Identity for the Twisted Bracket (Theorem T2)
  Pinnacle Quantum Group — April 2026

  Proves the Jacobi identity for the genuinely twisted graded bracket
    [X,Y]_α = [x,y] + (n·α x)•y − (m·α y)•x   (grades m, n).
  Key insight: α is closed (dα = 0, since α = d(ln D)).  In this
  constant-coefficient algebraic model the derivation action X(ι_Y α)
  is inexpressible, so closedness shadows to the hypothesis
  α ∘ [·,·] = 0; it is exactly what kills the α([·,·]) cross-terms in
  the twisted Jacobiator, while the α·α cross-terms cancel identically.
  A non-abelian model (the affine algebra of the line) discharges the
  hypothesis with α ≠ 0, so the main theorem is non-vacuously applicable.
  Reference: RLA README §5, Appendix A.1
-/
import Mathlib

noncomputable section

namespace RLA.JacobiIdentity

/-! ## 1. Simplified Algebraic Model
    Work with a Lie algebra L with an α-functional to prove Jacobi.
    The bracket is bilinear; only right-slot linearity is axiomatized,
    since the left slot follows from antisymmetry where needed. -/

structure LieAlgWithAlpha where
  L : Type*
  [inst_acg : AddCommGroup L]
  [inst_mod : Module ℝ L]
  bracket : L → L → L
  alpha : L → ℝ
  lie_antisymm : ∀ X Y, bracket X Y = -bracket Y X
  lie_jacobi : ∀ X Y Z,
    bracket X (bracket Y Z) + bracket Y (bracket Z X) + bracket Z (bracket X Y) = 0
  bracket_add_right : ∀ X Y Z, bracket X (Y + Z) = bracket X Y + bracket X Z
  bracket_smul_right : ∀ (r : ℝ) X Y, bracket X (r • Y) = r • bracket X Y
  alpha_linear : ∀ X Y, alpha (X + Y) = alpha X + alpha Y
  alpha_smul : ∀ (r : ℝ) X, alpha (r • X) = r * alpha X

attribute [instance] LieAlgWithAlpha.inst_acg LieAlgWithAlpha.inst_mod

variable (A : LieAlgWithAlpha)

theorem bracket_neg_right (X Y : A.L) : A.bracket X (-Y) = -A.bracket X Y := by
  have h := A.bracket_smul_right (-1 : ℝ) X Y
  simpa [neg_one_smul] using h

theorem bracket_sub_right (X Y Z : A.L) :
    A.bracket X (Y - Z) = A.bracket X Y - A.bracket X Z := by
  rw [sub_eq_add_neg, A.bracket_add_right, bracket_neg_right, ← sub_eq_add_neg]

theorem alpha_neg (X : A.L) : A.alpha (-X) = -A.alpha X := by
  have h := A.alpha_smul (-1 : ℝ) X
  simpa [neg_one_smul] using h

theorem alpha_sub (X Y : A.L) : A.alpha (X - Y) = A.alpha X - A.alpha Y := by
  rw [sub_eq_add_neg, A.alpha_linear, alpha_neg, ← sub_eq_add_neg]

/-! ## 2. Graded Elements -/

structure GElem where
  v : A.L
  n : ℤ

/-! ## 3. Twisted Bracket
    `[X,Y]_α = [x,y] + (n·α x)•y − (m·α y)•x` for grades `m = X.n`, `n = Y.n`.
    The α-twist terms are the algebraic residue of the Weyl rescaling. -/

def tb (X Y : GElem A) : GElem A where
  v := A.bracket X.v Y.v
      + ((Y.n : ℝ) * A.alpha X.v) • Y.v
      - ((X.n : ℝ) * A.alpha Y.v) • X.v
  n := X.n + Y.n

theorem tb_v (X Y : GElem A) :
    (tb A X Y).v = A.bracket X.v Y.v
      + ((Y.n : ℝ) * A.alpha X.v) • Y.v
      - ((X.n : ℝ) * A.alpha Y.v) • X.v := rfl

theorem tb_n (X Y : GElem A) : (tb A X Y).n = X.n + Y.n := rfl

/-! ## 4. Jacobi Identity for Pure Lie Part -/

theorem lie_jacobi_identity (X Y Z : GElem A) :
    A.bracket X.v (A.bracket Y.v Z.v) +
    A.bracket Y.v (A.bracket Z.v X.v) +
    A.bracket Z.v (A.bracket X.v Y.v) = 0 :=
  A.lie_jacobi X.v Y.v Z.v

/-! ## 5. Grade Additivity Under Jacobi -/

theorem jacobi_grade_consistency (X Y Z : GElem A) :
    (tb A X (tb A Y Z)).n = X.n + Y.n + Z.n := by
  unfold tb; ring

theorem jacobi_grades_equal (X Y Z : GElem A) :
    (tb A X (tb A Y Z)).n = (tb A Y (tb A Z X)).n ∧
    (tb A Y (tb A Z X)).n = (tb A Z (tb A X Y)).n := by
  unfold tb; constructor <;> ring

/-! ## 6. Closure of α: Key Cancellation Property
    Since α = d(ln D) and d² = 0, α is exact hence closed.  The geometric
    identity ι_{[X,Y]}α = X(ι_Y α) − Y(ι_X α) is inexpressible in this
    constant-coefficient model (α is a bare functional, with no derivation
    acting on it), so dα = 0 shadows to the honest algebraic hypothesis
    `h_closed : ∀ X Y, α [X,Y] = 0`.  Under it, α of a twisted bracket is
    computed exactly: only the antisymmetric α·α cross-term survives.  This
    is the quantitative cancellation that drives the twisted Jacobi proof. -/

theorem alpha_closure_enables_jacobi
    (h_closed : ∀ a b, A.alpha (A.bracket a b) = 0) (X Y : GElem A) :
    A.alpha (tb A X Y).v
      = ((Y.n : ℝ) - (X.n : ℝ)) * (A.alpha X.v * A.alpha Y.v) := by
  rw [tb_v, alpha_sub, A.alpha_linear, A.alpha_smul, A.alpha_smul, h_closed]
  ring

/-! ## 7. Full Twisted Jacobi -/

/-- **Theorem T2 (twisted Jacobi).**  The cyclic sum of vector components of
    the twisted bracket vanishes, given closedness of α
    (`α ∘ [·,·] = 0`, the algebraic residue of dα = 0).  The hypothesis is
    load-bearing: it kills the three `α [·,·]` cross-terms, while the α·α
    cross-terms cancel identically and the pure triple brackets cancel by
    the Jacobi axiom.  Together with `jacobi_grades_equal` (the grade
    components of the three Jacobiator terms agree), this is the full
    graded statement. -/
theorem twisted_jacobi_holds (h_closed : ∀ a b, A.alpha (A.bracket a b) = 0)
    (X Y Z : GElem A) :
    (tb A X (tb A Y Z)).v + (tb A Y (tb A Z X)).v + (tb A Z (tb A X Y)).v = 0 := by
  obtain ⟨x, m⟩ := X
  obtain ⟨y, n⟩ := Y
  obtain ⟨z, p⟩ := Z
  -- Cyclic replacement for the triple bracket using the Jacobi axiom.
  have h3 : A.bracket z (A.bracket x y)
      = -(A.bracket x (A.bracket y z) + A.bracket y (A.bracket z x)) := by
    have h := A.lie_jacobi x y z
    have h' : A.bracket z (A.bracket x y)
        + (A.bracket x (A.bracket y z) + A.bracket y (A.bracket z x)) = 0 := by
      rw [← h]; abel
    exact eq_neg_of_add_eq_zero_left h'
  simp only [tb_v, tb_n]
  simp only [alpha_sub, A.alpha_linear, A.alpha_smul, h_closed]
  simp only [bracket_sub_right, A.bracket_add_right, A.bracket_smul_right]
  rw [A.lie_antisymm y x, A.lie_antisymm z y, A.lie_antisymm x z, h3]
  push_cast
  simp only [smul_add, smul_sub, smul_smul, smul_neg, neg_smul,
    add_mul, sub_mul, mul_add, mul_sub, add_smul, sub_smul]
  ring_nf
  abel_nf
  simp [zero_smul, smul_zero]

/-! ## 8. A Non-Abelian Model Discharging the Closedness Hypothesis
    The affine Lie algebra of the line, `[e₁, e₂] = e₂`, realized on ℝ × ℝ
    with `α` the projection onto the first coordinate.  Brackets land in
    span e₂, so `α ∘ [·,·] = 0` holds while α ≠ 0 and the bracket is
    non-abelian — `twisted_jacobi_holds` is non-vacuously applicable. -/

def affineModel : LieAlgWithAlpha where
  L := ℝ × ℝ
  bracket X Y := (0, X.1 * Y.2 - X.2 * Y.1)
  alpha X := X.1
  lie_antisymm := by
    intro X Y
    apply Prod.ext <;> simp
    ring
  lie_jacobi := by
    intro X Y Z
    apply Prod.ext <;> simp
    ring
  bracket_add_right := by
    intro X Y Z
    apply Prod.ext <;> simp
    ring
  bracket_smul_right := by
    intro r X Y
    apply Prod.ext <;> simp
    ring
  alpha_linear := by intro X Y; simp
  alpha_smul := by intro r X; simp

theorem affineModel_closed :
    ∀ a b, affineModel.alpha (affineModel.bracket a b) = 0 :=
  fun _ _ => rfl

theorem affineModel_alpha_ne_zero : affineModel.alpha (1, 0) ≠ 0 :=
  one_ne_zero

/-- The twisted Jacobi identity holds unconditionally in the affine model. -/
example (X Y Z : GElem affineModel) :
    (tb affineModel X (tb affineModel Y Z)).v
      + (tb affineModel Y (tb affineModel Z X)).v
      + (tb affineModel Z (tb affineModel X Y)).v = 0 :=
  twisted_jacobi_holds affineModel affineModel_closed X Y Z

end RLA.JacobiIdentity
