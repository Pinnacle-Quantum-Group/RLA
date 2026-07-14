/-
  RLA — Scaled Commutator (Lemma L3)
  Pinnacle Quantum Group — April 2026

  Proves Lemma L3 at the operator level: for a commutative ℝ-algebra A,
  a derivation X : Derivation ℝ A A and a scale factor d : A,
    ⁅d^(m+1) • X, d^(n+1) • X⁆ = ((n - m) • (d^(m+n+1) * X d)) • X,
  computed genuinely from the Leibniz rule and the commutator of
  derivations ⁅D₁, D₂⁆ a = D₁ (D₂ a) - D₂ (D₁ a).  Antisymmetry and
  vanishing at equal grades follow from the Lie algebra structure on
  derivations (lie_skew, lie_self).  Over a field with d ≠ 0 the
  right-hand side is (n - m) • (d^(m+n+2) * α) • X with
  α = d⁻¹ * X d — the ι_X(α) = X(ln D) form of the α-twist in the
  graded bracket.  A preliminary scalar model is kept only to record
  that it is degenerate (every scalar commutator vanishes), which is
  exactly why L3 must be stated for genuine derivations.
  Reference: RLA README §5, Appendix B
-/
import Mathlib

noncomputable section
open Real

namespace RLA.ScaledCommutator

/-! ## 1. Scalar Model of Scaled Fields
    We first model scaled fields as ℝ-valued quantities D^n * X;
    grades add under multiplication. -/

def scaledField (D : ℝ) (X : ℝ) (n : ℤ) : ℝ := D ^ n * X

theorem scaled_field_grade_additive (D X : ℝ) (m n : ℤ) (hD : D ≠ 0) :
    scaledField D X m * scaledField D X n = D ^ (m + n) * X ^ 2 := by
  unfold scaledField
  rw [zpow_add₀ hD]; ring

/-! ## 2. Degeneracy of the Scalar Model
    The scalar model cannot express a nonzero bracket: ℝ is
    commutative, so every scalar commutator vanishes identically.
    This is why Lemma L3 below is proved for genuine derivations
    (first-order differential operators), not scalars. -/

def scalarCommutator (f g : ℝ) : ℝ := f * g - g * f

theorem scalar_commutator_zero (f g : ℝ) : scalarCommutator f g = 0 := by
  unfold scalarCommutator; ring

/-! ## 3. Lemma L3: the Scaled Commutator of Derivations
    A is any commutative ℝ-algebra, X : Derivation ℝ A A a vector
    field (derivation), d : A the scale factor D.  The bracket is the
    honest commutator of operators, ⁅D₁, D₂⁆ a = D₁ (D₂ a) - D₂ (D₁ a),
    from Mathlib's Lie algebra structure on derivations. -/

variable {A : Type*} [CommRing A] [Algebra ℝ A]

/-- The bracket of two scaled copies of a single derivation:
    ⁅a • X, b • X⁆ = (a·X(b) - b·X(a)) • X, by the Leibniz rule and
    cancellation of the second-order terms ([X, X] = 0 mechanism). -/
theorem bracket_smul_smul (X : Derivation ℝ A A) (a b : A) :
    ⁅a • X, b • X⁆ = (a * X b - b * X a) • X := by
  ext c
  simp only [Derivation.commutator_apply, Derivation.smul_apply, Derivation.leibniz,
    smul_eq_mul]
  ring

/-- Leibniz power rule for a derivation, stated at exponent n + 1 so no
    ℕ-subtraction is involved: X(d^(n+1)) = (n+1) · d^n · X(d). -/
theorem deriv_pow_succ (X : Derivation ℝ A A) (d : A) (n : ℕ) :
    X (d ^ (n + 1)) = (n + 1) • (d ^ n * X d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.succ_eq_add_one]
    rw [pow_succ, Derivation.leibniz, ih]
    simp only [smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring

/-- **Lemma L3** (operator form).  For grades m+1 and n+1,
    ⁅D^(m+1) X, D^(n+1) X⁆ = ((n - m) · D^(m+n+1) · X(D)) • X.
    Since D^(m+n+1)·X(D) = D^(m+n+2)·X(ln D) (see `L3_commutator_alpha`),
    this is the README's [D^m X, D^n X] = (n-m) D^(m+n) X(ln D) X at
    grades shifted by one — the shift avoids ℕ-truncation in D^(m+n-1). -/
theorem L3_commutator (X : Derivation ℝ A A) (d : A) (m n : ℕ) :
    ⁅d ^ (m + 1) • X, d ^ (n + 1) • X⁆ =
      (((n : ℤ) - (m : ℤ)) • (d ^ (m + n + 1) * X d)) • X := by
  rw [bracket_smul_smul, deriv_pow_succ, deriv_pow_succ]
  congr 1
  simp only [nsmul_eq_mul, zsmul_eq_mul]
  push_cast
  ring

/-- Antisymmetry of the scaled commutator — a genuine corollary of the
    Lie ring structure on derivations, not a ring identity. -/
theorem L3_antisymmetric (X : Derivation ℝ A A) (d : A) (m n : ℕ) :
    ⁅d ^ (m + 1) • X, d ^ (n + 1) • X⁆ = -⁅d ^ (n + 1) • X, d ^ (m + 1) • X⁆ :=
  (lie_skew _ _).symm

/-- Equal grades commute: ⁅D^(n+1) X, D^(n+1) X⁆ = 0, from ⁅Y, Y⁆ = 0. -/
theorem L3_zero_same_grade (X : Derivation ℝ A A) (d : A) (n : ℕ) :
    ⁅d ^ (n + 1) • X, d ^ (n + 1) • X⁆ = 0 :=
  lie_self _

/-- Unit grades: ⁅X, D X⁆ = X(D) • X (grades 0 and 1; X(D) = D·X(ln D)). -/
theorem L3_unit_grades (X : Derivation ℝ A A) (d : A) :
    ⁅X, d • X⁆ = X d • X := by
  have h := bracket_smul_smul X 1 d
  simpa using h

/-- Over a field with d ≠ 0 the L3 coefficient rewrites through
    α := d⁻¹ * X d = ι_X(d ln D): the bracket is
    (n - m) • (D^(m+n+2) · α) • X, the README's α-twisted form. -/
theorem L3_commutator_alpha {K : Type*} [Field K] [Algebra ℝ K]
    (X : Derivation ℝ K K) (d : K) (hd : d ≠ 0) (m n : ℕ) :
    ⁅d ^ (m + 1) • X, d ^ (n + 1) • X⁆ =
      (((n : ℤ) - (m : ℤ)) • (d ^ (m + n + 2) * (d⁻¹ * X d))) • X := by
  have h : d ^ (m + n + 2) * (d⁻¹ * X d) = d ^ (m + n + 1) * X d := by
    field_simp
    ring
  rw [L3_commutator, ← h]

/-- The scaled commutator, applied to a test element and normalized by
    D^(m+n+1)·X(D)·X(c), is linear in the grade difference n - m. -/
theorem L3_linear_in_grade_diff {K : Type*} [Field K] [Algebra ℝ K]
    (X : Derivation ℝ K K) (d : K) (m n : ℕ) (c : K) :
    ⁅d ^ (m + 1) • X, d ^ (n + 1) • X⁆ c / (d ^ (m + n + 1) * X d * X c)
        = (n : K) - (m : K) ∨
      d ^ (m + n + 1) * X d * X c = 0 := by
  by_cases h : d ^ (m + n + 1) * X d * X c = 0
  · exact Or.inr h
  · left
    rw [div_eq_iff h, L3_commutator, Derivation.smul_apply]
    simp only [smul_eq_mul, zsmul_eq_mul]
    push_cast
    ring

/-! ## 4. Leibniz Expansion Detail (scalar scale factor) -/

theorem leibniz_D_power (D : ℝ) (hD : 0 < D) (n : ℤ) :
    D ^ (n + 1) = D ^ n * D := by
  rw [zpow_add₀ (ne_of_gt hD), zpow_one]

/-- α = d(ln D) in one variable: the logarithmic derivative of a
    differentiable positive scale field D is D'/D. -/
theorem alpha_from_D (D : ℝ → ℝ) (x : ℝ) (hD : DifferentiableAt ℝ D x)
    (hDx : 0 < D x) :
    deriv (fun t => log (D t)) x = deriv D x / D x :=
  deriv.log hD (ne_of_gt hDx)

theorem D_ratio_is_alpha (D₁ D₂ : ℝ) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂) :
    log D₂ - log D₁ = log (D₂ / D₁) :=
  (log_div (ne_of_gt hD₂) (ne_of_gt hD₁)).symm

end RLA.ScaledCommutator
