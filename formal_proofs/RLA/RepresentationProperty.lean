/-
  RLA — Representation Property (Theorem T5)
  Pinnacle Quantum Group — April 2026

  Two-layer formalization of the weighted level-n Lie derivative
      L^(n)_X T := L_{D^n X} T + w·n·(ι_X α)·T,   α := d ln D
  (README §6, Definition 4).

  Layer 1 (§§1–7) is the elementary scalar bookkeeping model `RepData`
  (with an unconstrained `lieDeriv`): α = 0 / n = 0 recovery, additivity of
  the weight correction in the grade, and D-grading facts.

  Layer 2 (§§8–10) is a genuine operator model: X, Y are `Derivation ℝ A A`
  over a commutative ℝ-algebra A, the dilation D : Aˣ is a unit,
  ι_X α := D⁻¹·X(D), and L^(n)_X acts on weight-w scalars by
      Lw D w X n T = D^n·X(T) + w·n·(ι_X α)·T.
  The main theorem `commutator_Lw` computes the commutator exactly:
      [L^(m)_X, L^(n)_Y] T = D^(m+n)·([X,Y] + n(ι_X α)Y − m(ι_Y α)X)(T)
                              + w·n·D^m·X(ι_Y α)·T − w·m·D^n·Y(ι_X α)·T.
  README Theorem 5 asserts this identity WITHOUT the two residual terms;
  those are the Leibniz contributions (D^m X)(ι_Y α) dropped in the expansion
  of Appendix A.2, and they do not vanish for w ≠ 0 with non-constant D
  (e.g. m = 1, n = 0, D = eˣ, X = ∂ₓ, Y = x∂ₓ on smooth functions).
  Theorem 5 as printed is recovered exactly in the two regimes where it is
  true:
    • `commutator_representation`            — weight w = 0, and
    • `commutator_representation_alpha_zero` — α = 0 (X(D) = Y(D) = 0).
  Reference: RLA README §6, Theorem 5, Appendix A.2
-/
import Mathlib

noncomputable section

namespace RLA.RepresentationProperty

/-! ## 1. Abstract Representation Model (scalar bookkeeping layer)
    `RepData.lieDeriv` is an *unconstrained* stand-in for L_V; only the
    bookkeeping of the weight term is meaningful at this layer.  The honest
    operator model, where the commutator identity is actually proved, is in
    §§8–10 below. -/

structure RepData where
  lieDeriv : ℝ → ℝ → ℝ
  alpha : ℝ → ℝ
  weight : ℝ
  D : ℝ
  hD_pos : 0 < D

/-! ## 2. Weighted Level-n Lie Derivative (scalar model) -/

def weightedLieDeriv (rd : RepData) (X : ℝ) (n : ℤ) (T : ℝ) : ℝ :=
  rd.lieDeriv (rd.D ^ n * X) T + rd.weight * ↑n * rd.alpha X * T

/-! ## 3. Corollary 6: α = 0 Recovery -/

theorem alpha_zero_recovery (rd : RepData) (X : ℝ) (n : ℤ) (T : ℝ)
    (hα : rd.alpha X = 0) :
    weightedLieDeriv rd X n T = rd.lieDeriv (rd.D ^ n * X) T := by
  unfold weightedLieDeriv; simp [hα]

/-! ## 4. Zero-Level is Standard Lie Derivative -/

theorem zero_level_standard (rd : RepData) (X T : ℝ) :
    weightedLieDeriv rd X 0 T = rd.lieDeriv (rd.D ^ (0 : ℤ) * X) T := by
  unfold weightedLieDeriv; simp

theorem zero_level_simplify (rd : RepData) (X T : ℝ) :
    weightedLieDeriv rd X 0 T = rd.lieDeriv X T := by
  unfold weightedLieDeriv; simp [zpow_zero]

/-! ## 5. Grade Additivity of Representation -/

/-- The weight correction of the level-(m+n) operator splits as the sum of
the level-m and level-n corrections: the α-term of `weightedLieDeriv` is
additive in the grade. -/
theorem representation_grade_additive (rd : RepData) (X : ℝ) (m n : ℤ) (T : ℝ) :
    weightedLieDeriv rd X (m + n) T =
      rd.lieDeriv (rd.D ^ (m + n) * X) T +
        (rd.weight * ↑m * rd.alpha X * T + rd.weight * ↑n * rd.alpha X * T) := by
  unfold weightedLieDeriv
  push_cast
  ring

/-! ## 6. D-Scaling Properties -/

theorem D_pow_additive (D : ℝ) (hD : D > 0) (m n : ℤ) :
    D ^ (m + n) = D ^ m * D ^ n :=
  zpow_add₀ (ne_of_gt hD) m n

theorem D_pow_pos (D : ℝ) (hD : D > 0) (n : ℤ) : 0 < D ^ n :=
  zpow_pos_of_pos hD n

/-! ## 7. Weight Scaling -/

theorem weight_linearity (rd : RepData) (X : ℝ) (m n : ℤ) (T : ℝ) :
    rd.weight * ↑(m + n) * rd.alpha X * T =
    rd.weight * ↑m * rd.alpha X * T + rd.weight * ↑n * rd.alpha X * T := by
  push_cast; ring

/-! ## 8. The Genuine Operator Model: Derivations and a Unit Dilation -/

variable {A : Type*} [CommRing A] [Algebra ℝ A]

/-- Scalar model of `ι_X α = ι_X (d ln D) = X(ln D)`: for a unit `D` this is
`D⁻¹ · X(D)`, so no logarithm is needed. -/
def iotaAlpha (D : Aˣ) (X : Derivation ℝ A A) : A := ↑D⁻¹ * X ↑D

/-- The weighted level-`n` Lie derivative of README Definition 4, acting on a
weight-`w` scalar `T`:  `L^(n)_X T = D^n · X(T) + w·n·(ι_X α)·T`.  The weight
enters through `algebraMap ℝ A`, so derivations annihilate it. -/
def Lw (D : Aˣ) (w : ℝ) (X : Derivation ℝ A A) (n : ℤ) (T : A) : A :=
  ↑(D ^ n) * X T + algebraMap ℝ A (w * (n : ℝ)) * (iotaAlpha D X * T)

/-- At level 0 the weighted Lie derivative is the underlying derivation
(README Corollary 6, second half, in the operator model). -/
theorem Lw_zero_level (D : Aˣ) (w : ℝ) (X : Derivation ℝ A A) (T : A) :
    Lw D w X 0 T = X T := by
  simp [Lw]

/-- If `X(D) = 0` (i.e. `ι_X α = 0`) the weight term drops out and only the
transported derivation `D^n·X` remains (README Corollary 6, first half). -/
theorem Lw_alpha_zero (D : Aˣ) (w : ℝ) (X : Derivation ℝ A A) (n : ℤ) (T : A)
    (hX : X ↑D = 0) :
    Lw D w X n T = ↑(D ^ n) * X T := by
  simp [Lw, iotaAlpha, hX]

/-- A derivation applied to the inverse of a unit: `X(D⁻¹) = −D⁻¹·(ι_X α)`. -/
theorem derivation_units_inv (D : Aˣ) (X : Derivation ℝ A A) :
    X ↑D⁻¹ = -(↑D⁻¹ * iotaAlpha D X) := by
  rw [X.leibniz_of_mul_eq_one D.inv_mul]
  simp only [iotaAlpha, smul_eq_mul]
  ring

/-- Logarithmic derivative of an integer power: `X(Dⁿ) = n·(ι_X α)·Dⁿ`.
This is the scaling identity behind README Lemma 3. -/
theorem derivation_units_zpow (D : Aˣ) (X : Derivation ℝ A A) (n : ℤ) :
    X ↑(D ^ n) = (n : A) * (iotaAlpha D X * ↑(D ^ n)) := by
  induction n using Int.induction_on with
  | hz => simp
  | hp k ih =>
      have hDD : (↑D⁻¹ : A) * ↑D = 1 := D.inv_mul
      rw [zpow_add_one, Units.val_mul, Derivation.leibniz, ih]
      simp only [iotaAlpha, smul_eq_mul, Int.cast_add, Int.cast_one]
      linear_combination (-(X (↑D : A) * (↑(D ^ (k : ℤ)) : A))) * hDD
  | hn k ih =>
      rw [zpow_sub_one, Units.val_mul, Derivation.leibniz, ih, derivation_units_inv D X]
      simp only [iotaAlpha, smul_eq_mul, Int.cast_sub, Int.cast_neg, Int.cast_one]
      ring

/-! ## 9. The Twisted Bracket as a Genuine Vector Field -/

/-- The grade-dependent twisted bracket of README Eq. (1),
`[X,Y]_α = [X,Y] + n·(ι_X α)·Y − m·(ι_Y α)·X`, packaged as an honest
derivation (mathlib supplies the Lie ring and `A`-module structure on
`Derivation ℝ A A`). -/
def twistedVF (D : Aˣ) (m n : ℤ) (X Y : Derivation ℝ A A) : Derivation ℝ A A :=
  ⁅X, Y⁆ + ((n : A) * iotaAlpha D X) • Y - ((m : A) * iotaAlpha D Y) • X

@[simp]
theorem twistedVF_apply (D : Aˣ) (m n : ℤ) (X Y : Derivation ℝ A A) (T : A) :
    twistedVF D m n X Y T =
      X (Y T) - Y (X T) + (n : A) * (iotaAlpha D X * Y T)
        - (m : A) * (iotaAlpha D Y * X T) := by
  simp only [twistedVF, Derivation.sub_apply, Derivation.add_apply,
    Derivation.commutator_apply, Derivation.smul_apply, smul_eq_mul]
  ring

/-! ## 10. Representation Theorem: Exact Commutator with Residual -/

/-- **Corrected representation identity** (README Theorem 5, repaired).
The commutator of two weighted level-`m`/`n` Lie derivatives is the
level-(m+n) transport of the twisted bracket `[X,Y]_α` **plus an explicit
residual**:
`w·n·D^m·X(ι_Y α)·T − w·m·D^n·Y(ι_X α)·T`.
README Theorem 5 omits the residual: its Appendix A.2 expansion drops the
Leibniz terms `(D^m X)(ι_Y α)`, and the boxed identity (4) is false for
`w ≠ 0` with non-constant `D` (counterexample: `m = 1`, `n = 0`, `D = eˣ`,
`X = ∂ₓ`, `Y = x∂ₓ`).  The corollaries below recover (4) exactly in the two
regimes where the residual vanishes identically. -/
theorem commutator_Lw (D : Aˣ) (w : ℝ) (X Y : Derivation ℝ A A) (m n : ℤ) (T : A) :
    Lw D w X m (Lw D w Y n T) - Lw D w Y n (Lw D w X m T) =
      ↑(D ^ (m + n)) * twistedVF D m n X Y T
        + algebraMap ℝ A (w * (n : ℝ)) * (↑(D ^ m) * (X (iotaAlpha D Y) * T))
        - algebraMap ℝ A (w * (m : ℝ)) * (↑(D ^ n) * (Y (iotaAlpha D X) * T)) := by
  have hmn : (↑(D ^ (m + n)) : A) = ↑(D ^ m) * ↑(D ^ n) := by
    rw [zpow_add, Units.val_mul]
  simp only [Lw, Derivation.map_add, Derivation.leibniz, Derivation.map_algebraMap,
    derivation_units_zpow, twistedVF_apply, smul_eq_mul, hmn, mul_zero, zero_mul, add_zero]
  ring

/-- **Representation property, weight-zero regime** (README Theorem 5 /
Corollary 6 where it is true).  For `w = 0` the residual vanishes and the
weighted Lie derivative genuinely represents the twisted bracket:
`[L^(m)_X, L^(n)_Y] T = L^(m+n)_{[X,Y]_α} T`. -/
theorem commutator_representation (D : Aˣ) (X Y : Derivation ℝ A A) (m n : ℤ) (T : A) :
    Lw D 0 X m (Lw D 0 Y n T) - Lw D 0 Y n (Lw D 0 X m T) =
      Lw D 0 (twistedVF D m n X Y) (m + n) T := by
  rw [commutator_Lw]
  simp [Lw]

/-- **Representation property, α = 0 regime** (README Theorem 5 where it is
true for arbitrary weight).  If `X(D) = Y(D) = 0` then `ι_X α = ι_Y α = 0`,
the residual vanishes, the twisted bracket collapses to `⁅X, Y⁆`, and grade
additivity `m + n` holds on the nose.  This supersedes the scalar-model
lemma `alpha_zero_recovery`. -/
theorem commutator_representation_alpha_zero (D : Aˣ) (w : ℝ)
    (X Y : Derivation ℝ A A) (m n : ℤ) (T : A)
    (hX : X ↑D = 0) (hY : Y ↑D = 0) :
    Lw D w X m (Lw D w Y n T) - Lw D w Y n (Lw D w X m T) =
      Lw D w (twistedVF D m n X Y) (m + n) T := by
  have hiX : iotaAlpha D X = 0 := by simp [iotaAlpha, hX]
  have hiY : iotaAlpha D Y = 0 := by simp [iotaAlpha, hY]
  have hbr : iotaAlpha D (twistedVF D m n X Y) = 0 := by
    simp [iotaAlpha, hX, hY, Derivation.map_zero]
  rw [commutator_Lw]
  simp [Lw, hiX, hiY, hbr, Derivation.map_zero]

end RLA.RepresentationProperty
