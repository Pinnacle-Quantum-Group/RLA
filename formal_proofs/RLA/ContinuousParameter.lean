/-
  RLA — Continuous Recursion Parameter (Proposition P8)
  Pinnacle Quantum Group — April 2026

  Proves properties of the continuous recursion parameter lam ∈ ℝ:
  - D^lam := e^{lam ln D} is well-defined and positive for D > 0, with the
    semigroup law D^{lam₁}·D^{lam₂} = D^{lam₁+lam₂}
  - Discretizing lam ∈ ℤ recovers the integer grading
  - The weighted operator L^(lam) T = D^lam·T′ + w·lam·α·T (constant D, α)
    acting on functions T : ℝ → ℝ: its weight term is additive in the grade
    (`P8_grade_sum`), the family is ABELIAN — [L^(lam₁), L^(lam₂)] = 0
    (`continuousLieOp_commutator_eq_zero`) — and consequently the naive P8
    commutator law [L^(lam₁), L^(lam₂)] = L^(lam₁+lam₂) is REFUTED here
    (`P8_naive_commutator_false`): a constant-coefficient model cannot
    express P8.  The genuine commutator identity, with α = D⁻¹·X(D) the
    honest logarithmic derivative, is proved in
    `RepresentationProperty.commutator_Lw`.
  - Witt-type generator relations: d/dlam D^lam = ln D · D^lam
    (`witt_derivative_scale`, extended to the full weighted family in
    `witt_derivative_lieDeriv`), and the continuous Witt algebra
    ℓ_lam = x^{lam+1}·d/dx on (0,∞) with the grade-additive commutation law
    [ℓ_{lam₁}, ℓ_{lam₂}] = (lam₂ − lam₁)·ℓ_{lam₁+lam₂} (`witt_commutator`)
  Reference: RLA README §8, Appendix A.3
-/
import Mathlib

noncomputable section
open Real

namespace RLA.ContinuousParameter

/-! ## 1. Continuous Scale Power: D^lam = e^{lam ln D} -/

def continuousScale (D : ℝ) (_hD : 0 < D) (lam : ℝ) : ℝ := D ^ lam

theorem continuous_scale_pos (D : ℝ) (hD : 0 < D) (lam : ℝ) :
    0 < continuousScale D hD lam := rpow_pos_of_pos hD lam

theorem continuous_scale_additive (D : ℝ) (hD : 0 < D) (lam₁ lam₂ : ℝ) :
    continuousScale D hD (lam₁ + lam₂) =
    continuousScale D hD lam₁ * continuousScale D hD lam₂ := by
  unfold continuousScale
  exact rpow_add hD lam₁ lam₂

theorem continuous_scale_zero (D : ℝ) (hD : 0 < D) :
    continuousScale D hD 0 = 1 := rpow_zero D

theorem continuous_scale_one (D : ℝ) (hD : 0 < D) :
    continuousScale D hD 1 = D := rpow_one D

/-! ## 2. Integer Recovery: lam ∈ ℤ gives D^n -/

theorem integer_recovery (D : ℝ) (hD : 0 < D) (n : ℤ) :
    continuousScale D hD ↑n = D ^ n := by
  unfold continuousScale
  exact rpow_int_cast D n

theorem nat_recovery (D : ℝ) (hD : 0 < D) (n : ℕ) :
    continuousScale D hD ↑n = D ^ n := by
  unfold continuousScale
  exact rpow_nat_cast D n

/-! ## 3. Grade Additivity of Continuous Representation -/

structure ContinuousRepData where
  D : ℝ
  hD : 0 < D
  α : ℝ  -- ι_X(α)
  w : ℝ  -- tensor weight

/-- Scalar bookkeeping form of the weighted grade-`lam` operator applied to a
weight-`w` scalar `T`: only the coefficient structure `D^lam·T + w·lam·α·T`
is recorded.  The honest operator form is `continuousLieOp` below. -/
def continuousLieDeriv (rd : ContinuousRepData) (lam : ℝ) (T : ℝ) : ℝ :=
  continuousScale rd.D rd.hD lam * T + rd.w * lam * rd.α * T

/-- The continuous-parameter weighted Lie derivative as an honest operator on
functions `T : ℝ → ℝ` along the unit field ∂ₓ, with constant dilation `D` and
constant `α`:  `L^(lam) T = D^lam·T′ + w·lam·α·T`. -/
def continuousLieOp (rd : ContinuousRepData) (lam : ℝ) (T : ℝ → ℝ) : ℝ → ℝ :=
  fun x => continuousScale rd.D rd.hD lam * deriv T x + rd.w * lam * rd.α * T x

/-- **P8 grade additivity of the weight term.**  At grade `lam₁ + lam₂` the
weighted operator factors its scale through the semigroup law and splits its
weight correction as the sum of the grade-`lam₁` and grade-`lam₂` corrections
(the continuous analogue of
`RepresentationProperty.representation_grade_additive`). -/
theorem P8_grade_sum (rd : ContinuousRepData) (lam₁ lam₂ : ℝ) (T : ℝ → ℝ) (x : ℝ) :
    continuousLieOp rd (lam₁ + lam₂) T x =
      continuousScale rd.D rd.hD lam₁ * continuousScale rd.D rd.hD lam₂ * deriv T x +
        (rd.w * lam₁ * rd.α * T x + rd.w * lam₂ * rd.α * T x) := by
  unfold continuousLieOp
  rw [continuous_scale_additive]
  ring

theorem P8_scale_composition (rd : ContinuousRepData) (lam₁ lam₂ : ℝ) :
    continuousScale rd.D rd.hD lam₁ * continuousScale rd.D rd.hD lam₂ =
    continuousScale rd.D rd.hD (lam₁ + lam₂) :=
  (continuous_scale_additive rd.D rd.hD lam₁ lam₂).symm

/-! ## 4. Commutators: the Constant-Coefficient Family is Abelian -/

/-- Pointwise derivative of `L^(lam) T` for `T` twice differentiable at `x`. -/
theorem continuousLieOp_hasDerivAt (rd : ContinuousRepData) (lam : ℝ)
    (T : ℝ → ℝ) (x : ℝ) (hT : DifferentiableAt ℝ T x)
    (hT' : DifferentiableAt ℝ (deriv T) x) :
    HasDerivAt (continuousLieOp rd lam T)
      (continuousScale rd.D rd.hD lam * deriv (deriv T) x +
        rd.w * lam * rd.α * deriv T x) x :=
  (hT'.hasDerivAt.const_mul _).add (hT.hasDerivAt.const_mul _)

/-- **The constant-coefficient family is abelian.**  Because `D` and `α` are
constants (so ∂ₓ annihilates them) and both operators are built on the same
underlying field ∂ₓ, any two members of the family `{L^(lam)}` commute:
`[L^(lam₁), L^(lam₂)] T = 0` on twice-differentiable `T`. -/
theorem continuousLieOp_commutator_eq_zero (rd : ContinuousRepData)
    (lam₁ lam₂ : ℝ) (T : ℝ → ℝ) (x : ℝ) (hT : DifferentiableAt ℝ T x)
    (hT' : DifferentiableAt ℝ (deriv T) x) :
    continuousLieOp rd lam₁ (continuousLieOp rd lam₂ T) x -
      continuousLieOp rd lam₂ (continuousLieOp rd lam₁ T) x = 0 := by
  have h₁ := (continuousLieOp_hasDerivAt rd lam₁ T x hT hT').deriv
  have h₂ := (continuousLieOp_hasDerivAt rd lam₂ T x hT hT').deriv
  simp only [continuousLieOp] at h₁ h₂ ⊢
  rw [h₁, h₂]
  ring

/-- **The naive P8 commutator law is FALSE in the constant-coefficient
model.**  An earlier revision of this file claimed
`[L^(lam₁), L^(lam₂)] = L^(lam₁+lam₂)`.  Since the family is abelian
(`continuousLieOp_commutator_eq_zero`), that law would force
`L^(lam₁+lam₂) T = 0` for every admissible `T`, which already fails for the
constant function `T = 1` (where `L^(1) T = w·α·T ≠ 0` for `w = α = 1`).
The genuine P8 identity requires a non-constant dilation with
`α = d ln D`; it is proved as `RepresentationProperty.commutator_Lw`. -/
theorem P8_naive_commutator_false :
    ¬ ∀ (rd : ContinuousRepData) (lam₁ lam₂ : ℝ) (T : ℝ → ℝ) (x : ℝ),
        DifferentiableAt ℝ T x → DifferentiableAt ℝ (deriv T) x →
        continuousLieOp rd lam₁ (continuousLieOp rd lam₂ T) x -
          continuousLieOp rd lam₂ (continuousLieOp rd lam₁ T) x =
        continuousLieOp rd (lam₁ + lam₂) T x := by
  intro h
  have hT : DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) 0 := differentiableAt_const 1
  have hT' : DifferentiableAt ℝ (deriv fun _ : ℝ => (1 : ℝ)) 0 := by
    rw [deriv_const']
    exact differentiableAt_const 0
  have hval := h ⟨1, one_pos, 1, 1⟩ 0 1 (fun _ => 1) 0 hT hT'
  rw [continuousLieOp_commutator_eq_zero ⟨1, one_pos, 1, 1⟩ 0 1 (fun _ => 1) 0
    hT hT'] at hval
  have hrhs : continuousLieOp ⟨1, one_pos, 1, 1⟩ (0 + 1) (fun _ => 1) 0 = 1 := by
    simp [continuousLieOp, continuousScale]
  rw [hrhs] at hval
  exact zero_ne_one hval

/-! ## 5. Witt-Type Generator: ∂/∂lam -/

theorem witt_derivative_scale (D : ℝ) (hD : 0 < D) (lam : ℝ) :
    HasDerivAt (continuousScale D hD) (log D * continuousScale D hD lam) lam := by
  unfold continuousScale
  -- D^x as a function of x has derivative D^x * log D (constant base)
  have h := (Real.hasStrictDerivAt_const_rpow hD lam).hasDerivAt
  convert h using 1
  ring

/-- Witt-type generator on the full weighted family: for fixed `T`, the map
`lam ↦ L^(lam) T` (scalar bookkeeping form) is differentiable in the
recursion parameter, with derivative `(ln D · D^lam + w·α)·T`. -/
theorem witt_derivative_lieDeriv (rd : ContinuousRepData) (T lam : ℝ) :
    HasDerivAt (fun l => continuousLieDeriv rd l T)
      ((log rd.D * continuousScale rd.D rd.hD lam + rd.w * rd.α) * T) lam := by
  have h₁ : HasDerivAt (fun l => continuousScale rd.D rd.hD l * T)
      (log rd.D * continuousScale rd.D rd.hD lam * T) lam :=
    (witt_derivative_scale rd.D rd.hD lam).mul_const T
  have h₂ : HasDerivAt (fun l : ℝ => rd.w * l * rd.α * T)
      (rd.w * 1 * rd.α * T) lam :=
    (((hasDerivAt_id lam).const_mul rd.w).mul_const rd.α).mul_const T
  have h := h₁.add h₂
  unfold continuousLieDeriv
  convert h using 1
  ring

/-! ## 6. Continuous → Discrete Limit -/

theorem discrete_sampling (D : ℝ) (hD : 0 < D) (n : ℕ) :
    continuousScale D hD ↑n = D ^ n :=
  nat_recovery D hD n

theorem interpolation_between_integers (D : ℝ) (hD : 0 < D) (n : ℕ) :
    continuousScale D hD ↑n * continuousScale D hD (1/2) =
    continuousScale D hD (↑n + 1/2) :=
  (continuous_scale_additive D hD ↑n (1/2)).symm

/-! ## 7. Smooth Family Property -/

theorem scale_continuous (D : ℝ) (hD : 0 < D) :
    Continuous (continuousScale D hD) := by
  unfold continuousScale
  exact continuous_const.rpow continuous_id (fun _ => Or.inl (ne_of_gt hD))

/-! ## 8. Continuous Witt Algebra: ℓ_lam = x^{lam+1}·d/dx on (0,∞) -/

/-- The continuous-parameter Witt generator `ℓ_lam T = x^{lam+1}·T′` — the
vector-field realization of the grade-`lam` scaling generator on the
half-line.  For `lam = n ∈ ℤ` these are the classical Witt generators
`ℓ_n = x^{n+1}·d/dx` (see `wittOp_nat_recovery`), and `x^{lam+1}` is exactly
`continuousScale x _ (lam+1)` at each `x > 0`. -/
def wittOp (lam : ℝ) (T : ℝ → ℝ) : ℝ → ℝ := fun x => x ^ (lam + 1) * deriv T x

/-- At natural grade `lam = n` the generator coefficient is the monomial
`x^(n+1)`: the continuous Witt family samples to the classical one. -/
theorem wittOp_nat_recovery (n : ℕ) (T : ℝ → ℝ) (x : ℝ) :
    wittOp ↑n T x = x ^ (n + 1) * deriv T x := by
  unfold wittOp
  rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, rpow_nat_cast]

/-- Derivative of the generator coefficient `y ↦ y^{lam+1}` away from 0. -/
private theorem hasDerivAt_rpow_coeff (lam : ℝ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y ^ (lam + 1)) ((lam + 1) * x ^ lam) x := by
  have h := Real.hasDerivAt_rpow_const (x := x) (p := lam + 1)
    (Or.inl (ne_of_gt hx))
  rwa [add_sub_cancel] at h

/-- **Continuous Witt relation (Proposition P8, generator form).**  The
continuous-grade generators obey the Witt-type commutation law
`[ℓ_{lam₁}, ℓ_{lam₂}] T = (lam₂ − lam₁)·ℓ_{lam₁+lam₂} T` at every `x > 0`,
for any `T` whose derivative is differentiable at `x`.  The grade of the
bracket is `lam₁ + lam₂`: this is the P8 grade additivity realized as a
genuine operator identity (contrast `continuousLieOp_commutator_eq_zero`,
where constant coefficients force the bracket to vanish). -/
theorem witt_commutator (lam₁ lam₂ : ℝ) (T : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hT' : DifferentiableAt ℝ (deriv T) x) :
    wittOp lam₁ (wittOp lam₂ T) x - wittOp lam₂ (wittOp lam₁ T) x =
      (lam₂ - lam₁) * wittOp (lam₁ + lam₂) T x := by
  have h₁ : HasDerivAt (wittOp lam₁ T)
      ((lam₁ + 1) * x ^ lam₁ * deriv T x + x ^ (lam₁ + 1) * deriv (deriv T) x)
      x :=
    (hasDerivAt_rpow_coeff lam₁ x hx).mul hT'.hasDerivAt
  have h₂ : HasDerivAt (wittOp lam₂ T)
      ((lam₂ + 1) * x ^ lam₂ * deriv T x + x ^ (lam₂ + 1) * deriv (deriv T) x)
      x :=
    (hasDerivAt_rpow_coeff lam₂ x hx).mul hT'.hasDerivAt
  have e₁ : x ^ (lam₁ + 1) * x ^ lam₂ = x ^ (lam₁ + lam₂ + 1) := by
    rw [← rpow_add hx]
    congr 1
    ring
  have e₂ : x ^ (lam₂ + 1) * x ^ lam₁ = x ^ (lam₁ + lam₂ + 1) := by
    rw [← rpow_add hx]
    congr 1
    ring
  simp only [wittOp]
  rw [h₁.deriv, h₂.deriv]
  linear_combination ((lam₂ + 1) * deriv T x) * e₁ - ((lam₁ + 1) * deriv T x) * e₂

end RLA.ContinuousParameter
