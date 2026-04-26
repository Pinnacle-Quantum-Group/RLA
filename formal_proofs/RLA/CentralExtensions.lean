/-
  RLA — Central Extensions and Virasoro Analogy (Appendix D)
  Pinnacle Quantum Group — April 2026

  Formalizes the 2-cocycle condition for central extensions of
  the twisted graded algebra, paralleling Virasoro central charge.
  Reference: RLA README Appendix D
-/
import Mathlib

noncomputable section

namespace RLA.CentralExtensions

/-! ## 1. 2-Cocycle on Graded Algebra -/

def cocycle (ω : ℤ → ℤ → ℝ) : Prop :=
  (∀ m n, ω m n = -ω n m) ∧                         -- antisymmetry
  (∀ m n p, ω m (n + p) + ω n (p + m) + ω p (m + n) = 0)  -- cocycle condition

/-! ## 2. Virasoro-Type Cocycle: ω(m,n) = c/12 · m(m²-1) · δ_{m+n,0} -/

def virasoroCocycle (c : ℝ) (m n : ℤ) : ℝ :=
  if m + n = 0 then c / 12 * (↑m * (↑m ^ 2 - 1)) else 0

theorem virasoro_antisymmetric (c : ℝ) (m n : ℤ) :
    virasoroCocycle c m n = -virasoroCocycle c n m := by
  unfold virasoroCocycle
  split
  · rename_i h
    have hn : n + m = 0 := by linarith
    simp [hn]
    have : (↑n : ℝ) = -↑m := by exact_mod_cast (by omega : n = -m)
    rw [this]; ring
  · rename_i h
    have : ¬(n + m = 0) := by omega
    simp [this]

theorem virasoro_zero_diagonal (c : ℝ) (m : ℤ) :
    virasoroCocycle c m m = 0 ∨ m = 0 := by
  unfold virasoroCocycle
  by_cases hm : m + m = 0
  · right; omega
  · left; rw [if_neg hm]

/-! ## 3. Trivial Cocycle (Coboundary) -/

def trivialCocycle (f : ℤ → ℝ) (m n : ℤ) : ℝ :=
  f (m + n) - f m - f n

/-- The coboundary `(δf)(m,n) := f(m+n) - f(m) - f(n)` is **symmetric**
    under swap. This is the algebraic shadow of cohomological triviality:
    a globally defined `f` means no orientation twist, hence no sign
    flip on swap. Genuine 2-cocycles (e.g. `virasoroCocycle` at `c ≠ 0`)
    are *antisymmetric* — that's the orientation obstruction that makes
    the central extension nontrivial.

    The Möbius-vs-cylinder distinction in cohomology form:
    coboundary class = cylinder (no twist), nontrivial cocycle class =
    Möbius (orientation obstruction). The original statement of this
    theorem (with `-` on the RHS) collapsed exactly that distinction. -/
theorem trivial_is_symmetric (f : ℤ → ℝ) :
    ∀ m n, trivialCocycle f m n = trivialCocycle f n m := by
  intro m n
  unfold trivialCocycle
  rw [add_comm n m]; ring

/-- A coboundary is the differential of a 1-cochain. Identical to
    `trivialCocycle`; named here to make the cohomological role
    visible at the type level. -/
def coboundary (f : ℤ → ℝ) : ℤ → ℤ → ℝ :=
  fun m n => f (m + n) - f m - f n

theorem trivialCocycle_eq_coboundary (f : ℤ → ℝ) :
    trivialCocycle f = coboundary f := rfl

theorem coboundary_symmetric (f : ℤ → ℝ) (m n : ℤ) :
    coboundary f m n = coboundary f n m := by
  unfold coboundary; rw [add_comm n m]; ring

/-- Cohomology classes intersect trivially on the diagonal: a 2-form
    that is simultaneously a coboundary and antisymmetric must vanish
    on every (m, m). Algebraic statement of "cylinders are not
    Möbius strips." -/
theorem coboundary_antisymm_intersection_trivial
    (f : ℤ → ℝ) (h_antisymm : ∀ m n, coboundary f m n = -coboundary f n m) :
    ∀ m, coboundary f m m = 0 := by
  intro m
  have h_sym := coboundary_symmetric f m m
  have h_anti := h_antisymm m m
  linarith

/-! ## 4. Central Extension Construction -/

structure CentralExtension where
  bracket : ℤ → ℤ → ℤ → ℝ  -- extended bracket: grade₁ × grade₂ → (grade, central)
  charge : ℝ
  cocycle_val : ℤ → ℤ → ℝ
  h_cocycle_antisymm : ∀ m n, cocycle_val m n = -cocycle_val n m

def extendedBracketGrade (m n : ℤ) : ℤ := m + n

theorem extended_grade_additive (m n : ℤ) :
    extendedBracketGrade m n = m + n := rfl

theorem central_charge_commutes (ce : CentralExtension) (m n : ℤ) :
    ce.cocycle_val m n + ce.cocycle_val n m = 0 := by
  linarith [ce.h_cocycle_antisymm m n]

/-! ## 5. Witt Algebra (c = 0 case) -/

def wittBracket (m n : ℤ) : ℤ := (n - m) * 1  -- simplified

theorem witt_antisymmetric (m n : ℤ) :
    wittBracket m n = -wittBracket n m := by
  unfold wittBracket; ring

theorem witt_zero_cocycle : virasoroCocycle 0 = fun _ _ => 0 := by
  ext m n; unfold virasoroCocycle; simp

/-! ## 6. Non-trivial Central Charge -/

theorem nontrivial_virasoro (c : ℝ) (hc : c ≠ 0) :
    virasoroCocycle c 2 (-2) ≠ 0 := by
  unfold virasoroCocycle
  rw [if_pos (by norm_num : (2 : ℤ) + (-2) = 0)]
  push_cast
  intro h
  apply hc
  -- h : c/12 * (2 * (2^2 - 1)) = 0  ⇒  c = 0
  linarith [show c / 12 * (2 * ((2 : ℝ) ^ 2 - 1)) = c / 2 from by ring]

/-- Cohomology nontriviality: for `c ≠ 0`, the Virasoro cocycle is NOT
    a coboundary. This is what makes the central extension nontrivial
    and the spectral partition (Σ ≠ 0 vs Σ = 0 in FIL_Langlands)
    detectable. The orientation/Möbius statement in formal dress:
    coboundaries (cylinders) cannot equal antisymmetric Virasoro
    cocycles (Möbius) when the central charge is nonzero. -/
theorem central_extension_nontrivial (c : ℝ) (hc : c ≠ 0) :
    ¬ ∃ f : ℤ → ℝ, ∀ m n, virasoroCocycle c m n = coboundary f m n := by
  rintro ⟨f, hf⟩
  -- virasoroCocycle is antisymmetric; coboundary is symmetric.
  -- If virasoro = coboundary pointwise, then virasoro at (2,-2) equals
  -- virasoro at (-2,2), which combined with antisymmetry forces it to 0,
  -- contradicting nontrivial_virasoro.
  have h_anti := virasoro_antisymmetric c 2 (-2)
  have h_sym := coboundary_symmetric f 2 (-2)
  have h1 := hf 2 (-2)
  have h2 := hf (-2) 2
  -- v(2,-2) = c(2,-2) = c(-2,2) = v(-2,2)
  have h_eq : virasoroCocycle c 2 (-2) = virasoroCocycle c (-2) 2 :=
    h1.trans (h_sym.trans h2.symm)
  -- combine with v(2,-2) = -v(-2,2) to get v(2,-2) = 0
  have h_zero : virasoroCocycle c 2 (-2) = 0 := by linarith
  exact nontrivial_virasoro c hc h_zero

end RLA.CentralExtensions
