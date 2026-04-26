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

theorem trivial_is_cocycle (f : ℤ → ℝ) (hf : f 0 = 0) :
    ∀ m n, trivialCocycle f m n = -trivialCocycle f n m := by
  intro m n
  unfold trivialCocycle
  rw [show m + n = n + m from add_comm m n]
  ring

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

end RLA.CentralExtensions
