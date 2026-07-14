/-
  RLA — Central Extensions and Virasoro Analogy (Appendix D)
  Pinnacle Quantum Group — April 2026

  Formalizes the Lie-algebra 2-cocycle condition for central extensions
  of the Witt-type graded algebra [L_m, L_n] = (n - m)·L_{m+n}, and proves
  the two facts that make the Virasoro analogy real:
    (i)  the Virasoro cocycle ω(m,n) = c/12 · m(m²-1) · δ_{m+n,0} satisfies
         the genuine (structure-constant-weighted) 2-cocycle identity
         (`virasoro_is_cocycle`), and
    (ii) for c ≠ 0 it is NOT a Lie coboundary (m,n) ↦ (n-m)·f(m+n)
         (`central_extension_nontrivial`), i.e. its class in H²(Witt) is
         nonzero, while the linear part m·δ_{m+n,0} IS a coboundary
         (`linear_term_is_coboundary`) — only the m³ term is essential.
  Reference: RLA README Appendix D
-/
import Mathlib

noncomputable section

namespace RLA.CentralExtensions

/-! ## 1. 2-Cocycle on the Graded (Witt-Type) Algebra -/

/-- The Lie-algebra 2-cocycle condition for the Witt bracket
    `[L_m, L_n] = (n - m)·L_{m+n}`: antisymmetry together with the cyclic
    identity carrying the structure constants,

      `(n-m)·ω(m+n,p) + (p-n)·ω(n+p,m) + (m-p)·ω(p+m,n) = 0`.

    This is `ω([x,y],z) + ω([y,z],x) + ω([z,x],y) = 0` written out on the
    graded basis. A structure-constant-free 3-term sum
    `ω(m,n+p) + ω(n,p+m) + ω(p,m+n) = 0` (used as the definition in an
    earlier version of this file) is NOT the right condition here — the
    Virasoro cocycle fails it (see `virasoro_fails_naive_condition`). -/
def cocycle (ω : ℤ → ℤ → ℝ) : Prop :=
  (∀ m n, ω m n = -ω n m) ∧                          -- antisymmetry
  (∀ m n p : ℤ, ((n : ℝ) - m) * ω (m + n) p
              + ((p : ℝ) - n) * ω (n + p) m
              + ((m : ℝ) - p) * ω (p + m) n = 0)     -- cocycle condition

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

/-- **The Virasoro cocycle is a genuine 2-cocycle** for the Witt bracket.
    Off the plane `m + n + p = 0` all three Kronecker deltas vanish; on
    the plane, substituting `p = -m - n` reduces the identity to the
    polynomial identity
    `(n-m)·s(s²-1) - (m+2n)·m(m²-1)·(-1)... = 0` (with `s = m+n`),
    which `ring` closes. This is the file's centerpiece: the cubic
    profile `m(m²-1)` is not decoration, it satisfies the actual
    cocycle equation. -/
theorem virasoro_is_cocycle (c : ℝ) : cocycle (virasoroCocycle c) := by
  refine ⟨virasoro_antisymmetric c, ?_⟩
  intro m n p
  unfold virasoroCocycle
  by_cases h : m + n + p = 0
  · rw [if_pos h, if_pos (show n + p + m = 0 by omega),
        if_pos (show p + m + n = 0 by omega)]
    have hp : (p : ℝ) = -(m : ℝ) - n := by exact_mod_cast (show p = -m - n by omega)
    push_cast
    rw [hp]; ring
  · rw [if_neg h, if_neg (show ¬n + p + m = 0 by omega),
        if_neg (show ¬p + m + n = 0 by omega)]
    ring

/-- The Virasoro cocycle does **not** satisfy the naive
    (structure-constant-free) 3-term condition
    `ω(m,n+p) + ω(n,p+m) + ω(p,m+n) = 0` that an earlier version of this
    file used as its "cocycle condition": at `(m,n,p) = (1,1,-2)` the sum
    is `-c/2 ≠ 0`. Kept as a permanent record of why `cocycle` carries
    the Witt structure constants `(n-m)` etc. -/
theorem virasoro_fails_naive_condition (c : ℝ) (hc : c ≠ 0) :
    ¬(∀ m n p : ℤ, virasoroCocycle c m (n + p) + virasoroCocycle c n (p + m)
        + virasoroCocycle c p (m + n) = 0) := by
  intro h
  have h1 := h 1 1 (-2)
  unfold virasoroCocycle at h1
  norm_num at h1
  exact hc h1

/-! ## 3. Coboundaries: Lie-Algebra (Witt) and Group-Style -/

/-- The **Lie-algebra 2-coboundary** of a 1-cochain `f` for the Witt
    bracket: `(δf)(m,n) = (n - m)·f(m+n)`. This — not the symmetric
    group-style `f(m+n) - f(m) - f(n)` below — is the correct notion of
    "trivial cocycle" for central extensions of the graded algebra:
    it is what you get by shifting the central term by a regrading
    `L_m ↦ L_m + f(m)·Z`. -/
def lieCoboundary (f : ℤ → ℝ) (m n : ℤ) : ℝ :=
  ((n : ℝ) - m) * f (m + n)

theorem lieCoboundary_antisymmetric (f : ℤ → ℝ) (m n : ℤ) :
    lieCoboundary f m n = -lieCoboundary f n m := by
  unfold lieCoboundary
  rw [add_comm n m]; ring

/-- Every Lie coboundary is a 2-cocycle (`δ² = 0` in low degree), so
    `lieCoboundary` really does land in the space `cocycle` carves out,
    and quotienting cocycles by coboundaries (= H²) makes sense. -/
theorem lieCoboundary_is_cocycle (f : ℤ → ℝ) : cocycle (lieCoboundary f) := by
  refine ⟨lieCoboundary_antisymmetric f, ?_⟩
  intro m n p
  unfold lieCoboundary
  rw [show n + p + m = m + n + p by ring, show p + m + n = m + n + p by ring]
  push_cast
  ring

def trivialCocycle (f : ℤ → ℝ) (m n : ℤ) : ℝ :=
  f (m + n) - f m - f n

/-- The group-style coboundary `(δf)(m,n) := f(m+n) - f(m) - f(n)` is
    **symmetric** under swap, so it can never equal a nonzero
    antisymmetric 2-form. This is the easy, algebra-free half of the
    story; the cohomologically meaningful nontriviality (against
    `lieCoboundary`) is `central_extension_nontrivial` below.

    The Möbius-vs-cylinder distinction in cohomology form:
    coboundary class = cylinder (no twist), nontrivial cocycle class =
    Möbius (orientation obstruction). The original statement of this
    theorem (with `-` on the RHS) collapsed exactly that distinction. -/
theorem trivial_is_symmetric (f : ℤ → ℝ) :
    ∀ m n, trivialCocycle f m n = trivialCocycle f n m := by
  intro m n
  unfold trivialCocycle
  rw [add_comm n m]; ring

/-- Group-style coboundary, identical to `trivialCocycle`; named here to
    make the cohomological role visible at the type level. NOTE: this is
    the coboundary of the abelian *group* ℤ, not the Lie-algebra
    coboundary relevant to central extensions — see `lieCoboundary`. -/
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

/-- **Cohomological nontriviality** (the genuine Virasoro statement):
    for `c ≠ 0`, the Virasoro cocycle is not the Lie coboundary
    `(m,n) ↦ (n-m)·f(m+n)` of ANY 1-cochain `f`, i.e. its class in
    `H²(Witt, ℝ)` is nonzero. This is what makes the central extension
    nontrivial and the spectral partition (Σ ≠ 0 vs Σ = 0 in
    FIL_Langlands) detectable.

    Proof: evaluating a putative `f` at `(1,-1)` forces `f 0 = 0`
    (because `1·(1²-1) = 0`), but evaluating at `(2,-2)` gives
    `c/2 = -4·f 0 = 0`, contradicting `c ≠ 0`. -/
theorem central_extension_nontrivial (c : ℝ) (hc : c ≠ 0) :
    ¬∃ f : ℤ → ℝ, ∀ m n, virasoroCocycle c m n = lieCoboundary f m n := by
  rintro ⟨f, hf⟩
  have h1 := hf 1 (-1)
  have h2 := hf 2 (-2)
  unfold virasoroCocycle lieCoboundary at h1 h2
  norm_num at h1 h2
  -- h1 : f 0 = 0 (up to normalization), h2 : c/12·6 = -4·f 0
  apply hc
  linarith

/-- Weaker, symmetric-coboundary nontriviality (kept for the record):
    the Virasoro cocycle at `c ≠ 0` is not a group-style symmetric
    coboundary `f(m+n) - f(m) - f(n)` either — immediate from
    antisymmetry vs. symmetry. The cohomologically meaningful statement
    is `central_extension_nontrivial` above. -/
theorem virasoro_not_symmetric_coboundary (c : ℝ) (hc : c ≠ 0) :
    ¬∃ f : ℤ → ℝ, ∀ m n, virasoroCocycle c m n = coboundary f m n := by
  rintro ⟨f, hf⟩
  -- virasoroCocycle is antisymmetric; coboundary is symmetric.
  -- If virasoro = coboundary pointwise, then virasoro at (2,-2) equals
  -- virasoro at (-2,2), which combined with antisymmetry forces it to 0,
  -- contradicting nontrivial_virasoro.
  have h_anti := virasoro_antisymmetric c 2 (-2)
  have h_sym := coboundary_symmetric f 2 (-2)
  have h1 := hf 2 (-2)
  have h2 := hf (-2) 2
  have h_zero : virasoroCocycle c 2 (-2) = 0 := by linarith
  exact nontrivial_virasoro c hc h_zero

/-- The **linear part** `a·m·δ_{m+n,0}` of a Virasoro-type cocycle IS a
    Lie coboundary — take `f` supported at `0` with `f 0 = -a/2`. So the
    `-c/12·m` piece of `ω(m,n) = c/12·(m³-m)·δ_{m+n,0}` can be gauged
    away, and only the cubic term `m³` is cohomologically essential:
    the standard normalization statement for the Virasoro central term. -/
theorem linear_term_is_coboundary (a : ℝ) :
    ∃ f : ℤ → ℝ, ∀ m n : ℤ,
      (if m + n = 0 then a * (m : ℝ) else 0) = lieCoboundary f m n := by
  refine ⟨fun k => if k = 0 then -(a / 2) else 0, fun m n => ?_⟩
  simp only [lieCoboundary]
  by_cases h : m + n = 0
  · rw [if_pos h, if_pos h]
    have hn : (n : ℝ) = -(m : ℝ) := by exact_mod_cast (show n = -m by omega)
    rw [hn]; ring
  · rw [if_neg h, if_neg h]
    ring

end RLA.CentralExtensions
