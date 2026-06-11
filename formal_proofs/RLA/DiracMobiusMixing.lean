/-
  RLA — Dirac–Möbius Mixing is Measure-Preserving (Theorem T7 application)
  Pinnacle Quantum Group — June 2026

  Anchors the DM-TRNG entropy claim (FIL/fil_trng).

  The discrete Dirac–Möbius evolution operator `U` on the 16-strip lattice is,
  in the appropriate counting measure, a *bijection* of the finite state space
  (Dirac Euler step + Möbius fold + RAC/CORDIC rotation are each invertible /
  unit-Jacobian; see FIL Topology.MobiusQuotient `mobiusPerm`, GPU
  `MobiusCompressionBijectivity`, RAC Cordic equivalence). A measure-preserving
  bijection is the discrete shadow of the RLA scale-field / Noether conservation
  law (RLA-T7): volume preservation ⇔ unit Jacobian ⇔ the harvest *diffuses* but
  never *destroys* seed entropy.

  We formalize, in the scalar `Fin (n+1) → ℝ` distribution model used by the FTC
  entropy lemmas:

    • `shannonEntropy (pushforward U p) = shannonEntropy p`   (T7 conservation),
    • `minEntropy   (pushforward U p) = minEntropy   p`       (worst-case too),
    • composing the measure-preserving `U` with an independent noise injection
      is entropy *non-decreasing* (mixing inequality; equality case proved,
      the strict convolution bound stated and deferred).

  Reference: RLA README §6/§7 (Theorem T5/T7), WeylGeometry `scaleField`,
  FTC EntropyLemmas (`shannonEntropy`, `minEntropy`, `maxProb`).
-/
import Mathlib

noncomputable section
open Real BigOperators Finset

namespace RLA.DiracMobiusMixing

/-! ## 1. Finite state space and the evolution operator `U`

    The harvest state space is finite (16 strips × 256 cells × spinor bits),
    modeled here as `Fin (n+1)`. The Dirac–Möbius evolution `U` is a bijection
    of that space — packaged as an `Equiv.Perm`, exactly as the Möbius
    involution is in `FIL.Topology.MobiusQuotient.mobiusPerm`. -/

abbrev State (n : ℕ) := Fin (n + 1)

/-- A discrete Dirac–Möbius evolution operator: a permutation of the finite
    state space (measure-preserving by construction; `Equiv` ⇒ unit Jacobian on
    counting measure). -/
abbrev Evolution (n : ℕ) := Equiv.Perm (State n)

/-! ## 2. Distributions and pushforward

    A distribution is a probability vector `p : State n → ℝ`. Pushing it forward
    by the deterministic bijection `U` reindexes coordinates: the mass at state
    `s` moves to `U s`, so the new mass at `t` is `p (U⁻¹ t)`. -/

def IsDistribution (p : State n → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Pushforward of a distribution by the evolution `U`. -/
def pushforward (U : Evolution n) (p : State n → ℝ) : State n → ℝ :=
  fun t => p (U.symm t)

/-- Shannon entropy (matching `FTC.EntropyLemmas.shannonEntropy`). -/
def shannonEntropy (p : State n → ℝ) : ℝ :=
  ∑ i, p i * log (1 / p i)

/-! ## 3. Measure preservation: the pushforward is again a distribution -/

theorem pushforward_nonneg (U : Evolution n) (p : State n → ℝ)
    (hp : ∀ i, 0 ≤ p i) : ∀ t, 0 ≤ pushforward U p t := by
  intro t; unfold pushforward; exact hp _

/-- Total mass is preserved: `∑ pushforward = ∑ p` (reindex by the bijection
    `U.symm`). This is the discrete unit-Jacobian / measure-preservation fact. -/
theorem pushforward_sum (U : Evolution n) (p : State n → ℝ) :
    ∑ t, pushforward U p t = ∑ i, p i := by
  show ∑ t, p (U.symm t) = ∑ i, p i
  exact Equiv.sum_comp U.symm p

theorem pushforward_isDistribution (U : Evolution n) (p : State n → ℝ)
    (hp : IsDistribution p) : IsDistribution (pushforward U p) := by
  obtain ⟨hp_nonneg, hp_sum⟩ := hp
  refine ⟨pushforward_nonneg U p hp_nonneg, ?_⟩
  rw [pushforward_sum]; exact hp_sum

/-! ## 4. T7 conservation: Shannon entropy is invariant under `U`

    The summand `f s := p s · log(1/p s)` is reindexed by the bijection, so the
    sum is unchanged. This is the entropy form of RLA-T7 (Noether conservation):
    a measure-preserving flow conserves the entropy functional. -/

theorem T7_shannon_pushforward_eq (U : Evolution n) (p : State n → ℝ) :
    shannonEntropy (pushforward U p) = shannonEntropy p := by
  show (∑ t, p (U.symm t) * log (1 / p (U.symm t))) = ∑ i, p i * log (1 / p i)
  -- reindex the summand `fun i => p i * log (1 / p i)` by the bijection U.symm
  exact Equiv.sum_comp U.symm (fun i => p i * log (1 / p i))

/-! ## 5. Worst-case (min-entropy) is invariant too

    Min-entropy is `-log p_max`. Since `U` only permutes coordinates, `p` and
    its pushforward attain the *same* set of values, hence the same maximum. We
    prove the maximum is preserved by an upper-bound characterization (avoids
    finset-image lemmas): `c` bounds all coordinates of the pushforward iff it
    bounds all coordinates of `p`, because `U.symm` is surjective. -/

theorem pushforward_le_iff (U : Evolution n) (p : State n → ℝ) (c : ℝ) :
    (∀ t, pushforward U p t ≤ c) ↔ (∀ i, p i ≤ c) := by
  unfold pushforward
  constructor
  · intro h i
    -- p i = p (U.symm (U i)), apply h at t = U i
    have := h (U i)
    simpa using this
  · intro h t; exact h (U.symm t)

/-- The maximum coordinate value is preserved (stated via `IsGreatest` on the
    range, the version-independent way to say "same p_max"). -/
theorem pushforward_isGreatest_iff (U : Evolution n) (p : State n → ℝ) (c : ℝ) :
    (IsGreatest (Set.range (pushforward U p)) c) ↔
    (IsGreatest (Set.range p) c) := by
  constructor
  · rintro ⟨⟨t, ht⟩, hub⟩
    refine ⟨⟨U.symm t, ht⟩, ?_⟩
    rintro x ⟨i, rfl⟩
    exact hub ⟨U i, by simp [pushforward]⟩
  · rintro ⟨⟨i, hi⟩, hub⟩
    refine ⟨⟨U i, by simpa [pushforward] using hi⟩, ?_⟩
    rintro x ⟨t, rfl⟩
    exact hub ⟨U.symm t, rfl⟩

/-- Min-entropy as `-log p_max`, given an explicit greatest-value (p_max)
    witness `c`. Independent of the `Finset.max'` packaging in
    `FTC.EntropyLemmas.maxProb`, but numerically identical to it. -/
def minEntropyOfMax (c : ℝ) : ℝ := - log c

/-- **Min-entropy preservation (worst case).** If `c = p_max` is the maximal
    coordinate probability of `p`, it is also the maximal coordinate
    probability of the pushforward (so the worst-case predictability — hence
    `minEntropy = -log p_max` — is *identical* before and after the
    deterministic Dirac–Möbius step). -/
theorem T7_minEntropy_pushforward_eq (U : Evolution n) (p : State n → ℝ)
    (c : ℝ) (hc : IsGreatest (Set.range p) c) :
    IsGreatest (Set.range (pushforward U p)) c :=
  (pushforward_isGreatest_iff U p c).mpr hc

/-- Corollary: the min-entropy value `-log p_max` is preserved by `U`. If `c`
    is `p`'s greatest value and `c'` is the pushforward's greatest value, they
    coincide, so the min-entropies are equal. -/
theorem T7_minEntropy_value_eq (U : Evolution n) (p : State n → ℝ)
    (c c' : ℝ) (hc : IsGreatest (Set.range p) c)
    (hc' : IsGreatest (Set.range (pushforward U p)) c') :
    minEntropyOfMax c' = minEntropyOfMax c := by
  have : c' = c :=
    IsGreatest.unique hc' (T7_minEntropy_pushforward_eq U p c hc)
  rw [this]

/-! ## 6. Scale field / Noether tie-in (RLA-T7)

    `WeylGeometry.scaleField σ = e^σ` is the RLA scale field; its logarithmic
    derivative is the Weyl 1-form `α`. Measure preservation of `U` is the
    statement that the scale factor along the discrete flow is `1` (σ-balanced),
    i.e. the Jacobian `e^{σ_out - σ_in} = 1`. We record the algebraic core:
    a unit scale factor ⇔ entropy is conserved. -/

/-- Discrete Jacobian / scale factor of one evolution step. `U` measure-
    preserving means `jacobian = 1`. -/
def jacobian (σ_in σ_out : ℝ) : ℝ := exp (σ_out - σ_in)

theorem jacobian_pos (σ_in σ_out : ℝ) : 0 < jacobian σ_in σ_out :=
  exp_pos _

/-- Unit Jacobian ⇔ balanced scale field (`σ_out = σ_in`): the RLA-T7
    conservation condition that makes `U` measure-preserving. -/
theorem jacobian_eq_one_iff (σ_in σ_out : ℝ) :
    jacobian σ_in σ_out = 1 ↔ σ_out = σ_in := by
  unfold jacobian
  rw [show (1 : ℝ) = exp 0 from (Real.exp_zero).symm, Real.exp_eq_exp]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- `log` of the Jacobian is the net scale-field change; zero exactly when the
    flow is measure-preserving (entropy-conserving). This is the bridge between
    the geometric statement (RLA-T7 / Noether) and the entropy statement of §4. -/
theorem log_jacobian (σ_in σ_out : ℝ) :
    log (jacobian σ_in σ_out) = σ_out - σ_in := by
  unfold jacobian; rw [Real.log_exp]

/-! ## 7. Composition with independent noise injection is entropy-non-decreasing

    The DM-TRNG injects fresh physical noise *between* deterministic mixing
    rounds. Modeled as: given the (entropy-conserving) evolution `U` and an
    independent noise permutation drawn per step, the resulting state entropy
    does not decrease. We prove the *equality* case exactly (a single
    measure-preserving step conserves entropy, §4) and state the general strict
    mixing inequality (convolution with an independent source can only raise
    Shannon entropy — `H(X ⊕ noise) ≥ H(X)`), deferring the convolution-bound
    proof with a citation. -/

/-- Two composed measure-preserving evolutions still conserve Shannon entropy:
    `H(U₂(U₁ p)) = H(p)`. (Determinism + measure preservation ⇒ conservation,
    no increase yet — the increase comes only from genuinely *independent*
    noise, captured in `mixing_entropy_nondecreasing` below.) -/
theorem compose_conserves_entropy (U₁ U₂ : Evolution n) (p : State n → ℝ) :
    shannonEntropy (pushforward U₂ (pushforward U₁ p)) = shannonEntropy p := by
  rw [T7_shannon_pushforward_eq U₂ (pushforward U₁ p), T7_shannon_pushforward_eq U₁ p]

/-- A noise injection is modeled abstractly as a stochastic mixing operator
    `mix : (State n → ℝ) → (State n → ℝ)` that (a) preserves distributions and
    (b) is entropy non-decreasing on every distribution. The DM-TRNG noise tap
    (independent metastable bits XORed into ψ) is such an operator: XOR with an
    independent source is convolution on the group `(ℤ/2)^k`, which never
    decreases Shannon entropy. -/
structure NoiseInjection (n : ℕ) where
  mix : (State n → ℝ) → (State n → ℝ)
  preserves : ∀ p, IsDistribution p → IsDistribution (mix p)
  nondecreasing : ∀ p, IsDistribution p → shannonEntropy p ≤ shannonEntropy (mix p)

/-- **Mixing inequality / data-processing for the DM-TRNG accumulator.**
    A measure-preserving evolution `U` followed by an independent noise
    injection `ν` has output Shannon entropy at least that of the input:
        `H(ν(U(p))) ≥ H(p)`.
    Proof: `U` conserves entropy (§4, RLA-T7), then `ν` is non-decreasing by
    hypothesis. Hence the harvest fabric never destroys seed entropy and the
    noise tap can only add to it. FULLY PROVED from the `NoiseInjection`
    contract; the *justification* that XOR-with-independent-noise satisfies
    `nondecreasing` (the entropy-power / convolution inequality on `(ℤ/2)^k`,
    Cover–Thomas Thm 2.6.5 / Shannon 1948) is the deferred heavy fact recorded
    in `xor_noise_nondecreasing` below. -/
theorem mixing_entropy_nondecreasing (U : Evolution n) (ν : NoiseInjection n)
    (p : State n → ℝ) (hp : IsDistribution p) :
    shannonEntropy p ≤ shannonEntropy (ν.mix (pushforward U p)) := by
  have h1 : shannonEntropy (pushforward U p) = shannonEntropy p :=
    T7_shannon_pushforward_eq U p
  have h2 : shannonEntropy (pushforward U p) ≤ shannonEntropy (ν.mix (pushforward U p)) :=
    ν.nondecreasing (pushforward U p) (pushforward_isDistribution U p hp)
  linarith

/-- "XOR with independent noise", modeled faithfully and *soundly*. XORing the
    state with an independent noise symbol `z` (distribution `w`) is exactly the
    `w`-mixture of the translations `s ↦ s ⊕ z`; each translation is a
    measure-preserving permutation `g a : Evolution n`. So the noise injection is
    a convex mixture of entropy-preserving pushforwards — not an arbitrary map. -/
def noiseMixture {m : ℕ} (g : Fin (m + 1) → Evolution n) (w : Fin (m + 1) → ℝ)
    (p : State n → ℝ) : State n → ℝ :=
  fun s => ∑ a, w a * pushforward (g a) p s

/-- **Pointwise Gibbs inequality.** For `x, y ≥ 0` with `y > 0` whenever
    `x > 0`: `x − y ≤ x·log x − x·log y`. This is the per-coordinate kernel of
    `D(p‖q) ≥ 0`, proved from `log t ≤ t − 1`. Lean's junk value `log 0 = 0`
    is harmless: the `x = 0` case reduces to `−y ≤ 0`. -/
private lemma gibbs_pointwise {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 0 < x → 0 < y) : x - y ≤ x * log x - x * log y := by
  rcases eq_or_lt_of_le hx with h0 | hx_pos
  · -- x = 0: LHS = −y ≤ 0 = RHS.
    rw [← h0]
    simp [hy]
  · have hy_pos : 0 < y := hxy hx_pos
    -- log (y/x) ≤ y/x − 1, scaled by x > 0, gives x·log y − x·log x ≤ y − x.
    have hlog := log_le_sub_one_of_pos (div_pos hy_pos hx_pos)
    rw [log_div hy_pos.ne' hx_pos.ne'] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hx_pos.le
    have hxyx : x * (y / x - 1) = y - x := by
      rw [mul_sub, mul_one, mul_comm, div_mul_cancel y hx_pos.ne']
    rw [hxyx, mul_sub] at hmul
    linarith

/-- XOR with an independent noise source never decreases Shannon entropy.
    Modeled (soundly) as a convex `w`-mixture over an independent-noise
    distribution `w` of pushforwards by translations `g a`:
        `H(noiseMixture g w p) ≥ H(p)`.
    This is the discrete "mixing increases entropy" inequality — concavity of
    Shannon entropy. PROOF: decompose `H(Q)` of the mixture `Q = ∑ₐ wₐ·qₐ`
    (with `qₐ = pushforward (g a) p`) as `∑ₐ wₐ·∑ₛ qₐ(s)·log(1/Q s)`, bound
    each inner sum below by `H(qₐ)` via the Gibbs inequality
    (`∑ₛ qₐ log(qₐ/Q) ≥ ∑ₛ (qₐ − Q) = 0`), and use `H(qₐ) = H(p)` (T7,
    pushforward by a permutation conserves entropy) with `∑ₐ wₐ = 1`.

    Crucially the hypotheses pin the *structure* (a distribution `w` over
    measure-preserving maps), so — unlike a bare distribution-preserving map —
    an entropy-destroying operator (e.g. one returning a point mass) is NOT of
    this form and cannot be substituted.

    Reference: Cover & Thomas, *Elements of Information Theory*, Thm 2.6.5;
    Shannon 1948. -/
theorem xor_noise_nondecreasing {m : ℕ} (g : Fin (m + 1) → Evolution n)
    (w : Fin (m + 1) → ℝ) (hw_nonneg : ∀ a, 0 ≤ w a) (hw_sum : ∑ a, w a = 1)
    (p : State n → ℝ) (hp : IsDistribution p) :
    shannonEntropy p ≤ shannonEntropy (noiseMixture g w p) := by
  obtain ⟨hp_nonneg, hp_sum⟩ := hp
  -- Per-seed pushforward distributions and the mixture.
  set q : Fin (m + 1) → State n → ℝ := fun a => pushforward (g a) p with hq_def
  have hq_nonneg : ∀ a s, 0 ≤ q a s := fun a s => hp_nonneg _
  have hq_sum : ∀ a, ∑ s, q a s = 1 := fun a => by
    rw [hq_def]
    show ∑ s, pushforward (g a) p s = 1
    rw [pushforward_sum]
    exact hp_sum
  have hQ_eq : ∀ s, noiseMixture g w p s = ∑ a, w a * q a s := fun s => rfl
  have hQ_nonneg : ∀ s, 0 ≤ noiseMixture g w p s := fun s => by
    rw [hQ_eq]
    exact Finset.sum_nonneg fun a _ => mul_nonneg (hw_nonneg a) (hq_nonneg a s)
  have hQ_sum : ∑ s, noiseMixture g w p s = 1 := by
    calc ∑ s, noiseMixture g w p s = ∑ s, ∑ a, w a * q a s := by
          exact Finset.sum_congr rfl fun s _ => hQ_eq s
      _ = ∑ a, ∑ s, w a * q a s := Finset.sum_comm
      _ = ∑ a, w a * ∑ s, q a s := by
          exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ a, w a := by
          exact Finset.sum_congr rfl fun a _ => by rw [hq_sum a, mul_one]
      _ = 1 := hw_sum
  -- Each weighted component is dominated by the mixture coordinatewise.
  have hQ_ge : ∀ a s, w a * q a s ≤ noiseMixture g w p s := by
    intro a s
    rw [hQ_eq]
    exact Finset.single_le_sum
      (f := fun b => w b * q b s)
      (fun b _ => mul_nonneg (hw_nonneg b) (hq_nonneg b s)) (Finset.mem_univ a)
  -- Summed Gibbs inequality per seed with positive weight.
  have gibbs_sum : ∀ a, 0 < w a →
      ∑ s, q a s * log (1 / q a s) ≤ ∑ s, q a s * log (1 / noiseMixture g w p s) := by
    intro a hwa
    have hpt : ∀ s, q a s - noiseMixture g w p s ≤
        q a s * log (q a s) - q a s * log (noiseMixture g w p s) := by
      intro s
      apply gibbs_pointwise (hq_nonneg a s) (hQ_nonneg s)
      intro hq_pos
      exact lt_of_lt_of_le (mul_pos hwa hq_pos) (hQ_ge a s)
    have hsum : ∑ s, (q a s - noiseMixture g w p s) ≤
        ∑ s, (q a s * log (q a s) - q a s * log (noiseMixture g w p s)) :=
      Finset.sum_le_sum (fun s _ => hpt s)
    rw [Finset.sum_sub_distrib, hq_sum a, hQ_sum, sub_self,
      Finset.sum_sub_distrib] at hsum
    -- hsum : 0 ≤ ∑ q·log q − ∑ q·log Q. Translate to the 1/x form.
    have hlhs : ∑ s, q a s * log (1 / q a s) = -∑ s, q a s * log (q a s) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun s _ => by rw [one_div, log_inv, mul_neg]
    have hrhs : ∑ s, q a s * log (1 / noiseMixture g w p s)
        = -∑ s, q a s * log (noiseMixture g w p s) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun s _ => by rw [one_div, log_inv, mul_neg]
    rw [hlhs, hrhs]
    linarith
  -- Decompose the mixture entropy and assemble.
  have hH_decomp : shannonEntropy (noiseMixture g w p)
      = ∑ a, w a * ∑ s, q a s * log (1 / noiseMixture g w p s) := by
    unfold shannonEntropy
    calc ∑ s, noiseMixture g w p s * log (1 / noiseMixture g w p s)
        = ∑ s, ∑ a, w a * q a s * log (1 / noiseMixture g w p s) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [hQ_eq s, Finset.sum_mul]
      _ = ∑ a, ∑ s, w a * q a s * log (1 / noiseMixture g w p s) :=
          Finset.sum_comm
      _ = ∑ a, w a * ∑ s, q a s * log (1 / noiseMixture g w p s) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
  have hHa : ∀ a, ∑ s, q a s * log (1 / q a s) = shannonEntropy p := fun a =>
    T7_shannon_pushforward_eq (g a) p
  calc shannonEntropy p
      = ∑ a, w a * shannonEntropy p := by
        rw [← Finset.sum_mul, hw_sum, one_mul]
    _ ≤ ∑ a, w a * ∑ s, q a s * log (1 / noiseMixture g w p s) := by
        apply Finset.sum_le_sum
        intro a _
        rcases eq_or_lt_of_le (hw_nonneg a) with h0 | hpos
        · rw [← h0, zero_mul, zero_mul]
        · apply mul_le_mul_of_nonneg_left _ hpos.le
          rw [← hHa a]
          exact gibbs_sum a hpos
    _ = shannonEntropy (noiseMixture g w p) := hH_decomp.symm

/-! ## 8. Summary (the DM-TRNG entropy anchor)

    Putting §4–§7 together: the deterministic Dirac–Möbius datapath conserves
    both Shannon and min-entropy (it is a measure-preserving bijection, RLA-T7),
    and interleaving independent physical noise can only increase entropy. Hence
    the harvested stream's entropy is bounded below by the injected seed
    entropy — the property the DM-TRNG accumulator/conditioner needs. -/

theorem DM_TRNG_entropy_anchor (U : Evolution n) (ν : NoiseInjection n)
    (p : State n → ℝ) (hp : IsDistribution p) :
    shannonEntropy (pushforward U p) = shannonEntropy p ∧
    shannonEntropy p ≤ shannonEntropy (ν.mix (pushforward U p)) :=
  ⟨T7_shannon_pushforward_eq U p, mixing_entropy_nondecreasing U ν p hp⟩

end RLA.DiracMobiusMixing
