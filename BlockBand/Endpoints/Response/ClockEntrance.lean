module

public import BlockBand.Endpoints.Response.FractionalTrace
public import BlockBand.Endpoints.Response.ClockEntranceLogistic

/-!
# Finite fractional entrance of the near clock after positive travel

Law: the unabsorbed two-input path `growthPathLaw W b` with matched leads, fixed `0 < b < 1/2`,
bulk energy `-2 < E < 2`; clock `A = nearClock` of a unit source (`IsUnitSource t₁ R q`), time
zero `t₁ + R`.

## Main results

* `ce_smallChannels`: the `smallChannels` clause, with no hypothesis, obtained by integrating the
  pointwise bound `smallChannelPower_le_rpow_mul_fracTrace`.
* `ce_later_of_logistic`: the `later` clause from the finite-`W` logistic recursion
  `ClockFractionalLogisticRecursion` and the deterministic discrete logistic comparison
  `ce_logistic_bound`, started at `s₁/2`, with constant `B + 8/(c s₁)` chosen before the source and
  `t₁`.
* `ce_entrance_of_later`: the `entrance` clause; `later` on `[ε, ε]` bounds the limsup.
* `clockFractionalEntrance_holds`: `ClockFractionalEntranceContract` from the logistic recursion.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open scoped ENNReal
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Endpoints

/-!
## `smallChannels`
-/

/-- The small-channel clock bound, the `smallChannels` clause of
`ClockFractionalEntranceContract`, with no hypothesis: for `0 < p < r < 1`, every unit source,
every threshold `a ≥ 0`, every width `W` and every length `j`,
`E Σ_{λ_i(A) ≤ a} λ_i(A)^r ≤ a^{r-p} E H_p` (lower integrals in `ℝ≥0∞`). -/
theorem ce_smallChannels : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < r → r < 1 → ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
      ∀ a : ℝ, 0 ≤ a → ∀ W j : ℕ,
        ∫⁻ ω, ENNReal.ofReal (smallChannelPower a r (nearClock b E W j q ω))
            ∂growthPathLaw W b ≤
          ENNReal.ofReal (a ^ (r - p)) *
            ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b E W j q ω)) ∂growthPathLaw W b := by
  intro b _ _ E _ _ p r hp hpr _ t₁ R q _ a ha W j
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha _)]
  exact ENNReal.ofReal_le_ofReal
    (smallChannelPower_le_rpow_mul_fracTrace ha (hp.trans hpr) hpr.le _)

/-!
## The finite-`W` logistic recursion
-/

/-- The finite-`W` logistic recursion for the fractional trace. Fixed `b`, bulk `E`, `0 < p < 1`,
a comparison interval of travel times `[s₀, s₂]`, `0 < s₀ ≤ s₂`; constants `C` and `c > 0` chosen
before the source and the preceding middle length `t₁` (they may depend on `p, s₀, s₂`); for every
unit source an `o(W⁻²)` error `e` (`W² e(W) → 0`) and `W₀`; for `W ≥ W₀` a nonnegative real
sequence `y` (the weighted expectation) with `E H_p(A_j) ≤ y_j` on
`travelLength W t₁ R s₀ ≤ j ≤ travelLength W t₁ R s₂` and
`y_{j+1} ≤ y_j + W⁻¹(C y_j - c y_j² + C) + e(W)` on the steps of that range. -/
def ClockFractionalLogisticRecursion : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ s₀ s₂ : ℝ, 0 < s₀ → s₀ ≤ s₂ →
      ∃ C c : ℝ, 0 < c ∧ ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
        ∃ e : ℕ → ℝ, Tendsto (fun W : ℕ => (W : ℝ) ^ 2 * e W) atTop (𝓝 0) ∧
        ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∃ y : ℕ → ℝ, (∀ j, 0 ≤ y j) ∧
          (∀ j : ℕ, travelLength W t₁ R s₀ ≤ j → j ≤ travelLength W t₁ R s₂ →
            ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b E W j q ω)) ∂growthPathLaw W b ≤
              ENNReal.ofReal (y j)) ∧
          ∀ j : ℕ, travelLength W t₁ R s₀ ≤ j → j < travelLength W t₁ R s₂ →
            y (j + 1) ≤ y j + (W : ℝ)⁻¹ * (C * y j - c * y j ^ 2 + C) + e W

/-!
## `later` and `entrance`
-/

/-- Floor bookkeeping: for `0 ≤ t₁ + R`, `0 < s₁ ≤ s`, `W s₁ ≥ 4`, the travel lengths satisfy
`s₁/4 ≤ W⁻¹ (⌊W(t₁+R+s)⌋ - ⌊W(t₁+R+s₁/2)⌋)`. -/
theorem ce_travel_gap {t₁ R s₁ s : ℝ} (hTR : 0 ≤ t₁ + R) (hs₁ : 0 < s₁) (hs : s₁ ≤ s)
    {W : ℕ} (hW : 4 ≤ (W : ℝ) * s₁) :
    s₁ / 4 ≤ (W : ℝ)⁻¹ *
      ((travelLength W t₁ R s : ℝ) - travelLength W t₁ R (s₁ / 2)) := by
  have hW0 : 0 < (W : ℝ) := by
    by_contra h
    have : (W : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [this, zero_mul] at hW; linarith
  have hx0 : 0 ≤ (W : ℝ) * (t₁ + R + s₁ / 2) := mul_nonneg hW0.le (by linarith)
  have hlo : (W : ℝ) * (t₁ + R + s) < (travelLength W t₁ R s : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hhi : (travelLength W t₁ R (s₁ / 2) : ℝ) ≤ (W : ℝ) * (t₁ + R + s₁ / 2) :=
    Nat.floor_le hx0
  rw [le_inv_mul_iff₀ hW0]
  nlinarith

/-- Monotonicity of the travel length in the travel time. -/
theorem ce_travelLength_mono (W : ℕ) (t₁ R : ℝ) {s s' : ℝ} (h : s ≤ s') :
    travelLength W t₁ R s ≤ travelLength W t₁ R s' :=
  Nat.floor_le_floor (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg W))

/-- The `later` clause of `ClockFractionalEntranceContract` from the finite-`W` logistic
recursion: on `[s₁, s₂]`, `0 < s₁ ≤ s₂`, run the recursion on the comparison interval `[s₁/2, s₂]`
and apply the discrete logistic comparison with elapsed time `s₁/4` (in units of `W`). The constant
`B + 2/(c s₁/4)`, with `B` the logistic level of `(max C 0 + 1, c)`, depends on `b, E, p, s₁, s₂`
only. -/
theorem ce_later_of_logistic (hLog : ClockFractionalLogisticRecursion) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ p : ℝ, 0 < p → p < 1 → ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ ≤ s₂ →
        ∃ C : ℝ, ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
          ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ s ∈ Set.Icc s₁ s₂,
            clockFracMoment b E p W t₁ R s q ≤ ENNReal.ofReal C := by
  intro b hb hb' E hE hE' p hp hp' s₁ s₂ hs₁ hs₁₂
  obtain ⟨C, c, hc, hrecAll⟩ :=
    hLog b hb hb' E hE hE' p hp hp' (s₁ / 2) s₂ (by linarith) (by linarith)
  set C' : ℝ := max C 0 + 1 with hC'
  have hC'0 : 0 ≤ C' := by have := le_max_right C 0; linarith
  set B := ce_logisticLevel C' c with hB
  refine ⟨B + 2 / (c * (s₁ / 4)), fun t₁ R q hq => ?_⟩
  obtain ⟨e, he, W₀, hW₀⟩ := hrecAll t₁ R q hq
  have hTR : 0 ≤ t₁ + R := by linarith [hq.1, hq.2.1]
  -- the width conditions
  have hev : ∀ᶠ W : ℕ in atTop, (W : ℝ) ^ 2 * e W < 1 ∧ 1 ≤ (W : ℝ) ∧
      4 ≤ (W : ℝ) * s₁ ∧ C' * B ≤ (W : ℝ) := by
    have htend : Tendsto (fun W : ℕ => (W : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h4 : ∀ᶠ W : ℕ in atTop, 4 ≤ (W : ℝ) * s₁ :=
      (htend.eventually_ge_atTop (4 / s₁)).mono fun W hW => by
        rw [div_le_iff₀ hs₁] at hW; exact hW
    exact (he.eventually (gt_mem_nhds zero_lt_one)).and
      ((htend.eventually_ge_atTop 1).and (h4.and (htend.eventually_ge_atTop (C' * B))))
  obtain ⟨W₁, hW₁⟩ := eventually_atTop.1 hev
  refine ⟨max W₀ W₁, fun W hW s hs => ?_⟩
  obtain ⟨he1, hW1, hWs, hWB⟩ := hW₁ W (le_of_max_le_right hW)
  obtain ⟨y, hy0, hydom, hyrec⟩ := hW₀ W (le_of_max_le_left hW)
  have hW0 : 0 < (W : ℝ) := by linarith
  -- the recursion with `C'` (absorbing the error `e W ≤ W⁻² ≤ W⁻¹`)
  have hrec' : ∀ n, travelLength W t₁ R (s₁ / 2) ≤ n → n < travelLength W t₁ R s₂ →
      y (n + 1) ≤ y n + (W : ℝ)⁻¹ * (C' * y n - c * y n ^ 2 + C') := by
    intro n h0 h2
    have h := hyrec n h0 h2
    have heW : e W ≤ (W : ℝ)⁻¹ := by
      have hsq : 0 < (W : ℝ) ^ 2 := by positivity
      have : e W < 1 / (W : ℝ) ^ 2 := by rw [lt_div_iff₀ hsq]; linarith
      have : 1 / (W : ℝ) ^ 2 ≤ (W : ℝ)⁻¹ := by
        rw [one_div, inv_le_inv₀ hsq hW0]; nlinarith
      linarith
    have hCy : C * y n ≤ max C 0 * y n :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (hy0 n)
    have hCC : C ≤ max C 0 := le_max_left _ _
    have hWinv : 0 ≤ (W : ℝ)⁻¹ := inv_nonneg.mpr hW0.le
    have : (W : ℝ)⁻¹ * (C * y n - c * y n ^ 2 + C) + e W ≤
        (W : ℝ)⁻¹ * (C' * y n - c * y n ^ 2 + C') := by
      have hdiff : (W : ℝ)⁻¹ * (C' * y n - c * y n ^ 2 + C') -
          ((W : ℝ)⁻¹ * (C * y n - c * y n ^ 2 + C)) =
          (W : ℝ)⁻¹ * ((max C 0 * y n - C * y n) + (max C 0 - C) + y n + 1) := by
        rw [hC']; ring
      have : (W : ℝ)⁻¹ ≤ (W : ℝ)⁻¹ * ((max C 0 * y n - C * y n) + (max C 0 - C) + y n + 1) := by
        have : 1 ≤ (max C 0 * y n - C * y n) + (max C 0 - C) + y n + 1 := by
          linarith [hy0 n]
        nlinarith
      linarith
    linarith
  have hsmall : (W : ℝ)⁻¹ * C' * B ≤ 1 := by
    rw [mul_assoc, inv_mul_le_iff₀ hW0]; linarith
  set n := travelLength W t₁ R s
  have hn0 : travelLength W t₁ R (s₁ / 2) ≤ n := ce_travelLength_mono W t₁ R (by linarith [hs.1])
  have hn2 : n ≤ travelLength W t₁ R s₂ := ce_travelLength_mono W t₁ R hs.2
  have hbound := ce_logistic_bound hC'0 hc (inv_pos.mpr hW0) hsmall y hy0
    (travelLength W t₁ R (s₁ / 2)) (travelLength W t₁ R s₂) hrec' n hn0 hn2 (s₁ / 4)
    (by linarith) (ce_travel_gap hTR hs₁ hs.1 hWs)
  have hdom := hydom n hn0 hn2
  exact hdom.trans (ENNReal.ofReal_le_ofReal hbound)

/-- The `entrance` clause of `ClockFractionalEntranceContract` from the `later` clause on the
degenerate interval `[ε, ε]`: the eventual bound bounds the `limsup`. -/
theorem ce_entrance_of_later
    (hLater : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ p : ℝ, 0 < p → p < 1 → ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ ≤ s₂ →
        ∃ C : ℝ, ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
          ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ s ∈ Set.Icc s₁ s₂,
            clockFracMoment b E p W t₁ R s q ≤ ENNReal.ofReal C) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ p : ℝ, 0 < p → p < 1 → ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
          limsup (fun W : ℕ => clockFracMoment b E p W t₁ R ε q) atTop ≤ ENNReal.ofReal C := by
  intro b hb hb' E hE hE' p hp hp' ε hε
  obtain ⟨C, hC⟩ := hLater b hb hb' E hE hE' p hp hp' ε ε hε le_rfl
  refine ⟨C, fun t₁ R q hq => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC t₁ R q hq
  exact limsup_le_of_le (by isBoundedDefault)
    (eventually_atTop.2 ⟨W₀, fun W hW => hW₀ W hW ε ⟨le_rfl, le_rfl⟩⟩)

/-- **The clock fractional-entrance lemma**: `ClockFractionalEntranceContract`.
The only hypothesis is the finite-`W` recursion `ClockFractionalLogisticRecursion`; the
`smallChannels` clause uses no hypothesis (`ce_smallChannels`).
-/
theorem clockFractionalEntrance_holds (hLog : ClockFractionalLogisticRecursion) :
    ClockFractionalEntranceContract where
  entrance := ce_entrance_of_later (ce_later_of_logistic hLog)
  later := ce_later_of_logistic hLog
  smallChannels := ce_smallChannels

end BlockBand.Endpoints
