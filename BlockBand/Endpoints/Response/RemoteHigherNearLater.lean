module

public import BlockBand.Endpoints.Response.RemoteHigherNearDefs
public import BlockBand.Endpoints.Response.RemoteHigherNearLogistic
public import BlockBand.Endpoints.Response.ClockEntrance

/-!
# Finite-`W` bounds of higher clock moments after positive travel

`rhn_higherLater_of_recursion : RhnHigherWeightedRecursion → RhnHigherLater`: on `[s₁, s₂]` run
the recursion of the weighted expectation `y_j = E[(1 + Kδ₀) H_p^r]` on the comparison interval
`[s₁/2, s₂]` and apply the higher discrete comparison `rhn_logistic_bound` with elapsed time
`s₁/4` (in units of `W`); `E H_p^r ≤ y_j` because the weight is `≥ 1`. The constant
`B + (8r/(c s₁))^r`, `B = rhn_logisticLevel (max C 0 + 1) c r`, depends on `b, E, p, r, s₁, s₂`
only (the `r`-analogue of the committed `ce_later_of_logistic`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open scoped ENNReal
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Endpoints

/-- The scalar weight `1 + Kδ₀` is `≥ 1` for `K ≥ 0`. -/
theorem rhn_one_le_weight {K : ℝ} (hK : 0 ≤ K) (b E : ℝ) (W j : ℕ) (ω : GrowthPath W) :
    1 ≤ ce_weight K b E W j ω := by
  unfold ce_weight ce_jet0 jetDistance0
  have := mul_nonneg hK (norm_nonneg ((W : ℂ)⁻¹ * (passiveResolvent b E
    (BlockBand.Internal.Contracts.TransmissionStatements.pathX b E W j ω)).trace -
      BlockBand.Internal.Contracts.Layers.matchedA E))
  linarith

/-- `E H_p(A_j)^r ≤ E[(1 + Kδ₀) H_p(A_j)^r]` (`K ≥ 0`, `r ≥ 0`). -/
theorem rhn_lintegral_rpow_le_weighted {K : ℝ} (hK : 0 ≤ K) (b E p : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (W j : ℕ) (q : ℝ → ℝ) :
    ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b E W j q ω)) ^ r ∂growthPathLaw W b ≤
      rhn_weightedHigherMoment K b E p r W j q := by
  unfold rhn_weightedHigherMoment
  refine lintegral_mono fun ω => ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (fracTrace_nonneg _ _) hr]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := rhn_one_le_weight hK b E W j ω
  have h0 : 0 ≤ ce_fracClock b E p W j q ω ^ r := Real.rpow_nonneg (fracTrace_nonneg _ _) _
  unfold ce_fracClock at h0 ⊢
  nlinarith

/-- **`RhnHigherLater` from the higher weighted recursion**: the
`r`-analogue of `ce_later_of_logistic`. -/
theorem rhn_higherLater_of_recursion (hRec : RhnHigherWeightedRecursion) : RhnHigherLater := by
  intro b hb hb' E hE hE' p r hp hp' hr hpr s₁ s₂ hs₁ hs₁₂
  obtain ⟨K, C, c, hK, hc, hrecAll⟩ :=
    hRec b hb hb' E hE hE' p r hp hp' hr hpr (s₁ / 2) s₂ (by linarith) (by linarith)
  set C' : ℝ := max C 0 + 1 with hC'
  have hC'0 : 0 ≤ C' := by have := le_max_right C 0; linarith
  set B := rhn_logisticLevel C' c r with hB
  refine ⟨B + (2 * r / (c * (s₁ / 4))) ^ r, fun t₁ R q hq => ?_⟩
  obtain ⟨e, he, W₀, hW₀⟩ := hrecAll t₁ R q hq
  have hTR : 0 ≤ t₁ + R := by linarith [hq.1, hq.2.1]
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
  obtain ⟨hfin, hyrec⟩ := hW₀ W (le_of_max_le_left hW)
  have hW0 : 0 < (W : ℝ) := by linarith
  set y : ℕ → ℝ := fun j => (rhn_weightedHigherMoment K b E p r W j q).toReal with hy
  have hy0 : ∀ j, 0 ≤ y j := fun j => ENNReal.toReal_nonneg
  have hrec' : ∀ n, travelLength W t₁ R (s₁ / 2) ≤ n → n < travelLength W t₁ R s₂ →
      y (n + 1) ≤ y n + (W : ℝ)⁻¹ * (C' * y n - c * y n ^ (1 + 1 / r) + C') := by
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
    have : (W : ℝ)⁻¹ * (C * y n - c * y n ^ (1 + 1 / r) + C) + e W ≤
        (W : ℝ)⁻¹ * (C' * y n - c * y n ^ (1 + 1 / r) + C') := by
      have hdiff : (W : ℝ)⁻¹ * (C' * y n - c * y n ^ (1 + 1 / r) + C') -
          ((W : ℝ)⁻¹ * (C * y n - c * y n ^ (1 + 1 / r) + C)) =
          (W : ℝ)⁻¹ * ((max C 0 * y n - C * y n) + (max C 0 - C) + y n + 1) := by
        rw [hC']; ring
      have : (W : ℝ)⁻¹ ≤ (W : ℝ)⁻¹ * ((max C 0 * y n - C * y n) + (max C 0 - C) + y n + 1) := by
        have : 1 ≤ (max C 0 * y n - C * y n) + (max C 0 - C) + y n + 1 := by
          linarith [hy0 n]
        nlinarith
      linarith
    exact h.trans (by linarith)
  have hsmall : (W : ℝ)⁻¹ * C' * B ≤ 1 := by
    rw [mul_assoc, inv_mul_le_iff₀ hW0]; linarith
  set n := travelLength W t₁ R s
  have hn0 : travelLength W t₁ R (s₁ / 2) ≤ n := ce_travelLength_mono W t₁ R (by linarith [hs.1])
  have hn2 : n ≤ travelLength W t₁ R s₂ := ce_travelLength_mono W t₁ R hs.2
  have hbound := rhn_logistic_bound hC'0 hc (inv_pos.mpr hW0) hr hsmall y hy0
    (travelLength W t₁ R (s₁ / 2)) (travelLength W t₁ R s₂) hrec' n hn0 hn2 (s₁ / 4)
    (by linarith) (ce_travel_gap hTR hs₁ hs.1 hWs)
  calc ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b E W n q ω)) ^ r ∂growthPathLaw W b
      ≤ rhn_weightedHigherMoment K b E p r W n q :=
        rhn_lintegral_rpow_le_weighted hK b E p (by linarith) W n q
    _ = ENNReal.ofReal (y n) := (ENNReal.ofReal_toReal (hfin n hn0 hn2)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

end BlockBand.Endpoints
