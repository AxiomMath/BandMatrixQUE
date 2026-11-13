module

public import BlockBand.Critical.Herglotz.MarkTruncation
public import BlockBand.Critical.Herglotz.SecondMoment

/-!
# Moments of product tests `w(x) q(g)` of the decorated sine process

The canonical Cauchy series and its smooth cutoffs are, entrywise and for quadratic forms
`v^* 𝖢_r v`, linear statistics `X = Σ_j w(x_j) q(g_j)` with a location weight `w ∈ C_c(ℝ)`
(signed, e.g. `χ_L(x) x / (π (x² + Y²))`) and a nonnegative continuous mark weight `q ∈ L²(γ)`
(e.g. `q(g) = |v^* g|²`), unbounded in `g`.

Law: `Ξ` is a decorated sine process on `(Ω, P)` (`IsDecoratedSineProcess`;
`γ = circularVectorLaw (Fin r)`); Lebesgue measure in `x`. Results:

* `productTest_lintegral` — nonnegative `u`: measurability, `E ∫⁻ u q dΞ = (∫ u)(∫ q dγ)` and
  `E (∫⁻ u q dΞ)² ≤ (∫ u²)(∫ q² dγ) + ((∫ u)(∫ q dγ))²`. The second moment uses the `k = 2`
  sine Fredholm term (`lintegral_sq_coordinate_of_decoratedSine`) on mark truncations, the
  projection bound `sinePairForm_self_le` and Fatou in the truncation level.
* `productTest_moments` — the same for the Bochner statistic `X = ∫ u q dΞ`, with almost sure
  integrability against `Ξ(ω)`.
* `signedProductTest_variance` — **variance bound** for signed `w`:
  `E X = (∫ w)(∫ q dγ)` and `E (X - E X)² ≤ 2 (∫ w²)(∫ q² dγ)` (the projection bound
  "`Var Σ f(x_j) ≤ ∫ |f|²`", here with the factor `2` from splitting `w = w⁺ - w⁻`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BlockBand.Critical.Herglotz

open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)

variable {r : ℕ}

/-- A continuous `q` with `q² ∈ L¹(γ)` is integrable for the probability measure `γ`. -/
theorem integrable_of_integrable_sq {q : (Fin r → ℂ) → ℝ} (hq : Continuous q)
    (hq2 : Integrable (fun g => q g ^ 2) (circularVectorLaw (Fin r))) :
    Integrable q (circularVectorLaw (Fin r)) := by
  refine ((integrable_const 1).add hq2).mono' hq.aestronglyMeasurable
    (Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [sq_nonneg (|q g| - 1), sq_abs (q g)]

/-- **Moments of a nonnegative product test** (lintegral form). Law: `Ξ` decorated sine
(`IsDecoratedSineProcess`), `γ = circularVectorLaw (Fin r)`, Lebesgue measure in `x`.
For `u ≥ 0` continuous with compact support on `ℝ` and `q ≥ 0` continuous on `ℂ^r` with
`q² ∈ L¹(γ)`, `Y(ω) = ∫⁻ ofReal (u(x) q(g)) dΞ(ω)` is measurable,
`E Y = ofReal ((∫ u)(∫ q dγ))` and `E Y² ≤ ofReal ((∫ u²)(∫ q² dγ) + ((∫ u)(∫ q dγ))²)`. -/
theorem productTest_lintegral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ)
    {u : ℝ → ℝ} (hu : Continuous u) (huc : HasCompactSupport u) (hu0 : ∀ x, 0 ≤ u x)
    {q : (Fin r → ℂ) → ℝ} (hq : Continuous q) (hq0 : ∀ g, 0 ≤ q g)
    (hq2 : Integrable (fun g => q g ^ 2) (circularVectorLaw (Fin r))) :
    Measurable (fun ω => ∫⁻ p, ENNReal.ofReal (u p.1 * q p.2) ∂(Ξ ω).measure) ∧
      ∫⁻ ω, ∫⁻ p, ENNReal.ofReal (u p.1 * q p.2) ∂(Ξ ω).measure ∂P =
        ENNReal.ofReal ((∫ x, u x) * ∫ g, q g ∂circularVectorLaw (Fin r)) ∧
      ∫⁻ ω, (∫⁻ p, ENNReal.ofReal (u p.1 * q p.2) ∂(Ξ ω).measure) ^ 2 ∂P ≤
        ENNReal.ofReal ((∫ x, u x ^ 2) * (∫ g, q g ^ 2 ∂circularVectorLaw (Fin r)) +
          ((∫ x, u x) * ∫ g, q g ∂circularVectorLaw (Fin r)) ^ 2) := by
  set γ := circularVectorLaw (Fin r) with hγ
  have hf : Continuous fun p : ℝ × (Fin r → ℂ) => u p.1 * q p.2 :=
    (hu.comp continuous_fst).mul (hq.comp continuous_snd)
  have hf0 (p : ℝ × (Fin r → ℂ)) : 0 ≤ u p.1 * q p.2 := mul_nonneg (hu0 _) (hq0 _)
  have hS : IsCompact (tsupport u) := huc
  have hfS (x : ℝ) (g : Fin r → ℂ) (hx : x ∉ tsupport u) : u (x, g).1 * q (x, g).2 = 0 := by
    simp [image_eq_zero_of_notMem_tsupport hx]
  obtain ⟨hmeas, hE⟩ := lintegral_lintegral_ofReal_of_decoratedSine h hf hf0 hS hfS
  have hui : Integrable u := hu.integrable_of_hasCompactSupport huc
  have hqi : Integrable q γ := integrable_of_integrable_sq hq hq2
  refine ⟨hmeas, ?_, ?_⟩
  · rw [hE]
    calc ∫⁻ x, ∫⁻ g, ENNReal.ofReal (u (x, g).1 * q (x, g).2) ∂γ
        = ∫⁻ x, ENNReal.ofReal (u x) * ∫⁻ g, ENNReal.ofReal (q g) ∂γ := by
          refine lintegral_congr fun x => ?_
          simp_rw [ENNReal.ofReal_mul (hu0 x)]
          exact lintegral_const_mul _ (ENNReal.measurable_ofReal.comp hq.measurable)
      _ = (∫⁻ x, ENNReal.ofReal (u x)) * ∫⁻ g, ENNReal.ofReal (q g) ∂γ :=
          lintegral_mul_const _ (ENNReal.measurable_ofReal.comp hu.measurable)
      _ = ENNReal.ofReal ((∫ x, u x) * ∫ g, q g ∂γ) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hui (Eventually.of_forall hu0),
            ← ofReal_integral_eq_lintegral_ofReal hqi (Eventually.of_forall hq0),
            ENNReal.ofReal_mul (integral_nonneg hu0)]
  -- second moment: Fatou in the truncation level
  set fM := markTruncation (fun p : ℝ × (Fin r → ℂ) => u p.1 * q p.2) hf hS hfS with hfM
  have hrep (ω : Ω) := lintegral_ofReal_eq_iSup_markTruncation hf hf0 hS hfS (Ξ ω)
  have hYm (M : ℕ) : Measurable fun ω => ENNReal.ofReal (∫ p, fM M p ∂(Ξ ω).measure) :=
    ENNReal.measurable_ofReal.comp
      ((BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate
        (fM M)).measurable.comp h.measurable)
  have htend (ω : Ω) : Tendsto (fun M => ENNReal.ofReal (∫ p, fM M p ∂(Ξ ω).measure) ^ 2)
      atTop (𝓝 ((∫⁻ p, ENNReal.ofReal (u p.1 * q p.2) ∂(Ξ ω).measure) ^ 2)) := by
    rw [(hrep ω).1]
    exact ENNReal.Tendsto.pow (tendsto_atTop_iSup (hrep ω).2)
  have hbound (M : ℕ) : ∫⁻ ω, ENNReal.ofReal (∫ p, fM M p ∂(Ξ ω).measure) ^ 2 ∂P ≤
      ENNReal.ofReal ((∫ x, u x ^ 2) * (∫ g, q g ^ 2 ∂γ) + ((∫ x, u x) * ∫ g, q g ∂γ) ^ 2) := by
    have hfM0 (p : ℝ × (Fin r → ℂ)) : 0 ≤ fM M p := mul_nonneg (hf0 p) (markCutoff_nonneg M p.2)
    have hsq (ω : Ω) : ENNReal.ofReal (∫ p, fM M p ∂(Ξ ω).measure) ^ 2 =
        ENNReal.ofReal ((∫ p, fM M p ∂(Ξ ω).measure) ^ 2) :=
      (ENNReal.ofReal_pow (integral_nonneg hfM0) 2).symm
    simp_rw [hsq]
    rw [lintegral_sq_coordinate_of_decoratedSine h (fM M) hfM0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hqψ : Integrable (fun g => q g * markCutoff M g) γ :=
      hqi.mono' (hq.mul (continuous_markCutoff M)).aestronglyMeasurable
        (Eventually.of_forall fun g => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 g) (markCutoff_nonneg M g))]
          exact mul_le_of_le_one_right (hq0 g) (markCutoff_le_one M g))
    have hqψ2 : Integrable (fun g => (q g * markCutoff M g) ^ 2) γ :=
      hq2.mono' ((hq.mul (continuous_markCutoff M)).pow 2).aestronglyMeasurable
        (Eventually.of_forall fun g => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (mul_nonneg (hq0 g) (markCutoff_nonneg M g))
            (mul_le_of_le_one_right (hq0 g) (markCutoff_le_one M g)) 2)
    set c1 := ∫ g, q g * markCutoff M g ∂γ with hc1
    set c2 := ∫ g, (q g * markCutoff M g) ^ 2 ∂γ with hc2
    have hc1le : c1 ≤ ∫ g, q g ∂γ := integral_mono hqψ hqi fun g =>
      mul_le_of_le_one_right (hq0 g) (markCutoff_le_one M g)
    have hc10 : 0 ≤ c1 := integral_nonneg fun g => mul_nonneg (hq0 g) (markCutoff_nonneg M g)
    have hc2le : c2 ≤ ∫ g, q g ^ 2 ∂γ := integral_mono hqψ2 hq2 fun g =>
      pow_le_pow_left₀ (mul_nonneg (hq0 g) (markCutoff_nonneg M g))
        (mul_le_of_le_one_right (hq0 g) (markCutoff_le_one M g)) 2
    have ha_eq : (fun x => ∫ g, fM M (x, g) ∂γ) = fun x => u x * c1 := by
      funext x
      simp only [hfM, markTruncation_apply]
      rw [hc1, ← integral_const_mul]
      congr 1
      funext g
      ring
    have hb_eq : ∫ x, ∫ g, fM M (x, g) ^ 2 ∂γ = (∫ x, u x ^ 2) * c2 := by
      have hin (x : ℝ) : ∫ g, fM M (x, g) ^ 2 ∂γ = u x ^ 2 * c2 := by
        simp only [hfM, markTruncation_apply]
        rw [hc2, ← integral_const_mul]
        congr 1
        funext g
        ring
      simp_rw [hin]
      exact integral_mul_const c2 _
    rw [ha_eq, hb_eq]
    have hsp := sinePairForm_self_le (hui.mul_const c1)
    rw [integral_mul_const] at hsp
    have hu20 : 0 ≤ ∫ x, u x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hu10 : 0 ≤ ∫ x, u x := integral_nonneg hu0
    have h1 : (∫ x, u x ^ 2) * c2 ≤ (∫ x, u x ^ 2) * ∫ g, q g ^ 2 ∂γ :=
      mul_le_mul_of_nonneg_left hc2le hu20
    have h2 : ((∫ x, u x) * c1) ^ 2 ≤ ((∫ x, u x) * ∫ g, q g ∂γ) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hu10 hc10) (mul_le_mul_of_nonneg_left hc1le hu10) 2
    linarith
  calc ∫⁻ ω, (∫⁻ p, ENNReal.ofReal (u p.1 * q p.2) ∂(Ξ ω).measure) ^ 2 ∂P
      = ∫⁻ ω, liminf (fun M => ENNReal.ofReal (∫ p, fM M p ∂(Ξ ω).measure) ^ 2) atTop ∂P :=
        lintegral_congr fun ω => (htend ω).liminf_eq.symm
    _ ≤ liminf (fun M => ∫⁻ ω, ENNReal.ofReal (∫ p, fM M p ∂(Ξ ω).measure) ^ 2 ∂P) atTop :=
        lintegral_liminf_le fun M => (hYm M).pow_const 2
    _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall hbound)

/-- **Moments of a nonnegative product test** (Bochner form). Same law and hypotheses as
`productTest_lintegral`. For `X(ω) = ∫ u(x) q(g) dΞ(ω)`: almost surely `u q` is
`Ξ(ω)`-integrable; `X` is measurable and integrable with `E X = (∫ u)(∫ q dγ)`; `X²` is
integrable with `E X² ≤ (∫ u²)(∫ q² dγ) + ((∫ u)(∫ q dγ))²`. -/
theorem productTest_moments {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ)
    {u : ℝ → ℝ} (hu : Continuous u) (huc : HasCompactSupport u) (hu0 : ∀ x, 0 ≤ u x)
    {q : (Fin r → ℂ) → ℝ} (hq : Continuous q) (hq0 : ∀ g, 0 ≤ q g)
    (hq2 : Integrable (fun g => q g ^ 2) (circularVectorLaw (Fin r))) :
    (∀ᵐ ω ∂P, Integrable (fun p : ℝ × (Fin r → ℂ) => u p.1 * q p.2) (Ξ ω).measure) ∧
      Measurable (fun ω => ∫ p, u p.1 * q p.2 ∂(Ξ ω).measure) ∧
      Integrable (fun ω => ∫ p, u p.1 * q p.2 ∂(Ξ ω).measure) P ∧
      ∫ ω, (∫ p, u p.1 * q p.2 ∂(Ξ ω).measure) ∂P =
        (∫ x, u x) * ∫ g, q g ∂circularVectorLaw (Fin r) ∧
      Integrable (fun ω => (∫ p, u p.1 * q p.2 ∂(Ξ ω).measure) ^ 2) P ∧
      ∫ ω, (∫ p, u p.1 * q p.2 ∂(Ξ ω).measure) ^ 2 ∂P ≤
        (∫ x, u x ^ 2) * (∫ g, q g ^ 2 ∂circularVectorLaw (Fin r)) +
          ((∫ x, u x) * ∫ g, q g ∂circularVectorLaw (Fin r)) ^ 2 := by
  obtain ⟨hYm, hE1, hE2⟩ := productTest_lintegral h hu huc hu0 hq hq0 hq2
  set Y := fun ω => ∫⁻ p, ENNReal.ofReal (u p.1 * q p.2) ∂(Ξ ω).measure with hY
  have hf : Continuous fun p : ℝ × (Fin r → ℂ) => u p.1 * q p.2 :=
    (hu.comp continuous_fst).mul (hq.comp continuous_snd)
  have hf0 (p : ℝ × (Fin r → ℂ)) : 0 ≤ u p.1 * q p.2 := mul_nonneg (hu0 _) (hq0 _)
  have hX (ω : Ω) : ∫ p, u p.1 * q p.2 ∂(Ξ ω).measure = (Y ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hf.aestronglyMeasurable
  have hb1 : 0 ≤ (∫ x, u x) * ∫ g, q g ∂circularVectorLaw (Fin r) :=
    mul_nonneg (integral_nonneg hu0) (integral_nonneg hq0)
  have hb2 : 0 ≤ (∫ x, u x ^ 2) * (∫ g, q g ^ 2 ∂circularVectorLaw (Fin r)) +
      ((∫ x, u x) * ∫ g, q g ∂circularVectorLaw (Fin r)) ^ 2 :=
    add_nonneg (mul_nonneg (integral_nonneg fun x => sq_nonneg _)
      (integral_nonneg fun g => sq_nonneg _)) (sq_nonneg _)
  have hfin1 : ∫⁻ ω, Y ω ∂P ≠ ∞ := by rw [hE1]; exact ENNReal.ofReal_ne_top
  have hfin2 : ∫⁻ ω, Y ω ^ 2 ∂P ≠ ∞ := (hE2.trans_lt ENNReal.ofReal_lt_top).ne
  have hlt := ae_lt_top hYm hfin1
  simp_rw [hX]
  refine ⟨?_, hYm.ennreal_toReal, integrable_toReal_of_lintegral_ne_top hYm.aemeasurable hfin1,
    ?_, ?_, ?_⟩
  · filter_upwards [hlt] with ω hω
    exact (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
      (Eventually.of_forall hf0)).1 hω.ne
  · rw [integral_toReal hYm.aemeasurable hlt, hE1, ENNReal.toReal_ofReal hb1]
  · simp_rw [← ENNReal.toReal_pow]
    exact integrable_toReal_of_lintegral_ne_top (hYm.pow_const 2).aemeasurable hfin2
  · simp_rw [← ENNReal.toReal_pow]
    rw [integral_toReal (hYm.pow_const 2).aemeasurable (ae_lt_top (hYm.pow_const 2) hfin2)]
    exact ENNReal.toReal_le_of_le_ofReal hb2 hE2

/-- Second central moment of a nonnegative product test:
`E (X - (∫ u)(∫ q))² ≤ (∫ u²)(∫ q² dγ)`, with integrability (same hypotheses as
`productTest_moments`). -/
theorem productTest_central {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ)
    {u : ℝ → ℝ} (hu : Continuous u) (huc : HasCompactSupport u) (hu0 : ∀ x, 0 ≤ u x)
    {q : (Fin r → ℂ) → ℝ} (hq : Continuous q) (hq0 : ∀ g, 0 ≤ q g)
    (hq2 : Integrable (fun g => q g ^ 2) (circularVectorLaw (Fin r))) :
    Integrable (fun ω => (∫ p, u p.1 * q p.2 ∂(Ξ ω).measure -
      (∫ x, u x) * ∫ g, q g ∂circularVectorLaw (Fin r)) ^ 2) P ∧
    ∫ ω, (∫ p, u p.1 * q p.2 ∂(Ξ ω).measure -
      (∫ x, u x) * ∫ g, q g ∂circularVectorLaw (Fin r)) ^ 2 ∂P ≤
        (∫ x, u x ^ 2) * ∫ g, q g ^ 2 ∂circularVectorLaw (Fin r) := by
  have := h.prob
  obtain ⟨-, -, hi, hE, hi2, hE2⟩ := productTest_moments h hu huc hu0 hq hq0 hq2
  set X := fun ω => ∫ p, u p.1 * q p.2 ∂(Ξ ω).measure with hX
  set m := (∫ x, u x) * ∫ g, q g ∂circularVectorLaw (Fin r) with hm
  have heq : (fun ω => (X ω - m) ^ 2) = fun ω => X ω ^ 2 - 2 * m * X ω + m ^ 2 := by
    funext ω; ring
  have hint : Integrable (fun ω => X ω ^ 2 - 2 * m * X ω + m ^ 2) P :=
    (hi2.sub (hi.const_mul (2 * m))).add (integrable_const _)
  refine ⟨heq ▸ hint, ?_⟩
  have h1 : ∫ ω, (X ω ^ 2 - 2 * m * X ω + m ^ 2) ∂P =
      (∫ ω, X ω ^ 2 ∂P) - 2 * m * (∫ ω, X ω ∂P) + m ^ 2 := by
    rw [integral_add (f := fun ω => X ω ^ 2 - 2 * m * X ω) (g := fun _ => m ^ 2)
      (hi2.sub (hi.const_mul (2 * m))) (integrable_const _),
      integral_sub (f := fun ω => X ω ^ 2) (g := fun ω => 2 * m * X ω) hi2 (hi.const_mul _),
      integral_const_mul, integral_const]
    simp
  rw [heq, h1, hE]
  linarith [hE2]

/-- **Variance bound for a signed product test** ("`Var Σ f(x_j) ≤ ∫ |f|²`" up to the factor
`2`). Law: `Ξ` decorated sine (`IsDecoratedSineProcess`), `γ = circularVectorLaw (Fin r)`,
Lebesgue measure in `x`. For `w` continuous with compact support on `ℝ` (any sign) and `q ≥ 0`
continuous with `q² ∈ L¹(γ)`, with `X(ω) = ∫ w(x) q(g) dΞ(ω)`: almost surely `w q` is
`Ξ(ω)`-integrable, `X` is integrable, `E X = (∫ w)(∫ q dγ)`, and
`E (X - (∫ w)(∫ q dγ))² ≤ 2 (∫ w²)(∫ q² dγ)`. -/
theorem signedProductTest_variance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    {q : (Fin r → ℂ) → ℝ} (hq : Continuous q) (hq0 : ∀ g, 0 ≤ q g)
    (hq2 : Integrable (fun g => q g ^ 2) (circularVectorLaw (Fin r))) :
    (∀ᵐ ω ∂P, Integrable (fun p : ℝ × (Fin r → ℂ) => w p.1 * q p.2) (Ξ ω).measure) ∧
      Integrable (fun ω => ∫ p, w p.1 * q p.2 ∂(Ξ ω).measure) P ∧
      ∫ ω, (∫ p, w p.1 * q p.2 ∂(Ξ ω).measure) ∂P =
        (∫ x, w x) * ∫ g, q g ∂circularVectorLaw (Fin r) ∧
      Integrable (fun ω => (∫ p, w p.1 * q p.2 ∂(Ξ ω).measure -
        (∫ x, w x) * ∫ g, q g ∂circularVectorLaw (Fin r)) ^ 2) P ∧
      ∫ ω, (∫ p, w p.1 * q p.2 ∂(Ξ ω).measure -
        (∫ x, w x) * ∫ g, q g ∂circularVectorLaw (Fin r)) ^ 2 ∂P ≤
          2 * ((∫ x, w x ^ 2) * ∫ g, q g ^ 2 ∂circularVectorLaw (Fin r)) := by
  have := h.prob
  set γ := circularVectorLaw (Fin r) with hγ
  set u₁ : ℝ → ℝ := fun x => max (w x) 0 with hu₁
  set u₂ : ℝ → ℝ := fun x => max (-w x) 0 with hu₂
  have hS : IsCompact (tsupport w) := hwc
  have hc₁ : HasCompactSupport u₁ :=
    HasCompactSupport.intro hS fun x hx => by simp [hu₁, image_eq_zero_of_notMem_tsupport hx]
  have hc₂ : HasCompactSupport u₂ :=
    HasCompactSupport.intro hS fun x hx => by simp [hu₂, image_eq_zero_of_notMem_tsupport hx]
  have hcu₁ : Continuous u₁ := hw.max continuous_const
  have hcu₂ : Continuous u₂ := hw.neg.max continuous_const
  obtain ⟨ae₁, -, i₁, E₁, -, -⟩ :=
    productTest_moments h hcu₁ hc₁ (fun x => le_max_right _ _) hq hq0 hq2
  obtain ⟨ae₂, -, i₂, E₂, -, -⟩ :=
    productTest_moments h hcu₂ hc₂ (fun x => le_max_right _ _) hq hq0 hq2
  obtain ⟨iv₁, V₁⟩ := productTest_central h hcu₁ hc₁ (fun x => le_max_right _ _) hq hq0 hq2
  obtain ⟨iv₂, V₂⟩ := productTest_central h hcu₂ hc₂ (fun x => le_max_right _ _) hq hq0 hq2
  have hdec (x : ℝ) : w x = u₁ x - u₂ x := (max_zero_sub_eq_self (w x)).symm
  have hu₁i : Integrable u₁ := hcu₁.integrable_of_hasCompactSupport hc₁
  have hu₂i : Integrable u₂ := hcu₂.integrable_of_hasCompactSupport hc₂
  have hsq₁ : Integrable (fun x => u₁ x ^ 2) := (hcu₁.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hS fun x hx => by simp [hu₁, image_eq_zero_of_notMem_tsupport hx])
  have hsq₂ : Integrable (fun x => u₂ x ^ 2) := (hcu₂.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hS fun x hx => by simp [hu₂, image_eq_zero_of_notMem_tsupport hx])
  have hwint : ∫ x, w x = (∫ x, u₁ x) - ∫ x, u₂ x := by
    rw [← integral_sub hu₁i hu₂i]
    exact integral_congr_ae (Eventually.of_forall hdec)
  have hw2 : ∫ x, w x ^ 2 = (∫ x, u₁ x ^ 2) + ∫ x, u₂ x ^ 2 := by
    rw [← integral_add hsq₁ hsq₂]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hu₁, hu₂]
    rcases le_total 0 (w x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hx, max_eq_left (by linarith)]; ring
  set X₁ := fun ω => ∫ p, u₁ p.1 * q p.2 ∂(Ξ ω).measure with hX₁
  set X₂ := fun ω => ∫ p, u₂ p.1 * q p.2 ∂(Ξ ω).measure with hX₂
  set c := ∫ g, q g ∂γ with hc
  have hpt (p : ℝ × (Fin r → ℂ)) : w p.1 * q p.2 = u₁ p.1 * q p.2 - u₂ p.1 * q p.2 := by
    rw [hdec]; ring
  have hae : ∀ᵐ ω ∂P, Integrable (fun p : ℝ × (Fin r → ℂ) => w p.1 * q p.2) (Ξ ω).measure ∧
      ∫ p, w p.1 * q p.2 ∂(Ξ ω).measure = X₁ ω - X₂ ω := by
    filter_upwards [ae₁, ae₂] with ω h₁ h₂
    have hfun : (fun p : ℝ × (Fin r → ℂ) => w p.1 * q p.2) =
        fun p => u₁ p.1 * q p.2 - u₂ p.1 * q p.2 := funext hpt
    rw [hfun]
    exact ⟨h₁.sub h₂, integral_sub h₁ h₂⟩
  have hXeq : (fun ω => ∫ p, w p.1 * q p.2 ∂(Ξ ω).measure) =ᵐ[P] fun ω => X₁ ω - X₂ ω :=
    hae.mono fun ω hω => hω.2
  have hiX : Integrable (fun ω => ∫ p, w p.1 * q p.2 ∂(Ξ ω).measure) P :=
    (i₁.sub i₂).congr hXeq.symm
  have hm : (∫ x, w x) * c = (∫ x, u₁ x) * c - (∫ x, u₂ x) * c := by rw [hwint]; ring
  have hEX : ∫ ω, (∫ p, w p.1 * q p.2 ∂(Ξ ω).measure) ∂P = (∫ x, w x) * c := by
    rw [integral_congr_ae hXeq, integral_sub i₁ i₂, E₁, E₂, hm]
  set D : Ω → ℝ := fun ω => 2 * (X₁ ω - (∫ x, u₁ x) * c) ^ 2 +
    2 * (X₂ ω - (∫ x, u₂ x) * c) ^ 2 with hD
  have hDi : Integrable D P := (iv₁.const_mul 2).add (iv₂.const_mul 2)
  have hbd : ∀ᵐ ω ∂P, ‖(∫ p, w p.1 * q p.2 ∂(Ξ ω).measure - (∫ x, w x) * c) ^ 2‖ ≤ D ω := by
    filter_upwards [hXeq] with ω hω
    rw [hω, hm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [hD]
    nlinarith [sq_nonneg (X₁ ω - (∫ x, u₁ x) * c + (X₂ ω - (∫ x, u₂ x) * c))]
  have hiV : Integrable (fun ω => (∫ p, w p.1 * q p.2 ∂(Ξ ω).measure - (∫ x, w x) * c) ^ 2)
      P :=
    hDi.mono' ((hiX.aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2) hbd
  refine ⟨hae.mono fun ω hω => hω.1, hiX, hEX, hiV, ?_⟩
  calc ∫ ω, (∫ p, w p.1 * q p.2 ∂(Ξ ω).measure - (∫ x, w x) * c) ^ 2 ∂P
      ≤ ∫ ω, D ω ∂P := integral_mono_ae hiV hDi (hbd.mono fun ω hω =>
        (le_abs_self _).trans (by rwa [← Real.norm_eq_abs]))
    _ = 2 * ∫ ω, (X₁ ω - (∫ x, u₁ x) * c) ^ 2 ∂P +
          2 * ∫ ω, (X₂ ω - (∫ x, u₂ x) * c) ^ 2 ∂P := by
        rw [integral_add (iv₁.const_mul 2) (iv₂.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ 2 * ((∫ x, u₁ x ^ 2) * ∫ g, q g ^ 2 ∂γ) + 2 * ((∫ x, u₂ x ^ 2) * ∫ g, q g ^ 2 ∂γ) := by
        linarith
    _ = 2 * ((∫ x, w x ^ 2) * ∫ g, q g ^ 2 ∂γ) := by rw [hw2]; ring

end BlockBand.Critical.Herglotz
