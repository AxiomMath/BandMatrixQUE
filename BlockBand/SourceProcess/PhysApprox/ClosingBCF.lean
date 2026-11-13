module

public import BlockBand.SourceProcess.PhysApprox.Assembly
public import BlockBand.SourceProcess.ComplexConstruct.Tight
public import BlockBand.SourceProcess.RawTag.Holds
public import BlockBand.SourceProcess.PhysApprox.Meas

/-!
# Entrywise closing errors give the closing error of bounded tests

This file proves `TargetT1`. Measure `μ_W = probedPathLaw W np b ⊗ phaseLaw` (probability).
`X = complexSourceData` at `⌊WT⌋` (a function of the probed path) and `Y = closedSourceData`
(path, probes, phase).

* `abs_integral_comp_sub_le` (generic): `|E Φ(X) - E Φ(Y)| ≤ ε' + 2‖Φ‖ μ(B)` if
  `|Φ(X) - Φ(Y)| ≤ ε'` off the measurable set `B`.
* `complexClosingError_of_meas`: given the measurability of the closed source data
  (`ClosedDataMeasurable`, discharged by `measurable_closedSourceData`), `RawTagMoments`,
  `KClosingFractional` and `GramClosingSmall` give `ComplexClosingError`. The proof: tightness of
  the laws (`complexSourceTight_of_raw`) gives a compact `K` with `μ_W(X ∉ K)` small for
  all `W`; `Φ` is uniformly continuous on the compact `cthickening 1 K`, with modulus `δ ≤ 1`;
  off `B = {X ∉ K} ∪ ⋃_{r,i,k} {‖Y_{rik} - X_{rik}‖ ≥ δ}` the sup distance is `< δ`; Markov's
  inequality bounds each entry event by `KClosingFractional` (`p = 1/2`, `r = 0`) or
  `GramClosingSmall` (`r ≠ 0`), eventually in `h` and then in `W`, finitely many at once.
* `complexClosingError_of_meas_contracts`: the same with `RawTagMoments` from the contract
  hypotheses (`rawTagMoments_holds`); `t1 : TargetT1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory Filter Topology Metric
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing
open scoped ENNReal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The measurability of the closed source data (`measurable_closedSourceData`). -/
def ClosedDataMeasurable : Prop :=
  ∀ (b E s T h : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (W : ℕ),
    Measurable fun y : ProbedPath W np × ℝ => closedSourceData b E s T h τ m W (phase y.2) y.1

section Generic

variable {α E : Type*} [MeasurableSpace α] [TopologicalSpace E] [MeasurableSpace E]
  [OpensMeasurableSpace E]

/-- `|E Φ(X) - E Φ(Y)| ≤ ε' + 2‖Φ‖ μ(B)` if `|Φ(X) - Φ(Y)| ≤ ε'` off `B`. -/
theorem abs_integral_comp_sub_le (μ : Measure α) [IsProbabilityMeasure μ]
    (Φ : BoundedContinuousFunction E ℝ) {X Y : α → E} (hX : Measurable X) (hY : Measurable Y)
    {B : Set α} (hB : MeasurableSet B) {ε : ℝ} (hε : 0 ≤ ε)
    (hgood : ∀ a, a ∉ B → |Φ (X a) - Φ (Y a)| ≤ ε) :
    |∫ a, Φ (X a) ∂μ - ∫ a, Φ (Y a) ∂μ| ≤ ε + 2 * ‖Φ‖ * μ.real B := by
  have hiX : Integrable (fun a => Φ (X a)) μ :=
    (integrable_const ‖Φ‖).mono' (Φ.continuous.measurable.comp hX).aestronglyMeasurable
      (ae_of_all _ fun a => Φ.norm_coe_le_norm _)
  have hiY : Integrable (fun a => Φ (Y a)) μ :=
    (integrable_const ‖Φ‖).mono' (Φ.continuous.measurable.comp hY).aestronglyMeasurable
      (ae_of_all _ fun a => Φ.norm_coe_le_norm _)
  have hind : Integrable (B.indicator fun _ => (1 : ℝ)) μ := (integrable_const (1 : ℝ)).indicator hB
  have hpt : ∀ a, |Φ (X a) - Φ (Y a)| ≤ ε + 2 * ‖Φ‖ * B.indicator (fun _ => (1 : ℝ)) a := by
    intro a
    by_cases ha : a ∈ B
    · have h1 := Φ.dist_le_two_norm (X a) (Y a)
      rw [Real.dist_eq] at h1
      simp only [Set.indicator_of_mem ha, mul_one]
      linarith
    · simp only [Set.indicator_of_notMem ha, mul_zero, add_zero]
      exact hgood a ha
  have hiB : Integrable (fun a => ε + 2 * ‖Φ‖ * B.indicator (fun _ => (1 : ℝ)) a) μ :=
    (integrable_const ε).add (hind.const_mul _)
  calc |∫ a, Φ (X a) ∂μ - ∫ a, Φ (Y a) ∂μ| = |∫ a, (Φ (X a) - Φ (Y a)) ∂μ| := by
        rw [integral_sub hiX hiY]
    _ ≤ ∫ a, |Φ (X a) - Φ (Y a)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ a, (ε + 2 * ‖Φ‖ * B.indicator (fun _ => (1 : ℝ)) a) ∂μ :=
        integral_mono (hiX.sub hiY).abs hiB hpt
    _ = ε + 2 * ‖Φ‖ * μ.real B := by
        rw [integral_add (integrable_const ε) (hind.const_mul _), integral_const_mul,
          integral_indicator_const _ hB]
        simp

end Generic

/-- Markov's inequality for a lower-integral bound: `μ{δ ≤ f} ≤ ε` from
`∫⁻ ofReal(f^p) ≤ ofReal(ε δ^p)`. -/
theorem measure_le_of_lintegral_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Measurable f) {p δ ε : ℝ} (hp : 0 < p) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (h : ∫⁻ a, ENNReal.ofReal (f a ^ p) ∂μ ≤ ENNReal.ofReal (ε * δ ^ p)) :
    μ {a | δ ≤ f a} ≤ ENNReal.ofReal ε := by
  have hδp : 0 < δ ^ p := Real.rpow_pos_of_pos hδ p
  have hsub : {a | δ ≤ f a} ⊆ {a | ENNReal.ofReal (δ ^ p) ≤ ENNReal.ofReal (f a ^ p)} :=
    fun a ha => ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hδ.le ha hp.le)
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div
    (ENNReal.measurable_ofReal.comp (hf.pow_const p)).aemeasurable
    (by simpa using hδp) ENNReal.ofReal_ne_top).trans ?_
  refine (ENNReal.div_le_div_right h _).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hε, ENNReal.mul_div_cancel_right (by simpa using hδp)
    ENNReal.ofReal_ne_top]

/-- **The closing error, conditional on the measurability of the closed data**: `RawTagMoments`,
`KClosingFractional` and `GramClosingSmall` give `ComplexClosingError`. -/
theorem complexClosingError_of_meas (hmeas : ClosedDataMeasurable) (hR : RawTagMoments)
    (h1 : KClosingFractional) (h2 : GramClosingSmall) : ComplexClosingError := by
  intro b E np τ m T hD s hs hτ Φ ε hε
  have hT := complexSourceTight_of_raw hR b E np τ m T hD
  set c : ℝ := 2 * ‖Φ‖ + 1 with hcdef
  have hc : 0 < c := by positivity
  set η : ℝ := ε / (4 * c * (4 * ((np : ℝ) * np) + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hεc : 0 < ε / (4 * c) := by positivity
  obtain ⟨K, hK, hKc⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 hT (ENNReal.ofReal (ε / (4 * c)))
      (by simpa using hεc)
  have : ProperSpace (SourceData np) :=
    inferInstanceAs (ProperSpace (Fin 4 → Fin np → Fin np → ℂ))
  have hK1 : IsCompact (cthickening 1 K) := hK.cthickening
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuousOn_iff.1
    (hK1.uniformContinuousOn_of_continuous Φ.continuous.continuousOn) (ε / 2) (by positivity)
  set δ : ℝ := min δ₀ 1 with hδdef
  have hδpos : 0 < δ := lt_min hδ₀ one_pos
  -- the entry events
  set Xf : ∀ W : ℕ, ProbedPath W np × ℝ → SourceData np :=
    fun W a => complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m a.1 with hXf
  set Yf : ∀ h : ℝ, ∀ W : ℕ, ProbedPath W np × ℝ → SourceData np :=
    fun h W a => closedSourceData b E s T h τ m W (phase a.2) a.1 with hYf
  have hXm : ∀ W, Measurable (Xf W) := fun W =>
    (measurable_complexSourceData b E W _ τ m).comp measurable_fst
  have hYm : ∀ h W, Measurable (Yf h W) := fun h W => hmeas b E s T h τ m W
  have hent : ∀ (h : ℝ) (W : ℕ) (q : Fin 4 × Fin np × Fin np),
      Measurable fun a => ‖Yf h W a q.1 q.2.1 q.2.2 - Xf W a q.1 q.2.1 q.2.2‖ := by
    intro h W q
    exact (((measurable_pi_apply q.1).comp (hYm h W)).eval_matrix.sub
      ((measurable_pi_apply q.1).comp (hXm W)).eval_matrix).norm
  have hA : ∀ q : Fin 4 × Fin np × Fin np, ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ᶠ W in atTop,
      ((probedPathLaw W np b).prod phaseLaw)
        {a | δ ≤ ‖Yf h W a q.1 q.2.1 q.2.2 - Xf W a q.1 q.2.1 q.2.2‖} ≤ ENNReal.ofReal η := by
    rintro ⟨r, i, k⟩
    by_cases hr : r = 0
    · subst hr
      filter_upwards [h1 b E np τ m T hD s hs hτ (1 / 2) (by norm_num) (by norm_num) i k
        (η * δ ^ (1 / 2 : ℝ)) (by positivity)] with h hh
      filter_upwards [hh] with W hW
      exact measure_le_of_lintegral_rpow_le (hent h W (0, i, k)) (by norm_num) hδpos hη.le hW
    · filter_upwards [h2 b E np τ m T hD s hs hτ r hr i k (η * δ) (by positivity)] with h hh
      filter_upwards [hh] with W hW
      refine measure_le_of_lintegral_rpow_le (p := 1) (hent h W (r, i, k)) one_pos hδpos hη.le
        ?_
      simpa only [Real.rpow_one] using hW
  filter_upwards [Filter.eventually_all.2 hA] with h hh
  filter_upwards [Filter.eventually_all.2 hh] with W hW
  set μ := (probedPathLaw W np b).prod phaseLaw with hμ
  set B : Set (ProbedPath W np × ℝ) := {a | Xf W a ∉ K} ∪
    ⋃ q : Fin 4 × Fin np × Fin np, {a | δ ≤ ‖Yf h W a q.1 q.2.1 q.2.2 - Xf W a q.1 q.2.1 q.2.2‖}
    with hBdef
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hBm : MeasurableSet B :=
    ((hXm W) hKm.compl).union (MeasurableSet.iUnion fun q =>
      measurableSet_le measurable_const (hent h W q))
  have hgood : ∀ a, a ∉ B → |Φ (Xf W a) - Φ (Yf h W a)| ≤ ε / 2 := by
    intro a ha
    simp only [hBdef, Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists,
      not_le] at ha
    obtain ⟨hXK, hlt⟩ := ha
    have hXK' : Xf W a ∈ K := not_not.1 hXK
    have hdist : dist (Xf W a) (Yf h W a) < δ := by
      rw [dist_eq_norm, pi_norm_lt_iff hδpos]
      intro r
      rw [Matrix.norm_lt_iff hδpos]
      intro i k
      have := hlt (r, i, k)
      rw [norm_sub_rev] at this
      simpa using this
    have hd := hδ (Xf W a) (self_subset_cthickening K hXK') (Yf h W a)
      (mem_cthickening_of_dist_le _ _ 1 K hXK'
        ((dist_comm _ _).le.trans (hdist.le.trans (min_le_right _ _))))
      (hdist.trans_le (min_le_left _ _))
    rw [Real.dist_eq] at hd
    exact hd.le
  have hμB : μ B ≤ ENNReal.ofReal (ε / (4 * c)) +
      ∑ _q : Fin 4 × Fin np × Fin np, ENNReal.ofReal η := by
    refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
    · have e : {a : ProbedPath W np × ℝ | Xf W a ∉ K} =
          ((complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m) ⁻¹' Kᶜ) ×ˢ Set.univ := by
        ext a
        simp [hXf]
      rw [hμ, e, Measure.prod_prod, measure_univ, mul_one,
        ← Measure.map_apply (measurable_complexSourceData b E W _ τ m) hKm.compl]
      exact hKc _ ⟨W, rfl⟩
    · exact (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun q _ => hW q)
  have hμBr : μ.real B ≤ ε / (2 * c) := by
    have hcard : (∑ _q : Fin 4 × Fin np × Fin np, ENNReal.ofReal η) =
        ENNReal.ofReal (4 * ((np : ℝ) * np) * η) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity)]
      push_cast
      ring_nf
    have hle : 4 * ((np : ℝ) * np) * η ≤ ε / (4 * c) := by
      have hd : 4 * ((np : ℝ) * np) + 1 ≠ 0 := by positivity
      have h1 : (4 * ((np : ℝ) * np) + 1) * η = ε / (4 * c) := by
        rw [hηdef, mul_div_assoc', mul_comm (4 * ((np : ℝ) * np) + 1) ε,
          mul_div_mul_right _ _ hd]
      linarith
    rw [hcard, ← ENNReal.ofReal_add hεc.le (by positivity)] at hμB
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (hμB.trans
      (ENNReal.ofReal_le_ofReal ?_))
    have : ε / (4 * c) + ε / (4 * c) = ε / (2 * c) := by field_simp; ring
    linarith
  have hphys : physExpectation b E T τ m Φ W = ∫ a, Φ (Xf W a) ∂μ := by
    have h0 := integral_fun_fst (μ := probedPathLaw W np b) (ν := phaseLaw)
      (fun x => Φ (complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m x))
    rw [probReal_univ, one_smul] at h0
    show physExpectation b E T τ m Φ W = ∫ a, Φ (complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m a.1)
      ∂((probedPathLaw W np b).prod phaseLaw)
    rw [h0]
    rfl
  have hmain := abs_integral_comp_sub_le μ Φ (hXm W) (hYm h W) hBm (by positivity) hgood
  rw [hphys]
  refine hmain.trans ?_
  have hΦ : 0 ≤ ‖Φ‖ := norm_nonneg _
  have h3 : 2 * ‖Φ‖ * μ.real B ≤ 2 * ‖Φ‖ * (ε / (2 * c)) :=
    mul_le_mul_of_nonneg_left hμBr (by positivity)
  have h4 : 2 * ‖Φ‖ * (ε / (2 * c)) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **The closing error with the contract hypotheses**, conditional on the measurability of the
closed data. -/
theorem complexClosingError_of_meas_contracts (hmeas : ClosedDataMeasurable)
    (hMT : Layers.MatchedTracesContract) (hGA : Layers.GaussianAbsorptionContract)
    (hSR : Layers.ScalarRecursionContract) (hLp : Inputs.GaussianLpGradient)
    (h1 : KClosingFractional) (h2 : GramClosingSmall) : ComplexClosingError :=
  complexClosingError_of_meas hmeas (RawTag.rawTagMoments_holds hGA hLp hSR hMT) h1 h2

theorem closedDataMeasurable : ClosedDataMeasurable :=
  fun b E s T h _ τ m W => measurable_closedSourceData b E s T h τ m W

/-- **`TargetT1`.** -/
theorem t1 : TargetT1 := fun hMT hGA hSR hLp _ h1 h2 =>
  complexClosingError_of_meas_contracts closedDataMeasurable hMT hGA hSR hLp h1 h2

end BlockBand.SourceProcess.PhysApprox
