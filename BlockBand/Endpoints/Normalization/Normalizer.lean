module

public import BlockBand.Endpoints.Normalization.PalmBridge
public import BlockBand.Internal.Contracts.ClocksCommonPort
public import BlockBand.Internal.Contracts.Critical
public import BlockBand.Coarea.FreshPalmDensity

/-!
# The normalizer theorem, its one-block version, and the deterministic-normalizer corollary

**Hypotheses.** `ClocksCommonPort.PairRegularEventContract` (resp. `BlockRegularEventContract`),
only at `D = 1`; `Critical.PointDensityContract`; `CoareaPalm.FreshEigenpairDensityContract`
(fields `frame_exists`, `density`, `palm`); and the type of `Clocks.ExactPalmContract.upper`
(resp. `OneBlockPalmContract.upper`), taken as the hypothesis `hU`. Also used: the lemma
`FreshPalm.fiber_test_eq` (rank identification on the fiber support).

**Main results.**
* `freshMeanEigenvalueMeasure_eq_withDensity`: `Z = N ρ_{F,c}`, i.e. the normalized expected
  eigenvalue measure of `F + GUE_N(c/N)` has the continuous density `palmMass F c y / N`
  (every `N ≥ 1`, Hermitian `F`, `c > 0`; exact).
* `palmMass_pointDensity`: `|Z_{F,c}(x)/N - π⁻¹ Im m_{F,c}(x)| ≤ ε_N` on the class.
* `deterministic_normalizer_lower` (the deterministic-normalizer corollary):
  `Im m_{F,c}(x) ≥ v_* ⇒ Z_{F,c}(x) ≥ (v_*/2π) N` for `N ≥ N₀`, uniformly on
  `FreshClass F A c x r₀ s₀ v₀`.
* `normalizer_of : … → NormalizerContract` (fields `l1`, `tv`) and
  `oneBlockNormalizer_of : … → OneBlockNormalizerContract`.

**Measures, domain, uniformity.** `Pω` is the exterior law of a splitting (a probability law:
`isProbabilityMeasure_pairSplitting`, `…_blockSplitting`), `𝔭_W = w(u)du ⊗ Pω`, `𝔪_W` the exact
exterior window measure; uniform in `4 ≤ n ≤ TW`, the model, the pair/block, the splitting law and
the frame.

**Proof.** At `u` with `w(u) ≠ 0` the energy `e(u) = E + u/(Nρ(E))` is a
deterministic bulk energy with `|e(u) - E| ≤ R/(Nρ(E))`. On the regular event `IsPairRegular`
(any reindexing `σ`; bridged to `PalmBridge` along `card = 2W`, `pairNormalizer_toReal_eq`),
`Z(e)/𝒩 = ρ_{F(e),s}(e)` and the point-density lemma with `|m - conj a(e)| ≤ η` give
`|Z(e)/𝒩 - ρ(e)| ≤ ε_𝒩 + η/π`; continuity of `ρ` at `E` gives `ρ(e(u))/ρ(E) → 1`. Off the
event, `Z/𝒩 ≤ C` (`hU`, on the a.s. Hermitian exteriors) and the outer probability is
`≤ W⁻¹`. Integrating against `w(u)du` uses `lintegral_prod_le` (no joint measurability is
needed for `l1`). The `tv` field is `tv_of_l1`: the map `e ↦ u` pushes `𝔪_W` to
`(Z(e(u))/(𝒩ρ(E))) 𝔭_W` (`n/(2Nρ) = 1/(2Wρ)`; one block `n/(Nρ) = 1/(Wρ)`), using joint
measurability of `(e, ω) ↦ Z(ω, e)` (`measurable_pairNormalizer_joint`), then
`|∫F d𝔪 - ∫F d𝔭| ≤ ∫|Z/(𝒩ρ(E)) - 1| d𝔭`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal ComplexConjugate

/-!
## 1. The fresh normalizer is `N` times the expected eigenvalue density
-/

section FreshDensity

variable {N : ℕ}

/-- The rank-`ℓ` Palm mass `m_ℓ(E) = E_{A⁰}[w_{ℓ,E}]`. -/
def rankPalmMass (F : Matrix (Fin N) (Fin N) ℂ) (c E : ℝ) (ℓ : Fin N) : ℝ :=
  ∫ A0, palmWeight F c E ℓ A0 ∂freshTracelessLaw N c

theorem rankPalmMass_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (c E : ℝ) (ℓ : Fin N) :
    0 ≤ rankPalmMass F c E ℓ :=
  integral_nonneg fun A0 => palmWeight_nonneg' F c E ℓ A0

theorem continuous_rankPalmMass (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (ℓ : Fin N) :
    Continuous fun E => rankPalmMass F c E ℓ := by
  unfold rankPalmMass
  refine continuous_of_dominated (bound := fun _ =>
      (Real.sqrt (2 * Real.pi * BlockBand.Palm.scalarVariance (Real.toNNReal c) N))⁻¹)
    (fun E => (measurable_palmWeight' F c E ℓ).aestronglyMeasurable)
    (fun E => Eventually.of_forall fun A0 => ?_) (integrable_const _)
    (Eventually.of_forall fun A0 => BlockBand.Coarea.FreshPalm.continuous_palmWeight_E F c ℓ A0)
  rw [Real.norm_eq_abs, abs_of_nonneg (palmWeight_nonneg' F c E ℓ A0)]
  exact palmWeight_le_prefactor F c E ℓ A0

theorem palmMass_eq_sum_rank (F : Matrix (Fin N) (Fin N) ℂ) (c E : ℝ) :
    palmMass F c E = ∑ ℓ : Fin N, rankPalmMass F c E ℓ := rfl

theorem continuous_palmMass_energy (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) :
    Continuous fun E => palmMass F c E := by
  simp only [palmMass_eq_sum_rank]
  exact continuous_finsetSum _ fun ℓ _ => continuous_rankPalmMass F c ℓ

/-- The rank-`ℓ` eigenvalue law of `F + GUE_N(c/N)` has Lebesgue density `m_ℓ(E)`, tested
against measurable `h ≥ 0`. Consumes `FreshEigenpairDensityContract` (`frame_exists`, `density`,
`palm`) and the unconditional rank identification `FreshPalm.fiber_test_eq`. -/
theorem lintegral_freshEigenvalue_eq (hD : FreshEigenpairDensityContract) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {c : ℝ} (hc : 0 < c) (ℓ : Fin N)
    {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ G, h (freshEigenvalue (F + G) ℓ) ∂gueMeasure (Fin N) (Real.toNNReal (c / N)) =
      ∫⁻ E, h E * ENNReal.ofReal (rankPalmMass F c E ℓ) := by
  obtain ⟨U, hU⟩ := hD.frame_exists N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : 0 < Real.toNNReal (c / N) := Real.toNNReal_pos.2 (div_pos hc hNr)
  have hg : Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
      h (freshEigenvalue (F + G) ℓ) * (fun _ => (1 : ℝ≥0∞))
        (BlockBand.Coarea.FreshPalm.freshProjector (F + tracelessPart G) ℓ) :=
    (hh.comp ((BlockBand.Coarea.FreshPalm.measurable_freshEigenvalue ℓ).comp
      (FixedOmega.measurable_matrix_add measurable_const measurable_id))).mul measurable_const
  have key := hD.density N hN F hF _ ht ℓ U hU _ hg
  simp only [mul_one] at key
  rw [key]
  refine lintegral_congr fun E => ?_
  have h1 := BlockBand.Coarea.FreshPalm.fiber_test_eq hN hF ℓ hU (f := fun _ => (1 : ℝ≥0∞))
    measurable_const h (Real.toNNReal (c / N)) E
  have h2 := hD.palm N hN F hF c hc ℓ U hU (fun _ => (1 : ℝ≥0∞)) measurable_const E
  simp only [mul_one] at h1 h2
  rw [h1, ← h2]
  congr 1
  have h3 := lintegral_palmWeight_eq_ofReal F c E ℓ
  simp only [mul_one] at h3
  exact h3

/-- **`Z = N ρ_{F,c}`** (the identity of the deterministic-normalizer corollary: the
normalizer is exactly the expected counting density). For `N ≥ 1`, Hermitian `F` and `c > 0`:
the normalized expected eigenvalue measure of `F + GUE_N(c/N)` is `ρ(y) dy` with
`ρ(y) = palmMass F c y / N`. From `FreshEigenpairDensityContract`. -/
theorem freshMeanEigenvalueMeasure_eq_withDensity (hD : FreshEigenpairDensityContract)
    (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {c : ℝ} (hc : 0 < c) :
    freshMeanEigenvalueMeasure N c F =
      volume.withDensity (fun y => ENNReal.ofReal (palmMass F c y / N)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  ext B hB
  rw [withDensity_apply _ hB]
  unfold freshMeanEigenvalueMeasure
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  have hrank : ∀ ℓ : Fin N,
      ((gueMeasure (Fin N) (Real.toNNReal (c / N))).map
          (fun G => freshEigenvalue (F + G) ℓ)) B =
        ∫⁻ y in B, ENNReal.ofReal (rankPalmMass F c y ℓ) := by
    intro ℓ
    have hm : Measurable fun G : Matrix (Fin N) (Fin N) ℂ => freshEigenvalue (F + G) ℓ :=
      (BlockBand.Coarea.FreshPalm.measurable_freshEigenvalue ℓ).comp
        (FixedOmega.measurable_matrix_add measurable_const measurable_id)
    rw [← lintegral_indicator_one hB, lintegral_map (measurable_one.indicator hB) hm,
      lintegral_freshEigenvalue_eq hD hN hF hc ℓ (measurable_one.indicator hB),
      ← lintegral_indicator hB]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ B <;> simp [hy]
  simp only [hrank]
  have hmeas : ∀ ℓ : Fin N, Measurable fun y => ENNReal.ofReal (rankPalmMass F c y ℓ) :=
    fun ℓ => ENNReal.measurable_ofReal.comp (continuous_rankPalmMass F c ℓ).measurable
  rw [← lintegral_finsetSum _ fun ℓ _ => hmeas ℓ, ← lintegral_const_mul' _ _
    (ENNReal.inv_ne_top.2 (by exact_mod_cast hN.ne'))]
  refine lintegral_congr fun y => ?_
  rw [palmMass_eq_sum_rank, ENNReal.ofReal_div_of_pos hNr,
    ENNReal.ofReal_sum_of_nonneg fun ℓ _ => rankPalmMass_nonneg F c y ℓ, ENNReal.ofReal_natCast,
    div_eq_mul_inv, mul_comm]

end FreshDensity

/-!
## 2. Point density at the normalizer and the deterministic-normalizer corollary
-/

section PointDensity

variable {N : ℕ}

/-- Read at the Palm mass: with the `PointDensityContract` and the
identity `Z = N ρ_{F,c}`, there is `ε_N → 0` (depending only on `A, c, r₀, s₀, v₀`) with
`|Z_{F,c}(x)/N - π⁻¹ Im m_{F,c}(x)| ≤ ε_N` for all `N ≥ 1`, `F` in the class at `(c, x)`.
-/
theorem palmMass_pointDensity (hPD : PointDensityContract) (hD : FreshEigenpairDensityContract)
    {A c r₀ s₀ v₀ : ℝ} (hFC : FreshConstants c r₀ s₀ v₀) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (x : ℝ),
        FreshClass F A c x r₀ s₀ v₀ →
          |palmMass F c x / N - (freshDyson F c x).im / Real.pi| ≤ ε N := by
  obtain ⟨ε, hε, hb⟩ := hPD A c r₀ s₀ v₀ hFC
  refine ⟨ε, hε, fun N hN F x hF => ?_⟩
  have hc : 0 < c := hFC.1
  exact (hb N hN F x hF).2 (fun y => palmMass F c y / N)
    ((continuous_palmMass_energy F c).div_const _)
    (freshMeanEigenvalueMeasure_eq_withDensity hD hN hF.1 hc)

/-- **The deterministic-normalizer lower bound**, from `PointDensityContract` and
`FreshEigenpairDensityContract`. Fixed first: the norm exponent `A` and constants with
`FreshConstants c r₀ s₀ v₀`, then `v_* > 0`.
There is `N₀` such that uniformly for `N ≥ N₀`
(`N ≥ 1`), every `F` in the deformation class `FreshClass F A c x r₀ s₀ v₀` (Hermitian,
`‖F‖ ≤ N^A`, regular at `(c, x)`) and every real `x` with `Im m_{F,c}(x) ≥ v_*`:
`Z_{F,c}(x) ≥ (v_*/2π) N`, where `Z_{F,c}(x) = palmMass F c x = Σ_ℓ E_{A⁰}[w_{ℓ,x}]` is the
complete unranked Palm mass (all ordered sectors).
The identity `Z_{F,c} = N ρ_{F,c}` is
`freshMeanEigenvalueMeasure_eq_withDensity`.
Measure:
`GUE_N(c/N)` and its traceless part.
-/
theorem deterministic_normalizer_lower (hPD : PointDensityContract)
    (hD : FreshEigenpairDensityContract) :
    ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ → ∀ vstar : ℝ, 0 < vstar →
      ∃ N₀ : ℕ, ∀ N : ℕ, 0 < N → N₀ ≤ N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (x : ℝ),
        FreshClass F A c x r₀ s₀ v₀ → vstar ≤ (freshDyson F c x).im →
          vstar / (2 * Real.pi) * N ≤ palmMass F c x := by
  intro A c r₀ s₀ v₀ hFC vstar hv
  obtain ⟨ε, hε, hb⟩ := palmMass_pointDensity (A := A) hPD hD hFC
  have hpi := Real.pi_pos
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hε (vstar / (2 * Real.pi)) (by positivity)
  refine ⟨N₀, fun N hN hNN F x hF hm => ?_⟩
  have h1 := hb N hN F x hF
  have h2 := hN₀ N hNN
  rw [Real.dist_eq, sub_zero] at h2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : vstar / Real.pi ≤ (freshDyson F c x).im / Real.pi :=
    div_le_div_of_nonneg_right hm hpi.le
  have h4 : vstar / (2 * Real.pi) ≤ palmMass F c x / N := by
    have h5 := (abs_le.1 h1).1
    have h6 : ε N ≤ |ε N| := le_abs_self _
    have h7 : vstar / Real.pi - vstar / (2 * Real.pi) = vstar / (2 * Real.pi) := by
      field_simp; ring
    linarith
  rwa [le_div_iff₀ hNr] at h4

private theorem im_conj_matchedA' (e : ℝ) : (conj (matchedA e)).im = Real.sqrt (4 - e ^ 2) / 2 := by
  simp [matchedA, neg_div]

/-- On the regular event: `|Z/N - ρ_sc(e)| ≤ ε_N + η/π`, from the point density bound and
`|m - conj a(e)| ≤ η` (`ρ_sc(e) = π⁻¹ Im conj a(e)`). -/
theorem palmMass_near_semicircle {F : Matrix (Fin N) (Fin N) ℂ} {c e η εN : ℝ}
    (hb : |palmMass F c e / N - (freshDyson F c e).im / Real.pi| ≤ εN)
    (hm : ‖freshDyson F c e - conj (matchedA e)‖ ≤ η) :
    |palmMass F c e / N - Parameters.semicircleDensity e| ≤ εN + η / Real.pi := by
  have hpi := Real.pi_pos
  have hsc : Parameters.semicircleDensity e = (conj (matchedA e)).im / Real.pi := by
    rw [im_conj_matchedA', Parameters.semicircleDensity]; field_simp
  have him : |(freshDyson F c e).im - (conj (matchedA e)).im| ≤ η := by
    rw [← Complex.sub_im]; exact (Complex.abs_im_le_norm _).trans hm
  have h2 : |(freshDyson F c e).im / Real.pi - Parameters.semicircleDensity e| ≤ η / Real.pi := by
    rw [hsc, ← sub_div, abs_div, abs_of_pos hpi]
    exact div_le_div_of_nonneg_right him hpi.le
  calc |palmMass F c e / N - Parameters.semicircleDensity e|
      ≤ |palmMass F c e / N - (freshDyson F c e).im / Real.pi| +
          |(freshDyson F c e).im / Real.pi - Parameters.semicircleDensity e| := abs_sub_le _ _ _
    _ ≤ εN + η / Real.pi := add_le_add hb h2

end PointDensity

/-!
## 3. Abstract window lemmas
-/

section Window

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A window vanishes outside a bounded interval. -/
private theorem window_bound {w : ℝ → ℝ} (hw : IsWindow w) : ∃ R : ℝ, ∀ u, w u ≠ 0 → |u| ≤ R := by
  obtain ⟨r, hr⟩ := hw.2.1.isCompact.isBounded.subset_closedBall 0
  refine ⟨r, fun u hu => ?_⟩
  have h := hr (subset_tsupport w hu)
  rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h

private theorem lintegral_window {w : ℝ → ℝ} (hw : IsWindow w) : ∫⁻ u, ENNReal.ofReal (w u) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hw.1.integrable_of_hasCompactSupport hw.2.1)
    (Eventually.of_forall hw.2.2.1), hw.2.2.2, ENNReal.ofReal_one]

/-- The energy-window marginal `w(u) du` is a probability measure. -/
theorem isProbabilityMeasure_windowLaw {w : ℝ → ℝ} (hw : IsWindow w) :
    IsProbabilityMeasure (volume.withDensity fun u => ENNReal.ofReal (w u)) :=
  ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact lintegral_window hw⟩

/-- A law whose product with a probability law has a probability image is a probability law
(applied to the exterior law of a splitting). -/
theorem isProbabilityMeasure_of_prod_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure ν] {f : Ω × X → Y} (hf : Measurable f)
    {L : Measure Y} [IsProbabilityMeasure L] (h : (μ.prod ν).map f = L) :
    IsProbabilityMeasure μ := by
  have h1 := congrArg (fun m : Measure Y => m Set.univ) h
  simp only [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ, measure_univ] at h1
  rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ (μ := ν), mul_one] at h1
  exact ⟨h1⟩

/-- The prior `L¹` bound from fixed-energy bounds on the support of the window
(`lintegral_prod_le`: no joint measurability is needed). -/
theorem l1_of_pointwise (Pω : Measure Ω) [SFinite Pω] {w : ℝ → ℝ} (hw : IsWindow w)
    (f : ℝ × Ω → ℝ≥0∞) (δ : ℝ) (h : ∀ u, w u ≠ 0 → ∫⁻ ω, f (u, ω) ∂Pω ≤ ENNReal.ofReal δ) :
    ∫⁻ x, f x ∂priorWindowMeasure Pω w ≤ ENNReal.ofReal δ := by
  have hwm : Measurable fun u => ENNReal.ofReal (w u) :=
    ENNReal.measurable_ofReal.comp hw.1.measurable
  have := isProbabilityMeasure_windowLaw hw
  unfold priorWindowMeasure
  calc ∫⁻ x, f x ∂(volume.withDensity fun u => ENNReal.ofReal (w u)).prod Pω
      ≤ ∫⁻ u, ∫⁻ ω, f (u, ω) ∂Pω ∂(volume.withDensity fun u => ENNReal.ofReal (w u)) :=
        lintegral_prod_le f
    _ ≤ ∫⁻ u, ENNReal.ofReal (w u) * ∫⁻ ω, f (u, ω) ∂Pω :=
        lintegral_withDensity_le_lintegral_mul _ hwm _
    _ ≤ ∫⁻ u, ENNReal.ofReal (w u) * ENNReal.ofReal δ := by
        refine lintegral_mono fun u => ?_
        by_cases hu : w u = 0
        · simp [hu]
        · gcongr
          exact h u hu
    _ = ENNReal.ofReal δ := by rw [lintegral_mul_const _ hwm, lintegral_window hw, one_mul]

/-- Splitting a fixed-energy expectation on a good event of small outer probability. -/
theorem lintegral_le_good_bad (Pω : Measure Ω) [IsProbabilityMeasure Pω] (φ : Ω → ℝ≥0∞)
    (Herm Good : Ω → Prop) (hHerm : ∀ᵐ ω ∂Pω, Herm ω) {δ M β : ℝ}
    (hgood : ∀ ω, Herm ω → Good ω → φ ω ≤ ENNReal.ofReal δ)
    (hall : ∀ ω, Herm ω → φ ω ≤ ENNReal.ofReal M)
    (hbad : Pω {ω | ¬ Good ω} ≤ ENNReal.ofReal β) :
    ∫⁻ ω, φ ω ∂Pω ≤ ENNReal.ofReal δ + ENNReal.ofReal M * ENNReal.ofReal β := by
  set S := toMeasurable Pω {ω | ¬ Good ω}
  have hS : MeasurableSet S := measurableSet_toMeasurable _ _
  calc ∫⁻ ω, φ ω ∂Pω
      ≤ ∫⁻ ω, (ENNReal.ofReal δ + S.indicator (fun _ => ENNReal.ofReal M) ω) ∂Pω := by
        refine lintegral_mono_ae ?_
        filter_upwards [hHerm] with ω hω
        by_cases hωS : ω ∈ S
        · rw [Set.indicator_of_mem hωS]; exact (hall ω hω).trans le_add_self
        · have hg : Good ω := by
            by_contra hng; exact hωS (subset_toMeasurable _ _ hng)
          exact (hgood ω hω hg).trans le_self_add
    _ = ENNReal.ofReal δ + ENNReal.ofReal M * Pω S := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_indicator_const hS]
    _ ≤ _ := by rw [measure_toMeasurable]; gcongr

/-- **Total variation from the prior `L¹` bound** (the "in particular" of the normalizer theorem):
change of variables `e ↦ u = λ(e - E)` (prefactor `pref = λ/K`), then
`|∫F d𝔪 - ∫F d𝔭| = |∫F (Z/K - 1) d𝔭| ≤ ∫|Z/K - 1| d𝔭`, for measurable `|F| ≤ 1`. Needs the
joint measurability of `(e, ω) ↦ Z(ω, e)` and an a.s. uniform bound on `Z`. -/
theorem tv_of_l1 (Pω : Measure Ω) [IsProbabilityMeasure Pω] {w : ℝ → ℝ} (hw : IsWindow w)
    {E lam pref K B ε : ℝ} (hlam : 0 < lam) (hK : 0 < K) (hpref : pref = lam / K) (hε : 0 ≤ ε)
    (Z : Ω → ℝ → ℝ≥0∞) (hZm : Measurable fun x : ℝ × Ω => Z x.2 x.1)
    (hZB : ∀ᵐ ω ∂Pω, ∀ e, Z ω e ≤ ENNReal.ofReal B)
    (hl1 : ∫⁻ x, ENNReal.ofReal |(Z x.2 (E + x.1 / lam)).toReal / K - 1|
        ∂priorWindowMeasure Pω w ≤ ENNReal.ofReal ε)
    (F : ℝ × Ω → ℝ) (hF : Measurable F) (hF1 : ∀ x, |F x| ≤ 1) :
    |(∫ x, F (lam * (x.1 - E), x.2) ∂(volume.prod Pω).withDensity fun x =>
        ENNReal.ofReal (pref * w (lam * (x.1 - E))) * Z x.2 x.1) -
      ∫ x, F x ∂priorWindowMeasure Pω w| ≤ ε := by
  have hwm : Measurable w := hw.1.measurable
  have hw'm : Measurable fun u => ENNReal.ofReal (w u) := ENNReal.measurable_ofReal.comp hwm
  have := isProbabilityMeasure_windowLaw hw
  have h𝔭 : priorWindowMeasure Pω w =
      (volume.withDensity fun u => ENNReal.ofReal (w u)).prod Pω := rfl
  have : IsProbabilityMeasure (priorWindowMeasure Pω w) := by rw [h𝔭]; infer_instance
  set ψ : ℝ × Ω → ℝ × Ω := fun x => (lam * (x.1 - E), x.2) with hψdef
  have hψ : Measurable ψ :=
    (measurable_const.mul (measurable_fst.sub measurable_const)).prodMk measurable_snd
  set d : ℝ × Ω → ℝ≥0∞ := fun x => ENNReal.ofReal (pref * w (lam * (x.1 - E))) * Z x.2 x.1
    with hddef
  have hd : Measurable d :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul
      (hwm.comp (measurable_const.mul (measurable_fst.sub measurable_const))))).mul hZm
  set ζ : ℝ × Ω → ℝ≥0∞ := fun x => ENNReal.ofReal (1 / K) * Z x.2 (E + x.1 / lam) with hζdef
  have hζ : Measurable ζ := measurable_const.mul
    (hZm.comp ((measurable_const.add (measurable_fst.div_const lam)).prodMk measurable_snd))
  have hmap : ((volume.prod Pω).withDensity d).map ψ =
      (priorWindowMeasure Pω w).withDensity ζ := by
    refine Measure.ext_of_lintegral _ fun φ hφ => ?_
    rw [lintegral_map hφ hψ]
    change ∫⁻ a, (φ ∘ ψ) a ∂((volume.prod Pω).withDensity d) = _
    rw [lintegral_withDensity_eq_lintegral_mul _ hd (hφ.comp hψ),
      lintegral_withDensity_eq_lintegral_mul _ hζ hφ, h𝔭,
      lintegral_prod _ (hd.mul (hφ.comp hψ)).aemeasurable,
      lintegral_prod _ (hζ.mul hφ).aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ hw'm ((hζ.mul hφ).lintegral_prod_right')]
    set Hint : ℝ × Ω → ℝ≥0∞ := fun y =>
      ENNReal.ofReal (pref * w y.1) * Z y.2 (E + y.1 / lam) * φ y with hHintdef
    have hHint : Measurable Hint :=
      ((ENNReal.measurable_ofReal.comp (measurable_const.mul (hwm.comp measurable_fst))).mul
        (hZm.comp ((measurable_const.add (measurable_fst.div_const lam)).prodMk
          measurable_snd))).mul hφ
    set H : ℝ → ℝ≥0∞ := fun u => ∫⁻ ω, Hint (u, ω) ∂Pω with hHdef
    have hH : Measurable H := hHint.lintegral_prod_right'
    have hstep1 : ∀ e : ℝ, ∫⁻ ω, (d * (φ ∘ ψ)) (e, ω) ∂Pω = H (lam * (e - E)) := by
      intro e
      refine lintegral_congr fun ω => ?_
      have he : E + lam * (e - E) / lam = e := by field_simp; ring
      simp only [Pi.mul_apply, Function.comp, hddef, hψdef, hHintdef, he]
    rw [lintegral_congr hstep1]
    have hsub := lintegral_sub_right_eq_self (μ := volume) (fun e => H (lam * e)) E
    rw [hsub]
    have hcv : ∫⁻ e, H (lam * e) = ENNReal.ofReal |lam⁻¹| * ∫⁻ u, H u := by
      rw [← smul_eq_mul, ← lintegral_smul_measure, ← Real.map_volume_mul_left hlam.ne',
        lintegral_map hH (measurable_const_mul lam)]
    rw [hcv, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun u => ?_
    simp only [hHdef, hHintdef, Pi.mul_apply]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun ω => ?_
    simp only [hζdef]
    have hcoef : ENNReal.ofReal |lam⁻¹| * ENNReal.ofReal (pref * w u) =
        ENNReal.ofReal (w u) * ENNReal.ofReal (1 / K) := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (hw.2.2.1 u)]
      congr 1
      rw [abs_of_pos (inv_pos.2 hlam), hpref]
      field_simp
    calc ENNReal.ofReal |lam⁻¹| * (ENNReal.ofReal (pref * w u) * Z ω (E + u / lam) * φ (u, ω))
        = (ENNReal.ofReal |lam⁻¹| * ENNReal.ofReal (pref * w u)) *
            (Z ω (E + u / lam) * φ (u, ω)) := by ring
      _ = ENNReal.ofReal (w u) * (ENNReal.ofReal (1 / K) * Z ω (E + u / lam) * φ (u, ω)) := by
        rw [hcoef]; ring
  have hZB' : ∀ᵐ x ∂priorWindowMeasure Pω w, ∀ e, Z x.2 e ≤ ENNReal.ofReal B := by
    rw [h𝔭]; exact Measure.quasiMeasurePreserving_snd.ae hZB
  have hζreal : ∀ x, (ζ x).toReal = (Z x.2 (E + x.1 / lam)).toReal / K := by
    intro x
    simp only [hζdef]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    ring
  have hζbd : ∀ᵐ x ∂priorWindowMeasure Pω w, (ζ x).toReal ≤ max B 0 / K := by
    filter_upwards [hZB'] with x hx
    rw [hζreal]
    refine div_le_div_of_nonneg_right ?_ hK.le
    exact ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
      ((hx _).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hζfin : ∀ᵐ x ∂priorWindowMeasure Pω w, ζ x < ∞ := by
    filter_upwards [hZB'] with x hx
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((hx _).trans_lt ENNReal.ofReal_lt_top)
  rw [← integral_map hψ.aemeasurable hF.aestronglyMeasurable, hmap,
    integral_withDensity_eq_integral_toReal_smul hζ hζfin]
  have hζtm : Measurable fun x => (ζ x).toReal := hζ.ennreal_toReal
  have hint1 : Integrable (fun x => (ζ x).toReal • F x) (priorWindowMeasure Pω w) := by
    refine Integrable.of_bound (hζtm.smul hF).aestronglyMeasurable (max B 0 / K) ?_
    filter_upwards [hζbd] with x hx
    rw [smul_eq_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg]
    calc (ζ x).toReal * |F x| ≤ (ζ x).toReal * 1 :=
          mul_le_mul_of_nonneg_left (hF1 x) ENNReal.toReal_nonneg
      _ ≤ max B 0 / K := by rw [mul_one]; exact hx
  have hint2 : Integrable F (priorWindowMeasure Pω w) :=
    Integrable.of_bound hF.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hF1 x)
  have hint3 : Integrable (fun x => |(ζ x).toReal - 1|) (priorWindowMeasure Pω w) := by
    refine Integrable.of_bound ((hζtm.sub measurable_const).abs).aestronglyMeasurable
      (max B 0 / K + 1) ?_
    filter_upwards [hζbd] with x hx
    rw [Real.norm_eq_abs, abs_abs]
    have h0 : 0 ≤ (ζ x).toReal := ENNReal.toReal_nonneg
    rw [abs_le]; constructor <;> linarith
  rw [← integral_sub hint1 hint2]
  calc |∫ x, ((ζ x).toReal • F x - F x) ∂priorWindowMeasure Pω w|
      ≤ ∫ x, |(ζ x).toReal - 1| ∂priorWindowMeasure Pω w := by
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
          (Eventually.of_forall fun _ => norm_nonneg _) hint3 (Eventually.of_forall fun x => ?_))
        simp only [smul_eq_mul, Real.norm_eq_abs]
        rw [show (ζ x).toReal * F x - F x = ((ζ x).toReal - 1) * F x by ring, abs_mul]
        calc |(ζ x).toReal - 1| * |F x| ≤ |(ζ x).toReal - 1| * 1 :=
              mul_le_mul_of_nonneg_left (hF1 x) (abs_nonneg _)
          _ = |(ζ x).toReal - 1| := mul_one _
    _ = (∫⁻ x, ENNReal.ofReal |(ζ x).toReal - 1| ∂priorWindowMeasure Pω w).toReal :=
        integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => abs_nonneg _)
          hint3.aestronglyMeasurable
    _ ≤ ε := by
        refine ENNReal.toReal_le_of_le_ofReal hε (le_of_eq_of_le (lintegral_congr fun x => ?_) hl1)
        rw [hζreal]

end Window

/-!
## 4. Joint measurability, exterior laws, reindexing
-/

section Exterior

/-- `x ↦ F(e(x)) = V - C*(H_R - e)⁻¹C` is measurable jointly in all its data. -/
theorem measurable_physicalCoareaF_joint {X : Type*} [MeasurableSpace X] {α β : Type*}
    [Fintype α] [DecidableEq α] {H : X → Matrix α α ℂ} {C : X → Matrix α β ℂ}
    {V : X → Matrix β β ℂ} {e : X → ℝ} (hH : Measurable H) (hC : Measurable C)
    (hV : Measurable V) (he : Measurable e) :
    Measurable fun x => physicalCoareaF (H x) (C x) (V x) (e x) := by
  have hs : Measurable fun x => H x - ((e x : ℝ) : ℂ) • (1 : Matrix α α ℂ) := by
    refine FixedOmega.measurable_matrix_sub hH ?_
    refine Measurable.of_eval_matrix _ fun a b => ?_
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact (Complex.measurable_ofReal.comp he).mul measurable_const
  unfold physicalCoareaF physicalCoareaResolvent
  exact FixedOmega.measurable_matrix_sub hV
    (CoareaNative.BlockBand.measurable_matrix_mul_rect
      (CoareaNative.BlockBand.measurable_matrix_mul_rect
        (CoareaNative.BlockBand.Measurable.matrix_conjTranspose hC)
        (CoareaNative.BlockBand.Measurable.matrixNonsingInv hs)) hC)

/-- The generic unranked mass `Z = normalizerOn` is jointly measurable in `(F, e)`. -/
theorem measurable_normalizerOn_joint {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (t : ℝ≥0) (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ) (hU : Measurable U) :
    Measurable fun y : Matrix ι ι ℂ × ℝ => normalizerOn n t U y.1 y.2 := by
  have hU1 : Measurable fun q : ((Matrix ι ι ℂ × ℝ) × (ι → ℂ)) ×
      Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ => U q.1.2 :=
    hU.comp (measurable_snd.comp measurable_fst)
  have hF : Measurable fun q : ((Matrix ι ι ℂ × ℝ) × (ι → ℂ)) ×
      Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ => q.1.1.1 :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have he : Measurable fun q : ((Matrix ι ι ℂ × ℝ) × (ι → ℂ)) ×
      Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ => q.1.1.2 :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hE : Measurable fun q : ((Matrix ι ι ℂ × ℝ) × (ι → ℂ)) ×
      Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ =>
      ((q.1.1.2 : ℝ) : ℂ) • (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ) := by
    apply Measurable.of_eval_matrix
    intro a b
    simp only [Matrix.smul_apply]
    exact (Complex.measurable_ofReal.comp he).smul measurable_const
  have hM : Measurable fun q : ((Matrix ι ι ℂ × ℝ) × (ι → ℂ)) ×
      Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ => frameMOn n U q.1.1.1 q.1.1.2 q.1.2 q.2 := by
    unfold frameMOn
    exact FixedOmega.measurable_matrix_sub (FixedOmega.measurable_matrix_add
      (CoareaNative.BlockBand.measurable_matrix_mul_rect
        (CoareaNative.BlockBand.measurable_matrix_mul_rect
          (CoareaNative.BlockBand.Measurable.matrix_conjTranspose hU1) hF) hU1)
      measurable_snd) hE
  have hR : Measurable fun q : ((Matrix ι ι ℂ × ℝ) × (ι → ℂ)) ×
      Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ => regressionFactor t q.1.1.2 q.1.2 q.1.1.1 := by
    have hg : Measurable fun q : ((Matrix ι ι ℂ × ℝ) × (ι → ℂ)) ×
        Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ => (q.1.1.2, q.1.2, q.1.1.1) :=
      he.prodMk ((measurable_snd.comp measurable_fst).prodMk hF)
    have h1 := measurable_regressionFactor_joint (ι := ι) (t : ℝ)
    have h2 := h1.comp hg
    exact h2
  have hdet : Measurable fun q : ((Matrix ι ι ℂ × ℝ) × (ι → ℂ)) ×
      Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ =>
      Complex.normSq (frameMOn n U q.1.1.1 q.1.1.2 q.1.2 q.2).det :=
    Complex.continuous_normSq.measurable.comp ((continuous_id.matrix_det).measurable.comp hM)
  have hI : Measurable fun q : ((Matrix ι ι ℂ × ℝ) × (ι → ℂ)) ×
      Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ =>
      ENNReal.ofReal (coareaConstant n t * regressionFactor t q.1.1.2 q.1.2 q.1.1.1 *
        Complex.normSq (frameMOn n U q.1.1.1 q.1.1.2 q.1.2 q.2).det) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.mul hR).mul hdet)
  have h2 : Measurable fun a : (Matrix ι ι ℂ × ℝ) × (ι → ℂ) =>
      ∫⁻ G', ENNReal.ofReal (coareaConstant n t * regressionFactor t a.1.2 a.2 a.1.1 *
        Complex.normSq (frameMOn n U a.1.1 a.1.2 a.2 G').det) ∂gueMeasure (Fin (n - 1)) t :=
    hI.lintegral_prod_right'
  have h3 : Measurable fun y : Matrix ι ι ℂ × ℝ =>
      ∫⁻ v, ∫⁻ G', ENNReal.ofReal (coareaConstant n t * regressionFactor t y.2 v y.1 *
        Complex.normSq (frameMOn n U y.1 y.2 v G').det) ∂gueMeasure (Fin (n - 1)) t
        ∂projectiveHaar ι :=
    h2.lintegral_prod_right'
  unfold normalizerOn
  exact h3

variable (p : Parameters)

/-- The pair normalizer `(e, ω) ↦ Z(ω, e)` is jointly measurable. -/
theorem measurable_pairNormalizer_joint (i : ZMod p.n)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : Measurable U) :
    Measurable fun x : ℝ × SplitState p i => pairNormalizer p i U x.2 x.1 := by
  have hF : Measurable fun x : ℝ × SplitState p i =>
      (physicalCoareaF x.2.1 x.2.2.1 x.2.2.2 x.1, x.1) :=
    (measurable_physicalCoareaF_joint (measurable_fst.comp measurable_snd)
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      (measurable_snd.comp (measurable_snd.comp measurable_snd)) measurable_fst).prodMk
      measurable_fst
  have h := (measurable_normalizerOn_joint (2 * p.W) (pairTime p (pairS p)) U hU).comp hF
  have heq : (fun x : ℝ × SplitState p i => pairNormalizer p i U x.2 x.1) =
      (fun y : PairMatrix p i × ℝ => normalizerOn (2 * p.W) (pairTime p (pairS p)) U y.1 y.2) ∘
        (fun x : ℝ × SplitState p i => (physicalCoareaF x.2.1 x.2.2.1 x.2.2.2 x.1, x.1)) :=
    funext fun x => pairNormalizer_eq_on p i U x.2 x.1
  rw [heq]
  exact h

/-- The one-block normalizer `(e, ω) ↦ Z₀(ω, e)` is jointly measurable. -/
theorem measurable_blockNormalizer_joint (k : ZMod p.n)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) :
    Measurable fun x : ℝ × BlockState p k => blockNormalizer p k U x.2 x.1 := by
  have hF : Measurable fun x : ℝ × BlockState p k => (blockF p k x.2 x.1, x.1) :=
    (measurable_physicalCoareaF_joint (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd) measurable_const measurable_fst).prodMk
      measurable_fst
  have h := (measurable_normalizerOn_joint p.W (Real.toNNReal (p.c / p.W)) U hU).comp hF
  have heq : (fun x : ℝ × BlockState p k => blockNormalizer p k U x.2 x.1) =
      (fun y : Matrix (BlockSite p k) (BlockSite p k) ℂ × ℝ =>
          normalizerOn p.W (Real.toNNReal (p.c / p.W)) U y.1 y.2) ∘
        (fun x : ℝ × BlockState p k => (blockF p k x.2 x.1, x.1)) :=
    funext fun x => blockNormalizer_eq_on p k U x.2 x.1
  rw [heq]
  exact h

/-- The one-block reassembly is measurable. -/
theorem measurable_assembleBlock (k : ZMod p.n) :
    Measurable fun x : BlockState p k × Matrix (BlockSite p k) (BlockSite p k) ℂ =>
      assembleBlock p k x.1 x.2 := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  unfold assembleBlock
  have h1 : Measurable fun z : BlockState p k × Matrix (BlockSite p k) (BlockSite p k) ℂ =>
      z.1.1 := measurable_fst.comp measurable_fst
  have h2 : Measurable fun z : BlockState p k × Matrix (BlockSite p k) (BlockSite p k) ℂ =>
      z.1.2 := measurable_snd.comp measurable_fst
  have h4 : Measurable fun z : BlockState p k × Matrix (BlockSite p k) (BlockSite p k) ℂ =>
      z.2 := measurable_snd
  split_ifs
  · exact Matrix.measurable_apply.comp h4
  · exact continuous_star.measurable.comp (Matrix.measurable_apply.comp h2)
  · exact Matrix.measurable_apply.comp h2
  · exact Matrix.measurable_apply.comp h1

/-- The exterior law of a pair splitting is a probability measure. -/
theorem isProbabilityMeasure_pairSplitting (model : p.GaussianRingModel) (i : ZMod p.n)
    {s : ℝ} {Pω : Measure (SplitState p i)} (hP : IsPairSplitting p i model s Pω) :
    IsProbabilityMeasure Pω :=
  isProbabilityMeasure_of_prod_map (ContractClauses.measurable_assemble p i) hP

/-- The exterior law of a one-block splitting is a probability measure. -/
theorem isProbabilityMeasure_blockSplitting (model : p.GaussianRingModel) (k : ZMod p.n)
    {Pω : Measure (BlockState p k)} (hP : IsBlockSplitting p k model Pω) :
    IsProbabilityMeasure Pω :=
  isProbabilityMeasure_of_prod_map (measurable_assembleBlock p k) hP

/-- For every one-block splitting law, `Pω`-a.e. exterior has `H_R` Hermitian. -/
theorem ae_blockSplit_isHermitian (model : p.GaussianRingModel) (k : ZMod p.n)
    {Pω : Measure (BlockState p k)} (hP : IsBlockSplitting p k model Pω) :
    ∀ᵐ ω ∂Pω, ω.1.IsHermitian := by
  have h0 := model.isPhysical.1
  rw [← hP, ae_map_iff (measurable_assembleBlock p k).aemeasurable
    BlockBand.Model.Construction.measurableSet_isHermitian] at h0
  filter_upwards [Measure.ae_ae_of_ae_prod h0] with ω hω
  obtain ⟨G, hG⟩ := hω.exists
  ext x y
  have h := hG.apply x.1 y.1
  simp only [assembleBlock, x.2, y.2, dite_false] at h
  simpa [Matrix.conjTranspose_apply] using h

theorem card_pairSite_eq (i : ZMod p.n) : Fintype.card (PairSite p i) = 2 * p.W := by
  rw [Fintype.card_congr (FixedOmega.pairEquiv p i), Fintype.card_fin]

theorem card_blockSite_eq (k : ZMod p.n) : Fintype.card (BlockSite p k) = p.W := by
  rw [Fintype.card_congr (blockEquiv p k), Fintype.card_fin]

theorem palmMass_reindex_finCongr {n m : ℕ} (h : n = m) (G : Matrix (Fin n) (Fin n) ℂ)
    (c E : ℝ) : palmMass (Matrix.reindex (finCongr h) (finCongr h) G) c E = palmMass G c E := by
  subst h; simp

/-- **Bridge along `card = 2W`**: for the arbitrary reindexing `σ` of
`IsPairRegular`, `Z(e) = palmMass (pairDeformation σ ω e) s e` at a Hermitian exterior.
Consumes `FreshEigenpairDensityContract` (through `pairNormalizer_eq_palmMass`).
-/
theorem pairNormalizer_toReal_eq (hD : FreshEigenpairDensityContract) (i : ZMod p.n)
    (σ : PairSite p i ≃ Fin (Fintype.card (PairSite p i)))
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (ω : SplitState p i) (hω : IsHermitianExterior p i ω) (e : ℝ) :
    (pairNormalizer p i U ω e).toReal = palmMass (pairDeformation p i σ ω e) (pairS p) e := by
  have hcard := card_pairSite_eq p i
  rw [pairNormalizer_eq_palmMass p i hD (σ.trans (finCongr hcard)) U hU ω hω e,
    ENNReal.toReal_ofReal (palmMass_nonneg _ _ _)]
  have hre : Matrix.reindex (σ.trans (finCongr hcard)) (σ.trans (finCongr hcard))
      (physicalCoareaF ω.1 ω.2.1 ω.2.2 e) =
      Matrix.reindex (finCongr hcard) (finCongr hcard) (pairDeformation p i σ ω e) := by
    ext a b; simp [pairDeformation, Matrix.reindex_apply]
  rw [hre, palmMass_reindex_finCongr]

/-- One-block bridge along `card = W`. -/
theorem blockNormalizer_toReal_eq (hD : FreshEigenpairDensityContract) (k : ZMod p.n)
    (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (hω : ω.1.IsHermitian) (e : ℝ) :
    (blockNormalizer p k U ω e).toReal = palmMass (blockDeformation p k σ ω e) p.c e := by
  have hcard := card_blockSite_eq p k
  rw [blockNormalizer_eq_palmMass p k hD (σ.trans (finCongr hcard)) U hU ω hω e,
    ENNReal.toReal_ofReal (palmMass_nonneg _ _ _)]
  have hre : Matrix.reindex (σ.trans (finCongr hcard)) (σ.trans (finCongr hcard))
      (blockF p k ω e) =
      Matrix.reindex (finCongr hcard) (finCongr hcard) (blockDeformation p k σ ω e) := by
    ext a b; simp [blockDeformation, Matrix.reindex_apply]
  rw [hre, palmMass_reindex_finCongr]

end Exterior

/-!
## 5. Energy bookkeeping
-/

section Energy

private theorem semicircleDensity_pos' {E : ℝ} (h1 : -2 < E) (h2 : E < 2) :
    0 < Parameters.semicircleDensity E := by
  unfold Parameters.semicircleDensity
  have h : 0 < 4 - E ^ 2 := by nlinarith
  exact div_pos (Real.sqrt_pos.2 h) (by positivity)

private theorem continuous_semicircleDensity : Continuous Parameters.semicircleDensity := by
  unfold Parameters.semicircleDensity
  fun_prop

/-- A bulk energy `E` lies in `bulkInterval κ` with room `κ`, and `ρ` is continuous at `E`. -/
private theorem energy_setup {E : ℝ} (h1 : -2 < E) (h2 : E < 2) {γ : ℝ} (hγ : 0 < γ) :
    ∃ κ δc : ℝ, 0 < κ ∧ 0 < δc ∧ (∀ e, |e - E| ≤ κ → e ∈ bulkInterval κ) ∧
      ∀ e, |e - E| < δc →
        |Parameters.semicircleDensity e - Parameters.semicircleDensity E| ≤ γ := by
  obtain ⟨δc, hδc, hδ⟩ := Metric.continuous_iff.1 continuous_semicircleDensity E γ hγ
  have hE : |E| < 2 := abs_lt.2 ⟨h1, h2⟩
  refine ⟨(2 - |E|) / 2, δc, by linarith, hδc, fun e he => ?_, fun e he => ?_⟩
  · have h3 := abs_le.1 he
    have h4 := neg_abs_le E
    have h5 := le_abs_self E
    unfold bulkInterval
    constructor <;> linarith [h3.1, h3.2]
  · have h := hδ e (by rwa [Real.dist_eq])
    rw [Real.dist_eq] at h
    exact h.le

private theorem ratio_good {z d ρE ρe γ₁ γ₂ : ℝ} (hd : 0 < d) (hρ : 0 < ρE)
    (h1 : |z / d - ρe| ≤ γ₁) (h2 : |ρe - ρE| ≤ γ₂) :
    |z / (d * ρE) - 1| ≤ (γ₁ + γ₂) / ρE := by
  have h : z / (d * ρE) - 1 = (z / d - ρE) / ρE := by field_simp
  rw [h, abs_div, abs_of_pos hρ]
  refine div_le_div_of_nonneg_right ?_ hρ.le
  calc |z / d - ρE| ≤ |z / d - ρe| + |ρe - ρE| := abs_sub_le _ _ _
    _ ≤ γ₁ + γ₂ := add_le_add h1 h2

private theorem ratio_all {z d ρE C : ℝ} (hd : 0 < d) (hρ : 0 < ρE) (hC : 0 ≤ C) (hz0 : 0 ≤ z)
    (hz : z ≤ C * d) : |z / (d * ρE) - 1| ≤ C / ρE + 1 := by
  have h1 : z / (d * ρE) ≤ C / ρE := by
    rw [div_le_div_iff₀ (by positivity) hρ]
    nlinarith
  have h0 : 0 ≤ z / (d * ρE) := by positivity
  have h2 : 0 ≤ C / ρE := by positivity
  rw [abs_le]; constructor <;> linarith

private theorem toReal_le_abs_mul {Z : ℝ≥0∞} {C d : ℝ} (hd : 0 ≤ d) (h : Z ≤ ENNReal.ofReal (C * d)) :
    Z.toReal ≤ |C| * d :=
  ENNReal.toReal_le_of_le_ofReal (by positivity)
    (h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self C) hd)))

/-- Width thresholds: `R < Wρm` and `M/W ≤ ε/2` for all large `W`. -/
private theorem eventually_W {R ρ m M ε : ℝ} (hρ : 0 < ρ) (hm : 0 < m) (hε : 0 < ε) :
    ∃ W₁ : ℕ, ∀ W : ℕ, W₁ ≤ W → R < W * ρ * m ∧ 0 < W ∧ M * (W : ℝ)⁻¹ ≤ ε / 2 := by
  refine ⟨⌈R / (ρ * m)⌉₊ + ⌈2 * M / ε⌉₊ + 1, fun W hW => ?_⟩
  have hW' : ((⌈R / (ρ * m)⌉₊ + ⌈2 * M / ε⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
  push_cast at hW'
  have ha := Nat.le_ceil (R / (ρ * m))
  have hb := Nat.le_ceil (2 * M / ε)
  have hc : (0 : ℝ) ≤ ⌈R / (ρ * m)⌉₊ := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ ⌈2 * M / ε⌉₊ := Nat.cast_nonneg _
  have hWpos : (0 : ℝ) < W := by linarith
  refine ⟨?_, by exact_mod_cast hWpos, ?_⟩
  · have h1 : R / (ρ * m) < W := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    linarith
  · have h1 : 2 * M / ε < W := by linarith
    rw [div_lt_iff₀ hε] at h1
    rw [← div_eq_mul_inv, div_le_iff₀ hWpos]
    linarith

end Energy

/-!
## 6. the normalizer theorem and its one-block version
-/

section Normalizer

/-- **The normalizer theorem, field `l1`**, from `ClocksCommonPort.PairRegularEventContract` (at
`D = 1`), `Critical.PointDensityContract`, `FreshEigenpairDensityContract` (bridge
`pairNormalizer_eq_palmMass` and `Z = Nρ_{F,c}`) and the type of `ExactPalmContract.upper`.
Measure: the comparison probability
`𝔭_W = w(u)du ⊗ Pω`; uniform as in `NormalizerContract`.
Proof: for `w(u) ≠ 0`, at the
deterministic energy `e = e(u)` (in the bulk, `|e - E| = O(R/N)`), on the regular event
`|Z(e)/𝒩 - ρ(e)| ≤ ε_𝒩 + η/π`; off it `Z/𝒩 ≤ C`, and its outer probability is `≤ W⁻¹`;
then integrate against `w(u)du`.
-/
theorem normalizer_l1_of (hReg : PairRegularEventContract) (hPD : PointDensityContract)
    (hD : FreshEigenpairDensityContract)
    (hU : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∃ C : ℝ, ∀ (p : Parameters), p.b = b →
      ∀ (i : ZMod p.n) (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ),
      IsPairFrame p i U → ∀ ω : SplitState p i, IsHermitianExterior p i ω → ∀ e : ℝ,
        pairNormalizer p i U ω e ≤ ENNReal.ofReal (C * (2 * p.W))) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ (T : ℝ) (w : ℝ → ℝ),
    IsWindow w → ∀ ε : ℝ, 0 < ε → ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W →
      (p.n : ℝ) ≤ T * p.W → ∀ (model : p.GaussianRingModel) (i : ZMod p.n)
      (Pω : Measure (SplitState p i)), IsPairSplitting p i model (pairS p) Pω →
      ∀ U, IsPairFrame p i U →
        ∫⁻ x, ENNReal.ofReal |(pairNormalizer p i U x.2 (microEnergy p E x.1)).toReal /
            (2 * p.W * Parameters.semicircleDensity E) - 1| ∂priorWindowMeasure Pω w ≤
          ENNReal.ofReal ε := by
  intro b hb hb2 E hE1 hE2 T w hw ε hε
  have hρ : 0 < Parameters.semicircleDensity E := semicircleDensity_pos' hE1 hE2
  obtain ⟨κ, δc, hκ, hδc, hbulk, hcont⟩ :=
    energy_setup hE1 hE2 (γ := Parameters.semicircleDensity E * ε / 6) (by positivity)
  obtain ⟨R, hR⟩ := window_bound hw
  obtain ⟨r₀, s₀, v₀, hFC, hDreg⟩ := hReg b hb hb2 κ T hκ
  obtain ⟨A, hA⟩ := hDreg 1 one_pos
  obtain ⟨εf, hεf, hpd⟩ := palmMass_pointDensity (A := A) hPD hD hFC
  obtain ⟨C, hC⟩ := hU b hb hb2
  have hM0 : 0 ≤ |C| / Parameters.semicircleDensity E + 1 := by positivity
  have hη : 0 < Real.pi * Parameters.semicircleDensity E * ε / 6 := by
    have := Real.pi_pos; positivity
  obtain ⟨Wr, hWr⟩ := hA _ hη
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hεf (Parameters.semicircleDensity E * ε / 6)
    (by positivity)
  obtain ⟨W₂, hW₂⟩ := eventually_W (R := R) (M := |C| / Parameters.semicircleDensity E + 1)
    hρ (lt_min hδc hκ) hε
  refine ⟨max Wr (max N₁ W₂), fun p hpb hW hn model i Pω hP U hUf => ?_⟩
  have hWr' : Wr ≤ p.W := le_trans (le_max_left _ _) hW
  have hN₁' : N₁ ≤ p.W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW₂' : W₂ ≤ p.W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  obtain ⟨hRW, -, hMW⟩ := hW₂ p.W hW₂'
  have := isProbabilityMeasure_pairSplitting p model i hP
  have hcs : pairS p = min b (1 - 2 * b) := by simp [pairS, Parameters.c, hpb]
  have hWpos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hNW : (p.W : ℝ) ≤ p.N := by
    unfold Parameters.N; push_cast
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
    nlinarith
  have hcardR : ((Fintype.card (PairSite p i) : ℕ) : ℝ) = 2 * p.W := by
    rw [card_pairSite_eq]; push_cast; ring
  have hcardpos : 0 < Fintype.card (PairSite p i) := by
    rw [card_pairSite_eq]; have := p.W_pos; omega
  have hεN : |εf (Fintype.card (PairSite p i))| < Parameters.semicircleDensity E * ε / 6 := by
    have h := hN₁ (Fintype.card (PairSite p i)) (by rw [card_pairSite_eq]; omega)
    rwa [Real.dist_eq, sub_zero] at h
  refine l1_of_pointwise Pω hw _ ε fun u hu => ?_
  have hNρ : 0 < (p.N : ℝ) * Parameters.semicircleDensity E := by
    have : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
    positivity
  have heE : |microEnergy p E u - E| < min δc κ := by
    have h : microEnergy p E u - E = u / ((p.N : ℝ) * Parameters.semicircleDensity E) := by
      simp only [microEnergy]; ring
    rw [h, abs_div, abs_of_pos hNρ, div_lt_iff₀ hNρ]
    calc |u| ≤ R := hR u hu
      _ < p.W * Parameters.semicircleDensity E * min δc κ := hRW
      _ ≤ p.N * Parameters.semicircleDensity E * min δc κ := by gcongr
      _ = _ := by ring
  have he : microEnergy p E u ∈ bulkInterval κ := hbulk _ (le_trans heE.le (min_le_right _ _))
  have hρe := hcont _ (lt_of_lt_of_le heE (min_le_left _ _))
  have hbad := hWr p hpb hWr' hn model i Pω hP (Fintype.equivFin (PairSite p i)) _ he
  have hfin := lintegral_le_good_bad Pω
    (fun ω => ENNReal.ofReal |(pairNormalizer p i U ω (microEnergy p E u)).toReal /
      (2 * p.W * Parameters.semicircleDensity E) - 1|)
    (IsHermitianExterior p i)
    (fun ω => IsPairRegular p i (Fintype.equivFin (PairSite p i)) A r₀ s₀ v₀
      (Real.pi * Parameters.semicircleDensity E * ε / 6) (microEnergy p E u) ω)
    (ae_split_isHermitian p i model (pairS p) Pω hP) (δ := ε / 2)
    (M := |C| / Parameters.semicircleDensity E + 1) ?_ ?_ hbad
  · refine hfin.trans ?_
    rw [Real.rpow_neg_one, ← ENNReal.ofReal_mul hM0,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · intro ω hω hreg
    refine ENNReal.ofReal_le_ofReal ?_
    rw [pairNormalizer_toReal_eq p hD i (Fintype.equivFin (PairSite p i)) U hUf ω hω]
    obtain ⟨hcls, hm⟩ := hreg
    rw [hcs] at hcls hm ⊢
    have h1 := hpd _ hcardpos _ _ hcls
    have h2 := palmMass_near_semicircle h1 hm
    rw [hcardR] at h2
    refine (ratio_good (by positivity) hρ h2 hρe).trans ?_
    rw [div_le_iff₀ hρ]
    have h3 : Real.pi * Parameters.semicircleDensity E * ε / 6 / Real.pi =
        Parameters.semicircleDensity E * ε / 6 := by
      have := Real.pi_pos; field_simp
    have h4 := le_abs_self (εf (Fintype.card (PairSite p i)))
    rw [h3]
    linarith
  · intro ω hω
    refine ENNReal.ofReal_le_ofReal ?_
    have h := toReal_le_abs_mul (by positivity) (hC p hpb i U hUf ω hω (microEnergy p E u))
    exact ratio_all (by positivity) hρ (abs_nonneg C) ENNReal.toReal_nonneg h

/-- **, field `tv`**.
From the
`l1` field by the change of variables `u = Nρ(E)(e - E)` (`n/(2Nρ(E)) = 1/(2Wρ(E))`) and
`|∫F d𝔪_W - ∫F d𝔭_W| ≤ ∫|Z/(𝒩ρ(E)) - 1| d𝔭_W` for measurable `|F| ≤ 1` (`tv_of_l1`; joint
measurability `measurable_pairNormalizer_joint`, a.s. bound `hU` on Hermitian exteriors).
Consumes the same contracts as `normalizer_l1_of`.
-/
theorem normalizer_tv_of (hReg : PairRegularEventContract) (hPD : PointDensityContract)
    (hD : FreshEigenpairDensityContract)
    (hU : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∃ C : ℝ, ∀ (p : Parameters), p.b = b →
      ∀ (i : ZMod p.n) (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ),
      IsPairFrame p i U → ∀ ω : SplitState p i, IsHermitianExterior p i ω → ∀ e : ℝ,
        pairNormalizer p i U ω e ≤ ENNReal.ofReal (C * (2 * p.W))) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ (T : ℝ) (w : ℝ → ℝ),
    IsWindow w → ∀ ε : ℝ, 0 < ε → ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W →
      (p.n : ℝ) ≤ T * p.W → ∀ (model : p.GaussianRingModel) (i : ZMod p.n)
      (Pω : Measure (SplitState p i)), IsPairSplitting p i model (pairS p) Pω →
      ∀ U, IsPairFrame p i U → ∀ F : ℝ × SplitState p i → ℝ, Measurable F →
      (∀ x, |F x| ≤ 1) →
        |(∫ x, F (microCoord p E x.1, x.2) ∂pairWindowMeasure p i U Pω E w) -
            ∫ x, F x ∂priorWindowMeasure Pω w| ≤ ε := by
  intro b hb hb2 E hE1 hE2 T w hw ε hε
  obtain ⟨W₀, hW₀⟩ := normalizer_l1_of hReg hPD hD hU b hb hb2 E hE1 hE2 T w hw ε hε
  obtain ⟨C, hC⟩ := hU b hb hb2
  refine ⟨W₀, fun p hpb hW hn model i Pω hP U hUf F hF hF1 => ?_⟩
  have := isProbabilityMeasure_pairSplitting p model i hP
  have hρ := semicircleDensity_pos' hE1 hE2
  have hl1 := hW₀ p hpb hW hn model i Pω hP U hUf
  have hZB : ∀ᵐ ω ∂Pω, ∀ e, pairNormalizer p i U ω e ≤ ENNReal.ofReal (C * (2 * p.W)) := by
    filter_upwards [ae_split_isHermitian p i model (pairS p) Pω hP] with ω hω
    exact hC p hpb i U hUf ω hω
  have hNpos : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hWpos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hpref : (p.n : ℝ) / 2 =
      (p.N : ℝ) * Parameters.semicircleDensity E / (2 * p.W * Parameters.semicircleDensity E) := by
    rw [show ((p.N : ℕ) : ℝ) = p.n * p.W by unfold Parameters.N; push_cast; ring]
    field_simp
  exact tv_of_l1 Pω hw (E := E) (lam := (p.N : ℝ) * Parameters.semicircleDensity E)
    (pref := (p.n : ℝ) / 2) (K := 2 * p.W * Parameters.semicircleDensity E)
    (B := C * (2 * p.W)) (by positivity) (by positivity) hpref hε.le
    (fun ω e => pairNormalizer p i U ω e) (measurable_pairNormalizer_joint p i U hUf.1) hZB hl1
    F hF hF1

/-- **`NormalizerContract`**, from `PairRegularEventContract`, `PointDensityContract`,
`FreshEigenpairDensityContract` and the exact type of `ExactPalmContract.upper` (`hU`).
-/
theorem normalizer_of (hReg : PairRegularEventContract) (hPD : PointDensityContract)
    (hD : FreshEigenpairDensityContract)
    (hU : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∃ C : ℝ, ∀ (p : Parameters), p.b = b →
      ∀ (i : ZMod p.n) (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ),
      IsPairFrame p i U → ∀ ω : SplitState p i, IsHermitianExterior p i ω → ∀ e : ℝ,
        pairNormalizer p i U ω e ≤ ENNReal.ofReal (C * (2 * p.W))) :
    NormalizerContract :=
  ⟨normalizer_l1_of hReg hPD hD hU, normalizer_tv_of hReg hPD hD hU⟩

/-- Type check: the `upper` hypothesis of `normalizer_of` is exactly `ExactPalmContract.upper`. -/
theorem normalizer_of_exactPalm (hReg : PairRegularEventContract) (hPD : PointDensityContract)
    (hD : FreshEigenpairDensityContract) (hE : ExactPalmContract) : NormalizerContract :=
  normalizer_of hReg hPD hD hE.upper

/-- As `normalizer_l1_of` with the one-block data: fresh
block `GUE_W(c/W)`, `N_fresh = W`, variance `c = 1 - 2b`, `F(e) = blockF`, regular event
`IsBlockRegular` (`BlockRegularEventContract`, at `D = 1`), upper bound `hU` of type
`OneBlockPalmContract.upper`, bridge `blockNormalizer_eq_palmMass`.
-/
theorem oneBlockNormalizer_l1_of (hReg : BlockRegularEventContract)
    (hPD : PointDensityContract) (hD : FreshEigenpairDensityContract)
    (hU : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∃ C : ℝ, ∀ (p : Parameters), p.b = b →
      ∀ (k : ZMod p.n) (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ),
      IsBlockFrame p k U → ∀ ω : BlockState p k, ω.1.IsHermitian → ∀ e : ℝ,
        blockNormalizer p k U ω e ≤ ENNReal.ofReal (C * p.W)) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ (T : ℝ) (w : ℝ → ℝ),
    IsWindow w → ∀ ε : ℝ, 0 < ε → ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W →
      (p.n : ℝ) ≤ T * p.W → ∀ (model : p.GaussianRingModel) (k : ZMod p.n)
      (Pω : Measure (BlockState p k)), IsBlockSplitting p k model Pω →
      ∀ U, IsBlockFrame p k U →
        ∫⁻ x, ENNReal.ofReal |(blockNormalizer p k U x.2 (microEnergy p E x.1)).toReal /
            (p.W * Parameters.semicircleDensity E) - 1| ∂priorWindowMeasure Pω w ≤
          ENNReal.ofReal ε := by
  intro b hb hb2 E hE1 hE2 T w hw ε hε
  have hρ : 0 < Parameters.semicircleDensity E := semicircleDensity_pos' hE1 hE2
  obtain ⟨κ, δc, hκ, hδc, hbulk, hcont⟩ :=
    energy_setup hE1 hE2 (γ := Parameters.semicircleDensity E * ε / 6) (by positivity)
  obtain ⟨R, hR⟩ := window_bound hw
  obtain ⟨r₀, s₀, v₀, hFC, hDreg⟩ := hReg b hb hb2 κ T hκ
  obtain ⟨A, hA⟩ := hDreg 1 one_pos
  obtain ⟨εf, hεf, hpd⟩ := palmMass_pointDensity (A := A) hPD hD hFC
  obtain ⟨C, hC⟩ := hU b hb hb2
  have hM0 : 0 ≤ |C| / Parameters.semicircleDensity E + 1 := by positivity
  have hη : 0 < Real.pi * Parameters.semicircleDensity E * ε / 6 := by
    have := Real.pi_pos; positivity
  obtain ⟨Wr, hWr⟩ := hA _ hη
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hεf (Parameters.semicircleDensity E * ε / 6)
    (by positivity)
  obtain ⟨W₂, hW₂⟩ := eventually_W (R := R) (M := |C| / Parameters.semicircleDensity E + 1)
    hρ (lt_min hδc hκ) hε
  refine ⟨max Wr (max N₁ W₂), fun p hpb hW hn model k Pω hP U hUf => ?_⟩
  have hWr' : Wr ≤ p.W := le_trans (le_max_left _ _) hW
  have hN₁' : N₁ ≤ p.W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW₂' : W₂ ≤ p.W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  obtain ⟨hRW, -, hMW⟩ := hW₂ p.W hW₂'
  have := isProbabilityMeasure_blockSplitting p model k hP
  have hcs : p.c = 1 - 2 * b := by simp [Parameters.c, hpb]
  have hWpos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hNW : (p.W : ℝ) ≤ p.N := by
    unfold Parameters.N; push_cast
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
    nlinarith
  have hcardR : ((Fintype.card (BlockSite p k) : ℕ) : ℝ) = p.W := by
    rw [card_blockSite_eq]
  have hcardpos : 0 < Fintype.card (BlockSite p k) := by
    rw [card_blockSite_eq]; exact p.W_pos
  have hεN : |εf (Fintype.card (BlockSite p k))| < Parameters.semicircleDensity E * ε / 6 := by
    have h := hN₁ (Fintype.card (BlockSite p k)) (by rw [card_blockSite_eq]; omega)
    rwa [Real.dist_eq, sub_zero] at h
  refine l1_of_pointwise Pω hw _ ε fun u hu => ?_
  have hNρ : 0 < (p.N : ℝ) * Parameters.semicircleDensity E := by
    have : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
    positivity
  have heE : |microEnergy p E u - E| < min δc κ := by
    have h : microEnergy p E u - E = u / ((p.N : ℝ) * Parameters.semicircleDensity E) := by
      simp only [microEnergy]; ring
    rw [h, abs_div, abs_of_pos hNρ, div_lt_iff₀ hNρ]
    calc |u| ≤ R := hR u hu
      _ < p.W * Parameters.semicircleDensity E * min δc κ := hRW
      _ ≤ p.N * Parameters.semicircleDensity E * min δc κ := by gcongr
      _ = _ := by ring
  have he : microEnergy p E u ∈ bulkInterval κ := hbulk _ (le_trans heE.le (min_le_right _ _))
  have hρe := hcont _ (lt_of_lt_of_le heE (min_le_left _ _))
  have hbad := hWr p hpb hWr' hn model k Pω hP (Fintype.equivFin (BlockSite p k)) _ he
  have hfin := lintegral_le_good_bad Pω
    (fun ω => ENNReal.ofReal |(blockNormalizer p k U ω (microEnergy p E u)).toReal /
      (p.W * Parameters.semicircleDensity E) - 1|)
    (fun ω => ω.1.IsHermitian)
    (fun ω => IsBlockRegular p k (Fintype.equivFin (BlockSite p k)) A r₀ s₀ v₀
      (Real.pi * Parameters.semicircleDensity E * ε / 6) (microEnergy p E u) ω)
    (ae_blockSplit_isHermitian p model k hP) (δ := ε / 2)
    (M := |C| / Parameters.semicircleDensity E + 1) ?_ ?_ hbad
  · refine hfin.trans ?_
    rw [Real.rpow_neg_one, ← ENNReal.ofReal_mul hM0,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · intro ω hω hreg
    refine ENNReal.ofReal_le_ofReal ?_
    rw [blockNormalizer_toReal_eq p hD k (Fintype.equivFin (BlockSite p k)) U hUf ω hω]
    obtain ⟨hcls, hm⟩ := hreg
    rw [hcs] at hcls hm ⊢
    have h1 := hpd _ hcardpos _ _ hcls
    have h2 := palmMass_near_semicircle h1 hm
    rw [hcardR] at h2
    refine (ratio_good (by positivity) hρ h2 hρe).trans ?_
    rw [div_le_iff₀ hρ]
    have h3 : Real.pi * Parameters.semicircleDensity E * ε / 6 / Real.pi =
        Parameters.semicircleDensity E * ε / 6 := by
      have := Real.pi_pos; field_simp
    have h4 := le_abs_self (εf (Fintype.card (BlockSite p k)))
    rw [h3]
    linarith
  · intro ω hω
    refine ENNReal.ofReal_le_ofReal ?_
    have h := toReal_le_abs_mul (by positivity) (hC p hpb k U hUf ω hω (microEnergy p E u))
    exact ratio_all (by positivity) hρ (abs_nonneg C) ENNReal.toReal_nonneg h

/-- **One-block normalizer, field `tv`**: from `oneBlockNormalizer_l1_of` by the change of
variables (`n/(Nρ(E)) = 1/(Wρ(E))`).
-/
theorem oneBlockNormalizer_tv_of (hReg : BlockRegularEventContract)
    (hPD : PointDensityContract) (hD : FreshEigenpairDensityContract)
    (hU : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∃ C : ℝ, ∀ (p : Parameters), p.b = b →
      ∀ (k : ZMod p.n) (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ),
      IsBlockFrame p k U → ∀ ω : BlockState p k, ω.1.IsHermitian → ∀ e : ℝ,
        blockNormalizer p k U ω e ≤ ENNReal.ofReal (C * p.W)) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ (T : ℝ) (w : ℝ → ℝ),
    IsWindow w → ∀ ε : ℝ, 0 < ε → ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W →
      (p.n : ℝ) ≤ T * p.W → ∀ (model : p.GaussianRingModel) (k : ZMod p.n)
      (Pω : Measure (BlockState p k)), IsBlockSplitting p k model Pω →
      ∀ U, IsBlockFrame p k U → ∀ F : ℝ × BlockState p k → ℝ, Measurable F →
      (∀ x, |F x| ≤ 1) →
        |(∫ x, F (microCoord p E x.1, x.2) ∂blockWindowMeasure p k U Pω E w) -
            ∫ x, F x ∂priorWindowMeasure Pω w| ≤ ε := by
  intro b hb hb2 E hE1 hE2 T w hw ε hε
  obtain ⟨W₀, hW₀⟩ := oneBlockNormalizer_l1_of hReg hPD hD hU b hb hb2 E hE1 hE2 T w hw ε hε
  obtain ⟨C, hC⟩ := hU b hb hb2
  refine ⟨W₀, fun p hpb hW hn model k Pω hP U hUf F hF hF1 => ?_⟩
  have := isProbabilityMeasure_blockSplitting p model k hP
  have hρ := semicircleDensity_pos' hE1 hE2
  have hl1 := hW₀ p hpb hW hn model k Pω hP U hUf
  have hZB : ∀ᵐ ω ∂Pω, ∀ e, blockNormalizer p k U ω e ≤ ENNReal.ofReal (C * p.W) := by
    filter_upwards [ae_blockSplit_isHermitian p model k hP] with ω hω
    exact hC p hpb k U hUf ω hω
  have hNpos : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hWpos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hpref : (p.n : ℝ) =
      (p.N : ℝ) * Parameters.semicircleDensity E / (p.W * Parameters.semicircleDensity E) := by
    rw [show ((p.N : ℕ) : ℝ) = p.n * p.W by unfold Parameters.N; push_cast; ring]
    field_simp
  exact tv_of_l1 Pω hw (E := E) (lam := (p.N : ℝ) * Parameters.semicircleDensity E)
    (pref := (p.n : ℝ)) (K := p.W * Parameters.semicircleDensity E)
    (B := C * p.W) (by positivity) (by positivity) hpref hε.le
    (fun ω e => blockNormalizer p k U ω e) (measurable_blockNormalizer_joint p k U hUf.1) hZB
    hl1 F hF hF1

/-- **`OneBlockNormalizerContract`** (both fields), from `BlockRegularEventContract`,
`PointDensityContract`, `FreshEigenpairDensityContract` and the exact type of
`OneBlockPalmContract.upper` (`hU`).
-/
theorem oneBlockNormalizer_of (hReg : BlockRegularEventContract) (hPD : PointDensityContract)
    (hD : FreshEigenpairDensityContract)
    (hU : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∃ C : ℝ, ∀ (p : Parameters), p.b = b →
      ∀ (k : ZMod p.n) (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ),
      IsBlockFrame p k U → ∀ ω : BlockState p k, ω.1.IsHermitian → ∀ e : ℝ,
        blockNormalizer p k U ω e ≤ ENNReal.ofReal (C * p.W)) :
    OneBlockNormalizerContract :=
  ⟨oneBlockNormalizer_l1_of hReg hPD hD hU, oneBlockNormalizer_tv_of hReg hPD hD hU⟩

/-- Type check: the `upper` hypothesis of `oneBlockNormalizer_of` is exactly
`OneBlockPalmContract.upper`. -/
theorem oneBlockNormalizer_of_oneBlockPalm (hReg : BlockRegularEventContract)
    (hPD : PointDensityContract) (hD : FreshEigenpairDensityContract)
    (hE : OneBlockPalmContract) : OneBlockNormalizerContract :=
  oneBlockNormalizer_of hReg hPD hD hE.upper

end Normalizer

end BlockBand.Endpoints.Normalization
