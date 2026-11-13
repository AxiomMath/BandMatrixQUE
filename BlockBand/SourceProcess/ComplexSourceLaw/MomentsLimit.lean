module

public import BlockBand.SourceProcess.ComplexSourceLaw.Moments

/-!
# The `moments` field of the complex source law

* finite width (`lintegral_sourceDataMoment_le`): `E Σ|y_{rij}|^p ≤ B(p, η, C, m)` for `W ≥ W₀`
  and every final time `T ≤ T₀` (path lengths `⌊WT⌋ ≤ max(T₀, 0) W`; bulk margin
  `κ = min(2+E, 2-E)`);
* limit (`lintegral_le_of_isComplexSourceLimit`): the moment is lower semicontinuous under the
  complex source limit, through the bounded continuous truncations `min(f, M)`;
* `moments_of_raw`: hence every complex source limit `ν` has `∫ Σ|y_{rij}|^p dν ≤ C`, uniformly in
  `T ≤ T₀`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionLaws

theorem measurable_sourceDataMoment {np : ℕ} (p : ℝ) :
    Measurable (sourceDataMoment (np := np) p) := by
  unfold sourceDataMoment
  exact Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply r).eval_matrix (i := i) (j := j)).norm.pow_const p

theorem continuous_sourceDataMoment {np : ℕ} {p : ℝ} (hp : 0 < p) :
    Continuous (sourceDataMoment (np := np) p) := by
  unfold sourceDataMoment
  exact continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ =>
      (((continuous_apply r).matrix_elem i j).norm.rpow_const fun _ => Or.inr hp.le)

theorem sourceDataMoment_nonneg {np : ℕ} (p : ℝ) (y : SourceData np) :
    0 ≤ sourceDataMoment p y := by
  unfold sourceDataMoment; positivity

/-- The truncation `min(f, M)` as a bounded continuous test. -/
def truncMoment {np : ℕ} {p : ℝ} (hp : 0 < p) (M : ℕ) :
    BoundedContinuousFunction (SourceData np) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => min (sourceDataMoment p y) M, (continuous_sourceDataMoment hp).min continuous_const⟩
    M fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 := sourceDataMoment_nonneg p x
      have h2 := sourceDataMoment_nonneg p y
      rw [abs_le]
      constructor <;> linarith [min_le_right (sourceDataMoment p x) (M : ℝ),
        min_le_right (sourceDataMoment p y) (M : ℝ), le_min h1 (Nat.cast_nonneg M),
        le_min h2 (Nat.cast_nonneg M)]

theorem truncMoment_apply {np : ℕ} {p : ℝ} (hp : 0 < p) (M : ℕ) (y : SourceData np) :
    truncMoment hp M y = min (sourceDataMoment p y) M := rfl

theorem measurable_truncMoment {np : ℕ} {p : ℝ} (hp : 0 < p) (M : ℕ) :
    Measurable (truncMoment (np := np) hp M) := by
  have : (truncMoment (np := np) hp M : SourceData np → ℝ) =
      fun y => min (sourceDataMoment p y) M := rfl
  rw [this]
  exact (measurable_sourceDataMoment p).min measurable_const

/-- `ofReal ∫ g ≤ ∫⁻ ofReal f` for `0 ≤ g ≤ f`, `g` measurable and bounded. -/
theorem integral_trunc_le {α : Type*} [MeasurableSpace α] (ρ : Measure α) [IsProbabilityMeasure ρ]
    {np : ℕ} {p : ℝ} (hp : 0 < p) (M : ℕ) {X : α → SourceData np} (hX : Measurable X) :
    ENNReal.ofReal (∫ a, truncMoment hp M (X a) ∂ρ) ≤
      ∫⁻ a, ENNReal.ofReal (sourceDataMoment p (X a)) ∂ρ := by
  have hm := (measurable_truncMoment (np := np) hp M).comp hX
  have hint : Integrable (fun a => truncMoment hp M (X a)) ρ :=
    Integrable.of_bound hm.aestronglyMeasurable M (ae_of_all _ fun a => by
      rw [truncMoment_apply, Real.norm_eq_abs,
        abs_of_nonneg (le_min (sourceDataMoment_nonneg p _) (Nat.cast_nonneg M))]
      exact min_le_right _ _)
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun a =>
    le_min (sourceDataMoment_nonneg p _) (Nat.cast_nonneg M))]
  exact lintegral_mono fun a => ENNReal.ofReal_le_ofReal (min_le_left _ _)

/-- **Lower semicontinuity of the moment under the complex source limit.** -/
theorem lintegral_le_of_isComplexSourceLimit {b E T : ℝ} {np : ℕ} {τ m : Fin np → ℝ}
    {ν : Measure (SourceData np)} (hν : IsComplexSourceLimit b E T τ m ν) {p : ℝ} (hp : 0 < p)
    {B : ENNReal} (hB : B ≠ ⊤)
    (hfin : ∀ᶠ W : ℕ in atTop, ∫⁻ x, ENNReal.ofReal (sourceDataMoment p
      (complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m x)) ∂probedPathLaw W np b ≤ B) :
    ∫⁻ y, ENNReal.ofReal (sourceDataMoment p y) ∂ν ≤ B := by
  have : IsProbabilityMeasure ν := hν.1
  have hM : ∀ M : ℕ, ∫ y, truncMoment hp M y ∂ν ≤ B.toReal := by
    intro M
    refine le_of_tendsto (hν.2 (truncMoment hp M)) ?_
    filter_upwards [hfin] with W hW
    have h := (integral_trunc_le (probedPathLaw W np b) hp M
      (measurable_complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m)).trans hW
    exact (ENNReal.ofReal_le_iff_le_toReal hB).1 h
  have hpt : ∀ y : SourceData np, ENNReal.ofReal (sourceDataMoment p y) =
      ⨆ M : ℕ, ENNReal.ofReal (truncMoment hp M y) := by
    intro y
    refine le_antisymm ?_ (iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _))
    refine le_iSup_of_le ⌈sourceDataMoment p y⌉₊ (le_of_eq ?_)
    rw [truncMoment_apply, min_eq_left (Nat.le_ceil _)]
  have hmono : Monotone fun (M : ℕ) (y : SourceData np) => ENNReal.ofReal (truncMoment hp M y) :=
    fun M M' hMM' y => ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.2 hMM'))
  rw [lintegral_congr fun y => hpt y,
    lintegral_iSup (fun M => (measurable_truncMoment hp M).ennreal_ofReal) hmono]
  refine iSup_le fun M => ?_
  have hint : Integrable (truncMoment (np := np) hp M) ν :=
    Integrable.of_bound (measurable_truncMoment hp M).aestronglyMeasurable M
      (ae_of_all _ fun y => by
        rw [truncMoment_apply, Real.norm_eq_abs,
          abs_of_nonneg (le_min (sourceDataMoment_nonneg p _) (Nat.cast_nonneg M))]
        exact min_le_right _ _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y =>
    le_min (sourceDataMoment_nonneg p _) (Nat.cast_nonneg M))]
  exact (ENNReal.ofReal_le_ofReal (hM M)).trans (ENNReal.ofReal_toReal hB).le

/-- `⌊WT⌋ ≤ max(T₀, 0) W` for `T ≤ T₀`. -/
theorem floor_le_max_mul {W : ℕ} {T T₀ : ℝ} (hT : T ≤ T₀) :
    ((⌊(W : ℝ) * T⌋₊ : ℕ) : ℝ) ≤ max T₀ 0 * W := by
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  by_cases h : 0 ≤ (W : ℝ) * T
  · refine (Nat.floor_le h).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hT.trans (le_max_left _ _)) hW
  · rw [Nat.floor_of_nonpos (le_of_not_ge h), Nat.cast_zero]
    exact mul_nonneg (le_max_right _ _) hW

/-- **The `ComplexSourceLawContract.moments`** from `RawTagMoments`. -/
theorem moments_of_raw (hR : RawTagMoments) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (np : ℕ) (τ m : Fin np → ℝ), Function.Injective τ → (∀ j, 0 < τ j) → (∀ j, 0 ≤ m j) →
    ∀ p : ℝ, 1 ≤ p → ∀ T₀ : ℝ, ∃ C : ℝ, ∀ T : ℝ, (∀ j, τ j < T) → T ≤ T₀ →
      ∀ ν : Measure (SourceData np), IsComplexSourceLimit b E T τ m ν →
        ∫⁻ y, ENNReal.ofReal (sourceDataMoment p y) ∂ν ≤ ENNReal.ofReal C := by
  intro b hb0 hb1 E hE0 hE1 np τ m _ _ hm p hp T₀
  set κ := min (2 + E) (2 - E)
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hEκ : E ∈ bulkInterval κ :=
    ⟨by linarith [min_le_left (2 + E) (2 - E)], by linarith [min_le_right (2 + E) (2 - E)]⟩
  obtain ⟨C, W₀, hC⟩ := hR b hb0 hb1 κ hκ (max T₀ 0) p hp
  have hη := Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE0 hE1
  refine ⟨(momentBound (etaZ b E) p C m).toReal, fun T _ hT ν hν => ?_⟩
  rw [ENNReal.ofReal_toReal (momentBound_ne_top _ _ _ _)]
  refine lintegral_le_of_isComplexSourceLimit hν (by linarith) (momentBound_ne_top _ _ _ _) ?_
  filter_upwards [eventually_ge_atTop W₀] with W hW
  exact lintegral_sourceDataMoment_le b E hη _ τ m hm hp
    (hC W hW E hEκ _ (floor_le_max_mul hT))

end BlockBand.SourceProcess.ComplexSourceLaw
