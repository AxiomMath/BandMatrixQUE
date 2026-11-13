module

public import BlockBand.Endpoints.Sine.MicroscopicTagAssemblyWindow

/-!
# The microscopic tag comparison under the prior window measure

This file passes from the energy window to the prior window measure
(`mts_window_to_prior`, through `OneBlockNormalizerContract.tv`), and under the prior from the
Palm tag test to the Gaussian tag test of covariance `Γ₀` (`mts_prior_palm_gauss`, through
`UniformClockTagsPalmContract`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile
open scoped ENNReal NNReal ComplexOrder BoundedContinuousFunction

/-!
## Palm and Gaussian tag tests: bounds and linearity
-/

section Fresh

variable {N : ℕ}

theorem mts_integrable_palmWeight (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N) :
    Integrable (fun A0 => palmWeight F c₀ E ℓ A0) (freshTracelessLaw N c₀) := by
  have := mts_isProbabilityMeasure_freshTracelessLaw N c₀
  exact Integrable.of_bound (mts_measurable_palmWeight F c₀ E ℓ).aestronglyMeasurable
    (Real.sqrt (2 * Real.pi * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N))⁻¹
    (ae_of_all _ fun A0 => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mts_palmWeight_nonneg F c₀ E ℓ A0)]
      exact BlockBand.Palm.scalarWeight_le_prefactor _ _ _ _)

theorem mts_abs_palmExpect_le (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ)
    {φ : (Fin N → ℂ) → ℝ} {C : ℝ} (hC : 0 ≤ C) (hφ : ∀ v, |φ v| ≤ C) :
    |palmExpect F c₀ E φ| ≤ C := by
  unfold palmExpect
  rw [abs_div, abs_of_nonneg (mts_palmMass_nonneg F c₀ E)]
  rcases (mts_palmMass_nonneg F c₀ E).lt_or_eq with hZ | hZ
  · rw [div_le_iff₀ hZ]
    calc _ ≤ ∑ ℓ : Fin N, |∫ A0, palmWeight F c₀ E ℓ A0 * φ (freshEigenvector (F + A0) ℓ)
          ∂freshTracelessLaw N c₀| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ℓ : Fin N, ∫ A0, C * palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀ :=
          Finset.sum_le_sum fun ℓ _ => abs_integral_le_integral_abs.trans
            (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
              ((mts_integrable_palmWeight F c₀ E ℓ).const_mul C) (ae_of_all _ fun A0 => by
                simp only
                rw [abs_mul, abs_of_nonneg (mts_palmWeight_nonneg F c₀ E ℓ A0), mul_comm]
                exact mul_le_mul_of_nonneg_right (hφ _) (mts_palmWeight_nonneg F c₀ E ℓ A0)))
      _ = C * palmMass F c₀ E := by
          unfold palmMass
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ℓ _ => integral_const_mul _ _
  · rw [← hZ, div_zero]; exact hC

theorem mts_palmExpect_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ)
    {φ : (Fin N → ℂ) → ℝ} (hφ : ∀ v, 0 ≤ φ v) : 0 ≤ palmExpect F c₀ E φ := by
  unfold palmExpect
  exact div_nonneg (Finset.sum_nonneg fun ℓ _ => integral_nonneg fun A0 =>
    mul_nonneg (mts_palmWeight_nonneg F c₀ E ℓ A0) (hφ _)) (mts_palmMass_nonneg F c₀ E)

theorem mts_measurable_ratioTag {ι : Type*} [Fintype ι] (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    (C D : Matrix ι ι ℂ) : Measurable (fun v : ι → ℂ => Φ (ratioHalfLine C D (fun _ => 0) v)) :=
  Φ.continuous.measurable.comp (mts_measurable_ratioHalfLine C D)

/-- The Palm expectation of the averaged tag test is the average of the Palm tag expectations. -/
theorem mts_palmExpect_tagTest (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (q : ℕ)
    (Dt : Fin q → Matrix (Fin N) (Fin N) ℂ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) :
    palmExpect F c₀ E (mts_tagTest q Dt Φ) = (q : ℝ)⁻¹ * ∑ j, palmExpect F c₀ E
      (fun v => Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) (fun _ => 0) v)) := by
  have hint : ∀ (ℓ : Fin N) (j : Fin q), Integrable (fun A0 => palmWeight F c₀ E ℓ A0 *
      Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) (fun _ => 0)
        (freshEigenvector (F + A0) ℓ))) (freshTracelessLaw N c₀) := fun ℓ j =>
    (mts_integrable_palmWeight F c₀ E ℓ).mul_bdd
      ((mts_measurable_ratioTag Φ _ _).comp
        (mts_measurable_freshEigenvector F ℓ)).aestronglyMeasurable
      (ae_of_all _ fun A0 => Φ.norm_coe_le_norm _)
  unfold palmExpect mts_tagTest
  have h1 : ∀ ℓ : Fin N, (∫ A0, palmWeight F c₀ E ℓ A0 * ((q : ℝ)⁻¹ * ∑ j,
      Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) (fun _ => 0) (freshEigenvector (F + A0) ℓ)))
      ∂freshTracelessLaw N c₀) = (q : ℝ)⁻¹ * ∑ j, ∫ A0, palmWeight F c₀ E ℓ A0 *
      Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) (fun _ => 0) (freshEigenvector (F + A0) ℓ))
      ∂freshTracelessLaw N c₀ := by
    intro ℓ
    rw [← integral_finsetSum _ fun j _ => hint ℓ j, ← integral_const_mul]
    congr 1; funext A0
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [h1]
  rw [← Finset.mul_sum, Finset.sum_comm, mul_div_assoc, Finset.sum_div]

theorem mts_isProbabilityMeasure_circularVectorLaw (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (circularVectorLaw ι) := by
  unfold circularVectorLaw; infer_instance

/-- The Gaussian expectation of the averaged tag test is the average of the tag expectations. -/
theorem mts_integral_tagTest (M : Matrix (Fin N) (Fin N) ℂ) (q : ℕ)
    (Dt : Fin q → Matrix (Fin N) (Fin N) ℂ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) :
    ∫ g, mts_tagTest q Dt Φ (M *ᵥ g) ∂circularVectorLaw (Fin N) = (q : ℝ)⁻¹ * ∑ j,
      ∫ g, Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) (fun _ => 0) (M *ᵥ g))
        ∂circularVectorLaw (Fin N) := by
  have := mts_isProbabilityMeasure_circularVectorLaw (Fin N)
  unfold mts_tagTest
  have hm : ∀ j, Measurable fun g : Fin N → ℂ =>
      Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) (fun _ => 0) (M *ᵥ g)) := fun j =>
    (mts_measurable_ratioTag Φ _ _).comp (mts_measurable_mulVec measurable_const measurable_id)
  rw [integral_const_mul, integral_finsetSum _ fun j _ => Integrable.of_bound
    (hm j).aestronglyMeasurable ‖Φ‖ (ae_of_all _ fun g => Φ.norm_coe_le_norm _)]

end Fresh

/-!
## The prior window measure
-/

section Prior

variable {Ω : Type*} [MeasurableSpace Ω]

theorem mts_isProbabilityMeasure_windowWeight {w : ℝ → ℝ} (hw : IsWindow w) :
    IsProbabilityMeasure (volume.withDensity fun u => ENNReal.ofReal (w u)) := by
  have hwi : Integrable w := hw.1.integrable_of_hasCompactSupport hw.2.1
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hwi (ae_of_all _ hw.2.2.1), hw.2.2.2,
    ENNReal.ofReal_one]

theorem mts_isProbabilityMeasure_prior {Pω : Measure Ω} [IsProbabilityMeasure Pω]
    {w : ℝ → ℝ} (hw : IsWindow w) : IsProbabilityMeasure (priorWindowMeasure Pω w) := by
  have := mts_isProbabilityMeasure_windowWeight hw
  unfold priorWindowMeasure
  infer_instance

theorem mts_ae_prior_window {Pω : Measure Ω} [IsProbabilityMeasure Pω] {w : ℝ → ℝ}
    (hw : IsWindow w) : ∀ᵐ x ∂priorWindowMeasure Pω w, w (x : ℝ × Ω).1 ≠ 0 := by
  have hwm : Measurable fun u => ENNReal.ofReal (w u) :=
    ENNReal.measurable_ofReal.comp hw.1.measurable
  have h1 : ∀ᵐ u ∂(volume.withDensity fun u => ENNReal.ofReal (w u)), w u ≠ 0 := by
    rw [ae_withDensity_iff hwm]
    refine ae_of_all _ fun u hu h0 => hu ?_
    rw [h0, ENNReal.ofReal_zero]
  have := mts_isProbabilityMeasure_windowWeight hw
  unfold priorWindowMeasure
  exact (Measure.quasiMeasurePreserving_fst (μ := volume.withDensity fun u =>
    ENNReal.ofReal (w u)) (ν := Pω)).ae h1

/-- `∫ f d𝔭_W = ∫ w(u) E_ω f(u, ω) du` for integrable `f`. -/
theorem mts_integral_prior {Pω : Measure Ω} [IsProbabilityMeasure Pω] {w : ℝ → ℝ}
    (hw : IsWindow w) {f : ℝ × Ω → ℝ} (hf : Integrable f (priorWindowMeasure Pω w)) :
    ∫ x, f x ∂priorWindowMeasure Pω w = ∫ u, w u * ∫ ω, f (u, ω) ∂Pω := by
  have hwm : Measurable fun u => ENNReal.ofReal (w u) :=
    ENNReal.measurable_ofReal.comp hw.1.measurable
  unfold priorWindowMeasure at hf ⊢
  rw [integral_prod _ hf, integral_withDensity_eq_integral_toReal_smul hwm]
  · refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (hw.2.2.1 u)]
  · exact ae_of_all _ fun u => ENNReal.ofReal_lt_top

end Prior

/-!
## The Palm and Gaussian tag tests along the prior
-/

section Tags

variable (p : Parameters) (k : ZMod p.n)

/-- The Palm tag test `Â_{F(e)}[q⁻¹Σ_j Φ(q v*D_jv/v*Dv)]` at `(e, ω)`. -/
def mts_palmTag (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (q : ℕ)
    (Dt : ℝ × BlockState p k → Fin q → Matrix (Fin (Fintype.card (BlockSite p k)))
      (Fin (Fintype.card (BlockSite p k))) ℂ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    (x : ℝ × BlockState p k) : ℝ :=
  palmExpect (blockDeformation p k σ x.2 x.1) p.c x.1 (mts_tagTest q (Dt x) Φ)

/-- The Gaussian tag test of covariance `Γ₀ = M₀M₀*`, `M₀ = blockFieldFactor`, at `(e, ω)`. -/
def mts_gaussTag (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (q : ℕ)
    (Dt : ℝ × BlockState p k → Fin q → Matrix (Fin (Fintype.card (BlockSite p k)))
      (Fin (Fintype.card (BlockSite p k))) ℂ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    (x : ℝ × BlockState p k) : ℝ :=
  ∫ g, mts_tagTest q (Dt x) Φ (Matrix.reindex σ σ (blockFieldFactor p k x.2 x.1) *ᵥ g)
    ∂circularVectorLaw (Fin (Fintype.card (BlockSite p k)))

/-- The prior point `(u, ω) ↦ (e(u), ω)`. -/
def mts_priorPoint (E : ℝ) (x : ℝ × BlockState p k) : ℝ × BlockState p k :=
  (microEnergy p E x.1, x.2)

theorem mts_measurable_microEnergy (E : ℝ) : Measurable (microEnergy p E) :=
  (by unfold microEnergy; fun_prop : Continuous (microEnergy p E)).measurable

theorem mts_microCoord_microEnergy {E : ℝ} (hρ : 0 < Parameters.semicircleDensity E) (u : ℝ) :
    microCoord p E (microEnergy p E u) = u := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  unfold microEnergy microCoord
  field_simp
  ring

theorem mts_measurable_priorPoint (E : ℝ) : Measurable (mts_priorPoint p k E) :=
  ((mts_measurable_microEnergy p E).comp measurable_fst).prodMk measurable_snd

variable {p k}

theorem mts_measurable_palmTag (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (q : ℕ)
    {Dt : ℝ × BlockState p k → Fin q → Matrix (Fin (Fintype.card (BlockSite p k)))
      (Fin (Fintype.card (BlockSite p k))) ℂ} (hDt : ∀ j, Measurable fun x => Dt x j)
    (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) : Measurable (mts_palmTag p k σ q Dt Φ) := by
  have hFm : Measurable fun x : ℝ × BlockState p k => blockDeformation p k σ x.2 x.1 :=
    (mts_measurable_reindex σ).comp (mts_measurable_blockF_of p k measurable_snd measurable_fst)
  exact mts_measurable_palmExpect hFm measurable_fst _ (mts_measurable_tagTest_of q
    (Dt := fun y : (ℝ × BlockState p k) × _ => Dt y.1) (fun j => (hDt j).comp measurable_fst) Φ
    measurable_snd)

theorem mts_measurable_gaussTag (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (q : ℕ)
    {Dt : ℝ × BlockState p k → Fin q → Matrix (Fin (Fintype.card (BlockSite p k)))
      (Fin (Fintype.card (BlockSite p k))) ℂ} (hDt : ∀ j, Measurable fun x => Dt x j)
    (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) : Measurable (mts_gaussTag p k σ q Dt Φ) := by
  have := mts_isProbabilityMeasure_circularVectorLaw (Fin (Fintype.card (BlockSite p k)))
  have hM : Measurable fun x : ℝ × BlockState p k =>
      Matrix.reindex σ σ (blockFieldFactor p k x.2 x.1) :=
    (mts_measurable_reindex σ).comp
      (mts_measurable_blockFieldFactor_of p k measurable_snd measurable_fst)
  have h := mts_measurable_tagTest_of q
    (Dt := fun y : (ℝ × BlockState p k) × (Fin (Fintype.card (BlockSite p k)) → ℂ) => Dt y.1)
    (fun j => (hDt j).comp measurable_fst) Φ
    (mts_measurable_mulVec (hM.comp measurable_fst) measurable_snd)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem mts_abs_palmTag_le (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (q : ℕ)
    (Dt : ℝ × BlockState p k → Fin q → Matrix (Fin (Fintype.card (BlockSite p k)))
      (Fin (Fintype.card (BlockSite p k))) ℂ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (x : ℝ × BlockState p k) :
    |mts_palmTag p k σ q Dt Φ x| ≤ ‖Φ‖ :=
  mts_abs_palmExpect_le _ _ _ (norm_nonneg _) (mts_abs_tagTest_le q (Dt x) Φ)

theorem mts_abs_gaussTag_le (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (q : ℕ)
    (Dt : ℝ × BlockState p k → Fin q → Matrix (Fin (Fintype.card (BlockSite p k)))
      (Fin (Fintype.card (BlockSite p k))) ℂ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (x : ℝ × BlockState p k) :
    |mts_gaussTag p k σ q Dt Φ x| ≤ ‖Φ‖ := by
  have := mts_isProbabilityMeasure_circularVectorLaw (Fin (Fintype.card (BlockSite p k)))
  have h := norm_integral_le_of_norm_le_const (μ := circularVectorLaw (Fin (Fintype.card
    (BlockSite p k)))) (C := ‖Φ‖) (f := fun g => mts_tagTest q (Dt x) Φ
      (Matrix.reindex σ σ (blockFieldFactor p k x.2 x.1) *ᵥ g))
    (ae_of_all _ fun g => by rw [Real.norm_eq_abs]; exact mts_abs_tagTest_le q (Dt x) Φ _)
  simp only [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

theorem mts_palmTag_nonneg (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (q : ℕ)
    (Dt : ℝ × BlockState p k → Fin q → Matrix (Fin (Fintype.card (BlockSite p k)))
      (Fin (Fintype.card (BlockSite p k))) ℂ) {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ} (hΦ : ∀ x, 0 ≤ Φ x)
    (x : ℝ × BlockState p k) : 0 ≤ mts_palmTag p k σ q Dt Φ x :=
  mts_palmExpect_nonneg _ _ _ (mts_tagTest_nonneg q (Dt x) hΦ)

end Tags

/-!
## From the window to the prior (`OneBlockNormalizerContract.tv`)
-/

/-- **Window to prior.** Hypothesis: `OneBlockNormalizerContract` (`tv`).
Fixed
first `b`, bulk `E`, `T`, a window `w`, `Φ ≥ 0` and `ε > 0`; then for `W ≥ W₀`, `n ≤ TW`, every
model, block, one-block splitting law, frame, reindexing and measurable tag family:
`|∫ Â[test] d𝔪⁰_W - ∫ Â[test](e(u), ω) d𝔭_W| ≤ ε`.
-/
theorem mts_window_to_prior (hNorm : OneBlockNormalizerContract) {b : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) (T : ℝ) {w : ℝ → ℝ}
    (hw : IsWindow w) {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ} (hΦ : ∀ x, 0 ≤ Φ x) {ε : ℝ} (hε : 0 < ε) :
    ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (k : ZMod p.n) (Pω : Measure (BlockState p k)),
      IsBlockSplitting p k model Pω → ∀ U, IsBlockFrame p k U →
    ∀ (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (q : ℕ)
      (Dt : ℝ × BlockState p k → Fin q → Matrix (Fin (Fintype.card (BlockSite p k)))
        (Fin (Fintype.card (BlockSite p k))) ℂ), (∀ j, Measurable fun x => Dt x j) →
      |(∫⁻ x, ENNReal.ofReal (mts_palmTag p k σ q Dt Φ x)
            ∂blockWindowMeasure p k U Pω E w).toReal -
          ∫ x, mts_palmTag p k σ q Dt Φ (mts_priorPoint p k E x) ∂priorWindowMeasure Pω w| ≤ ε := by
  set B := ‖Φ‖ + 1 with hBdef
  have hB : 0 < B := by positivity
  obtain ⟨W₀, hW₀⟩ := hNorm.tv b hb hb' E hE1 hE2 T w hw (ε / B) (by positivity)
  refine ⟨W₀, fun p hpb hW hn model k Pω hs U hU σ q Dt hDt => ?_⟩
  have hρ := mts_semicircleDensity_pos hE1 hE2
  have hm := mts_measurable_palmTag σ q hDt Φ
  set F : ℝ × BlockState p k → ℝ := fun y => mts_palmTag p k σ q Dt Φ (mts_priorPoint p k E y) / B
  have hFm : Measurable F := (hm.comp (mts_measurable_priorPoint p k E)).div_const _
  have hF1 : ∀ y, |F y| ≤ 1 := fun y => by
    simp only [F]
    rw [abs_div, abs_of_pos hB, div_le_one hB]
    exact (mts_abs_palmTag_le σ q Dt Φ _).trans (by linarith)
  have hF := hW₀ p hpb hW hn model k Pω hs U hU F hFm hF1
  have h1 : (fun x : ℝ × BlockState p k => F (microCoord p E x.1, x.2)) =
      fun x => mts_palmTag p k σ q Dt Φ x / B := by
    funext x
    simp only [F, mts_priorPoint, mts_microEnergy_microCoord p hρ]
  rw [h1, integral_div, integral_div, ← sub_div, abs_div, abs_of_pos hB,
    div_le_div_iff_of_pos_right hB] at hF
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => mts_palmTag_nonneg σ q Dt hΦ x)
    hm.aestronglyMeasurable]
  exact hF

/-!
## From the Palm law to the Gaussian field `Γ₀` under the prior
-/

/-- **Palm to Gaussian field of covariance `Γ₀` under the prior window measure.** Hypotheses:
`UniformClockTagsPalmContract`, `ClockCovarianceStabilityContract` and
`BlockRegularEventContract`.
Fixed first `b`, bulk `E`, `T`, a window `w`, `Φ`, `ε > 0` and
`K > 0`; then for `W ≥ W₀`, `n ≤ TW`, every model, block, one-block splitting law, reindexing,
`q ≥ 1` and measurable tag family `D_j(e, ω) ⪰ 0` with `Σ_j D_j ⪰ 1`:
`|∫ Â[test](e(u), ω) d𝔭_W - ∫ E_g test(M₀g)(e(u), ω) d𝔭_W| ≤ 3ε + 2‖Φ‖/K`.
-/
theorem mts_prior_palm_gauss (hUCT : UniformClockTagsPalmContract)
    (hCS : ClockCovarianceStabilityContract) (hReg : BlockRegularEventContract) {b : ℝ}
    (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) (T : ℝ) {w : ℝ → ℝ}
    (hw : IsWindow w) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K) :
    ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (k : ZMod p.n) (Pω : Measure (BlockState p k)),
      IsBlockSplitting p k model Pω →
    ∀ (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (q : ℕ), 0 < q →
    ∀ Dt : ℝ × BlockState p k → Fin q → Matrix (Fin (Fintype.card (BlockSite p k)))
        (Fin (Fintype.card (BlockSite p k))) ℂ, (∀ j, Measurable fun x => Dt x j) →
      (∀ x j, (Dt x j).PosSemidef) → (∀ x, ((∑ j, Dt x j) - 1).PosSemidef) →
      |(∫ x, mts_palmTag p k σ q Dt Φ (mts_priorPoint p k E x) ∂priorWindowMeasure Pω w) -
          ∫ x, mts_gaussTag p k σ q Dt Φ (mts_priorPoint p k E x) ∂priorWindowMeasure Pω w| ≤
        3 * ε + 2 * ‖Φ‖ / K := by
  classical
  obtain ⟨hκ, hκE⟩ := mts_bulk_margin hE1 hE2
  set κ := (2 - |E|) / 2
  have hρ := mts_semicircleDensity_pos hE1 hE2
  obtain ⟨R, hR⟩ := mts_exists_support_radius hw.2.1
  obtain ⟨r₀, s₀, v₀, hFC, hDc⟩ := mts_prior_irregular_le hReg hb hb' hE1 hE2 T hw
  obtain ⟨A, hA⟩ := hDc 1 one_pos
  obtain ⟨η, hη, W₁, hW₁⟩ := mts_palm_gauss_regular (A := A) hUCT hCS hb hb' hκ hFC Φ hε hK
  obtain ⟨W₂, hW₂⟩ := hA η hη
  set B := ‖Φ‖ + 1 with hBdef
  have hB : 0 < B := by positivity
  set ε' := 2 * ε + 2 * ‖Φ‖ / K with hε'def
  have hε' : 0 ≤ ε' := by positivity
  refine ⟨max (max W₁ W₂) (max ⌈R / (κ * Parameters.semicircleDensity E)⌉₊
    (⌈2 * B / ε⌉₊ + 1)), ?_⟩
  intro p hpb hW hn model k Pω hs σ q hq Dt hDt hDpsd hD1
  have hP := mts_isProbabilityMeasure_of_blockSplitting hs
  have hPr := mts_isProbabilityMeasure_prior (Pω := Pω) hw
  have hW1 : W₁ ≤ p.W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW2 : W₂ ≤ p.W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hWR : R / (κ * Parameters.semicircleDensity E) ≤ p.W := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans hW))
  have hWε : 2 * B / ε + 1 ≤ p.W := by
    have h2 : ((⌈2 * B / ε⌉₊ + 1 : ℕ) : ℝ) ≤ p.W := by
      exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hW)
    push_cast at h2
    linarith [Nat.le_ceil (2 * B / ε)]
  have hWpos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  set Pa := fun x => mts_palmTag p k σ q Dt Φ (mts_priorPoint p k E x) with hPadef
  set Ga := fun x => mts_gaussTag p k σ q Dt Φ (mts_priorPoint p k E x) with hGadef
  have hPam : Measurable Pa :=
    (mts_measurable_palmTag σ q hDt Φ).comp (mts_measurable_priorPoint p k E)
  have hGam : Measurable Ga :=
    (mts_measurable_gaussTag σ q hDt Φ).comp (mts_measurable_priorPoint p k E)
  have hbulk : MeasurableSet {x : ℝ × BlockState p k | microEnergy p E x.1 ∈ bulkInterval κ} :=
    measurableSet_Icc.preimage ((mts_measurable_microEnergy p E).comp measurable_fst)
  set Δ : ℝ × BlockState p k → ℝ := fun x =>
    if microEnergy p E x.1 ∈ bulkInterval κ then Pa x - Ga x else 0 with hΔdef
  have hΔm : Measurable Δ := by
    refine Measurable.ite hbulk ?_ measurable_const
    exact hPam.sub hGam
  have hΔb : ∀ x, |Δ x| ≤ 2 * B := by
    intro x
    simp only [hΔdef]
    split_ifs
    · calc |Pa x - Ga x| ≤ |Pa x| + |Ga x| := abs_sub _ _
        _ ≤ ‖Φ‖ + ‖Φ‖ := add_le_add (mts_abs_palmTag_le σ q Dt Φ _) (mts_abs_gaussTag_le σ q Dt Φ _)
        _ ≤ 2 * B := by linarith
    · simp only [abs_zero]; positivity
  have hΔreg : ∀ x : ℝ × BlockState p k,
      IsBlockRegular p k σ A r₀ s₀ v₀ η (microEnergy p E x.1) x.2 → |Δ x| ≤ ε' := by
    intro x hx
    simp only [hΔdef]
    split_ifs with he
    · have h := hW₁ p hpb hW1 k σ x.2 (microEnergy p E x.1) he hx q hq
        (Dt (microEnergy p E x.1, x.2)) (hDpsd _) (hD1 _)
      simp only [hPadef, hGadef, mts_palmTag, mts_gaussTag, mts_priorPoint]
      rw [mts_palmExpect_tagTest, mts_integral_tagTest]
      exact h
    · simp only [abs_zero]; exact hε'
  obtain ⟨G, hGm, hG1, hG0, hΔG⟩ := mts_truncation hΔm hε' (by positivity : (0 : ℝ) < B) hΔb
    (fun x => IsBlockRegular p k σ A r₀ s₀ v₀ η (microEnergy p E x.1) x.2) hΔreg
  have hGint := hW₂ p hpb hW2 hn model k Pω hs σ G hGm hG1 (fun u ω hreg => hG0 (u, ω) hreg)
  have hGr : ∫ x, |G x| ∂priorWindowMeasure Pω w ≤ (p.W : ℝ) ^ (-(1 : ℝ)) := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => abs_nonneg _)
      (continuous_abs.measurable.comp hGm).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hGint
  have hae : (fun x => Pa x - Ga x) =ᵐ[priorWindowMeasure Pω w] Δ := by
    filter_upwards [mts_ae_prior_window (Pω := Pω) hw] with x hx
    have hu : |x.1| ≤ R := hR x.1 hx
    have hbx : microEnergy p E x.1 ∈ bulkInterval κ :=
      mts_mem_bulk_of_window p hρ hκE hκ hWR (by rw [mts_microCoord_microEnergy p hρ]; exact hu)
    simp only [hΔdef, hbx, ite_true]
  have hPi : Integrable Pa (priorWindowMeasure Pω w) := Integrable.of_bound
    hPam.aestronglyMeasurable ‖Φ‖ (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact mts_abs_palmTag_le σ q Dt Φ _)
  have hGi : Integrable Ga (priorWindowMeasure Pω w) := Integrable.of_bound
    hGam.aestronglyMeasurable ‖Φ‖ (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact mts_abs_gaussTag_le σ q Dt Φ _)
  have hGGi : Integrable (fun x => |G x|) (priorWindowMeasure Pω w) := Integrable.of_bound
    (continuous_abs.measurable.comp hGm).aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_abs]; exact hG1 x)
  have hWinv : 2 * B * (p.W : ℝ) ^ (-(1 : ℝ)) ≤ ε := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_iff₀ hWpos]
    have := (div_le_iff₀ hε).1 (by linarith : 2 * B / ε ≤ p.W - 1)
    nlinarith
  rw [← integral_sub hPi hGi, integral_congr_ae hae]
  calc |∫ x, Δ x ∂priorWindowMeasure Pω w| ≤ ∫ x, |Δ x| ∂priorWindowMeasure Pω w :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, (ε' + 2 * B * |G x|) ∂priorWindowMeasure Pω w :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          ((integrable_const ε').add (hGGi.const_mul _)) (ae_of_all _ fun x =>
            (hΔG x).trans (by
              have : G x ≤ |G x| := le_abs_self _
              have h2B : 0 ≤ 2 * B := by positivity
              nlinarith))
    _ = ε' + 2 * B * ∫ x, |G x| ∂priorWindowMeasure Pω w := by
        rw [integral_add (integrable_const _) (hGGi.const_mul _), integral_const_mul,
          integral_const]
        simp
    _ ≤ ε' + 2 * B * (p.W : ℝ) ^ (-(1 : ℝ)) := by
        have h2B : 0 ≤ 2 * B := by positivity
        nlinarith
    _ ≤ 3 * ε + 2 * ‖Φ‖ / K := by rw [hε'def]; linarith

end BlockBand.Endpoints
