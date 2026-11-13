module

public import BlockBand.Window.SmallCritical.Mode
public import BlockBand.Window.SmallCritical.GridMean
public import BlockBand.QUE.Fourier.PhysicalFiniteTest

/-!
# The small-ratio critical theorem: variance clause

The mark variance of a critical marked limit satisfies `V_P(w, φ) ≤ C M² τ^{1-η}` for smooth `φ`
with `‖φ - φ̄‖_∞ ≤ M`.

Proof. Window transfer applied to `A_α = |q·p_α|²` with the deterministic grid-mean-zero
test `q_k = (φ(k/n) - φ̄)/M - (grid mean)` (`|q| ≤ 2`), with `ε ≤ C τ_W` from the QUE theorem; the
grid mean tends to `φ̄` and the bounded window count pays the grid-mean error; Fatou passes to
the limit; spectral stationarity gives uniformity in `w`.

Hypotheses: `WindowTransferContract` and `ModeBoundContract`; no other input.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.SmallCritical

open MeasureTheory Filter Topology Set
open BlockBand.Model.Construction BlockBand.Internal.Contracts.WindowAngular BlockBand.QUE.Fourier
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal

attribute [local instance] massProfile_opensMeasurableSpace

/-- The mark functional `g_φ(ν) = |ν(φ) - φ̄|²`. -/
def varMark (φ : Torus → ℝ) (ν : MassProfile) : ℝ :=
  |(∫ r, φ r ∂(ν : Measure Torus)) - ∫ r, φ r| ^ 2

theorem continuous_varMark {φ : Torus → ℝ} (hφ : Continuous φ) : Continuous (varMark φ) :=
  ((continuous_profile_integral_real φ hφ).sub continuous_const).abs.pow 2

theorem varMark_nonneg (φ : Torus → ℝ) (ν : MassProfile) : 0 ≤ varMark φ ν := sq_nonneg _

theorem markVariance_eq_weightFunctional (P : ProbabilityMeasure MarkedPointMeasure)
    (w : SpectralWeight) (φ : Torus → ℝ) :
    markVariance P w φ = weightFunctional P (varMark φ) w := rfl

variable {p : Parameters}

/-- The deterministic site test `v_x = (φ(x₁/n) - φ̄)/M`. -/
def siteTest (p : Parameters) (φ : Torus → ℝ) (M : ℝ) : p.Site → ℝ :=
  fun x => (φ (physicalProfileGrid p x.1) - ∫ r, φ r) / M

/-- `S_α = Σ_x v_x |ψ_α(x)|² - N⁻¹ Σ_x v_x`, the centred QUE statistic. -/
def varStat (p : Parameters) (φ : Torus → ℝ) (M : ℝ) (α : Fin p.N) (H : p.SiteMatrix) : ℝ :=
  (∑ x, siteTest p φ M x * ‖physicalOrderedEigenvector p H α x‖ ^ 2) -
    (p.N : ℝ)⁻¹ * ∑ x, siteTest p φ M x

/-- The window observable `A_α = min(1, S_α²/4)`. -/
def varObservable (p : Parameters) (φ : Torus → ℝ) (M : ℝ) (α : Fin p.N) (H : p.SiteMatrix) : ℝ :=
  min 1 (varStat p φ M α H ^ 2 / 4)

theorem siteTest_abs_le {φ : Torus → ℝ} {M : ℝ} (hM : 0 < M) (hφM : ∀ r, |φ r - ∫ r', φ r'| ≤ M)
    (x : p.Site) : |siteTest p φ M x| ≤ 1 := by
  unfold siteTest
  rw [abs_div, abs_of_pos hM, div_le_one hM]
  exact hφM _

theorem measurable_varStat (φ : Torus → ℝ) (M : ℝ) (α : Fin p.N) :
    Measurable (varStat p φ M α) := by
  unfold varStat
  refine Measurable.sub_const (Finset.measurable_sum _ fun x _ => ?_) _
  exact measurable_const.mul (measurable_physicalOrderedSiteMass p α x)

theorem measurable_varObservable (φ : Torus → ℝ) (M : ℝ) (α : Fin p.N) :
    Measurable (varObservable p φ M α) :=
  measurable_const.min (((measurable_varStat φ M α).pow_const 2).div_const 4)

theorem varObservable_mem (φ : Torus → ℝ) (M : ℝ) (α : Fin p.N) (H : p.SiteMatrix) :
    0 ≤ varObservable p φ M α H ∧ varObservable p φ M α H ≤ 1 :=
  ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩

theorem varObservable_shift (φ : Torus → ℝ) (M : ℝ) (α : Fin p.N) :
    IsScalarShiftInvariant (varObservable p φ M α) :=
  isScalarShiftInvariant_eigenvector α (fun ψ => min 1 (((∑ x, siteTest p φ M x * ‖ψ x‖ ^ 2) -
    (p.N : ℝ)⁻¹ * ∑ x, siteTest p φ M x) ^ 2 / 4))

/-- Almost surely `|S_α| ≤ 2` (unit eigenvectors, `|v| ≤ 1`). -/
theorem varStat_abs_le_ae (model : p.GaussianRingModel) {φ : Torus → ℝ} {M : ℝ} (hM : 0 < M)
    (hφM : ∀ r, |φ r - ∫ r', φ r'| ≤ M) (α : Fin p.N) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), |varStat p φ M α H| ≤ 2 := by
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable] with H hH hsep
  have htot := physicalOrderedEigenvector_totalMass p H hH hsep α
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have h1 : |∑ x, siteTest p φ M x * ‖physicalOrderedEigenvector p H α x‖ ^ 2| ≤ 1 := by
    calc _ ≤ ∑ x, |siteTest p φ M x * ‖physicalOrderedEigenvector p H α x‖ ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, ‖physicalOrderedEigenvector p H α x‖ ^ 2 := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [abs_mul, abs_of_nonneg (sq_nonneg ‖physicalOrderedEigenvector p H α x‖)]
          exact mul_le_of_le_one_left (sq_nonneg _) (siteTest_abs_le hM hφM x)
      _ = 1 := htot
  have h2 : |(p.N : ℝ)⁻¹ * ∑ x, siteTest p φ M x| ≤ 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hN)]
    calc (p.N : ℝ)⁻¹ * |∑ x, siteTest p φ M x| ≤ (p.N : ℝ)⁻¹ * ∑ _x : p.Site, (1 : ℝ) := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun x _ => siteTest_abs_le hM hφM x)
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
          have : (Fintype.card p.Site : ℝ) = p.N := by
            simp [Parameters.N, Parameters.Site]
          rw [this, inv_mul_cancel₀ hN.ne']
  unfold varStat
  calc _ ≤ |∑ x, siteTest p φ M x * ‖physicalOrderedEigenvector p H α x‖ ^ 2| +
        |(p.N : ℝ)⁻¹ * ∑ x, siteTest p φ M x| := abs_sub _ _
    _ ≤ 2 := by linarith

/-- `E A_α ≤ min(1, queStatistic)`. -/
theorem integral_varObservable_le (model : p.GaussianRingModel) {φ : Torus → ℝ} {M : ℝ}
    (hM : 0 < M) (hφM : ∀ r, |φ r - ∫ r', φ r'| ≤ M) (α : Fin p.N) :
    ∫ H, varObservable p φ M α H ∂(model.law : Measure p.SiteMatrix) ≤
      min 1 ((constructSpectralRealization p model).queStatistic α (siteTest p φ M)) := by
  have hiA : Integrable (varObservable p φ M α) (model.law : Measure p.SiteMatrix) :=
    (integrable_const (1 : ℝ)).mono' (measurable_varObservable φ M α).aestronglyMeasurable
      (Eventually.of_forall fun H => by
        rw [Real.norm_eq_abs, abs_of_nonneg (varObservable_mem φ M α H).1]
        exact (varObservable_mem φ M α H).2)
  have hiS : Integrable (fun H => varStat p φ M α H ^ 2) (model.law : Measure p.SiteMatrix) := by
    refine (integrable_const (4 : ℝ)).mono'
      ((measurable_varStat φ M α).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [varStat_abs_le_ae model hM hφM α] with H hH
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (varStat p φ M α H), sq_abs (varStat p φ M α H)]
  refine le_min ?_ ?_
  · calc _ ≤ ∫ _H, (1 : ℝ) ∂(model.law : Measure p.SiteMatrix) :=
          integral_mono hiA (integrable_const _) fun H => (varObservable_mem φ M α H).2
      _ = 1 := by simp
  · have hq : (constructSpectralRealization p model).queStatistic α (siteTest p φ M) =
        ∫ H, varStat p φ M α H ^ 2 ∂(model.law : Measure p.SiteMatrix) := by
      unfold Parameters.SpectralRealization.queStatistic
      refine integral_congr_ae (Eventually.of_forall fun H => ?_)
      simp only [sq_abs]
      rfl
    rw [hq]
    refine integral_mono hiA hiS fun H => ?_
    calc varObservable p φ M α H ≤ varStat p φ M α H ^ 2 / 4 := min_le_right _ _
      _ ≤ varStat p φ M α H ^ 2 := by nlinarith [sq_nonneg (varStat p φ M α H)]

/-- Almost surely `g_φ(ν_α) ≤ 8M² A_α + 2 (gridDefect)² · 1`. -/
theorem varMark_le_ae (model : p.GaussianRingModel) {φ : Torus → ℝ} {M : ℝ} (hM : 0 < M)
    (hφM : ∀ r, |φ r - ∫ r', φ r'| ≤ M) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ α,
      varMark φ (physicalOrderedProfile p H α) ≤
        (8 * M ^ 2) * varObservable p φ M α H + (2 * gridDefect p φ ^ 2) * 1 := by
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable,
    ae_all_iff.2 (fun α => varStat_abs_le_ae model hM hφM α)] with H hH hsep hS α
  have hsum := physicalOrderedBlockMass_sum p H hH hsep α
  have hint := integral_physicalOrderedProfile (F := ℝ) H hH hsep α φ
  simp only [smul_eq_mul] at hint
  have hkey : (∫ r, φ r ∂(physicalOrderedProfile p H α : Measure Torus)) - ∫ r, φ r =
      M * varStat p φ M α H + gridDefect p φ := by
    have hsite : (∑ x, siteTest p φ M x * ‖physicalOrderedEigenvector p H α x‖ ^ 2) =
        (∑ k : ZMod p.n, physicalOrderedBlockMass p H α k *
          ((φ (physicalProfileGrid p k) - ∫ r, φ r) / M)) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => ?_
      unfold physicalOrderedBlockMass siteTest
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    have hgd : gridDefect p φ = M * ((p.N : ℝ)⁻¹ * ∑ x, siteTest p φ M x) := by
      have hMne : M ≠ 0 := hM.ne'
      unfold gridDefect siteTest
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun (x : p.Site) _ => ?_
      field_simp
    unfold varStat
    rw [hsite, hgd, hint]
    have : ∑ k : ZMod p.n, physicalOrderedBlockMass p H α k *
        ((φ (physicalProfileGrid p k) - ∫ r, φ r) / M) =
        (∑ k : ZMod p.n, physicalOrderedBlockMass p H α k * φ (physicalProfileGrid p k) -
          (∑ k : ZMod p.n, physicalOrderedBlockMass p H α k) * ∫ r, φ r) / M := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, hsum]
    field_simp
    ring
  have hS2 : varStat p φ M α H ^ 2 / 4 ≤ 1 := by
    have := hS α
    nlinarith [sq_abs (varStat p φ M α H), abs_nonneg (varStat p φ M α H)]
  unfold varMark
  rw [hkey, varObservable, min_eq_right hS2, sq_abs, mul_one]
  nlinarith [sq_nonneg (M * varStat p φ M α H - gridDefect p φ)]

/-- `E Σ_α ofReal(w(u_α) A_α) = ofReal 𝒱_{n,W}(A)` for `[0,1]`-valued measurable `A`. -/
theorem lintegral_window_eq (model : p.GaussianRingModel) (E : ℝ)
    {w : ℝ → ℝ} (hwc : Continuous w) (hws : HasCompactSupport w) (hw0 : ∀ u, 0 ≤ w u)
    (A : Fin p.N → p.SiteMatrix → ℝ) (hAm : ∀ α, Measurable (A α))
    (hA01 : ∀ α H, 0 ≤ A α H ∧ A α H ≤ 1) :
    ∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal
        (w ((p.N : ℝ) * Parameters.semicircleDensity E * (physicalOrderedEigenvalue p H α - E)) *
          A α H) ∂(model.law : Measure p.SiteMatrix) =
      ENNReal.ofReal (windowExpectation p model E (Parameters.semicircleDensity E) w A) := by
  have h := lintegral_le_windowExpectation (g := fun _ => (0 : ℝ)) model E hwc hws hw0
    (fun _ => le_rfl) A hAm hA01 zero_le_one (Eventually.of_forall fun H α => by
      simpa using (hA01 α H).1)
  set ρ := Parameters.semicircleDensity E
  obtain ⟨Mw, hMw⟩ := hws.exists_bound_of_continuous hwc
  set F : p.SiteMatrix → ℝ := fun H => ∑ α : Fin p.N,
      w ((p.N : ℝ) * ρ * (physicalOrderedEigenvalue p H α - E)) * A α H with hF
  have hFm : Measurable F := by
    refine Finset.measurable_sum _ fun α _ => ?_
    exact (hwc.measurable.comp (measurable_const.mul
      ((measurable_physicalOrderedEigenvalue p α).sub_const E))).mul (hAm α)
  have hF0 : ∀ H, 0 ≤ F H := fun H =>
    Finset.sum_nonneg fun α _ => mul_nonneg (hw0 _) (hA01 α H).1
  have hFb : ∀ H, ‖F H‖ ≤ (p.N : ℝ) * Mw := by
    intro H
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 H)]
    calc F H ≤ ∑ _α : Fin p.N, Mw := by
          refine Finset.sum_le_sum fun α _ => ?_
          have h1 := hMw ((p.N : ℝ) * ρ * (physicalOrderedEigenvalue p H α - E))
          rw [Real.norm_eq_abs, abs_of_nonneg (hw0 _)] at h1
          calc w _ * A α H ≤ w _ * 1 := mul_le_mul_of_nonneg_left (hA01 α H).2 (hw0 _)
            _ ≤ Mw := by rw [mul_one]; exact h1
      _ = (p.N : ℝ) * Mw := by simp
  have hFi : Integrable F (model.law : Measure p.SiteMatrix) :=
    (integrable_const ((p.N : ℝ) * Mw)).mono' hFm.aestronglyMeasurable
      (Eventually.of_forall hFb)
  clear h
  change _ = ENNReal.ofReal (∫ H, F H ∂(model.law : Measure p.SiteMatrix))
  rw [ofReal_integral_eq_lintegral_ofReal hFi (Eventually.of_forall hF0)]
  refine lintegral_congr fun H => ?_
  rw [hF, ENNReal.ofReal_sum_of_nonneg fun α _ => mul_nonneg (hw0 _) (hA01 α H).1]

/-- Two-observable bridge: `g(ν_α) ≤ c₁ A_α + c₂ B_α` a.s. gives
`E Σ ofReal(w g) ≤ ofReal(c₁ 𝒱(A) + c₂ 𝒱(B))`. -/
theorem lintegral_le_windowExpectation_two (model : p.GaussianRingModel) (E : ℝ)
    {w : ℝ → ℝ} (hwc : Continuous w) (hws : HasCompactSupport w) (hw0 : ∀ u, 0 ≤ w u)
    {g : MassProfile → ℝ} (A B : Fin p.N → p.SiteMatrix → ℝ) (hAm : ∀ α, Measurable (A α))
    (hA01 : ∀ α H, 0 ≤ A α H ∧ A α H ≤ 1) (hBm : ∀ α, Measurable (B α))
    (hB01 : ∀ α H, 0 ≤ B α H ∧ B α H ≤ 1) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hg : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ α,
      g (physicalOrderedProfile p H α) ≤ c₁ * A α H + c₂ * B α H) :
    ∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal
        (w ((p.N : ℝ) * Parameters.semicircleDensity E * (physicalOrderedEigenvalue p H α - E)) *
          g (physicalOrderedProfile p H α)) ∂(model.law : Measure p.SiteMatrix) ≤
      ENNReal.ofReal (c₁ * windowExpectation p model E (Parameters.semicircleDensity E) w A +
        c₂ * windowExpectation p model E (Parameters.semicircleDensity E) w B) := by
  set ρ := Parameters.semicircleDensity E
  set u : p.SiteMatrix → Fin p.N → ℝ := fun H α =>
    (p.N : ℝ) * ρ * (physicalOrderedEigenvalue p H α - E) with hu
  have hmeas : ∀ (C : Fin p.N → p.SiteMatrix → ℝ), (∀ α, Measurable (C α)) →
      Measurable (fun H => ∑ α : Fin p.N, ENNReal.ofReal (w (u H α) * C α H)) := by
    intro C hC
    refine Finset.measurable_sum _ fun α _ => ENNReal.measurable_ofReal.comp ?_
    exact (hwc.measurable.comp (measurable_const.mul
      ((measurable_physicalOrderedEigenvalue p α).sub_const E))).mul (hC α)
  have hW0 : ∀ (C : Fin p.N → p.SiteMatrix → ℝ), (∀ α H, 0 ≤ C α H ∧ C α H ≤ 1) →
      0 ≤ windowExpectation p model E ρ w C := by
    intro C hC
    exact integral_nonneg fun H => Finset.sum_nonneg fun α _ => mul_nonneg (hw0 _) (hC α H).1
  calc _ ≤ ∫⁻ H, (ENNReal.ofReal c₁ * ∑ α : Fin p.N, ENNReal.ofReal (w (u H α) * A α H) +
        ENNReal.ofReal c₂ * ∑ α : Fin p.N, ENNReal.ofReal (w (u H α) * B α H))
        ∂(model.law : Measure p.SiteMatrix) := by
        apply lintegral_mono_ae
        filter_upwards [hg] with H hH
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun α _ => ?_
        rw [← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_mul hc₂,
          ← ENNReal.ofReal_add (mul_nonneg hc₁ (mul_nonneg (hw0 _) (hA01 α H).1))
            (mul_nonneg hc₂ (mul_nonneg (hw0 _) (hB01 α H).1))]
        apply ENNReal.ofReal_le_ofReal
        calc w (u H α) * g (physicalOrderedProfile p H α) ≤
            w (u H α) * (c₁ * A α H + c₂ * B α H) := mul_le_mul_of_nonneg_left (hH α) (hw0 _)
          _ = _ := by ring
    _ = ENNReal.ofReal c₁ * ENNReal.ofReal (windowExpectation p model E ρ w A) +
        ENNReal.ofReal c₂ * ENNReal.ofReal (windowExpectation p model E ρ w B) := by
        rw [lintegral_add_left ((hmeas A hAm).const_mul _), lintegral_const_mul _ (hmeas A hAm),
          lintegral_const_mul _ (hmeas B hBm), lintegral_window_eq model E hwc hws hw0 A hAm hA01,
          lintegral_window_eq model E hwc hws hw0 B hBm hB01]
    _ = _ := by
        rw [← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_mul hc₂,
          ← ENNReal.ofReal_add (mul_nonneg hc₁ (hW0 A hA01)) (mul_nonneg hc₂ (hW0 B hB01))]

/-- The variance clause of the small-ratio critical theorem, from the window transfer theorem and
the mode bound. -/
theorem smallCritical_variance (hWT : WindowTransferContract)
    (hMode : ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ → θ < 1 / 2 →
      ModeBoundContract b θ T hb hb') :
    ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), E ^ 2 < 4 →
      ∀ η : ℝ, 0 < η → η < 1 → ∃ C : ℝ, 0 ≤ C ∧
        ∀ (τ : ℝ), 0 < τ → τ ≤ 1 → ∀ P : ProbabilityMeasure MarkedPointMeasure,
          IsCriticalMarkedLimit τ b E hb hb' P →
          ∀ (w : SpectralWeight) (φ : Torus → ℝ), IsSmoothTorusTest φ →
          ∀ M : ℝ, (∀ r, |φ r - ∫ r', φ r'| ≤ M) →
            markVariance P w φ ≤ ENNReal.ofReal (C * M ^ 2 * τ ^ (1 - η)) := by
  intro b hb hb' E hE η hη hη1
  obtain ⟨ϑ, hϑ0, hϑ1, hϑl, hϑr⟩ := exists_bulk_margin hE
  have hρ := Parameters.semicircleDensity_pos_of_sq_lt_four E hE
  set q : ℝ := 1 / η with hqdef
  have hq : 1 < q := by rw [hqdef, lt_div_iff₀ hη]; linarith
  have hqe : 1 - 1 / q = 1 - η := by simp [hqdef]
  obtain ⟨C₁, r, hr, hWTb⟩ := hWT b hb hb' 2 E (Parameters.semicircleDensity E) hE hρ
    refWeight continuous_refWeight hasCompactSupport_refWeight refWeight_nonneg integral_refWeight
    ϑ hϑ0 hϑ1 hϑl hϑr q hq
  obtain ⟨Cm, hCm0, hCm⟩ := hMode b ϑ 2 hb hb' hϑ0 hϑ1
  set D : ℝ := max (5 * Cm + 1) 1 with hD
  have hD1 : 1 ≤ D := le_max_right _ _
  set Cp : ℝ := max C₁ 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  refine ⟨64 * refMass * Cp * D, by have := refMass_pos; positivity, ?_⟩
  intro τ hτ hτ1 P hP w φ hφ M hM
  have hφc : Continuous φ := hφ.1
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  rcases hM0.lt_or_eq with hMpos | hMeq
  swap
  · -- `M = 0`: the test is constant and the variance vanishes.
    have hconst : ∀ r, φ r = ∫ r', φ r' := fun r => by
      have := hM r; rw [← hMeq] at this
      exact sub_eq_zero.mp (abs_nonpos_iff.mp this)
    have hzero : ∀ ν : MassProfile, varMark φ ν = 0 := by
      intro ν
      unfold varMark
      have : (∫ r, φ r ∂(ν : Measure Torus)) = ∫ r', φ r' := by
        rw [integral_congr_ae (Eventually.of_forall hconst)]
        simp
      rw [this, sub_self, abs_zero]; norm_num
    rw [markVariance_eq_weightFunctional]
    unfold weightFunctional
    simp only [hzero, mul_zero, ENNReal.ofReal_zero, lintegral_zero]
    exact bot_le
  set ε : ℝ := min 1 (D * τ) with hε
  have hε0 : 0 < ε := lt_min zero_lt_one (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hstat := stationary_of_criticalLimit hτ hE hP
  -- Step 1: the reference window at the limit.
  have hstep1 : weightFunctional P (varMark φ) refWeight ≤
      ENNReal.ofReal (16 * M ^ 2 * Cp * ε ^ (1 - η)) := by
    obtain ⟨s, R, σ, hσ, hlim⟩ := hP
    set rj : ℕ → ℝ := fun j => r (s.n (σ j)) (s.W (σ j)) with hrj
    set gd : ℕ → ℝ := fun j => gridDefect (s.parameters b hb hb' (σ j)) φ with hgd
    have hrj0 : Tendsto rj atTop (𝓝 0) := (hr τ s hτ).comp hσ.tendsto_atTop
    have hgd0 : Tendsto gd atTop (𝓝 0) :=
      (gridDefect_tendsto s hτ b hb hb' φ hφc).comp hσ.tendsto_atTop
    have hrest : Tendsto (fun j => 8 * M ^ 2 * rj j + 2 * gd j ^ 2 * (2 * Cp + rj j))
        atTop (𝓝 0) := by
      have := ((hrj0.const_mul (8 * M ^ 2)).add
        (((hgd0.pow 2).const_mul 2).mul ((tendsto_const_nhds (x := 2 * Cp)).add hrj0)))
      simpa using this
    refine markedLimit_lintegral_le s R σ P hlim
      (continuous_prodTest continuous_refWeight (continuous_varMark hφc))
      (hasCompactSupport_prodTest hasCompactSupport_refWeight _)
      (prodTest_nonneg refWeight_nonneg (varMark_nonneg φ)) _ _ hrest ?_
    have hW : Tendsto (fun j => (s.W j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp s.width_tendsto
    have hWτ : ∀ᶠ j in atTop, 1 / ((s.W j : ℝ) + 1) ≤ τ := by
      have h := (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 hW)).eventually
        (eventually_le_nhds hτ)
      filter_upwards [h] with j hj
      simpa [one_div] using hj
    have hev := hσ.tendsto_atTop.eventually
      ((critical_eventually s hτ b hb hb' (by linarith : τ < 2) 0).and hWτ)
    filter_upwards [hev] with j hj
    obtain ⟨⟨hj1, hj2, _, hj4⟩, hj5⟩ := hj
    set p : Parameters := s.parameters b hb hb' (σ j) with hp
    have hn : (0 : ℝ) < s.n (σ j) := by
      exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) (s.n_ge_four (σ j)))
    have hWj : (0 : ℝ) < s.W (σ j) := by exact_mod_cast s.W_pos (σ j)
    have hnW : (s.n (σ j) : ℝ) ≤ 2 * s.W (σ j) := by
      rw [div_lt_iff₀ hWj] at hj1; linarith
    set t : ℝ := (s.n (σ j) : ℝ) / s.W (σ j) with ht
    have ht0 : 0 ≤ t := div_nonneg hn.le hWj.le
    have ht32 : t ^ (3 / 2 : ℝ) ≤ 3 * τ := by
      calc t ^ (3 / 2 : ℝ) ≤ (2 * τ) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow ht0 hj2.le (by norm_num)
        _ = (2 : ℝ) ^ (3 / 2 : ℝ) * τ ^ (3 / 2 : ℝ) := Real.mul_rpow (by norm_num) hτ.le
        _ ≤ 3 * τ ^ (1 : ℝ) := by
            apply mul_le_mul two_rpow_three_halves_le
              (Real.rpow_le_rpow_of_exponent_ge hτ hτ1 (by norm_num)) (by positivity)
              (by norm_num)
        _ = 3 * τ := by rw [Real.rpow_one]
    have hmean : ∀ α, IsBulkRank p ϑ α →
        ∫ H, varObservable p φ M α H ∂((R (σ j)).model.law : Measure p.SiteMatrix) ≤ ε := by
      intro α hα
      have hque := physical_site_test_bound (constructSpectralRealization p (R (σ j)).model) α
        (siteTest p φ M) (siteTest_abs_le hMpos hM)
        (Cm * ((s.n (σ j) : ℝ) / s.W (σ j) + ((s.n (σ j) : ℝ) / s.W (σ j)) ^ (3 / 2 : ℝ)))
        (by positivity) (fun m hm =>
          (hCm (s.n (σ j)) (s.W (σ j)) (s.n_ge_four (σ j)) (s.W_pos (σ j)) hnW
            (R (σ j)).model α hα m hm).2)
      refine (integral_varObservable_le _ hMpos hM α).trans (min_le_min le_rfl ?_)
      refine hque.trans ?_
      change Cm * (t + t ^ (3 / 2 : ℝ)) + 1 / ((s.W (σ j) : ℝ) + 1) ≤ D * τ
      calc Cm * (t + t ^ (3 / 2 : ℝ)) + 1 / ((s.W (σ j) : ℝ) + 1) ≤
            Cm * (2 * τ + 3 * τ) + τ := by
            gcongr
        _ = (5 * Cm + 1) * τ := by ring
        _ ≤ D * τ := mul_le_mul_of_nonneg_right (le_max_left _ _) hτ.le
    have hwinA := hWTb (s.n (σ j)) (s.W (σ j)) (s.n_ge_four (σ j)) (s.W_pos (σ j)) hnW
      (R (σ j)).model ε hε0 hε1 (varObservable p φ M) (measurable_varObservable φ M)
      (varObservable_mem φ M) (varObservable_shift φ M) hmean
    have hwinB := hWTb (s.n (σ j)) (s.W (σ j)) (s.n_ge_four (σ j)) (s.W_pos (σ j)) hnW
      (R (σ j)).model 1 zero_lt_one le_rfl (fun _ _ => (1 : ℝ)) (fun _ => measurable_const)
      (fun _ _ => ⟨zero_le_one, le_rfl⟩) (fun _ _ _ => rfl) (fun α _ => by simp)
    have hbridge := lintegral_le_windowExpectation_two (R (σ j)).model E continuous_refWeight
      hasCompactSupport_refWeight refWeight_nonneg (varObservable p φ M) (fun _ _ => (1 : ℝ))
      (measurable_varObservable φ M) (varObservable_mem φ M) (fun _ => measurable_const)
      (fun _ _ => ⟨zero_le_one, le_rfl⟩) (by positivity : (0 : ℝ) ≤ 8 * M ^ 2)
      (by positivity : (0 : ℝ) ≤ 2 * gridDefect p φ ^ 2) (varMark_le_ae _ hMpos hM)
    refine hbridge.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hqe] at hwinA hwinB
    rw [Real.one_rpow, mul_one] at hwinB
    have ha0 : 0 ≤ countScale (s.n (σ j)) (s.W (σ j)) / Real.sqrt (s.n (σ j)) := by
      unfold countScale
      have : 0 ≤ Real.log (2 * (s.W (σ j) : ℝ)) :=
        Real.log_nonneg (by have : (1 : ℝ) ≤ s.W (σ j) := by exact_mod_cast s.W_pos (σ j)
                            linarith)
      positivity
    have hCa : ∀ e : ℝ, 0 ≤ e →
        C₁ * (countScale (s.n (σ j)) (s.W (σ j)) / Real.sqrt (s.n (σ j))) * e ≤ 2 * Cp * e := by
      intro e he
      apply mul_le_mul_of_nonneg_right _ he
      calc C₁ * _ ≤ Cp * (countScale (s.n (σ j)) (s.W (σ j)) / Real.sqrt (s.n (σ j))) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) ha0
        _ ≤ Cp * 2 := mul_le_mul_of_nonneg_left hj4 hCp0
        _ = 2 * Cp := by ring
    have hA : windowExpectation p (R (σ j)).model E (Parameters.semicircleDensity E) refWeight
        (varObservable p φ M) ≤ 2 * Cp * ε ^ (1 - η) + r (s.n (σ j)) (s.W (σ j)) :=
      le_trans hwinA (by linarith [hCa (ε ^ (1 - η)) (Real.rpow_nonneg hε0.le _)])
    have hB : windowExpectation p (R (σ j)).model E (Parameters.semicircleDensity E) refWeight
        (fun _ _ => (1 : ℝ)) ≤ 2 * Cp + rj j := by
      have := hCa 1 zero_le_one
      rw [mul_one, mul_one] at this
      exact le_trans hwinB (by linarith)
    have hM2 : 0 ≤ 8 * M ^ 2 := by positivity
    have hg2 : 0 ≤ 2 * gridDefect p φ ^ 2 := by positivity
    calc 8 * M ^ 2 * windowExpectation p (R (σ j)).model E (Parameters.semicircleDensity E)
          refWeight (varObservable p φ M) +
        2 * gridDefect p φ ^ 2 * windowExpectation p (R (σ j)).model E
          (Parameters.semicircleDensity E) refWeight (fun _ _ => (1 : ℝ)) ≤
        8 * M ^ 2 * (2 * Cp * ε ^ (1 - η) + r (s.n (σ j)) (s.W (σ j))) +
          2 * gridDefect p φ ^ 2 * (2 * Cp + rj j) := by
          gcongr
      _ = 16 * M ^ 2 * Cp * ε ^ (1 - η) +
          (8 * M ^ 2 * rj j + 2 * gd j ^ 2 * (2 * Cp + rj j)) := by
          simp only [hrj, hgd]; ring
  -- Step 2: uniformity in the weight.
  have hstep2 : weightFunctional P (varMark φ) w ≤
      4 * (ENNReal.ofReal refMass * weightFunctional P (varMark φ) refWeight) := by
    have h4 := weightFunctional_le_four P hstat (continuous_varMark hφc) (varMark_nonneg φ)
      continuous_refPsi hasCompactSupport_refPsi refPsi_nonneg refPsi_ge_one
      w.toContinuousMap.continuous w.compactSupport w.nonnegative w.integral_eq_one
    have hpsi : weightFunctional P (varMark φ) refPsi =
        ENNReal.ofReal refMass * weightFunctional P (varMark φ) refWeight := by
      rw [← weightFunctional_const_mul P _ _ refMass_pos.le]
      congr 1
      funext u
      exact refPsi_eq u
    rw [hpsi] at h4
    exact h4
  -- Step 3: algebra.
  rw [markVariance_eq_weightFunctional]
  refine hstep2.trans ?_
  have halg : 4 * (refMass * (16 * M ^ 2 * Cp * ε ^ (1 - η))) ≤
      64 * refMass * Cp * D * M ^ 2 * τ ^ (1 - η) := by
    have hmr := min_rpow_le hD1 hτ.le hη hη1
    have hmr' : (min 1 (D * τ)) ^ (1 - η) ≤ D * τ ^ (1 - η) :=
      hmr.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith))
    have hm0 : 0 ≤ 64 * refMass * Cp * M ^ 2 := by have := refMass_pos; positivity
    calc 4 * (refMass * (16 * M ^ 2 * Cp * ε ^ (1 - η))) =
          (64 * refMass * Cp * M ^ 2) * ε ^ (1 - η) := by ring
      _ ≤ (64 * refMass * Cp * M ^ 2) * (D * τ ^ (1 - η)) :=
          mul_le_mul_of_nonneg_left hmr' hm0
      _ = _ := by ring
  calc 4 * (ENNReal.ofReal refMass * weightFunctional P (varMark φ) refWeight) ≤
        4 * (ENNReal.ofReal refMass * ENNReal.ofReal (16 * M ^ 2 * Cp * ε ^ (1 - η))) := by
        gcongr
    _ = ENNReal.ofReal (4 * (refMass * (16 * M ^ 2 * Cp * ε ^ (1 - η)))) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
          ENNReal.ofReal_mul refMass_pos.le]
        norm_num
    _ ≤ _ := ENNReal.ofReal_le_ofReal halg

end BlockBand.Window.SmallCritical
