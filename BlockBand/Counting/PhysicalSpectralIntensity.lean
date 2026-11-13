module
public import BlockBand.Counting.FiniteSpectralIntensity
public import BlockBand.Counting.PhysicalFactorialConsequences
public import BlockBand.QUE.Fourier.PhysicalWeightedMass

/-!
# Expected unfolded spectral intensity of the physical Gaussian ring

The expected intensity of the unfolded spectrum of the deformed physical Gaussian ring is a
finite measure of total mass `N`, bounded by `𝕂` times Lebesgue measure.  Hence expected
unfolded spectral sums `E ∑ f(N ρ (λ_α - E))` are bounded by `𝕂 ‖f‖_{L¹}`, for every
spectral realization of the model.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory Set BlockBand.Counting BlockBand.External.PSSS
open scoped ENNReal NNReal

def GaussianRingModel.physicalSpectralIntensity {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : HermitianMatrix p.Site) (E rho : ℝ) : Measure ℝ :=
  finiteSpectralIntensity (model.law : Measure p.SiteMatrix)
    (p.physicalUnfoldedEigenvalue A E rho)

theorem GaussianRingModel.physicalSpectralIntensity_isFiniteMeasure {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : HermitianMatrix p.Site) (E rho : ℝ) :
    IsFiniteMeasure (model.physicalSpectralIntensity A E rho) := by
  unfold physicalSpectralIntensity
  infer_instance
attribute [instance] GaussianRingModel.physicalSpectralIntensity_isFiniteMeasure

theorem GaussianRingModel.physicalSpectralIntensity_univ {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : HermitianMatrix p.Site) (E rho : ℝ) :
    model.physicalSpectralIntensity A E rho univ = (p.N : ℝ≥0∞) := by
  simpa [physicalSpectralIntensity, Site, N] using finiteSpectralIntensity_univ
    (model.law : Measure p.SiteMatrix) (p.physicalUnfoldedEigenvalue A E rho)
    (p.measurable_physicalUnfoldedEigenvalue A E rho)

theorem GaussianRingModel.physicalSpectralIntensity_Icc {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : HermitianMatrix p.Site) (E rho a b : ℝ) :
    model.physicalSpectralIntensity A E rho (Icc a b) =
      ENNReal.ofReal (∫ H, (p.physicalUnfoldedIntervalCount A E rho a b H : ℝ)
        ∂(model.law : Measure p.SiteMatrix)) := by
  exact finiteSpectralIntensity_apply_eq_ofReal_integral _ _
    (p.measurable_physicalUnfoldedEigenvalue A E rho) _ measurableSet_Icc

/-- The finite unfolded intensity is at most `𝕂` times Lebesgue measure. -/
theorem GaussianRingModel.physicalSpectralIntensity_le_volume {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (source : SourceContract.{0})
    (A : HermitianMatrix p.Site) (E rho : ℝ) (hrho : 0 < rho) :
    model.physicalSpectralIntensity A E rho ≤
      ENNReal.ofReal (source.C / (Real.sqrt p.c * rho)) • (volume : Measure ℝ) := by
  apply finiteSpectralIntensity_le_volume_of_expectedCount_le _ _
    (p.measurable_physicalUnfoldedEigenvalue A E rho)
    (p.physicalUnfoldedConstant source rho) (p.physicalUnfoldedConstant_pos source hrho).le
  intro a b hab
  simpa [factorialCount, physicalUnfoldedIntervalCount, eigenvalueCount,
    finiteSpectralCount] using
    model.physicalUnfoldedIntervalCount_factorialBound source A E rho hrho a b hab 1 (by omega)

/-- Every Lebesgue L¹ test is integrable for the intensity. -/
theorem GaussianRingModel.integrable_physicalSpectralIntensity {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (source : SourceContract.{0})
    (A : HermitianMatrix p.Site) (E rho : ℝ) (hrho : 0 < rho)
    (f : ℝ → ℝ) (hf : Integrable f (volume : Measure ℝ)) :
    Integrable f (model.physicalSpectralIntensity A E rho) :=
  (hf.smul_measure ENNReal.ofReal_ne_top).mono_measure
    (model.physicalSpectralIntensity_le_volume source A E rho hrho)

/-- Integrating against the intensity gives the expected spectral sum. -/
theorem GaussianRingModel.integral_physicalSpectralIntensity {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : HermitianMatrix p.Site) (E rho : ℝ)
    (f : ℝ → ℝ) (hf : Integrable f (model.physicalSpectralIntensity A E rho)) :
    ∫ x, f x ∂model.physicalSpectralIntensity A E rho =
      ∫ H, ∑ i : Fin (Fintype.card p.Site), f (p.physicalUnfoldedEigenvalue A E rho H i)
        ∂(model.law : Measure p.SiteMatrix) :=
  integral_finiteSpectralIntensity _ _ (p.measurable_physicalUnfoldedEigenvalue A E rho) f hf

/-- Expected absolute spectral sum is bounded by the Lebesgue L¹ norm. -/
theorem GaussianRingModel.physicalSpectralSum_abs_le {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (source : SourceContract.{0})
    (A : HermitianMatrix p.Site) (E rho : ℝ) (hrho : 0 < rho)
    (f : ℝ → ℝ) (hf : Integrable f (volume : Measure ℝ)) :
    (∫ H, ∑ i : Fin (Fintype.card p.Site), |f (p.physicalUnfoldedEigenvalue A E rho H i)|
      ∂(model.law : Measure p.SiteMatrix)) ≤
      (source.C / (Real.sqrt p.c * rho)) * ∫ x, |f x| ∂(volume : Measure ℝ) := by
  have ha : Integrable (fun x => |f x|) (volume : Measure ℝ) := hf.abs
  rw [← model.integral_physicalSpectralIntensity A E rho (fun x => |f x|)
    (model.integrable_physicalSpectralIntensity source A E rho hrho _ ha)]
  have h := integral_mono_measure (model.physicalSpectralIntensity_le_volume source A E rho hrho)
    (Filter.Eventually.of_forall fun x => abs_nonneg (f x))
    (ha.smul_measure ENNReal.ofReal_ne_top)
  have hK : 0 ≤ source.C / (Real.sqrt p.c * rho) :=
    (p.physicalUnfoldedConstant_pos source hrho).le
  rw [integral_smul_measure, ENNReal.toReal_ofReal hK] at h
  exact h

/-- Every spectral realization has the same expected unfolded spectral sums.
Only the Hermitian support and uniqueness of the ordered spectrum are used. -/
theorem GaussianRingModel.spectralSum_eq_physicalSpectralSum {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (spectral : p.SpectralRealization model)
    (E : ℝ) (g : ℝ → ℝ) :
    (∫ H, ∑ α : Fin p.N, g (spectral.unfoldedEigenvalue E H α)
      ∂(model.law : Measure p.SiteMatrix)) =
    ∫ H, ∑ i : Fin (Fintype.card p.Site),
      g (p.physicalUnfoldedEigenvalue ⟨0, Matrix.isHermitian_zero⟩ E (semicircleDensity E) H i)
      ∂(model.law : Measure p.SiteMatrix) := by
  apply integral_congr_ae
  filter_upwards [model.isPhysical.1,
    BlockBand.QUE.Fourier.spectral_eigenvalue_eq_canonical_ae spectral] with H hH heig
  have hloc (α : Fin p.N) : spectral.unfoldedEigenvalue E H α =
      p.physicalUnfoldedEigenvalue ⟨0, Matrix.isHermitian_zero⟩ E (semicircleDensity E) H
        (BlockBand.Model.Construction.physicalSpectralRank p α) := by
    rw [SpectralRealization.unfoldedEigenvalue, heig α]
    unfold BlockBand.Model.Construction.physicalOrderedEigenvalue
    rw [BlockBand.Model.Construction.rawIncreasingEigenvalue_eq _ H hH]
    rw [p.physicalUnfoldedEigenvalue_eq ⟨0, Matrix.isHermitian_zero⟩ E (semicircleDensity E) H hH]
    simp
  simp_rw [hloc]
  let e : Fin p.N ≃ Fin (Fintype.card p.Site) :=
    { toFun := BlockBand.Model.Construction.physicalSpectralRank p
      invFun := Fin.cast (BlockBand.Model.Construction.physicalSite_card p)
      left_inv := by intro i; apply Fin.ext; rfl
      right_inv := by intro i; apply Fin.ext; rfl }
  exact Equiv.sum_comp e
    (fun i => g (p.physicalUnfoldedEigenvalue ⟨0, Matrix.isHermitian_zero⟩ E (semicircleDensity E) H i))

/-- L¹ absolute sum bound for every physical spectral realization. -/
theorem GaussianRingModel.spectralSum_abs_le {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (source : SourceContract.{0})
    (spectral : p.SpectralRealization model) (E : ℝ) (hrho : 0 < semicircleDensity E)
    (f : ℝ → ℝ) (hf : Integrable f (volume : Measure ℝ)) :
    (∫ H, ∑ α : Fin p.N, |f (spectral.unfoldedEigenvalue E H α)|
      ∂(model.law : Measure p.SiteMatrix)) ≤
      (source.C / (Real.sqrt p.c * semicircleDensity E)) * ∫ x, |f x| ∂(volume : Measure ℝ) := by
  rw [model.spectralSum_eq_physicalSpectralSum spectral E (fun x => |f x|)]
  exact model.physicalSpectralSum_abs_le source ⟨0, Matrix.isHermitian_zero⟩ E (semicircleDensity E) hrho f hf

/-- Nonnegative L¹ spectral test bound used in the weighted marked assembly. -/
theorem GaussianRingModel.spectralSum_nonneg_le {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (source : SourceContract.{0})
    (spectral : p.SpectralRealization model) (E : ℝ) (hrho : 0 < semicircleDensity E)
    (g : ℝ → ℝ) (hg : Integrable g (volume : Measure ℝ)) (hnonneg : ∀ x, 0 ≤ g x) :
    (∫ H, ∑ α : Fin p.N, g (spectral.unfoldedEigenvalue E H α)
      ∂(model.law : Measure p.SiteMatrix)) ≤
      (source.C / (Real.sqrt p.c * semicircleDensity E)) * ∫ x, g x ∂(volume : Measure ℝ) := by
  simpa only [abs_of_nonneg (hnonneg _)] using
    model.spectralSum_abs_le source spectral E hrho g hg

end BlockBand.Parameters
