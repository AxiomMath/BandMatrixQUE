module

public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.Counting.PhysicalSpectralIntensity

/-!
# The normalized mean empirical measure: mass, PSSS density bound, density uniqueness

Law: the physical Gaussian ring law `model.law` of an arbitrary admissible `p` (`n ≥ 4`, `W ≥ 1`,
`0 < b < 1/2`). `μ = meanEmpiricalMeasure p model = N⁻¹ Σ_i Law(λ_i)` (increasing eigenvalues of
the Hermitian version, multiplicities counted, `N = nW`).

* `meanEmpiricalMeasure_univ`: `μ` has total mass one.
* `meanEmpiricalMeasure_le_volume`: `μ ≤ K_b · Lebesgue` with `K_b = C/√c`, `C` the PSSS
  constant (`PSSS.SourceContract`, first factorial moment, through
  `GaussianRingModel.physicalSpectralIntensity_le_volume` at `E = 0`, `ρ = 1/N`). This is the
  first bound of the smooth-density estimate, uniform in `n, W` for fixed `b`.
* `le_of_withDensity_le_smul_volume`, `eq_of_withDensity_eq_of_pos`: deterministic facts on
  continuous densities on `ℝ` (Lebesgue measure).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open MeasureTheory Set
open BlockBand.Counting BlockBand.External
open scoped ENNReal NNReal

/-- Increasing eigenvalues only depend on the matrix (proof irrelevance after `subst`). -/
theorem increasingEigenvalue_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Foundations.Spectral.increasingEigenvalue hA = Foundations.Spectral.increasingEigenvalue hB := by
  subst h
  rfl

/-- The eigenvalue locations of the mean empirical measure. -/
def physicalEigenvalue (p : Parameters) (H : p.SiteMatrix) (i : Fin (Fintype.card p.Site)) : ℝ :=
  Foundations.Spectral.increasingEigenvalue (p.physicalHermitianVersion H).2 i

theorem measurable_physicalEigenvalue (p : Parameters) (i : Fin (Fintype.card p.Site)) :
    Measurable (fun H => physicalEigenvalue p H i) :=
  (BlockBand.Model.Construction.measurable_increasingEigenvalue i).comp
    p.measurable_physicalHermitianVersion

/-- At `A = 0`, `E = 0`, `ρ = 1/N` the unfolded eigenvalues are the eigenvalues. -/
theorem physicalUnfoldedEigenvalue_zero_inv (p : Parameters) (H : p.SiteMatrix)
    (i : Fin (Fintype.card p.Site)) :
    p.physicalUnfoldedEigenvalue ⟨0, Matrix.isHermitian_zero⟩ 0 ((p.N : ℝ)⁻¹) H i =
      physicalEigenvalue p H i := by
  have hN : (p.N : ℝ) ≠ 0 := by exact_mod_cast p.N_pos.ne'
  unfold Parameters.physicalUnfoldedEigenvalue physicalEigenvalue
  have key : Foundations.Spectral.increasingEigenvalue
      (p.physicalDeformedVersion ⟨0, Matrix.isHermitian_zero⟩ H).2 =
      Foundations.Spectral.increasingEigenvalue (p.physicalHermitianVersion H).2 :=
    increasingEigenvalue_congr (by simp [Parameters.physicalDeformedVersion]) _ _
  rw [key]
  field_simp
  simp

theorem meanEmpiricalMeasure_eq (p : Parameters) (model : p.GaussianRingModel) :
    Internal.Contracts.Inputs.meanEmpiricalMeasure p model =
      (p.N : ℝ≥0∞)⁻¹ • model.physicalSpectralIntensity ⟨0, Matrix.isHermitian_zero⟩ 0
        ((p.N : ℝ)⁻¹) := by
  unfold Internal.Contracts.Inputs.meanEmpiricalMeasure
    Parameters.GaussianRingModel.physicalSpectralIntensity
  congr 2
  funext H i
  exact (physicalUnfoldedEigenvalue_zero_inv p H i).symm

/-- `μ` is a probability measure (total mass `N⁻¹ · N`). -/
theorem meanEmpiricalMeasure_univ (p : Parameters) (model : p.GaussianRingModel) :
    Internal.Contracts.Inputs.meanEmpiricalMeasure p model univ = 1 := by
  rw [meanEmpiricalMeasure_eq, Measure.smul_apply, model.physicalSpectralIntensity_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast p.N_pos.ne') (ENNReal.natCast_ne_top _)

theorem isProbabilityMeasure_meanEmpiricalMeasure (p : Parameters) (model : p.GaussianRingModel) :
    IsProbabilityMeasure (Internal.Contracts.Inputs.meanEmpiricalMeasure p model) :=
  ⟨meanEmpiricalMeasure_univ p model⟩

/-- The PSSS density constant `K_b = C/√c`. -/
def densityBound (source : PSSS.SourceContract.{0}) (b : ℝ) : ℝ :=
  source.C / Real.sqrt (1 - 2 * b)

theorem densityBound_pos (source : PSSS.SourceContract.{0}) {b : ℝ} (hb : b < 1 / 2) :
    0 < densityBound source b :=
  div_pos source.C_pos (Real.sqrt_pos.mpr (by linarith))

/-- First bound of the smooth-density estimate: `μ ≤ K_b · Lebesgue`, for every admissible `p` and
realization; `K_b` depends only on `b` and the PSSS constant. Uses `PSSS.SourceContract`. -/
theorem meanEmpiricalMeasure_le_volume (source : PSSS.SourceContract.{0}) (p : Parameters)
    (model : p.GaussianRingModel) :
    Internal.Contracts.Inputs.meanEmpiricalMeasure p model ≤
      ENNReal.ofReal (densityBound source p.b) • (volume : Measure ℝ) := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have h := model.physicalSpectralIntensity_le_volume source ⟨0, Matrix.isHermitian_zero⟩ 0
    ((p.N : ℝ)⁻¹) (inv_pos.mpr hN)
  rw [meanEmpiricalMeasure_eq]
  refine (show (p.N : ℝ≥0∞)⁻¹ • model.physicalSpectralIntensity ⟨0, Matrix.isHermitian_zero⟩ 0
      ((p.N : ℝ)⁻¹) ≤ (p.N : ℝ≥0∞)⁻¹ • (ENNReal.ofReal (source.C / (Real.sqrt p.c * (p.N : ℝ)⁻¹)) •
        (volume : Measure ℝ)) from Measure.le_iff'.mpr fun s => ?_).trans_eq ?_
  · simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (h s) _
  rw [smul_smul]
  congr 1
  have hc : 0 < Real.sqrt p.c := Real.sqrt_pos.mpr p.c_pos
  have he : source.C / (Real.sqrt p.c * (p.N : ℝ)⁻¹) =
      (p.N : ℝ) * densityBound source p.b := by
    unfold densityBound
    change source.C / (Real.sqrt p.c * (p.N : ℝ)⁻¹) = (p.N : ℝ) * (source.C / Real.sqrt p.c)
    field_simp
  rw [he, ENNReal.ofReal_mul hN.le, ENNReal.ofReal_natCast, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast p.N_pos.ne') (ENNReal.natCast_ne_top _), one_mul]

/-- A continuous density of a measure dominated by `K · Lebesgue` is at most `K`
everywhere (deterministic, Lebesgue measure on `ℝ`). -/
theorem le_of_withDensity_le_smul_volume {ρ : ℝ → ℝ} (hρ : Continuous ρ) {K : ℝ} (hK : 0 ≤ K)
    (h : volume.withDensity (fun e => ENNReal.ofReal (ρ e)) ≤
      ENNReal.ofReal K • (volume : Measure ℝ)) (e : ℝ) : ρ e ≤ K := by
  have hae : (fun e => ENNReal.ofReal (ρ e)) ≤ᵐ[volume] fun _ => ENNReal.ofReal K := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (ENNReal.measurable_ofReal.comp hρ.measurable)
    intro s hs _
    have h1 := h s
    rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul] at h1
    rw [setLIntegral_const]
    exact h1
  by_contra hlt
  push Not at hlt
  have hU : IsOpen {e | K < ρ e} := isOpen_lt continuous_const hρ
  have hne : ({e | K < ρ e} : Set ℝ).Nonempty := ⟨e, hlt⟩
  have hpos := hU.measure_pos (volume : Measure ℝ) hne
  have hnull : volume {e | K < ρ e} = 0 := by
    rw [← nonpos_iff_eq_zero]
    refine (measure_mono_ae ?_).trans_eq (measure_empty (μ := volume))
    filter_upwards [hae] with x hx hxU
    exact absurd ((ENNReal.ofReal_le_ofReal_iff hK).mp hx) (not_le.mpr hxU)
  exact hpos.ne' hnull

/-- Two continuous densities of the same measure on `ℝ`, one of them strictly positive,
coincide everywhere (deterministic, Lebesgue measure). -/
theorem eq_of_withDensity_eq_of_pos {ρ ρ' : ℝ → ℝ} (hρ : Continuous ρ) (hρ' : Continuous ρ')
    (hpos : ∀ e, 0 < ρ' e)
    (h : volume.withDensity (fun e => ENNReal.ofReal (ρ e)) =
      volume.withDensity (fun e => ENNReal.ofReal (ρ' e))) : ρ = ρ' := by
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (ENNReal.measurable_ofReal.comp hρ.measurable).aemeasurable
    (ENNReal.measurable_ofReal.comp hρ'.measurable).aemeasurable).mp h
  have heq : (fun e => ENNReal.ofReal (ρ e)) = fun e => ENNReal.ofReal (ρ' e) :=
    (Continuous.ae_eq_iff_eq (μ := volume) (ENNReal.continuous_ofReal.comp hρ)
      (ENNReal.continuous_ofReal.comp hρ')).mp hae
  funext e
  have he := congrFun heq e
  have h0 : 0 < ENNReal.ofReal (ρ e) := by rw [he]; exact ENNReal.ofReal_pos.mpr (hpos e)
  exact (ENNReal.ofReal_eq_ofReal_iff (ENNReal.ofReal_pos.mp h0).le (hpos e).le).mp he

end BlockBand.Density
