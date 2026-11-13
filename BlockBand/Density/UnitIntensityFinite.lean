module

public import BlockBand.Density.Smooth
public import BlockBand.Density.WeakLimitMean
public import BlockBand.Counting.SimpleSpectralLimitsPhysical
public import BlockBand.Counting.SimpleSpectralLimitsTopology

/-!
# Finite-`(n,W)` first and second spectral moments of the marked law

The last display of the proof of the critical density theorem. Law: the marked law
`R.markedLaw E` of an arbitrary finite realization `R` of an admissible `p`, bulk energy with
`ρ(E) > 0`. For `g ∈ C_c(ℝ)` and `F_g(ξ) = ∫ g dξ_spec`:
* `integral_spectralTest_markedLaw`: `E F_g = N ∫ ρ_{n,W}(x) g(Nρ(E)(x-E)) dx`
  (`ρ_{n,W} = meanDensity`), exact, no estimate;
* `spectralTest_sq_bound`: if `|g| ≤ B` and `g = 0` off `[-L,L]`, `F_g²` is integrable and
  `E F_g² ≤ B² ((K·2L)² + K·2L)`, `K = C/(√c ρ(E))` with `C` the PSSS constant (factorial
  moments of orders 1 and 2; `PSSS.SourceContract`). Uniform in `n, W` for fixed `b, E`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open MeasureTheory Set Filter BlockBand.Counting BlockBand.External
open scoped ENNReal NNReal Topology

/-- The spectral test `F_g(ξ) = ∫ g dξ_spec`. -/
def spectralTest (g : CompactlySupportedContinuousMap ℝ ℝ) (ξ : MarkedPointMeasure) : ℝ :=
  ∫ x, g x ∂ξ.spectral.measure

theorem continuous_spectralTest (g : CompactlySupportedContinuousMap ℝ ℝ) :
    Continuous (spectralTest g) := by
  have h1 : Continuous (fun σ : VaguePointMeasure ℝ =>
      fun f : CompactlySupportedContinuousMap ℝ ℝ => σ.coordinate f) := continuous_induced_dom
  exact (continuous_apply g).comp (h1.comp continuous_markedSpectralProjection)

theorem physicalUnfoldedEigenvalue_zero (p : Parameters) (E rho : ℝ) (H : p.SiteMatrix)
    (i : Fin (Fintype.card p.Site)) :
    p.physicalUnfoldedEigenvalue ⟨0, Matrix.isHermitian_zero⟩ E rho H i =
      (p.N : ℝ) * rho * (physicalEigenvalue p H i - E) := by
  have key : Foundations.Spectral.increasingEigenvalue
      (p.physicalDeformedVersion ⟨0, Matrix.isHermitian_zero⟩ H).2 =
      Foundations.Spectral.increasingEigenvalue (p.physicalHermitianVersion H).2 :=
    increasingEigenvalue_congr (by simp [Parameters.physicalDeformedVersion]) _ _
  unfold Parameters.physicalUnfoldedEigenvalue physicalEigenvalue
  rw [key]

theorem spectralTest_markedConfig_ae {p : Parameters} (R : FiniteRealization p) (E : ℝ)
    (g : CompactlySupportedContinuousMap ℝ ℝ) :
    ∀ᵐ H ∂(R.model.law : Measure p.SiteMatrix),
      spectralTest g (R.spectral.markedConfig E H) =
        ∑ α : Fin p.N, g (R.spectral.unfoldedEigenvalue E H α) := by
  let : MeasurableSingletonClass MassProfile :=
    Model.Construction.massProfile_measurableSingletonClass
  filter_upwards [R.spectral.markedConfig_ae E] with H hH
  unfold spectralTest
  rw [(R.spectral.markedConfig E H).spectral_eq,
    integral_map (φ := Prod.fst) (f := fun x : ℝ => g x) measurable_fst.aemeasurable
      g.continuous.aestronglyMeasurable, hH,
    integral_finsetSum_measure (fun _ _ => integrable_dirac (by simp))]
  simp only [integral_dirac]
  rfl

/-- **Exact mean of a spectral test** (before the limit). -/
theorem integral_spectralTest_markedLaw {p : Parameters} (R : FiniteRealization p) (E : ℝ)
    (g : CompactlySupportedContinuousMap ℝ ℝ) :
    ∫ ξ, spectralTest g ξ ∂(R.markedLaw E : Measure MarkedPointMeasure) =
      (p.N : ℝ) * ∫ x, meanDensity p R.model x *
        g ((p.N : ℝ) * Parameters.semicircleDensity E * (x - E)) := by
  have hlaw : (R.markedLaw E : Measure MarkedPointMeasure) =
      Measure.map (R.spectral.markedConfig E) (R.model.law : Measure p.SiteMatrix) := rfl
  rw [hlaw, integral_map (R.spectral.measurable_markedConfig E).aemeasurable
    (continuous_spectralTest g).aestronglyMeasurable,
    integral_congr_ae (spectralTest_markedConfig_ae R E g),
    R.model.spectralSum_eq_physicalSpectralSum R.spectral E g]
  simp_rw [physicalUnfoldedEigenvalue_zero]
  set G : ℝ → ℝ := fun x => g ((p.N : ℝ) * Parameters.semicircleDensity E * (x - E)) with hG
  have hGc : Continuous G := g.continuous.comp (by fun_prop)
  obtain ⟨B, hB⟩ := g.continuous.bounded_above_of_compact_support g.hasCompactSupport
  have hGint : ∀ (Q : Measure ℝ) [IsFiniteMeasure Q], Integrable G Q := fun Q _ =>
    (integrable_const B).mono' hGc.aestronglyMeasurable
      (Eventually.of_forall fun x => hB _)
  -- the mean-measure integral
  have hμ := congrArg (fun m : Measure ℝ => ∫ x, G x ∂m) (meanEmpiricalMeasure_eq_withDensity p R.model)
  have hden : (fun e => ENNReal.ofReal (meanDensity p R.model e)) =
      fun e => (((meanDensity p R.model e).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hden, integral_withDensity_eq_integral_smul (f := fun e => (meanDensity p R.model e).toNNReal)
    (measurable_real_toNNReal.comp (contDiff_meanDensity p R.model).continuous.measurable) G] at hμ
  have hsm : ∀ x, (meanDensity p R.model x).toNNReal • G x = meanDensity p R.model x * G x := by
    intro x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (meanDensity_pos p R.model x).le, smul_eq_mul]
  simp_rw [hsm] at hμ
  rw [← hμ]
  unfold Internal.Contracts.Inputs.meanEmpiricalMeasure
  have hI := integral_finiteSpectralIntensity (R.model.law : Measure p.SiteMatrix)
    (fun H i => physicalEigenvalue p H i) (fun i => measurable_physicalEigenvalue p i) G (hGint _)
  simp only [physicalEigenvalue] at hI ⊢
  rw [integral_smul_measure, hI]
  have hN : (p.N : ℝ) ≠ 0 := by exact_mod_cast p.N_pos.ne'
  rw [smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ← mul_assoc, mul_inv_cancel₀ hN,
    one_mul]

theorem natCast_sq_eq_descFactorial (n : ℕ) :
    (n : ℝ) ^ 2 = (n.descFactorial 2 : ℝ) + (n.descFactorial 1 : ℝ) := by
  rw [Nat.descFactorial_one, show (2 : ℕ) = 1 + 1 from rfl, Nat.descFactorial_succ,
    Nat.descFactorial_one]
  rcases n with _ | k
  · simp
  · rw [Nat.add_sub_cancel]
    push_cast
    ring

/-- **Uniform second moment of a spectral test** (the "exponential count bound" at order 2).
Uses `PSSS.SourceContract`. -/
theorem spectralTest_sq_bound (source : PSSS.SourceContract.{0}) {p : Parameters}
    (R : FiniteRealization p) (E : ℝ) (hρ : 0 < Parameters.semicircleDensity E)
    (g : CompactlySupportedContinuousMap ℝ ℝ) {B L : ℝ} (hB : ∀ x, |g x| ≤ B) (hL : 0 ≤ L)
    (hsupp : ∀ x, x ∉ Icc (-L) L → g x = 0) :
    Integrable (fun ξ => spectralTest g ξ ^ 2) (R.markedLaw E : Measure MarkedPointMeasure) ∧
      ∫ ξ, spectralTest g ξ ^ 2 ∂(R.markedLaw E : Measure MarkedPointMeasure) ≤
        B ^ 2 * ((p.physicalUnfoldedConstant source (Parameters.semicircleDensity E) * (2 * L)) ^ 2 +
          p.physicalUnfoldedConstant source (Parameters.semicircleDensity E) * (2 * L)) := by
  set ρ := Parameters.semicircleDensity E
  set K := p.physicalUnfoldedConstant source ρ
  set count := p.physicalUnfoldedIntervalCount ⟨0, Matrix.isHermitian_zero⟩ E ρ (-L) L
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hlaw : (R.markedLaw E : Measure MarkedPointMeasure) =
      Measure.map (R.spectral.markedConfig E) (R.model.law : Measure p.SiteMatrix) := rfl
  -- pointwise bound
  have hpt : ∀ᵐ H ∂(R.model.law : Measure p.SiteMatrix),
      spectralTest g (R.spectral.markedConfig E H) ^ 2 ≤
        B ^ 2 * ((count H).descFactorial 2 + (count H).descFactorial 1 : ℝ) := by
    filter_upwards [finiteRealization_spectral_Icc_count_ae R E (-L) L] with H hH
    set σ := (R.spectral.markedConfig E H).spectral.measure
    have hfin : σ (Icc (-L) L) < ⊤ :=
      (R.spectral.markedConfig E H).spectral.finite_on_compact _ isCompact_Icc
    have : IsFiniteMeasure (σ.restrict (Icc (-L) L)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
    have hind : Integrable ((Icc (-L) L).indicator fun _ => B) σ :=
      (integrable_indicator_iff measurableSet_Icc).mpr (integrable_const B)
    have h1 : |spectralTest g (R.spectral.markedConfig E H)| ≤ B * (count H : ℝ) := by
      unfold spectralTest
      have := norm_integral_le_of_norm_le hind (Eventually.of_forall fun x => by
        by_cases hx : x ∈ Icc (-L) L
        · rw [indicator_of_mem hx, Real.norm_eq_abs]; exact hB x
        · rw [indicator_of_notMem hx, hsupp x hx, norm_zero])
      rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, Real.norm_eq_abs] at this
      have hr : σ.real (Icc (-L) L) = (count H : ℝ) := by
        rw [measureReal_def, hH, ENNReal.toReal_natCast]
      rw [hr] at this
      linarith
    rw [← natCast_sq_eq_descFactorial]
    calc spectralTest g (R.spectral.markedConfig E H) ^ 2 ≤ (B * (count H : ℝ)) ^ 2 := by
          have := abs_le.mp h1
          nlinarith [abs_nonneg (spectralTest g (R.spectral.markedConfig E H)),
            sq_abs (spectralTest g (R.spectral.markedConfig E H))]
      _ = B ^ 2 * (count H : ℝ) ^ 2 := by ring
  have hi1 : Integrable (fun H => ((count H).descFactorial 1 : ℝ))
      (R.model.law : Measure p.SiteMatrix) :=
    R.model.physicalUnfoldedIntervalCount_integrable ⟨0, Matrix.isHermitian_zero⟩ E ρ (-L) L 1
  have hi2 : Integrable (fun H => ((count H).descFactorial 2 : ℝ))
      (R.model.law : Measure p.SiteMatrix) :=
    R.model.physicalUnfoldedIntervalCount_integrable ⟨0, Matrix.isHermitian_zero⟩ E ρ (-L) L 2
  have hdom : Integrable (fun H => B ^ 2 * ((count H).descFactorial 2 + (count H).descFactorial 1 : ℝ))
      (R.model.law : Measure p.SiteMatrix) := (hi2.add hi1).const_mul _
  have hmeas : AEStronglyMeasurable (fun H => spectralTest g (R.spectral.markedConfig E H) ^ 2)
      (R.model.law : Measure p.SiteMatrix) :=
    (((continuous_spectralTest g).measurable.comp
      (R.spectral.measurable_markedConfig E)).pow_const 2).aestronglyMeasurable
  have hint : Integrable (fun H => spectralTest g (R.spectral.markedConfig E H) ^ 2)
      (R.model.law : Measure p.SiteMatrix) :=
    hdom.mono' hmeas (by
      filter_upwards [hpt] with H hH
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hH)
  have hcm : AEStronglyMeasurable (fun ξ => spectralTest g ξ ^ 2)
      (Measure.map (R.spectral.markedConfig E) (R.model.law : Measure p.SiteMatrix)) :=
    ((continuous_spectralTest g).pow 2).aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · rw [hlaw]
    exact (integrable_map_measure hcm (R.spectral.measurable_markedConfig E).aemeasurable).mpr hint
  · rw [hlaw, integral_map (R.spectral.measurable_markedConfig E).aemeasurable hcm]
    refine (integral_mono_ae hint hdom hpt).trans ?_
    rw [integral_const_mul, integral_add hi2 hi1]
    have b2 : ∫ H, ((count H).descFactorial 2 : ℝ) ∂(R.model.law : Measure p.SiteMatrix) ≤
        (K * (L - -L)) ^ 2 :=
      R.model.physicalUnfoldedIntervalCount_factorialBound source ⟨0, Matrix.isHermitian_zero⟩
        E ρ hρ (-L) L (by linarith) 2 (by norm_num)
    have b1 : ∫ H, ((count H).descFactorial 1 : ℝ) ∂(R.model.law : Measure p.SiteMatrix) ≤
        (K * (L - -L)) ^ 1 :=
      R.model.physicalUnfoldedIntervalCount_factorialBound source ⟨0, Matrix.isHermitian_zero⟩
        E ρ hρ (-L) L (by linarith) 1 le_rfl
    have hLL : L - -L = 2 * L := by ring
    rw [hLL, pow_one] at b1
    rw [hLL] at b2
    exact mul_le_mul_of_nonneg_left (add_le_add b2 b1) (sq_nonneg B)

end BlockBand.Density
