module

public import BlockBand.Palm.CoarseRelativeGradient

/-!
# Coarse relative local law: fixed-moment fluctuation of the normalized trace

For `G ~ GUE_N(1/N)` and `G_s(z) = (F + √s G - z)⁻¹`, the normalized trace `⟨G_s(z)⟩` satisfies
the fixed-moment bound `P(|⟨G_s(z)⟩ - E⟨G_s(z)⟩| ≥ λ) ≤ (C√p √s/(N η² λ))^p`, derived from the
Gaussian `L^p` gradient inequality `GaussianLpGradient`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate NNReal ENNReal

variable {N : ℕ}

/-- The product law of the real Gaussian coordinates of `GUE_N`. -/
abbrev coordLaw (N : ℕ) : Measure (((Fin N × Fin N) × Fin 2) → ℝ) :=
  gaussianProduct (fun _ : (Fin N × Fin N) × Fin 2 => (1 : ℝ≥0))

instance coordLaw_isProb (N : ℕ) : IsProbabilityMeasure (coordLaw N) := by
  unfold coordLaw gaussianProduct
  infer_instance

/-- `|⟨R⟩| ≤ η⁻¹`. -/
theorem coarseTrace_norm_le {F G : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (hG : G.IsHermitian) (hN : 0 < N) (s : ℝ) {z : ℂ} (hz : 0 < z.im) :
    ‖(N : ℂ)⁻¹ * (coarseResolvent F G s z).trace‖ ≤ z.im⁻¹ := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hH := coarse_hermitian hF hG s
  unfold coarseResolvent
  rw [trace_resolvent_eq_average hH hz.ne']
  exact certificateAverage_norm_le_const _ _
    (fun i => certificateScalarResolvent_norm_le _ hz le_rfl)

/-- Measurability of `G ↦ ⟨(F + √s G - z)⁻¹⟩` on all matrices. -/
theorem coarseTrace_measurable (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) :
    Measurable (fun G : Matrix (Fin N) (Fin N) ℂ =>
      (N : ℂ)⁻¹ * (coarseResolvent F G s z).trace) := by
  have hinv : Measurable (fun G : Matrix (Fin N) (Fin N) ℂ => coarseResolvent F G s z) := by
    have h : (fun G : Matrix (Fin N) (Fin N) ℂ => coarseResolvent F G s z) = fun G =>
        Ring.inverse (F + (Real.sqrt s : ℂ) • G - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det •
          (F + (Real.sqrt s : ℂ) • G - z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate := by
      funext G
      unfold coarseResolvent
      rw [Matrix.inv_def]
    rw [h]
    have h1 : Continuous fun G : Matrix (Fin N) (Fin N) ℂ =>
        (F + (Real.sqrt s : ℂ) • G - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det := by fun_prop
    have h2 : Continuous fun G : Matrix (Fin N) (Fin N) ℂ =>
        (F + (Real.sqrt s : ℂ) • G - z • (1 : Matrix (Fin N) (Fin N) ℂ)).adjugate := by fun_prop
    have h3 : Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
        Ring.inverse (F + (Real.sqrt s : ℂ) • G - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det := by
      simp_rw [Ring.inverse_eq_inv']
      exact h1.measurable.inv
    exact h3.smul h2.measurable
  have htr : Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => A.trace) := by fun_prop
  exact measurable_const.mul (htr.measurable.comp hinv)

/-- Fixed-moment Markov bound from `GaussianLpGradient`. -/
theorem coarseTrace_fluctuation_coord (hLp : GaussianLpGradient) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 1 ≤ p → ∀ (N : ℕ), 0 < N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian → ∀ s : ℝ, 0 ≤ s → ∀ z : ℂ, 0 < z.im →
      ∀ lam : ℝ, 0 < lam →
        coordLaw N {y | lam ≤ ‖coarseTraceFn F s z (Real.toNNReal (1 / N)) y -
            ∫ y', coarseTraceFn F s z (Real.toNNReal (1 / N)) y' ∂coordLaw N‖} ≤
          ENNReal.ofReal ((C * Real.sqrt p * (Real.sqrt s * (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹) / lam) ^ p) := by
  obtain ⟨C, hC, hLp'⟩ := hLp
  refine ⟨C, hC, ?_⟩
  intro p hp N hN F hF s hs z hz lam hlam
  set t := Real.toNNReal (1 / N)
  set f := coarseTraceFn F s z t with hfdef
  set μ := coordLaw N
  set B := Real.sqrt s * (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ with hB
  have hB0 : 0 ≤ B := by positivity
  have hf : ContDiff ℝ 1 f := coarseTraceFn_contDiff hF s hz.ne' t
  have hbdd : ∀ y, ‖f y‖ ≤ z.im⁻¹ := fun y =>
    coarseTrace_norm_le hF (gueCoord_isHermitian t y) hN s hz
  have hMem : MemLp f (ENNReal.ofReal p) μ :=
    MemLp.of_bound hf.continuous.aestronglyMeasurable _ (Filter.Eventually.of_forall hbdd)
  have hfl := hLp' p hp ((Fin N × Fin N) × Fin 2) (fun _ => 1) f hf hMem
  have hgrad : eLpNorm (weightedGradientNorm (fun _ => (1 : ℝ≥0)) f) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal B := by
    have h := eLpNorm_le_of_ae_bound (μ := μ) (p := ENNReal.ofReal p) (C := B)
      (f := weightedGradientNorm (fun _ => (1 : ℝ≥0)) f)
      (by
        have : Continuous (weightedGradientNorm (fun _ => (1 : ℝ≥0)) f) := by
          unfold weightedGradientNorm
          have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
          fun_prop
        exact this.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by unfold weightedGradientNorm; exact Real.sqrt_nonneg _)]
        exact coarseTraceFn_grad_le hF hN hs hz y))
    rwa [measure_univ, ENNReal.one_rpow, one_mul] at h
  have hL : eLpNorm (fun y => f y - ∫ y', f y' ∂μ) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (C * Real.sqrt p * B) := by
    refine hfl.trans ?_
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ C * Real.sqrt p)]
    exact by gcongr
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hptr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by linarith)
  have hset : {y | lam ≤ ‖f y - ∫ y', f y' ∂μ‖} =
      {y | ENNReal.ofReal lam ≤ ‖f y - ∫ y', f y' ∂μ‖ₑ} := by
    ext y
    simp only [Set.mem_ofPred_eq, ← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).symm
  rw [hset]
  have hM := meas_ge_le_mul_pow_eLpNorm_enorm μ hp0 hptop
    (f := fun y => f y - ∫ y', f y' ∂μ) (ε := ENNReal.ofReal lam)
    (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hlam) (fun h => absurd h ENNReal.ofReal_ne_top)
  refine hM.trans ?_
  rw [hptr]
  have hpow : eLpNorm (fun y => f y - ∫ y', f y' ∂μ) (ENNReal.ofReal p) μ ^ p ≤
      ENNReal.ofReal (C * Real.sqrt p * B) ^ p :=
    ENNReal.rpow_le_rpow hL (by linarith)
  calc (ENNReal.ofReal lam)⁻¹ ^ p * eLpNorm (fun y => f y - ∫ y', f y' ∂μ) (ENNReal.ofReal p) μ ^ p
      ≤ (ENNReal.ofReal lam)⁻¹ ^ p * ENNReal.ofReal (C * Real.sqrt p * B) ^ p :=
        by gcongr
    _ = ENNReal.ofReal ((C * Real.sqrt p * B / lam) ^ p) := by
      rw [← ENNReal.ofReal_inv_of_pos hlam,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
        ← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow (by positivity) (by positivity)]
      congr 2
      ring

/-- GUE form of the fluctuation bound: `P(|⟨G_s(z)⟩ - E⟨G_s(z)⟩| ≥ λ) ≤ (C√p √s/(N η² λ))^p` under
`G ~ GUE_N(1/N)`, from `GaussianLpGradient`. -/
theorem coarseTrace_fluctuation (hLp : GaussianLpGradient) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 1 ≤ p → ∀ (N : ℕ), 0 < N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian → ∀ s : ℝ, 0 ≤ s → ∀ z : ℂ, 0 < z.im →
      ∀ lam : ℝ, 0 < lam →
        gueMeasure (Fin N) (Real.toNNReal (1 / N))
            {G | lam ≤ ‖(N : ℂ)⁻¹ * (coarseResolvent F G s z).trace -
              ∫ G', (N : ℂ)⁻¹ * (coarseResolvent F G' s z).trace
                ∂gueMeasure (Fin N) (Real.toNNReal (1 / N))‖} ≤
          ENNReal.ofReal ((C * Real.sqrt p * (Real.sqrt s * (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹) / lam) ^ p) := by
  obtain ⟨C, hC, h⟩ := coarseTrace_fluctuation_coord hLp
  refine ⟨C, hC, ?_⟩
  intro p hp N hN F hF s hs z hz lam hlam
  have hmeasG := coarseTrace_measurable F s z
  have hcoord : Measurable (gueCoord (ι := Fin N) (Real.toNNReal (1 / N))) := by
    have hc : Measurable (BlockBand.SourceProcess.circularBrownianCoordinates (ι := Fin N)) := by
      apply Measurable.of_eval
      intro u
      unfold BlockBand.SourceProcess.circularBrownianCoordinates
      fun_prop
    have hg : Continuous (gueSample (ι := Fin N) (Real.toNNReal (1 / N))) := by
      unfold gueSample
      fun_prop
    exact hg.measurable.comp hc
  rw [gueMeasure_eq_map_gaussianProduct]
  rw [integral_map hcoord.aemeasurable hmeasG.aestronglyMeasurable]
  have hS : MeasurableSet {G : Matrix (Fin N) (Fin N) ℂ | lam ≤ ‖(N : ℂ)⁻¹ *
      (coarseResolvent F G s z).trace - ∫ y, (N : ℂ)⁻¹ * (coarseResolvent F
        (gueCoord (Real.toNNReal (1 / N)) y) s z).trace ∂coordLaw N‖} :=
    measurableSet_le measurable_const ((hmeasG.sub measurable_const).norm)
  rw [Measure.map_apply hcoord hS]
  exact h p hp N hN F hF s hs z hz lam hlam

end BlockBand.Palm.CoarseRelative
