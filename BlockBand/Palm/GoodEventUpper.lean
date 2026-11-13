module

public import BlockBand.Palm.CoarseRelativeTraceMean
public import BlockBand.Palm.CoarseRelativeFluctuation

/-!
# Good spectral event: the fixed-time upper bound on `Im⟨G_s⟩`

Spectral averaging gives `E Im⟨G_s(x+ih)⟩ ≤ C` uniformly in `F`.
This is proved here from the exact IBP mean equation instead of a Wegner input, for every
Hermitian `F`, every `s > 0` and every `z` with `Im z > 0` (no regularity, no norm bound):

* `im_avg_resolvent_le`: `Im⟨(F - w)⁻¹⟩ ≤ 1/Im w`.
* `meanTrace_im_le`: if the residual `e = s η⁻² · C √s N⁻¹ η⁻²` is at most `1`, then
  `Im E⟨R⟩ ≤ 2 + 1/s` (from `y ≤ 1/(η + s y) + e`).
* `im_upper_tail`: under the same condition,
  `P(Im⟨R⟩ > 3 + 1/s) ≤ (C √p √s N⁻¹ η⁻²)^p` (fixed-moment fluctuation at level `1`).

Only the Gaussian inputs `MultivariateGaussianIBP` and `GaussianLpGradient` are used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.GoodEvent

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open BlockBand.Palm.CoarseRelative
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate NNReal ENNReal

variable {N : ℕ}

/-- `Im⟨(F - w)⁻¹⟩ ≤ 1/Im w` for Hermitian `F`. -/
theorem im_avg_resolvent_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {w : ℂ} (hw : 0 < w.im) :
    ((N : ℂ)⁻¹ * ((F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace).im ≤ 1 / w.im := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [trace_resolvent_eq_average hF hw.ne']
  refine (Complex.im_le_norm _).trans ?_
  rw [one_div]
  exact certificateAverage_norm_le_const _ _
    (fun i => certificateScalarResolvent_norm_le _ hw le_rfl)

/-- Elementary step: `0 < y`, `y ≤ 1/(η + s y) + 1` imply `y ≤ 2 + 1/s`. -/
theorem upper_of_fixed_point {y η s : ℝ} (_hy : 0 < y) (hη : 0 < η) (hs : 0 < s)
    (h : y ≤ 1 / (η + s * y) + 1) : y ≤ 2 + 1 / s := by
  have hs' : 0 < 1 / s := by positivity
  by_cases hy1 : y ≤ 1
  · linarith
  · rw [not_le] at hy1
    have hden : s ≤ η + s * y := by nlinarith
    have h1 : 1 / (η + s * y) ≤ 1 / s := one_div_le_one_div_of_le hs hden
    linarith

/-- Mean bound, uniform in `F` and `Re z`. -/
theorem meanTrace_im_le (hIBP : MultivariateGaussianIBP) (hLp : GaussianLpGradient) : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian → ∀ s : ℝ, 0 < s →
      ∀ z : ℂ, 0 < z.im →
      s * (z.im⁻¹ * z.im⁻¹) * (C * (Real.sqrt s * (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹)) ≤ 1 →
        (meanTrace F s z).im ≤ 2 + 1 / s := by
  obtain ⟨C, hC, hL1⟩ := coarseTrace_L1_le hLp
  refine ⟨C, hC, ?_⟩
  intro N hN F hF s hs z hz he
  have hres := meanTrace_residual_le hF hs.le hz hN hIBP
  have hL := hL1 N hN F hF s hs.le z hz
  have herr : ‖meanTrace F s z - (N : ℂ)⁻¹ * (meanM F s z).trace‖ ≤ 1 := by
    refine hres.trans (le_trans ?_ he)
    exact mul_le_mul_of_nonneg_left hL (by positivity)
  have hypos := meanTrace_im_pos hF hz (s := s) hN
  set y := (meanTrace F s z).im with hydef
  have hwim : (z + (s : ℂ) * meanTrace F s z).im = z.im + s * y := by
    rw [add_ofReal_mul_im]
  have hwpos : 0 < (z + (s : ℂ) * meanTrace F s z).im := by
    rw [hwim]; positivity
  have hM := im_avg_resolvent_le hF hN hwpos
  have hMdef : meanM F s z =
      (F - (z + (s : ℂ) * meanTrace F s z) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := rfl
  rw [← hMdef, hwim] at hM
  have hdiff : y - ((N : ℂ)⁻¹ * (meanM F s z).trace).im ≤ 1 := by
    have := Complex.im_le_norm (meanTrace F s z - (N : ℂ)⁻¹ * (meanM F s z).trace)
    rw [Complex.sub_im] at this
    linarith
  exact upper_of_fixed_point hypos hz hs (by linarith)

/-- Fixed-time tail: `P(Im⟨R⟩ > 3 + 1/s) ≤ (C √p √s N⁻¹ η⁻²)^p` under `GUE_N(1/N)`. -/
theorem im_upper_tail (hIBP : MultivariateGaussianIBP) (hLp : GaussianLpGradient) : ∃ C : ℝ, 0 < C ∧
    ∀ p : ℝ, 1 ≤ p → ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian →
      ∀ s : ℝ, 0 < s → ∀ z : ℂ, 0 < z.im →
      s * (z.im⁻¹ * z.im⁻¹) * (C * (Real.sqrt s * (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹)) ≤ 1 →
        gueMeasure (Fin N) (Real.toNNReal (1 / N))
            {G | 3 + 1 / s < ((N : ℂ)⁻¹ * (coarseResolvent F G s z).trace).im} ≤
          ENNReal.ofReal ((C * Real.sqrt p * (Real.sqrt s * (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹)) ^ p) := by
  obtain ⟨C₁, hC₁, hmean⟩ := meanTrace_im_le hIBP hLp
  obtain ⟨C₂, hC₂, hfl⟩ := coarseTrace_fluctuation hLp
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro p hp N hN F hF s hs z hz he
  set B := Real.sqrt s * (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ with hBdef
  have hB0 : 0 ≤ B := by positivity
  have he1 : s * (z.im⁻¹ * z.im⁻¹) * (C₁ * B) ≤ 1 := by
    refine le_trans ?_ he
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _) hB0)
      (by positivity)
  have hy := hmean N hN F hF s hs z hz he1
  set t := Real.toNNReal (1 / N)
  -- the GUE mean equals the coordinate mean
  have hcoord : Measurable (gueCoord (ι := Fin N) t) := by
    have hc : Measurable (BlockBand.SourceProcess.circularBrownianCoordinates (ι := Fin N)) := by
      apply Measurable.of_eval
      intro u
      unfold BlockBand.SourceProcess.circularBrownianCoordinates
      fun_prop
    have hg : Continuous (gueSample (ι := Fin N) t) := by
      unfold gueSample
      fun_prop
    exact hg.measurable.comp hc
  have hmeasG := coarseTrace_measurable F s z
  have hint : (∫ G', (N : ℂ)⁻¹ * (coarseResolvent F G' s z).trace ∂gueMeasure (Fin N) t) =
      meanTrace F s z := by
    rw [gueMeasure_eq_map_gaussianProduct,
      integral_map hcoord.aemeasurable hmeasG.aestronglyMeasurable]
    rfl
  have hsub : {G : Matrix (Fin N) (Fin N) ℂ |
      3 + 1 / s < ((N : ℂ)⁻¹ * (coarseResolvent F G s z).trace).im} ⊆
      {G | 1 ≤ ‖(N : ℂ)⁻¹ * (coarseResolvent F G s z).trace -
        ∫ G', (N : ℂ)⁻¹ * (coarseResolvent F G' s z).trace ∂gueMeasure (Fin N) t‖} := by
    intro G hG
    simp only [Set.mem_ofPred_eq] at hG ⊢
    rw [hint]
    have := Complex.im_le_norm ((N : ℂ)⁻¹ * (coarseResolvent F G s z).trace - meanTrace F s z)
    rw [Complex.sub_im] at this
    linarith
  refine (measure_mono hsub).trans ?_
  refine (hfl p hp N hN F hF s hs.le z hz 1 one_pos).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [div_one]
  apply Real.rpow_le_rpow (by positivity) _ (by linarith)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)) hB0

end BlockBand.Palm.GoodEvent
