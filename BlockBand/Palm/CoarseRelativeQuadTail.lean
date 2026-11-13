module

public import BlockBand.Palm.CoarseRelativeDirection

/-!
# Coarse relative local law: fixed-moment tail of the centred quadratic form

For `G ~ GUE_N(1/N)`, the centred quadratic form `q* G_s(z) q - E[q* G_s(z) q]` satisfies a
fixed-moment Markov bound of order `(C √p √(s/N) η⁻² (2 + 4C'²p) ‖M_s q‖² / λ)^p`, derived from
the Gaussian `L^p` gradient inequality.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate NNReal ENNReal

/-- Centred tail of `q* G_s q`. -/
theorem quad_fluctuation (hLp : GaussianLpGradient) :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧ ∀ p : ℝ, 1 ≤ p → ∀ (N : ℕ), 0 < N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian → ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → 0 < (freshDyson F s z).im → ∀ q : Fin N → ℂ,
      ∀ lam : ℝ, 0 < lam →
        coordLaw N {y | lam ≤ ‖quadFn F s z (Real.toNNReal (1 / N)) q y -
            ∫ y', quadFn F s z (Real.toNNReal (1 / N)) q y' ∂coordLaw N‖} ≤
          ENNReal.ofReal ((C * Real.sqrt p * (4 * Real.sqrt (s / N) * (z.im⁻¹) ^ 2 *
            ((2 + 4 * C' ^ 2 * p) * nsq (freshM F s z *ᵥ q))) / lam) ^ p) := by
  obtain ⟨C', hC', hG⟩ := gueVec_eLpNorm_le hLp
  obtain ⟨C, hC, hLp'⟩ := hLp
  refine ⟨C, C', hC, hC', ?_⟩
  intro p hp N hN F hF s hs hs1 z hz hz1 hm q lam hlam
  set t := Real.toNNReal (1 / N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : (t : ℝ) = 1 / N := Real.coe_toNNReal _ (by positivity)
  set f := quadFn F s z t q with hfdef
  set μ := coordLaw N
  set v := freshM F s z *ᵥ q with hv
  set v' := (freshM F s z)ᴴ *ᵥ q with hv'
  have hw : (freshW F s z).im ≠ 0 := (add_ofReal_mul_im_pos hs hz.le hm).ne'
  have hvv : nsq v' = nsq v := by
    rw [hv, hv', freshM_eq]; exact resolvent_conj_nsq hF hw q
  set k := 4 * Real.sqrt (s / N) * (z.im⁻¹) ^ 2 with hk
  have hk0 : 0 ≤ k := by positivity
  have hA : 0 ≤ 2 * nsq v := mul_nonneg (by norm_num) (nsq_nonneg v)
  have hBq : 0 ≤ 2 * C' ^ 2 * p * nsq v := mul_nonneg (by positivity) (nsq_nonneg v)
  set g₁ := fun y => nsq (gueCoord t y *ᵥ v)
  set g₂ := fun y => nsq (gueCoord t y *ᵥ v')
  have hf : ContDiff ℝ 1 f := quadFn_contDiff hF s hz.ne' t q
  have hMem : MemLp f (ENNReal.ofReal p) μ :=
    MemLp.of_bound hf.continuous.aestronglyMeasurable _
      (Filter.Eventually.of_forall (quadFn_bound hF s hz t q))
  have hfl := hLp' p hp ((Fin N × Fin N) × Fin 2) (fun _ => 1) f hf hMem
  -- pointwise gradient bound
  have hpt : ∀ y, weightedGradientNorm (fun _ => (1 : ℝ≥0)) f y ≤
      k * (2 * nsq v + g₁ y + g₂ y) := by
    intro y
    have hGh := gueCoord_isHermitian t y
    have h1 := quadFn_grad_le hF hs.le hz.ne' t q y
    have h2 := coordRes_vec_nsq_le hF hGh hN hs hs1 hz hz1 hm q
    have h3 := coordRes_conj_vec_nsq_le hF hGh hN hs hs1 hz hz1 hm q
    rw [← hv] at h2
    rw [← hv', hvv] at h3
    refine h1.trans ?_
    have hst : Real.sqrt (s * t) = Real.sqrt (s / N) := by rw [ht, mul_one_div]
    rw [hst, hk]
    have : (nsq ((coordRes F s z t y)ᴴ *ᵥ q) + nsq (coordRes F s z t y *ᵥ q)) / 2 ≤
        4 * (z.im⁻¹) ^ 2 * (2 * nsq v + g₁ y + g₂ y) := by
      simp only [g₁, g₂]
      nlinarith [h2, h3]
    calc Real.sqrt (s / N) * ((nsq ((coordRes F s z t y)ᴴ *ᵥ q) +
          nsq (coordRes F s z t y *ᵥ q)) / 2)
        ≤ Real.sqrt (s / N) * (4 * (z.im⁻¹) ^ 2 * (2 * nsq v + g₁ y + g₂ y)) :=
          mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hgradc : Continuous (weightedGradientNorm (fun _ => (1 : ℝ≥0)) f) := by
    unfold weightedGradientNorm
    have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
    fun_prop
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hgrad : eLpNorm (weightedGradientNorm (fun _ => (1 : ℝ≥0)) f) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (k * ((2 + 4 * C' ^ 2 * p) * nsq v)) := by
    have hmono := eLpNorm_mono_real (μ := μ) (p := ENNReal.ofReal p)
      hgradc.aestronglyMeasurable (g := fun y => k * (2 * nsq v + g₁ y + g₂ y))
      (fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by unfold weightedGradientNorm; exact Real.sqrt_nonneg _)]
        exact hpt y)
    refine hmono.trans ?_
    have hfun : (fun y => k * (2 * nsq v + g₁ y + g₂ y)) =
        k • ((fun _ => 2 * nsq v) + g₁ + g₂) := by
      funext y; simp [smul_eq_mul]
    rw [hfun, eLpNorm_const_smul]
    have hc : eLpNorm (fun _ : ((Fin N × Fin N) × Fin 2) → ℝ => 2 * nsq v) (ENNReal.ofReal p) μ =
        ENNReal.ofReal (2 * nsq v) := by
      rw [eLpNorm_const _ hp0 (IsProbabilityMeasure.ne_zero μ), measure_univ, ENNReal.one_rpow,
        mul_one, Real.enorm_eq_ofReal hA]
    have h1 := hG p hp N hN v
    have h2 := hG p hp N hN v'
    rw [hvv] at h2
    have hsum : eLpNorm ((fun _ => 2 * nsq v) + g₁ + g₂) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (2 * nsq v) + ENNReal.ofReal (2 * C' ^ 2 * p * nsq v) +
          ENNReal.ofReal (2 * C' ^ 2 * p * nsq v) := by
      refine (eLpNorm_add_le hp1).trans ?_
      refine add_le_add ((eLpNorm_add_le hp1).trans (add_le_add hc.le h1)) h2
    calc ‖k‖ₑ * eLpNorm ((fun _ => 2 * nsq v) + g₁ + g₂) (ENNReal.ofReal p) μ
        ≤ ENNReal.ofReal k * (ENNReal.ofReal (2 * nsq v) + ENNReal.ofReal (2 * C' ^ 2 * p * nsq v) +
          ENNReal.ofReal (2 * C' ^ 2 * p * nsq v)) := by
          rw [Real.enorm_eq_ofReal hk0]; gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_add hA hBq,
            ← ENNReal.ofReal_add (add_nonneg hA hBq) hBq,
            ← ENNReal.ofReal_mul hk0]
          congr 2
          ring
  set B := k * ((2 + 4 * C' ^ 2 * p) * nsq v) with hB
  have hB0 : 0 ≤ B := mul_nonneg hk0 (mul_nonneg (by positivity) (nsq_nonneg v))
  have hL : eLpNorm (fun y => f y - ∫ y', f y' ∂μ) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (C * Real.sqrt p * B) := by
    refine hfl.trans ?_
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ C * Real.sqrt p)]
    exact by gcongr
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
    (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hlam)
    (fun h => absurd h ENNReal.ofReal_ne_top)
  refine hM.trans ?_
  rw [hptr]
  have hpow : eLpNorm (fun y => f y - ∫ y', f y' ∂μ) (ENNReal.ofReal p) μ ^ p ≤
      ENNReal.ofReal (C * Real.sqrt p * B) ^ p :=
    ENNReal.rpow_le_rpow hL (by linarith)
  calc (ENNReal.ofReal lam)⁻¹ ^ p * eLpNorm (fun y => f y - ∫ y', f y' ∂μ) (ENNReal.ofReal p) μ ^ p
      ≤ (ENNReal.ofReal lam)⁻¹ ^ p * ENNReal.ofReal (C * Real.sqrt p * B) ^ p := by gcongr
    _ = ENNReal.ofReal ((C * Real.sqrt p * B / lam) ^ p) := by
      rw [← ENNReal.ofReal_inv_of_pos hlam,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
        ← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow (by positivity) (by positivity)]
      congr 2
      ring

end BlockBand.Palm.CoarseRelative
