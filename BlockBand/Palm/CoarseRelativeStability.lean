module

public import BlockBand.Palm.CoarseRelativeUnion
public import BlockBand.Internal.Contracts.Inputs

/-!
# Coarse relative local law: stability of approximate Dyson roots, GUE coordinates

* `approx_root_stability`: if `m̃` has `Im m̃ > 0` and residual
  `|m̃ - ⟨(F - z - s m̃)⁻¹⟩| ≤ e`, then (hypotheses `hδ`, `hδ'`)
  `|m_s(z) - m̃| δ₀ ≤ e` for every `δ₀ ≤ η/(η + s Im m_s)`, `δ₀ ≤ (η - s e)/(η + s Im m̃)`.
  The proof is a direct Ward/Cauchy–Schwarz subtraction at the fixed point, with no height
  continuation: at a fixed height `η ≥ N^{-1/100}` the loss `δ₀⁻¹` is polynomial. Deterministic.
* `gueMeasure_eq_map_gaussianProduct`: GUE is the image of the standard Gaussian product law
  under the coordinate map `gueCoord`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open scoped ComplexConjugate ENNReal NNReal

variable {N : ℕ}

/-- The common subtraction bound: Ward-type control of both averages gives
`‖1 - sT‖ ≥ δ₀`. -/
theorem one_sub_mul_norm_ge {s A B δ₀ : ℝ} {T : ℂ} (hs : 0 < s) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsA : s * A ≤ 1 - δ₀) (hsB : s * B ≤ 1 - δ₀) (hT : ‖T‖ ^ 2 ≤ A * B) :
    δ₀ ≤ ‖1 - (s : ℂ) * T‖ ∧ s * ‖T‖ ≤ 1 - δ₀ := by
  have hδ1 : 0 ≤ 1 - δ₀ := le_trans (mul_nonneg hs.le hA) hsA
  have hsT : s * ‖T‖ ≤ 1 - δ₀ := by
    have hsq : (s * ‖T‖) ^ 2 ≤ (1 - δ₀) ^ 2 := by
      calc (s * ‖T‖) ^ 2 = s ^ 2 * ‖T‖ ^ 2 := by ring
        _ ≤ s ^ 2 * (A * B) := mul_le_mul_of_nonneg_left hT (by positivity)
        _ = (s * A) * (s * B) := by ring
        _ ≤ (1 - δ₀) * (1 - δ₀) := mul_le_mul hsA hsB (mul_nonneg hs.le hB) hδ1
        _ = (1 - δ₀) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) hδ1 two_ne_zero).mp hsq
  refine ⟨?_, hsT⟩
  have h1 : ‖(s : ℂ) * T‖ = s * ‖T‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have h2 := norm_sub_norm_le (1 : ℂ) ((s : ℂ) * T)
  rw [norm_one, h1] at h2
  linarith

/-- Stability of approximate roots of the Dyson equation at a fixed point. -/
theorem approx_root_stability {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) (hm : 0 < (freshDyson F s z).im)
    {mt : ℂ} (hmt : 0 < mt.im) {e : ℝ}
    (he : ‖certificateDysonResidual hF.eigenvalues s z mt‖ ≤ e) {δ₀ : ℝ}
    (hδ : δ₀ ≤ z.im / (z.im + s * (freshDyson F s z).im))
    (hδ' : δ₀ ≤ (z.im - s * e) / (z.im + s * mt.im)) :
    ‖freshDyson F s z - mt‖ * δ₀ ≤ e := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set m := freshDyson F s z with hmdef
  have hwpos : 0 < (z + (s : ℂ) * m).im := add_ofReal_mul_im_pos hs hz.le hm
  have hwpos' : 0 < (z + (s : ℂ) * mt).im := add_ofReal_mul_im_pos hs hz.le hmt
  have hres := freshDyson_residual_eq_zero hF hs hz.le hm
  set r : Fin N → ℂ := fun i => certificateScalarResolvent (hF.eigenvalues i) (z + s * m)
  set r' : Fin N → ℂ := fun i => certificateScalarResolvent (hF.eigenvalues i) (z + s * mt)
  have heq : m = certificateAverage r :=
    (certificateDysonResidual_eq_zero_iff hF.eigenvalues s z m).mp hres
  set et := certificateDysonResidual hF.eigenvalues s z mt with het
  have heq' : mt = certificateAverage r' + et := by
    rw [het]; unfold certificateDysonResidual; ring
  set T := certificateAverage (fun i => r i * r' i) with hT
  have hdiff0 : certificateAverage r - certificateAverage r' =
      ((z + s * m) - (z + s * mt)) * T := by
    rw [hT]
    unfold certificateAverage
    rw [← Finset.expect_sub_distrib, Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro i _
    show certificateScalarResolvent (hF.eigenvalues i) (z + s * m) -
        certificateScalarResolvent (hF.eigenvalues i) (z + s * mt) =
      ((z + s * m) - (z + s * mt)) * (certificateScalarResolvent (hF.eigenvalues i) (z + s * m) *
        certificateScalarResolvent (hF.eigenvalues i) (z + s * mt))
    rw [certificate_scalar_resolvent_sub _ hwpos.ne' hwpos'.ne']
    ring
  have hkey : (m - mt) * (1 - (s : ℂ) * T) = -et := by
    have h1 : m - mt = certificateAverage r - certificateAverage r' - et := by
      calc m - mt = certificateAverage r - (certificateAverage r' + et) := by
            rw [← heq, ← heq']
        _ = _ := by ring
    rw [hdiff0] at h1
    linear_combination h1
  -- Ward controls
  have hward := certificate_dyson_ward hF.eigenvalues s z m hres
  set Aa := certificateRealAverage (fun i => Complex.normSq (r i))
  set Ab := certificateRealAverage (fun i => Complex.normSq (r' i))
  have hAa0 : 0 ≤ Aa := Finset.expect_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hAb0 : 0 ≤ Ab := Finset.expect_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hp : 0 < z.im + s * m.im := by rw [← add_ofReal_mul_im]; exact hwpos
  have hp' : 0 < z.im + s * mt.im := by rw [← add_ofReal_mul_im]; exact hwpos'
  have hwa : m.im = (z.im + s * m.im) * Aa := hward
  have hsA : s * Aa ≤ 1 - δ₀ := by
    have h1 : z.im / (z.im + s * m.im) = 1 - s * Aa := by
      rw [div_eq_iff hp.ne']
      linear_combination (-s) * hwa
    linarith
  have hwb : (certificateAverage r').im = (z.im + s * mt.im) * Ab := by
    have := certificate_average_ward hF.eigenvalues (z + s * mt)
    rw [add_ofReal_mul_im] at this
    exact this
  have hsB : s * Ab ≤ 1 - δ₀ := by
    have hime : (certificateAverage r').im ≤ mt.im + e := by
      have h1 : (certificateAverage r').im = mt.im - et.im := by
        rw [heq']; simp
      have h2 := neg_abs_le et.im
      have h3 := (Complex.abs_im_le_norm et).trans he
      linarith
    have h1 : s * Ab * (z.im + s * mt.im) ≤ s * mt.im + s * e := by
      have : s * ((z.im + s * mt.im) * Ab) ≤ s * (mt.im + e) := by
        rw [← hwb]; exact mul_le_mul_of_nonneg_left hime hs.le
      linarith
    have h2 : (z.im - s * e) / (z.im + s * mt.im) = 1 - (s * mt.im + s * e) / (z.im + s * mt.im) := by
      field_simp
      ring
    have h3 : s * Ab ≤ (s * mt.im + s * e) / (z.im + s * mt.im) := by
      rw [le_div_iff₀ hp']; exact h1
    linarith
  have hTsq : ‖T‖ ^ 2 ≤ Aa * Ab := certificateAverage_mul_normSq_le r r'
  obtain ⟨hlow, -⟩ := one_sub_mul_norm_ge hs hAa0 hAb0 hsA hsB hTsq
  have hnorm := congrArg norm hkey
  rw [norm_mul, norm_neg] at hnorm
  calc ‖m - mt‖ * δ₀ ≤ ‖m - mt‖ * ‖1 - (s : ℂ) * T‖ :=
        mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
    _ = ‖et‖ := hnorm
    _ ≤ e := he

/-- The residual in trace form. -/
theorem residual_eq_trace_form {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s : ℝ}
    {z m : ℂ} (hw : (z + (s : ℂ) * m).im ≠ 0) :
    certificateDysonResidual hF.eigenvalues s z m =
      m - (N : ℂ)⁻¹ * ((F - (z + (s : ℂ) * m) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace := by
  rw [trace_resolvent_eq_average hF hw]
  rfl

/-!
## GUE as the image of the standard Gaussian product law
-/

/-- The real-coordinate GUE sample map `y ↦ √(t/2)(X + X*)`, `X_ab = (y_{ab0} + i y_{ab1})/√2`. -/
def gueCoord {ι : Type*} (t : ℝ≥0) (y : ((ι × ι) × Fin 2) → ℝ) : Matrix ι ι ℂ :=
  gueSample t (BlockBand.SourceProcess.circularBrownianCoordinates y)

/-- `GUE_ι(t) = (gaussianProduct 1).map (gueCoord t)`. -/
theorem gueMeasure_eq_map_gaussianProduct (ι : Type) [Fintype ι] (t : ℝ≥0) :
    gueMeasure ι t = (BlockBand.Internal.Contracts.Inputs.gaussianProduct
      (fun _ : (ι × ι) × Fin 2 => (1 : ℝ≥0))).map (gueCoord t) := by
  have hc : Measurable (BlockBand.SourceProcess.circularBrownianCoordinates (ι := ι)) := by
    apply Measurable.of_eval
    intro u
    unfold BlockBand.SourceProcess.circularBrownianCoordinates
    fun_prop
  have hg : Continuous (gueSample (ι := ι) t) := by
    unfold gueSample
    fun_prop
  unfold gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
    BlockBand.Internal.Contracts.Inputs.gaussianProduct
  rw [Measure.map_map hg.measurable hc]
  rfl

end BlockBand.Palm.CoarseRelative
