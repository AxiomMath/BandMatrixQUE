module

public import BlockBand.Palm.CoarseRelativeMean

/-!
# Coarse relative local law: the approximate scalar equation for `E⟨G_s⟩`

For Hermitian `F`, `s ≥ 0`, `Im z > 0`, `N ≥ 1`, `G ~ GUE_N(1/N)` (coordinates `y`):
* `meanTrace_im_pos`, `meanTrace_norm_le`: `0 < Im m̄`, `|m̄| ≤ η⁻¹`.
* `meanTrace_residual_eq`: the exact identity
  `m̄ - ⟨(F - z - s m̄)⁻¹⟩ = s E[(⟨R⟩ - m̄) ⟨M̄ R⟩]` from the mean equation.
* `meanTrace_residual_le`: `|m̄ - ⟨(F - z - s m̄)⁻¹⟩| ≤ s η⁻² E|⟨R⟩ - m̄|`.
* `coarseTrace_L1_le`: `E|⟨R⟩ - m̄| ≤ C √s N⁻¹ η⁻²` (`GaussianLpGradient`, `p = 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate NNReal ENNReal

variable {N : ℕ}

/-- `m̄ = E⟨R⟩`. -/
def meanTrace (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) : ℂ :=
  ∫ y, coarseTraceFn F s z (Real.toNNReal (1 / N)) y ∂coordLaw N

/-- `E[R]` entrywise. -/
def meanRes (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun m l => ∫ y, coordRes F s z (Real.toNNReal (1 / N)) y m l ∂coordLaw N

/-- `E[⟨R⟩ R]` entrywise. -/
def meanRes2 (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun k l => ∫ y, coarseTraceFn F s z (Real.toNNReal (1 / N)) y *
    coordRes F s z (Real.toNNReal (1 / N)) y k l ∂coordLaw N

section Facts

variable {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s : ℝ} {z : ℂ} (hz : 0 < z.im)
include hF hz

theorem coordRes_entry_integrable (m l : Fin N) :
    Integrable (fun y => coordRes F s z (Real.toNNReal (1 / N)) y m l) (coordLaw N) :=
  Integrable.of_bound ((continuous_apply_apply m l).comp
      (coordRes_continuous hF s hz.ne' _)).aestronglyMeasurable _
    (Filter.Eventually.of_forall (fun y => coordRes_entry_le hF s hz _ y m l))

theorem coarseTraceFn_continuous :
    Continuous (coarseTraceFn F s z (Real.toNNReal (1 / N))) :=
  (coarseTraceFn_contDiff hF s hz.ne' _).continuous

theorem coarseTraceFn_bound (hN : 0 < N) (y : ((Fin N × Fin N) × Fin 2) → ℝ) :
    ‖coarseTraceFn F s z (Real.toNNReal (1 / N)) y‖ ≤ z.im⁻¹ :=
  coarseTrace_norm_le hF (gueCoord_isHermitian _ y) hN s hz

theorem coarseTraceFn_integrable (hN : 0 < N) :
    Integrable (coarseTraceFn F s z (Real.toNNReal (1 / N))) (coordLaw N) :=
  Integrable.of_bound (coarseTraceFn_continuous hF hz).aestronglyMeasurable _
    (Filter.Eventually.of_forall (coarseTraceFn_bound hF hz hN))

theorem coarseTraceFn_im_pos (hN : 0 < N) (y : ((Fin N × Fin N) × Fin 2) → ℝ) :
    0 < (coarseTraceFn F s z (Real.toNNReal (1 / N)) y).im := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hH := coarse_hermitian hF (gueCoord_isHermitian (Real.toNNReal (1 / N)) y) s
  unfold coarseTraceFn coarseResolvent
  rw [trace_resolvent_eq_average hH hz.ne', certificateAverage_im]
  exact Finset.expect_pos (fun i _ => certificate_scalar_im_pos _ hz) Finset.univ_nonempty

theorem meanTrace_im_pos (hN : 0 < N) : 0 < (meanTrace F s z).im := by
  have hint := coarseTraceFn_integrable hF hz (s := s) hN
  have him : Integrable (fun y => (coarseTraceFn F s z (Real.toNNReal (1 / N)) y).im)
      (coordLaw N) := hint.im
  have h := (integral_pos_iff_support_of_nonneg
    (fun y => (coarseTraceFn_im_pos hF hz hN y).le) him).mpr (by
      have : Function.support (fun y => (coarseTraceFn F s z (Real.toNNReal (1 / N)) y).im) =
          Set.univ := by
        ext y
        simp only [Function.mem_support, Set.mem_univ, iff_true]
        exact (coarseTraceFn_im_pos hF hz hN y).ne'
      rw [this, measure_univ]
      exact one_pos)
  have heq : (∫ y, coarseTraceFn F s z (Real.toNNReal (1 / N)) y ∂coordLaw N).im =
      ∫ y, (coarseTraceFn F s z (Real.toNNReal (1 / N)) y).im ∂coordLaw N :=
    (integral_im hint).symm
  unfold meanTrace
  rw [heq]
  exact h

theorem meanTrace_norm_le (hN : 0 < N) : ‖meanTrace F s z‖ ≤ z.im⁻¹ := by
  have h := norm_integral_le_of_norm_le_const (μ := coordLaw N)
    (Filter.Eventually.of_forall (coarseTraceFn_bound hF hz (s := s) hN))
  rwa [probReal_univ, mul_one] at h

theorem meanTrace_eq_trace :
    meanTrace F s z = (N : ℂ)⁻¹ * (meanRes F s z).trace := by
  unfold meanTrace meanRes coarseTraceFn
  rw [integral_const_mul]
  congr 1
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.of_apply]
  rw [integral_finsetSum _ (fun m _ => coordRes_entry_integrable hF hz m m)]

/-- Matrix form of the mean equation `(F - z) E[R] - s E[⟨R⟩R] = I`. -/
theorem mean_matrix_eq (hIBP : MultivariateGaussianIBP) (hN : 0 < N) (hs : 0 ≤ s) :
    (F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) * meanRes F s z - (s : ℂ) • meanRes2 F s z = 1 := by
  ext k l
  rw [Matrix.sub_apply, mul_apply, Matrix.smul_apply, smul_eq_mul]
  have h := coarse_mean_equation hIBP hF hN hs hz k l
  unfold meanRes meanRes2 coarseTraceFn
  simp only [Matrix.of_apply]
  exact h

end Facts

/-- `M̄ = (F - z - s m̄)⁻¹`. -/
def meanM (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (F - (z + (s : ℂ) * meanTrace F s z) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

theorem meanW_im_ge {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s : ℝ} (hs : 0 ≤ s)
    {z : ℂ} (hz : 0 < z.im) (hN : 0 < N) :
    z.im ≤ (z + (s : ℂ) * meanTrace F s z).im := by
  rw [add_ofReal_mul_im]
  have := meanTrace_im_pos hF hz (s := s) hN
  nlinarith

/-- `|⟨A B⟩| ≤ a b` from squared operator bounds. -/
theorem trace_mul_norm_le {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B : Matrix ι ι ℂ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ v : ι → ℂ, nsq (A *ᵥ v) ≤ a ^ 2 * nsq v)
    (hB : ∀ v : ι → ℂ, nsq (B *ᵥ v) ≤ b ^ 2 * nsq v) :
    ‖((Fintype.card ι : ℂ))⁻¹ * (A * B).trace‖ ≤ a * b := by
  have hAB : ∀ v : ι → ℂ, nsq ((A * B) *ᵥ v) ≤ (a * b) ^ 2 * nsq v := by
    intro v
    rw [← mulVec_mulVec]
    calc nsq (A *ᵥ (B *ᵥ v)) ≤ a ^ 2 * nsq (B *ᵥ v) := hA _
      _ ≤ a ^ 2 * (b ^ 2 * nsq v) := mul_le_mul_of_nonneg_left (hB v) (by positivity)
      _ = (a * b) ^ 2 * nsq v := by ring
  have hent := entry_le_of_nsq (by positivity) hAB
  rw [norm_mul, norm_inv, Complex.norm_natCast, Matrix.trace]
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [inv_mul_le_iff₀ hcard]
  calc ‖∑ i, (A * B).diag i‖ ≤ ∑ i, ‖(A * B).diag i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, a * b := Finset.sum_le_sum (fun i _ => hent i i)
    _ = Fintype.card ι * (a * b) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

section Residual

variable {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
  (hz : 0 < z.im) (hN : 0 < N)
include hF hs hz hN

/-- Exact residual identity `m̄ - ⟨M̄⟩ = s E[(⟨R⟩ - m̄)⟨M̄ R⟩]`. -/
theorem meanTrace_residual_eq (hIBP : MultivariateGaussianIBP) :
    meanTrace F s z - (N : ℂ)⁻¹ * (meanM F s z).trace =
      (s : ℂ) * ∫ y, (coarseTraceFn F s z (Real.toNNReal (1 / N)) y - meanTrace F s z) *
        ((N : ℂ)⁻¹ * (meanM F s z * coordRes F s z (Real.toNNReal (1 / N)) y).trace)
        ∂coordLaw N := by
  have hwim : (z + (s : ℂ) * meanTrace F s z).im ≠ 0 :=
    (lt_of_lt_of_le hz (meanW_im_ge hF hs hz hN)).ne'
  have hmean := mean_matrix_eq hF hz hIBP hN hs
  have hmean' : (F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) * meanRes F s z =
      1 + (s : ℂ) • meanRes2 F s z := sub_eq_iff_eq_add.mp hmean
  have h1 : (F - (z + (s : ℂ) * meanTrace F s z) • (1 : Matrix (Fin N) (Fin N) ℂ)) *
      meanRes F s z = 1 + (s : ℂ) • (meanRes2 F s z - meanTrace F s z • meanRes F s z) := by
    have hsplit : F - (z + (s : ℂ) * meanTrace F s z) • (1 : Matrix (Fin N) (Fin N) ℂ) =
        (F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) - ((s : ℂ) * meanTrace F s z) • 1 := by
      rw [add_smul]; abel
    calc _ = (F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) * meanRes F s z -
          ((s : ℂ) * meanTrace F s z) • meanRes F s z := by
          rw [hsplit, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = (1 + (s : ℂ) • meanRes2 F s z) - ((s : ℂ) * meanTrace F s z) • meanRes F s z := by
          rw [hmean']
      _ = _ := by rw [smul_sub, smul_smul]; abel
  have h2 : meanRes F s z = meanM F s z + (s : ℂ) •
      (meanM F s z * (meanRes2 F s z - meanTrace F s z • meanRes F s z)) := by
    have hinv := hermitian_shift_inv_mul hF hwim
    calc meanRes F s z = (meanM F s z * (F - (z + (s : ℂ) * meanTrace F s z) •
          (1 : Matrix (Fin N) (Fin N) ℂ))) * meanRes F s z := by
          rw [meanM, hinv, Matrix.one_mul]
      _ = meanM F s z * (1 + (s : ℂ) •
          (meanRes2 F s z - meanTrace F s z • meanRes F s z)) := by rw [Matrix.mul_assoc, h1]
      _ = _ := by rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have h3 : meanTrace F s z = (N : ℂ)⁻¹ * (meanM F s z).trace + (s : ℂ) * ((N : ℂ)⁻¹ *
      (meanM F s z * (meanRes2 F s z - meanTrace F s z • meanRes F s z)).trace) := by
    calc meanTrace F s z = (N : ℂ)⁻¹ * (meanRes F s z).trace := meanTrace_eq_trace hF hz
      _ = (N : ℂ)⁻¹ * (meanM F s z + (s : ℂ) •
          (meanM F s z * (meanRes2 F s z - meanTrace F s z • meanRes F s z))).trace :=
          congrArg (fun A => (N : ℂ)⁻¹ * A.trace) h2
      _ = _ := by rw [trace_add, trace_smul, smul_eq_mul]; ring
  -- the trace of M̄ X as an expectation
  have hRi := fun m' l' => coordRes_entry_integrable hF hz (s := s) m' l'
  have hfc := coarseTraceFn_continuous hF hz (s := s)
  have hX : ∀ a b, (meanRes2 F s z - meanTrace F s z • meanRes F s z) a b =
      ∫ y, (coarseTraceFn F s z (Real.toNNReal (1 / N)) y - meanTrace F s z) *
        coordRes F s z (Real.toNNReal (1 / N)) y a b ∂coordLaw N := by
    intro a b
    have hprod : Integrable (fun y => coarseTraceFn F s z (Real.toNNReal (1 / N)) y *
        coordRes F s z (Real.toNNReal (1 / N)) y a b) (coordLaw N) :=
      (hRi a b).bdd_mul hfc.aestronglyMeasurable
        (Filter.Eventually.of_forall (coarseTraceFn_bound hF hz hN))
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, meanRes, meanRes2,
      Matrix.of_apply]
    rw [← integral_const_mul, ← integral_sub hprod ((hRi a b).const_mul _)]
    congr 1
    funext y
    ring
  have hterm : ∀ a b, Integrable (fun y => meanM F s z a b *
      ((coarseTraceFn F s z (Real.toNNReal (1 / N)) y - meanTrace F s z) *
        coordRes F s z (Real.toNNReal (1 / N)) y b a)) (coordLaw N) := by
    intro a b
    have : Integrable (fun y => (coarseTraceFn F s z (Real.toNNReal (1 / N)) y -
        meanTrace F s z) * coordRes F s z (Real.toNNReal (1 / N)) y b a) (coordLaw N) :=
      (hRi b a).bdd_mul (hfc.sub continuous_const).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun y => (norm_sub_le _ _).trans
          (add_le_add (coarseTraceFn_bound hF hz hN y) (meanTrace_norm_le hF hz hN))))
    exact this.const_mul _
  have htr : (meanM F s z * (meanRes2 F s z - meanTrace F s z • meanRes F s z)).trace =
      ∫ y, (coarseTraceFn F s z (Real.toNNReal (1 / N)) y - meanTrace F s z) *
        (meanM F s z * coordRes F s z (Real.toNNReal (1 / N)) y).trace ∂coordLaw N := by
    have hpt : ∀ y, (coarseTraceFn F s z (Real.toNNReal (1 / N)) y - meanTrace F s z) *
        (meanM F s z * coordRes F s z (Real.toNNReal (1 / N)) y).trace =
        ∑ a, ∑ b, meanM F s z a b *
          ((coarseTraceFn F s z (Real.toNNReal (1 / N)) y - meanTrace F s z) *
            coordRes F s z (Real.toNNReal (1 / N)) y b a) := by
      intro y
      rw [Matrix.trace, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Matrix.diag_apply, mul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hterm a b))]
    rw [Matrix.trace]
    apply Finset.sum_congr rfl
    intro a _
    rw [integral_finsetSum _ (fun b _ => hterm a b), Matrix.diag_apply, mul_apply]
    apply Finset.sum_congr rfl
    intro b _
    rw [integral_const_mul, hX]
  rw [sub_eq_of_eq_add' h3, htr, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by dsimp only; ring)

/-- `|m̄ - ⟨(F - z - s m̄)⁻¹⟩| ≤ s η⁻² E|⟨R⟩ - m̄|`. -/
theorem meanTrace_residual_le (hIBP : MultivariateGaussianIBP) :
    ‖meanTrace F s z - (N : ℂ)⁻¹ * (meanM F s z).trace‖ ≤
      s * (z.im⁻¹ * z.im⁻¹) * ∫ y, ‖coarseTraceFn F s z (Real.toNNReal (1 / N)) y -
        meanTrace F s z‖ ∂coordLaw N := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set t := Real.toNNReal (1 / N)
  rw [meanTrace_residual_eq hF hs hz hN hIBP, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hs, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hs
  have hwge := meanW_im_ge hF hs hz hN (s := s)
  have hwpos : 0 < (z + (s : ℂ) * meanTrace F s z).im := lt_of_lt_of_le hz hwge
  have hbound : ∀ y, ‖(N : ℂ)⁻¹ * (meanM F s z * coordRes F s z t y).trace‖ ≤
      z.im⁻¹ * z.im⁻¹ := by
    intro y
    have hH := coarse_hermitian hF (gueCoord_isHermitian t y) s
    have h := trace_mul_norm_le (meanM F s z) (coordRes F s z t y)
      (a := z.im⁻¹) (b := z.im⁻¹) (by positivity) (by positivity)
      (fun v => by
        have h1 := hermitian_resolvent_nsq_le hF hwpos.ne' v
        refine h1.trans (mul_le_mul_of_nonneg_right ?_ (nsq_nonneg v))
        rw [inv_pow]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hz.le hwge 2))
      (fun v => by
        have h1 := hermitian_resolvent_nsq_le hH hz.ne' v
        rw [inv_pow]
        exact h1)
    rwa [Fintype.card_fin] at h
  calc ‖∫ y, (coarseTraceFn F s z t y - meanTrace F s z) *
        ((N : ℂ)⁻¹ * (meanM F s z * coordRes F s z t y).trace) ∂coordLaw N‖
      ≤ ∫ y, ‖(coarseTraceFn F s z t y - meanTrace F s z) *
        ((N : ℂ)⁻¹ * (meanM F s z * coordRes F s z t y).trace)‖ ∂coordLaw N :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖coarseTraceFn F s z t y - meanTrace F s z‖ * (z.im⁻¹ * z.im⁻¹) ∂coordLaw N := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        · exact (((coarseTraceFn_integrable hF hz hN).sub
            (integrable_const _)).norm).mul_const _
        · exact Filter.Eventually.of_forall (fun y => by
            dsimp only
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hbound y) (norm_nonneg _))
    _ = (z.im⁻¹ * z.im⁻¹) * ∫ y, ‖coarseTraceFn F s z t y - meanTrace F s z‖ ∂coordLaw N := by
        rw [integral_mul_const]; ring

end Residual

/-- The case `p = 1` of the fluctuation bound: `E|⟨R⟩ - m̄| ≤ C √s N⁻¹ η⁻²` from
`GaussianLpGradient`. -/
theorem coarseTrace_L1_le (hLp : GaussianLpGradient) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian →
      ∀ s : ℝ, 0 ≤ s → ∀ z : ℂ, 0 < z.im →
        ∫ y, ‖coarseTraceFn F s z (Real.toNNReal (1 / N)) y - meanTrace F s z‖ ∂coordLaw N ≤
          C * (Real.sqrt s * (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹) := by
  obtain ⟨C, hC, hLp'⟩ := hLp
  refine ⟨C, hC, ?_⟩
  intro N hN F hF s hs z hz
  set t := Real.toNNReal (1 / N)
  set f := coarseTraceFn F s z t with hfdef
  set B := Real.sqrt s * (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ with hB
  have hB0 : 0 ≤ B := by positivity
  have hf : ContDiff ℝ 1 f := coarseTraceFn_contDiff hF s hz.ne' t
  have hMem : MemLp f (ENNReal.ofReal 1) (coordLaw N) :=
    MemLp.of_bound hf.continuous.aestronglyMeasurable _
      (Filter.Eventually.of_forall (coarseTraceFn_bound hF hz hN))
  have hfl := hLp' 1 le_rfl ((Fin N × Fin N) × Fin 2) (fun _ => 1) f hf hMem
  have hgrad : eLpNorm (weightedGradientNorm (fun _ => (1 : ℝ≥0)) f) (ENNReal.ofReal 1)
      (coordLaw N) ≤ ENNReal.ofReal B := by
    have h := eLpNorm_le_of_ae_bound (μ := coordLaw N) (p := ENNReal.ofReal 1) (C := B)
      (f := weightedGradientNorm (fun _ => (1 : ℝ≥0)) f)
      (by
        have : Continuous (weightedGradientNorm (fun _ => (1 : ℝ≥0)) f) := by
          unfold weightedGradientNorm
          have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
          fun_prop
        exact this.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (by unfold weightedGradientNorm; exact Real.sqrt_nonneg _)]
        exact coarseTraceFn_grad_le hF hN hs hz y))
    rwa [measure_univ, ENNReal.one_rpow, one_mul] at h
  have hL : eLpNorm (fun y => f y - ∫ y', f y' ∂coordLaw N) 1 (coordLaw N) ≤
      ENNReal.ofReal (C * B) := by
    have h := hfl.trans (by gcongr : ENNReal.ofReal (C * Real.sqrt 1) *
      eLpNorm (weightedGradientNorm (fun _ => (1 : ℝ≥0)) f) (ENNReal.ofReal 1) (coordLaw N) ≤
        ENNReal.ofReal (C * Real.sqrt 1) * ENNReal.ofReal B)
    rw [ENNReal.ofReal_one, Real.sqrt_one, mul_one, ← ENNReal.ofReal_mul hC.le] at h
    exact h
  have hmeas : AEStronglyMeasurable (fun y => f y - ∫ y', f y' ∂coordLaw N) (coordLaw N) :=
    (hf.continuous.sub continuous_const).aestronglyMeasurable
  rw [show meanTrace F s z = ∫ y', f y' ∂coordLaw N from rfl,
    integral_norm_eq_lintegral_enorm hmeas, ← eLpNorm_one_eq_lintegral_enorm hmeas]
  have hfin : eLpNorm (fun y => f y - ∫ y', f y' ∂coordLaw N) 1 (coordLaw N) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hL
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

end BlockBand.Palm.CoarseRelative
