module

public import Mathlib
public import BlockBand.PointProcess.Specifications

/-!
# Sine-kernel determinants and the sine Laplace series

The limiting side of the Laplace clause. For every finite `k` and every
`x : Fin k → ℝ`, the matrix `[sineKernel (x i) (x j)]` (`sineKernel x y = sinc (π (x-y))`,
diagonal `1`) is positive semidefinite, because
`sinc (π a) = ∫_{-1/2}^{1/2} cos (2π a s) ds`; hence `0 ≤ det ≤ 1` (AM–GM on the eigenvalues,
trace `k`). Consequently, for every nonnegative `f` vanishing off `[-L, L]`, the `k`-th term
of `sineLaplaceFunctional f` lies in `[0, (2L)^k]` (Lebesgue measure on `ℝ^k`) and the series
is absolutely summable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open MeasureTheory Set Finset Matrix

/-- The `k × k` sine matrix at the points `x`. -/
def sineMatrix {k : ℕ} (x : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => BlockBand.sineKernel (x i) (x j)

/-- Fourier representation `sinc (π a) = ∫_{-1/2}^{1/2} cos (2π a s) ds`. -/
theorem sinc_pi_eq_integral (a : ℝ) :
    Real.sinc (Real.pi * a) = ∫ s in (-1/2 : ℝ)..(1/2), Real.cos (2 * Real.pi * a * s) := by
  by_cases ha : a = 0
  · subst ha
    simp
    norm_num
  · have hc : 2 * Real.pi * a ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun s => Real.cos s) hc, integral_cos,
      Real.sinc_of_ne_zero (by positivity)]
    have h1 : 2 * Real.pi * a * (1 / 2) = Real.pi * a := by ring
    have h2 : 2 * Real.pi * a * (-1 / 2) = -(Real.pi * a) := by ring
    rw [h1, h2, Real.sin_neg, smul_eq_mul]
    field_simp
    ring

/-- The sine matrix is positive semidefinite. -/
theorem sineMatrix_posSemidef {k : ℕ} (x : Fin k → ℝ) : (sineMatrix x).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [conjTranspose_apply, sineMatrix, BlockBand.sineKernel, star_trivial]
    rw [show x j - x i = -(x i - x j) by ring, mul_neg, Real.sinc_neg]
  · intro c
    have hS : ∀ i j, sineMatrix x i j =
        ∫ s in (-1/2 : ℝ)..(1/2), Real.cos (2 * Real.pi * (x i - x j) * s) := by
      intro i j
      rw [sineMatrix, BlockBand.sineKernel, sinc_pi_eq_integral]
    have hint : ∀ i j, IntervalIntegrable
        (fun s => c i * (Real.cos (2 * Real.pi * (x i - x j) * s) * c j)) volume
        (-1/2 : ℝ) (1/2) := fun i j => by
      apply Continuous.intervalIntegrable
      fun_prop
    have hq : star c ⬝ᵥ sineMatrix x *ᵥ c = ∫ s in (-1/2 : ℝ)..(1/2),
        ∑ i, ∑ j, c i * (Real.cos (2 * Real.pi * (x i - x j) * s) * c j) := by
      rw [intervalIntegral.integral_finsetSum (f := fun i s =>
        ∑ j, c i * (Real.cos (2 * Real.pi * (x i - x j) * s) * c j))
        (fun i _ => by apply Continuous.intervalIntegrable; fun_prop)]
      simp only [dotProduct, mulVec, star_trivial]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_finsetSum (f := fun j s =>
        c i * (Real.cos (2 * Real.pi * (x i - x j) * s) * c j)) (fun j _ => hint i j),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const, hS]
    rw [hq]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro s _
    have hsq : ∑ i, ∑ j, c i * (Real.cos (2 * Real.pi * (x i - x j) * s) * c j) =
        (∑ i, c i * Real.cos (2 * Real.pi * x i * s)) ^ 2 +
          (∑ i, c i * Real.sin (2 * Real.pi * x i * s)) ^ 2 := by
      rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show 2 * Real.pi * (x i - x j) * s = 2 * Real.pi * x i * s - 2 * Real.pi * x j * s by
        ring, Real.cos_sub]
      ring
    rw [hsq]
    positivity

/-- Sine determinants are nonnegative. -/
theorem sineMatrix_det_nonneg {k : ℕ} (x : Fin k → ℝ) : 0 ≤ (sineMatrix x).det :=
  (sineMatrix_posSemidef x).det_nonneg

/-- Sine determinants are at most one (unit diagonal, AM–GM on the eigenvalues). -/
theorem sineMatrix_det_le_one {k : ℕ} (x : Fin k → ℝ) : (sineMatrix x).det ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp
  have hP := sineMatrix_posSemidef x
  have hA := hP.1
  have hdet : (sineMatrix x).det = ∏ i, hA.eigenvalues i := by
    rw [hA.det_eq_prod_eigenvalues]
    simp
  have htr : ∑ i, hA.eigenvalues i = (k : ℝ) := by
    have h := hA.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h
    rw [← h, trace]
    simp [sineMatrix, BlockBand.sineKernel]
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have hnn : ∀ i, 0 ≤ hA.eigenvalues i := hP.eigenvalues_nonneg
  have hgm := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => ((k : ℝ))⁻¹)
    (fun i => hA.eigenvalues i) (fun _ _ => by positivity)
    (by simp [Finset.card_univ, Fintype.card_fin]; field_simp) (fun i _ => hnn i)
  have hsum : ∑ i, (k : ℝ)⁻¹ * hA.eigenvalues i = 1 := by
    rw [← Finset.mul_sum, htr, inv_mul_cancel₀ hk']
  rw [hsum] at hgm
  have hprod : ∏ i, hA.eigenvalues i = (∏ i, hA.eigenvalues i ^ ((k : ℝ))⁻¹) ^ k := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.rpow_inv_natCast_pow (hnn i) hk.ne']
  rw [hdet, hprod]
  exact pow_le_one₀ (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hnn i) _) hgm

/-- The `k`-th term of `sineLaplaceFunctional f`. -/
def sineTerm (f : CompactlySupportedContinuousMap ℝ ℝ) (k : ℕ) : ℝ :=
  ∫ x : Fin k → ℝ,
    Matrix.det (fun i j : Fin k => BlockBand.sineKernel (x i) (x j)) *
      ∏ i : Fin k, (1 - Real.exp (-f (x i)))
    ∂Measure.pi (fun _ : Fin k => volume)

/-- `sineLaplaceFunctional` is the series of the `sineTerm`s (definitional). -/
theorem sineLaplaceFunctional_eq_tsum (f : CompactlySupportedContinuousMap ℝ ℝ) :
    BlockBand.sineLaplaceFunctional f =
      ∑' k : ℕ, ((-1 : ℝ) ^ k / (Nat.factorial k : ℝ)) * sineTerm f k := rfl

/-- The closed box `[-L, L]^k`. -/
def box (k : ℕ) (L : ℝ) : Set (Fin k → ℝ) := Set.Icc (fun _ => -L) (fun _ => L)

/-- The box `[-L, L]^k` is measurable. -/
theorem measurableSet_box (k : ℕ) (L : ℝ) : MeasurableSet (box k L) := measurableSet_Icc

/-- Lebesgue measure of `[-L, L]^k` is `(2L)^k` for `L ≥ 0`. -/
theorem volume_real_box (k : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    (volume : Measure (Fin k → ℝ)).real (box k L) = (2 * L) ^ k := by
  rw [box, measureReal_def, Real.volume_Icc_pi_toReal (fun i => by simp only; linarith)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- Coordinatewise membership in the box. -/
theorem mem_box_iff {k : ℕ} {L : ℝ} (x : Fin k → ℝ) : x ∈ box k L ↔ ∀ i, x i ∈ Icc (-L) L := by
  simp only [box, Set.mem_Icc, Pi.le_def, Set.mem_Icc]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- A measurable function with values in `[0, 1_{[-L,L]^k}]` integrates to at most `(2L)^k`. -/
theorem integral_le_box {k : ℕ} {L : ℝ} (hL : 0 ≤ L) (g : (Fin k → ℝ) → ℝ)
    (hg : AEStronglyMeasurable g volume) (h0 : ∀ x, 0 ≤ g x)
    (h1 : ∀ x, g x ≤ (box k L).indicator 1 x) :
    Integrable g volume ∧ ∫ x, g x ≤ (2 * L) ^ k := by
  have hfin : volume (box k L) < ⊤ := by
    rw [box, Real.volume_Icc_pi]
    exact ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top
  have hind : Integrable ((box k L).indicator (1 : (Fin k → ℝ) → ℝ)) volume :=
    (integrableOn_const (C := (1 : ℝ)) hfin.ne).integrable_indicator (measurableSet_box k L)
  have hint : Integrable g volume := by
    refine hind.mono' hg (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
    exact h1 x
  refine ⟨hint, ?_⟩
  calc ∫ x, g x ≤ ∫ x, (box k L).indicator 1 x :=
        integral_mono hint hind h1
    _ = (2 * L) ^ k := by
        rw [integral_indicator_one (measurableSet_box k L), volume_real_box k hL]

/-- For `f ≥ 0` vanishing off `[-L, L]` (`L ≥ 0`), the sine term is integrable and in
`[0, (2L)^k]`. -/
theorem sineTerm_nonneg_le (f : CompactlySupportedContinuousMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {L : ℝ} (hL : 0 ≤ L) (hsupp : ∀ x, x ∉ Icc (-L) L → f x = 0) (k : ℕ) :
    Integrable (fun x : Fin k → ℝ => Matrix.det (fun i j : Fin k =>
        BlockBand.sineKernel (x i) (x j)) * ∏ i : Fin k, (1 - Real.exp (-f (x i)))) volume ∧
      0 ≤ sineTerm f k ∧ sineTerm f k ≤ (2 * L) ^ k := by
  have hφ0 : ∀ y, 0 ≤ 1 - Real.exp (-f y) := fun y => by
    have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf y)); linarith
  have hφ1 : ∀ y, 1 - Real.exp (-f y) ≤ 1 := fun y => by
    have := Real.exp_pos (-f y); linarith
  have hφs : ∀ y, y ∉ Icc (-L) L → 1 - Real.exp (-f y) = 0 := fun y hy => by
    rw [hsupp y hy]; simp
  have hcont : Continuous (fun x : Fin k → ℝ => Matrix.det (fun i j : Fin k =>
      BlockBand.sineKernel (x i) (x j)) * ∏ i : Fin k, (1 - Real.exp (-f (x i)))) := by
    apply Continuous.mul
    · apply Continuous.matrix_det
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [BlockBand.sineKernel]
      exact Real.continuous_sinc.comp (continuous_const.mul
        ((continuous_apply i).sub (continuous_apply j)))
    · exact continuous_finsetProd _ fun i _ =>
        continuous_const.sub (Real.continuous_exp.comp ((f.continuous.comp (continuous_apply i)).neg))
  have h0 : ∀ x : Fin k → ℝ, 0 ≤ Matrix.det (fun i j : Fin k =>
      BlockBand.sineKernel (x i) (x j)) * ∏ i : Fin k, (1 - Real.exp (-f (x i))) := fun x =>
    mul_nonneg (sineMatrix_det_nonneg x) (Finset.prod_nonneg fun i _ => hφ0 _)
  have h1 : ∀ x : Fin k → ℝ, Matrix.det (fun i j : Fin k =>
      BlockBand.sineKernel (x i) (x j)) * ∏ i : Fin k, (1 - Real.exp (-f (x i))) ≤
      (box k L).indicator 1 x := by
    intro x
    by_cases hx : x ∈ box k L
    · rw [indicator_of_mem hx, Pi.one_apply]
      calc _ ≤ 1 * 1 := mul_le_mul (sineMatrix_det_le_one x)
              (Finset.prod_le_one₀ (fun i _ => hφ0 _) fun i _ => hφ1 _)
              (Finset.prod_nonneg fun i _ => hφ0 _) zero_le_one
        _ = 1 := one_mul 1
    · rw [indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ Icc (-L) L := by
        by_contra h
        simp only [not_exists, not_not] at h
        exact hx ((mem_box_iff x).mpr h)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (hφs _ hi), mul_zero]
  obtain ⟨hint, hle⟩ := integral_le_box hL _ hcont.aestronglyMeasurable h0 h1
  exact ⟨hint, integral_nonneg h0, hle⟩

/-- The terms of the sine Laplace series are bounded by `(2L)^k / k!`, hence summable. -/
theorem summable_sineSeries (f : CompactlySupportedContinuousMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {L : ℝ} (hL : 0 ≤ L) (hsupp : ∀ x, x ∉ Icc (-L) L → f x = 0) :
    Summable (fun k : ℕ => ((-1 : ℝ) ^ k / (Nat.factorial k : ℝ)) * sineTerm f k) := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial (2 * L)) fun k => ?_
  obtain ⟨-, h0, h1⟩ := sineTerm_nonneg_le f hf hL hsupp k
  rw [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_of_nonneg h0,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)), one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right h1 (by positivity)

end BlockBand.GaussianBulk
