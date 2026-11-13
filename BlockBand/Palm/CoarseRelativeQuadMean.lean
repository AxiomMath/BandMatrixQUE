module

public import BlockBand.Palm.CoarseRelativeQuadTail

/-!
# Coarse relative local law: the directional mean error

The mean of the quadratic form `q* G_s q` is compared with `q* M_s q`, relative to `‖M_s q‖²`.

* `meanRes_decomp`: `E R = M̄ + s M̄ (E[⟨R⟩R] - m̄ E R)` (from the IBP mean equation).
* `quadFn_mean_identity`: `E[q*Rq] - q*M_s q = s(m̄ - m) q*M̄M_s q + s E[(⟨R⟩ - m̄) q*M̄ R q]`.
* `quadFn_mean_le`: with `ν² = ‖M_s q‖² > 0` and `s|m̄ - m| ≤ η`,
  `|E[q*Rq] - q*M_s q| ≤ ν² (2|m̄ - m| + 6η⁻¹(C₁N⁻¹η⁻² + C₁N^{-1/2}η⁻³ + C'² N^{-1/2}))`
  from `GaussianLpGradient` and `MultivariateGaussianIBP`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate NNReal ENNReal

theorem quad_integral_comm {ι α : Type} [Fintype ι] [MeasurableSpace α] {μ : Measure α}
    (P : Matrix ι ι ℂ) (q : ι → ℂ) (Y : α → Matrix ι ι ℂ)
    (hY : ∀ a b, Integrable (fun y => Y y a b) μ) :
    ∫ y, star q ⬝ᵥ ((P * Y y) *ᵥ q) ∂μ =
      star q ⬝ᵥ ((P * Matrix.of (fun a b => ∫ y, Y y a b ∂μ)) *ᵥ q) := by
  have hexp : ∀ Z : Matrix ι ι ℂ, star q ⬝ᵥ ((P * Z) *ᵥ q) =
      ∑ a, ∑ b, ∑ c, (star q a * P a c * q b) * Z c b := by
    intro Z
    simp only [dotProduct, mulVec, mul_apply, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
    integrable_finsetSum _ (fun c _ => (hY c b).const_mul _)))]
  apply Finset.sum_congr rfl; intro a _
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ => (hY c b).const_mul _))]
  apply Finset.sum_congr rfl; intro b _
  rw [integral_finsetSum _ (fun c _ => (hY c b).const_mul _)]
  apply Finset.sum_congr rfl; intro c _
  rw [integral_const_mul, Matrix.of_apply]

theorem dot_norm_le {ι : Type} [Fintype ι] (x y : ι → ℂ) :
    ‖star x ⬝ᵥ y‖ ≤ Real.sqrt (nsq x) * Real.sqrt (nsq y) := by
  rw [← Real.sqrt_mul (nsq_nonneg x)]
  exact Real.le_sqrt_of_sq_le (norm_star_dotProduct_sq_le x y)

variable {N : ℕ}

section Fixed

variable {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
  (hz : 0 < z.im) (hN : 0 < N)
include hF hs hz hN

/-- `E R = M̄ + s M̄ (E[⟨R⟩R] - m̄ E R)`. -/
theorem meanRes_decomp (hIBP : MultivariateGaussianIBP) :
    meanRes F s z = meanM F s z + (s : ℂ) •
      (meanM F s z * (meanRes2 F s z - meanTrace F s z • meanRes F s z)) := by
  have hwim : (z + (s : ℂ) * meanTrace F s z).im ≠ 0 :=
    (lt_of_lt_of_le hz (meanW_im_ge hF hs hz hN)).ne'
  have hmean' : (F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) * meanRes F s z =
      1 + (s : ℂ) • meanRes2 F s z := sub_eq_iff_eq_add.mp (mean_matrix_eq hF hz hIBP hN hs)
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
  have hinv := hermitian_shift_inv_mul hF hwim
  calc meanRes F s z = (meanM F s z * (F - (z + (s : ℂ) * meanTrace F s z) •
        (1 : Matrix (Fin N) (Fin N) ℂ))) * meanRes F s z := by
        rw [meanM, hinv, Matrix.one_mul]
    _ = meanM F s z * (1 + (s : ℂ) •
        (meanRes2 F s z - meanTrace F s z • meanRes F s z)) := by rw [Matrix.mul_assoc, h1]
    _ = _ := by rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]

/-- Exact directional mean identity. -/
theorem quadFn_mean_identity (hIBP : MultivariateGaussianIBP)
    (hm : 0 < (freshDyson F s z).im) (q : Fin N → ℂ) :
    ∫ y, quadFn F s z (Real.toNNReal (1 / N)) q y ∂coordLaw N -
        star q ⬝ᵥ (freshM F s z *ᵥ q) =
      (s : ℂ) * (meanTrace F s z - freshDyson F s z) *
          (star q ⬝ᵥ ((meanM F s z * freshM F s z) *ᵥ q)) +
        (s : ℂ) * ∫ y, (coarseTraceFn F s z (Real.toNNReal (1 / N)) y - meanTrace F s z) *
          (star q ⬝ᵥ ((meanM F s z * coordRes F s z (Real.toNNReal (1 / N)) y) *ᵥ q))
          ∂coordLaw N := by
  set t := Real.toNNReal (1 / N)
  have hRi := fun a b => coordRes_entry_integrable hF hz (s := s) a b
  have hfc := coarseTraceFn_continuous hF hz (s := s)
  -- E Q = q* E R q
  have hEQ : ∫ y, quadFn F s z t q y ∂coordLaw N = star q ⬝ᵥ (meanRes F s z *ᵥ q) := by
    have h := quad_integral_comm (μ := coordLaw N) 1 q (fun y => coordRes F s z t y) hRi
    simp only [Matrix.one_mul] at h
    exact h
  -- X entries
  have hYi : ∀ a b, Integrable (fun y => ((coarseTraceFn F s z t y - meanTrace F s z) •
      coordRes F s z t y) a b) (coordLaw N) := by
    intro a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact (hRi a b).bdd_mul (hfc.sub continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => (norm_sub_le _ _).trans
        (add_le_add (coarseTraceFn_bound hF hz hN y) (meanTrace_norm_le hF hz hN))))
  have hX : meanRes2 F s z - meanTrace F s z • meanRes F s z =
      Matrix.of (fun a b => ∫ y, ((coarseTraceFn F s z t y - meanTrace F s z) •
        coordRes F s z t y) a b ∂coordLaw N) := by
    ext a b
    have hprod : Integrable (fun y => coarseTraceFn F s z t y * coordRes F s z t y a b)
        (coordLaw N) :=
      (hRi a b).bdd_mul hfc.aestronglyMeasurable
        (Filter.Eventually.of_forall (coarseTraceFn_bound hF hz hN))
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, meanRes, meanRes2,
      Matrix.of_apply]
    rw [← integral_const_mul, ← integral_sub hprod ((hRi a b).const_mul _)]
    congr 1
    funext y
    ring
  have hMX : star q ⬝ᵥ ((meanM F s z * (meanRes2 F s z - meanTrace F s z • meanRes F s z)) *ᵥ q) =
      ∫ y, (coarseTraceFn F s z t y - meanTrace F s z) *
        (star q ⬝ᵥ ((meanM F s z * coordRes F s z t y) *ᵥ q)) ∂coordLaw N := by
    rw [hX, ← quad_integral_comm _ q _ hYi]
    congr 1
    funext y
    rw [Matrix.mul_smul, smul_mulVec, dotProduct_smul, smul_eq_mul]
  -- M̄ - M
  have hw : (freshW F s z).im ≠ 0 := by
    rw [freshW_im]
    exact (add_pos_of_pos_of_nonneg hz (mul_nonneg hs hm.le)).ne'
  have hwb : (z + (s : ℂ) * meanTrace F s z).im ≠ 0 :=
    (lt_of_lt_of_le hz (meanW_im_ge hF hs hz hN)).ne'
  have hMM : meanM F s z - freshM F s z =
      ((s : ℂ) * (meanTrace F s z - freshDyson F s z)) • (meanM F s z * freshM F s z) := by
    have h := hermitian_resolvent_sub hF hwb hw
    unfold meanM
    rw [freshM_eq, h]
    unfold freshW
    congr 1
    ring
  rw [hEQ, meanRes_decomp hF hs hz hN hIBP, add_mulVec, dotProduct_add, smul_mulVec,
    dotProduct_smul, smul_eq_mul, hMX]
  have : star q ⬝ᵥ (meanM F s z *ᵥ q) - star q ⬝ᵥ (freshM F s z *ᵥ q) =
      (s : ℂ) * (meanTrace F s z - freshDyson F s z) *
        (star q ⬝ᵥ ((meanM F s z * freshM F s z) *ᵥ q)) := by
    rw [← dotProduct_sub, ← sub_mulVec, hMM, smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [← this]
  ring

end Fixed

theorem quad_mul_eq {ι : Type} [Fintype ι] (P Y : Matrix ι ι ℂ) (q : ι → ℂ) :
    star q ⬝ᵥ ((P * Y) *ᵥ q) = star (Pᴴ *ᵥ q) ⬝ᵥ (Y *ᵥ q) := by
  rw [star_mulVec, conjTranspose_conjTranspose, ← mulVec_mulVec, dotProduct_mulVec]

theorem nsq_continuous {ι : Type} [Fintype ι] : Continuous (fun x : ι → ℂ => nsq x) := by
  unfold nsq; fun_prop

set_option maxHeartbeats 1000000 in
/-- The directional mean error, relative to `‖M_s q‖²`. -/
theorem quadFn_mean_le (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP) :
    ∃ C₁ C' : ℝ, 0 < C₁ ∧ 0 < C' ∧ ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ),
      F.IsHermitian → ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ z : ℂ, 0 < z.im → z.im ≤ 1 →
      0 < (freshDyson F s z).im → s * ‖meanTrace F s z - freshDyson F s z‖ ≤ z.im →
      ∀ q : Fin N → ℂ, 0 < nsq (freshM F s z *ᵥ q) →
        ‖∫ y, quadFn F s z (Real.toNNReal (1 / N)) q y ∂coordLaw N -
            star q ⬝ᵥ (freshM F s z *ᵥ q)‖ ≤
          nsq (freshM F s z *ᵥ q) * (2 * ‖meanTrace F s z - freshDyson F s z‖ +
            6 * z.im⁻¹ * (C₁ * (N : ℝ)⁻¹ * (z.im⁻¹) ^ 2 + C₁ * (Real.sqrt N)⁻¹ * (z.im⁻¹) ^ 3 +
              C' ^ 2 * (Real.sqrt N)⁻¹)) := by
  obtain ⟨C₁, hC₁, hL1⟩ := coarseTrace_L1_le hLp
  obtain ⟨C', hC', hG⟩ := gueVec_eLpNorm_le hLp
  refine ⟨C₁, C', hC₁, hC', ?_⟩
  intro N hN F hF s hs hs1 z hz hz1 hm hclose q hq
  set t := Real.toNNReal (1 / N)
  set η := z.im with hηdef
  set v := freshM F s z *ᵥ q with hv
  set ν := Real.sqrt (nsq v) with hν
  have hν0 : 0 < ν := Real.sqrt_pos.mpr hq
  have hνsq : ν ^ 2 = nsq v := Real.sq_sqrt (nsq_nonneg v)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hηi : 1 ≤ η⁻¹ := one_le_inv₀ hz |>.mpr hz1
  have hw : (freshW F s z).im ≠ 0 := (add_ofReal_mul_im_pos hs hz.le hm).ne'
  have hwbge := meanW_im_ge hF hs.le hz hN (s := s)
  have hwb : (z + (s : ℂ) * meanTrace F s z).im ≠ 0 := (lt_of_lt_of_le hz hwbge).ne'
  -- Step a: ‖M̄* q‖ ≤ 2ν
  have hMbar : Real.sqrt (nsq ((meanM F s z)ᴴ *ᵥ q)) ≤ 2 * ν := by
    have hca : (conj (z + (s : ℂ) * meanTrace F s z)).im ≠ 0 := by
      rw [Complex.conj_im]; exact neg_ne_zero.mpr hwb
    have hcb : (conj (freshW F s z)).im ≠ 0 := by
      rw [Complex.conj_im]; exact neg_ne_zero.mpr hw
    have h := resolvent_vec_bound hF isHermitian_zero 0 hca hcb q
    have hlhs : (F + ((0 : ℝ) : ℂ) • (0 : Matrix (Fin N) (Fin N) ℂ) -
        conj (z + (s : ℂ) * meanTrace F s z) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
        (meanM F s z)ᴴ := by
      rw [smul_zero, add_zero]; unfold meanM; exact (hermitian_resolvent_conjTranspose hF _).symm
    have hrhs : (F - conj (freshW F s z) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = (freshM F s z)ᴴ := by
      rw [freshM_eq]; exact (hermitian_resolvent_conjTranspose hF _).symm
    rw [hlhs, hrhs] at h
    have hMc : Real.sqrt (nsq ((freshM F s z)ᴴ *ᵥ q)) = ν := by
      rw [hν, hv, freshM_eq, resolvent_conj_nsq hF hw q]
    rw [hMc, abs_zero, zero_mul, zero_add] at h
    have hba : ‖conj (freshW F s z) - conj (z + (s : ℂ) * meanTrace F s z)‖ =
        s * ‖meanTrace F s z - freshDyson F s z‖ := by
      rw [← map_sub, Complex.norm_conj]
      unfold freshW
      rw [show z + (s : ℂ) * freshDyson F s z - (z + (s : ℂ) * meanTrace F s z) =
          (s : ℂ) * -(meanTrace F s z - freshDyson F s z) by ring, norm_mul, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    rw [hba, Complex.conj_im, abs_neg, abs_of_pos (lt_of_lt_of_le hz hwbge)] at h
    have hfac : (z + (s : ℂ) * meanTrace F s z).im⁻¹ *
        (s * ‖meanTrace F s z - freshDyson F s z‖ * ν) ≤ ν := by
      have h1 : (z + (s : ℂ) * meanTrace F s z).im⁻¹ ≤ η⁻¹ := inv_anti₀ hz hwbge
      calc _ ≤ η⁻¹ * (η * ν) := mul_le_mul h1 (mul_le_mul_of_nonneg_right hclose hν0.le)
            (by positivity) (by positivity)
        _ = ν := by field_simp
    linarith
  -- identity
  rw [quadFn_mean_identity hF hs.le hz hN hIBP hm q]
  refine (norm_add_le _ _).trans ?_
  -- term 1
  have hT1 : ‖(s : ℂ) * (meanTrace F s z - freshDyson F s z) *
      (star q ⬝ᵥ ((meanM F s z * freshM F s z) *ᵥ q))‖ ≤
      2 * ‖meanTrace F s z - freshDyson F s z‖ * nsq v := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, quad_mul_eq]
    have h1 := dot_norm_le ((meanM F s z)ᴴ *ᵥ q) (freshM F s z *ᵥ q)
    rw [← hν, ← hv] at h1
    have h2 : ‖star ((meanM F s z)ᴴ *ᵥ q) ⬝ᵥ (freshM F s z *ᵥ q)‖ ≤ 2 * ν * ν :=
      h1.trans (mul_le_mul_of_nonneg_right hMbar hν0.le)
    calc s * ‖meanTrace F s z - freshDyson F s z‖ *
          ‖star ((meanM F s z)ᴴ *ᵥ q) ⬝ᵥ (freshM F s z *ᵥ q)‖
        ≤ 1 * ‖meanTrace F s z - freshDyson F s z‖ * (2 * ν * ν) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)) h2 (norm_nonneg _)
            (by positivity)
      _ = 2 * ‖meanTrace F s z - freshDyson F s z‖ * nsq v := by rw [← hνsq]; ring
  -- term 2
  set f := coarseTraceFn F s z t
  set mb := meanTrace F s z
  set θ := ν * Real.sqrt N with hθ
  have hθ0 : 0 < θ := mul_pos hν0 hsN
  set g := fun y => nsq (gueCoord t y *ᵥ v)
  have hGc : Continuous (fun y : ((Fin N × Fin N) × Fin 2) → ℝ => gueCoord t y) :=
    (gueCoordLin (ι := Fin N) t).continuous_of_finiteDimensional
  have hgc : Continuous g := nsq_continuous.comp (hGc.matrix_mulVec continuous_const)
  have hgmeas : AEStronglyMeasurable g (coordLaw N) := hgc.aestronglyMeasurable
  have hGb := hG 1 le_rfl N hN v
  rw [ENNReal.ofReal_one, mul_one] at hGb
  have hgi : Integrable g (coordLaw N) := by
    refine ⟨hgmeas, ?_⟩
    rw [HasFiniteIntegral, ← eLpNorm_one_eq_lintegral_enorm hgmeas]
    exact lt_of_le_of_lt hGb ENNReal.ofReal_lt_top
  have hK : ∫ y, g y ∂coordLaw N ≤ 2 * C' ^ 2 * nsq v := by
    have h1 : ∫ y, g y ∂coordLaw N = ∫ y, ‖g y‖ ∂coordLaw N := by
      congr 1; funext y; rw [Real.norm_of_nonneg (nsq_nonneg _)]
    rw [h1, integral_norm_eq_lintegral_enorm hgmeas, ← eLpNorm_one_eq_lintegral_enorm hgmeas]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hGb
    rwa [ENNReal.toReal_ofReal (by have := nsq_nonneg v; positivity)] at this
  have hfi : Integrable (fun y => ‖f y - mb‖) (coordLaw N) :=
    ((coarseTraceFn_integrable hF hz hN).sub (integrable_const _)).norm
  have hL := hL1 N hN F hF s hs.le z hz
  have hfb : ∀ y, ‖f y - mb‖ ≤ 2 * η⁻¹ := fun y => (norm_sub_le _ _).trans
    (by linarith [coarseTraceFn_bound hF hz (s := s) hN y, meanTrace_norm_le hF hz hN (s := s)])
  -- pointwise bound
  have hpt : ∀ y, ‖(f y - mb) * (star q ⬝ᵥ ((meanM F s z * coordRes F s z t y) *ᵥ q))‖ ≤
      6 * ν * η⁻¹ * ((ν + θ * η⁻¹) * ‖f y - mb‖ + g y / (2 * θ)) := by
    intro y
    set x := ‖f y - mb‖
    have hx0 : 0 ≤ x := norm_nonneg _
    have hg0 : 0 ≤ g y := nsq_nonneg _
    set r := Real.sqrt (g y)
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrr : r ^ 2 = nsq (gueCoord t y *ᵥ v) := Real.sq_sqrt hg0
    have hR := coordRes_vec_nsq_le hF (gueCoord_isHermitian t y) hN hs hs1 hz hz1 hm q
    rw [← hv] at hR
    have hRs : Real.sqrt (nsq (coordRes F s z t y *ᵥ q)) ≤ 3 * η⁻¹ * (ν + r) := by
      have h2 : nsq (coordRes F s z t y *ᵥ q) ≤ (3 * η⁻¹ * (ν + r)) ^ 2 := by
        refine hR.trans ?_
        rw [← hνsq, ← hrr]
        nlinarith [sq_nonneg (ν - r), mul_nonneg hν0.le hr0, sq_nonneg η⁻¹]
      calc _ ≤ Real.sqrt ((3 * η⁻¹ * (ν + r)) ^ 2) := Real.sqrt_le_sqrt h2
        _ = _ := Real.sqrt_sq (by positivity)
    have hQ : ‖star q ⬝ᵥ ((meanM F s z * coordRes F s z t y) *ᵥ q)‖ ≤
        2 * ν * (3 * η⁻¹ * (ν + r)) := by
      rw [quad_mul_eq]
      exact (dot_norm_le _ _).trans (mul_le_mul hMbar hRs (Real.sqrt_nonneg _) (by positivity))
    have hamgm : x * r ≤ θ * η⁻¹ * x + g y / (2 * θ) := by
      have h1 : 2 * θ * (x * r) ≤ θ ^ 2 * x ^ 2 + g y := by
        nlinarith [sq_nonneg (θ * x - r)]
      have h2 : θ ^ 2 * x ^ 2 ≤ θ ^ 2 * x * (2 * η⁻¹) := by
        have := mul_le_mul_of_nonneg_left (hfb y) (by positivity : 0 ≤ θ ^ 2 * x)
        nlinarith
      have h3 : 2 * θ * (x * r) ≤ 2 * θ * (θ * η⁻¹ * x + g y / (2 * θ)) := by
        have : 2 * θ * (θ * η⁻¹ * x + g y / (2 * θ)) = θ ^ 2 * x * (2 * η⁻¹) + g y := by
          field_simp
        rw [this]; linarith
      exact le_of_mul_le_mul_left h3 (by positivity)
    rw [norm_mul]
    calc x * ‖star q ⬝ᵥ ((meanM F s z * coordRes F s z t y) *ᵥ q)‖
        ≤ x * (2 * ν * (3 * η⁻¹ * (ν + r))) := mul_le_mul_of_nonneg_left hQ hx0
      _ = 6 * ν * η⁻¹ * (ν * x + x * r) := by ring
      _ ≤ 6 * ν * η⁻¹ * (ν * x + (θ * η⁻¹ * x + g y / (2 * θ))) := by gcongr
      _ = _ := by ring
  have hint2 : ∫ y, ‖(f y - mb) * (star q ⬝ᵥ ((meanM F s z * coordRes F s z t y) *ᵥ q))‖
      ∂coordLaw N ≤ 6 * ν * η⁻¹ * ((ν + θ * η⁻¹) * ∫ y, ‖f y - mb‖ ∂coordLaw N +
        (∫ y, g y ∂coordLaw N) / (2 * θ)) := by
    have hrhs : Integrable (fun y => 6 * ν * η⁻¹ * ((ν + θ * η⁻¹) * ‖f y - mb‖ + g y / (2 * θ)))
        (coordLaw N) := ((hfi.const_mul _).add (hgi.div_const _)).const_mul _
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hrhs
      (Filter.Eventually.of_forall hpt)).trans_eq ?_
    rw [integral_const_mul, integral_add (hfi.const_mul _) (hgi.div_const _), integral_const_mul,
      integral_div]
  have hT2 : ‖(s : ℂ) * ∫ y, (f y - mb) *
      (star q ⬝ᵥ ((meanM F s z * coordRes F s z t y) *ᵥ q)) ∂coordLaw N‖ ≤
      nsq v * (6 * η⁻¹ * (C₁ * (N : ℝ)⁻¹ * (η⁻¹) ^ 2 + C₁ * (Real.sqrt N)⁻¹ * (η⁻¹) ^ 3 +
        C' ^ 2 * (Real.sqrt N)⁻¹)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    refine (mul_le_mul hs1 ((norm_integral_le_integral_norm _).trans hint2) (norm_nonneg _)
      zero_le_one).trans ?_
    rw [one_mul]
    have hLb : ∫ y, ‖f y - mb‖ ∂coordLaw N ≤ C₁ * ((N : ℝ)⁻¹ * (η⁻¹) ^ 2) := by
      refine hL.trans ?_
      apply mul_le_mul_of_nonneg_left _ hC₁.le
      rw [inv_pow]
      calc Real.sqrt s * (N : ℝ)⁻¹ * (η ^ 2)⁻¹ ≤ 1 * (N : ℝ)⁻¹ * (η ^ 2)⁻¹ := by
            gcongr; rw [Real.sqrt_le_one]; exact hs1
        _ = _ := by ring
    have hL0 : 0 ≤ ∫ y, ‖f y - mb‖ ∂coordLaw N := integral_nonneg (fun _ => norm_nonneg _)
    have hK' : (∫ y, g y ∂coordLaw N) / (2 * θ) ≤ C' ^ 2 * ν * (Real.sqrt N)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      calc ∫ y, g y ∂coordLaw N ≤ 2 * C' ^ 2 * nsq v := hK
        _ = C' ^ 2 * ν * (Real.sqrt N)⁻¹ * (2 * θ) := by
            rw [hθ, ← hνsq]; field_simp
    have hsq : Real.sqrt N * (N : ℝ)⁻¹ = (Real.sqrt N)⁻¹ := by
      have h := Real.sq_sqrt hNr.le
      field_simp
      linarith
    calc 6 * ν * η⁻¹ * ((ν + θ * η⁻¹) * ∫ y, ‖f y - mb‖ ∂coordLaw N +
          (∫ y, g y ∂coordLaw N) / (2 * θ))
        ≤ 6 * ν * η⁻¹ * ((ν + θ * η⁻¹) * (C₁ * ((N : ℝ)⁻¹ * (η⁻¹) ^ 2)) +
          C' ^ 2 * ν * (Real.sqrt N)⁻¹) := by
          gcongr
      _ = nsq v * (6 * η⁻¹ * (C₁ * (N : ℝ)⁻¹ * (η⁻¹) ^ 2 +
          C₁ * (Real.sqrt N * (N : ℝ)⁻¹) * (η⁻¹) ^ 3 + C' ^ 2 * (Real.sqrt N)⁻¹)) := by
          rw [← hνsq, hθ]; ring
      _ = _ := by rw [hsq]
  calc _ ≤ 2 * ‖meanTrace F s z - freshDyson F s z‖ * nsq v + nsq v * (6 * η⁻¹ *
        (C₁ * (N : ℝ)⁻¹ * (η⁻¹) ^ 2 + C₁ * (Real.sqrt N)⁻¹ * (η⁻¹) ^ 3 +
          C' ^ 2 * (Real.sqrt N)⁻¹)) := add_le_add hT1 hT2
    _ = _ := by ring

end BlockBand.Palm.CoarseRelative
