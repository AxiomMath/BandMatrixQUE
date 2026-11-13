module

public import BlockBand.Palm.CoarseRelativeTracePointwise

/-!
# Coarse relative local law: Gaussian moments of `‖G v‖²`

For `G ~ GUE_N(1/N)` and a fixed vector `v`, the `L^p` norm of `‖G v‖²` is bounded by
`2C² p ‖v‖²`, using the Gaussian `L^p` gradient inequality in GUE coordinates.

* `sum_dot_gueCoord_sq`: exact rank-one identity `Σ_j |u* (∂_jG) w|² = t ‖u‖² ‖w‖²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate NNReal ENNReal

section RankOne

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem trace_vecMulVec_mul (u w : ι → ℂ) (D : Matrix ι ι ℂ) :
    (vecMulVec w (star u) * D).trace = star u ⬝ᵥ (D *ᵥ w) := by
  simp only [Matrix.trace, Matrix.diag_apply, mul_apply, vecMulVec_apply, dotProduct, mulVec,
    Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- **Rank-one identity** `Σ_j |u* ∂_jG w|² = t ‖u‖² ‖w‖²`. -/
theorem sum_dot_gueCoord_sq (t : ℝ≥0) (u w : ι → ℂ) :
    ∑ j : (ι × ι) × Fin 2, ‖star u ⬝ᵥ (gueCoord t (Pi.single j (1 : ℝ)) *ᵥ w)‖ ^ 2 =
      (t : ℝ) * (nsq u * nsq w) := by
  simp_rw [← trace_vecMulVec_mul]
  rw [sum_norm_trace_gueCoord_sq]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [vecMulVec_apply, norm_mul, Pi.star_apply, norm_star, mul_pow]
  unfold nsq
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro _ _
  apply Finset.sum_congr rfl
  intro _ _
  ring

end RankOne

variable {N : ℕ}

/-- The real-linear functional `y ↦ (G(y) v)_a`. -/
def gueVecLin (t : ℝ≥0) (v : Fin N → ℂ) (a : Fin N) :
    (((Fin N × Fin N) × Fin 2) → ℝ) →ₗ[ℝ] ℂ :=
  ({ toFun := fun A => (A *ᵥ v) a
     map_add' := fun A B => by simp [add_mulVec]
     map_smul' := fun r A => by simp [smul_mulVec] } :
      Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] ℂ).comp (gueCoordLin t)

theorem gueVecLin_apply (t : ℝ≥0) (v : Fin N → ℂ) (a : Fin N) (y) :
    gueVecLin t v a y = (gueCoord t y *ᵥ v) a := rfl

theorem gueVec_fderiv (t : ℝ≥0) (v : Fin N → ℂ) (a : Fin N) (y w) :
    fderiv ℝ (fun y => (gueCoord t y *ᵥ v) a) y w = (gueCoord t w *ᵥ v) a := by
  have h : (fun y => (gueCoord t y *ᵥ v) a) = ⇑(LinearMap.toContinuousLinearMap (gueVecLin t v a)) := by
    funext y; rfl
  rw [h, ContinuousLinearMap.fderiv]
  rfl

theorem gueVec_contDiff (t : ℝ≥0) (v : Fin N → ℂ) (a : Fin N) :
    ContDiff ℝ 1 (fun y => (gueCoord t y *ᵥ v) a) := by
  have h : (fun y => (gueCoord t y *ᵥ v) a) = ⇑(LinearMap.toContinuousLinearMap (gueVecLin t v a)) := by
    funext y; rfl
  rw [h]
  exact ContinuousLinearMap.contDiff _

theorem gueVec_grad (t : ℝ≥0) (v : Fin N → ℂ) (a : Fin N) (y) :
    weightedGradientNorm (fun _ => (1 : ℝ≥0)) (fun y => (gueCoord t y *ᵥ v) a) y =
      Real.sqrt ((t : ℝ) * nsq v) := by
  unfold weightedGradientNorm
  congr 1
  simp only [NNReal.coe_one, one_mul, gueVec_fderiv]
  have h := sum_dot_gueCoord_sq t (Pi.single a 1) v
  rw [nsq_single_one, one_mul] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  simp [dotProduct, Pi.single_apply]

/-- Coordinates are centred and in every `L^p`. -/
theorem coord_integral_zero {ι : Type} [Fintype ι] (j : ι) :
    ∫ y : ι → ℝ, y j ∂gaussianProduct (fun _ : ι => (1 : ℝ≥0)) = 0 := by
  unfold gaussianProduct
  have hmp := measurePreserving_eval (fun _ : ι => ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)) j
  have := integral_map (μ := Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)))
    (φ := Function.eval j) (f := fun x : ℝ => x) (measurable_pi_apply j).aemeasurable
    measurable_id.aestronglyMeasurable
  rw [hmp.map_eq, ProbabilityTheory.integral_id_gaussianReal] at this
  exact this.symm

theorem coord_memLp {ι : Type} [Fintype ι] (j : ι) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun y : ι → ℝ => y j) p (gaussianProduct (fun _ : ι => (1 : ℝ≥0))) := by
  unfold gaussianProduct
  have hmp := measurePreserving_eval (fun _ : ι => ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)) j
  exact (ProbabilityTheory.memLp_id_gaussianReal' p hp).comp_measurePreserving hmp

theorem gueVec_eq_sum (t : ℝ≥0) (v : Fin N → ℂ) (a : Fin N) (y) :
    (gueCoord t y *ᵥ v) a = ∑ j, (y j : ℂ) * (gueCoord t (Pi.single j (1 : ℝ)) *ᵥ v) a := by
  rw [gueCoord_eq_sum t y, Matrix.sum_mulVec]
  simp [Finset.sum_apply, smul_mulVec]

theorem gueVec_memLp (t : ℝ≥0) (v : Fin N → ℂ) (a : Fin N) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun y => (gueCoord t y *ᵥ v) a) p (coordLaw N) := by
  have h : (fun y => (gueCoord t y *ᵥ v) a) =
      ∑ j, fun y : ((Fin N × Fin N) × Fin 2) → ℝ =>
        ((y j : ℝ) : ℂ) * (gueCoord t (Pi.single j (1 : ℝ)) *ᵥ v) a := by
    funext y
    rw [gueVec_eq_sum, Finset.sum_apply]
  rw [h]
  exact memLp_finsetSum' _ (fun j _ => ((coord_memLp j p hp).ofReal (K := ℂ)).mul_const _)

theorem gueVec_integral_zero (t : ℝ≥0) (v : Fin N → ℂ) (a : Fin N) :
    ∫ y, (gueCoord t y *ᵥ v) a ∂coordLaw N = 0 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall (gueVec_eq_sum t v a)),
    show coordLaw N = gaussianProduct (fun _ => (1 : ℝ≥0)) from rfl]
  have hi : ∀ j : (Fin N × Fin N) × Fin 2, Integrable (fun y : ((Fin N × Fin N) × Fin 2) → ℝ =>
      ((y j : ℝ) : ℂ) * (gueCoord t (Pi.single j (1 : ℝ)) *ᵥ v) a)
      (gaussianProduct (fun _ => (1 : ℝ≥0))) := fun j =>
    ((coord_integrable j).ofReal (𝕜 := ℂ)).mul_const _
  rw [integral_finsetSum _ (fun j _ => hi j)]
  apply Finset.sum_eq_zero
  intro j _
  rw [integral_mul_const, integral_complex_ofReal, coord_integral_zero]
  simp

/-- `‖ ‖G v‖² ‖_{L^p} ≤ 2C² p ‖v‖²` under `GUE_N(1/N)` (coordinates). -/
theorem gueVec_eLpNorm_le (hLp : GaussianLpGradient) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 1 ≤ p → ∀ (N : ℕ), 0 < N → ∀ v : Fin N → ℂ,
      eLpNorm (fun y => nsq (gueCoord (Real.toNNReal (1 / N)) y *ᵥ v)) (ENNReal.ofReal p)
          (coordLaw N) ≤ ENNReal.ofReal (2 * C ^ 2 * p * nsq v) := by
  obtain ⟨C, hC, hLp'⟩ := hLp
  refine ⟨C, hC, ?_⟩
  intro p hp N hN v
  set t := Real.toNNReal (1 / N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : (t : ℝ) = 1 / N := Real.coe_toNNReal _ (by positivity)
  set ℓ := fun (a : Fin N) (y : ((Fin N × Fin N) × Fin 2) → ℝ) => (gueCoord t y *ᵥ v) a
  have hmeas : ∀ a, AEStronglyMeasurable (ℓ a) (coordLaw N) := fun a =>
    (gueVec_contDiff t v a).continuous.aestronglyMeasurable
  -- each coordinate in L^{2p}
  have h2p : 1 ≤ 2 * p := by linarith
  have hcoord : ∀ a, eLpNorm (ℓ a) (ENNReal.ofReal (2 * p)) (coordLaw N) ≤
      ENNReal.ofReal (C * Real.sqrt (2 * p) * Real.sqrt ((t : ℝ) * nsq v)) := by
    intro a
    have h := hLp' (2 * p) h2p ((Fin N × Fin N) × Fin 2) (fun _ => 1) (ℓ a)
      (gueVec_contDiff t v a) (gueVec_memLp t v a _ ENNReal.ofReal_ne_top)
    have hint : ∫ y, ℓ a y ∂gaussianProduct (fun _ => (1 : ℝ≥0)) = 0 :=
      gueVec_integral_zero t v a
    simp only [hint, sub_zero] at h
    refine h.trans ?_
    have hg : eLpNorm (weightedGradientNorm (fun _ => (1 : ℝ≥0)) (ℓ a)) (ENNReal.ofReal (2 * p))
        (coordLaw N) ≤ ENNReal.ofReal (Real.sqrt ((t : ℝ) * nsq v)) := by
      have := eLpNorm_le_of_ae_bound (μ := coordLaw N) (p := ENNReal.ofReal (2 * p))
        (f := weightedGradientNorm (fun _ => (1 : ℝ≥0)) (ℓ a))
        (C := Real.sqrt ((t : ℝ) * nsq v))
        (by
          have he : weightedGradientNorm (fun _ => (1 : ℝ≥0)) (ℓ a) =
              fun _ => Real.sqrt ((t : ℝ) * nsq v) := funext (gueVec_grad t v a)
          rw [he]; exact aestronglyMeasurable_const)
        (Filter.Eventually.of_forall (fun y => by
          rw [gueVec_grad, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]))
      rwa [measure_univ, ENNReal.one_rpow, one_mul] at this
    calc ENNReal.ofReal (C * Real.sqrt (2 * p)) *
          eLpNorm (weightedGradientNorm (fun _ => (1 : ℝ≥0)) (ℓ a)) (ENNReal.ofReal (2 * p))
            (gaussianProduct fun _ => 1)
        ≤ ENNReal.ofReal (C * Real.sqrt (2 * p)) * ENNReal.ofReal (Real.sqrt ((t : ℝ) * nsq v)) := by
          gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  -- squares
  have hsq : ∀ a, eLpNorm (fun y => ‖ℓ a y‖ ^ (2 : ℝ)) (ENNReal.ofReal p) (coordLaw N) ≤
      ENNReal.ofReal (2 * C ^ 2 * p * ((t : ℝ) * nsq v)) := by
    intro a
    rw [eLpNorm_norm_rpow _ (hmeas a) two_pos, ← ENNReal.ofReal_mul (by linarith),
      mul_comm p 2]
    refine (ENNReal.rpow_le_rpow (hcoord a) (by norm_num)).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      Real.rpow_two, Real.rpow_two, Real.rpow_two, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (mul_nonneg (NNReal.coe_nonneg _) (nsq_nonneg v))]
    nlinarith [sq_nonneg C]
  have hfun : (fun y => nsq (gueCoord t y *ᵥ v)) = ∑ a, fun y => ‖ℓ a y‖ ^ (2 : ℝ) := by
    funext y
    rw [Finset.sum_apply]
    unfold nsq
    apply Finset.sum_congr rfl
    intro a _
    rw [Real.rpow_two]
  rw [hfun]
  refine (eLpNorm_sum_le (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp)).trans ?_
  calc ∑ a, eLpNorm (fun y => ‖ℓ a y‖ ^ (2 : ℝ)) (ENNReal.ofReal p) (coordLaw N)
      ≤ ∑ _a : Fin N, ENNReal.ofReal (2 * C ^ 2 * p * ((t : ℝ) * nsq v)) :=
        Finset.sum_le_sum (fun a _ => hsq a)
    _ = ENNReal.ofReal (2 * C ^ 2 * p * nsq v) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ht]
        congr 1
        field_simp

end BlockBand.Palm.CoarseRelative
