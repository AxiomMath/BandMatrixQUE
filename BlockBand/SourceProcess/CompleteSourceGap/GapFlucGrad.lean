module

public import BlockBand.SourceProcess.CompleteSourceGap.OnePort
public import BlockBand.SourceProcess.FullSource.DeltaFlucHolds

/-!
# The gradient of the gap-letter functional `x*K𝒢₁₂𝒢₂₁Ky`

* `gapLayer E w X x y ω = x*(Kι₁ 𝒢P₂𝒢 ι₁*K)y`; at `w = z` it is `x*Γy` (`bilinear_gapLetter`).
* Along a line `d𝒢 = -𝒢 dM 𝒢`, so `∂_iφ = -(x*Kι₁𝒢)(∂_iM)(𝒢P₂𝒢ι₁*Ky) - (x*Kι₁𝒢P₂𝒢)(∂_iM)(𝒢ι₁*Ky)`
  (`hasDerivAt_gap_line`, `fderiv_gap_gReg`); every factor is a bounded letter, and
  `|∇φ|_v ≤ √(12/W)·2‖Kι₁𝒢‖‖𝒢‖‖𝒢ι₁*K‖‖x‖‖y‖` (`grad_gap_reg`).
* `gap_centered_reg`: the resulting centred `L^p` bound at a fixed regularization `ε`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.PassiveLayer BlockBand.SourceProcess.FullSource
open BlockBand.Transmission.PassiveCovariance (vecNorm_nonneg norm_bilinear_le LayerMat)
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator NNReal ENNReal

variable {W : ℕ}

/-- `φ = x*(Kι₁ 𝒢P₂𝒢 ι₁*K)y`. -/
def gapLayer (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  bilinear x (pK w X * (layerAt E w X ω * pTwo W * layerAt E w X ω) * qK w X) y

theorem gapLetter_eq_pq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    gapLetter b E X ω = pK (boundaryZ b E) X *
      (layerAt E (boundaryZ b E) X ω * pTwo W * layerAt E (boundaryZ b E) X ω) *
        qK (boundaryZ b E) X := by
  have hL : freshL b E X ω = lAt E (boundaryZ b E) X ω := rfl
  rw [gapLetter, hL, lAt_eq_iota, g21_eq_iota, pTwo, qK]
  simp only [Matrix.mul_assoc]

theorem bilinear_gapLetter (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    bilinear x (gapLetter b E X ω) y = gapLayer E (boundaryZ b E) X x y ω := by
  rw [gapLetter_eq_pq]; rfl

theorem measurable_gapLayer (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ) :
    Measurable (gapLayer E w X x y) := by
  have hG := measurable_layerAt (W := W) E w X
  have hH : Measurable fun ω => layerAt E w X ω * pTwo W * layerAt E w X ω :=
    (continuous_id.matrix_mul continuous_const |>.matrix_mul continuous_id |>.measurable).comp hG
  exact (dCLM (pK w X) (qK w X) x y).continuous.measurable.comp hH

/-- Derivative of `x*(P(M + tN)⁻¹P₂(M + tN)⁻¹Q)y` at `t = 0`, in contracted form. -/
theorem hasDerivAt_gap_line (P : Matrix (Fin W) (LayerSite W .oneBlockOnePort) ℂ)
    (Q : Matrix (LayerSite W .oneBlockOnePort) (Fin W) ℂ) (x y : Fin W → ℂ) (M N : LayerMat W)
    (hM : IsUnit M) :
    HasDerivAt (fun t : ℝ =>
        bilinear x (P * ((M + (t : ℂ) • N)⁻¹ * pTwo W * (M + (t : ℂ) • N)⁻¹) * Q) y)
      (-((star x ᵥ* (P * M⁻¹)) ⬝ᵥ (N *ᵥ ((M⁻¹ * pTwo W * M⁻¹ * Q) *ᵥ y)) +
        (star x ᵥ* (P * (M⁻¹ * pTwo W * M⁻¹))) ⬝ᵥ (N *ᵥ ((M⁻¹ * Q) *ᵥ y)))) 0 := by
  have hG := hasDerivAt_inv_line M N hM
  have hG0 : (M + ((0 : ℝ) : ℂ) • N)⁻¹ = M⁻¹ := by simp
  have hH := (hG.mul_const (pTwo W)).mul hG
  have h := ((dCLM P Q x y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hH
  simp only [hG0] at h
  convert h using 1
  · funext t; rfl
  rw [ContinuousLinearMap.coe_restrictScalars', dCLM_apply, bilinear]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_add, Matrix.add_mul, add_mulVec,
    neg_mulVec, dotProduct_add, dotProduct_neg, neg_add]
  congr 1
  · congr 1; simp only [dotProduct_mulVec, vecMul_vecMul, ← mulVec_mulVec, Matrix.mul_assoc]
  · congr 1; simp only [dotProduct_mulVec, vecMul_vecMul, ← mulVec_mulVec, Matrix.mul_assoc]

theorem contDiff_gap_gReg (E : ℝ) {w : ℂ} (hw : 0 < w.im) (b : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (P : Matrix (Fin W) (LayerSite W .oneBlockOnePort) ℂ)
    (Q : Matrix (LayerSite W .oneBlockOnePort) (Fin W) ℂ) (x y : Fin W → ℂ) :
    ContDiff ℝ 1 fun ρ => bilinear x (P * (gReg E w b X ε ρ * pTwo W * gReg E w b X ε ρ) * Q) y := by
  have hG : ContDiff ℝ 1 fun ρ => gReg E w b X ε ρ :=
    (contDiff_layerResolvent_reg E hw b hY hε).of_le le_top
  exact ((dCLM P Q x y).restrictScalars ℝ).contDiff.comp ((hG.mul contDiff_const).mul hG)

/-- The directional derivatives of the regularized gap functional. -/
theorem fderiv_gap_gReg (E : ℝ) {w : ℂ} (hw : 0 < w.im) (b : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (P : Matrix (Fin W) (LayerSite W .oneBlockOnePort) ℂ)
    (Q : Matrix (LayerSite W .oneBlockOnePort) (Fin W) ℂ) (x y : Fin W → ℂ)
    (ρ : CoordW W → ℝ) (i : CoordW W) :
    fderiv ℝ (fun ρ => bilinear x (P * (gReg E w b X ε ρ * pTwo W * gReg E w b X ε ρ) * Q) y) ρ
        (Pi.single i 1) =
      -((star x ᵥ* (P * gReg E w b X ε ρ)) ⬝ᵥ (layerDir b (Pi.single i 1) *ᵥ
          ((gReg E w b X ε ρ * pTwo W * gReg E w b X ε ρ * Q) *ᵥ y)) +
        (star x ᵥ* (P * (gReg E w b X ε ρ * pTwo W * gReg E w b X ε ρ))) ⬝ᵥ
          (layerDir b (Pi.single i 1) *ᵥ ((gReg E w b X ε ρ * Q) *ᵥ y))) := by
  have hMu := (layer_isUnit_reg E hw hY hε (coordMap_hermitian b ρ)).2.1
  refine fderiv_apply_eq_of_line
    (((contDiff_gap_gReg E hw b hY hε P Q x y).differentiable (by simp)) ρ) ?_
  have hline : (fun t : ℝ => bilinear x (P * (gReg E w b X ε (ρ + t • Pi.single i 1) * pTwo W *
      gReg E w b X ε (ρ + t • Pi.single i 1)) * Q) y) =
      fun t : ℝ => bilinear x (P * ((layerMatrix .oneBlockOnePort E w (liftX (regX X ε))
        (coordMap W b ρ) + (t : ℂ) • layerDir b (Pi.single i 1))⁻¹ * pTwo W *
        (layerMatrix .oneBlockOnePort E w (liftX (regX X ε))
        (coordMap W b ρ) + (t : ℂ) • layerDir b (Pi.single i 1))⁻¹) * Q) y := by
    funext t
    simp only [gReg, layerResolvent, layerMatrix_line]
  rw [hline]
  exact hasDerivAt_gap_line P Q x y _ _ hMu

/-- **Gradient bound**: `|∇φ|_v ≤ √(12/W)·2‖P𝒢‖‖𝒢‖‖𝒢Q‖‖x‖‖y‖` at the regularized input. -/
theorem grad_gap_reg {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) {w : ℂ}
    (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ}
    (hε : 0 < ε) (P : Matrix (Fin W) (LayerSite W .oneBlockOnePort) ℂ)
    (Q : Matrix (LayerSite W .oneBlockOnePort) (Fin W) ℂ) (x y : Fin W → ℂ) (ρ : CoordW W → ℝ) :
    weightedGradientNorm (coordVar W b)
        (fun ρ => bilinear x (P * (gReg E w b X ε ρ * pTwo W * gReg E w b X ε ρ) * Q) y) ρ ≤
      Real.sqrt (3 * (4 / W)) * (2 * (‖P * gReg E w b X ε ρ‖ * ‖gReg E w b X ε ρ‖ *
        ‖gReg E w b X ε ρ * Q‖) * (vecNorm x * vecNorm y)) := by
  set G := gReg E w b X ε ρ
  have h := weightedGradientNorm_le (coordVar W b)
    (fun ρ => bilinear x (P * (gReg E w b X ε ρ * pTwo W * gReg E w b X ε ρ) * Q) y) ρ
    (fun i => layerDir b (Pi.single i 1)) 1
    (star x ᵥ* (P * G)) ((G * pTwo W * G * Q) *ᵥ y) (star x ᵥ* (P * (G * pTwo W * G)))
    ((G * Q) *ᵥ y) 0 0 (by positivity)
    (fun i => by rw [fderiv_gap_gReg E hw b hY hε P Q x y ρ i]; simp [G])
    (fun a c => layerDir_sum_le hb0 hb hW a c)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  have hv0 : vecNorm (0 : LayerSite W .oneBlockOnePort → ℂ) = 0 := by simp [vecNorm]
  simp only [hv0, mul_zero, add_zero, norm_one, one_mul]
  have hP2 : ‖pTwo W‖ ≤ 1 := norm_pTwo_le
  have hx := vecNorm_nonneg x
  have hy := vecNorm_nonneg y
  have hPG := norm_nonneg (P * G)
  have hGn := norm_nonneg G
  have hGQ := norm_nonneg (G * Q)
  have h1 : vecNorm (star x ᵥ* (P * G)) ≤ ‖P * G‖ * vecNorm x := by
    have := vecNorm_vecMul_le (star x) (P * G); rwa [vecNorm_star] at this
  have hGPG : ‖G * pTwo W * G * Q‖ ≤ ‖G‖ * ‖G * Q‖ := by
    rw [Matrix.mul_assoc]
    refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ hGQ)
    exact (Matrix.l2_opNorm_mul _ _).trans (by nlinarith)
  have h2 : vecNorm ((G * pTwo W * G * Q) *ᵥ y) ≤ ‖G‖ * ‖G * Q‖ * vecNorm y :=
    (vecNorm_mulVec_le' _ _).trans (mul_le_mul_of_nonneg_right hGPG hy)
  have hPGPG : ‖P * (G * pTwo W * G)‖ ≤ ‖P * G‖ * ‖G‖ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ hGn)
    exact (Matrix.l2_opNorm_mul _ _).trans (by nlinarith)
  have h3 : vecNorm (star x ᵥ* (P * (G * pTwo W * G))) ≤ ‖P * G‖ * ‖G‖ * vecNorm x := by
    have := vecNorm_vecMul_le (star x) (P * (G * pTwo W * G)); rw [vecNorm_star] at this
    exact this.trans (mul_le_mul_of_nonneg_right hPGPG hx)
  have h4 : vecNorm ((G * Q) *ᵥ y) ≤ ‖G * Q‖ * vecNorm y := vecNorm_mulVec_le' _ _
  have hn1 := vecNorm_nonneg (star x ᵥ* (P * G))
  have hn3 := vecNorm_nonneg (star x ᵥ* (P * (G * pTwo W * G)))
  have hn2 := vecNorm_nonneg ((G * pTwo W * G * Q) *ᵥ y)
  have hn4 := vecNorm_nonneg ((G * Q) *ᵥ y)
  calc vecNorm (star x ᵥ* (P * G)) * vecNorm ((G * pTwo W * G * Q) *ᵥ y) +
        vecNorm (star x ᵥ* (P * (G * pTwo W * G))) * vecNorm ((G * Q) *ᵥ y)
      ≤ (‖P * G‖ * vecNorm x) * (‖G‖ * ‖G * Q‖ * vecNorm y) +
          (‖P * G‖ * ‖G‖ * vecNorm x) * (‖G * Q‖ * vecNorm y) := by
        gcongr
    _ = _ := by ring

/-!
## The weight and the fixed-`ε` bound
-/

/-- The gradient weight `2(‖K𝒢₁₁‖ + ‖L‖)‖𝒢‖(1 + ‖𝒢‖(5 + ‖A‖ + ‖B‖))`. -/
def gWeight (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    ℝ :=
  2 * ((‖kG11 E w X ω‖ + ‖lAt E w X ω‖) * ‖layerAt E w X ω‖ *
    (1 + ‖layerAt E w X ω‖ * (5 + ‖ω.1 0‖ + ‖ω.2 0 0‖)))

theorem measurable_gWeight (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (gWeight (W := W) E w X) := by
  have hA : Measurable fun ω : LayerSample W .oneBlockOnePort => ‖ω.1 0‖ :=
    continuous_norm.measurable.comp ((measurable_pi_apply 0).comp measurable_fst)
  have hB : Measurable fun ω : LayerSample W .oneBlockOnePort => ‖ω.2 0 0‖ :=
    continuous_norm.measurable.comp
      ((measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp measurable_snd))
  have hk := continuous_norm.measurable.comp (measurable_kG11 E w X)
  have hl := continuous_norm.measurable.comp (measurable_lAt E w X)
  have hg := continuous_norm.measurable.comp (measurable_layerAt E w X)
  exact measurable_const.mul (((hk.add hl).mul hg).mul
    (measurable_const.add (hg.mul ((measurable_const.add hA).add hB))))

/-- `2‖Kι₁𝒢‖‖𝒢‖‖𝒢ι₁*K‖ ≤ gWeight` wherever the layer matrix is invertible (`|w| + |E| ≤ 5`). -/
theorem gap_le_weight (E : ℝ) {w : ℂ} (hw5 : ‖w‖ + |E| ≤ 5) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort)
    (hu : IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω)) :
    2 * (‖pK w X * layerAt E w X ω‖ * ‖layerAt E w X ω‖ * ‖layerAt E w X ω * qK w X‖) ≤
      gWeight E w X ω := by
  have h1 := norm_pK_mul_le E w X ω
  have h2 := norm_gQ_le E w X ω hu
  have h3 : 1 + ‖layerAt E w X ω‖ * (‖w‖ + |E| + ‖ω.1 0‖ + ‖ω.2 0 0‖) ≤
      1 + ‖layerAt E w X ω‖ * (5 + ‖ω.1 0‖ + ‖ω.2 0 0‖) := by
    gcongr
  have hg := norm_nonneg (layerAt E w X ω)
  unfold gWeight
  gcongr
  exact h2.trans h3

/-- **Fixed-`ε` centered bound** from the body of `GaussianLpGradient`. -/
theorem gap_centered_reg {C₀ : ℝ} (hLp : LpGradientBody C₀) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) {w : ℂ} (hw : 0 < w.im) (hw5 : ‖w‖ + |E| ≤ 5)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε) {p : ℝ}
    (hp : 1 ≤ p) (x y : Fin W → ℂ)
    (hMem : MemLp (gapLayer E w (regX X ε) x y) (ENNReal.ofReal p) (freshLaw W b)) :
    eLpNorm (fun ω => gapLayer E w (regX X ε) x y ω -
        ∫ ω', gapLayer E w (regX X ε) x y ω' ∂freshLaw W b) (ENNReal.ofReal p) (freshLaw W b) ≤
      ENNReal.ofReal (C₀ * Real.sqrt p) *
        (ENNReal.ofReal (Real.sqrt (3 * (4 / W)) * (vecNorm x * vecNorm y)) *
          eLpNorm (gWeight E w (regX X ε)) (ENNReal.ofReal p) (freshLaw W b)) := by
  set F := gapLayer E w (regX X ε) x y
  set P := pK w (regX X ε)
  set Q := qK w (regX X ε)
  set f : (CoordW W → ℝ) → ℂ := fun ρ =>
    bilinear x (P * (gReg E w b X ε ρ * pTwo W * gReg E w b X ε ρ) * Q) y
  have hfF : f = F ∘ coordMap W b := rfl
  have hcm := measurable_coordMap W b
  have hfc : ContDiff ℝ 1 f := contDiff_gap_gReg E hw b hY hε P Q x y
  have hFm : AEStronglyMeasurable F ((gaussianProduct (coordVar W b)).map (coordMap W b)) := by
    rw [← freshLaw_eq_map]; exact hMem.aestronglyMeasurable
  have hMf : MemLp f (ENNReal.ofReal p) (gaussianProduct (coordVar W b)) := by
    rw [hfF]
    exact (memLp_map_measure_iff hFm hcm.aemeasurable).mp (by rw [← freshLaw_eq_map]; exact hMem)
  have h := hLp p hp (CoordW W) (coordVar W b) f hfc hMf
  set k := Real.sqrt (3 * (4 / W)) * (vecNorm x * vecNorm y)
  have hk0 : 0 ≤ k := mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (vecNorm_nonneg x) (vecNorm_nonneg y))
  have hLHS : eLpNorm (fun ω => F ω - ∫ ω', F ω' ∂freshLaw W b) (ENNReal.ofReal p) (freshLaw W b) =
      eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct (coordVar W b)) (ENNReal.ofReal p)
        (gaussianProduct (coordVar W b)) := by
    rw [freshLaw_eq_map, integral_map hcm.aemeasurable hFm]
    have hg : AEStronglyMeasurable (fun ω => F ω - ∫ y, F (coordMap W b y)
        ∂gaussianProduct (coordVar W b)) ((gaussianProduct (coordVar W b)).map (coordMap W b)) :=
      hFm.sub aestronglyMeasurable_const
    rw [eLpNorm_map_measure hg hcm.aemeasurable]
    rfl
  have hgrad : eLpNorm (weightedGradientNorm (coordVar W b) f) (ENNReal.ofReal p)
      (gaussianProduct (coordVar W b)) ≤ ENNReal.ofReal k *
        eLpNorm (gWeight E w (regX X ε)) (ENNReal.ofReal p) (freshLaw W b) := by
    have hpt : ∀ ρ, ‖weightedGradientNorm (coordVar W b) f ρ‖ ≤
        k * gWeight E w (regX X ε) (coordMap W b ρ) := by
      intro ρ
      rw [Real.norm_of_nonneg (by unfold weightedGradientNorm; exact Real.sqrt_nonneg _)]
      have hu := (layer_isUnit_reg E hw hY hε (coordMap_hermitian b ρ)).2.1
      have hpq := gap_le_weight E hw5 (regX X ε) (coordMap W b ρ) hu
      refine (grad_gap_reg hb0 hb hW E hw hY hε P Q x y ρ).trans ?_
      have hxy := mul_nonneg (vecNorm_nonneg x) (vecNorm_nonneg y)
      have hs := Real.sqrt_nonneg (3 * (4 / (W : ℝ)))
      calc Real.sqrt (3 * (4 / W)) * (2 * (‖P * gReg E w b X ε ρ‖ * ‖gReg E w b X ε ρ‖ *
            ‖gReg E w b X ε ρ * Q‖) * (vecNorm x * vecNorm y))
          ≤ Real.sqrt (3 * (4 / W)) * (gWeight E w (regX X ε) (coordMap W b ρ) *
            (vecNorm x * vecNorm y)) := by gcongr; exact hpq
        _ = k * gWeight E w (regX X ε) (coordMap W b ρ) := by simp only [k]; ring
    have hcont : Continuous (weightedGradientNorm (coordVar W b) f) := by
      unfold weightedGradientNorm
      have hd := hfc.continuous_fderiv one_ne_zero
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
      exact continuous_const.mul ((hd.clm_apply continuous_const).norm.pow 2)
    refine (eLpNorm_mono_real hcont.aestronglyMeasurable hpt).trans (le_of_eq ?_)
    have hsm := eLpNorm_const_smul k (gWeight E w (regX X ε) ∘ coordMap W b) (ENNReal.ofReal p)
      (gaussianProduct (coordVar W b))
    rw [show (k • (gWeight E w (regX X ε) ∘ coordMap W b)) =
        fun ρ => k * gWeight E w (regX X ε) (coordMap W b ρ) from rfl] at hsm
    have hwm : AEStronglyMeasurable (gWeight E w (regX X ε))
        ((gaussianProduct (coordVar W b)).map (coordMap W b)) :=
      (measurable_gWeight E w _).aestronglyMeasurable
    rw [hsm, Real.enorm_eq_ofReal hk0, freshLaw_eq_map, eLpNorm_map_measure hwm hcm.aemeasurable]
  rw [hLHS]
  exact h.trans (by gcongr)

end BlockBand.SourceProcess.CompleteSourceGap
