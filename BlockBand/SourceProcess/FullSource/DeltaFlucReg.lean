module

public import BlockBand.SourceProcess.FullSource.DeltaFlucGrad

/-!
# The Gaussian `L^p` bound for `x*K𝒢₁₁Ky` at the regularized input

The centered `L^p` bound of `x*K𝒢₁₁Ky` at the regularized input, from the Gaussian `L^p`
gradient inequality and moment bounds for the gradient weight.

* `dLayer E w X x y ω = x*(Kι₁ 𝒢 ι₁*K)y = x*K𝒢₁₁Ky`;
* `dWeight = (‖K𝒢₁₁‖ + ‖L‖)(1 + ‖𝒢‖(5 + ‖A‖ + ‖B‖))`, which dominates `‖Kι₁𝒢‖‖𝒢ι₁*K‖`
  (`pq_le_weight`, wherever the layer matrix is invertible, for `|w| + |E| ≤ 5`);
* `dWeight_mom`: `‖dWeight‖_p ≤ C_Λ`, uniformly in passive `X`, `W ≥ W₀`, `E ∈ bulkInterval κ`
  (`moments` at `4p`, `‖A‖, ‖B‖ ∈ L^{4p}`, Hölder).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance (vecNorm_nonneg norm_bilinear_le)
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator NNReal ENNReal

variable {W : ℕ}

/-- `φ = x*K𝒢₁₁Ky` (in the form `x*(Kι₁ 𝒢 ι₁*K)y`). -/
def dLayer (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  bilinear x (pK w X * layerAt E w X ω * qK w X) y

/-- The gradient weight `(‖K𝒢₁₁‖ + ‖L‖)(1 + ‖𝒢‖(5 + ‖A‖ + ‖B‖))`. -/
def dWeight (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    ℝ :=
  (‖kG11 E w X ω‖ + ‖lAt E w X ω‖) * (1 + ‖layerAt E w X ω‖ * (5 + ‖ω.1 0‖ + ‖ω.2 0 0‖))

theorem measurable_dLayer (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ) :
    Measurable (dLayer E w X x y) :=
  (dCLM (pK w X) (qK w X) x y).continuous.measurable.comp (measurable_layerAt E w X)

theorem measurable_dWeight (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (dWeight (W := W) E w X) := by
  have hA : Measurable fun ω : LayerSample W .oneBlockOnePort => ‖ω.1 0‖ :=
    continuous_norm.measurable.comp ((measurable_pi_apply 0).comp measurable_fst)
  have hB : Measurable fun ω : LayerSample W .oneBlockOnePort => ‖ω.2 0 0‖ :=
    continuous_norm.measurable.comp
      ((measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp measurable_snd))
  have hk := continuous_norm.measurable.comp (measurable_kG11 E w X)
  have hl := continuous_norm.measurable.comp (measurable_lAt E w X)
  have hg := continuous_norm.measurable.comp (measurable_layerAt E w X)
  exact (hk.add hl).mul (measurable_const.add (hg.mul ((measurable_const.add hA).add hB)))

theorem dWeight_nonneg (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : 0 ≤ dWeight E w X ω := by
  unfold dWeight; positivity

/-- `‖Kι₁𝒢‖‖𝒢ι₁*K‖ ≤ dWeight` wherever the layer matrix is invertible (`|w| + |E| ≤ 5`). -/
theorem pq_le_weight (E : ℝ) {w : ℂ} (hw5 : ‖w‖ + |E| ≤ 5) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort)
    (hu : IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω)) :
    ‖pK w X * layerAt E w X ω‖ * ‖layerAt E w X ω * qK w X‖ ≤ dWeight E w X ω := by
  have h1 := norm_pK_mul_le E w X ω
  have h2 := norm_gQ_le E w X ω hu
  have h3 : 1 + ‖layerAt E w X ω‖ * (‖w‖ + |E| + ‖ω.1 0‖ + ‖ω.2 0 0‖) ≤
      1 + ‖layerAt E w X ω‖ * (5 + ‖ω.1 0‖ + ‖ω.2 0 0‖) := by
    gcongr
  exact mul_le_mul h1 (h2.trans h3) (norm_nonneg _) (by positivity)

/-- **Fixed-`ε` centered bound** from the body of `GaussianLpGradient`. -/
theorem d_centered_reg {C₀ : ℝ} (hLp : LpGradientBody C₀) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hW : 1 ≤ W) (E : ℝ) {w : ℂ} (hw : 0 < w.im) (hw5 : ‖w‖ + |E| ≤ 5)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε) {p : ℝ}
    (hp : 1 ≤ p) (x y : Fin W → ℂ)
    (hMem : MemLp (dLayer E w (regX X ε) x y) (ENNReal.ofReal p) (freshLaw W b)) :
    eLpNorm (fun ω => dLayer E w (regX X ε) x y ω -
        ∫ ω', dLayer E w (regX X ε) x y ω' ∂freshLaw W b) (ENNReal.ofReal p) (freshLaw W b) ≤
      ENNReal.ofReal (C₀ * Real.sqrt p) *
        (ENNReal.ofReal (Real.sqrt (3 * (4 / W)) * (vecNorm x * vecNorm y)) *
          eLpNorm (dWeight E w (regX X ε)) (ENNReal.ofReal p) (freshLaw W b)) := by
  set F := dLayer E w (regX X ε) x y
  set P := pK w (regX X ε)
  set Q := qK w (regX X ε)
  set f : (CoordW W → ℝ) → ℂ := fun ρ => bilinear x (P * gReg E w b X ε ρ * Q) y
  have hfF : f = F ∘ coordMap W b := rfl
  have hcm := measurable_coordMap W b
  have hfc : ContDiff ℝ 1 f := contDiff_d_gReg E hw b hY hε P Q x y
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
        eLpNorm (dWeight E w (regX X ε)) (ENNReal.ofReal p) (freshLaw W b) := by
    have hpt : ∀ ρ, ‖weightedGradientNorm (coordVar W b) f ρ‖ ≤
        k * dWeight E w (regX X ε) (coordMap W b ρ) := by
      intro ρ
      rw [Real.norm_of_nonneg (by unfold weightedGradientNorm; exact Real.sqrt_nonneg _)]
      have hu := (layer_isUnit_reg E hw hY hε (coordMap_hermitian b ρ)).2.1
      have hpq := pq_le_weight E hw5 (regX X ε) (coordMap W b ρ) hu
      refine (grad_d_reg hb0 hb hW E hw hY hε P Q x y ρ).trans ?_
      have hxy := mul_nonneg (vecNorm_nonneg x) (vecNorm_nonneg y)
      have hs := Real.sqrt_nonneg (3 * (4 / (W : ℝ)))
      calc Real.sqrt (3 * (4 / W)) * (‖P * gReg E w b X ε ρ‖ * ‖gReg E w b X ε ρ * Q‖ *
            (vecNorm x * vecNorm y))
          ≤ Real.sqrt (3 * (4 / W)) * (dWeight E w (regX X ε) (coordMap W b ρ) *
            (vecNorm x * vecNorm y)) := by gcongr; exact hpq
        _ = k * dWeight E w (regX X ε) (coordMap W b ρ) := by simp only [k]; ring
    have hcont : Continuous (weightedGradientNorm (coordVar W b) f) := by
      unfold weightedGradientNorm
      have hd := hfc.continuous_fderiv one_ne_zero
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
      exact continuous_const.mul ((hd.clm_apply continuous_const).norm.pow 2)
    refine (eLpNorm_mono_real hcont.aestronglyMeasurable hpt).trans (le_of_eq ?_)
    have hsm := eLpNorm_const_smul k (dWeight E w (regX X ε) ∘ coordMap W b) (ENNReal.ofReal p)
      (gaussianProduct (coordVar W b))
    rw [show (k • (dWeight E w (regX X ε) ∘ coordMap W b)) =
        fun ρ => k * dWeight E w (regX X ε) (coordMap W b ρ) from rfl] at hsm
    have hwm : AEStronglyMeasurable (dWeight E w (regX X ε))
        ((gaussianProduct (coordVar W b)).map (coordMap W b)) :=
      (measurable_dWeight E w _).aestronglyMeasurable
    rw [hsm, Real.enorm_eq_ofReal hk0, freshLaw_eq_map, eLpNorm_map_measure hwm hcm.aemeasurable]
  rw [hLHS]
  exact h.trans (by gcongr)

/-- **`‖dWeight‖_p ≤ C_Λ`**, uniformly over passive inputs (`moments` at `4p`). -/
theorem dWeight_mom (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) {p : ℝ} (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ w ∈ paramDisk b E,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        MomBd (freshLaw W b) (dWeight E w X) p C ∧
        MomBd (freshLaw W b) (fun ω => ‖kG11 E w X ω‖ + ‖lAt E w X ω‖) p C := by
  have hp0 : 0 < p := by linarith
  obtain ⟨C', W₀, hm⟩ := moments_holds hGA b hb0 hb κ hκ (4 * p) (by linarith)
  obtain ⟨CA, hCA0, hCA⟩ := blockA_mom hb (p := 4 * p) (by linarith)
  obtain ⟨CB, hCB0, hCB⟩ := bondB_mom hb0 (p := 4 * p) (by linarith)
  set Cm := max C' 0
  have hCm : 0 ≤ Cm := le_max_right _ _
  set CL := (Cm + Cm) * (1 + Cm * (5 + CA + CB))
  refine ⟨max CL (Cm + Cm), max W₀ 1, le_max_of_le_right (by positivity),
    fun W hW E hE w hw X hY => ?_⟩
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  obtain ⟨-, hg, hk, hl⟩ := hm W (le_of_max_le_left hW) E hE w hw X hY
  obtain ⟨hgM, hkM, hlM⟩ := letter_momBd (b := b) ⟨hg, hk, hl⟩
  have hkl : MomBd (freshLaw W b) (fun ω => ‖kG11 E w X ω‖ + ‖lAt E w X ω‖) (2 * p) (Cm + Cm) :=
    (hkM.exponent_mono (by linarith)).add (by linarith) (hlM.exponent_mono (by linarith)) hCm hCm
  have h5 : MomBd (freshLaw W b) (fun _ => (5 : ℝ)) (4 * p) 5 := by
    simpa using MomBd.const (μ := freshLaw W b) (5 : ℝ) (4 * p) (by positivity)
  have hP : MomBd (freshLaw W b) (fun ω => 5 + ‖ω.1 0‖ + ‖ω.2 0 0‖) (4 * p) (5 + CA + CB) :=
    (h5.add (by linarith) (hCA W hW1) (by norm_num) hCA0).add (by linarith) (hCB W hW1)
      (by positivity) hCB0
  have hgM4 : MomBd (freshLaw W b) (fun ω => ‖layerAt E w X ω‖) (2 * (2 * p)) Cm := by
    rw [show 2 * (2 * p) = 4 * p by ring]; exact hgM
  have hP4 : MomBd (freshLaw W b) (fun ω => 5 + ‖ω.1 0‖ + ‖ω.2 0 0‖) (2 * (2 * p))
      (5 + CA + CB) := by
    rw [show 2 * (2 * p) = 4 * p by ring]; exact hP
  have hgP := MomBd.mul (by positivity : (0 : ℝ) < 2 * p) hgM4 hP4 hCm
  have h1 : MomBd (freshLaw W b) (fun _ => (1 : ℝ)) (2 * p) 1 := by
    simpa using MomBd.const (μ := freshLaw W b) (1 : ℝ) (2 * p) (by positivity)
  have h1P := h1.add (by linarith) hgP zero_le_one (by positivity)
  refine ⟨(hkl.mul hp0 h1P (by positivity)).of_le (le_max_left _ _), ?_⟩
  exact (hkl.exponent_mono (by linarith)).of_le (le_max_right _ _)

end BlockBand.SourceProcess.FullSource
