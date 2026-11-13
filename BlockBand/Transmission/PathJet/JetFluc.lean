module

public import BlockBand.Transmission.PathJet.JetGrad

/-!
# The `C_p/W` fluctuation of the fresh jet (regularized layer)

The jet analogue of `grad_tau_reg` and `tau_centered_reg` (`PassiveLayer.FlucMain`).

* `grad_tau2_reg`: the weighted gradient norm of `ρ ↦ τ₂(𝒢_reg(ρ))` is `≤ 2√8‖𝒢‖³/W`;
* `tau2_centered_reg`: the Gaussian `L^p` gradient inequality (`LpGradientBody C₀`) gives
  `‖τ₂ - Eτ₂‖_p ≤ C₀√p · (2√8/W) · ‖‖𝒢‖³‖_p` for the regularized input `regX X ε`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

open Matrix MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.Inputs BlockBand.Transmission.PassiveLayer
open scoped Matrix.Norms.L2Operator ComplexOrder NNReal ENNReal

open BlockBand.Transmission

variable {W : ℕ}

theorem grad_tau2_reg {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) {w : ℂ}
    (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ}
    (hε : 0 < ε) (ρ : CoordW W → ℝ) :
    weightedGradientNorm (coordVar W b) (fun ρ => tau2Map W (gReg E w b X ε ρ)) ρ ≤
      2 * Real.sqrt 8 * ‖gReg E w b X ε ρ‖ ^ 3 / W := by
  set G := gReg E w b X ε ρ
  set A := jetK W G
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  unfold weightedGradientNorm
  have hterm : ∀ i, ‖fderiv ℝ (fun ρ => tau2Map W (gReg E w b X ε ρ)) ρ (Pi.single i 1)‖ ^ 2 =
      4 * ((W : ℝ)⁻¹ ^ 2 * ‖(A * layerDir b (Pi.single i 1)).trace‖ ^ 2) := by
    intro i
    rw [fderiv_tau2_gReg E hw b hY hε ρ i, norm_neg, norm_mul, norm_mul, norm_inv,
      Complex.norm_natCast, show ‖(2 : ℂ)‖ = 2 by simp]
    ring
  simp only [hterm]
  have hsum : ∑ i, (coordVar W b i : ℝ) * (4 * ((W : ℝ)⁻¹ ^ 2 *
      ‖(A * layerDir b (Pi.single i 1)).trace‖ ^ 2)) ≤ 4 * ((W : ℝ)⁻¹ ^ 2 * (4 / W * hsSq A)) := by
    have := layerDir_trace_sum_le hb0 hb hW A
    calc _ = 4 * ((W : ℝ)⁻¹ ^ 2 * ∑ i, (coordVar W b i : ℝ) *
          ‖(A * layerDir b (Pi.single i 1)).trace‖ ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ _ := by gcongr
  have hA : ‖A‖ ≤ ‖G‖ ^ 3 := norm_jetK_le G
  have hhs : hsSq A ≤ 2 * W * ‖G‖ ^ 6 := by
    have h := hsSq_le_card A
    rw [card_layerSite] at h
    have : ‖A‖ ^ 2 ≤ (‖G‖ ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
    push_cast at h
    nlinarith [norm_nonneg A]
  have hfin : 4 * ((W : ℝ)⁻¹ ^ 2 * (4 / W * hsSq A)) ≤ (2 * Real.sqrt 8 * ‖G‖ ^ 3 / W) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    have h4 : 0 ≤ 4 / (W : ℝ) := by positivity
    calc 4 * ((W : ℝ)⁻¹ ^ 2 * (4 / W * hsSq A)) ≤
        4 * ((W : ℝ)⁻¹ ^ 2 * (4 / W * (2 * W * ‖G‖ ^ 6))) := by gcongr
      _ = _ := by field_simp; ring
  refine (Real.sqrt_le_sqrt (hsum.trans hfin)).trans ?_
  rw [Real.sqrt_sq (by positivity)]

/-- The fresh jet functional `τ₂(𝒢(w))` of the layer. -/
def tau2Layer (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    ℂ := tau2Map W (layerAt E w X ω)

theorem measurable_tau2Layer (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (tau2Layer (W := W) E w X) :=
  continuous_tau2Map.measurable.comp (PassiveLayer.measurable_layerAt E w X)

theorem tau2_centered_reg {C₀ : ℝ} (hLp : LpGradientBody C₀) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hW : 1 ≤ W) (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε) {p : ℝ} (hp : 1 ≤ p)
    (hMem : MemLp (tau2Layer E w (regX X ε)) (ENNReal.ofReal p) (freshLaw W b)) :
    eLpNorm (fun ω => tau2Layer E w (regX X ε) ω - ∫ ω', tau2Layer E w (regX X ε) ω' ∂freshLaw W b)
        (ENNReal.ofReal p) (freshLaw W b) ≤
      ENNReal.ofReal (C₀ * Real.sqrt p) * (ENNReal.ofReal (2 * Real.sqrt 8 / W) *
        eLpNorm (fun ω => ‖layerAt E w (regX X ε) ω‖ ^ 3) (ENNReal.ofReal p) (freshLaw W b)) := by
  set F := tau2Layer E w (regX X ε)
  set f : (CoordW W → ℝ) → ℂ := fun ρ => tau2Map W (gReg E w b X ε ρ)
  have hfF : f = F ∘ coordMap W b := rfl
  have hcm := measurable_coordMap W b
  have hG : ContDiff ℝ 1 fun ρ => gReg E w b X ε ρ :=
    (contDiff_layerResolvent_reg E hw b hY hε).of_le le_top
  have hfc : ContDiff ℝ 1 f := contDiff_tau2_comp hG
  have hFm : AEStronglyMeasurable F ((gaussianProduct (coordVar W b)).map (coordMap W b)) := by
    rw [← freshLaw_eq_map]; exact hMem.aestronglyMeasurable
  have hMf : MemLp f (ENNReal.ofReal p) (gaussianProduct (coordVar W b)) := by
    rw [hfF]
    exact (memLp_map_measure_iff hFm hcm.aemeasurable).mp (by rw [← freshLaw_eq_map]; exact hMem)
  have h := hLp p hp (CoordW W) (coordVar W b) f hfc hMf
  have hk0 : 0 ≤ 2 * Real.sqrt 8 / W := by positivity
  have hpw : Measurable fun ω => ‖layerAt E w (regX X ε) ω‖ ^ 3 :=
    (continuous_norm.measurable.comp (PassiveLayer.measurable_layerAt E w _)).pow_const 3
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
      (gaussianProduct (coordVar W b)) ≤ ENNReal.ofReal (2 * Real.sqrt 8 / W) *
        eLpNorm (fun ω => ‖layerAt E w (regX X ε) ω‖ ^ 3) (ENNReal.ofReal p) (freshLaw W b) := by
    have hpt : ∀ ρ, ‖weightedGradientNorm (coordVar W b) f ρ‖ ≤
        (2 * Real.sqrt 8 / W) * ‖layerAt E w (regX X ε) (coordMap W b ρ)‖ ^ 3 := by
      intro ρ
      rw [Real.norm_of_nonneg (by unfold weightedGradientNorm; exact Real.sqrt_nonneg _)]
      refine (grad_tau2_reg hb0 hb hW E hw hY hε ρ).trans (le_of_eq ?_)
      simp only [gReg, layerAt]; ring
    have hcont : Continuous (weightedGradientNorm (coordVar W b) f) := by
      unfold weightedGradientNorm
      have hd := hfc.continuous_fderiv one_ne_zero
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
      exact continuous_const.mul ((hd.clm_apply continuous_const).norm.pow 2)
    refine (eLpNorm_mono_real hcont.aestronglyMeasurable hpt).trans (le_of_eq ?_)
    have hsm := eLpNorm_const_smul (2 * Real.sqrt 8 / W)
      ((fun ω => ‖layerAt E w (regX X ε) ω‖ ^ 3) ∘ coordMap W b) (ENNReal.ofReal p)
      (gaussianProduct (coordVar W b))
    rw [show ((2 * Real.sqrt 8 / W) • ((fun ω => ‖layerAt E w (regX X ε) ω‖ ^ 3) ∘ coordMap W b)) =
        fun ρ => 2 * Real.sqrt 8 / W * ‖layerAt E w (regX X ε) (coordMap W b ρ)‖ ^ 3 from rfl] at hsm
    rw [hsm, Real.enorm_eq_ofReal hk0, freshLaw_eq_map,
      eLpNorm_map_measure (by rw [← freshLaw_eq_map]; exact hpw.aestronglyMeasurable)
        hcm.aemeasurable]
  rw [hLHS]
  exact h.trans (by gcongr)

end BlockBand.Transmission.PathJet
