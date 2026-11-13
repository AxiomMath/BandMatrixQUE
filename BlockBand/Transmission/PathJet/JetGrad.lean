module

public import BlockBand.Transmission.PassiveLayer.FlucMain
public import BlockBand.Transmission.PassiveCovariance.MeanField

/-!
# The fresh jet as a layer functional and its Gaussian gradient

The fresh jet is `∂_w W⁻¹Tr(w - X₊)⁻¹ = -W⁻¹Tr R₊²` and `R₊ = 𝒢₂₂` a.s., so it is
`-τ₂(𝒢)` with `τ₂(G) = W⁻¹tr(P₂GP₂G)` (`tau2Map`). Along a line `M + tN`,
`∂_t τ₂((M+tN)⁻¹) = -2W⁻¹tr(K N)`, `K = GP₂GP₂G` (`hasDerivAt_tau2_line`). With the
Hilbert–Schmidt contraction `layerDir_trace_sum_le` and `‖K‖²_HS ≤ 2W‖G‖⁶`, the weighted
gradient norm of `τ₂ ∘ 𝒢_reg` is `≤ 2√8‖G‖³/W` (`grad_tau2_reg`).
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

/-- `τ₂(G) = W⁻¹ tr(P₂GP₂G)`; on the layer resolvent this is `W⁻¹Tr 𝒢₂₂²`. -/
def tau2Map (W : ℕ) (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    ℂ := (W : ℂ)⁻¹ * (pTwo W * G * pTwo W * G).trace

/-- The matrix `K = GP₂GP₂G` of the jet gradient. -/
def jetK (W : ℕ) (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  G * pTwo W * G * pTwo W * G

theorem continuous_tau2Map : Continuous (tau2Map W) := by
  unfold tau2Map
  refine continuous_const.mul ?_
  have hc : Continuous fun G : Matrix (LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort) ℂ => pTwo W * G * pTwo W * G :=
    (((continuous_const.mul continuous_id).mul continuous_const).mul continuous_id)
  exact (Matrix.traceLinearMap (LayerSite W .oneBlockOnePort) ℂ ℂ).toContinuousLinearMap.continuous.comp hc

theorem norm_trace_layer_le (M : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    ‖M.trace‖ ≤ 2 * W * ‖M‖ := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ z, ‖M z z‖ ≤ ∑ _z : LayerSite W .oneBlockOnePort, ‖M‖ :=
        Finset.sum_le_sum fun z _ => norm_entry_le' _ _ _
    _ = 2 * W * ‖M‖ := by simp; left; ring

theorem norm_tau2Map_le (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    ‖tau2Map W G‖ ≤ 2 * ‖G‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp [tau2Map]
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hP := norm_pTwo_le (W := W)
  have hP0 := norm_nonneg (pTwo W)
  have hG0 := norm_nonneg G
  have hn : ‖pTwo W * G * pTwo W * G‖ ≤ ‖G‖ ^ 2 := by
    have h1 : ‖pTwo W * G‖ ≤ ‖G‖ := (norm_mul_le _ _).trans (by nlinarith)
    have h2 : ‖pTwo W * G * pTwo W‖ ≤ ‖G‖ := (norm_mul_le _ _).trans (by nlinarith)
    calc _ ≤ ‖pTwo W * G * pTwo W‖ * ‖G‖ := norm_mul_le _ _
      _ ≤ ‖G‖ * ‖G‖ := by gcongr
      _ = ‖G‖ ^ 2 := (sq _).symm
  rw [tau2Map, norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖(pTwo W * G * pTwo W * G).trace‖
      ≤ (W : ℝ)⁻¹ * (2 * W * ‖G‖ ^ 2) := by
        gcongr; exact (norm_trace_layer_le _).trans (by gcongr)
    _ = 2 * ‖G‖ ^ 2 := by field_simp

theorem norm_jetK_le (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    ‖jetK W G‖ ≤ ‖G‖ ^ 3 := by
  have hP := norm_pTwo_le (W := W)
  have hP0 := norm_nonneg (pTwo W)
  have hG0 := norm_nonneg G
  have h1 : ‖G * pTwo W‖ ≤ ‖G‖ := (norm_mul_le _ _).trans (by nlinarith)
  have h2 : ‖G * pTwo W * G * pTwo W‖ ≤ ‖G‖ ^ 2 := by
    calc _ ≤ ‖G * pTwo W * G‖ * ‖pTwo W‖ := norm_mul_le _ _
      _ ≤ ‖G * pTwo W * G‖ := by
          have := norm_nonneg (G * pTwo W * G); nlinarith
      _ ≤ ‖G * pTwo W‖ * ‖G‖ := norm_mul_le _ _
      _ ≤ ‖G‖ * ‖G‖ := by gcongr
      _ = ‖G‖ ^ 2 := (sq _).symm
  calc ‖jetK W G‖ ≤ ‖G * pTwo W * G * pTwo W‖ * ‖G‖ := norm_mul_le _ _
    _ ≤ ‖G‖ ^ 2 * ‖G‖ := by gcongr
    _ = ‖G‖ ^ 3 := by ring

theorem contDiff_tau2_comp {ι : Type*} [Fintype ι]
    {G : (ι → ℝ) → Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ}
    (hG : ContDiff ℝ 1 G) : ContDiff ℝ 1 fun ρ => tau2Map W (G ρ) := by
  have h1 : ContDiff ℝ 1 fun ρ => pTwo W * G ρ * pTwo W * G ρ :=
    ((contDiff_const.mul hG).mul contDiff_const).mul hG
  have h2 := ((Matrix.traceLinearMap (LayerSite W .oneBlockOnePort) ℂ ℂ).toContinuousLinearMap.restrictScalars
    ℝ).contDiff.comp h1
  exact contDiff_const.mul h2

/-- Derivative of `τ₂` along an affine line of matrices: `-2W⁻¹tr(KN)`. -/
theorem hasDerivAt_tau2_line (M N : Matrix (LayerSite W .oneBlockOnePort)
    (LayerSite W .oneBlockOnePort) ℂ) (hM : IsUnit M) :
    HasDerivAt (fun t : ℝ => tau2Map W ((M + (t : ℂ) • N)⁻¹))
      (-(2 * ((W : ℂ)⁻¹ * (jetK W M⁻¹ * N).trace))) 0 := by
  set P := pTwo W
  have hG := hasDerivAt_inv_line M N hM
  have h0 : (M + ((0 : ℝ) : ℂ) • N)⁻¹ = M⁻¹ := by simp
  have hA := ((hG.const_mul P).mul_const P).mul hG
  simp only [h0] at hA
  have ht := (((Matrix.traceLinearMap (LayerSite W .oneBlockOnePort) ℂ ℂ).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hA).const_mul ((W : ℂ)⁻¹)
  convert ht using 1
  · funext t; simp [tau2Map, Function.comp, P, Matrix.mul_assoc]
  simp only [ContinuousLinearMap.coe_restrictScalars', LinearMap.coe_toContinuousLinearMap',
    Matrix.traceLinearMap_apply]
  set G := M⁻¹
  have e1 : (P * -(G * N * G) * P * G).trace = -(jetK W G * N).trace := by
    rw [show P * -(G * N * G) * P * G = -((P * G) * N * (G * P * G)) by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]]
    rw [trace_neg, Matrix.trace_mul_cycle]
    simp only [jetK, P, Matrix.mul_assoc]
  have e2 : (P * G * P * -(G * N * G)).trace = -(jetK W G * N).trace := by
    rw [show P * G * P * -(G * N * G) = -((P * G * P * G) * N * G) by
      simp only [Matrix.mul_neg, Matrix.mul_assoc]]
    rw [trace_neg, Matrix.trace_mul_cycle]
    simp only [jetK, P, Matrix.mul_assoc]
  rw [Matrix.trace_add, e1, e2]
  ring

theorem fderiv_tau2_gReg (E : ℝ) {w : ℂ} (hw : 0 < w.im) (b : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε) (ρ : CoordW W → ℝ) (i : CoordW W) :
    fderiv ℝ (fun ρ => tau2Map W (gReg E w b X ε ρ)) ρ (Pi.single i 1) =
      -(2 * ((W : ℂ)⁻¹ * (jetK W (gReg E w b X ε ρ) * layerDir b (Pi.single i 1)).trace)) := by
  have hMu := (layer_isUnit_reg E hw hY hε (coordMap_hermitian b ρ)).2.1
  have hG : ContDiff ℝ 1 fun ρ => gReg E w b X ε ρ :=
    (contDiff_layerResolvent_reg E hw b hY hε).of_le le_top
  have hc : ContDiff ℝ 1 fun ρ => tau2Map W (gReg E w b X ε ρ) :=
    contDiff_tau2_comp hG
  refine fderiv_apply_eq_of_line ((hc.differentiable (by simp)) ρ) ?_
  have hline : (fun t : ℝ => tau2Map W (gReg E w b X ε (ρ + t • Pi.single i 1))) =
      fun t : ℝ => tau2Map W ((layerMatrix .oneBlockOnePort E w (liftX (regX X ε)) (coordMap W b ρ) +
          (t : ℂ) • layerDir b (Pi.single i 1))⁻¹) := by
    funext t
    simp only [gReg, layerResolvent, layerMatrix_line]
  rw [hline]
  exact hasDerivAt_tau2_line _ _ hMu

end BlockBand.Transmission.PathJet
