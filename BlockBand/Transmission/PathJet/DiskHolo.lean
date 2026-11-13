module

public import BlockBand.Transmission.PathJet.DiskLayer

/-!
# Holomorphy of the layer means in the port parameter

For `Y = Y₀ + ε`, `Y₀ ⪰ 0`, `ε > 0` (e.g. `regX X n`), and any continuous linear functional
`L` on layer matrices, `w ↦ E L(𝒢(w))` has complex derivative `E L(-𝒢P𝒢)` at every
`w₀` with `Im w₀ > 0` (`hasDerivAt_integral_gW`). This is dominated differentiation under the
integral, with the deterministic bound `‖𝒢(w)‖ ≤ (min ε (Im w₀/2))⁻¹` on the ball of radius
`Im w₀/2` (`norm_gW_le`).

Specializations: the normalized physical and port traces `v(w) = E⟨𝒢₁₁(w)⟩`,
`u(w) = E⟨𝒢₂₂(w)⟩` (`vW`, `uW`), `hasDerivAt_vW`, `hasDerivAt_uW`, `differentiableOn_vW`,
`differentiableOn_uW` on the open upper half-plane.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

open MeasureTheory Matrix Filter Topology Metric
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Holomorphy of layer means** (dominated differentiation). -/
theorem hasDerivAt_integral_gW (b E : ℝ) {X Y₀ : Matrix (Fin W) (Fin W) ℂ} {ε : ℝ}
    (hε : 0 < ε) (hY₀ : Y₀.PosSemidef) (hYe : passiveY X = Y₀ + ε • (1 : Matrix (Fin W) (Fin W) ℂ))
    (L : LayerMat W →L[ℂ] ℂ) {w₀ : ℂ} (hw₀ : 0 < w₀.im) :
    Integrable (fun ω => L (-(gW E w₀ X ω * portProj W * gW E w₀ X ω))) (freshLaw W b) ∧
      HasDerivAt (fun w => ∫ ω, L (gW E w X ω) ∂freshLaw W b)
        (∫ ω, L (-(gW E w₀ X ω * portProj W * gW E w₀ X ω)) ∂freshLaw W b) w₀ := by
  set r := w₀.im / 2 with hr
  have hr0 : 0 < r := by positivity
  set m := min ε r
  have hm : 0 < m := lt_min hε hr0
  have hYpd : (passiveY X).PosDef := by
    rw [hYe]; exact Matrix.PosDef.posSemidef_add hY₀ (Matrix.PosDef.one.smul hε)
  have him : ∀ w ∈ ball w₀ r, r < w.im := by
    intro w hw
    have h1 : |w.im - w₀.im| ≤ ‖w - w₀‖ := by
      rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h2 : ‖w - w₀‖ < r := by rwa [mem_ball, dist_eq_norm] at hw
    have := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
    linarith
  have hGb : ∀ ω : LayerSample W .oneBlockOnePort, (ω.1 0).IsHermitian → ∀ w ∈ ball w₀ r,
      ‖gW E w X ω‖ ≤ m⁻¹ := by
    intro ω hA w hw
    have hwi := him w hw
    refine (norm_gW_le E (hr0.trans hwi) hε hY₀ hYe ω hA).trans ?_
    exact inv_anti₀ hm (min_le_min le_rfl hwi.le)
  set B : ℝ := ‖L‖ * (m⁻¹ * ‖portProj W‖ * m⁻¹)
  have hmeas : ∀ w, Measurable fun ω => gW E w X ω := fun w => measurable_layerRes E w X
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := freshLaw W b)
    (F := fun w ω => L (gW E w X ω))
    (F' := fun w ω => L (-(gW E w X ω * portProj W * gW E w X ω))) (bound := fun _ => B)
    (ball_mem_nhds w₀ hr0) (Eventually.of_forall fun w =>
      (L.continuous.measurable.comp (hmeas w)).aestronglyMeasurable) ?_ ?_ ?_
    (integrable_const B) ?_
  · refine Integrable.of_bound (L.continuous.measurable.comp (hmeas w₀)).aestronglyMeasurable
      (‖L‖ * m⁻¹) ((PathScalar.ae_layer_herm b).mono fun ω hA => ?_)
    exact (L.le_opNorm _).trans (by
      gcongr; exact hGb ω hA w₀ (mem_ball_self hr0))
  · exact (L.continuous.measurable.comp (((hmeas w₀).mul_const _).mul (hmeas w₀)).neg).aestronglyMeasurable
  · refine (PathScalar.ae_layer_herm b).mono fun ω hA w hw => ?_
    refine (L.le_opNorm _).trans ?_
    rw [norm_neg]
    have hG := hGb ω hA w hw
    have hP := norm_nonneg (portProj W)
    have := norm_nonneg (gW E w X ω)
    show ‖L‖ * _ ≤ ‖L‖ * (m⁻¹ * ‖portProj W‖ * m⁻¹)
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg L)
    calc ‖gW E w X ω * portProj W * gW E w X ω‖
        ≤ ‖gW E w X ω‖ * ‖portProj W‖ * ‖gW E w X ω‖ := by
          refine (norm_mul_le _ _).trans ?_
          gcongr; exact norm_mul_le _ _
      _ ≤ m⁻¹ * ‖portProj W‖ * m⁻¹ := by gcongr
  · refine (PathScalar.ae_layer_herm b).mono fun ω hA w hw => ?_
    have hu := isUnit_layerMatrix_w E (hr0.trans (him w hw)) hYpd ω hA
    exact L.hasFDerivAt.comp_hasDerivAt w (hasDerivAt_gW E w X ω hu)

/-- The normalized physical trace functional `M ↦ W⁻¹ Σ_x M_{xx}` (physical block). -/
def physCLM (W : ℕ) : LayerMat W →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (W : ℂ)⁻¹ * ∑ x : Fin W, M (phys x) (phys x)
      map_add' := fun M N => by simp [Finset.sum_add_distrib, mul_add]
      map_smul' := fun c M => by simp [Finset.mul_sum]; ring_nf }

/-- The normalized port trace functional `M ↦ W⁻¹ Σ_x M_{x̄x̄}`. -/
def portCLM (W : ℕ) : LayerMat W →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (W : ℂ)⁻¹ * ∑ x : Fin W, M (port x) (port x)
      map_add' := fun M N => by simp [Finset.sum_add_distrib, mul_add]
      map_smul' := fun c M => by simp [Finset.mul_sum]; ring_nf }

theorem physCLM_apply (M : LayerMat W) :
    physCLM W M = (W : ℂ)⁻¹ * ∑ x : Fin W, M (phys x) (phys x) := rfl

theorem portCLM_apply (M : LayerMat W) :
    portCLM W M = (W : ℂ)⁻¹ * ∑ x : Fin W, M (port x) (port x) := rfl

/-- `v(w) = E⟨𝒢₁₁(w)⟩`. -/
def vW (b E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  ∫ ω, (W : ℂ)⁻¹ * (passiveLetter E w X ω 0).trace ∂freshLaw W b

/-- `u(w) = E⟨𝒢₂₂(w)⟩` (`= E W⁻¹Tr (w - X₊)⁻¹` a.s.). -/
def uW (b E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  ∫ ω, (W : ℂ)⁻¹ * (passiveLetter E w X ω 3).trace ∂freshLaw W b

theorem vW_eq (b E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    vW b E w X = ∫ ω, physCLM W (gW E w X ω) ∂freshLaw W b := rfl

theorem uW_eq (b E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    uW b E w X = ∫ ω, portCLM W (gW E w X ω) ∂freshLaw W b := rfl

theorem hasDerivAt_vW (b E : ℝ) {X Y₀ : Matrix (Fin W) (Fin W) ℂ} {ε : ℝ} (hε : 0 < ε)
    (hY₀ : Y₀.PosSemidef) (hYe : passiveY X = Y₀ + ε • (1 : Matrix (Fin W) (Fin W) ℂ))
    {w₀ : ℂ} (hw₀ : 0 < w₀.im) :
    HasDerivAt (fun w => vW b E w X)
      (∫ ω, physCLM W (-(gW E w₀ X ω * portProj W * gW E w₀ X ω)) ∂freshLaw W b) w₀ :=
  (hasDerivAt_integral_gW b E hε hY₀ hYe (physCLM W) hw₀).2

theorem hasDerivAt_uW (b E : ℝ) {X Y₀ : Matrix (Fin W) (Fin W) ℂ} {ε : ℝ} (hε : 0 < ε)
    (hY₀ : Y₀.PosSemidef) (hYe : passiveY X = Y₀ + ε • (1 : Matrix (Fin W) (Fin W) ℂ))
    {w₀ : ℂ} (hw₀ : 0 < w₀.im) :
    HasDerivAt (fun w => uW b E w X)
      (∫ ω, portCLM W (-(gW E w₀ X ω * portProj W * gW E w₀ X ω)) ∂freshLaw W b) w₀ :=
  (hasDerivAt_integral_gW b E hε hY₀ hYe (portCLM W) hw₀).2

theorem differentiableOn_vW (b E : ℝ) {X Y₀ : Matrix (Fin W) (Fin W) ℂ} {ε : ℝ} (hε : 0 < ε)
    (hY₀ : Y₀.PosSemidef) (hYe : passiveY X = Y₀ + ε • (1 : Matrix (Fin W) (Fin W) ℂ)) :
    DifferentiableOn ℂ (fun w => vW b E w X) {w | 0 < w.im} := fun _ hw =>
  (hasDerivAt_vW b E hε hY₀ hYe hw).differentiableAt.differentiableWithinAt

theorem differentiableOn_uW (b E : ℝ) {X Y₀ : Matrix (Fin W) (Fin W) ℂ} {ε : ℝ} (hε : 0 < ε)
    (hY₀ : Y₀.PosSemidef) (hYe : passiveY X = Y₀ + ε • (1 : Matrix (Fin W) (Fin W) ℂ)) :
    DifferentiableOn ℂ (fun w => uW b E w X) {w | 0 < w.im} := fun _ hw =>
  (hasDerivAt_uW b E hε hY₀ hYe hw).differentiableAt.differentiableWithinAt

end BlockBand.Transmission.PathJet
