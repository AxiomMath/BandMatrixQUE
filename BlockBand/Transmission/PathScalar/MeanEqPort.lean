module

public import BlockBand.Transmission.PathScalar.MeanEqUnif

/-!
# The port mean equation (trace form), uniformly on `bulkInterval κ`

For strictly passive `X`, the mean port trace `u` and the mean physical trace `v = E⟨𝒢₁₁⟩`
satisfy `|u(z - bv) - 1| ≤ C/W²`, uniformly on `bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem ae_layer_herm (b : ℝ) :
    ∀ᵐ ω ∂layerLaw W b .oneBlockOnePort, (ω.1 0).IsHermitian := by
  have h := ae_isHermitian_pi W (Real.toNNReal ((1 - 2 * b) / W))
  unfold layerLaw
  exact (measurePreserving_fst).quasiMeasurePreserving.ae h

theorem H0_port (E : ℝ) (z : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (G : LayerMat W) (x : Fin W)
    (β : LayerSite W .oneBlockOnePort) :
    (layerMatrix .oneBlockOnePort E z (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0 * G)
      (port x) β = z * G (port x) β := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, layerMatrix, bondMatrix, Matrix.one_apply,
    LayerShape.incident]

theorem H0_phys (E : ℝ) (z : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (G : LayerMat W) (x : Fin W)
    (β : LayerSite W .oneBlockOnePort) :
    (layerMatrix .oneBlockOnePort E z (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0 * G)
      (phys x) β = -(E : ℂ) * G (phys x) β - ∑ k, X x k * G (phys k) β := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, layerMatrix, bondMatrix, Matrix.one_apply,
    BlockBand.Internal.Contracts.Layers.blockDiag, sub_mul, Finset.sum_sub_distrib]
  rw [Fintype.sum_prod_type]; simp

/-- The normalized physical trace `⟨𝒢₁₁⟩`. -/
abbrev physTr (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  (W : ℂ)⁻¹ * (passiveLetter E (boundaryZ b E) X ω 0).trace

theorem ae_layerLin_mul {b E : ℝ} (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosDef) :
    ∀ᵐ ω ∂layerLaw W b .oneBlockOnePort, layerLin ω * gRes b E X ω =
      1 - layerMatrix .oneBlockOnePort E (boundaryZ b E)
        (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0 * gRes b E X ω := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  filter_upwards [ae_layer_herm b] with ω hω
  exact layerLin_mul_gRes b E X ω (isUnit_layerMatrix_strict hη hX ω hω)

theorem integral_freshPortTrace {b E : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W)
    (X : Matrix (Fin W) (Fin W) ℂ)
    (hint : ∀ x, Integrable (fun ω => gRes b E X ω (port x) (port x)) (layerLaw W b .oneBlockOnePort)) :
    ∫ ω, freshPortTrace b E X ω ∂freshLaw W b =
      (W : ℂ)⁻¹ * ∑ x, ∫ ω, gRes b E X ω (port x) (port x) ∂layerLaw W b .oneBlockOnePort := by
  rw [← integral_finsetSum _ (fun x _ => hint x), ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_isUnit_layerF hb hW E X] with ω hF
  exact freshPortTrace_eq_layer b E X ω hF

/-- **The port mean equation, trace form**, uniformly on `bulkInterval κ`. -/
theorem meanEq_port_u (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
        ‖(∫ ω, freshPortTrace b E X ω ∂freshLaw W b) *
          (boundaryZ b E - (b : ℂ) * ∫ ω, physTr b E X ω ∂freshLaw W b) - 1‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C2, W2, m2⟩ := layer_moments_u hA hb0 hb hκ (2 * (1 : ℕ)) (by norm_num)
  obtain ⟨C4, W4, m4⟩ := layer_moments_u hA hb0 hb hκ (2 * (2 : ℕ)) (by norm_num)
  obtain ⟨C, W₁, hcov⟩ := wordCov_u hA hb0 hb hκ 1 le_rfl
  refine ⟨b * max C 0, max (max W₁ W2) (max W4 1), by positivity, fun W hW E hE X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hW2⟩, hW4, hW0⟩ := hW
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hx0 : (0 : ℝ) < W := by exact_mod_cast hW0
  set μ := layerLaw W b .oneBlockOnePort
  set v := ∫ ω, physTr b E X ω ∂freshLaw W b
  set g : Fin W → ℂ := fun x => ∫ ω, gRes b E X ω (port x) (port x) ∂μ
  have hc := hcov W hW1 E hE X hX.posSemidef 0 3 1 (by simpa using norm_one_matrix_le)
  have hint : ∀ x, Integrable (fun ω => gRes b E X ω (port x) (port x)) μ := fun x => by
    have h' := hc.2.1 x x; simp only [one_mul] at h'; exact h'
  have hentry : ∀ x, ‖1 - boundaryZ b E * g x + (b : ℂ) * v * g x‖ ≤
      b * max C 0 / (W : ℝ) ^ 2 := by
    intro x
    have hSD := meanSD_port_of hη hX (m2 W hW2 E hE X hX.posSemidef)
      (m4 W hW4 E hE X hX.posSemidef) x (port x)
    have hl : ∫ ω, (layerLin ω * gRes b E X ω) (port x) (port x) ∂μ = 1 - boundaryZ b E * g x := by
      rw [integral_congr_ae ((ae_layerLin_mul hb h1 h2 hX).mono fun ω h => by
        rw [h, Matrix.sub_apply, H0_port, Matrix.one_apply_eq])]
      rw [integral_sub (integrable_const _) ((hint x).const_mul _), integral_const_mul]
      have h1' : ∫ _ω, (1 : ℂ) ∂μ = 1 := by simp
      rw [h1']
    have hr : ∫ ω, (∑ y, gRes b E X ω (phys y) (phys y)) * gRes b E X ω (port x) (port x) ∂μ =
        (W : ℂ) * ∫ ω, physTr b E X ω * gRes b E X ω (port x) (port x) ∂μ := by
      rw [← integral_const_mul]; congr 1; funext ω
      have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
      simp only [physTr, trace_letter0]; field_simp
    obtain ⟨-, -, -, hn⟩ := hc
    have hn' : ‖(∫ ω, physTr b E X ω * gRes b E X ω (port x) (port x) ∂μ) - v * g x‖ ≤
        C / (W : ℝ) ^ 2 := by
      refine le_trans (le_of_eq ?_) ((norm_entry_le' _ x x).trans hn)
      simp [matrixExpect, Matrix.sub_apply, Matrix.smul_apply, v, g, physTr, μ]
      rfl
    rw [hl, hr, ginVar_cast hb0] at hSD
    have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have e : 1 - boundaryZ b E * g x + (b : ℂ) * v * g x =
        -(b : ℂ) * ((∫ ω, physTr b E X ω * gRes b E X ω (port x) (port x) ∂μ) - v * g x) := by
      rw [hSD]; field_simp; ring
    rw [e, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    calc b * _ ≤ b * (max C 0 / (W : ℝ) ^ 2) := by
          gcongr; exact hn'.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
      _ = _ := by ring
  rw [integral_freshPortTrace hb hW0 X hint]
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have e : ((W : ℂ)⁻¹ * ∑ x, g x) * (boundaryZ b E - (b : ℂ) * v) - 1 =
      -((W : ℂ)⁻¹ * ∑ x, (1 - boundaryZ b E * g x + (b : ℂ) * v * g x)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
    field_simp; ring
  show ‖((W : ℂ)⁻¹ * ∑ x, g x) * (boundaryZ b E - (b : ℂ) * v) - 1‖ ≤ _
  rw [e, norm_neg, norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖∑ x, (1 - boundaryZ b E * g x + (b : ℂ) * v * g x)‖
      ≤ (W : ℝ)⁻¹ * ∑ _x : Fin W, b * max C 0 / (W : ℝ) ^ 2 := by
        gcongr; exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => hentry x)
    _ = b * max C 0 / (W : ℝ) ^ 2 := by simp; field_simp

end BlockBand.Transmission.PathScalar
