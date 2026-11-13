module

public import BlockBand.Transmission.PassiveCovariance.MeanFieldOp

/-!
# Bulk-uniform mean Schwinger–Dyson equations and trace covariance

Moments of the layer resolvent, the mean Schwinger–Dyson equations on the physical and port rows,
and the layer trace–matrix covariance in operator norm, uniformly in `E ∈ bulkInterval κ`: the
constants and `W₀` depend only on `b` and the bulk margin `κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LengthUniform

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- Bulk-uniform `layer_moments`: moments of the layer resolvent (`w = z_∂`), with `C, W₀`
depending on `b, κ, p` only, for all `E ∈ bulkInterval κ`. -/
theorem layer_moments_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (p : ℝ) (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
      eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal p) (layerLaw W b .oneBlockOnePort) ≤
        ENNReal.ofReal C := by
  obtain ⟨C, W₀, h⟩ := hA.moments b hb0 hb κ hκ p hp
  refine ⟨C, W₀, fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  exact (h W hW E hE _ (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX).2.1

/-- Bulk-uniform `meanSD_phys`: the mean Schwinger–Dyson equation on the physical rows. -/
theorem meanSD_phys_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
      ∀ (x : Fin W) (β : LayerSite W .oneBlockOnePort),
        ∫ ω, (layerLin ω * gRes b E X ω) (phys x) β ∂layerLaw W b .oneBlockOnePort =
          -((gueVar W b : ℂ) * ∫ ω, (∑ y, gRes b E X ω (phys y) (phys y)) * gRes b E X ω (phys x) β
            ∂layerLaw W b .oneBlockOnePort) -
          (ginVar W b : ℂ) * ∫ ω, (∑ y, gRes b E X ω (port y) (port y)) * gRes b E X ω (phys x) β
            ∂layerLaw W b .oneBlockOnePort := by
  obtain ⟨C2, W2, m2⟩ := layer_moments_bulk hA hb0 hb hκ (2 * (1 : ℕ)) (by norm_num)
  obtain ⟨C4, W4, m4⟩ := layer_moments_bulk hA hb0 hb hκ (2 * (2 : ℕ)) (by norm_num)
  refine ⟨max W2 W4, fun W hW E hE X hX x β => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hη := etaZ_pos b E (by linarith) h1 h2
  set μ := layerLaw W b .oneBlockOnePort
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hgm : Measurable fun ω => ‖gRes b E X ω‖ := continuous_norm.measurable.comp hGm
  have hfin : ∀ (c C : ℝ) (k : ℕ), ENNReal.ofReal c * ENNReal.ofReal C ^ k ≠ ∞ := fun c C k =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hL2 : ∀ γ, MemLp (fun ω => gRes b E X ω γ β * 1) 2 μ := fun γ =>
    lt_of_le_of_lt (eLpNorm_two_le_of_pow_bound (hGm.eval_matrix.mul_const _).aestronglyMeasurable
      (fun ω => norm_nonneg _) hgm.aestronglyMeasurable zero_le_one 1 le_rfl
      (fun ω => by simpa using norm_entry_le' (gRes b E X ω) γ β)
      (m2 W (le_trans (le_max_left _ _) hW) E hE X hX.posSemidef)) (hfin _ _ _).lt_top
  have hI2 : ∀ γ N, Integrable (fun ω => (1 : ℂ) * (gRes b E X ω * N * gRes b E X ω) γ β) μ :=
    fun γ N => MemLp.integrable one_le_two (lt_of_le_of_lt (eLpNorm_two_le_of_pow_bound
      ((((hGm.mul_const N).mul hGm).eval_matrix).const_mul _).aestronglyMeasurable
      (fun ω => norm_nonneg _) hgm.aestronglyMeasurable (norm_nonneg N) 2 (by norm_num)
      (fun ω => by
        rw [one_mul]
        exact (norm_entry_le' _ γ β).trans (norm_mul_mul_le _ _))
      (m4 W (le_trans (le_max_right _ _) hW) E hE X hX.posSemidef)) (hfin _ _ _).lt_top)
  have hR := replica_identity_phys b E X (Ψ := fun _ => 1) (DΨ := fun _ => 0) hη hX
    (hasLayerDeriv_const 1) measurable_const x β hL2 (fun _ _ => by simp) hI2
  simp only [mul_one, LinearMap.zero_apply, mul_zero, zero_sub, one_mul] at hR
  have hint : ∀ γ δ, Integrable (fun ω => gRes b E X ω γ δ * gRes b E X ω (phys x) β) μ := by
    intro γ δ
    have := hI2 γ (Matrix.single δ (phys x) 1)
    simpa only [one_mul, mul_single_mul_apply] using this
  rw [hR]
  simp only [integral_neg, mul_neg, Finset.sum_neg_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← integral_finsetSum _ (fun y _ => hint _ _),
    ← integral_finsetSum _ (fun y _ => hint _ _)]
  simp only [Finset.sum_mul]
  ring

/-- Bulk-uniform `meanSD_port`: the mean Schwinger–Dyson equation on the port rows. -/
theorem meanSD_port_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
      ∀ (x : Fin W) (β : LayerSite W .oneBlockOnePort),
        ∫ ω, (layerLin ω * gRes b E X ω) (port x) β ∂layerLaw W b .oneBlockOnePort =
          -((ginVar W b : ℂ) * ∫ ω, (∑ y, gRes b E X ω (phys y) (phys y)) * gRes b E X ω (port x) β
            ∂layerLaw W b .oneBlockOnePort) := by
  obtain ⟨C2, W2, m2⟩ := layer_moments_bulk hA hb0 hb hκ (2 * (1 : ℕ)) (by norm_num)
  obtain ⟨C4, W4, m4⟩ := layer_moments_bulk hA hb0 hb hκ (2 * (2 : ℕ)) (by norm_num)
  refine ⟨max W2 W4, fun W hW E hE X hX x β => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hη := etaZ_pos b E (by linarith) h1 h2
  set μ := layerLaw W b .oneBlockOnePort
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hgm : Measurable fun ω => ‖gRes b E X ω‖ := continuous_norm.measurable.comp hGm
  have hfin : ∀ (c C : ℝ) (k : ℕ), ENNReal.ofReal c * ENNReal.ofReal C ^ k ≠ ∞ := fun c C k =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hL2 : ∀ γ, MemLp (fun ω => gRes b E X ω γ β * 1) 2 μ := fun γ =>
    lt_of_le_of_lt (eLpNorm_two_le_of_pow_bound (hGm.eval_matrix.mul_const _).aestronglyMeasurable
      (fun ω => norm_nonneg _) hgm.aestronglyMeasurable zero_le_one 1 le_rfl
      (fun ω => by simpa using norm_entry_le' (gRes b E X ω) γ β)
      (m2 W (le_trans (le_max_left _ _) hW) E hE X hX.posSemidef)) (hfin _ _ _).lt_top
  have hI2 : ∀ γ N, Integrable (fun ω => (1 : ℂ) * (gRes b E X ω * N * gRes b E X ω) γ β) μ :=
    fun γ N => MemLp.integrable one_le_two (lt_of_le_of_lt (eLpNorm_two_le_of_pow_bound
      ((((hGm.mul_const N).mul hGm).eval_matrix).const_mul _).aestronglyMeasurable
      (fun ω => norm_nonneg _) hgm.aestronglyMeasurable (norm_nonneg N) 2 (by norm_num)
      (fun ω => by
        rw [one_mul]
        exact (norm_entry_le' _ γ β).trans (norm_mul_mul_le _ _))
      (m4 W (le_trans (le_max_right _ _) hW) E hE X hX.posSemidef)) (hfin _ _ _).lt_top)
  have hR := replica_identity_port b E X (Ψ := fun _ => 1) (DΨ := fun _ => 0) hη hX
    (hasLayerDeriv_const 1) measurable_const x β hL2 (fun _ _ => by simp) hI2
  simp only [mul_one, LinearMap.zero_apply, mul_zero, zero_sub, one_mul] at hR
  have hint : ∀ γ δ, Integrable (fun ω => gRes b E X ω γ δ * gRes b E X ω (port x) β) μ := by
    intro γ δ
    have := hI2 γ (Matrix.single δ (port x) 1)
    simpa only [one_mul, mul_single_mul_apply] using this
  rw [hR]
  simp only [integral_neg, mul_neg, Finset.sum_neg_distrib]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun y _ => hint _ _)]
  simp only [Finset.sum_mul]

/-- Bulk-uniform `traceCov_op`: the layer trace–matrix covariance in operator norm. -/
theorem traceCov_op_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ k : Fin 6,
        Integrable (trLetter b E X k) (layerLaw W b .oneBlockOnePort) ∧
        (∀ α β, Integrable (fun ω => gRes b E X ω α β) (layerLaw W b .oneBlockOnePort)) ∧
        (∀ α β, Integrable (fun ω => trLetter b E X k ω * gRes b E X ω α β)
          (layerLaw W b .oneBlockOnePort)) ∧
        ‖covMat (layerLaw W b .oneBlockOnePort) (trLetter b E X k) (gRes b E X)‖ ≤
          4 * C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₀, h⟩ := hA.traceMatrix b hb0 hb κ hκ 1 1
  refine ⟨max C 0, W₀, le_max_right _ _, fun W hW E hE X hX k => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hD : ∀ j : Fin 2, ‖(fun _ : Fin 2 => (1 : Matrix (Fin W) (Fin W) ℂ)) j‖ ≤ 1 :=
    fun _ => norm_one_matrix_le
  have hm := fun m : Fin 6 => h W hW E hE _
    (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX 1 1 le_rfl le_rfl
    (fun _ => (k, false)) (fun _ => 1) (fun _ => (m, false)) (fun _ => 1) hD hD
  simp only [passiveWord_single_fun] at hm
  have hent : ∀ (α β : LayerSite W .oneBlockOnePort), ∃ (m : Fin 6) (x y : Fin W),
      ∀ ω, gRes b E X ω α β = passiveLetter E (boundaryZ b E) X ω m x y := by
    have h0 : ∀ a : Fin 1, a = 0 := fun a => Subsingleton.elim _ _
    rintro (⟨i0, x⟩ | ⟨i0, x⟩) (⟨j0, y⟩ | ⟨j0, y⟩) <;> rw [h0 i0, h0 j0]
    exacts [⟨0, x, y, fun _ => rfl⟩, ⟨1, x, y, fun _ => rfl⟩, ⟨2, x, y, fun _ => rfl⟩,
      ⟨3, x, y, fun _ => rfl⟩]
  refine ⟨(hm 0).1, fun α β => ?_, fun α β => ?_, ?_⟩
  · obtain ⟨m, x, y, e⟩ := hent α β
    simp only [e]; exact (hm m).2.1 x y
  · obtain ⟨m, x, y, e⟩ := hent α β
    simp only [e]; exact (hm m).2.2.1 x y
  · have hb4 : ∀ m : Fin 4, ‖(![blk11, blk12, blk21, blk22] m)
        (covMat (layerLaw W b .oneBlockOnePort) (trLetter b E X k) (gRes b E X))‖ ≤
          max C 0 / (W : ℝ) ^ 2 := fun m => by
      rw [blk_covMat]
      exact ((hm _).2.2.2).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
    have := norm_layerMat_le (covMat (layerLaw W b .oneBlockOnePort) (trLetter b E X k) (gRes b E X))
    have e1 : _ := hb4 0; have e2 : _ := hb4 1; have e3 : _ := hb4 2; have e4 : _ := hb4 3
    change ‖blk11 _‖ ≤ _ at e1
    change ‖blk12 _‖ ≤ _ at e2
    change ‖blk21 _‖ ≤ _ at e3
    change ‖blk22 _‖ ≤ _ at e4
    calc _ ≤ _ := this
      _ ≤ max C 0 / (W : ℝ) ^ 2 + max C 0 / (W : ℝ) ^ 2 + max C 0 / (W : ℝ) ^ 2 +
          max C 0 / (W : ℝ) ^ 2 := by gcongr
      _ = _ := by ring

end BlockBand.Transmission.LengthUniform
