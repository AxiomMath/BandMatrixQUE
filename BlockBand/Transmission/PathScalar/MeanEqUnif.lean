module

public import BlockBand.Transmission.PathScalar.HoldsMean
public import BlockBand.Transmission.PassiveCovariance.MeanFieldPort

/-!
# The mean Schwinger–Dyson identities, uniformly on `bulkInterval κ`

The layer moments, the mean Schwinger–Dyson identities on the physical and port rows, and the
one-letter trace covariances, at `w = z_∂` with constants uniform on `bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The layer moments of `PassiveBoundsStatement`, uniformly on `bulkInterval κ` (`w = z_∂`). -/
theorem layer_moments_u (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (p : ℝ) (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
      eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal p) (layerLaw W b .oneBlockOnePort) ≤
        ENNReal.ofReal C := by
  obtain ⟨C, W₀, h⟩ := hA.moments b hb0 hb κ hκ p hp
  exact ⟨C, W₀, fun W hW E hE X hX => (h W hW E hE _ (boundaryZ_mem_paramDisk (by linarith)
    (bulk_bounds hκ hE).1 (bulk_bounds hκ hE).2) X hX).2.1⟩

section SD
variable {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {C2 C4 : ℝ}

theorem sd_integrability (hm2 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (1 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C2)
    (hm4 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4) (β : LayerSite W .oneBlockOnePort) :
    (∀ γ, MemLp (fun ω => gRes b E X ω γ β * 1) 2 (layerLaw W b .oneBlockOnePort)) ∧
      ∀ γ N, Integrable (fun ω => (1 : ℂ) * (gRes b E X ω * N * gRes b E X ω) γ β)
        (layerLaw W b .oneBlockOnePort) := by
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hgm : Measurable fun ω => ‖gRes b E X ω‖ := continuous_norm.measurable.comp hGm
  have hfin : ∀ (c C : ℝ) (k : ℕ), ENNReal.ofReal c * ENNReal.ofReal C ^ k ≠ ∞ := fun c C k =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  refine ⟨fun γ => lt_of_le_of_lt (eLpNorm_two_le_of_pow_bound
      (hGm.eval_matrix.mul_const _).aestronglyMeasurable
      (fun ω => norm_nonneg _) hgm.aestronglyMeasurable zero_le_one 1 le_rfl
      (fun ω => by simpa using norm_entry_le' (gRes b E X ω) γ β) hm2) (hfin _ _ _).lt_top,
    fun γ N => MemLp.integrable one_le_two (lt_of_le_of_lt (eLpNorm_two_le_of_pow_bound
      ((((hGm.mul_const N).mul hGm).eval_matrix).const_mul _).aestronglyMeasurable
      (fun ω => norm_nonneg _) hgm.aestronglyMeasurable (norm_nonneg N) 2 (by norm_num)
      (fun ω => by
        rw [one_mul]
        exact (norm_entry_le' _ γ β).trans (norm_mul_mul_le _ _)) hm4) (hfin _ _ _).lt_top)⟩

/-- `meanSD_phys` from given moment bounds. -/
theorem meanSD_phys_of (hη : 0 < etaZ b E) (hX : (passiveY X).PosDef)
    (hm2 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (1 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C2)
    (hm4 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4) (x : Fin W)
    (β : LayerSite W .oneBlockOnePort) :
    ∫ ω, (layerLin ω * gRes b E X ω) (phys x) β ∂layerLaw W b .oneBlockOnePort =
      -((gueVar W b : ℂ) * ∫ ω, (∑ y, gRes b E X ω (phys y) (phys y)) * gRes b E X ω (phys x) β
        ∂layerLaw W b .oneBlockOnePort) -
      (ginVar W b : ℂ) * ∫ ω, (∑ y, gRes b E X ω (port y) (port y)) * gRes b E X ω (phys x) β
        ∂layerLaw W b .oneBlockOnePort := by
  obtain ⟨hL2, hI2⟩ := sd_integrability hm2 hm4 β
  have hR := replica_identity_phys b E X (Ψ := fun _ => 1) (DΨ := fun _ => 0) hη hX
    (hasLayerDeriv_const 1) measurable_const x β hL2 (fun _ _ => by simp) hI2
  simp only [mul_one, LinearMap.zero_apply, mul_zero, zero_sub, one_mul] at hR
  have hint : ∀ γ δ, Integrable (fun ω => gRes b E X ω γ δ * gRes b E X ω (phys x) β)
      (layerLaw W b .oneBlockOnePort) := by
    intro γ δ
    have := hI2 γ (Matrix.single δ (phys x) 1)
    simpa only [one_mul, mul_single_mul_apply] using this
  rw [hR]
  simp only [integral_neg, mul_neg, Finset.sum_neg_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← integral_finsetSum _ (fun y _ => hint _ _),
    ← integral_finsetSum _ (fun y _ => hint _ _)]
  simp only [Finset.sum_mul]
  ring

/-- `meanSD_port` from given moment bounds. -/
theorem meanSD_port_of (hη : 0 < etaZ b E) (hX : (passiveY X).PosDef)
    (hm2 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (1 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C2)
    (hm4 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4) (x : Fin W)
    (β : LayerSite W .oneBlockOnePort) :
    ∫ ω, (layerLin ω * gRes b E X ω) (port x) β ∂layerLaw W b .oneBlockOnePort =
      -((ginVar W b : ℂ) * ∫ ω, (∑ y, gRes b E X ω (phys y) (phys y)) * gRes b E X ω (port x) β
        ∂layerLaw W b .oneBlockOnePort) := by
  obtain ⟨hL2, hI2⟩ := sd_integrability hm2 hm4 β
  have hR := replica_identity_port b E X (Ψ := fun _ => 1) (DΨ := fun _ => 0) hη hX
    (hasLayerDeriv_const 1) measurable_const x β hL2 (fun _ _ => by simp) hI2
  simp only [mul_one, LinearMap.zero_apply, mul_zero, zero_sub, one_mul] at hR
  have hint : ∀ γ δ, Integrable (fun ω => gRes b E X ω γ δ * gRes b E X ω (port x) β)
      (layerLaw W b .oneBlockOnePort) := by
    intro γ δ
    have := hI2 γ (Matrix.single δ (port x) 1)
    simpa only [one_mul, mul_single_mul_apply] using this
  rw [hR]
  simp only [integral_neg, mul_neg, Finset.sum_neg_distrib]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun y _ => hint _ _)]
  simp only [Finset.sum_mul]

end SD

/-- One-letter traces against a word with one deterministic insertion `D·ℓ_m`, uniformly on
`bulkInterval κ` (the `traceMatrix` clause with words of length one, insertions `‖D‖ ≤ Kd`). -/
theorem wordCov_u (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Kd : ℝ) (hKd : 1 ≤ Kd) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ (k m : Fin 6) (D : Matrix (Fin W) (Fin W) ℂ), ‖D‖ ≤ Kd →
        let μ := layerLaw W b .oneBlockOnePort
        let f := fun ω => (W : ℂ)⁻¹ * (passiveLetter E (boundaryZ b E) X ω k).trace
        let U := fun ω => D * passiveLetter E (boundaryZ b E) X ω m
        Integrable f μ ∧ (∀ x y, Integrable (fun ω => U ω x y) μ) ∧
          (∀ x y, Integrable (fun ω => f ω * U ω x y) μ) ∧
          ‖matrixExpect μ (fun ω => f ω • U ω) - (∫ ω, f ω ∂μ) • matrixExpect μ U‖ ≤
            C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₀, h⟩ := hA.traceMatrix b hb0 hb κ hκ 1 Kd
  refine ⟨C, W₀, fun W hW E hE X hX k m D hD => ?_⟩
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hD1 : ∀ j : Fin 2, ‖(fun _ : Fin 2 => (1 : Matrix (Fin W) (Fin W) ℂ)) j‖ ≤ Kd :=
    fun _ => norm_one_matrix_le.trans hKd
  have hD2 : ∀ j : Fin 2, ‖(![D, 1] : Fin 2 → Matrix (Fin W) (Fin W) ℂ) j‖ ≤ Kd := by
    intro j; fin_cases j
    · simpa using hD
    · simpa using norm_one_matrix_le.trans hKd
  have := h W hW E hE _ (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX 1 1 le_rfl le_rfl
    (fun _ => (k, false)) (fun _ => 1) (fun _ => (m, false)) ![D, 1] hD1 hD2
  have hw : passiveWord E (boundaryZ b E) X (fun _ : Fin 1 => (m, false)) ![D, 1] =
      fun ω => D * passiveLetter E (boundaryZ b E) X ω m := by
    funext ω; simp [passiveWord, List.ofFn_succ]
  simp only [passiveWord_single_fun, hw] at this
  exact this

end BlockBand.Transmission.PathScalar
