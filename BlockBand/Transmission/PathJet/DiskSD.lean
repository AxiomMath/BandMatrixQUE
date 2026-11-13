module

public import BlockBand.Transmission.PathJet.DiskHolo

/-!
# The mean Schwinger–Dyson identities at a port parameter `w`

For strictly passive `X` (`Y ≻ 0`) and `Im w > 0`, with `V = layerLin ω` and `𝒢 = 𝒢(w)`:
* `meanSD_phys_w`: `E(V𝒢)_{xβ} = -(c/W)E[(Σ_y𝒢_{yy})𝒢_{xβ}] - (b/W)E[(Σ_y𝒢_{ȳȳ})𝒢_{xβ}]`;
* `meanSD_port_w`: `E(V𝒢)_{x̄β} = -(b/W)E[(Σ_y𝒢_{yy})𝒢_{x̄β}]`;
* `ae_layerLin_mul_w`: `V𝒢 = 1 - M₀𝒢` a.s.
The integrability inputs are `L²`, `L⁴` bounds on `‖𝒢(w)‖` (the `moments` clause of
`PassiveBoundsStatement` on the disk).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

section SD
variable {b E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ} {C2 C4 : ℝ}

theorem sd_integrability_w
    (hm2 : eLpNorm (fun ω => ‖gW E w X ω‖) (ENNReal.ofReal (2 * (1 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C2)
    (hm4 : eLpNorm (fun ω => ‖gW E w X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4) (β : LayerSite W .oneBlockOnePort) :
    (∀ γ, MemLp (fun ω => gW E w X ω γ β) 2 (layerLaw W b .oneBlockOnePort)) ∧
      ∀ γ N, Integrable (fun ω => (gW E w X ω * N * gW E w X ω) γ β)
        (layerLaw W b .oneBlockOnePort) := by
  have hGm := measurable_layerRes (W := W) E w X
  have hgm : Measurable fun ω => ‖gW E w X ω‖ := continuous_norm.measurable.comp hGm
  have hfin : ∀ (c C : ℝ) (k : ℕ), ENNReal.ofReal c * ENNReal.ofReal C ^ k ≠ ∞ := fun c C k =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  refine ⟨fun γ => lt_of_le_of_lt (eLpNorm_two_le_of_pow_bound
      hGm.eval_matrix.aestronglyMeasurable
      (fun ω => norm_nonneg _) hgm.aestronglyMeasurable zero_le_one 1 le_rfl
      (fun ω => by simpa using norm_entry_le' (gW E w X ω) γ β) hm2) (hfin _ _ _).lt_top,
    fun γ N => MemLp.integrable one_le_two (lt_of_le_of_lt (eLpNorm_two_le_of_pow_bound
      (((hGm.mul_const N).mul hGm).eval_matrix).aestronglyMeasurable
      (fun ω => norm_nonneg _) hgm.aestronglyMeasurable (norm_nonneg N) 2 (by norm_num)
      (fun ω => (norm_entry_le' _ γ β).trans (norm_mul_mul_le _ _)) hm4) (hfin _ _ _).lt_top)⟩

theorem stein_entry_w (hw : 0 < w.im) (hY : (passiveY X).PosDef)
    (hm2 : eLpNorm (fun ω => ‖gW E w X ω‖) (ENNReal.ofReal (2 * (1 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C2)
    (hm4 : eLpNorm (fun ω => ‖gW E w X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4) (γ β : LayerSite W .oneBlockOnePort) :
    HasLayerDeriv (fun ω => gW E w X ω γ β) (fun ω => resDeriv (gW E w X ω) γ β) ∧
      Measurable (fun ω => gW E w X ω γ β) ∧
      MemLp (fun ω => gW E w X ω γ β) 2 (layerLaw W b .oneBlockOnePort) ∧
      ∀ N, Integrable (fun ω => resDeriv (gW E w X ω) γ β N) (layerLaw W b .oneBlockOnePort) := by
  obtain ⟨hL2, hI2⟩ := sd_integrability_w hm2 hm4 β
  refine ⟨hasLayerDeriv_resolvent_entry E w _ (fun ω hω => isUnit_layerMatrix_w E hw hY ω hω) γ β,
    (measurable_layerRes E w X).eval_matrix, hL2 γ, fun N => ?_⟩
  simpa [resDeriv] using (hI2 γ N).neg

/-- **The mean Schwinger–Dyson identity at `w`, physical rows** (`Ψ = 1`). -/
theorem meanSD_phys_w (hw : 0 < w.im) (hY : (passiveY X).PosDef)
    (hm2 : eLpNorm (fun ω => ‖gW E w X ω‖) (ENNReal.ofReal (2 * (1 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C2)
    (hm4 : eLpNorm (fun ω => ‖gW E w X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4) (x : Fin W)
    (β : LayerSite W .oneBlockOnePort) :
    ∫ ω, (layerLin ω * gW E w X ω) (phys x) β ∂layerLaw W b .oneBlockOnePort =
      -((gueVar W b : ℂ) * ∫ ω, (∑ y, gW E w X ω (phys y) (phys y)) * gW E w X ω (phys x) β
        ∂layerLaw W b .oneBlockOnePort) -
      (ginVar W b : ℂ) * ∫ ω, (∑ y, gW E w X ω (port y) (port y)) * gW E w X ω (phys x) β
        ∂layerLaw W b .oneBlockOnePort := by
  set μ := layerLaw W b .oneBlockOnePort
  obtain ⟨hL2, hI2⟩ := sd_integrability_w hm2 hm4 β
  have hA : ∀ y, Integrable (fun ω => ω.1 0 x y * gW E w X ω (phys y) β) μ :=
    fun y => (memLp_layer_A b x y).integrable_mul (hL2 _)
  have hB : ∀ y, Integrable (fun ω => ω.2 0 0 x y * gW E w X ω (port y) β) μ :=
    fun y => (memLp_layer_B b x y).integrable_mul (hL2 _)
  have hint : ∀ γ δ, Integrable (fun ω => gW E w X ω γ δ * gW E w X ω (phys x) β) μ := by
    intro γ δ
    have := hI2 γ (Matrix.single δ (phys x) 1)
    simpa only [mul_single_mul_apply] using this
  have e : (fun ω => (layerLin ω * gW E w X ω) (phys x) β) = fun ω =>
      ∑ y, ω.1 0 x y * gW E w X ω (phys y) β + ∑ y, ω.2 0 0 x y * gW E w X ω (port y) β := by
    funext ω; rw [layerLin_mul_phys]
  rw [e, integral_add (integrable_finsetSum _ fun y _ => hA y) (integrable_finsetSum _ fun y _ => hB y),
    integral_finsetSum _ (fun y _ => hA y), integral_finsetSum _ (fun y _ => hB y)]
  have hAy : ∀ y, ∫ ω, ω.1 0 x y * gW E w X ω (phys y) β ∂μ =
      -((gueVar W b : ℂ) * ∫ ω, gW E w X ω (phys y) (phys y) * gW E w X ω (phys x) β ∂μ) := by
    intro y
    obtain ⟨hd, hm, hl, hi⟩ := stein_entry_w hw hY hm2 hm4 (phys y) β
    rw [stein_layerA_lin b _ _ hd hm hl hi x y, layerA_single, ← mul_neg, ← integral_neg]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [resDeriv, mul_single_mul_apply]
  have hBy : ∀ y, ∫ ω, ω.2 0 0 x y * gW E w X ω (port y) β ∂μ =
      -((ginVar W b : ℂ) * ∫ ω, gW E w X ω (port y) (port y) * gW E w X ω (phys x) β ∂μ) := by
    intro y
    obtain ⟨hd, hm, hl, hi⟩ := stein_entry_w hw hY hm2 hm4 (port y) β
    rw [stein_layerB_lin b _ _ hd hm hl hi x y, lowerB_single, ← mul_neg, ← integral_neg]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [resDeriv, mul_single_mul_apply]
  simp only [hAy, hBy, Finset.sum_neg_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← integral_finsetSum _ (fun y _ => hint _ _),
    ← integral_finsetSum _ (fun y _ => hint _ _)]
  simp only [Finset.sum_mul]
  ring

/-- **The mean Schwinger–Dyson identity at `w`, port rows** (`Ψ = 1`). -/
theorem meanSD_port_w (hw : 0 < w.im) (hY : (passiveY X).PosDef)
    (hm2 : eLpNorm (fun ω => ‖gW E w X ω‖) (ENNReal.ofReal (2 * (1 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C2)
    (hm4 : eLpNorm (fun ω => ‖gW E w X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4) (x : Fin W)
    (β : LayerSite W .oneBlockOnePort) :
    ∫ ω, (layerLin ω * gW E w X ω) (port x) β ∂layerLaw W b .oneBlockOnePort =
      -((ginVar W b : ℂ) * ∫ ω, (∑ y, gW E w X ω (phys y) (phys y)) * gW E w X ω (port x) β
        ∂layerLaw W b .oneBlockOnePort) := by
  set μ := layerLaw W b .oneBlockOnePort
  obtain ⟨hL2, hI2⟩ := sd_integrability_w hm2 hm4 β
  have hB : ∀ y, Integrable (fun ω => star (ω.2 0 0 y x) * gW E w X ω (phys y) β) μ :=
    fun y => (memLp_layer_B b y x).star.integrable_mul (hL2 _)
  have hint : ∀ γ δ, Integrable (fun ω => gW E w X ω γ δ * gW E w X ω (port x) β) μ := by
    intro γ δ
    have := hI2 γ (Matrix.single δ (port x) 1)
    simpa only [mul_single_mul_apply] using this
  have e : (fun ω => (layerLin ω * gW E w X ω) (port x) β) = fun ω =>
      ∑ y, star (ω.2 0 0 y x) * gW E w X ω (phys y) β := by
    funext ω; rw [layerLin_mul_port]
  rw [e, integral_finsetSum _ (fun y _ => hB y)]
  have hBy : ∀ y, ∫ ω, star (ω.2 0 0 y x) * gW E w X ω (phys y) β ∂μ =
      -((ginVar W b : ℂ) * ∫ ω, gW E w X ω (phys y) (phys y) * gW E w X ω (port x) β ∂μ) := by
    intro y
    obtain ⟨hd, hm, hl, hi⟩ := stein_entry_w hw hY hm2 hm4 (phys y) β
    rw [stein_layerBconj_lin b _ _ hd hm hl hi y x, upperB_single, ← mul_neg, ← integral_neg]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [resDeriv, mul_single_mul_apply]
  simp only [hBy, Finset.sum_neg_distrib]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun y _ => hint _ _)]
  simp only [Finset.sum_mul]

end SD

/-- `M(w) = M₀ + V`, `V = layerLin ω`. -/
theorem layerMatrix_eq_add_w (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    layerMatrix .oneBlockOnePort E w (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω =
      layerMatrix .oneBlockOnePort E w (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0 +
        layerLin ω := by
  have h := layerMatrix_add_smul E w (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0 ω 1
  simpa using h

/-- `V𝒢 = 1 - M₀𝒢` almost surely (strictly passive `X`, `Im w > 0`). -/
theorem ae_layerLin_mul_w (b E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosDef) :
    ∀ᵐ ω ∂layerLaw W b .oneBlockOnePort, layerLin ω * gW E w X ω =
      1 - layerMatrix .oneBlockOnePort E w
        (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0 * gW E w X ω := by
  filter_upwards [PathScalar.ae_layer_herm b] with ω hω
  have hu := isUnit_layerMatrix_w E hw hY ω hω
  have hH : layerMatrix .oneBlockOnePort E w
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω * gW E w X ω = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  rw [layerMatrix_eq_add_w, Matrix.add_mul] at hH
  rw [← hH]; abel

end BlockBand.Transmission.PathJet
