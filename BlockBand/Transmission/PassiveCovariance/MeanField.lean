module

public import BlockBand.Transmission.PassiveCovariance.SchwingerDyson
public import BlockBand.Transmission.PassiveCovariance.VitaliL2
public import BlockBand.Transmission.PassiveLayer.Consistency

/-!
# The mean Schwinger–Dyson equation and its `W⁻²` error

Hypothesis `PassiveBoundsStatement`, through its `moments` and `traceMatrix` clauses at
`w = z_∂`. Law `layerLaw W b .oneBlockOnePort`.

* `layer_moments`: `‖𝒢‖ ∈ L^p` uniformly over passive inputs.
* `meanSD_phys`: the replica identity with `Ψ = 1`, with all integrability discharged:
  `E[(V𝒢)_{xβ}] = -(c/W)E[(Tr𝒢₁₁)𝒢_{xβ}] - (b/W)E[(Tr𝒢₂₂)𝒢_{xβ}]`.
* `letter_traceCov`: single-letter trace–matrix covariances `≤ C/W²` (the `traceMatrix` clause
  of `PassiveBoundsStatement` with words of length one).
* `meanField_phys`: for strictly passive `X`,
  `|E[(V𝒢)_{x,·}] + (1-2b)E⟨𝒢₁₁⟩E𝒢_{x,·} + bE⟨𝒢₂₂⟩E𝒢_{x,·}| ≤ C/W²` on the physical rows
  (`𝒢₁₁` and `𝒢₁₂` columns). Since `V𝒢 = I - H₀𝒢`, this is the mean-field equation
  `E𝒢 = (H₀ + S(E𝒢))⁻¹ + O(W⁻²)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem norm_entry_le' {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (i j : ι) :
    ‖M i j‖ ≤ ‖M‖ := by
  have h := norm_bilinear_le (Pi.single i 1) M (Pi.single j 1)
  have hv : ∀ k : ι, vecNorm (Pi.single k (1 : ℂ)) = 1 := fun k => by
    rw [vecNorm, Finset.sum_eq_single k (fun l _ hl => by simp [hl]) (by simp)]
    simp
  have hb : bilinear (Pi.single i 1) M (Pi.single j 1) = M i j := by
    simp [bilinear, mulVec, dotProduct, Pi.single_apply]
  rwa [hb, hv, hv, mul_one, one_mul] at h

/-- Moments of the layer resolvent from `PassiveBoundsStatement` (`w = z_∂`). -/
theorem layer_moments (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (p : ℝ) (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
      eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal p) (layerLaw W b .oneBlockOnePort) ≤
        ENNReal.ofReal C := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨C, W₀, h⟩ := hA.moments b hb0 hb _ hκ p hp
  exact ⟨C, W₀, fun W hW X hX => (h W hW E (mem_bulkInterval_min E) _
    (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX).2.1⟩

theorem norm_mul_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι] (G N : Matrix ι ι ℂ) :
    ‖G * N * G‖ ≤ ‖N‖ * ‖G‖ ^ 2 := by
  calc ‖G * N * G‖ ≤ ‖G * N‖ * ‖G‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖G‖ * ‖N‖ * ‖G‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
    _ = ‖N‖ * ‖G‖ ^ 2 := by ring

/-- **The mean Schwinger–Dyson equation, physical rows** (`Ψ = 1` in `replica_identity_phys`),
with all integrability supplied by the `moments` clause of `PassiveBoundsStatement`:
`E[(V𝒢)_{xβ}] = -(c/W) E[(Tr𝒢₁₁)𝒢_{xβ}] - (b/W) E[(Tr𝒢₂₂)𝒢_{xβ}]`. -/
theorem meanSD_phys (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
      ∀ (x : Fin W) (β : LayerSite W .oneBlockOnePort),
        ∫ ω, (layerLin ω * gRes b E X ω) (phys x) β ∂layerLaw W b .oneBlockOnePort =
          -((gueVar W b : ℂ) * ∫ ω, (∑ y, gRes b E X ω (phys y) (phys y)) * gRes b E X ω (phys x) β
            ∂layerLaw W b .oneBlockOnePort) -
          (ginVar W b : ℂ) * ∫ ω, (∑ y, gRes b E X ω (port y) (port y)) * gRes b E X ω (phys x) β
            ∂layerLaw W b .oneBlockOnePort := by
  obtain ⟨C2, W2, m2⟩ := layer_moments hA hb0 hb h1 h2 (2 * (1 : ℕ)) (by norm_num)
  obtain ⟨C4, W4, m4⟩ := layer_moments hA hb0 hb h1 h2 (2 * (2 : ℕ)) (by norm_num)
  refine ⟨max W2 W4, fun W hW X hX x β => ?_⟩
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
      (m2 W (le_trans (le_max_left _ _) hW) X hX.posSemidef)) (hfin _ _ _).lt_top
  have hI2 : ∀ γ N, Integrable (fun ω => (1 : ℂ) * (gRes b E X ω * N * gRes b E X ω) γ β) μ :=
    fun γ N => MemLp.integrable one_le_two (lt_of_le_of_lt (eLpNorm_two_le_of_pow_bound
      ((((hGm.mul_const N).mul hGm).eval_matrix).const_mul _).aestronglyMeasurable
      (fun ω => norm_nonneg _) hgm.aestronglyMeasurable (norm_nonneg N) 2 (by norm_num)
      (fun ω => by
        rw [one_mul]
        exact (norm_entry_le' _ γ β).trans (norm_mul_mul_le _ _))
      (m4 W (le_trans (le_max_right _ _) hW) X hX.posSemidef)) (hfin _ _ _).lt_top)
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

theorem passiveWord_single (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (k : Fin 6)
    (ω : LayerSample W .oneBlockOnePort) :
    passiveWord E w X (fun _ : Fin 1 => (k, false)) (fun _ => 1) ω = passiveLetter E w X ω k := by
  simp [passiveWord, List.ofFn_succ]

theorem passiveWord_single_fun (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (k : Fin 6) :
    passiveWord E w X (fun _ : Fin 1 => (k, false)) (fun _ => 1) =
      fun ω => passiveLetter E w X ω k := funext fun ω => passiveWord_single E w X k ω

/-- **Single-letter trace–matrix covariance** from the `traceMatrix` clause (`w = z_∂`):
`|E[⟨ℓ_k⟩ (ℓ_m)_{xy}] - E⟨ℓ_k⟩ E(ℓ_m)_{xy}| ≤ C/W²` for letters `ℓ ∈ {𝒢₁₁,𝒢₁₂,𝒢₂₁,𝒢₂₂,K𝒢₁₁,L}`. -/
theorem letter_traceCov (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ (k m : Fin 6) (x y : Fin W),
        let μ := layerLaw W b .oneBlockOnePort
        let f := fun ω => (W : ℂ)⁻¹ * (passiveLetter E (boundaryZ b E) X ω k).trace
        Integrable f μ ∧ Integrable (fun ω => passiveLetter E (boundaryZ b E) X ω m x y) μ ∧
          Integrable (fun ω => f ω * passiveLetter E (boundaryZ b E) X ω m x y) μ ∧
          ‖(∫ ω, f ω * passiveLetter E (boundaryZ b E) X ω m x y ∂μ) -
            (∫ ω, f ω ∂μ) * ∫ ω, passiveLetter E (boundaryZ b E) X ω m x y ∂μ‖ ≤ C / (W : ℝ) ^ 2 := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨C, W₀, h⟩ := hA.traceMatrix b hb0 hb _ hκ 1 1
  refine ⟨C, W₀, fun W hW X hX k m x y => ?_⟩
  have hD : ∀ j : Fin 2, ‖(fun _ : Fin 2 => (1 : Matrix (Fin W) (Fin W) ℂ)) j‖ ≤ 1 :=
    fun _ => norm_one_matrix_le
  obtain ⟨i1, i2, i3, i4⟩ := h W hW E (mem_bulkInterval_min E) _
    (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX 1 1 le_rfl le_rfl
    (fun _ => (k, false)) (fun _ => 1) (fun _ => (m, false)) (fun _ => 1) hD hD
  simp only [passiveWord_single_fun] at i1 i2 i3 i4
  refine ⟨i1, i2 x y, i3 x y, (le_trans (le_of_eq ?_) (norm_entry_le' _ x y)).trans i4⟩
  simp [matrixExpect, Matrix.sub_apply, Matrix.smul_apply]

theorem trace_letter0 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    (passiveLetter E (boundaryZ b E) X ω 0).trace = ∑ y, gRes b E X ω (phys y) (phys y) := rfl

theorem trace_letter3 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    (passiveLetter E (boundaryZ b E) X ω 3).trace = ∑ y, gRes b E X ω (port y) (port y) := rfl

theorem gueVar_cast {b : ℝ} (hb : b < 1 / 2) : (gueVar W b : ℂ) = ((1 - 2 * b : ℝ) : ℂ) / W := by
  rw [gueVar, Real.coe_toNNReal _ (div_nonneg (by linarith) (Nat.cast_nonneg W))]; push_cast; ring

theorem ginVar_cast {b : ℝ} (hb0 : 0 < b) : (ginVar W b : ℂ) = (b : ℂ) / W := by
  rw [ginVar, Real.coe_toNNReal _ (div_nonneg hb0.le (Nat.cast_nonneg W))]; push_cast; ring

/-- **The mean Schwinger–Dyson equation with its `W⁻²` error** (towards the passive mean):
for strictly passive `X` and the physical-row entries
`m ∈ {0, 1}` (`𝒢₁₁`, `𝒢₁₂`),
`|E[(V𝒢)_{x,·}] + (1-2b)E⟨𝒢₁₁⟩E𝒢_{x,·} + bE⟨𝒢₂₂⟩E𝒢_{x,·}| ≤ C/W²`. The error is the
single-letter trace–matrix covariance of the `traceMatrix` clause. -/
theorem meanField_phys (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
      ∀ (m : Fin 6) (x y : Fin W), (m = 0 ∨ m = 1) →
        let μ := layerLaw W b .oneBlockOnePort
        let G := fun ω => passiveLetter E (boundaryZ b E) X ω m x y
        let β : LayerSite W .oneBlockOnePort := if m = 0 then phys y else port y
        ‖(∫ ω, (layerLin ω * gRes b E X ω) (phys x) β ∂μ) +
            ((1 - 2 * b : ℝ) : ℂ) * (∫ ω, (W : ℂ)⁻¹ * (passiveLetter E (boundaryZ b E) X ω 0).trace ∂μ) *
              (∫ ω, G ω ∂μ) +
            (b : ℂ) * (∫ ω, (W : ℂ)⁻¹ * (passiveLetter E (boundaryZ b E) X ω 3).trace ∂μ) *
              (∫ ω, G ω ∂μ)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨W₁, hSD⟩ := meanSD_phys hA hb0 hb h1 h2
  obtain ⟨C, W₂, hcov⟩ := letter_traceCov hA hb0 hb h1 h2
  refine ⟨C, max (max W₁ W₂) 1, fun W hW X hX m x y hm => ?_⟩
  intro μ G β
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWpos : (W : ℂ) ≠ 0 := by
    have : 1 ≤ W := le_trans (le_max_right _ _) hW
    exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
  have hGβ : ∀ ω, gRes b E X ω (phys x) β = G ω := fun ω => by
    rcases hm with rfl | rfl <;> rfl
  obtain ⟨-, -, -, c0⟩ := hcov W hW2 X hX.posSemidef 0 m x y
  obtain ⟨-, -, -, c3⟩ := hcov W hW2 X hX.posSemidef 3 m x y
  rw [hSD W hW1 X hX x β]
  simp only [hGβ]
  have e0 : ∀ ω, (∑ y, gRes b E X ω (phys y) (phys y)) * G ω =
      (W : ℂ) * ((W : ℂ)⁻¹ * (passiveLetter E (boundaryZ b E) X ω 0).trace * G ω) := fun ω => by
    rw [trace_letter0]; field_simp
  have e3 : ∀ ω, (∑ y, gRes b E X ω (port y) (port y)) * G ω =
      (W : ℂ) * ((W : ℂ)⁻¹ * (passiveLetter E (boundaryZ b E) X ω 3).trace * G ω) := fun ω => by
    rw [trace_letter3]; field_simp
  simp only [e0, e3, integral_const_mul, gueVar_cast hb, ginVar_cast hb0]
  simp only [integral_const_mul] at c0 c3
  set A0 := ∫ ω, (W : ℂ)⁻¹ * (passiveLetter E (boundaryZ b E) X ω 0).trace * G ω ∂μ
  set A3 := ∫ ω, (W : ℂ)⁻¹ * (passiveLetter E (boundaryZ b E) X ω 3).trace * G ω ∂μ
  set F0 := (W : ℂ)⁻¹ * ∫ ω, (passiveLetter E (boundaryZ b E) X ω 0).trace ∂μ
  set F3 := (W : ℂ)⁻¹ * ∫ ω, (passiveLetter E (boundaryZ b E) X ω 3).trace ∂μ
  set g := ∫ ω, G ω ∂μ
  have key : -((((1 - 2 * b : ℝ) : ℂ) / W) * ((W : ℂ) * A0)) - (b : ℂ) / W * ((W : ℂ) * A3) +
      ((1 - 2 * b : ℝ) : ℂ) * F0 * g + (b : ℂ) * F3 * g =
      -(((1 - 2 * b : ℝ) : ℂ) * (A0 - F0 * g)) - (b : ℂ) * (A3 - F3 * g) := by
    field_simp; ring
  rw [key]
  have hc1 : 0 ≤ 1 - 2 * b := by linarith
  calc ‖-(((1 - 2 * b : ℝ) : ℂ) * (A0 - F0 * g)) - (b : ℂ) * (A3 - F3 * g)‖
      ≤ (1 - 2 * b) * (C / (W : ℝ) ^ 2) + b * (C / (W : ℝ) ^ 2) := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc1]
          exact mul_le_mul_of_nonneg_left c0 hc1
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
          exact mul_le_mul_of_nonneg_left c3 hb0.le
    _ ≤ C / (W : ℝ) ^ 2 := by
        have hC : 0 ≤ C / (W : ℝ) ^ 2 := le_trans (norm_nonneg _) c0
        nlinarith

end BlockBand.Transmission.PassiveCovariance
