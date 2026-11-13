module

public import BlockBand.SourceProcess.FullSource.Birth

/-!
# The first tag: the one-block two-port path is a fresh layer

The length-one path with its two matched leads is the fresh layer of shape `.oneBlockTwoPorts` at
`X = 0` (`fullPathMatrix_one_eq`), with the layer law (`growthPathLaw_map_sampleOne`). Hence
`t_1 = W⁻¹Tr 𝒰_1*𝒰_1 ≤ ‖G‖²` has all fixed moments by `GaussianAbsorptionContract`
(`birth_moment_zero`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar BlockBand.Transmission.PassiveLayer
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The fresh coordinates of the first block: `A₀`, near bond `B₁`, far bond `B₀`. -/
def sampleOne (ω : GrowthPath W) : LayerSample W .oneBlockTwoPorts :=
  (fun _ => ω.1 0, fun _ j => ω.2 (![1, 0] j))

theorem measurable_sampleOne : Measurable (sampleOne (W := W)) :=
  (Measurable.of_eval fun _ => (measurable_pi_apply _).comp measurable_fst).prodMk
    (Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
      (measurable_pi_apply _).comp measurable_snd)

theorem fullPathMatrix_one_eq (b E : ℝ) (ω : GrowthPath W) :
    fullPathMatrix b E W 1 ω = layerMatrix .oneBlockTwoPorts E (boundaryZ b E) 0 (sampleOne ω) := by
  ext (x | ⟨i, x⟩) (y | ⟨l, y⟩)
  · have hxy : x.1 = y.1 := Subsingleton.elim _ _
    simp [fullPathMatrix, layerMatrix, pathMatrix, pathAt,
      BlockBand.Internal.Contracts.Layers.blockDiag, sampleOne, hxy]
  · fin_cases l <;> simp [fullPathMatrix, layerMatrix, pathPortCoupling, bondMatrix,
      LayerShape.incident, pathAt, sampleOne]
  · fin_cases i <;> simp [fullPathMatrix, layerMatrix, pathPortCoupling, bondMatrix,
      LayerShape.incident, pathAt, sampleOne]
  · simp [fullPathMatrix, layerMatrix]

/-- **The law of the first block** is the fresh layer law of shape `.oneBlockTwoPorts`. -/
theorem growthPathLaw_map_sampleOne (b : ℝ) :
    (growthPathLaw W b).map sampleOne = layerLaw W b .oneBlockTwoPorts := by
  set μA := gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
  set μB := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  have hA := measurePreserving_reindex μA (fun _ : Fin 1 => (0 : ℕ)) (fun _ _ _ => Subsingleton.elim _ _)
  have he : Function.Injective (fun j : Fin 2 => (![1, 0] j : ℕ)) := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  have hB0 := measurePreserving_reindex μB (fun j : Fin 2 => (![1, 0] j : ℕ)) he
  have hU : MeasurePreserving (fun (u : Fin 2 → Matrix (Fin W) (Fin W) ℂ) (_ : Fin 1) => u)
      (Measure.pi fun _ : Fin 2 => μB)
      (Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 2 => μB) := by
    have := (measurePreserving_funUnique (Measure.pi fun _ : Fin 2 => μB) (Fin 1)).symm
    convert this using 1
    · funext u; rfl
    · rfl
  have hAll := hA.prod (hU.comp hB0)
  have e : sampleOne (W := W) = Prod.map (fun (ω : ℕ → Matrix (Fin W) (Fin W) ℂ) (_ : Fin 1) => ω 0)
      ((fun (u : Fin 2 → Matrix (Fin W) (Fin W) ℂ) (_ : Fin 1) => u) ∘
        fun (ω : ℕ → Matrix (Fin W) (Fin W) ℂ) (j : Fin 2) => ω (![1, 0] j)) := by
    funext ω; rfl
  rw [e]
  exact hAll.map_eq

theorem tagProjection_one_zero : tagProjection W 1 0 = 1 := by
  ext x y
  simp only [tagProjection, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : x = y <;> simp [h]

theorem measurable_layerResolvent_two (E : ℝ) (z : ℂ) :
    Measurable fun s : LayerSample W .oneBlockTwoPorts =>
      layerResolvent .oneBlockTwoPorts E z 0 s := by
  have hB := measurable_bondMatrix (W := W) (α := LayerSample W .oneBlockTwoPorts)
    .oneBlockTwoPorts measurable_snd
  have hD := measurable_blockDiag (W := W) (k := 1) (α := LayerSample W .oneBlockTwoPorts)
    measurable_fst
  refine measurable_matrix_inv.comp (Measurable.of_eval_matrix _ fun x y => ?_)
  rcases x with x | x <;> rcases y with y | y <;>
    simp only [layerMatrix, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply]
  · exact (hD.eval_matrix.sub measurable_const).sub measurable_const
  · exact hB.eval_matrix
  · exact (measurable_matrix_conjTranspose' hB).eval_matrix
  · exact measurable_const

/-- **Birth of the first tag** (`k = 0`), from `GaussianAbsorptionContract`: for `0 < b < 1/2`,
`κ > 0` and `q ≥ 1` there are `B ≥ 0` and `W₀` with `E[tagMass(0)^q] ≤ B` under `growthPathLaw W b`
for all `W ≥ W₀` and `E ∈ bulkInterval κ`. -/
theorem birth_moment_zero (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) {q : ℕ} (hq : 1 ≤ q) :
    ∃ (B : ℝ) (W₀ : ℕ), 0 ≤ B ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∫⁻ ω, ENNReal.ofReal (tagMass b E W 1 0 ω ^ q) ∂growthPathLaw W b ≤ ENNReal.ofReal B := by
  obtain ⟨ε₁, C, hε₁, hC, hGA'⟩ := hGA b hb0 hb (etaLow b κ) 2 (etaLow_pos (by linarith) hκ)
  refine ⟨C ^ (2 * q), ⌈(2 * q : ℝ) / ε₁⌉₊ + 1, by positivity, fun W hW E hE => ?_⟩
  have hW0 : 0 < W := by omega
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  have hpW : ((2 * q : ℕ) : ℝ) ≤ ε₁ * W := by
    have h1 := Nat.le_ceil ((2 * q : ℝ) / ε₁)
    have h2 : (((⌈(2 * q : ℝ) / ε₁⌉₊ + 1 : ℕ)) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at h2 ⊢
    rw [div_le_iff₀ hε₁] at h1
    nlinarith
  obtain ⟨-, hmom⟩ := hGA' W hW0 .oneBlockTwoPorts
    (0 : Matrix (PhysSite W .oneBlockTwoPorts) (PhysSite W .oneBlockTwoPorts) ℂ) Matrix.isHermitian_zero E (boundaryZ b E)
    (etaLow_le (by linarith) hκ hE) (bulk_norm_z hb0 hb hκ hE)
  have hm := hmom ((2 * q : ℕ) : ℝ) (by exact_mod_cast (show 1 ≤ 2 * q by omega)) hpW
  have hmG : Measurable fun s : LayerSample W .oneBlockTwoPorts =>
      ‖layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 s‖ :=
    (measurable_layerResolvent_two E _).norm
  have := isProbabilityMeasure_layerLaw W b .oneBlockTwoPorts
  obtain ⟨hi, hbd⟩ := integral_abs_pow_le (ν := layerLaw W b .oneBlockTwoPorts) (n := 2 * q)
    (by omega) hC.le ⟨hmG.aestronglyMeasurable, hm⟩
  -- the pointwise bound `t_1 ≤ ‖G‖²`
  have hpt : ∀ ω, tagMass b E W 1 0 ω ^ q ≤
      ‖layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 (sampleOne ω)‖ ^ (2 * q) := by
    intro ω
    set G := layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 (sampleOne ω)
    have hU : boundaryToInterior b E W 1 ω = G.toBlocks₁₂ := by
      rw [boundaryToInterior, fullInverse, fullPathMatrix_one_eq]; rfl
    have hnU : ‖G.toBlocks₁₂‖ ≤ ‖G‖ :=
      norm_submatrix_le G (f := Sum.inl) (g := Sum.inr) Sum.inl_injective Sum.inr_injective
    have htr := re_trace_le_card G.toBlocks₁₂
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, one_mul] at htr
    have ht : tagMass b E W 1 0 ω ≤ ‖G‖ ^ 2 := by
      rw [tagMass, tagResponse, tagProjection_one_zero, Matrix.mul_one, hU]
      calc (W : ℝ)⁻¹ * (G.toBlocks₁₂ᴴ * G.toBlocks₁₂).trace.re ≤ (W : ℝ)⁻¹ * (W * ‖G‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (htr.trans (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) hnU 2) hWr.le)) (by positivity)
        _ = ‖G‖ ^ 2 := by field_simp
    rw [pow_mul]
    exact pow_le_pow_left₀ (tagMass_nonneg b E 1 0 ω) ht q
  calc ∫⁻ ω, ENNReal.ofReal (tagMass b E W 1 0 ω ^ q) ∂growthPathLaw W b
      ≤ ∫⁻ ω, ENNReal.ofReal (‖layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0
          (sampleOne ω)‖ ^ (2 * q)) ∂growthPathLaw W b :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ∫⁻ s, ENNReal.ofReal (‖layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 s‖ ^ (2 * q))
          ∂layerLaw W b .oneBlockTwoPorts := by
        rw [← growthPathLaw_map_sampleOne, lintegral_map ((hmG.pow_const _).ennreal_ofReal)
          measurable_sampleOne]
    _ = ENNReal.ofReal (∫ s, |‖layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 s‖| ^ (2 * q)
          ∂layerLaw W b .oneBlockTwoPorts) := by
        rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun s => by
          positivity)]
        congr 1; funext s; rw [abs_of_nonneg (norm_nonneg _)]
    _ ≤ ENNReal.ofReal (C ^ (2 * q)) := ENNReal.ofReal_le_ofReal hbd

end BlockBand.SourceProcess.FullSource
