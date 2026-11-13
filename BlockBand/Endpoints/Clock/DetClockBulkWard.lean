module

public import BlockBand.Endpoints.Clock.DetClockProofWard
public import BlockBand.Endpoints.Clock.ClockMixingEnergyUniform

/-!
# The deterministic-clock lemma on `bulkInterval κ`: the Ward mean and the injection mean

`DetClockProof.wardMean_of`, `DetClockProof.wardOmega_le`, `DetClockProof.weightedCov_of`,
`DetClockInj.injectionMean_of` and `DetClockInj.cavity_close_matched` fix `-2 < E < 2` before their
constants. Their proofs depend on `E` only through `η = Im z_∂(E)`, `|z_∂(E)|` and `κ = 2 - |E|`.
Here `0 < κ < 4` and `E ∈ bulkInterval κ`, and these are replaced by the uniform bounds
`η_κ = etaLow b κ ≤ Im z` (`etaLow_le_im`), `|z| ≤ 3` (`norm_boundaryZ_le3`),
`(Im z)⁻¹ + |c₀| ≤ 2/η_κ` (`fBound_le`), `η_κ ‖a‖² ≤ -Im a` (from `yLow_le_yA`).
* `cavityClose_unif`: `|a - v| + |a - u| ≤ C δ₀` (`cavity_stability` at `(η_κ, 3, 1)`).
* `injectionMean_unif`: `|E Re Tr C₊ / W - d_*| ≤ C(δ₀ + W⁻²)`.
* `weightedCov_unif`: the three weighted covariances, from `OnePortWeightedCovarianceContract` at
  the given `κ` (instead of `κ = 2 - |E|`).
* `wardOmega_le_unif`, `wardMean_unif`: the sharper Ward mean, with `C, d, W₀` depending only on
  `(b, κ)`.

The algebra of each fixed-energy proof is reused at each `E` (with the exact `η = Im z` where it
cancels); only the constants are taken at the worst case. The hypotheses are
`GaussianAbsorptionContract` (at `η₀ = η_κ`, `M = 3`) and
`LayersOnePort.OnePortWeightedCovarianceContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.LayersOnePort
open scoped Matrix.Norms.L2Operator ComplexConjugate

namespace MovingEnergy

namespace DetClockBulk

open DetClockProof DetClockInj CavityMeanProb OpenInputsProof

variable {b κ : ℝ}

/-- `η_κ ‖a‖² ≤ -Im a` on `bulkInterval κ` (`‖a‖ = 1`, `η_κ = (1-b) y_κ ≤ y_κ ≤ -Im a`). -/
theorem etaLow_port (hb0 : 0 < b) (hκ : 0 < κ) (hκ4 : κ < 4) {E : ℝ}
    (hE : E ∈ bulkInterval κ) : etaLow b κ * ‖matchedA E‖ ^ 2 ≤ -(matchedA E).im := by
  obtain ⟨hE0, hE1⟩ := mem_bulk_lt hκ hE
  have hEa : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  rw [BlockBand.Layers.norm_matchedA hEa, one_pow, mul_one]
  unfold etaLow
  have e : -(matchedA E).im = yA E := rfl
  rw [e]
  have hy0 := yLow_pos hκ hκ4
  have hyy := yLow_le_yA hE
  have : (1 - b) * yLow κ ≤ 1 * yLow κ := mul_le_mul_of_nonneg_right (by linarith) hy0.le
  linarith

/-- **The cavity solution is `O(δ₀)`-close to the matched point, uniformly in
`E ∈ bulkInterval κ`** (the uniform version of `DetClockInj.cavity_close_matched`, with the stability
constant of `cavity_stability` at `(η_κ, 3, 1)`). -/
theorem cavityClose_unif (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ E ∈ bulkInterval κ, ∀ (W : ℕ), 0 < W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ v u : ℂ, IsCavityMatrixSolution X b (1 - 2 * b) E (boundaryZ b E) v u →
        ‖matchedA E - v‖ + ‖matchedA E - u‖ ≤ C * jetDistance0 b E X := by
  have hc : 0 < 1 - 2 * b := by linarith
  have hη0 := etaLow_pos hb1 hκ hκ4
  obtain ⟨C, hC, hstab⟩ := cavity_stability (b := b) (c := 1 - 2 * b) (η := etaLow b κ)
    (M := 3) (astar := 1) hb0 hc hη0 (by norm_num) one_pos
  refine ⟨C, hC, fun E hEκ W hW X hX v u hsol => ?_⟩
  obtain ⟨hE0, hE1⟩ := mem_bulk_lt hκ hEκ
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hη := etaZ_pos (by linarith : b < 1) hE0 hE1
  have hsol' := (isCavityMatrixSolution_iff hX hb0 hc).mp hsol
  have ha1 : ‖matchedA E‖ = 1 := BlockBand.Layers.norm_matchedA hE
  have haim := BlockBand.Layers.matchedA_im_neg (abs_lt.mpr ⟨hE0, hE1⟩)
  have hzeq : -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * matchedA E - (b : ℂ) * matchedA E =
      boundaryZ b E := by
    rw [BlockBand.Layers.boundaryZ_eq hE]; push_cast; ring
  have hres1 : ‖matchedA E - cavityStieltjes (fun _ => (W : ℝ)⁻¹) hX.eigenvalues
      (-(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * matchedA E - (b : ℂ) * matchedA E)‖ ≤
      jetDistance0 b E X := by
    rw [hzeq, ← normalizedResolventTrace_eq hX hη.ne', norm_sub_rev]
    exact le_rfl
  have hres2 : ‖matchedA E - (boundaryZ b E - (b : ℂ) * matchedA E)⁻¹‖ ≤ jetDistance0 b E X := by
    have : boundaryZ b E - (b : ℂ) * matchedA E = (matchedA E)⁻¹ := by unfold boundaryZ; ring
    rw [this, inv_inv, sub_self, norm_zero]
    exact norm_nonneg _
  exact hstab (Fin W) (fun _ => (W : ℝ)⁻¹) hX.eigenvalues E (boundaryZ b E) v u
    (matchedA E) (matchedA E) (jetDistance0 b E X) (isCavityWeights_uniform hW)
    (etaLow_le_im hb1 hκ hEκ) (norm_boundaryZ_le3 hb0 hb1 hκ hEκ) hsol' haim.le (by rw [ha1])
    (etaLow_port hb0 hκ hκ4 hEκ) hres1 hres2

/-- **Injection mean, uniformly in `E ∈ bulkInterval κ`** (the uniform version of
`DetClockInj.injectionMean_of`): there are `C, W₀` depending only on `(b, κ)`
such that for `W ≥ W₀`, every `E ∈ bulkInterval κ` and every Hermitian `X`, `Re Tr C₊` is
integrable and `|E Re Tr C₊ / W - d_*| ≤ C (δ₀ + W⁻²)`. -/
theorem injectionMean_unif (habs : GaussianAbsorptionContract) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      Integrable (fun ω => (freshC b E X ω).trace.re) (freshLaw W b) ∧
      |(∫ ω, (freshC b E X ω).trace.re ∂freshLaw W b) / W - dStar b| ≤
        C * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
  have hc : 0 < 1 - 2 * b := by linarith
  have hηL := etaLow_pos hb1 hκ hκ4
  obtain ⟨C₁, W₁, hC₁, htop⟩ := condMeanTop_large habs hb0 hb1 (M := 3) hηL
  obtain ⟨C₂, hC₂, hclose⟩ := cavityClose_unif hb0 hb1 hκ hκ4
  obtain ⟨ε₁, CA, hε₁, _hCA, habs'⟩ := habs b hb0 hb1 (etaLow b κ) 3 hηL
  refine ⟨(C₁ + C₂) / etaLow b κ, max (max W₁ ⌈2 / ε₁⌉₊) 1, fun W hWW E hEκ X hX => ?_⟩
  obtain ⟨hE0, hE1⟩ := mem_bulk_lt hκ hEκ
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hη := etaZ_pos (by linarith : b < 1) hE0 hE1
  set z := boundaryZ b E with hz
  set η := etaZ b E with hηdef
  have hzL : etaLow b κ ≤ z.im := etaLow_le_im hb1 hκ hEκ
  have hzM : ‖z‖ ≤ 3 := norm_boundaryZ_le3 hb0 hb1 hκ hEκ
  have hηLη : etaLow b κ ≤ η := hzL
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hWW
  have hWε : ⌈2 / ε₁⌉₊ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hWW
  have hW : 0 < W := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _) hWW)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have h2W : (2 : ℝ) ≤ ε₁ * W := by
    have h1 : 2 / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWε)
    rw [div_le_iff₀ hε₁] at h1; linarith
  have hXl := cavityLift_isHermitian hX
  set μ := layerLaw W b LayerShape.oneBlockOnePort with hμ
  set G := layerResolvent LayerShape.oneBlockOnePort E z (cavityLift X) with hG
  have hGf : ∀ ω, freshLayer b E X ω = G ω := fun ω => rfl
  obtain ⟨hinv, hmom⟩ := habs' W hW LayerShape.oneBlockOnePort (cavityLift X) hXl E z hzL hzM
  have hG2 := meq_sq_integrable_of_eLpNorm (hmom 2 (by norm_num) h2W)
  have hGm : Measurable G := measurable_layerResolvent _ _ _ _
  have hGn : Integrable (fun ω => ‖G ω‖) μ := meq_integrable_norm_of_sq hGm.aestronglyMeasurable hG2
  have hCm0 : Measurable (fun ω : LayerSample W .oneBlockOnePort => freshC b E X ω) :=
    (ClockMixingProb.meas_freshC (W := W) b E).comp (f := fun ω => (X, ω))
      (measurable_const.prodMk measurable_id)
  have hCm : Measurable (fun ω => (freshC b E X ω).trace.re) :=
    Complex.measurable_re.comp (ClockMixingProb.meas_trace hCm0)
  have hCi : Integrable (fun ω => (freshC b E X ω).trace.re) μ := by
    refine Integrable.mono' (hG2.const_mul (W : ℝ)) hCm.aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    have h0 : 0 ≤ (freshC b E X ω).trace.re := by
      rw [trace_freshC_eq_sum]; positivity
    rw [Real.norm_of_nonneg h0]
    exact ClockMixingAlg.trace_freshC_le b E X ω
  refine ⟨hCi, ?_⟩
  have hae : ∀ᵐ ω ∂μ, (freshC b E X ω).trace.re =
      -((W : ℝ) / η) * (physBlockTrace (G ω) 0).im := by
    filter_upwards [lct_ae_blocks_isHermitian W b LayerShape.oneBlockOnePort, hinv] with ω hA hH
    have h := etaZ_mul_trace_freshC hW b E hX ω hA hH
    rw [hGf] at h
    field_simp
    linarith
  have hPi : Integrable (fun ω => physBlockTrace (G ω) 0) μ :=
    Integrable.mono' hGn
      ((meq_continuous_physBlockTrace 0).measurable.comp hGm).aestronglyMeasurable
      (ae_of_all _ fun ω => meq_norm_physBlockTrace_le _ _)
  have hint : (∫ ω, (freshC b E X ω).trace.re ∂μ) =
      -((W : ℝ) / η) * (meqMeanA μ G 0).im := by
    rw [integral_congr_ae hae, integral_const_mul, meqMeanA]
    congr 1
    have h1 := Complex.imCLM.integral_comp_comm hPi
    simp only [Complex.imCLM_apply] at h1
    exact h1
  obtain ⟨vu, hsol, -⟩ := cavityMatrix_existsUnique hW hX hb0 hc (z' := z) hη
  have h1 : ‖meqMeanA μ G 0 - vu.1‖ ≤ C₁ / (W : ℝ) ^ 2 :=
    htop W hW hW1 X hX E z vu.1 vu.2 hzL hzM hsol
  have h2 : ‖matchedA E - vu.1‖ + ‖matchedA E - vu.2‖ ≤ C₂ * jetDistance0 b E X :=
    hclose E hEκ W hW X hX vu.1 vu.2 hsol
  have hd : dStar b = -(1 / η) * (matchedA E).im := by
    have hzim : η = -(1 - b) * (matchedA E).im := BlockBand.Layers.boundaryZ_im hE
    have haim := BlockBand.Layers.matchedA_im_neg (abs_lt.mpr ⟨hE0, hE1⟩)
    have h1b : (1 - b) ≠ 0 := by linarith
    unfold dStar
    rw [hzim]
    field_simp
    rw [div_self haim.ne]
  have hkey : (∫ ω, (freshC b E X ω).trace.re ∂μ) / W - dStar b =
      -(1 / η) * (meqMeanA μ G 0 - matchedA E).im := by
    rw [hint, hd, Complex.sub_im]
    field_simp
    ring
  change |(∫ ω, (freshC b E X ω).trace.re ∂μ) / W - dStar b| ≤ _
  rw [hkey, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1 / η)]
  have him : |(meqMeanA μ G 0 - matchedA E).im| ≤
      ‖meqMeanA μ G 0 - vu.1‖ + ‖matchedA E - vu.1‖ := by
    refine (Complex.abs_im_le_norm _).trans ?_
    calc ‖meqMeanA μ G 0 - matchedA E‖ = ‖(meqMeanA μ G 0 - vu.1) - (matchedA E - vu.1)‖ := by
          congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hWinv : C₁ / (W : ℝ) ^ 2 = C₁ * ((W : ℝ)⁻¹) ^ 2 := by field_simp
  have hmain : 1 / η * |(meqMeanA μ G 0 - matchedA E).im| ≤
      (C₁ + C₂) / η * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
    calc 1 / η * |(meqMeanA μ G 0 - matchedA E).im|
        ≤ 1 / η * (C₁ * ((W : ℝ)⁻¹) ^ 2 + C₂ * jetDistance0 b E X) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have : ‖matchedA E - vu.1‖ ≤ C₂ * jetDistance0 b E X := by
            linarith [norm_nonneg (matchedA E - vu.2)]
          linarith
      _ ≤ (C₁ + C₂) / η * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, div_le_div_iff_of_pos_right hη]
          have : 0 ≤ ((W : ℝ)⁻¹) ^ 2 := by positivity
          nlinarith
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact div_le_div_of_nonneg_left (by positivity) hηL hηLη

/-- **The three weighted covariances, uniformly in `E ∈ bulkInterval κ`** (the uniform
version of `DetClockProof.weightedCov_of`, with `OnePortWeightedCovarianceContract` taken at the
given `κ` instead of `κ = 2 - |E|`).
-/
theorem weightedCov_unif (hWC : OnePortWeightedCovarianceContract) (hb0 : 0 < b)
    (hb1 : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ‖meqCov (freshLaw W b) (fun ω => physBlockTrace (freshLayer b E X ω) 0)
          (fun ω => meqPhysProj 0 * freshLayer b E X ω * (onePortWeight b E X)ᴴ)‖ ≤
        C / (W : ℝ) ^ 2 ∧
      ‖meqCov (freshLaw W b) (fun ω => portBlockTrace (freshLayer b E X ω) 0)
          (fun ω => meqPhysProj 0 * freshLayer b E X ω * (onePortWeight b E X)ᴴ)‖ ≤
        C / (W : ℝ) ^ 2 ∧
      ‖meqCov (freshLaw W b) (fun ω => physBlockTrace (freshLayer b E X ω) 0)
          (fun ω => meqPortProj 0 * freshLayer b E X ω * (onePortWeight b E X)ᴴ)‖ ≤
        C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₀, h⟩ := hWC b hb0 hb1 κ hκ
  refine ⟨C, W₀, fun W hW hWW E hEb X hX => ?_⟩
  have hPn : ‖(onePortPhysProj : Matrix (LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort) ℂ)‖ ≤ 1 := by
    rw [← meqPhysProj_eq_onePort]; exact meq_norm_physProj_le 0
  have hQn : ‖(onePortPortProj : Matrix (LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort) ℂ)‖ ≤ 1 := by
    rw [← meqPortProj_eq_onePort]; exact meq_norm_portProj_le 0
  have hgA : (fun ω => physBlockTrace (freshLayer b E X ω) 0) =
      fun ω => (W : ℂ)⁻¹ * (onePortPhysProj * onePortResolvent b E X ω).trace := by
    funext ω; rw [physBlockTrace_eq_onePort]; rfl
  have hgP : (fun ω => portBlockTrace (freshLayer b E X ω) 0) =
      fun ω => (W : ℂ)⁻¹ * (onePortPortProj * onePortResolvent b E X ω).trace := by
    funext ω; rw [portBlockTrace_eq_onePort]; rfl
  obtain ⟨-, -, -, h1⟩ := h W hW hWW X hX E hEb onePortPhysProj onePortPhysProj hPn hPn
  obtain ⟨-, -, -, h2⟩ := h W hW hWW X hX E hEb onePortPortProj onePortPhysProj hQn hPn
  obtain ⟨-, -, -, h3⟩ := h W hW hWW X hX E hEb onePortPhysProj onePortPortProj hPn hQn
  rw [hgA, hgP, meqPhysProj_eq_onePort, meqPortProj_eq_onePort]
  exact ⟨h1, h2, h3⟩

/-- **The scalar closeness `|Ω| ≤ C(δ₀ + W⁻²)`, uniformly in `E ∈ bulkInterval κ`** (the
uniform version of `DetClockProof.wardOmega_le`). -/
theorem wardOmega_le_unif (hGA : GaussianAbsorptionContract) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 < C ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      X.IsHermitian → ‖wardOmega W b E X‖ ≤ C * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
  have hc : 0 < 1 - 2 * b := by linarith
  have hηL := etaLow_pos hb1 hκ hκ4
  obtain ⟨C₁, W₁, hC₁, htop⟩ := condMeanTop_large hGA hb0 hb1 (M := 3) hηL
  obtain ⟨C₃, W₃, hC₃, hport⟩ := condMean_large hGA hb0 hb1 (M := 3) hηL
  obtain ⟨C₂, hC₂, hclose⟩ := cavityClose_unif hb0 hb1 hκ hκ4
  refine ⟨C₁ + C₃ + C₂, max W₁ W₃, by positivity, fun W hW0 hWW E hEκ X hX => ?_⟩
  obtain ⟨hE0, hE1⟩ := mem_bulk_lt hκ hEκ
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hη := etaZ_pos (by linarith : b < 1) hE0 hE1
  have hzL : etaLow b κ ≤ (boundaryZ b E).im := etaLow_le_im hb1 hκ hEκ
  have hzM : ‖boundaryZ b E‖ ≤ 3 := norm_boundaryZ_le3 hb0 hb1 hκ hEκ
  obtain ⟨vu, hsol, -⟩ := cavityMatrix_existsUnique hW0 hX hb0 hc (e := E) (z' := boundaryZ b E) hη
  have hv := htop W hW0 (le_trans (le_max_left _ _) hWW) X hX E (boundaryZ b E) vu.1 vu.2 hzL
    hzM hsol
  have hu0 := hport W hW0 (le_trans (le_max_right _ _) hWW) X hX E (boundaryZ b E) vu.1 vu.2 hzL
    hzM hsol
  have hu : ‖meqMeanP (freshLaw W b) (freshLayer b E X) 0 - vu.2‖ ≤ C₃ / (W : ℝ) ^ 2 := by
    have he : meqMeanP (freshLaw W b) (freshLayer b E X) 0 =
        ∫ ω, cavityHplus E X (boundaryZ b E) ω ∂layerLaw W b .oneBlockOnePort := by
      rw [meqMeanP]
      exact integral_congr_ae ((CavityMeanProb.ae_cavityHplus_eq_portBlockTrace hb1 E X
        (boundaryZ b E)).mono fun ω hω => hω.symm)
    rw [he]; exact hu0
  have hcl := hclose E hEκ W hW0 X hX vu.1 vu.2 hsol
  set vbar := meqMeanA (freshLaw W b) (freshLayer b E X) 0
  set ubar := meqMeanP (freshLaw W b) (freshLayer b E X) 0
  have hv' : ‖vbar - vu.1‖ ≤ C₁ / (W : ℝ) ^ 2 := hv
  have hzeq : boundaryZ b E + E + ((1 - 2 * (b : ℂ)) * matchedA E + (b : ℂ) * matchedA E) = 0 := by
    rw [BlockBand.Layers.boundaryZ_eq hE]; ring
  have hΩe : wardOmega W b E X = (1 - 2 * (b : ℂ)) * (vbar - matchedA E) +
      (b : ℂ) * (ubar - matchedA E) := by
    unfold wardOmega; linear_combination hzeq
  have hcn : ‖(1 - 2 * (b : ℂ))‖ ≤ 1 := by
    rw [show (1 : ℂ) - 2 * (b : ℂ) = ((1 - 2 * b : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]; linarith
  have hbn : ‖(b : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]; linarith
  have e1 : ‖vbar - matchedA E‖ ≤ C₁ / (W : ℝ) ^ 2 + ‖matchedA E - vu.1‖ := by
    calc ‖vbar - matchedA E‖ = ‖(vbar - vu.1) - (matchedA E - vu.1)‖ := by ring_nf
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add hv' le_rfl)
  have e2 : ‖ubar - matchedA E‖ ≤ C₃ / (W : ℝ) ^ 2 + ‖matchedA E - vu.2‖ := by
    calc ‖ubar - matchedA E‖ = ‖(ubar - vu.2) - (matchedA E - vu.2)‖ := by ring_nf
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add hu le_rfl)
  have f1 := mul_le_mul hcn e1 (norm_nonneg _) zero_le_one
  have f2 := mul_le_mul hbn e2 (norm_nonneg _) zero_le_one
  have hn : ‖wardOmega W b E X‖ ≤ ‖(1 - 2 * (b : ℂ))‖ * ‖vbar - matchedA E‖ +
      ‖(b : ℂ)‖ * ‖ubar - matchedA E‖ := by
    rw [hΩe]; refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
  have hWi : ((W : ℝ)⁻¹) ^ 2 = 1 / (W : ℝ) ^ 2 := by rw [inv_pow, one_div]
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hw0 : 0 ≤ 1 / (W : ℝ) ^ 2 := by positivity
  have e3 : C₁ / (W : ℝ) ^ 2 + C₃ / (W : ℝ) ^ 2 = (C₁ + C₃) * (1 / (W : ℝ) ^ 2) := by ring
  have e4 : (C₁ + C₃ + C₂) * (jetDistance0 b E X + 1 / (W : ℝ) ^ 2) =
      (C₁ + C₃) * (1 / (W : ℝ) ^ 2) + C₂ * jetDistance0 b E X +
        ((C₁ + C₃) * jetDistance0 b E X + C₂ * (1 / (W : ℝ) ^ 2)) := by ring
  have e5 : 0 ≤ (C₁ + C₃) * jetDistance0 b E X + C₂ * (1 / (W : ℝ) ^ 2) := by positivity
  rw [hWi]
  linarith

/-- **The Ward mean, uniformly in `E ∈ bulkInterval κ`.** Fixed `0 < b < 1/2`, `0 < κ < 4`.
From `GaussianAbsorptionContract` and `OnePortWeightedCovarianceContract`: there are `C`,
`d > 0` and `W₀` depending only on `(b, κ)` such that for `W ≥ W₀`, every `E ∈ bulkInterval κ`
and every Hermitian `X` with `δ₀(X) ≤ d` there is `Ω ∈ ℂ` with `|Ω| ≤ C(δ₀ + W⁻²)` and
`‖E(LL*) - I - Ωf - Ω̄f*‖ ≤ C(δ₀² + W⁻²)`.
-/
theorem wardMean_unif (hGA : GaussianAbsorptionContract) (hWC : OnePortWeightedCovarianceContract)
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∃ (C d : ℝ) (W₀ : ℕ), 0 < d ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → jetDistance0 b E X ≤ d →
        ∃ Ω : ℂ, ‖Ω‖ ≤ C * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) ∧
          ‖matrixExpect (freshLaw W b) (freshU b E X) - 1 - Ω • passiveF b E X -
              conj Ω • (passiveF b E X)ᴴ‖ ≤
            C * (jetDistance0 b E X ^ 2 + ((W : ℝ)⁻¹) ^ 2) := by
  have hηL := etaLow_pos hb1 hκ hκ4
  set ηL := etaLow b κ with hηLdef
  obtain ⟨CΩ, WΩ, hCΩ0, hΩle⟩ := wardOmega_le_unif hGA hb0 hb1 hκ hκ4
  obtain ⟨ε₁, CA, hε₁, _hCA, habs'⟩ := hGA b hb0 hb1 ηL 3 hηL
  obtain ⟨Ch, Wh, hhyp⟩ := weightedCov_unif hWC hb0 hb1 hκ
  set Kf := 2 / ηL with hKf
  have hKf0 : 0 ≤ Kf := by positivity
  set CR := 3 * max Ch 0 with hCR
  have hCR0 : 0 ≤ CR := by positivity
  set d := ηL / (4 * CΩ) with hd
  have hd0 : 0 < d := by positivity
  set Cout := (8 * Kf * CΩ ^ 2 + 2 * CR) / ηL + CΩ with hCout
  have hCoutΩ : CΩ ≤ Cout := by
    have : 0 ≤ (8 * Kf * CΩ ^ 2 + 2 * CR) / ηL := by positivity
    linarith
  set Wd : ℕ := ⌈Real.sqrt (4 * CΩ / ηL)⌉₊ with hWd
  refine ⟨Cout, d, max (max WΩ (max ⌈2 / ε₁⌉₊ Wh)) (max Wd 1), hd0,
    fun W hWW E hEκ X hX hδ => ?_⟩
  obtain ⟨hE0, hE1⟩ := mem_bulk_lt hκ hEκ
  have hη := etaZ_pos (by linarith : b < 1) hE0 hE1
  set z := boundaryZ b E with hzdef
  set η := etaZ b E with hηdef
  have hzim : z.im = η := rfl
  have hηLη : ηL ≤ η := etaLow_le_im hb1 hκ hEκ
  have hzM : ‖z‖ ≤ 3 := norm_boundaryZ_le3 hb0 hb1 hκ hEκ
  have hzc : z ≠ conj z := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  have hζ : z - conj z ≠ 0 := sub_ne_zero.mpr hzc
  have hζn : ‖z - conj z‖ = 2 * η := by
    have : z - conj z = ((2 * η : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hzim]; ring
    rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have hWΩ : WΩ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hWW
  have hWε : ⌈2 / ε₁⌉₊ ≤ W := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hWW
  have hWh : Wh ≤ W := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hWW
  have hWdW : Wd ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hWW
  have hW0 : 0 < W := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) hWW))
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW0
  have h2W : (2 : ℝ) ≤ ε₁ * W := by
    have h1 : 2 / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWε)
    rw [div_le_iff₀ hε₁] at h1; linarith
  set w := ((W : ℝ)⁻¹) ^ 2 with hw
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 := by
    rw [hw, inv_pow]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hW1r)
  have hWinv2 : CΩ * w ≤ ηL / 4 := by
    have hs : Real.sqrt (4 * CΩ / ηL) ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWdW)
    have hsq : 4 * CΩ / ηL ≤ (W : ℝ) ^ 2 := by
      have e := Real.sq_sqrt (show 0 ≤ 4 * CΩ / ηL by positivity)
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
      linarith
    rw [div_le_iff₀ hηL] at hsq
    rw [hw, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  -- the layer
  have hXl := CavityMeanProb.cavityLift_isHermitian hX
  obtain ⟨hinv, hmom⟩ := habs' W hW0 LayerShape.oneBlockOnePort (cavityLift X) hXl E z hηLη hzM
  have hG2 : Integrable (fun ω => ‖freshLayer b E X ω‖ ^ 2) (freshLaw W b) :=
    meq_sq_integrable_of_eLpNorm (hmom 2 (by norm_num) h2W)
  have hGm : Measurable (fun ω => freshLayer b E X ω) := measurable_layerResolvent _ _ _ _
  have hGn : Integrable (fun ω => ‖freshLayer b E X ω‖) (freshLaw W b) :=
    meq_integrable_norm_of_sq hGm.aestronglyMeasurable hG2
  set Ω := wardOmega W b E X with hΩdef
  set δ₀ := jetDistance0 b E X with hδ₀
  have hδ0 : 0 ≤ δ₀ := norm_nonneg _
  have hΩb : ‖Ω‖ ≤ CΩ * (δ₀ + w) := hΩle W hW0 hWΩ E hEκ X hX
  refine ⟨Ω, hΩb.trans (mul_le_mul_of_nonneg_right hCoutΩ (by positivity)), ?_⟩
  have hΩs : ‖Ω‖ ≤ η / 2 := by
    have : CΩ * δ₀ ≤ ηL / 4 := by
      calc CΩ * δ₀ ≤ CΩ * d := mul_le_mul_of_nonneg_left hδ hCΩ0.le
        _ = ηL / 4 := by rw [hd]; field_simp
    have := mul_add CΩ δ₀ w
    linarith
  set K := z • (1 : Matrix (Fin W) (Fin W) ℂ) - X with hKdef
  set T := (z - Ω) • (1 : Matrix (Fin W) (Fin W) ℂ) - X with hTdef
  have hTim : η / 2 ≤ (z - Ω).im := by
    rw [Complex.sub_im, hzim]
    have := abs_le.mp ((Complex.abs_im_le_norm Ω).trans hΩs)
    linarith
  have hTim0 : 0 < (z - Ω).im := by linarith
  have hT : IsUnit T.det := isUnit_shift hX hTim0
  have hK : IsUnit K.det := isUnit_shift hX (by rw [hzim]; exact hη)
  have hTn : ‖T⁻¹‖ ≤ 2 / η := by
    refine (ClockMixingAlg.norm_resolvent_le hTim0 hX).trans ?_
    rw [show 2 / η = (η / 2)⁻¹ by field_simp]
    exact inv_anti₀ (by positivity) hTim
  have hfeq : passiveF b E X = K⁻¹ - (z - conj z)⁻¹ • (1 : Matrix (Fin W) (Fin W) ℂ) := by
    rw [passiveF, passiveResolvent, ClockMixingAlg.cZero_eq]
  have hfn : ‖passiveF b E X‖ ≤ Kf :=
    (ClockMixingAlg.norm_passiveF_le b E (by rw [hzim]; exact hη) hX).trans
      (fBound_le hb1 hκ hκ4 hEκ)
  have hTG : T * wardG11 W b E X = 1 + wardResid W b E X :=
    ward_topEq hb0.le hb1.le E hX hW0 (le_trans hη.le (le_of_eq hzim.symm)) hinv hG2
  have halg := ward_algebra hX (Ω := Ω) hζ hKdef hTdef hfeq hK hT hTG
  rw [ward_expect hX hzc hinv hGn, halg]
  -- the weighted residual
  obtain ⟨hh1, hh2, hh3⟩ := hhyp W hW0 hWh E hEκ X hX
  have hCh0 : Ch / (W : ℝ) ^ 2 ≤ max Ch 0 * w := by
    rw [hw, inv_pow, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  have hRn : ‖wardResid W b E X * Kᴴ‖ ≤ CR * w := by
    have := wardResid_mul_le hb0 hb1 hGn hG2 (hh1.trans hCh0) (hh2.trans hCh0) (hh3.trans hCh0)
    rw [hCR]; linarith
  set f := passiveF b E X with hfdef
  set Err := -((z - conj z) * Ω ^ 2) • (T⁻¹ * f) + (1 + Ω • T⁻¹) * (wardResid W b E X * Kᴴ)
    with hErr
  have hErrn : ‖Err‖ ≤ 4 * Kf * ‖Ω‖ ^ 2 + 2 * (CR * w) := by
    have e1 : ‖-((z - conj z) * Ω ^ 2) • (T⁻¹ * f)‖ ≤ 4 * Kf * ‖Ω‖ ^ 2 := by
      refine (norm_smul_le _ _).trans ?_
      rw [norm_neg, norm_mul, norm_pow, hζn]
      have h1 : ‖T⁻¹ * f‖ ≤ 2 / η * Kf :=
        (l2_opNorm_mul _ _).trans (mul_le_mul hTn hfn (norm_nonneg _) (by positivity))
      calc 2 * η * ‖Ω‖ ^ 2 * ‖T⁻¹ * f‖ ≤ 2 * η * ‖Ω‖ ^ 2 * (2 / η * Kf) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 4 * Kf * ‖Ω‖ ^ 2 := by field_simp; ring
    have e2 : ‖(1 : Matrix (Fin W) (Fin W) ℂ) + Ω • T⁻¹‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      have h1 := lct_norm_one_le (n := Fin W)
      have h2 : ‖Ω • T⁻¹‖ ≤ 1 := by
        refine (norm_smul_le _ _).trans ?_
        calc ‖Ω‖ * ‖T⁻¹‖ ≤ (η / 2) * (2 / η) := mul_le_mul hΩs hTn (norm_nonneg _) (by positivity)
          _ = 1 := by field_simp
      linarith
    have e3 : ‖(1 + Ω • T⁻¹) * (wardResid W b E X * Kᴴ)‖ ≤ 2 * (CR * w) :=
      (l2_opNorm_mul _ _).trans (mul_le_mul e2 hRn (norm_nonneg _) (by norm_num))
    exact (norm_add_le _ _).trans (add_le_add e1 e3)
  have hfin : ‖(-(z - conj z)⁻¹) • (Err - Errᴴ)‖ ≤ ‖Err‖ / η := by
    refine (norm_smul_le _ _).trans ?_
    rw [norm_neg, norm_inv, hζn]
    have : ‖Err - Errᴴ‖ ≤ 2 * ‖Err‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [l2_opNorm_conjTranspose]; linarith
    calc (2 * η)⁻¹ * ‖Err - Errᴴ‖ ≤ (2 * η)⁻¹ * (2 * ‖Err‖) := by gcongr
      _ = ‖Err‖ / η := by field_simp
  refine hfin.trans ?_
  have hΩ2 : ‖Ω‖ ^ 2 ≤ 2 * CΩ ^ 2 * (δ₀ ^ 2 + w) :=
    sq_le_of_le_mul_add (norm_nonneg _) hw0 hw1 hΩb
  have g1 : 4 * Kf * ‖Ω‖ ^ 2 ≤ 4 * Kf * (2 * CΩ ^ 2 * (δ₀ ^ 2 + w)) :=
    mul_le_mul_of_nonneg_left hΩ2 (by positivity)
  have g2 : 2 * (CR * w) ≤ 2 * (CR * (δ₀ ^ 2 + w)) := by
    have : w ≤ δ₀ ^ 2 + w := by nlinarith [sq_nonneg δ₀]
    have := mul_le_mul_of_nonneg_left this hCR0
    linarith
  have hErr2 : ‖Err‖ ≤ (8 * Kf * CΩ ^ 2 + 2 * CR) * (δ₀ ^ 2 + w) := by
    have : 4 * Kf * (2 * CΩ ^ 2 * (δ₀ ^ 2 + w)) + 2 * (CR * (δ₀ ^ 2 + w)) =
        (8 * Kf * CΩ ^ 2 + 2 * CR) * (δ₀ ^ 2 + w) := by ring
    linarith
  have k1 : ‖Err‖ / η ≤ ‖Err‖ / ηL := div_le_div_of_nonneg_left (norm_nonneg _) hηL hηLη
  have k2 : ‖Err‖ / ηL ≤ (8 * Kf * CΩ ^ 2 + 2 * CR) / ηL * (δ₀ ^ 2 + w) := by
    rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hErr2 hηL.le
  have k3 : (8 * Kf * CΩ ^ 2 + 2 * CR) / ηL * (δ₀ ^ 2 + w) ≤ Cout * (δ₀ ^ 2 + w) :=
    mul_le_mul_of_nonneg_right (by rw [hCout]; linarith) (by positivity)
  linarith

end DetClockBulk

end MovingEnergy

end BlockBand.Endpoints.Clock
