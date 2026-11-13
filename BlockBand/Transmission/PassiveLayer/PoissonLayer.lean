module

public import BlockBand.Transmission.PassiveLayer.LayerSchur
public import BlockBand.Transmission.PassiveLayer.Poisson
public import BlockBand.Transmission.PassiveCovariance.Fluctuation
public import BlockBand.Transmission.SchurDerivative
public import BlockBand.Transmission.Bridge.AlmostSure
public import BlockBand.Transmission.Bridge.NullDet

/-!
# Passive inverse moments by the half-plane Poisson average

Write `X = X_h - iY`, `X_h = hermPart X`, `Y = passiveY X ⪰ 0`, and
`𝒢(ζ) = poissonF E w X ω ζ = [[A - E - X_h + ζY, B], [B*, w]]⁻¹`.

* `poissonInput_I`: `X_h - iY = X`; `poissonInput_real_isHermitian`: `X_h - tY` is Hermitian
  for real `t`; `passiveY_poissonInput`: `-Im(X_h - ζY) = (Im ζ) Y ⪰ 0` for `Im ζ ≥ 0`.
* `poissonF_analytic`: on `A` Hermitian, `B` invertible, `Im w > 0`, `𝒢(ζ)` is holomorphic on
  the open, continuous and bounded on the closed upper half-plane (`layer_schur`).
* `enorm_layerAt_rpow_le`: `‖𝒢(i)‖^p ≤ ∫ ‖𝒢(t(θ))‖^p dν(θ)` (`Poisson`).
* `layerAt_moment`: **from `Layers.GaussianAbsorptionContract` (explicit hypothesis)**, for
  `η₀ > 0`, `M`: there are `ε₁, C > 0` such that for `W ≥ 1`, real `E`, `Im w ≥ η₀`, `|w| ≤ M`,
  every passive `X` and `1 ≤ p ≤ ε₁W`: the layer matrix is a.s. invertible and
  `‖‖𝒢‖‖_{L^p(freshLaw W b)} ≤ C` (operator norm). Tonelli in `(ω, θ)`.

The subharmonic Poisson inequality of the paper is replaced by the Poisson *identity* for the
bounded
holomorphic matrix function, the norm of an integral, and Jensen; no subharmonicity is needed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Transmission
open scoped Matrix.Norms.L2Operator ComplexOrder ENNReal

variable {W : ℕ}

/-- The Hermitian part `X_h = (X + X*)/2`. -/
def hermPart (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ := (1 / 2 : ℂ) • (X + Xᴴ)

/-- The Poisson family `ζ ↦ X_h - ζY` (`Y = -Im X`); its value at `ζ = i` is `X`. -/
def poissonInput (X : Matrix (Fin W) (Fin W) ℂ) (ζ : ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  hermPart X - ζ • passiveY X

theorem poissonInput_I (X : Matrix (Fin W) (Fin W) ℂ) : poissonInput X Complex.I = X := by
  ext u v
  simp only [poissonInput, hermPart, passiveY, matrixImaginaryPart, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem passiveY_isHermitian (X : Matrix (Fin W) (Fin W) ℂ) : (passiveY X).IsHermitian :=
  (matrixImaginaryPart_isHermitian X).neg

theorem hermPart_isHermitian (X : Matrix (Fin W) (Fin W) ℂ) : (hermPart X).IsHermitian := by
  ext u v
  simp [hermPart, Matrix.conjTranspose_apply, add_comm]
  ring

theorem poissonInput_real_isHermitian (X : Matrix (Fin W) (Fin W) ℂ) (t : ℝ) :
    (poissonInput X t).IsHermitian := by
  refine (hermPart_isHermitian X).sub ?_
  ext u v
  have := congrFun (congrFun (passiveY_isHermitian X) u) v
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul',
    Complex.star_def, Complex.conj_ofReal] at this ⊢
  rw [← this]

theorem passiveY_poissonInput (X : Matrix (Fin W) (Fin W) ℂ) (ζ : ℂ) :
    passiveY (poissonInput X ζ) = (ζ.im : ℂ) • passiveY X := by
  ext u v
  simp only [passiveY, matrixImaginaryPart, poissonInput, hermPart, Matrix.neg_apply,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
    smul_eq_mul, star_sub, star_mul', star_add, star_neg, star_div₀, star_star]
  apply Complex.ext <;> simp <;> ring

theorem layerMatrix_poisson (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) (ζ : ℂ) :
    layerMatrix .oneBlockOnePort E w (liftX (poissonInput X ζ)) ω =
      layerMatrix .oneBlockOnePort E w (liftX (hermPart X)) ω +
        ζ • fromBlocks (liftX (passiveY X)) 0 0 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [layerMatrix, liftX, poissonInput, fromBlocks]
  all_goals ring

/-- `ζ ↦ 𝒢(X_h - ζY)`, the layer resolvent along the Poisson family. -/
def poissonF (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort)
    (ζ : ℂ) : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  layerResolvent .oneBlockOnePort E w (liftX (poissonInput X ζ)) ω

theorem poissonF_I (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : poissonF E w X ω Complex.I = layerAt E w X ω := by
  rw [poissonF, poissonInput_I]; rfl

theorem passive_poissonInput {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    {ζ : ℂ} (hζ : ζ ∈ upperClosed) : (passiveY (poissonInput X ζ)).PosSemidef := by
  rw [passiveY_poissonInput]
  exact hY.smul (by exact_mod_cast (show (0 : ℝ) ≤ ζ.im from hζ))

theorem poissonF_analytic (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) :
    (∀ ζ ∈ upperClosed, ‖poissonF E w X ω ζ‖ ≤ layerBound w (schurDelta w ω)⁻¹ ‖bondL ω‖) ∧
      ContinuousOn (poissonF E w X ω) upperClosed ∧
      DifferentiableOn ℂ (poissonF E w X ω) upperOpen := by
  have hd : ∀ ζ ∈ upperClosed, DifferentiableAt ℂ (poissonF E w X ω) ζ := by
    intro ζ hζ
    have hu := (layer_schur E hw (passive_poissonInput hY hζ) hA hB).1
    rw [layerMatrix_poisson] at hu
    have hfun : poissonF E w X ω = fun ζ => (layerMatrix .oneBlockOnePort E w
        (liftX (hermPart X)) ω + ζ • fromBlocks (liftX (passiveY X)) 0 0 0)⁻¹ := by
      funext ζ; rw [poissonF, layerResolvent, layerMatrix_poisson]
    rw [hfun]
    exact (affineInverse_hasDerivAt _ _ ζ ((isUnit_iff_isUnit_det _).mpr hu)).differentiableAt
  refine ⟨fun ζ hζ => (layer_schur E hw (passive_poissonInput hY hζ) hA hB).2.2.2,
    fun ζ hζ => (hd ζ hζ).continuousAt.continuousWithinAt,
    fun ζ hζ => (hd ζ (show 0 ≤ ζ.im from le_of_lt hζ)).differentiableWithinAt⟩

/-- **Pointwise Poisson bound**: on the event `A` Hermitian, `B` invertible,
`‖𝒢(X)‖^p ≤ ∫ ‖𝒢(X_h - tY)‖^p dν(t)` with Hermitian inputs `X_h - tY`, `t` real. -/
theorem enorm_layerAt_rpow_le (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) {p : ℝ} (hp : 1 ≤ p) :
    ‖layerAt E w X ω‖ₑ ^ p ≤ ∫⁻ θ, ‖poissonF E w X ω (realCayley θ)‖ₑ ^ p ∂cayleyLaw := by
  obtain ⟨hb, hc, hd⟩ := poissonF_analytic E hw hY hA hB
  have := enorm_rpow_le_lintegral_cayley hc hd hb hp
  rwa [poissonF_I] at this

theorem layerLaw_map_block (W : ℕ) (b : ℝ) (σ : LayerShape) (a : Fin σ.blocks) :
    (layerLaw W b σ).map (fun ω => ω.1 a) =
      gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)) := by
  have : (fun ω : LayerSample W σ => ω.1 a) = (fun u => u a) ∘ Prod.fst := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply a) measurable_fst, layerLaw,
    Measure.map_fst_prod, measure_univ, one_smul, (measurePreserving_eval _ a).map_eq]

theorem layerLaw_map_bond (W : ℕ) (b : ℝ) (σ : LayerShape) (a : Fin σ.blocks) (j : Fin σ.ports) :
    (layerLaw W b σ).map (fun ω => ω.2 a j) =
      ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) := by
  have : (fun ω : LayerSample W σ => ω.2 a j) =
      (fun v : Fin σ.ports → Matrix (Fin W) (Fin W) ℂ => v j) ∘ (fun u => u a) ∘ Prod.snd := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply j)
    ((measurable_pi_apply a).comp measurable_snd), ← Measure.map_map (measurable_pi_apply a)
    measurable_snd, layerLaw, Measure.map_snd_prod, measure_univ, one_smul,
    (measurePreserving_eval _ a).map_eq, (measurePreserving_eval _ j).map_eq]

theorem ae_good (W : ℕ) {b : ℝ} (hb0 : 0 < b) (hW : 1 ≤ W) :
    ∀ᵐ ω ∂freshLaw W b, (ω.1 0).IsHermitian ∧ IsUnit (ω.2 0 0) := by
  have hA : ∀ᵐ ω ∂freshLaw W b, (ω.1 0).IsHermitian := by
    have h := Bridge.ae_isHermitian_gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
    rw [← layerLaw_map_block W b .oneBlockOnePort 0] at h
    exact ae_of_ae_map ((measurable_pi_apply 0).comp measurable_fst).aemeasurable h
  filter_upwards [hA, Bridge.ae_isUnit_layerLaw_bond hb0 hW .oneBlockOnePort] with ω h1 h2
  exact ⟨h1, h2 0 0⟩

theorem measurable_poissonF_uncurry (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (p : ℝ) :
    Measurable (Function.uncurry fun (ω : LayerSample W .oneBlockOnePort) (θ : ℝ) =>
      ‖poissonF E w X ω (realCayley θ)‖ₑ ^ p) := by
  have hK := measurable_layerMatrix E w (hermPart X)
  have hfun : (Function.uncurry fun (ω : LayerSample W .oneBlockOnePort) (θ : ℝ) =>
      poissonF E w X ω (realCayley θ)) = (fun M => M⁻¹) ∘ fun x =>
        layerMatrix .oneBlockOnePort E w (liftX (hermPart X)) x.1 +
          ((realCayley x.2 : ℝ) : ℂ) • fromBlocks (liftX (passiveY X)) 0 0 0 := by
    funext ⟨ω, θ⟩
    simp only [Function.uncurry_apply_pair, Function.comp_apply, poissonF, layerResolvent,
      layerMatrix_poisson]
  have hm : Measurable (Function.uncurry fun (ω : LayerSample W .oneBlockOnePort) (θ : ℝ) =>
      poissonF E w X ω (realCayley θ)) := by
    rw [hfun]
    refine Bridge.measurable_matrix_inv.comp ((hK.comp measurable_fst).add ?_)
    exact ((Complex.measurable_ofReal.comp (measurable_realCayley.comp measurable_snd)).smul_const _)
  exact (measurable_enorm.comp hm).pow_const p

section Helpers
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem lintegral_rpow_le_of_eLpNorm_le {f : α → ℝ} (hf : AEStronglyMeasurable f μ) {p : ℝ}
    (hp : 0 < p) {c : ℝ≥0∞} (h : eLpNorm f (ENNReal.ofReal p) μ ≤ c) : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ ≤ c ^ p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le] at h
  have := ENNReal.rpow_le_rpow h hp.le
  rwa [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one] at this

theorem eLpNorm_le_of_lintegral_rpow_le {f : α → ℝ} (hf : AEStronglyMeasurable f μ) {p : ℝ}
    (hp : 0 < p) {c : ℝ≥0∞} (h : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ ≤ c ^ p) : eLpNorm f (ENNReal.ofReal p) μ ≤ c := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le]
  calc (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ (c ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow h (by positivity)
    _ = c := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

end Helpers

/-- **Inverse moments of the passive layer** from the Hermitian `GaussianAbsorptionContract`. -/
theorem layerAt_moment (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {η₀ M : ℝ} (hη₀ : 0 < η₀) :
    ∃ ε₁ C : ℝ, 0 < ε₁ ∧ 0 < C ∧ ∀ W : ℕ, 1 ≤ W → ∀ (E : ℝ) (w : ℂ), η₀ ≤ w.im → ‖w‖ ≤ M →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ p : ℝ, 1 ≤ p →
        p ≤ ε₁ * W →
        (∀ᵐ ω ∂freshLaw W b, IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω).det) ∧
        eLpNorm (fun ω => ‖layerAt E w X ω‖) (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal C := by
  obtain ⟨ε₁, C, hε, hC, hGA'⟩ := hGA b hb0 hb η₀ M hη₀
  refine ⟨ε₁, C, hε, hC, fun W hW E w hw1 hw2 X hY p hp hpW => ?_⟩
  have hw : 0 < w.im := lt_of_lt_of_le hη₀ hw1
  have hp0 : 0 < p := by linarith
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_good W hb0 hW] with ω hω
    exact (layer_schur E hw hY hω.1 hω.2).1
  have hθ : ∀ θ : ℝ, ∫⁻ ω, ‖poissonF E w X ω (realCayley θ)‖ₑ ^ p ∂freshLaw W b ≤
      ENNReal.ofReal C ^ p := by
    intro θ
    have h := (hGA' W (by omega) .oneBlockOnePort (liftX (poissonInput X (realCayley θ)))
      (liftX_isHermitian (poissonInput_real_isHermitian X _)) E w hw1 hw2).2 p hp hpW
    have hm : AEStronglyMeasurable (fun ω => ‖layerResolvent .oneBlockOnePort E w
        (liftX (poissonInput X (realCayley θ))) ω‖) (layerLaw W b .oneBlockOnePort) :=
      (continuous_norm.measurable.comp (Bridge.measurable_matrix_inv.comp
        (measurable_layerMatrix E w _))).aestronglyMeasurable
    have := lintegral_rpow_le_of_eLpNorm_le hm hp0 h
    simpa only [enorm_norm, poissonF] using this
  have hm : AEStronglyMeasurable (fun ω => ‖layerAt E w X ω‖) (freshLaw W b) :=
    (continuous_norm.measurable.comp (Bridge.measurable_matrix_inv.comp
      (measurable_layerMatrix E w X))).aestronglyMeasurable
  apply eLpNorm_le_of_lintegral_rpow_le hm hp0
  simp only [enorm_norm]
  calc ∫⁻ ω, ‖layerAt E w X ω‖ₑ ^ p ∂freshLaw W b
      ≤ ∫⁻ ω, ∫⁻ θ, ‖poissonF E w X ω (realCayley θ)‖ₑ ^ p ∂cayleyLaw ∂freshLaw W b := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_good W hb0 hW] with ω hω
        exact enorm_layerAt_rpow_le E hw hY hω.1 hω.2 hp
    _ = ∫⁻ θ, ∫⁻ ω, ‖poissonF E w X ω (realCayley θ)‖ₑ ^ p ∂freshLaw W b ∂cayleyLaw :=
        lintegral_lintegral_swap (measurable_poissonF_uncurry E w X p).aemeasurable
    _ ≤ ∫⁻ _θ, ENNReal.ofReal C ^ p ∂cayleyLaw := lintegral_mono hθ
    _ = ENNReal.ofReal C ^ p := by simp

end BlockBand.Transmission.PassiveLayer
