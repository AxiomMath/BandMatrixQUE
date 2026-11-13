module

public import BlockBand.SourceProcess.FullSourceCovariance.CrossedSum

/-!
# Level 1 of both `Δ`-covariances: first term plus one product

* `fForm x y = a*K̂𝒢c = x*K𝒢₁₁y` (bounded letter);
* `hForm y y' = c*𝒢K̂c' = y*𝒢₁₁Ky'` (right weight);
* `omega0 = (z+E) + τ` (`selfTau`);
* `phiSame x y' = Σ_γ s_γ (a*K̂𝒢)_γ (𝒢K̂c')_γ`;
* `phiOpp x x' = Σ_γ s_γ (a*K̂𝒢)_γ conj((a'*K̂𝒢)_γ)` (a dressed word with bounded letters).

**`cov_same_level1`**: `Cov(x*Δy, x'*Δy') = E[Ω₀·F(x,y)·Ψ] + E[F(x',y)·phiSame(x,y')]`.
**`cov_opp_level1`**: `CrossCov(x,y;x',y') = E[Ω₀·F(x,y)·Ψ̄] + E[phiOpp(x,x')·conj H(y,y')]`.
Here `Ψ = x'*Δ⁰y'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `F(x,y) = a*K̂𝒢c = x*K𝒢₁₁y`. -/
def fForm (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  star (physVec x) ⬝ᵥ ((kHat b E X * gRes b E X ω) *ᵥ physVec y)

/-- `H(y,y') = c*𝒢K̂c' = y*𝒢₁₁Ky'`. -/
def hForm (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y y' : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  star (physVec y) ⬝ᵥ (gRes b E X ω *ᵥ (kHat b E X *ᵥ physVec y'))

/-- `Ω₀ = (z+E) + τ`. -/
def omega0 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  (boundaryZ b E + E) + selfTau b (gRes b E X ω)

/-- `Φ = Σ_γ s_γ (a*K̂𝒢)_γ (𝒢K̂c')_γ`. -/
def phiSame (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x y' : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  ∑ γ, physVar W b γ * ((star (physVec x) ᵥ* (kHat b E X * gRes b E X ω)) γ *
    (gRes b E X ω *ᵥ (kHat b E X *ᵥ physVec y')) γ)

/-- `Φ' = Σ_γ s_γ (a*K̂𝒢)_γ conj((a'*K̂𝒢)_γ)`. -/
def phiOpp (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x x' : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  ∑ γ, physVar W b γ * ((star (physVec x) ᵥ* (kHat b E X * gRes b E X ω)) γ *
    star ((star (physVec x') ᵥ* (kHat b E X * gRes b E X ω)) γ))

theorem sum_mul_vecMul (c a : LayerSite W .oneBlockOnePort → ℂ) (M : LayerMat W) :
    ∑ β, c β * (star a ᵥ* M) β = star a ⬝ᵥ (M *ᵥ c) := by
  rw [dotProduct_mulVec, dotProduct_comm]; rfl

theorem sum_mul_star (c h : LayerSite W .oneBlockOnePort → ℂ) :
    ∑ β, c β * star (h β) = star (star c ⬝ᵥ h) := by
  simp only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]

/-- The letter entries are polynomially bounded: `‖(a*K̂𝒢)_γ‖ ≤ ‖a‖B`, `‖(𝒢v)_γ‖ ≤ B‖v‖`. -/
theorem letter_entry_bounds (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) (a v : LayerSite W .oneBlockOnePort → ℂ)
    (γ : LayerSite W .oneBlockOnePort) :
    ‖(star a ᵥ* (kHat b E X * gRes b E X ω)) γ‖ ≤ vecNorm a * (1 + btFun b E X ω) ∧
      ‖(gRes b E X ω *ᵥ v) γ‖ ≤ vecNorm v * (1 + btFun b E X ω) := by
  have hk : ‖kHat b E X * gRes b E X ω‖ ≤ 1 + btFun b E X ω := by
    have := wBound_kHat_le b E X ω
    simp only [wBound] at this
    linarith [norm_nonneg (gRes b E X ω)]
  have hg := norm_gRes_le_one_add b E X ω
  have := PassiveCovariance.vecNorm_nonneg a; have := PassiveCovariance.vecNorm_nonneg v
  constructor
  · exact (norm_vecMul_apply_le a _ γ).trans (by gcongr)
  · exact (norm_mulVec_apply_le _ v γ).trans (by rw [mul_comm]; gcongr)

theorem continuous_letter_entry (Kh : LayerMat W) (a : LayerSite W .oneBlockOnePort → ℂ)
    (γ : LayerSite W .oneBlockOnePort) :
    Continuous fun G : LayerMat W => (star a ᵥ* (Kh * G)) γ :=
  (continuous_apply γ).comp (continuous_const.matrix_vecMul
    (continuous_const.matrix_mul continuous_id))

theorem continuous_mulVec_entry (v : LayerSite W .oneBlockOnePort → ℂ)
    (γ : LayerSite W .oneBlockOnePort) :
    Continuous fun G : LayerMat W => (G *ᵥ v) γ :=
  (continuous_apply γ).comp (continuous_id.matrix_mulVec continuous_const)

/-- Integrability of the triple letter products, bulk-uniform `W₀`. -/
theorem integrable_triple_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ (a a' v : LayerSite W .oneBlockOnePort → ℂ)
      (β γ δ : LayerSite W .oneBlockOnePort),
      Integrable (fun ω => (star a ᵥ* (kHat b E X * gRes b E X ω)) γ *
        ((star a' ᵥ* (kHat b E X * gRes b E X ω)) β * (gRes b E X ω *ᵥ v) δ))
        (layerLaw W b .oneBlockOnePort) ∧
      Integrable (fun ω => (star a ᵥ* (kHat b E X * gRes b E X ω)) γ *
        (star ((star a' ᵥ* (kHat b E X * gRes b E X ω)) β) * star ((gRes b E X ω *ᵥ v) δ)))
        (layerLaw W b .oneBlockOnePort) := by
  obtain ⟨W₀, hi⟩ := LengthUniform.integrable_poly_bulk hA hb0 hb hκ 3
  refine ⟨W₀, fun W hW E hE X hY a a' v β γ δ => ?_⟩
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have m1 := (continuous_letter_entry (kHat b E X) a γ).measurable.comp hGm
  have m2 := (continuous_letter_entry (kHat b E X) a' β).measurable.comp hGm
  have m3 := (continuous_mulVec_entry v δ).measurable.comp hGm
  have hbd : ∀ ω, ‖(star a ᵥ* (kHat b E X * gRes b E X ω)) γ‖ *
      (‖(star a' ᵥ* (kHat b E X * gRes b E X ω)) β‖ * ‖(gRes b E X ω *ᵥ v) δ‖) ≤
      (vecNorm a * vecNorm a' * vecNorm v) * (1 + btFun b E X ω) ^ 3 := fun ω => by
    obtain ⟨e1, -⟩ := letter_entry_bounds b E X ω a v γ
    obtain ⟨e2, e3⟩ := letter_entry_bounds b E X ω a' v β
    obtain ⟨-, e3⟩ := letter_entry_bounds b E X ω a' v δ
    have := PassiveCovariance.vecNorm_nonneg a; have := PassiveCovariance.vecNorm_nonneg a'
    have := PassiveCovariance.vecNorm_nonneg v; have := btFun_nonneg b E X ω
    calc _ ≤ (vecNorm a * (1 + btFun b E X ω)) *
          ((vecNorm a' * (1 + btFun b E X ω)) * (vecNorm v * (1 + btFun b E X ω))) := by
          gcongr
      _ = _ := by ring
  constructor
  · refine hi W hW E hE X hY _ (m1.mul (m2.mul m3)).aestronglyMeasurable
      (vecNorm a * vecNorm a' * vecNorm v) fun ω => ?_
    simp only [norm_mul]; exact hbd ω
  · refine hi W hW E hE X hY _ (m1.mul ((continuous_star.measurable.comp m2).mul
      (continuous_star.measurable.comp m3))).aestronglyMeasurable
      (vecNorm a * vecNorm a' * vecNorm v) fun ω => ?_
    simp only [norm_mul, norm_star]; exact hbd ω

/-- **Level 1, equal signs**: `Cov = E[Ω₀FΨ] + E[F(x',y)·Φ]`. -/
theorem cov_same_level1 (hA : PassiveBoundsStatement) (hGA : GaussianAbsorptionContract)
    {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ x y x' y' : Fin W → ℂ,
      bilinearCovariance (freshLaw W b) (freshDelta b E X) x y x' y' =
        ∫ ω, omega0 b E X ω * fForm b E X x y ω *
            bilinear x' (freshDelta b E X ω - matrixExpect (freshLaw W b) (freshDelta b E X)) y'
          ∂freshLaw W b +
        ∫ ω, fForm b E X x' y ω * phiSame b E X x y' ω ∂freshLaw W b := by
  obtain ⟨W₁, h0⟩ := cov_same_level0 hA hGA hb0 hb hκ
  obtain ⟨W₂, hi⟩ := integrable_triple_bulk hA hb0 hb hκ
  refine ⟨max W₁ W₂, fun W hW E hE X hY x y x' y' => ?_⟩
  rw [h0 W (le_of_max_le_left hW) E hE X hY x y x' y',
    crossed_same_sum b (physVec y) (physVec_port y) _ _ _ fun β γ =>
      (hi W (le_of_max_le_right hW) E hE X hY.posSemidef _ _ _ β γ γ).1]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [phiSame, fForm]
  rw [sum_mul_vecMul]

/-- **Level 1, opposite signs**: `CrossCov = E[Ω₀FΨ̄] + E[Φ'·conj H]`. -/
theorem cov_opp_level1 (hA : PassiveBoundsStatement) (hGA : GaussianAbsorptionContract)
    {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ x y x' y' : Fin W → ℂ,
      bilinearCrossCovariance (freshLaw W b) (freshDelta b E X) x y x' y' =
        ∫ ω, omega0 b E X ω * fForm b E X x y ω *
            star (bilinear x' (freshDelta b E X ω -
              matrixExpect (freshLaw W b) (freshDelta b E X)) y') ∂freshLaw W b +
        ∫ ω, phiOpp b E X x x' ω * star (hForm b E X y y' ω) ∂freshLaw W b := by
  obtain ⟨W₁, h0⟩ := cov_opp_level0 hA hGA hb0 hb hκ
  obtain ⟨W₂, hi⟩ := integrable_triple_bulk hA hb0 hb hκ
  refine ⟨max W₁ W₂, fun W hW E hE X hY x y x' y' => ?_⟩
  rw [h0 W (le_of_max_le_left hW) E hE X hY x y x' y',
    crossed_opp_sum b (physVec y) (physVec_port y) _ _ _ fun β γ =>
      (hi W (le_of_max_le_right hW) E hE X hY.posSemidef _ _ _ γ γ β).2]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [phiOpp, hForm]
  rw [sum_mul_star]

end BlockBand.SourceProcess.FullSourceCovariance
