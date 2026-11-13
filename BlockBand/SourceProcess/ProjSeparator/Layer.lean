module

public import BlockBand.SourceProcess.ProjSeparator.Bounds
public import BlockBand.SourceProcess.ContractingWords.WardRefined
public import BlockBand.SourceProcess.FullSourceCovariance.DeltaFlucAll
public import BlockBand.SourceProcess.FullSourceCovariance.CrossedSameHolds

/-!
# One fresh layer: the inputs on `Δ` and the projected separator as a quadratic form

Measure `freshLaw W b`; `X` passive (`passiveY X ⪰ 0`), `Δ = freshDelta b E X`, `M = EΔ`.

* `delta_inputs hGA hLp`: `C₂, C₄, C_M, W₀` from `b, κ`, for `W ≥ W₀`, `E ∈ bulkInterval κ`, passive `X`:
  integrable entries, `‖x*Δ⁰y‖_{L²} ≤ C₂W^{-1/2}‖x‖‖y‖`, `‖x*Δ⁰y‖_{L⁴} ≤ C₄W^{-1/2}‖x‖‖y‖`
  (`deltaFluctuation_all`), `‖M‖ ≤ C_M(δ₀ + W⁻²)` (`deltaMean_all`);
* `deltaCovarianceOpposite_holds hGA hLp hP`: `DeltaCovarianceOpposite` from the contract
  hypotheses;
* `bilinear_projGamma`: `u*projGamma v = (ιu)*(ΔQ(ΔQ)*)(ιv)`, `Q = ℝ₁₂`;
* `projGamma_mean`: integrable entries of `projGamma` and
  `u*(E projGamma)v = (ιu)*(MQ(MQ)*)(ιv) + Σ_j crossCov(ιu, q_j, ιv, q_j)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ProjSeparator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSourceCovariance BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance BlockBand.SourceProcess.ContractingWords
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The opposite-sign `Δ`-covariance `DeltaCovarianceOpposite`, from the contract hypotheses. -/
theorem deltaCovarianceOpposite_holds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) : DeltaCovarianceOpposite :=
  deltaCovarianceOpposite_of_onDomain hGA hLp (deltaCovarianceOppositeOnDomain_of_strict hGA
    (deltaCovarianceOppositeOnDomainStrict_of (BlockBand.Transmission.PassiveLayer.passiveBounds_holds
      hGA hLp) hGA (firstTermBound_holds hGA hLp)
      (crossedOppBound_of_mean hGA hLp hP (phiOppMean_holds hGA hLp))))

theorem eLpNorm_delta_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (p : ℕ) (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ x y : Fin W → ℂ,
        eLpNorm (fun ω => bilinear x (freshDelta b E X ω -
            matrixExpect (freshLaw W b) (freshDelta b E X)) y) (p : ℝ≥0∞) (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm x * vecNorm y) := by
  obtain ⟨C, W₀, h⟩ := deltaFluctuation_all hGA hLp b hb0 hb κ hκ p (by exact_mod_cast hp)
  refine ⟨max C 0, W₀, le_max_right _ _, fun W hW E hE X hY x y => ?_⟩
  have h' := h W hW E hE X hY x y
  rw [ENNReal.ofReal_natCast] at h'
  refine h'.trans (ENNReal.ofReal_le_ofReal ?_)
  have := vecNorm_nonneg x; have := vecNorm_nonneg y
  gcongr; exact le_max_left _ _

/-- **The `Δ` inputs at one fresh layer.** -/
theorem delta_inputs (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (C₂ C₄ CM : ℝ) (W₀ : ℕ), 0 ≤ C₂ ∧ 0 ≤ C₄ ∧ 0 ≤ CM ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        (∀ i j, Integrable (fun ω => freshDelta b E X ω i j) (freshLaw W b)) ∧
        (∀ x y : Fin W → ℂ, eLpNorm (fun ω => bilinear x (freshDelta b E X ω -
            matrixExpect (freshLaw W b) (freshDelta b E X)) y) 2 (freshLaw W b) ≤
          ENNReal.ofReal (C₂ / Real.sqrt W * vecNorm x * vecNorm y)) ∧
        (∀ x y : Fin W → ℂ, eLpNorm (fun ω => bilinear x (freshDelta b E X ω -
            matrixExpect (freshLaw W b) (freshDelta b E X)) y) 4 (freshLaw W b) ≤
          ENNReal.ofReal (C₄ / Real.sqrt W * vecNorm x * vecNorm y)) ∧
        ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ ≤
          CM * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
  obtain ⟨C₂, W₂, hC₂, h2⟩ := eLpNorm_delta_le hGA hLp hb0 hb hκ 2 (by norm_num)
  obtain ⟨C₄, W₄, hC₄, h4⟩ := eLpNorm_delta_le hGA hLp hb0 hb hκ 4 (by norm_num)
  obtain ⟨CM, WM, hCM, hM⟩ := deltaMean_all hGA hLp b hb0 hb κ hκ
  obtain ⟨CI, WI, -, hI⟩ := FullSource.delta_integrable hGA b hb0 hb κ hκ
  refine ⟨C₂, C₄, CM, max (max W₂ W₄) (max WM WI), hC₂, hC₄, hCM,
    fun W hW E hE X hY => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW2, hW4⟩, hWM, hWI⟩ := hW
  refine ⟨(hI W hWI E hE X hY).1, fun x y => ?_, fun x y => ?_, hM W hWM E hE X hY⟩
  · simpa using h2 W hW2 E hE X hY x y
  · simpa using h4 W hW4 E hE X hY x y

/-- `u*projGamma v = (ιu)*(ΔQ(ΔQ)*)(ιv)`. -/
theorem bilinear_projGamma (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (y : LayerSample W .oneBlockOnePort) (u v : Fin 2 × Fin W → ℂ) :
    bilinear u (projGamma b E XX y) v =
      bilinear (nearSel W *ᵥ u) (freshDelta b E (nearSchur (boundaryZ b E) XX) y * farQ b E XX *
        (freshDelta b E (nearSchur (boundaryZ b E) XX) y * farQ b E XX)ᴴ) (nearSel W *ᵥ v) := by
  rw [projGamma_eq, Matrix.mul_assoc, FullSource.bilinear_sandwich']

/-- `u*Pv = (ιu)*(ιv)`. -/
theorem bilinear_nearProjection (u v : Fin 2 × Fin W → ℂ) :
    bilinear u (nearProjection W) v = bilinear (nearSel W *ᵥ u) 1 (nearSel W *ᵥ v) := by
  rw [← nearSel_conj_mul_nearSel, ← FullSource.bilinear_sandwich', Matrix.one_mul]

/-- **The mean of the projected separator as a quadratic form.** -/
theorem projGamma_mean {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hD : ∀ i j, Integrable (fun ω => freshDelta b E (nearSchur (boundaryZ b E) XX) ω i j)
      (freshLaw W b))
    (h2 : ∀ x y, MemLp (fun ω => bilinear x (freshDelta b E (nearSchur (boundaryZ b E) XX) ω -
      matrixExpect (freshLaw W b) (freshDelta b E (nearSchur (boundaryZ b E) XX))) y) 2
      (freshLaw W b)) :
    (∀ i j, Integrable (fun ω => projGamma b E XX ω i j) (freshLaw W b)) ∧
      ∀ u v : Fin 2 × Fin W → ℂ,
        bilinear u (matrixExpect (freshLaw W b) (projGamma b E XX)) v =
          ∫ ω, bilinear u (projGamma b E XX ω) v ∂freshLaw W b ∧
        ∫ ω, bilinear u (projGamma b E XX ω) v ∂freshLaw W b =
          bilinear (nearSel W *ᵥ u) (matrixExpect (freshLaw W b)
              (freshDelta b E (nearSchur (boundaryZ b E) XX)) * farQ b E XX *
            (matrixExpect (freshLaw W b) (freshDelta b E (nearSchur (boundaryZ b E) XX)) *
              farQ b E XX)ᴴ) (nearSel W *ᵥ v) +
          ∑ j, bilinearCrossCovariance (freshLaw W b) (freshDelta b E (nearSchur (boundaryZ b E) XX))
            (nearSel W *ᵥ u) (colQ (farQ b E XX) j) (nearSel W *ᵥ v) (colQ (farQ b E XX) j) := by
  have hG := fun u v => integral_bilinear_gamma _ (farQ b E XX) hD h2
    (nearSel W *ᵥ u) (nearSel W *ᵥ v)
  have hint : ∀ u v, Integrable (fun ω => bilinear u (projGamma b E XX ω) v) (freshLaw W b) := by
    intro u v
    simp only [bilinear_projGamma]
    exact (hG u v).1
  have hent : ∀ i j, Integrable (fun ω => projGamma b E XX ω i j) (freshLaw W b) := by
    intro i j
    simp only [fun ω => FullSource.entry_eq_bilinear (projGamma b E XX ω) i j]
    exact hint _ _
  refine ⟨hent, fun u v => ⟨bilinear_matrixExpect _ u v hent, ?_⟩⟩
  simp only [bilinear_projGamma]
  exact (hG u v).2

end BlockBand.SourceProcess.ProjSeparator
