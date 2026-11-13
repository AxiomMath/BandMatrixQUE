module

public import BlockBand.SourceProcess.FullSource.DeltaReduction
public import BlockBand.SourceProcess.FullSource.SqClock
public import BlockBand.SourceProcess.FullSource.Main

/-!
# Assembly of `FullSourceEstimates`

* `mean_of_delta hGA hΔm`: the field `mean`, from `DeltaMean` (scalar domain) and, off the
  domain, `‖EΔ‖ ≤ C` (`delta_integrable`);
* `fluct_of_delta hGA hΔf`: the field `fluct` (same `d₀`), from `DeltaFluctuation`;
* `fullSourceMoments_field_holds hGA`: the field `moments`, **proved** from
  `GaussianAbsorptionContract` only;
* `fullSourceEstimates_of_delta`, and `FullSourceMomentsContract`,
  `EdgeClockMomentsContract` (and `ClockSquareBulk`) from the Gaussian inputs plus the two open
  one-port nodes `DeltaFluctuation`, `DeltaMean`.

Every step uses the a.s. Ward identity `𝓔 = ι(ΔF) + (ΔF)*ι*` (`ward_full`), so
`E𝓔 = ι(EΔ·F) + (EΔ·F)*ι*` and `u*(𝓔 - E𝓔)v = (ι*u)*Δ⁰(Fv) + conj((ι*v)*Δ⁰(Fu))`, `‖F‖ ≤ 3/(2η)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.Inputs
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

theorem matrixExpect_congr_ae' {Ω n : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A B : Ω → Matrix n n ℂ} (h : ∀ᵐ ω ∂μ, A ω = B ω) : matrixExpect μ A = matrixExpect μ B := by
  ext x y
  exact integral_congr_ae (h.mono fun ω hω => congrFun (congrFun hω x) y)

/-- Common setup: `η ≥ η₀`, `X` passive, `‖F‖ ≤ C_F`, `E𝓔 = ι(EΔ·F) + (EΔ·F)*ι*`. -/
theorem ward_setup {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) (hW : 1 ≤ W) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian)
    (hent : (passiveY (nearSchur (boundaryZ b E) XX)).PosSemidef → ∀ x y, Integrable
      (fun ω => freshDelta b E (nearSchur (boundaryZ b E) XX) ω x y) (freshLaw W b)) :
    0 < etaZ b E ∧ (passiveY (nearSchur (boundaryZ b E) XX)).PosSemidef ∧
      ‖wardF b E XX‖ ≤ ((1 - b) * κ / 4)⁻¹ + (2 * ((1 - b) * κ / 4))⁻¹ ∧
      matrixExpect (freshLaw W b) (wardNoise b E XX) =
        wardOf (matrixExpect (freshLaw W b) (freshDelta b E (nearSchur (boundaryZ b E) XX)))
          (wardF b E XX) := by
  have hη₀ : 0 < (1 - b) * κ / 4 := by have : 0 < 1 - b := by linarith
                                       positivity
  have hge := etaZ_ge hb0 hb hκ hE
  have hη : 0 < etaZ b E := lt_of_lt_of_le hη₀ hge
  have hY := nearSchur_passive hη hXX
  refine ⟨hη, hY, (norm_wardF_le b E hXX hη).trans (add_le_add (inv_anti₀ hη₀ hge)
    (inv_anti₀ (by positivity) (by linarith))), ?_⟩
  rw [matrixExpect_congr_ae' (ward_ae hb0 hXX hη hW)]
  exact matrixExpect_wardOf _ (hent hY) _

/-- **`FullSourceEstimates.mean`** from `DeltaMean`. -/
theorem mean_of_delta (hGA : GaussianAbsorptionContract) (hΔ : DeltaMean) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        ‖matrixExpect (freshLaw W b) (wardNoise b E XX)‖ ≤
          C * (jetDistance0 b E (nearSchur (boundaryZ b E) XX) + ((W : ℝ)⁻¹) ^ 2) := by
  intro b hb0 hb κ hκ
  obtain ⟨d₀, hd₀, C, W₀, hC⟩ := hΔ b hb0 hb κ hκ
  obtain ⟨CI, W₁, hCI, hI⟩ := delta_integrable hGA b hb0 hb κ hκ
  set CF := ((1 - b) * κ / 4)⁻¹ + (2 * ((1 - b) * κ / 4))⁻¹
  have hCF : 0 ≤ CF := by
    have : 0 < (1 - b) * κ / 4 := by have : 0 < 1 - b := by linarith
                                     positivity
    positivity
  refine ⟨2 * CF * (max C 0 + CI / d₀), max (max W₀ W₁) 1, fun W hW E hE XX hXX => ?_⟩
  have hW0 : W₀ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW1 : W₁ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW2 : 1 ≤ W := (le_max_right _ _).trans hW
  set X := nearSchur (boundaryZ b E) XX
  obtain ⟨-, hY, hF, hEw⟩ := ward_setup hb0 hb hκ hE hW2 hXX
    (fun hY => (hI W hW1 E hE X hY).1)
  rw [hEw]
  refine (norm_wardOf_le _ _).trans ?_
  set δ := jetDistance0 b E X
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hw0 : 0 ≤ ((W : ℝ)⁻¹) ^ 2 := by positivity
  have hEΔ := (hI W hW1 E hE X hY).2
  have key : ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ ≤
      (max C 0 + CI / d₀) * (δ + ((W : ℝ)⁻¹) ^ 2) := by
    by_cases hd : δ ≤ d₀
    · refine (hC W hW0 E hE X hY hd).trans ?_
      have := mul_le_mul_of_nonneg_right (le_max_left C 0) (add_nonneg hδ0 hw0)
      have : 0 ≤ CI / d₀ * (δ + ((W : ℝ)⁻¹) ^ 2) := by positivity
      nlinarith
    · replace hd := not_le.mp hd
      have h1 : CI ≤ CI / d₀ * δ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hd₀]
        exact mul_le_mul_of_nonneg_left hd.le hCI
      have : 0 ≤ max C 0 * (δ + ((W : ℝ)⁻¹) ^ 2) :=
        mul_nonneg (le_max_right _ _) (add_nonneg hδ0 hw0)
      have : CI / d₀ * δ ≤ CI / d₀ * (δ + ((W : ℝ)⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
  have hpos : 0 ≤ (max C 0 + CI / d₀) * (δ + ((W : ℝ)⁻¹) ^ 2) :=
    mul_nonneg (add_nonneg (le_max_right _ _) (by positivity)) (add_nonneg hδ0 hw0)
  calc 2 * (‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ * ‖wardF b E XX‖)
      ≤ 2 * ((max C 0 + CI / d₀) * (δ + ((W : ℝ)⁻¹) ^ 2) * CF) := by
        gcongr
    _ = 2 * CF * (max C 0 + CI / d₀) * (δ + ((W : ℝ)⁻¹) ^ 2) := by ring

/-- **`FullSourceEstimates.fluct`** from `DeltaFluctuation` (the same scalar domain `d₀`). -/
theorem fluct_of_delta (hGA : GaussianAbsorptionContract) (hΔ : DeltaFluctuation) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      jetDistance0 b E (nearSchur (boundaryZ b E) XX) ≤ d₀ → ∀ u v : Fin 2 × Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (wardNoise b E XX ω -
            matrixExpect (freshLaw W b) (wardNoise b E XX)) v) (ENNReal.ofReal p)
            (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) := by
  intro b hb0 hb κ hκ
  obtain ⟨d₀, hd₀, hΔp⟩ := hΔ b hb0 hb κ hκ
  refine ⟨d₀, hd₀, fun p hp => ?_⟩
  obtain ⟨C, W₀, hC⟩ := hΔp p hp
  obtain ⟨CI, W₁, -, hI⟩ := delta_integrable hGA b hb0 hb κ hκ
  set CF := ((1 - b) * κ / 4)⁻¹ + (2 * ((1 - b) * κ / 4))⁻¹
  have hCF : 0 ≤ CF := by
    have : 0 < (1 - b) * κ / 4 := by have : 0 < 1 - b := by linarith
                                     positivity
    positivity
  set C' := max C 0
  refine ⟨2 * C' * CF, max (max W₀ W₁) 1, fun W hW E hE XX hXX hδ u v => ?_⟩
  have hW0 : W₀ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW1 : W₁ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW2 : 1 ≤ W := (le_max_right _ _).trans hW
  set X := nearSchur (boundaryZ b E) XX
  set μ := freshLaw W b
  obtain ⟨hη, hY, hF, hEw⟩ := ward_setup hb0 hb hκ hE hW2 hXX
    (fun hY => (hI W hW1 E hE X hY).1)
  set Δ0 : LayerSample W .oneBlockOnePort → Matrix (Fin W) (Fin W) ℂ :=
    fun ω => freshDelta b E X ω - matrixExpect μ (freshDelta b E X)
  set F := wardF b E XX
  have hae : ∀ᵐ ω ∂μ, bilinear u (wardNoise b E XX ω - matrixExpect μ (wardNoise b E XX)) v =
      bilinear (nearSel W *ᵥ u) (Δ0 ω) (F *ᵥ v) +
        star (bilinear (nearSel W *ᵥ v) (Δ0 ω) (F *ᵥ u)) := by
    filter_upwards [ward_ae hb0 hXX hη hW2] with ω hω
    rw [hω, hEw, wardOf_sub, wardOf, bilinear_ward]
  rw [eLpNorm_congr_ae hae]
  refine (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hp)).trans ?_
  have hstar : eLpNorm (fun ω => star (bilinear (nearSel W *ᵥ v) (Δ0 ω) (F *ᵥ u)))
      (ENNReal.ofReal p) μ = eLpNorm (fun ω => bilinear (nearSel W *ᵥ v) (Δ0 ω) (F *ᵥ u))
      (ENNReal.ofReal p) μ := eLpNorm_star
  rw [hstar]
  have h1 := hC W hW0 E hE X hY hδ (nearSel W *ᵥ u) (F *ᵥ v)
  have h2 := hC W hW0 E hE X hY hδ (nearSel W *ᵥ v) (F *ᵥ u)
  have hb1 : ∀ a c : Fin 2 × Fin W → ℂ, C / Real.sqrt W * vecNorm (nearSel W *ᵥ a) *
      vecNorm (F *ᵥ c) ≤ C' * CF / Real.sqrt W * vecNorm a * vecNorm c := by
    intro a c
    have ha := vecNorm_nearSel_mulVec_le a
    have hc : vecNorm (F *ᵥ c) ≤ CF * vecNorm c :=
      (vecNorm_mulVec_le' F c).trans (mul_le_mul_of_nonneg_right hF (vecNorm_nonneg c))
    have hC' : C / Real.sqrt W ≤ C' / Real.sqrt W :=
      div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    have hC'0 : 0 ≤ C' / Real.sqrt W := div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)
    calc C / Real.sqrt W * vecNorm (nearSel W *ᵥ a) * vecNorm (F *ᵥ c)
        ≤ C' / Real.sqrt W * vecNorm a * (CF * vecNorm c) :=
          mul_le_mul (mul_le_mul hC' ha (vecNorm_nonneg _) hC'0) hc (vecNorm_nonneg _)
            (mul_nonneg hC'0 (vecNorm_nonneg _))
      _ = C' * CF / Real.sqrt W * vecNorm a * vecNorm c := by ring
  have hX0 : 0 ≤ C' * CF / Real.sqrt W * vecNorm u * vecNorm v := by
    have := vecNorm_nonneg u; have := vecNorm_nonneg v
    have : 0 ≤ C' := le_max_right _ _
    positivity
  calc eLpNorm (fun ω => bilinear (nearSel W *ᵥ u) (Δ0 ω) (F *ᵥ v)) (ENNReal.ofReal p) μ +
        eLpNorm (fun ω => bilinear (nearSel W *ᵥ v) (Δ0 ω) (F *ᵥ u)) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (C' * CF / Real.sqrt W * vecNorm u * vecNorm v) +
          ENNReal.ofReal (C' * CF / Real.sqrt W * vecNorm u * vecNorm v) := by
        refine add_le_add (h1.trans (ENNReal.ofReal_le_ofReal (hb1 u v)))
          (h2.trans (ENNReal.ofReal_le_ofReal ((hb1 v u).trans (le_of_eq (by ring)))))
    _ = ENNReal.ofReal (2 * C' * CF / Real.sqrt W * vecNorm u * vecNorm v) := by
        rw [← ENNReal.ofReal_add hX0 hX0]; congr 1; ring

/-- **`FullSourceEstimates`** from `GaussianAbsorptionContract` and the two open
one-port nodes on `Δ`. -/
theorem fullSourceEstimates_of_delta (hGA : GaussianAbsorptionContract)
    (hΔf : DeltaFluctuation) (hΔm : DeltaMean) : FullSourceEstimates :=
  ⟨mean_of_delta hGA hΔm, fluct_of_delta hGA hΔf, fullSourceMoments_field_holds hGA⟩

/-- `FullSourceMomentsContract` from the Gaussian inputs and the
open nodes `DeltaFluctuation`, `DeltaMean`. -/
theorem fullSourceMoments_of_delta (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hΔf : DeltaFluctuation) (hΔm : DeltaMean) :
    FullSourceMomentsContract :=
  fullSourceMoments_of_estimates (fullSourceEstimates_of_delta hGA hΔf hΔm) hGA hLp hSR

/-- `EdgeClockMomentsContract`, from the same hypotheses. -/
theorem edgeClockMoments_of_delta (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hΔf : DeltaFluctuation) (hΔm : DeltaMean) :
    EdgeClockMomentsContract :=
  edgeClockMoments_holds (fullSourceEstimates_of_delta hGA hΔf hΔm) hGA hLp hSR

/-- `ClockSquareBulk`, same hypotheses. -/
theorem clockSquareBulk_of_delta (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hΔf : DeltaFluctuation) (hΔm : DeltaMean) :
    ClockSquareBulk :=
  clockSquareBulk_holds (fullSourceEstimates_of_delta hGA hΔf hΔm) hGA hLp hSR

end BlockBand.SourceProcess.FullSource
