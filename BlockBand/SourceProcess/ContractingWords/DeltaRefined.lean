module

public import BlockBand.SourceProcess.ContractingWords.DeltaRefinedStrict
public import BlockBand.SourceProcess.FullSource.DeltaMeanHolds

/-!
# The refined mean `EΔ = ⟨EΔ⟩·I + O(δ₀² + W⁻²)` for every passive input

**`deltaMean_refined hGA hLp`**: for `b, κ` there are `C, W₀` such that for `W ≥ W₀`,
`E ∈ bulkInterval κ` and every passive `X` (`passiveY X ⪰ 0`),
`‖EΔ - ⟨EΔ⟩·I‖ ≤ C(δ₀(X)² + W⁻²)`, `⟨M⟩ = W⁻¹Tr M`, operator norm, `freshLaw W b`.
* On `δ₀ ≤ d₁/2`: `deltaMean_strict_refined` along the regularization `X_n = X - i(n+1)⁻¹`, as in
  `deltaMean_holds` (Vitali for `EΔ(X_n) → EΔ(X)`), through the continuous functional
  `M ↦ ‖M - ⟨M⟩I‖ ≤ 2‖M - ΩI‖` (`norm_sub_avg_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSource BlockBand.Transmission
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The normalized trace `⟨M⟩ = W⁻¹ Tr M`. -/
def avgTr (M : Matrix (Fin W) (Fin W) ℂ) : ℂ := (W : ℂ)⁻¹ * M.trace

theorem norm_avgTr_le (hW : 1 ≤ W) (M : Matrix (Fin W) (Fin W) ℂ) : ‖avgTr M‖ ≤ ‖M‖ := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have htr : ‖M.trace‖ ≤ W * ‖M‖ := by
    unfold Matrix.trace Matrix.diag
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖M i i‖ ≤ ∑ _i : Fin W, ‖M‖ := Finset.sum_le_sum fun i _ => norm_entry_le_op M i i
      _ = W * ‖M‖ := by simp
  rw [avgTr, norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖M.trace‖ ≤ (W : ℝ)⁻¹ * (W * ‖M‖) :=
        mul_le_mul_of_nonneg_left htr (by positivity)
    _ = ‖M‖ := by field_simp

theorem avgTr_sub_smul (hW : 1 ≤ W) (M : Matrix (Fin W) (Fin W) ℂ) (Ω : ℂ) :
    avgTr (M - Ω • 1) = avgTr M - Ω := by
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
  simp only [avgTr, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul]
  field_simp

/-- `‖M - ⟨M⟩I‖ ≤ 2‖M - ΩI‖` for every `Ω`. -/
theorem norm_sub_avg_le (hW : 1 ≤ W) (M : Matrix (Fin W) (Fin W) ℂ) (Ω : ℂ) :
    ‖M - avgTr M • 1‖ ≤ 2 * ‖M - Ω • 1‖ := by
  have e : M - avgTr M • 1 = (M - Ω • 1) - (avgTr M - Ω) • 1 := by
    rw [sub_smul]; abel
  have h1 : ‖avgTr M - Ω‖ ≤ ‖M - Ω • 1‖ := by
    rw [← avgTr_sub_smul hW]; exact norm_avgTr_le hW _
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul]
  have := PassiveCovariance.norm_one_matrix_le (n := Fin W)
  nlinarith [norm_nonneg (avgTr M - Ω), norm_nonneg (M - Ω • 1)]

theorem continuous_avgTr : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => avgTr M := by
  have ht : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => M.trace :=
    Continuous.matrix_trace continuous_id
  exact continuous_const.mul ht

theorem continuous_devAvg : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => ‖M - avgTr M • 1‖ :=
  (continuous_id.sub (continuous_avgTr.smul continuous_const)).norm

/-- **The refined mean of `Δ`** for every passive input. -/
theorem deltaMean_refined (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        ‖matrixExpect (freshLaw W b) (freshDelta b E X) -
            avgTr (matrixExpect (freshLaw W b) (freshDelta b E X)) • 1‖ ≤
          C * (jetDistance0 b E X ^ 2 + ((W : ℝ)⁻¹) ^ 2) := by
  intro b hb0 hb κ hκ
  have hA := PassiveLayer.passiveBounds_holds hGA hLp
  obtain ⟨d₁, C, W₀, hd₁, hC, hstrict⟩ := deltaMean_strict_refined hA hb0 hb hκ
  obtain ⟨C2, W₂, hC2, hmom⟩ := delta_moments hGA b hb0 hb κ hκ 2 (by norm_num)
  obtain ⟨_, W₃, hdet⟩ := PassiveLayer.moments_holds hGA b hb0 hb κ hκ 1 le_rfl
  obtain ⟨CI, W₄, hCI, hI⟩ := delta_integrable hGA b hb0 hb κ hκ
  refine ⟨2 * C + 2 * CI * (2 / d₁) ^ 2, max (max (max W₀ W₂) (max W₃ W₄)) 1, by positivity,
    fun W hW E hE X hY => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW0, hW2⟩, hW3, hW4⟩, hW1⟩ := hW
  set δ := jetDistance0 b E X
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hw0 : 0 ≤ ((W : ℝ)⁻¹) ^ 2 := by positivity
  by_cases hd : δ ≤ d₁ / 2
  · obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
    set μ := freshLaw W b
    set Xn := fun n : ℕ => PassiveCovariance.regX X n
    have hj := PassiveCovariance.tendsto_jet0_regX hb0 hb h1 h2 hY
    have hev : ∀ᶠ n in atTop, jetDistance0 b E (Xn n) ≤ d₁ :=
      hj.eventually (ge_mem_nhds (by linarith))
    have hmeas : ∀ (Y : Matrix (Fin W) (Fin W) ℂ), Measurable fun ω => freshDelta b E Y ω :=
      fun Y => measurable_freshDelta_comp b E (X := fun _ => Y) measurable_const measurable_id
    have hL2 : ∀ (Y : Matrix (Fin W) (Fin W) ℂ), (passiveY Y).PosSemidef → ∀ i j,
        eLpNorm (fun ω => freshDelta b E Y ω i j) 2 μ ≤ ENNReal.ofReal C2 := by
      intro Y hY' i j
      have hm := (hmom W hW2 E hE Y hY').2
      rw [show ENNReal.ofReal 2 = 2 by simp] at hm
      exact (eLpNorm_mono_ae_real (hmeas Y).eval_matrix.aestronglyMeasurable
        (ae_of_all _ fun ω => norm_entry_le_op _ i j)).trans hm
    have hdetX := (hdet W hW3 E hE (boundaryZ b E)
      (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hY).1
    have hent : ∀ i j, Tendsto (fun n => ∫ ω, freshDelta b E (Xn n) ω i j ∂μ) atTop
        (𝓝 (∫ ω, freshDelta b E X ω i j ∂μ)) := by
      intro i j
      refine PassiveCovariance.tendsto_integral_of_ae_of_eLpNorm_two
        (fun n => (hmeas (Xn n)).eval_matrix) ENNReal.ofReal_ne_top
        (fun n => hL2 _ (PassiveCovariance.passiveY_regX_posSemidef hY n) i j) (hL2 X hY i j) ?_
      filter_upwards [hdetX] with ω hω
      exact (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 (tendsto_freshDelta_regX b E X ω hω) i) j)
    have hM : Tendsto (fun n => matrixExpect μ (freshDelta b E (Xn n))) atTop
        (𝓝 (matrixExpect μ (freshDelta b E X))) :=
      tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hent i j
    have hR := ((hj.pow 2).add_const (((W : ℝ)⁻¹) ^ 2)).const_mul (2 * C)
    have hlim := le_of_tendsto_of_tendsto ((continuous_devAvg.tendsto _).comp hM) hR
      (hev.mono fun n hn => by
        obtain ⟨Ω, hΩ⟩ := hstrict W hW0 E hE (Xn n)
          (PassiveCovariance.passiveY_regX_posDef hY n) hn
        refine (norm_sub_avg_le hW1 _ Ω).trans ?_
        linarith)
    refine hlim.trans ?_
    have : 0 ≤ 2 * CI * (2 / d₁) ^ 2 * (δ ^ 2 + ((W : ℝ)⁻¹) ^ 2) := by positivity
    nlinarith
  · have hd' : d₁ / 2 < δ := not_le.mp hd
    have h0 := norm_sub_avg_le hW1 (matrixExpect (freshLaw W b) (freshDelta b E X)) 0
    rw [zero_smul, sub_zero] at h0
    have hEΔ := (hI W hW4 E hE X hY).2
    have hq : 1 ≤ (2 / d₁) ^ 2 * δ ^ 2 := by
      rw [← mul_pow]
      have : 1 ≤ 2 / d₁ * δ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hd₁]; linarith
      nlinarith
    have : 0 ≤ 2 * C * (δ ^ 2 + ((W : ℝ)⁻¹) ^ 2) := by positivity
    have : 2 * CI ≤ 2 * CI * ((2 / d₁) ^ 2 * δ ^ 2) := le_mul_of_one_le_right (by positivity) hq
    have : 2 * CI * ((2 / d₁) ^ 2 * δ ^ 2) ≤ 2 * CI * (2 / d₁) ^ 2 * (δ ^ 2 + ((W : ℝ)⁻¹) ^ 2) := by
      have : 0 ≤ 2 * CI * (2 / d₁) ^ 2 := by positivity
      nlinarith
    nlinarith

end BlockBand.SourceProcess.ContractingWords
