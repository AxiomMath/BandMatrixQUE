module

public import BlockBand.Transmission.PassiveLayer.TMCore
public import BlockBand.Transmission.PassiveLayer.Assembly

/-!
# The `traceMatrix` clause of the passive bounds lemma, and the assembled lemma

Law `freshLaw W b` (conditional on the deterministic passive `X`); operator norm; uniform in
`W ≥ W₀`, `E ∈ bulkInterval κ`, `w ∈ paramDisk b E`, passive `X`, word lengths `≤ Lw` and insertions
`‖D_j‖ ≤ K_d`.

`traceMatrix_holds` proves the `traceMatrix` clause from `GaussianAbsorptionContract`, and
`passiveBounds_holds` assembles `PassiveBoundsStatement` from `GaussianAbsorptionContract` and
`GaussianLpGradient`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory ProbabilityTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

/-- The moment weight `lbar` has the `L^p` moments of `moments`. -/
theorem lbar_momBd {b : ℝ} {E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ} {p C : ℝ}
    (hp : 1 ≤ p)
    (h : eLpNorm (fun ω => ‖layerAt E w X ω‖) (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal C ∧
      eLpNorm (fun ω => ‖kG11 E w X ω‖) (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal C ∧
      eLpNorm (fun ω => ‖lAt E w X ω‖) (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal C) :
    eLpNorm (lbar E w X) (ENNReal.ofReal p) (freshLaw W b) ≤
      ENNReal.ofReal (1 + 3 * max C 0) := by
  obtain ⟨hg, hk, hl⟩ := letter_momBd h
  have h0 := MomBd.const (μ := freshLaw W b) 1 p (by linarith)
  have hC := le_max_right C 0
  have h1 := (((h0.add hp hg (abs_nonneg _) hC).add hp hk (by positivity) hC).add hp hl
    (by positivity) hC)
  have e : (|(1 : ℝ)| + max C 0 + max C 0 + max C 0) = 1 + 3 * max C 0 := by
    rw [abs_one]; ring
  rw [e] at h1
  exact h1.2

/-- **The `traceMatrix` clause of the passive bounds lemma**, from `GaussianAbsorptionContract`
(explicit hypothesis). -/
theorem traceMatrix_holds (hGA : GaussianAbsorptionContract) : TraceMatrixClause := by
  intro b hb0 hb κ hκ Lw Kd
  set N := 2 * Lw + 2 with hNdef
  have hN4 : (1 : ℝ) ≤ 4 * N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    linarith
  obtain ⟨C', W₀m, hm⟩ := moments_holds hGA b hb0 hb κ hκ (4 * N) hN4
  set Cm := 1 + 3 * max C' 0 with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  set K₁ := max Kd 1 with hK₁
  refine ⟨6 * (Lw : ℝ) * Lw * K₁ ^ N * Cm ^ N, max W₀m 1, ?_⟩
  intro W hW E hE w hw X hY ℓf ℓU hℓf hℓU wf Df wU DU hDf hDU μ f U
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hWm : W₀m ≤ W := le_of_max_le_left hW
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hDf 0)
  obtain ⟨hwim, -, -, -⟩ := disk_bounds hb0 hb hκ hE hw
  have hwpos : 0 < w.im := lt_of_lt_of_le (by have : 0 < 1 - b := by linarith
                                              positivity) hwim
  have hinv : ∀ᵐ ω ∂freshLaw W b, IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω) := by
    filter_upwards [(hm W hWm E hE w hw X hY).1] with ω hω
    exact (Matrix.isUnit_iff_isUnit_det _).mpr hω
  have hmom : ∀ X' : Matrix (Fin W) (Fin W) ℂ, (passiveY X').PosSemidef →
      eLpNorm (lbar E w X') (ENNReal.ofReal (4 * N)) (freshLaw W b) ≤ ENNReal.ofReal Cm :=
    fun X' hX' => lbar_momBd hN4 (hm W hWm E hE w hw X' hX').2
  obtain ⟨h1, h2, h3, h4⟩ := tm_core hb0 hb hW1 E hwpos hY hKd wf Df wU DU hDf hDU
    (N := N) (by omega) hCm0 hinv hmom
  refine ⟨h1, h2, h3, h4.trans ?_⟩
  -- the uniform constant
  have hW' : (0 : ℝ) < (W : ℝ) ^ 2 := by positivity
  have hK₁ : 1 ≤ K₁ := le_max_right _ _
  have hKK : Kd ^ (ℓf + ℓU + 2) ≤ K₁ ^ N :=
    (pow_le_pow_left₀ hKd (le_max_left _ _) _).trans (pow_le_pow_right₀ hK₁ (by omega))
  have hl : (ℓf : ℝ) * ℓU ≤ Lw * Lw :=
    mul_le_mul (by exact_mod_cast hℓf) (by exact_mod_cast hℓU) (by positivity) (by positivity)
  have hCmN : 0 ≤ Cm ^ N := by positivity
  have hK0 : 0 ≤ Kd ^ (ℓf + ℓU + 2) := by positivity
  rw [div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ hW'.le
  calc 3 * ℓf * ℓU * Kd ^ (ℓf + ℓU + 2) * (2 * Cm ^ N)
      = 6 * ((ℓf : ℝ) * ℓU) * Kd ^ (ℓf + ℓU + 2) * Cm ^ N := by ring
    _ ≤ 6 * ((Lw : ℝ) * Lw) * K₁ ^ N * Cm ^ N := by gcongr
    _ = 6 * (Lw : ℝ) * Lw * K₁ ^ N * Cm ^ N := by ring

/-- , from the consumed input hypotheses
`Layers.GaussianAbsorptionContract` and `Inputs.GaussianLpGradient` (explicit hypotheses).
-/
theorem passiveBounds_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    PassiveBoundsStatement :=
  passiveBounds_of_traceMatrix hGA hLp (traceMatrix_holds hGA)

/-- `traceMatrix_holds` has exactly the type of the `traceMatrix` field. -/
example (hGA : GaussianAbsorptionContract) (S : PassiveBoundsStatement) :
    PassiveBoundsStatement :=
  { S with traceMatrix := traceMatrix_holds hGA }

end BlockBand.Transmission.PassiveLayer
