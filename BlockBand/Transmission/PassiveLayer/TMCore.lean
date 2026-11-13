module

public import BlockBand.Transmission.PassiveLayer.TMLimit

/-!
# The trace–matrix covariance bound at a passive input (`ε ↓ 0` by Vitali)

The trace–matrix covariance bound at the regularized inputs `X - iε` passes to the limit `ε ↓ 0`
by Vitali's theorem, given a.s. invertibility at `X` and an `L^{4N}` bound of the moment weight
uniform over passive inputs.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveCovariance
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

/-- **The trace–matrix covariance bound at a passive input**, from a.s. invertibility at `X`
and an `L^{4N}` bound of `lbar` uniform over passive inputs. -/
theorem tm_core {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) {w : ℂ}
    (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    {Kd : ℝ} (hKd : 0 ≤ Kd) {ℓf ℓU : ℕ}
    (wf : Fin ℓf → Fin 6 × Bool) (Df : Fin (ℓf + 1) → Matrix (Fin W) (Fin W) ℂ)
    (wU : Fin ℓU → Fin 6 × Bool) (DU : Fin (ℓU + 1) → Matrix (Fin W) (Fin W) ℂ)
    (hDf : ∀ j, ‖Df j‖ ≤ Kd) (hDU : ∀ j, ‖DU j‖ ≤ Kd)
    {N : ℕ} (hN : ℓf + ℓU + 2 ≤ N) {Cm : ℝ} (hCm : 0 ≤ Cm)
    (hinv : ∀ᵐ ω ∂freshLaw W b, IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω))
    (hmom : ∀ X' : Matrix (Fin W) (Fin W) ℂ, (passiveY X').PosSemidef →
      eLpNorm (lbar E w X') (ENNReal.ofReal (4 * N)) (freshLaw W b) ≤ ENNReal.ofReal Cm) :
    Integrable (fun ω => (W : ℂ)⁻¹ * (passiveWord E w X wf Df ω).trace) (freshLaw W b) ∧
      (∀ x y, Integrable (fun ω => passiveWord E w X wU DU ω x y) (freshLaw W b)) ∧
      (∀ x y, Integrable (fun ω => (W : ℂ)⁻¹ * (passiveWord E w X wf Df ω).trace *
        passiveWord E w X wU DU ω x y) (freshLaw W b)) ∧
      ‖matrixExpect (freshLaw W b) (fun ω => ((W : ℂ)⁻¹ * (passiveWord E w X wf Df ω).trace) •
          passiveWord E w X wU DU ω) -
        (∫ ω, (W : ℂ)⁻¹ * (passiveWord E w X wf Df ω).trace ∂freshLaw W b) •
          matrixExpect (freshLaw W b) (passiveWord E w X wU DU)‖ ≤
        3 * ℓf * ℓU * Kd ^ (ℓf + ℓU + 2) / (W : ℝ) ^ 2 * (2 * Cm ^ N) := by
  set μ := freshLaw W b with hμ
  set n := ℓf + ℓU + 2 with hn
  have hN1 : 1 ≤ N := by omega
  set Xk : ℕ → Matrix (Fin W) (Fin W) ℂ := fun k => regX X (epsN k) with hXk
  have hYk : ∀ k, (passiveY (Xk k)).PosSemidef := fun k => regX_posSemidef hY (epsN_pos k).le
  -- the three families of integrands, at any input
  set F : Matrix (Fin W) (Fin W) ℂ → LayerSample W .oneBlockOnePort → ℂ :=
    fun X' ω => (W : ℂ)⁻¹ * (passiveWord E w X' wf Df ω).trace with hF
  set Ue : Matrix (Fin W) (Fin W) ℂ → Fin W → Fin W → LayerSample W .oneBlockOnePort → ℂ :=
    fun X' x y ω => passiveWord E w X' wU DU ω x y with hUe
  set P : Matrix (Fin W) (Fin W) ℂ → Fin W → Fin W → LayerSample W .oneBlockOnePort → ℂ :=
    fun X' x y ω => F X' ω * Ue X' x y ω with hP
  have hFm : ∀ X', Measurable (F X') := fun X' =>
    measurable_const.mul ((Continuous.matrix_trace continuous_id).measurable.comp
      (measurable_passiveWord E w X' wf Df))
  have hUm : ∀ X' x y, Measurable (Ue X' x y) := fun X' x y =>
    (measurable_pi_apply y).comp ((measurable_pi_apply x).comp (measurable_passiveWord E w X' wU DU))
  have hPm : ∀ X' x y, Measurable (P X' x y) := fun X' x y => (hFm X').mul (hUm X' x y)
  set cf := Kd ^ (ℓf + 1) with hcf
  set cu := Kd ^ (ℓU + 1) with hcu
  have hcf0 : 0 ≤ cf := by positivity
  have hcu0 : 0 ≤ cu := by positivity
  have hFb : ∀ X' ω, ‖F X' ω‖ ≤ cf * lbar E w X' ω ^ N := fun X' ω =>
    (norm_trW_le _).trans (norm_passiveWord_le E w X' wf Df hKd hDf (by omega) ω)
  have hUb : ∀ X' x y ω, ‖Ue X' x y ω‖ ≤ cu * lbar E w X' ω ^ N := fun X' x y ω =>
    (norm_entry_le _ x y).trans (norm_passiveWord_le E w X' wU DU hKd hDU (by omega) ω)
  have hPb : ∀ X' x y ω, ‖P X' x y ω‖ ≤ (cf * cu) * lbar E w X' ω ^ (2 * N) := fun X' x y ω => by
    rw [norm_mul, show 2 * N = N + N by ring, pow_add]
    calc ‖F X' ω‖ * ‖Ue X' x y ω‖ ≤ (cf * lbar E w X' ω ^ N) * (cu * lbar E w X' ω ^ N) :=
          mul_le_mul (hFb X' ω) (hUb X' x y ω) (norm_nonneg _)
            (mul_nonneg hcf0 (pow_nonneg (lbar_nonneg E w X' ω) N))
      _ = _ := by ring
  -- uniform `L²` bounds over passive inputs
  set BF := ENNReal.ofReal cf * ENNReal.ofReal Cm ^ N
  set BU := ENNReal.ofReal cu * ENNReal.ofReal Cm ^ N
  set BP := ENNReal.ofReal (cf * cu) * ENNReal.ofReal Cm ^ (2 * N)
  have hBF : BF ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hBU : BU ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hBP : BP ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hM : ((4 * N : ℕ) : ℝ) = 4 * N := by push_cast; ring
  have hmom' : ∀ X', (passiveY X').PosSemidef →
      eLpNorm (lbar E w X') (ENNReal.ofReal ((4 * N : ℕ) : ℝ)) μ ≤ ENNReal.ofReal Cm :=
    fun X' hX' => by rw [hM]; exact hmom X' hX'
  have hF2 : ∀ X', (passiveY X').PosSemidef → eLpNorm (F X') 2 μ ≤ BF := fun X' hX' =>
    eLpNorm_two_le_lbar E w X' (hFm X') hcf0 hN1 (hFb X') (by omega) (hmom' X' hX')
  have hU2 : ∀ X', (passiveY X').PosSemidef → ∀ x y, eLpNorm (Ue X' x y) 2 μ ≤ BU :=
    fun X' hX' x y =>
      eLpNorm_two_le_lbar E w X' (hUm X' x y) hcu0 hN1 (hUb X' x y) (by omega) (hmom' X' hX')
  have hP2 : ∀ X', (passiveY X').PosSemidef → ∀ x y, eLpNorm (P X' x y) 2 μ ≤ BP :=
    fun X' hX' x y =>
      eLpNorm_two_le_lbar E w X' (hPm X' x y) (mul_nonneg hcf0 hcu0) (by omega) (hPb X' x y)
        (by omega) (hmom' X' hX')
  have hint2 : ∀ {g : LayerSample W .oneBlockOnePort → ℂ} {B : ℝ≥0∞}, Measurable g → B ≠ ∞ →
      eLpNorm g 2 μ ≤ B → Integrable g μ := fun hg hB h =>
    (show MemLp _ 2 μ from lt_of_le_of_lt h hB.lt_top).integrable one_le_two
  refine ⟨hint2 (hFm X) hBF (hF2 X hY), fun x y => hint2 (hUm X x y) hBU (hU2 X hY x y),
    fun x y => hint2 (hPm X x y) hBP (hP2 X hY x y), ?_⟩
  -- a.e. convergence
  have hlimW : ∀ᵐ ω ∂μ, ∀ {ℓ : ℕ} (wd : Fin ℓ → Fin 6 × Bool)
      (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ),
      Tendsto (fun k => passiveWord E w (Xk k) wd D ω) atTop (𝓝 (passiveWord E w X wd D ω)) := by
    filter_upwards [hinv] with ω hω
    intro ℓ wd D
    exact tendsto_passiveWord_reg E w X ω hω wd D
  have hlimF : ∀ᵐ ω ∂μ, Tendsto (fun k => F (Xk k) ω) atTop (𝓝 (F X ω)) := by
    filter_upwards [hlimW] with ω hω
    exact ((continuous_const.mul (Continuous.matrix_trace continuous_id)).tendsto _).comp (hω wf Df)
  have hlimU : ∀ x y, ∀ᵐ ω ∂μ, Tendsto (fun k => Ue (Xk k) x y ω) atTop (𝓝 (Ue X x y ω)) := by
    intro x y
    filter_upwards [hlimW] with ω hω
    exact ((entryR x y).continuous.tendsto _).comp (hω wU DU)
  have hlimP : ∀ x y, ∀ᵐ ω ∂μ, Tendsto (fun k => P (Xk k) x y ω) atTop (𝓝 (P X x y ω)) := by
    intro x y
    filter_upwards [hlimF, hlimU x y] with ω h1 h2
    exact h1.mul h2
  -- Vitali for the three means
  have tF := tendsto_integral_of_ae_of_eLpNorm_two (fun k => hFm (Xk k)) hBF
    (fun k => hF2 _ (hYk k)) (hF2 X hY) hlimF
  have tU : ∀ x y, Tendsto (fun k => ∫ ω, Ue (Xk k) x y ω ∂μ) atTop (𝓝 (∫ ω, Ue X x y ω ∂μ)) :=
    fun x y => tendsto_integral_of_ae_of_eLpNorm_two (fun k => hUm (Xk k) x y) hBU
      (fun k => hU2 _ (hYk k) x y) (hU2 X hY x y) (hlimU x y)
  have tP : ∀ x y, Tendsto (fun k => ∫ ω, P (Xk k) x y ω ∂μ) atTop (𝓝 (∫ ω, P X x y ω ∂μ)) :=
    fun x y => tendsto_integral_of_ae_of_eLpNorm_two (fun k => hPm (Xk k) x y) hBP
      (fun k => hP2 _ (hYk k) x y) (hP2 X hY x y) (hlimP x y)
  -- the covariance matrices
  set Δ : Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ := fun X' =>
    matrixExpect μ (fun ω => F X' ω • passiveWord E w X' wU DU ω) -
      (∫ ω, F X' ω ∂μ) • matrixExpect μ (passiveWord E w X' wU DU) with hΔ
  have hΔe : ∀ X' x y, Δ X' x y = ∫ ω, P X' x y ω ∂μ - (∫ ω, F X' ω ∂μ) * ∫ ω, Ue X' x y ω ∂μ :=
    fun X' x y => by
      simp only [hΔ, matrixExpect, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
        smul_eq_mul, hP, hUe]
  have tΔ : Tendsto (fun k => Δ (Xk k)) atTop (𝓝 (Δ X)) := by
    refine tendsto_pi_nhds.2 fun x => tendsto_pi_nhds.2 fun y => ?_
    simp only [hΔe]
    exact (tP x y).sub (tF.mul (tU x y))
  -- the bound for each regularization
  have hbd : ∀ k, ‖Δ (Xk k)‖ ≤ 3 * ℓf * ℓU * Kd ^ n / (W : ℝ) ^ 2 * (2 * Cm ^ N) := by
    intro k
    have hmN : eLpNorm (lbar E w (Xk k)) (ENNReal.ofReal N) μ ≤ ENNReal.ofReal Cm :=
      (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by
        have : (0 : ℝ) ≤ N := by positivity
        linarith))).trans (hmom _ (hYk k))
    obtain ⟨hiN, hIN⟩ := tm_moment (lbar_nonneg E w (Xk k)) hN1 hCm hmN
    have hle : ∀ ω, lbar E w (Xk k) ω ^ n ≤ lbar E w (Xk k) ω ^ N := fun ω =>
      pow_le_pow_right₀ (one_le_lbar E w (Xk k) ω) hN
    have hin : Integrable (fun ω => lbar E w (Xk k) ω ^ n) μ :=
      hiN.mono' ((measurable_lbar E w (Xk k)).pow_const n).aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          rw [Real.norm_of_nonneg (pow_nonneg (lbar_nonneg E w (Xk k) ω) n)]; exact hle ω)
    have h := tm_cov_reg_fresh hb0 hb hW E hw hY (epsN_pos k) hKd wf Df wU DU hDf hDU hin
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      (by positivity))
    exact (integral_mono hin hiN hle).trans hIN
  exact le_of_tendsto' tΔ.norm hbd

end BlockBand.Transmission.PassiveLayer
