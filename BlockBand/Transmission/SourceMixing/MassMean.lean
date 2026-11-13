module

public import BlockBand.Transmission.SourceMixing.MassMeanStrict

/-!
# The `q/W`-exact mass mean for every passive input

Hypothesis `PassiveBoundsStatement`. Law `freshLaw W b`, deterministic passive `X` (`Y ⪰ 0`), fixed
`b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; `δ₀ = jetDistance0`, `q = passiveMass`, `α = alphaCoef`; the constant
`C` and `W₀` depend on `b, E` only, uniformly in `X`.

For every passive `X`, `Re Tr(Q E[LL*]) ≤ q/(1+αq/W) + C(δ₀ + W⁻²)q`, obtained from the strictly
passive case by regularization.

* `mm_tendsto_EU`: along `X_n = X - i(n+1)⁻¹`, `E[LL*](X_n) → E[LL*](X)` (a.s. convergence of
  `LL*` and uniform `L²` bounds from the `moments` clause of the passive bounds at `p = 4`, as in
  `PassiveCovariance.tendsto_bilinearCovariance_regX`);
* `massMean_holds`: `massMean_strict` passed to the limit (`tendsto_Q_regX`,
  `tendsto_mass_regX`, `tendsto_jet0_regX`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The regularization limit of `E[LL*]`. -/
theorem mm_tendsto_EU (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      Tendsto (fun n => matrixExpect (freshLaw W b) (freshU b E (PassiveCovariance.regX X n)))
        atTop (𝓝 (matrixExpect (freshLaw W b) (freshU b E X))) := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨C4, W4, h4⟩ := hA.moments b hb0 hb _ hκ 4 (by norm_num)
  refine ⟨W4, fun W hW X hX => ?_⟩
  have hE := PassiveLayer.mem_bulkInterval_min E
  have hz := PassiveLayer.boundaryZ_mem_paramDisk (b := b) (by linarith) h1 h2
  set μ := freshLaw W b
  have m4 : ∀ X' : Matrix (Fin W) (Fin W) ℂ, (passiveY X').PosSemidef →
      eLpNorm (fun ω => ‖freshL b E X' ω‖) (ENNReal.ofReal (2 * (2 : ℕ))) μ ≤ ENNReal.ofReal C4 :=
    fun X' hX' => by
      have := (h4 W hW E hE _ hz X' hX').2.2.2
      norm_num at this ⊢; exact this
  have hinv := (h4 W hW E hE _ hz X hX).1
  have bndE : ∀ X', (passiveY X').PosSemidef → ∀ i j,
      eLpNorm (fun ω => freshU b E X' ω i j) 2 μ ≤ ENNReal.ofReal 1 * ENNReal.ofReal C4 ^ 2 :=
    fun X' hX' i j =>
    eLpNorm_two_le_of_pow_bound ((measurable_freshU b E X').eval_matrix).aestronglyMeasurable
      (fun _ => norm_nonneg _) (measurable_norm_freshL b E X').aestronglyMeasurable zero_le_one 2
      (by norm_num)
      (fun ω => by rw [one_mul]; exact (norm_entry_le _ i j).trans (norm_freshU_le b E X' ω))
      (m4 X' hX')
  have fin : ENNReal.ofReal 1 * ENNReal.ofReal C4 ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hae : ∀ᵐ ω ∂μ, Tendsto (fun n => freshU b E (PassiveCovariance.regX X n) ω) atTop
      (𝓝 (freshU b E X ω)) := by
    filter_upwards [hinv] with ω hω using tendsto_freshU_regX b E X ω hω
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  exact tendsto_integral_of_ae_of_eLpNorm_two
    (fun n => (measurable_freshU b E (PassiveCovariance.regX X n)).eval_matrix) fin
    (fun n => bndE _ (passiveY_regX_posSemidef hX n) i j) (bndE X hX i j)
    (by filter_upwards [hae] with ω hω using
      (((continuous_apply j).comp (continuous_apply i)).tendsto _).comp hω)

/-- The mass mean: `Re Tr(Q E[LL*]) ≤ q/(1+αq/W) + C(δ₀ + W⁻²)q` for every passive `X`. -/
theorem massMean_holds (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
        (passiveQ b E X * matrixExpect (freshLaw W b) (freshU b E X)).trace.re ≤
          passiveMass b E X / (1 + alphaCoef b E * passiveMass b E X / W) +
            C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) * passiveMass b E X := by
  obtain ⟨C, W₀, hC, hS⟩ := massMean_strict hA hb0 hb h1 h2
  obtain ⟨W₁, hT⟩ := mm_tendsto_EU hA hb0 hb h1 h2
  refine ⟨C, max W₀ W₁, hC, fun W hW X hX => ?_⟩
  set Xn := PassiveCovariance.regX X
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hα : 0 ≤ alphaCoef b E := by
    rw [alphaCoef]; have : 0 < b * etaZ b E := mul_pos hb0 hη; positivity
  have tq := tendsto_mass_regX hb0 hb h1 h2 hX
  have tQ := tendsto_Q_regX hb0 hb h1 h2 hX
  have tU := hT W (le_trans (le_max_right _ _) hW) X hX
  have hL : Tendsto (fun n => (passiveQ b E (Xn n) *
      matrixExpect (freshLaw W b) (freshU b E (Xn n))).trace.re) atTop
      (𝓝 ((passiveQ b E X * matrixExpect (freshLaw W b) (freshU b E X)).trace.re)) :=
    (Complex.continuous_re.tendsto _).comp ((continuous_id.matrix_trace.tendsto _).comp
      (tQ.mul tU))
  have hden : Tendsto (fun n => 1 + alphaCoef b E * passiveMass b E (Xn n) / W) atTop
      (𝓝 (1 + alphaCoef b E * passiveMass b E X / W)) :=
    tendsto_const_nhds.add ((tq.const_mul _).div_const _)
  have hne : 1 + alphaCoef b E * passiveMass b E X / W ≠ 0 := by
    have := passiveMass_nonneg b E hX; positivity
  have hR : Tendsto (fun n => passiveMass b E (Xn n) /
      (1 + alphaCoef b E * passiveMass b E (Xn n) / W) +
        C * (jetDistance0 b E (Xn n) + (W : ℝ)⁻¹ ^ 2) * passiveMass b E (Xn n)) atTop
      (𝓝 (passiveMass b E X / (1 + alphaCoef b E * passiveMass b E X / W) +
        C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) * passiveMass b E X)) :=
    (tq.div hden hne).add
      ((((tendsto_jet0_regX hb0 hb h1 h2 hX).add_const _).const_mul _).mul tq)
  exact le_of_tendsto_of_tendsto' hL hR fun n =>
    hS W (le_trans (le_max_left _ _) hW) (Xn n) (passiveY_regX_posDef hX n)

end BlockBand.Transmission.SourceMixing
