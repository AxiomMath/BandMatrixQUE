module

public import BlockBand.SourceProcess.FullSource.DeltaMeanStrict
public import BlockBand.SourceProcess.FullSource.DeltaFlucHolds
public import BlockBand.Transmission.PassiveLayer.TMMain

/-!
# The mean bound `DeltaMean`

`deltaMean_holds`: for passive `X` with `δ₀(X) ≤ d₀`, `‖EΔ‖ ≤ C(δ₀(X) + W⁻²)`.
Passive `X` is reached from strictly passive inputs along the regularization
`X_n = X - i(n+1)⁻¹` (`PassiveCovariance.regX`): `δ₀(X_n) → δ₀(X)` (`tendsto_jet0_regX`), so
`δ₀(X_n) ≤ d₁` eventually; `Δ(X_n) → Δ(X)` wherever the layer matrix at `X` is invertible (a.s.,
by `moments`), and `E Δ(X_n) → E Δ(X)` entrywise by Vitali
(`tendsto_integral_of_ae_of_eLpNorm_two`) with the uniform `L²` bound `delta_moments`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `Δ(X_n) → Δ(X)` wherever the layer matrix at `X` is invertible. -/
theorem tendsto_freshDelta_regX (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort)
    (hω : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω).det) :
    Tendsto (fun n => freshDelta b E (PassiveCovariance.regX X n) ω) atTop
      (𝓝 (freshDelta b E X ω)) := by
  set z := boundaryZ b E
  have hM := ((PassiveCovariance.continuous_layerMatrix_X E z ω).tendsto X).comp
    (PassiveCovariance.tendsto_regX X)
  have hG : Tendsto (fun n => PassiveLayer.layerAt E z (PassiveCovariance.regX X n) ω) atTop
      (𝓝 (PassiveLayer.layerAt E z X ω)) := PassiveCovariance.tendsto_matrix_inv hM hω
  have hg : Tendsto (fun n => PassiveLayer.g11 E z (PassiveCovariance.regX X n) ω) atTop
      (𝓝 (PassiveLayer.g11 E z X ω)) := by
    simp only [PassiveLayer.g11_eq_iota]
    exact tendsto_mul2 (tendsto_mul2 tendsto_const_nhds hG) tendsto_const_nhds
  have hK : Tendsto (fun n => z • (1 : Matrix (Fin W) (Fin W) ℂ) - PassiveCovariance.regX X n)
      atTop (𝓝 (z • 1 - X)) := tendsto_const_nhds.sub (PassiveCovariance.tendsto_regX X)
  simp only [freshDelta_eq]
  exact (tendsto_mul2 (tendsto_mul2 hK hg) hK).sub hK

/-- **`DeltaMean`** from `GaussianAbsorptionContract` and `GaussianLpGradient`. -/
theorem deltaMean_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    DeltaMean := by
  intro b hb0 hb κ hκ
  have hA := PassiveLayer.passiveBounds_holds hGA hLp
  obtain ⟨d₁, C, W₀, hd₁, hC, hstrict⟩ := deltaMean_strict hA hb0 hb hκ
  obtain ⟨C2, W₂, hC2, hmom⟩ := delta_moments hGA b hb0 hb κ hκ 2 (by norm_num)
  obtain ⟨_, W₃, hdet⟩ := PassiveLayer.moments_holds hGA b hb0 hb κ hκ 1 le_rfl
  refine ⟨d₁ / 2, by positivity, C, max (max W₀ W₂) W₃, fun W hW E hE X hY hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW0, hW2⟩, hW3⟩ := hW
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
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
  have hR := (hj.add_const (((W : ℝ)⁻¹) ^ 2)).const_mul C
  exact le_of_tendsto_of_tendsto hM.norm hR (hev.mono fun n hn =>
    hstrict W hW0 E hE (Xn n) (PassiveCovariance.passiveY_regX_posDef hY n) hn)

end BlockBand.SourceProcess.FullSource
