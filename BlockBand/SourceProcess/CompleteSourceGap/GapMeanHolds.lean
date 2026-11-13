module

public import BlockBand.SourceProcess.CompleteSourceGap.GapMeanStrict
public import BlockBand.SourceProcess.CompleteSourceGap.GapFlucHolds
public import BlockBand.SourceProcess.CompleteSourceGap.Fluct

/-!
# Mean of the gap letter, and the complete-source gap statement

* **`gapLetterMean_holds (hA) : GapLetterMean`** from `PassiveBoundsStatement` (available as
  `passiveBounds_holds hGA hLp`): `gapMean_strict` at the regularization `X_n = X - i(n+1)⁻¹`
  (`PassiveCovariance.regX`) and the limit `n → ∞`: `EΓ(X_n) → EΓ(X)` entrywise by Vitali
  (`tendsto_integral_of_ae_of_eLpNorm_two`; a.s. convergence where the layer matrix at `X` is
  invertible; uniform `L²` bound `(‖K‖ + 1)‖L‖‖𝒢‖`, passive moments at `p = 4`), and
  `δ₀, δ₁, q` are continuous along `X_n` (`tendsto_jet0_regX`, `tendsto_jet1_regX`,
  `tendsto_mass_regX`). The stationary jet exists by `stationaryJet_exists`.
* **`completeSourceGap_holds`**: `CompleteSourceGapStatement` from `GaussianAbsorptionContract`
  and `GaussianLpGradient`, combining the mean and the fluctuation of the gap letter.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission
open BlockBand.Transmission.PassiveLayer (PassiveBoundsStatement layerAt lAt g21 pK pTwo
  layerMatrix_regX liftX MomBd letter_momBd paramDisk)
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `Γ(X_n) → Γ(X)` wherever the layer matrix at `X` is invertible. -/
theorem tendsto_gapLetter_regX (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort)
    (hω : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω).det) :
    Tendsto (fun n => gapLetter b E (PassiveCovariance.regX X n) ω) atTop
      (𝓝 (gapLetter b E X ω)) := by
  set z := boundaryZ b E
  have hM := ((PassiveCovariance.continuous_layerMatrix_X E z ω).tendsto X).comp
    (PassiveCovariance.tendsto_regX X)
  have hG : Tendsto (fun n => layerAt E z (PassiveCovariance.regX X n) ω) atTop
      (𝓝 (layerAt E z X ω)) := PassiveCovariance.tendsto_matrix_inv hM hω
  have hK : Tendsto (fun n => z • (1 : Matrix (Fin W) (Fin W) ℂ) - PassiveCovariance.regX X n)
      atTop (𝓝 (z • 1 - X)) := tendsto_const_nhds.sub (PassiveCovariance.tendsto_regX X)
  have hP : Tendsto (fun n => pK z (PassiveCovariance.regX X n)) atTop (𝓝 (pK z X)) :=
    FullSource.tendsto_mul2 hK tendsto_const_nhds
  have hQ : Tendsto (fun n => FullSource.qK z (PassiveCovariance.regX X n)) atTop
      (𝓝 (FullSource.qK z X)) := FullSource.tendsto_mul2 tendsto_const_nhds hK
  have hH := FullSource.tendsto_mul2 (FullSource.tendsto_mul2 hG
    (tendsto_const_nhds (x := pTwo W))) hG
  simp only [gapLetter_eq_pq]
  exact FullSource.tendsto_mul2 (FullSource.tendsto_mul2 hP hH) hQ

theorem measurable_gapLetter (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (gapLetter b E X) :=
  Bridge.measurable_matrix_mul' (Bridge.measurable_matrix_mul'
    (PassiveLayer.measurable_lAt E (boundaryZ b E) X)
    (PassiveLayer.measurable_g21 E (boundaryZ b E) X)) measurable_const

theorem norm_gapLetter_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    ‖gapLetter b E X ω‖ ≤ ‖boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖ *
      (‖lAt E (boundaryZ b E) X ω‖ * ‖layerAt E (boundaryZ b E) X ω‖) := by
  have h1 := Matrix.l2_opNorm_mul (lAt E (boundaryZ b E) X ω * g21 E (boundaryZ b E) X ω)
    (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X)
  have h2 := Matrix.l2_opNorm_mul (lAt E (boundaryZ b E) X ω) (g21 E (boundaryZ b E) X ω)
  have h3 := norm_g21_le E (boundaryZ b E) X ω
  have hl := norm_nonneg (lAt E (boundaryZ b E) X ω)
  have hk := norm_nonneg (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X)
  have h4 : ‖lAt E (boundaryZ b E) X ω * g21 E (boundaryZ b E) X ω‖ ≤
      ‖lAt E (boundaryZ b E) X ω‖ * ‖layerAt E (boundaryZ b E) X ω‖ :=
    h2.trans (mul_le_mul_of_nonneg_left h3 hl)
  calc ‖gapLetter b E X ω‖ ≤ ‖lAt E (boundaryZ b E) X ω * g21 E (boundaryZ b E) X ω‖ *
        ‖boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖ := h1
    _ ≤ (‖lAt E (boundaryZ b E) X ω‖ * ‖layerAt E (boundaryZ b E) X ω‖) *
        ‖boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖ :=
        mul_le_mul_of_nonneg_right h4 hk
    _ = _ := by ring

theorem norm_K_regX_le' (z : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (n : ℕ) :
    ‖z • (1 : Matrix (Fin W) (Fin W) ℂ) - PassiveCovariance.regX X n‖ ≤
      ‖z • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖ + 1 := by
  rw [PassiveCovariance.regX, show z • (1 : Matrix (Fin W) (Fin W) ℂ) -
    (X - (Complex.I * (((n : ℝ) + 1)⁻¹ : ℝ)) • 1) =
      (z • 1 - X) + (Complex.I * (((n : ℝ) + 1)⁻¹ : ℝ)) • 1 by abel]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  have ht : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [norm_smul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  calc ((n : ℝ) + 1)⁻¹ * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 * 1 :=
        mul_le_mul ht PassiveCovariance.norm_one_matrix_le (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **`GapLetterMean`**, from `PassiveBoundsStatement`. -/
theorem gapLetterMean_holds (hA : PassiveBoundsStatement) : GapLetterMean := by
  intro b hb0 hb E h1 h2
  refine ⟨PassiveCovariance.stationaryJet_exists hb0 hb h1 h2, fun s hs => ?_⟩
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hE := PassiveLayer.mem_bulkInterval_min E
  obtain ⟨C, W₀, hC, hst⟩ := gapMean_strict hA hb0 hb h1 h2 s hs
  obtain ⟨Cq, Wq, hmq⟩ := hA.moments b hb0 hb _ hκ (2 * 2) (by norm_num)
  refine ⟨C, max W₀ Wq, fun W hW X hY => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨hW0, hWq⟩ := hW
  set μ := freshLaw W b
  set z := boundaryZ b E
  set Xn := fun n : ℕ => PassiveCovariance.regX X n
  have hz : z ∈ paramDisk b E := PassiveLayer.boundaryZ_mem_paramDisk (by linarith) h1 h2
  set Cm := max Cq 0
  have hCm : 0 ≤ Cm := le_max_right _ _
  set Kb := (‖z • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖ + 1) * (Cm * Cm)
  have hL2 : ∀ Y : Matrix (Fin W) (Fin W) ℂ, (passiveY Y).PosSemidef →
      ‖z • (1 : Matrix (Fin W) (Fin W) ℂ) - Y‖ ≤ ‖z • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖ + 1 →
      ∀ i j, eLpNorm (fun ω => gapLetter b E Y ω i j) 2 μ ≤ ENNReal.ofReal Kb := by
    intro Y hY' hK i j
    obtain ⟨-, hg, hk, hl⟩ := hmq W hWq E hE z hz Y hY'
    obtain ⟨hgM, -, hlM⟩ := letter_momBd (b := b) ⟨hg, hk, hl⟩
    have hprod := (PassiveLayer.MomBd.mul (p := 2) two_pos hlM hgM hCm).const_mul
      (c := ‖z • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖ + 1) (by positivity)
    have hb2 : eLpNorm (fun ω => gapLetter b E Y ω i j) (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal Kb :=
      (eLpNorm_mono_ae_real (measurable_gapLetter b E Y).eval_matrix.aestronglyMeasurable
        (ae_of_all _ fun ω => (FullSource.norm_entry_le_op _ i j).trans ((norm_gapLetter_le b E Y ω).trans
          (mul_le_mul_of_nonneg_right hK (by positivity))))).trans hprod.2
    simpa using hb2
  have hdetX := (hmq W hWq E hE z hz X hY).1
  have hent : ∀ i j, Tendsto (fun n => ∫ ω, gapLetter b E (Xn n) ω i j ∂μ) atTop
      (𝓝 (∫ ω, gapLetter b E X ω i j ∂μ)) := by
    intro i j
    refine PassiveCovariance.tendsto_integral_of_ae_of_eLpNorm_two
      (fun n => (measurable_gapLetter b E (Xn n)).eval_matrix) ENNReal.ofReal_ne_top
      (fun n => hL2 _ (PassiveCovariance.passiveY_regX_posSemidef hY n) (norm_K_regX_le' z X n) i j)
      (hL2 X hY (by linarith) i j) ?_
    filter_upwards [hdetX] with ω hω
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 (tendsto_gapLetter_regX b E X ω hω) i) j
  have hM : Tendsto (fun n => matrixExpect μ (gapLetter b E (Xn n))) atTop
      (𝓝 (matrixExpect μ (gapLetter b E X))) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hent i j
  have hL := (hM.sub_const (thetaStar b E s • (1 : Matrix (Fin W) (Fin W) ℂ))).norm
  have hR : Tendsto (fun n => C * (jetDistance0 b E (Xn n) + jetDistance1 b E s (Xn n) +
      passiveMass b E (Xn n) / W + ((W : ℝ)⁻¹) ^ 2)) atTop
      (𝓝 (C * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W +
        ((W : ℝ)⁻¹) ^ 2))) :=
    ((((PassiveCovariance.tendsto_jet0_regX hb0 hb h1 h2 hY).add
      (PassiveCovariance.tendsto_jet1_regX hb0 hb h1 h2 hY s)).add
      ((PassiveCovariance.tendsto_mass_regX hb0 hb h1 h2 hY).div_const _)).add_const _).const_mul _
  exact le_of_tendsto_of_tendsto' hL hR fun n =>
    hst W hW0 (Xn n) (PassiveCovariance.passiveY_regX_posDef hY n)

/-- **`CompleteSourceGapStatement`**, from `GaussianAbsorptionContract` and
`GaussianLpGradient`.
-/
theorem completeSourceGap_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    CompleteSourceGapStatement :=
  completeSourceGap_of hGA hLp (gapLetterMean_holds (PassiveLayer.passiveBounds_holds hGA hLp))
    (gapLetterFluctuation_holds hGA hLp)

end BlockBand.SourceProcess.CompleteSourceGap
