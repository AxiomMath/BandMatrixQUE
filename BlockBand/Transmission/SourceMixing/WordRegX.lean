module

public import BlockBand.Transmission.SourceMixing.OneStepStrict
public import BlockBand.Transmission.PassiveCovariance.WordCovPSD
public import BlockBand.Transmission.PassiveCovariance.Continuity

/-!
# Regularization limit of dressed-word means and of `E(Lf₊L*)`

Hypothesis `PassiveBoundsStatement` (`moments`, for a.s. invertibility at `X` and the uniform
moments). Law `freshLaw W b`, passive `X` (`Y ⪰ 0`), `X_n = PassiveCovariance.regX X n`, fixed
`b ∈ (0, 1/2)`, `E ∈ (-2, 2)`, `W ≥ W₀`.

Continuity of the means under the regularization `X_n = X - i(n+1)⁻¹`, which extends
strictly passive estimates to passive inputs.

* `tendsto_wordMean_regX`: `E w(𝒢(X_n)) → E w(𝒢(X))` (entrywise Vitali, `VitaliL2`);
* `transportedF_expect_eq`: `E(Lf₊L*) = (K̂(E W₃ - c₀E W₂))₀₀` for passive `X`;
* `tendsto_transportedF_regX`: `E(Lf₊L*)(X_n) → E(Lf₊L*)(X)`.
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

/-- The regularization limit of dressed-word means. -/
theorem tendsto_wordMean_regX (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) →
        Tendsto (fun n => matrixExpect (freshLaw W b)
            (fun ω => wordVal (kHat b E (PassiveCovariance.regX X n)) (gRes b E (PassiveCovariance.regX X n) ω) wd D)) atTop
          (𝓝 (matrixExpect (freshLaw W b) (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D))) := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨Cb, Wb, hCb, hbt⟩ := btFun_moment hA hb0 hb h1 h2 (2 * ((Lw + 1 : ℕ) : ℝ)) (by
    have : (1 : ℝ) ≤ ((Lw + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 Lw
    linarith)
  obtain ⟨_, Wm, hmom⟩ := hA.moments b hb0 hb _ hκ 1 le_rfl
  refine ⟨max Wb Wm, fun W hW X hX ℓ hℓ wd D hD => ?_⟩
  have hD' : ∀ j, ‖D j‖ ≤ max Kd 0 := fun j => (hD j).trans (le_max_left _ _)
  set μ := freshLaw W b
  have hinv := (hmom W (le_trans (le_max_right _ _) hW) E (mem_bulkInterval_min E) _
    (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX).1
  have hXn := fun n => passiveY_regX_posSemidef hX n
  refine tendsto_pi_nhds.2 fun α => tendsto_pi_nhds.2 fun β => ?_
  -- entries as word forms
  have ent : ∀ X' : Matrix (Fin W) (Fin W) ℂ, matrixExpect μ
      (fun ω => wordVal (kHat b E X') (gRes b E X' ω) wd D) α β =
      ∫ ω, wordForm (kHat b E X') (Pi.single α 1) (Pi.single β 1) wd D (gRes b E X' ω) ∂μ :=
    fun X' => by
      simp only [matrixExpect, Matrix.of_apply]
      exact integral_congr_ae (Eventually.of_forall fun ω => (wordForm_single _ _ _ _ _ _).symm)
  simp only [ent]
  set a : LayerSite W .oneBlockOnePort → ℂ := Pi.single α 1
  set c : LayerSite W .oneBlockOnePort → ℂ := Pi.single β 1
  set cK := max (max Kd 0) 1 ^ (Lw + 1) * (vecNorm a * vecNorm c)
  have hcK : 0 ≤ cK := by
    have := vecNorm_nonneg a; have := vecNorm_nonneg c; positivity
  have bnd : ∀ X', (passiveY X').PosSemidef →
      eLpNorm (fun ω => wordForm (kHat b E X') a c wd D (gRes b E X' ω)) 2 μ ≤
        ENNReal.ofReal cK * ENNReal.ofReal Cb ^ (Lw + 1) := fun X' hX' =>
    eLpNorm_two_le_of_pow_bound (g := fun ω => 1 + btFun b E X' ω)
      (measurable_wordForm _ a c wd D (measurable_layerRes E (boundaryZ b E) X')).aestronglyMeasurable
      (fun ω => by have := btFun_nonneg b E X' ω; show 0 ≤ 1 + btFun b E X' ω; linarith)
      (measurable_const.add (measurable_btFun b E X')).aestronglyMeasurable hcK (Lw + 1) (by omega)
      (fun ω => (wordForm_poly_bounds b E X' (le_max_right Kd 0) hℓ wd D hD' a c ω).1)
      (by have := hbt W (le_trans (le_max_left _ _) hW) X' hX'; push_cast at this ⊢; exact this)
  refine tendsto_integral_of_ae_of_eLpNorm_two
    (fun n => measurable_wordForm _ a c wd D (measurable_layerRes E (boundaryZ b E) (PassiveCovariance.regX X n)))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
    (fun n => bnd _ (hXn n)) (bnd X hX) ?_
  filter_upwards [hinv] with ω hω using tendsto_wordForm_regX b E X a c wd D ω hω

/-- `E(Lf₊L*) = (K̂(E W₃ - c₀E W₂))₀₀` for every passive `X`. -/
theorem transportedF_expect_eq (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      matrixExpect (freshLaw W b) (freshTransportedF b E X) =
        blkAt (kHat b E X * (matrixExpect (freshLaw W b)
            (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 0, 3] ![1, pTwo, pTwo, 1]) -
          cZero b E • matrixExpect (freshLaw W b)
            (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 3] ![1, pTwo, 1]))) 0 0 := by
  obtain ⟨Cw, Ww, -, hw⟩ := wordMean_bound hA hb0 hb h1 h2 3 1
  refine ⟨max Ww 1, fun W hW X hX => ?_⟩
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  set μ := freshLaw W b
  set Kh := kHat b E X
  set W3 : LayerSample W .oneBlockOnePort → LayerMat W :=
    fun ω => wordVal Kh (gRes b E X ω) ![0, 0, 3] ![1, pTwo, pTwo, 1]
  set W2 : LayerSample W .oneBlockOnePort → LayerMat W :=
    fun ω => wordVal Kh (gRes b E X ω) ![0, 3] ![1, pTwo, 1]
  have hi3 : ∀ α β, Integrable (fun ω => W3 ω α β) μ :=
    (hw W (le_trans (le_max_left _ _) hW) X hX 3 le_rfl _ _ norm_ins4_le).1
  have hi2 : ∀ α β, Integrable (fun ω => W2 ω α β) μ :=
    (hw W (le_trans (le_max_left _ _) hW) X hX 2 (by norm_num) _ _ norm_ins_le).1
  have hz : 0 < (boundaryZ b E).im := etaZ_pos b E (by linarith) h1 h2
  have hae : ∀ᵐ ω ∂μ, freshTransportedF b E X ω =
      blkAt (Kh * W3 ω) 0 0 - cZero b E • blkAt (Kh * W2 ω) 0 0 := by
    filter_upwards [ae_g22_eq_Rplus hb0 hb hW1 E hz hX] with ω hω
    simp only [W3, W2]
    rw [wordVal_W3, wordVal_GPKGstar, blkAt_three, blkAt_freshU, freshTransportedF, passiveF, passiveResolvent, ← hω, freshU]
    change lAt E (boundaryZ b E) X ω * (g22 E (boundaryZ b E) X ω - cZero b E • 1) *
      (lAt E (boundaryZ b E) X ω)ᴴ = _
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rfl
  rw [matrixExpect_congr_ae hae, matrixExpect_sub_smul (fun ω => blkAt (Kh * W3 ω) 0 0)
    (fun ω => blkAt (Kh * W2 ω) 0 0) (cZero b E)
    (fun x y => integrable_mul_entries Kh W3 hi3 _ _)
    (fun x y => integrable_mul_entries Kh W2 hi2 _ _), Matrix.mul_sub, Matrix.mul_smul, blkAt_sub,
    blkAt_smul, mul_matrixExpect' _ _ hi3, mul_matrixExpect' _ _ hi2, blkAt_matrixExpect,
    blkAt_matrixExpect]

theorem continuous_blkAt00 : Continuous fun M : LayerMat W => blkAt M 0 0 :=
  continuous_id.matrix_submatrix _ _

/-- The regularization limit of `E(Lf₊L*)`. -/
theorem tendsto_transportedF_regX (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      Tendsto (fun n => matrixExpect (freshLaw W b)
          (freshTransportedF b E (PassiveCovariance.regX X n))) atTop
        (𝓝 (matrixExpect (freshLaw W b) (freshTransportedF b E X))) := by
  obtain ⟨W₁, hid⟩ := transportedF_expect_eq hA hb0 hb h1 h2
  obtain ⟨W₂, h3⟩ := tendsto_wordMean_regX hA hb0 hb h1 h2 3 1
  refine ⟨max W₁ W₂, fun W hW X hX => ?_⟩
  have hXn := fun n => passiveY_regX_posSemidef hX n
  have e : (fun n => matrixExpect (freshLaw W b)
      (freshTransportedF b E (PassiveCovariance.regX X n))) = fun n =>
      blkAt (kHat b E (PassiveCovariance.regX X n) * (matrixExpect (freshLaw W b)
          (fun ω => wordVal (kHat b E (PassiveCovariance.regX X n))
            (gRes b E (PassiveCovariance.regX X n) ω) ![0, 0, 3] ![1, pTwo, pTwo, 1]) -
        cZero b E • matrixExpect (freshLaw W b)
          (fun ω => wordVal (kHat b E (PassiveCovariance.regX X n))
            (gRes b E (PassiveCovariance.regX X n) ω) ![0, 3] ![1, pTwo, 1]))) 0 0 :=
    funext fun n => hid W (le_trans (le_max_left _ _) hW) _ (hXn n)
  rw [e, hid W (le_trans (le_max_left _ _) hW) X hX]
  have hK : Tendsto (fun n => kHat b E (PassiveCovariance.regX X n)) atTop (𝓝 (kHat b E X)) :=
    ((continuous_kHat b E).tendsto X).comp (tendsto_regX X)
  have t3 := h3 W (le_trans (le_max_right _ _) hW) X hX 3 le_rfl ![0, 0, 3] ![1, pTwo, pTwo, 1]
    norm_ins4_le
  have t2 := h3 W (le_trans (le_max_right _ _) hW) X hX 2 (by norm_num) ![0, 3] ![1, pTwo, 1]
    norm_ins_le
  exact (continuous_blkAt00.tendsto _).comp (hK.mul (t3.sub (t2.const_smul _)))

end BlockBand.Transmission.SourceMixing
