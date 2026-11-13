module

public import BlockBand.Transmission.PassiveCovariance.WordCov
public import BlockBand.Transmission.PassiveCovariance.WordReplicaId
public import BlockBand.Transmission.PassiveCovariance.Continuity

/-!
# The general bilinear variance/covariance bound for every passive input (`Y ⪰ 0`)

Hypotheses `GaussianPoincare` and `PassiveBoundsStatement`. `wordForm_variance` and
`wordForm_covariance` hold for strictly passive `X`; here they are extended, with the same constants,
to every passive `X` (`(passiveY X).PosSemidef`, no norm bound), along `X_n = X - i/(n+1)` (`regX`):

* `tendsto_wordForm_regX`: `Ψ_n → Ψ` at every sample where the layer matrix at `X` is
  invertible (a.s., by the `moments` clause of `PassiveBoundsStatement`);
* Vitali (`tendsto_integral_of_ae_of_eLpNorm_two`, uniform `L²` bounds from `moments`)
  gives `E Ψ_n → E Ψ`, and Fatou gives `E|Ψ - EΨ|² ≤ liminf E|Ψ_n - EΨ_n|²`;
* `wordForm_variance_psd`, `wordForm_covariance_psd`: the variance and covariance bounds for
  `Y ⪰ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

section Generic
variable {n : Type} [Fintype n] [DecidableEq n]

theorem continuous_wordVal₂ {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → Matrix n n ℂ) :
    Continuous fun p : Matrix n n ℂ × Matrix n n ℂ => wordVal p.1 p.2 wd D := by
  have hL : ∀ k : Fin 4, Continuous fun p : Matrix n n ℂ × Matrix n n ℂ => wLetter p.1 p.2 k := by
    intro k
    fin_cases k
    · exact continuous_snd
    · exact continuous_fst.mul continuous_snd
    · exact continuous_snd.matrix_conjTranspose
    · exact (continuous_fst.mul continuous_snd).matrix_conjTranspose
  induction ℓ with
  | zero => simp only [wordVal_zero]; exact continuous_const
  | succ ℓ ih =>
    simp only [wordVal_succ]
    exact (continuous_const.mul (hL _)).mul (ih _ _)

theorem continuous_wordForm₂ (a c : n → ℂ) {ℓ : ℕ} (wd : Fin ℓ → Fin 4)
    (D : Fin (ℓ + 1) → Matrix n n ℂ) :
    Continuous fun p : Matrix n n ℂ × Matrix n n ℂ => wordForm p.1 a c wd D p.2 :=
  continuous_const.dotProduct ((continuous_wordVal₂ wd D).matrix_mulVec continuous_const)

end Generic

theorem continuous_kHat (b E : ℝ) : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => kHat b E X := by
  unfold kHat
  refine Continuous.matrix_fromBlocks ?_ continuous_const continuous_const continuous_const
  simp only [liftX_eq_submatrix]
  exact (continuous_const.sub continuous_id).matrix_submatrix _ _

/-- `Ψ(X_n) → Ψ(X)` at every sample where the layer matrix at `X` is invertible. -/
theorem tendsto_wordForm_regX (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (a c : LayerSite W .oneBlockOnePort → ℂ) {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W)
    (ω : LayerSample W .oneBlockOnePort)
    (hω : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω).det) :
    Tendsto (fun n => wordForm (kHat b E (regX X n)) a c wd D (gRes b E (regX X n) ω)) atTop
      (𝓝 (wordForm (kHat b E X) a c wd D (gRes b E X ω))) := by
  have hM : Tendsto (fun n => layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => regX X n u.2 v.2) ω) atTop
      (𝓝 (layerMatrix .oneBlockOnePort E (boundaryZ b E)
        (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω)) :=
    ((continuous_layerMatrix_X E (boundaryZ b E) ω).tendsto X).comp (tendsto_regX X)
  have hG : Tendsto (fun n => gRes b E (regX X n) ω) atTop (𝓝 (gRes b E X ω)) :=
    tendsto_matrix_inv hM hω
  have hK : Tendsto (fun n => kHat b E (regX X n)) atTop (𝓝 (kHat b E X)) :=
    ((continuous_kHat b E).tendsto X).comp (tendsto_regX X)
  have hP := hK.prodMk_nhds hG
  have hc := (continuous_wordForm₂ (n := LayerSite W .oneBlockOnePort) a c wd D).tendsto
    (kHat b E X, gRes b E X ω)
  refine (hc.comp hP).congr fun n => ?_
  rfl

/-- Cauchy–Schwarz from two variance bounds. -/
theorem norm_cov_le_of_var {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {P Q : Ω → ℂ} (hP : MemLp P 2 μ) (hQ : MemLp Q 2 μ) {K α β : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hvP : ∫ ω, ‖P ω - ∫ ω', P ω' ∂μ‖ ^ 2 ∂μ ≤ K * α ^ 2)
    (hvQ : ∫ ω, ‖Q ω - ∫ ω', Q ω' ∂μ‖ ^ 2 ∂μ ≤ K * β ^ 2) :
    Integrable (fun ω => (P ω - ∫ ω', P ω' ∂μ) * (Q ω - ∫ ω', Q ω' ∂μ)) μ ∧
      ‖∫ ω, (P ω - ∫ ω', P ω' ∂μ) * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ‖ ≤ K * (α * β) := by
  have hu : MemLp (fun ω => P ω - ∫ ω', P ω' ∂μ) 2 μ := hP.sub (memLp_const _)
  have hw : MemLp (fun ω => Q ω - ∫ ω', Q ω' ∂μ) 2 μ := hQ.sub (memLp_const _)
  refine ⟨hu.integrable_mul hw, ?_⟩
  have hH := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
    (by simpa using hu) (by simpa using hw)
  have e2 : ∀ x : ℝ, 0 ≤ x → x ^ (2 : ℝ) = x ^ 2 := fun x _ => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [e2 _ (norm_nonneg _)] at hH
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
  have hs1 : Real.sqrt (∫ ω, ‖P ω - ∫ ω', P ω' ∂μ‖ ^ 2 ∂μ) ≤ Real.sqrt K * α := by
    rw [← Real.sqrt_sq hα, ← Real.sqrt_mul hK]; exact Real.sqrt_le_sqrt hvP
  have hs2 : Real.sqrt (∫ ω, ‖Q ω - ∫ ω', Q ω' ∂μ‖ ^ 2 ∂μ) ≤ Real.sqrt K * β := by
    rw [← Real.sqrt_sq hβ, ← Real.sqrt_mul hK]; exact Real.sqrt_le_sqrt hvQ
  calc ‖∫ ω, (P ω - ∫ ω', P ω' ∂μ) * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ‖
      ≤ ∫ ω, ‖P ω - ∫ ω', P ω' ∂μ‖ * ‖Q ω - ∫ ω', Q ω' ∂μ‖ ∂μ := by
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        congr 1; funext ω; exact norm_mul _ _
    _ ≤ Real.sqrt K * α * (Real.sqrt K * β) :=
        hH.trans (mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (by positivity))
    _ = (Real.sqrt K * Real.sqrt K) * (α * β) := by ring
    _ = K * (α * β) := by rw [Real.mul_self_sqrt hK]

/-- **The general bilinear variance bound for every passive input** (`Y ⪰ 0`):
the constants of `wordForm_variance`, uniformly in passive `X`. -/
theorem wordForm_variance_psd (hP : GaussianPoincare) (hA : PassiveBoundsStatement) {b E : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4)
      (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) →
      ∀ a c : LayerSite W .oneBlockOnePort → ℂ,
        MemLp (fun ω => wordForm (kHat b E X) a c wd D (gRes b E X ω)) 2
            (layerLaw W b .oneBlockOnePort) ∧
        ∫ ω, ‖wordForm (kHat b E X) a c wd D (gRes b E X ω) -
            ∫ ω', wordForm (kHat b E X) a c wd D (gRes b E X ω') ∂layerLaw W b .oneBlockOnePort‖ ^ 2
          ∂layerLaw W b .oneBlockOnePort ≤ C / W * (vecNorm a ^ 2 * vecNorm c ^ 2) := by
  obtain ⟨C, W₁, hC, hstrict⟩ := wordForm_variance hP hA hb0 hb h1 h2 Lw Kd
  obtain ⟨Cb, Wb, hCb, hmom⟩ := btFun_moment hA hb0 hb h1 h2 (2 * ((Lw + 1 : ℕ) : ℝ)) (by
    have : (1 : ℝ) ≤ ((Lw + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ Lw + 1 by omega)
    linarith)
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨_, Wm, hmoments⟩ := hA.moments b hb0 hb _ hκ 1 le_rfl
  refine ⟨C, max (max W₁ Wb) Wm, hC, fun W hW X hX ℓ hℓ wd D hD a c => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWb : Wb ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWm : Wm ≤ W := le_trans (le_max_right _ _) hW
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD 0)
  set μ := layerLaw W b .oneBlockOnePort
  set Fn : ℕ → LayerSample W .oneBlockOnePort → ℂ := fun n ω =>
    wordForm (kHat b E (regX X n)) a c wd D (gRes b E (regX X n) ω)
  set F : LayerSample W .oneBlockOnePort → ℂ := fun ω =>
    wordForm (kHat b E X) a c wd D (gRes b E X ω)
  set Kb : ℝ≥0∞ := ENNReal.ofReal (max Kd 1 ^ (Lw + 1) * (vecNorm a * vecNorm c)) *
    ENNReal.ofReal Cb ^ (Lw + 1)
  have hKb : Kb ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hQ : 0 ≤ max Kd 1 ^ (Lw + 1) * (vecNorm a * vecNorm c) :=
    mul_nonneg (by positivity) (mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _))
  have hbd : ∀ X' : Matrix (Fin W) (Fin W) ℂ, (passiveY X').PosSemidef →
      eLpNorm (fun ω => wordForm (kHat b E X') a c wd D (gRes b E X' ω)) 2 μ ≤ Kb := fun X' hX' =>
    eLpNorm_two_le_of_pow_bound (g := fun ω => 1 + btFun b E X' ω)
      (measurable_wordForm _ a c wd D (measurable_layerRes E (boundaryZ b E) X')).aestronglyMeasurable
      (fun ω => by have := btFun_nonneg b E X' ω; positivity)
      (measurable_const.add (measurable_btFun b E X')).aestronglyMeasurable hQ (Lw + 1) (by omega)
      (fun ω => (wordForm_poly_bounds b E X' hKd hℓ wd D hD a c ω).1) (hmom W hWb X' hX')
  have hFn : ∀ n, MemLp (Fn n) 2 μ := fun n =>
    lt_of_le_of_lt (hbd _ (passiveY_regX_posSemidef hX n)) hKb.lt_top
  have hF : MemLp F 2 μ := lt_of_le_of_lt (hbd X hX) hKb.lt_top
  refine ⟨hF, ?_⟩
  have hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Fn n ω) atTop (𝓝 (F ω)) := by
    filter_upwards [(hmoments W hWm E (mem_bulkInterval_min E) _
      (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX).1] with ω hω
    exact tendsto_wordForm_regX b E X a c wd D ω hω
  have hFnm : ∀ n, Measurable (Fn n) := fun n =>
    measurable_wordForm _ a c wd D (measurable_layerRes E (boundaryZ b E) (regX X n))
  have hFm : Measurable F := measurable_wordForm _ a c wd D (measurable_layerRes E (boundaryZ b E) X)
  have hint : Tendsto (fun n => ∫ ω, Fn n ω ∂μ) atTop (𝓝 (∫ ω, F ω ∂μ)) :=
    tendsto_integral_of_ae_of_eLpNorm_two hFnm hKb
      (fun n => hbd _ (passiveY_regX_posSemidef hX n)) (hbd X hX) hae
  set B := C / W * (vecNorm a ^ 2 * vecNorm c ^ 2)
  set f : ℕ → LayerSample W .oneBlockOnePort → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal (‖Fn n ω - ∫ ω', Fn n ω' ∂μ‖ ^ 2)
  have hfm : ∀ n, AEMeasurable (f n) μ := fun n =>
    (ENNReal.measurable_ofReal.comp (((hFnm n).sub_const _).norm.pow_const 2)).aemeasurable
  have hlim : ∀ᵐ ω ∂μ, liminf (fun n => f n ω) atTop =
      ENNReal.ofReal (‖F ω - ∫ ω', F ω' ∂μ‖ ^ 2) := by
    filter_upwards [hae] with ω hω
    exact ((ENNReal.continuous_ofReal.tendsto _).comp ((hω.sub hint).norm.pow 2)).liminf_eq
  have hfn : ∀ n, ∫⁻ ω, f n ω ∂μ ≤ ENNReal.ofReal B := fun n => by
    have hi : Integrable (fun ω => ‖Fn n ω - ∫ ω', Fn n ω' ∂μ‖ ^ 2) μ :=
      ((hFn n).sub (memLp_const _)).norm.integrable_sq
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hstrict W hW1 (regX X n) (passiveY_regX_posDef hX n) ℓ hℓ
      wd D hD a c).2
  have hfatou := lintegral_liminf_le' (μ := μ) (u := atTop) hfm
  rw [lintegral_congr_ae hlim] at hfatou
  have hle : ∫⁻ ω, ENNReal.ofReal (‖F ω - ∫ ω', F ω' ∂μ‖ ^ 2) ∂μ ≤ ENNReal.ofReal B :=
    hfatou.trans ((Filter.liminf_le_liminf (Eventually.of_forall hfn)).trans
      (le_of_eq (Filter.liminf_const (ENNReal.ofReal B))))
  have hB : 0 ≤ B := by positivity
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
    ((hFm.sub_const _).norm.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hB hle

/-- **The general bilinear covariance bound for every passive input**:
`|Cov(a₁*w₁c₁, a₂*w₂c₂)| ≤ (C/W)‖a₁‖‖c₁‖‖a₂‖‖c₂‖`, uniformly in passive `X`. -/
theorem wordForm_covariance_psd (hP : GaussianPoincare) (hA : PassiveBoundsStatement) {b E : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
      ∀ ℓ₁ : ℕ, ℓ₁ ≤ Lw → ∀ (wd₁ : Fin ℓ₁ → Fin 4) (D₁ : Fin (ℓ₁ + 1) → LayerMat W),
      (∀ j, ‖D₁ j‖ ≤ Kd) →
      ∀ ℓ₂ : ℕ, ℓ₂ ≤ Lw → ∀ (wd₂ : Fin ℓ₂ → Fin 4) (D₂ : Fin (ℓ₂ + 1) → LayerMat W),
      (∀ j, ‖D₂ j‖ ≤ Kd) → ∀ a₁ c₁ a₂ c₂ : LayerSite W .oneBlockOnePort → ℂ,
        let μ := layerLaw W b .oneBlockOnePort
        let P := fun ω => wordForm (kHat b E X) a₁ c₁ wd₁ D₁ (gRes b E X ω)
        let Q := fun ω => wordForm (kHat b E X) a₂ c₂ wd₂ D₂ (gRes b E X ω)
        Integrable (fun ω => (P ω - ∫ ω', P ω' ∂μ) * (Q ω - ∫ ω', Q ω' ∂μ)) μ ∧
        ‖∫ ω, (P ω - ∫ ω', P ω' ∂μ) * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ‖ ≤
          C / W * (vecNorm a₁ * vecNorm c₁ * (vecNorm a₂ * vecNorm c₂)) := by
  obtain ⟨C, W₀, hC, hv⟩ := wordForm_variance_psd hP hA hb0 hb h1 h2 Lw Kd
  refine ⟨C, W₀, hC, fun W hW X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ ℓ₂ hℓ₂ wd₂ D₂ hD₂ a₁ c₁ a₂ c₂ => ?_⟩
  intro μ P Q
  obtain ⟨hP2, hPv⟩ := hv W hW X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ a₁ c₁
  obtain ⟨hQ2, hQv⟩ := hv W hW X hX ℓ₂ hℓ₂ wd₂ D₂ hD₂ a₂ c₂
  have hK : 0 ≤ C / W := by positivity
  exact norm_cov_le_of_var hP2 hQ2 hK (mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _))
    (mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)) (by simpa [mul_pow] using hPv)
    (by simpa [mul_pow] using hQv)

end BlockBand.Transmission.PassiveCovariance
