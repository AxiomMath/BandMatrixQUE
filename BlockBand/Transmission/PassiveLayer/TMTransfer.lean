module

public import BlockBand.Transmission.PassiveLayer.TMFixed

/-!
# The regularized covariance bound under `freshLaw`

* `lbar E w X ω = 1 + ‖𝒢‖ + ‖K𝒢₁₁‖ + ‖L‖` (the moment weight of `moments`), and
  `lam_le_lbar`: `Λ(K, 𝒢) ≤ lbar` (`‖Kι₁𝒢‖ ≤ ‖K𝒢₁₁‖ + ‖L‖`, `norm_pK_mul_le`).
* `measurable_passiveWord`, `matrixExpect_eq_coord` (entrywise expectation under
  `freshLaw = (gaussianProduct v).map coordMap` is the Bochner integral in the coordinates).
* `tm_cov_reg_fresh`: for passive `X` and `ε > 0`, with `X_ε = X - iε` and the words of the
  `traceMatrix` clause at `X_ε`,
  `‖E(fU) - E f E U‖ ≤ (3 ℓ_f ℓ_U K_d^n / W²) · 2 E lbar(X_ε)^n` under `freshLaw W b`,
  `n = ℓ_f + ℓ_U + 2`, given integrability of `lbar(X_ε)^n` (supplied by `moments`).
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

/-- The moment weight `1 + ‖𝒢‖ + ‖K𝒢₁₁‖ + ‖L‖`. -/
def lbar (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    ℝ :=
  1 + ‖layerAt E w X ω‖ + ‖kG11 E w X ω‖ + ‖lAt E w X ω‖

theorem one_le_lbar (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : 1 ≤ lbar E w X ω := by
  unfold lbar
  linarith [norm_nonneg (layerAt E w X ω), norm_nonneg (kG11 E w X ω), norm_nonneg (lAt E w X ω)]

theorem lbar_nonneg (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : 0 ≤ lbar E w X ω :=
  zero_le_one.trans (one_le_lbar E w X ω)

theorem lam_le_lbar (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : lam (w • 1 - X) (layerAt E w X ω) ≤ lbar E w X ω := by
  have h := norm_pK_mul_le E w X ω
  rw [pK] at h
  unfold lam lbar
  linarith

theorem measurable_lbar (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (lbar E w X) := by
  have h1 := (measurable_layerAt E w X).norm
  have h2 := (measurable_kG11 E w X).norm
  have h3 := (measurable_lAt E w X).norm
  exact ((measurable_const.add h1).add h2).add h3

theorem measurable_passiveWord (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) {ℓ : ℕ}
    (wd : Fin ℓ → Fin 6 × Bool) (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ) :
    Measurable (passiveWord E w X wd D) := by
  have e : passiveWord E w X wd D = (fun G => tmWord (w • 1 - X) wd D G) ∘ layerAt E w X := by
    funext ω; exact passiveWord_eq E w X wd D ω
  rw [e]
  exact ((continuous_tmWord wd D).comp (continuous_const.prodMk continuous_id)).measurable.comp
    (measurable_layerAt E w X)

theorem continuous_tmWord_comp {α : Type*} [TopologicalSpace α]
    {G : α → Matrix (LS W) (LS W) ℂ} (hG : Continuous G) (K : Matrix (Fin W) (Fin W) ℂ) {ℓ : ℕ}
    (wd : Fin ℓ → Fin 6 × Bool) (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ) :
    Continuous (fun x => tmWord K wd D (G x)) := by
  have h := (continuous_tmWord wd D).comp (Continuous.prodMk (continuous_const (y := K)) hG)
  exact h

/-- Entry functional on `W × W` matrices as an `ℝ`-continuous linear map. -/
def entryR (x y : Fin W) : Matrix (Fin W) (Fin W) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun N => N x y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Entrywise expectation under `freshLaw` is the Bochner integral in the coordinates. -/
theorem matrixExpect_eq_coord {b : ℝ}
    {Y : LayerSample W .oneBlockOnePort → Matrix (Fin W) (Fin W) ℂ} (hY : Measurable Y)
    (hint : Integrable (fun x => Y (coordMap W b x)) (gaussianProduct (coordVar W b))) :
    matrixExpect (freshLaw W b) Y = ∫ x, Y (coordMap W b x) ∂gaussianProduct (coordVar W b) := by
  ext x y
  have hm : Measurable (fun ω => Y ω x y) :=
    (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hY)
  simp only [matrixExpect, of_apply]
  rw [freshLaw_eq_map, integral_map (measurable_coordMap W b).aemeasurable hm.aestronglyMeasurable]
  exact ContinuousLinearMap.integral_comp_comm (entryR x y) hint

theorem integrable_of_bdd_cont {ι : Type} [Fintype ι] (v : ι → ℝ≥0) {F : Type*}
    [NormedAddCommGroup F] {g : (ι → ℝ) → F} (hg : Continuous g) {C : ℝ} (h : ∀ x, ‖g x‖ ≤ C) :
    Integrable g (gaussianProduct v) :=
  Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall h)

/-- **The covariance bound at the regularized input `X - iε`, under `freshLaw`.** -/
theorem tm_cov_reg_fresh {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) {w : ℂ}
    (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ}
    (hε : 0 < ε) {Kd : ℝ} (hKd : 0 ≤ Kd) {ℓf ℓU : ℕ}
    (wf : Fin ℓf → Fin 6 × Bool) (Df : Fin (ℓf + 1) → Matrix (Fin W) (Fin W) ℂ)
    (wU : Fin ℓU → Fin 6 × Bool) (DU : Fin (ℓU + 1) → Matrix (Fin W) (Fin W) ℂ)
    (hDf : ∀ j, ‖Df j‖ ≤ Kd) (hDU : ∀ j, ‖DU j‖ ≤ Kd)
    (hint : Integrable (fun ω => lbar E w (regX X ε) ω ^ (ℓf + ℓU + 2)) (freshLaw W b)) :
    ‖matrixExpect (freshLaw W b) (fun ω => ((W : ℂ)⁻¹ *
          (passiveWord E w (regX X ε) wf Df ω).trace) • passiveWord E w (regX X ε) wU DU ω) -
        (∫ ω, (W : ℂ)⁻¹ * (passiveWord E w (regX X ε) wf Df ω).trace ∂freshLaw W b) •
          matrixExpect (freshLaw W b) (passiveWord E w (regX X ε) wU DU)‖ ≤
      3 * ℓf * ℓU * Kd ^ (ℓf + ℓU + 2) / (W : ℝ) ^ 2 *
        (2 * ∫ ω, lbar E w (regX X ε) ω ^ (ℓf + ℓU + 2) ∂freshLaw W b) := by
  set μ := gaussianProduct (coordVar W b) with hμ
  set K := w • (1 : Matrix (Fin W) (Fin W) ℂ) - regX X ε with hK
  set G := gReg E w b X ε with hG
  set n := ℓf + ℓU + 2 with hn
  have hGc := gReg_contDiff E hw b hY hε
  have hGle := norm_gReg_le E hw b hY hε
  have h := tm_cov_of hb0 hb hW K hGc hGle (gReg_hasFDerivAt E hw b hY hε) hKd wf Df wU DU hDf hDU
  have hGx : ∀ x, layerAt E w (regX X ε) (coordMap W b x) = G x := fun x => rfl
  have hwd : ∀ {ℓ : ℕ} (wd : Fin ℓ → Fin 6 × Bool) (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ)
      (x : CoordW W → ℝ), passiveWord E w (regX X ε) wd D (coordMap W b x) = tmWord K wd D (G x) := by
    intro ℓ wd D x
    rw [passiveWord_eq, hGx]
  set R := (min ε w.im)⁻¹ with hRdef
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hGle 0)
  set Lb := 1 + R + ‖K * iota1 W‖ * R with hLb
  have hlam : ∀ x, lam K (G x) ≤ Lb := fun x => lam_le_of_norm_le K (hGle x)
  have hlam0 : ∀ x, 0 ≤ lam K (G x) := fun x => zero_le_one.trans (one_le_lam K (G x))
  have hwb : ∀ {ℓ : ℕ} (wd : Fin ℓ → Fin 6 × Bool) (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ),
      (∀ j, ‖D j‖ ≤ Kd) → ∀ x, ‖tmWord K wd D (G x)‖ ≤ Kd ^ (ℓ + 1) * Lb ^ ℓ := by
    intro ℓ wd D hD x
    exact (norm_tmWord_le K hKd wd D (G x) hD).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hlam0 x) (hlam x) ℓ) (by positivity))
  have hcw : ∀ {ℓ : ℕ} (wd : Fin ℓ → Fin 6 × Bool) (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ),
      Continuous (fun x => tmWord K wd D (G x)) := fun wd D =>
    continuous_tmWord_comp hGc.continuous K wd D
  have hiU : Integrable (fun x => tmWord K wU DU (G x)) μ :=
    integrable_of_bdd_cont _ (hcw wU DU) (hwb wU DU hDU)
  have hifU : Integrable (fun x => tmTr W (tmWord K wf Df (G x)) • tmWord K wU DU (G x)) μ := by
    refine integrable_of_bdd_cont _ (((tmTr W).continuous.comp (hcw wf Df)).smul (hcw wU DU))
      (C := (Kd ^ (ℓf + 1) * Lb ^ ℓf) * (Kd ^ (ℓU + 1) * Lb ^ ℓU)) fun x => ?_
    rw [norm_smul]
    exact mul_le_mul ((norm_tmTr_le _).trans (hwb wf Df hDf x)) (hwb wU DU hDU x)
      (norm_nonneg _) (by positivity)
  have hmf := measurable_passiveWord E w (regX X ε) wf Df
  have hmU := measurable_passiveWord E w (regX X ε) wU DU
  have hmtr : Measurable (fun ω => (W : ℂ)⁻¹ * (passiveWord E w (regX X ε) wf Df ω).trace) :=
    measurable_const.mul ((Continuous.matrix_trace continuous_id).measurable.comp hmf)
  have hpt1 : ∀ x, tmTr W (tmWord K wf Df (G x)) • tmWord K wU DU (G x) =
      ((W : ℂ)⁻¹ * (passiveWord E w (regX X ε) wf Df (coordMap W b x)).trace) •
        passiveWord E w (regX X ε) wU DU (coordMap W b x) := fun x => by
    rw [hwd, hwd, tmTr_apply]
  have hfun3 : (fun x => (W : ℂ)⁻¹ * (passiveWord E w (regX X ε) wf Df (coordMap W b x)).trace) =
      fun x => tmTr W (tmWord K wf Df (G x)) := by
    funext x; rw [hwd, tmTr_apply]
  have e1 := matrixExpect_eq_coord (b := b)
    (Y := fun ω => ((W : ℂ)⁻¹ * (passiveWord E w (regX X ε) wf Df ω).trace) •
      passiveWord E w (regX X ε) wU DU ω) (hmtr.smul hmU)
    (hifU.congr (Eventually.of_forall hpt1))
  have e2 := matrixExpect_eq_coord (b := b) hmU
    (hiU.congr (Eventually.of_forall fun x => (hwd wU DU x).symm))
  rw [← integral_congr_ae (Eventually.of_forall hpt1)] at e1
  rw [← integral_congr_ae (Eventually.of_forall fun x => (hwd wU DU x).symm)] at e2
  have e3 : ∫ ω, (W : ℂ)⁻¹ * (passiveWord E w (regX X ε) wf Df ω).trace ∂freshLaw W b =
      ∫ x, tmTr W (tmWord K wf Df (G x)) ∂μ := by
    rw [freshLaw_eq_map, integral_map (measurable_coordMap W b).aemeasurable
      hmtr.aestronglyMeasurable, hfun3]
  have e4 : ∫ ω, lbar E w (regX X ε) ω ^ n ∂freshLaw W b =
      ∫ x, lbar E w (regX X ε) (coordMap W b x) ^ n ∂μ := by
    rw [freshLaw_eq_map, integral_map (measurable_coordMap W b).aemeasurable
      ((measurable_lbar E w (regX X ε)).pow_const n).aestronglyMeasurable]
  rw [e1, e2, e3, e4]
  refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    (by positivity))
  have hint' : Integrable (fun x => lbar E w (regX X ε) (coordMap W b x) ^ n) μ := by
    rw [freshLaw_eq_map] at hint
    exact (integrable_map_measure ((measurable_lbar E w (regX X ε)).pow_const n).aestronglyMeasurable
      (measurable_coordMap W b).aemeasurable).mp hint
  refine integral_mono (integrable_of_bdd_cont _ (((continuous_lam K).comp hGc.continuous).pow n)
    (C := Lb ^ n) fun x => ?_) hint' fun x => ?_
  · rw [Real.norm_of_nonneg (pow_nonneg (hlam0 x) n)]
    exact pow_le_pow_left₀ (hlam0 x) (hlam x) n
  · have := lam_le_lbar E w (regX X ε) (coordMap W b x)
    rw [hGx] at this
    exact pow_le_pow_left₀ (hlam0 x) this n

end BlockBand.Transmission.PassiveLayer
