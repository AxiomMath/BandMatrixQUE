module

public import BlockBand.SourceProcess.RawTag.JointLaw
public import BlockBand.SourceProcess.RawTag.KhintchineVec
public import BlockBand.SourceProcess.RawTag.DeltaBounds
public import BlockBand.SourceProcess.ComplexSourceLaw.Measurability

/-!
# Moment bookkeeping on `GrowthPath W × Γ`

Transfer of moment bounds `MomBd` between `L^p` norms and integrals and between the factors of a
product measure, the fresh-layer Fubini for functions of the past and the fresh layer, and the
moments of `‖Δ_l‖` and of `‖W^{-1/2}g‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer BlockBand.SourceProcess.FullSource
open BlockBand.Transmission.PassiveCovariance
open scoped Matrix ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

/-- From an `L^p` bound to the `p`-th moment. -/
theorem lintegral_rpow_le_of_momBd {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {p C : ℝ} (hf : MomBd μ f p C) (hp : 0 < p) (hC : 0 ≤ C) :
    ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ ≤ ENNReal.ofReal (C ^ p) := by
  have h := hf.2
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hf.1,
    ENNReal.toReal_ofReal hp.le] at h
  have h' := ENNReal.rpow_le_rpow h hp.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hC hp.le] at h'
  refine le_of_eq_of_le (lintegral_congr fun x => ?_) h'
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]

/-- A bound under `μ` is a bound under `μ ⊗ ν` for functions of the first factor. -/
theorem MomBd.comp_fst {α Γ : Type*} [MeasurableSpace α] [MeasurableSpace Γ] {μ : Measure α}
    [SFinite μ] {ν : Measure Γ} [IsProbabilityMeasure ν] {f : α → ℝ} {p C : ℝ}
    (hf : MomBd μ f p C) : MomBd (μ.prod ν) (fun w => f w.1) p C := by
  have hmp : MeasurePreserving Prod.fst (μ.prod ν) μ := measurePreserving_fst
  refine ⟨hf.1.comp_measurePreserving hmp, ?_⟩
  rw [show (fun w : α × Γ => f w.1) = f ∘ Prod.fst from rfl,
    eLpNorm_comp_measurePreserving hf.1 hmp]
  exact hf.2

/-- A bound under `ν` is a bound under `μ ⊗ ν` for functions of the second factor. -/
theorem MomBd.comp_snd {α Γ : Type*} [MeasurableSpace α] [MeasurableSpace Γ] {μ : Measure α}
    [IsProbabilityMeasure μ] {ν : Measure Γ} [SFinite ν] {f : Γ → ℝ} {p C : ℝ}
    (hf : MomBd ν f p C) : MomBd (μ.prod ν) (fun w => f w.2) p C := by
  have hmp : MeasurePreserving Prod.snd (μ.prod ν) ν := measurePreserving_snd
  refine ⟨hf.1.comp_measurePreserving hmp, ?_⟩
  rw [show (fun w : α × Γ => f w.2) = f ∘ Prod.snd from rfl,
    eLpNorm_comp_measurePreserving hf.1 hmp]
  exact hf.2

/-- **Fresh-layer Fubini** for functions of the past coordinates and the fresh layer. -/
theorem lintegral_past_fresh (W l : ℕ) (b : ℝ)
    {Φ : PastSample W l → LayerSample W .oneBlockOnePort → ℝ≥0∞}
    (hΦ : Measurable fun z : PastSample W l × LayerSample W .oneBlockOnePort => Φ z.1 z.2) :
    ∫⁻ ω, Φ (pastCoords W l ω) (freshSample W l ω) ∂growthPathLaw W b =
      ∫⁻ q, ∫⁻ f, Φ q f ∂freshLaw W b ∂pastLaw W l b := by
  have hm : Measurable fun ω : GrowthPath W => (pastCoords W l ω, freshSample W l ω) :=
    (measurable_pastCoords W l).prodMk (measurable_freshSample W l)
  rw [← lintegral_prod _ hΦ.aemeasurable, ← growthPathLaw_map_past_fresh W l b,
    lintegral_map hΦ hm]

/-- **Moments of `‖Δ_l‖`** on the growth path (uniform over the step `l`). -/
theorem momBd_stepDelta (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) {r : ℝ} (hr : 1 ≤ r) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ l : ℕ,
      MomBd (growthPathLaw W b) (fun ω => ‖stepDelta b E W l ω‖) r C := by
  obtain ⟨C, W₀, hC, h⟩ := delta_moments hGA b hb0 hb κ hκ r hr
  refine ⟨C, W₀, hC, fun W hW E hE l => ?_⟩
  have hE' := hE
  obtain ⟨hE1, hE2⟩ := hE'
  have hκ2 : κ ≤ 2 := by linarith
  have hr0 : 0 < r := by linarith
  set ψ : PastSample W l × LayerSample W .oneBlockOnePort → ℝ :=
    fun z => ‖freshDelta b E (pastX b E (fun _ => 0) W l z.1) z.2‖ with hψ
  have hψm : Measurable ψ :=
    (measurable_freshDelta_comp b E ((measurable_pastX b E _ l).comp measurable_fst)
      measurable_snd).norm
  have hPF : Measurable fun ω : GrowthPath W => (pastCoords W l ω, freshSample W l ω) :=
    (measurable_pastCoords W l).prodMk (measurable_freshSample W l)
  have hfun : (fun ω => ‖stepDelta b E W l ω‖) =
      ψ ∘ fun ω => (pastCoords W l ω, freshSample W l ω) := by
    funext ω
    simp only [Function.comp, hψ, stepDelta, pathX, pathNearSchur_eq_past]
  rw [hfun]
  have hmap := growthPathLaw_map_past_fresh W l b
  have hbd : MomBd ((pastLaw W l b).prod (freshLaw W b)) ψ r C := by
    have hint : ∫⁻ z, ‖ψ z‖ₑ ^ r ∂((pastLaw W l b).prod (freshLaw W b)) ≤
        ENNReal.ofReal (C ^ r) := by
      rw [lintegral_prod _ (hψm.enorm.pow_const r).aemeasurable]
      have hq : ∀ᵐ q ∂pastLaw W l b, ∫⁻ f, ‖ψ (q, f)‖ₑ ^ r ∂freshLaw W b ≤
          ENNReal.ofReal (C ^ r) := by
        filter_upwards [ae_pastLaw_hermitian W l b] with q hq
        have hY := passiveY_pastX (b := b) (E := E) (by linarith) (by linarith) (by linarith)
          (fun _ => le_rfl) hq
        have := lintegral_rpow_le_of_momBd (h W hW E hE _ hY) hr0 hC
        refine le_of_eq_of_le (lintegral_congr fun f => ?_) this
        rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hr0.le]
      have := isProbabilityMeasure_pastLaw W l b
      refine (lintegral_mono_ae hq).trans (le_of_eq ?_)
      rw [lintegral_const, measure_univ, mul_one]
    have h1 := MomBd.of_lintegral hψm.aestronglyMeasurable hr0 (by positivity) hint
    rwa [← Real.rpow_mul hC, mul_one_div_cancel hr0.ne', Real.rpow_one] at h1
  refine ⟨(hψm.comp hPF).aestronglyMeasurable, ?_⟩
  rw [← eLpNorm_map_measure (hmap ▸ hbd.1) hPF.aemeasurable, hmap]
  exact hbd.2

/-- **Moments of `‖W^{-1/2}g‖`** for a standard circular vector. -/
theorem momBd_unitVec {r : ℝ} (hr : 2 ≤ r) (W : ℕ) (hW : 1 ≤ W) :
    MomBd (circularVectorLaw (Fin W)) (fun g => vecNorm (unitVec W g)) r
      ((2 * gaussMoment r) ^ (1 / r)) := by
  have hr0 : 0 < r := by linarith
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hm : Measurable fun g : Fin W → ℂ => vecNorm (unitVec W g) := by
    unfold vecNorm unitVec; fun_prop
  refine MomBd.of_lintegral hm.aestronglyMeasurable hr0
    (mul_nonneg (by norm_num) (gaussMoment_nonneg r)) ?_
  have hK := lintegral_normSq_rpow_le (W := W) (1 : Matrix (Fin W) (Fin W) ℂ)
    (r := r / 2) (by linarith)
  have hS : ∑ x : Fin W, ∑ a : Fin W, ‖(1 : Matrix (Fin W) (Fin W) ℂ) x a‖ ^ 2 = W := by
    have e1 : ∀ x a : Fin W, ‖(1 : Matrix (Fin W) (Fin W) ℂ) x a‖ ^ 2 = if x = a then 1 else 0 := by
      intro x a; by_cases h : x = a <;> simp [h, Matrix.one_apply]
    simp_rw [e1]; simp
  rw [hS, show 2 * (r / 2) = r by ring] at hK
  have e : ∀ g : Fin W → ℂ, ‖vecNorm (unitVec W g)‖ₑ ^ r =
      ENNReal.ofReal ((W : ℝ)⁻¹ ^ (r / 2)) *
        ENNReal.ofReal ((∑ x, ‖((1 : Matrix (Fin W) (Fin W) ℂ) *ᵥ g) x‖ ^ 2) ^ (r / 2)) := by
    intro g
    rw [Real.enorm_eq_ofReal (vecNorm_nonneg _), ENNReal.ofReal_rpow_of_nonneg (vecNorm_nonneg _)
      hr0.le, ← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow (by positivity)
      (by positivity), vecNorm, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    congr 1
    rw [show (1 / 2 : ℝ) * r = r / 2 by ring, one_mulVec, Finset.mul_sum]
    congr 2; funext a
    simp only [unitVec, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, one_div]
    rw [Real.sq_sqrt (inv_nonneg.mpr hWr.le)]
  simp_rw [e]
  rw [lintegral_const_mul _ (by fun_prop)]
  refine (mul_le_mul_right hK _).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_comm, mul_assoc, ← Real.mul_rpow (by positivity) (by positivity), mul_inv_cancel₀
    hWr.ne', Real.one_rpow, mul_one]

end BlockBand.SourceProcess.RawTag
