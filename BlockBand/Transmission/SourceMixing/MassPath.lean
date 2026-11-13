module

public import BlockBand.Transmission.SourceMixing.MassLayer
public import BlockBand.Transmission.SourceMixing.MixingPath

/-!
# Path tools for the mass-moment recursion

Fubini over one fresh layer of the growth path, and conversions between moments and `L^n` norms.

* `mp_integral_path_le`: Fubini over `pastLaw ⊗ freshLaw` for real integrals (the integral
  analogue of `mx_eLpNorm_path_le`): if `∫ Ψ(X,·) dfresh ≤ g(X)` for every passive `X`,
  `Ψ` is bounded and `g(X_j)` is integrable, then `E Ψ(X_j, fresh_j) ≤ E g(X_j)`.
* `mp_integral_pow_le`: `‖f‖_k ≤ σ` gives `∫ fᵏ ≤ σᵏ` for `f ≥ 0`, integer `k ≥ 1`.
* `mp_eLpNorm_le`: conversely, `0 ≤ f ≤ B` and `∫ fⁿ ≤ A` give `‖f‖_n ≤ A^{1/n}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder

variable {W : ℕ}

/-- Fubini over one fresh layer, integral form. -/
theorem mp_integral_path_le {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2)
    {Ψ : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort → ℝ} (hΨ : Measurable Ψ)
    {M : ℝ} (hΨM : ∀ x, ‖Ψ x‖ ≤ M) {g : Matrix (Fin W) (Fin W) ℂ → ℝ} (hg : Measurable g)
    (j : ℕ) (hgi : Integrable (fun ω => g (pathX b E W j ω)) (growthPathLaw W b))
    (hbd : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∫ ω, Ψ (X, ω) ∂freshLaw W b ≤ g X) :
    ∫ ω, Ψ (pathX b E W j ω, freshSample W j ω) ∂growthPathLaw W b ≤
      ∫ ω, g (pathX b E W j ω) ∂growthPathLaw W b := by
  set S := stepInput b E (fun _ => 0) W j
  have hS : Measurable S := measurable_stepInput b E _ j
  set Φ : PastSample W j × LayerSample W .oneBlockOnePort → ℝ := fun x => Ψ (S x.1, x.2)
  have hΦ : Measurable Φ := hΨ.comp ((hS.comp measurable_fst).prodMk measurable_snd)
  have hT := (measurable_pastCoords W j).prodMk (measurable_freshSample W j)
  have e1 : (fun ω => Ψ (pathX b E W j ω, freshSample W j ω)) =
      Φ ∘ fun ω => (pastCoords W j ω, freshSample W j ω) := by
    funext ω; simp only [Function.comp, Φ, S, PathJet.stepInput_zero]
  have e2 : (fun ω => g (pathX b E W j ω)) = (g ∘ S) ∘ pastCoords W j := by
    funext ω; simp only [Function.comp, S, PathJet.stepInput_zero]
  rw [e2] at hgi
  have hgS : Integrable (g ∘ S) (pastLaw W j b) := by
    have := (integrable_map_measure (hg.comp hS).aestronglyMeasurable
      (measurable_pastCoords W j).aemeasurable).2 hgi
    rwa [growthPathLaw_map_pastCoords] at this
  have hΦi : Integrable Φ ((pastLaw W j b).prod (freshLaw W b)) :=
    Integrable.of_bound hΦ.aestronglyMeasurable M (ae_of_all _ fun x => hΨM _)
  have m1 : ∫ ω, Φ (pastCoords W j ω, freshSample W j ω) ∂growthPathLaw W b =
      ∫ x, Φ x ∂((pastLaw W j b).prod (freshLaw W b)) := by
    rw [← growthPathLaw_map_past_fresh]
    exact (integral_map hT.aemeasurable hΦ.aestronglyMeasurable).symm
  have m2 : ∫ ω, (g ∘ S) (pastCoords W j ω) ∂growthPathLaw W b = ∫ x, (g ∘ S) x ∂pastLaw W j b := by
    rw [← growthPathLaw_map_pastCoords]
    exact (integral_map (measurable_pastCoords W j).aemeasurable
      (hg.comp hS).aestronglyMeasurable).symm
  rw [e1, e2]
  change ∫ ω, Φ (pastCoords W j ω, freshSample W j ω) ∂growthPathLaw W b ≤
    ∫ ω, (g ∘ S) (pastCoords W j ω) ∂growthPathLaw W b
  rw [m1, m2, integral_prod Φ hΦi]
  refine integral_mono_ae hΦi.integral_prod_left hgS ?_
  filter_upwards [ae_pastLaw_hermitian W j b] with x hx
  exact hbd (S x) (passiveY_stepInput hb h1 h2 (fun _ => le_rfl) hx)

/-- `‖f‖_k ≤ σ` gives `∫ fᵏ ≤ σᵏ` (`f ≥ 0` a.e., integer `k ≥ 1`). -/
theorem mp_integral_pow_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) (k : ℕ) (hk : 1 ≤ k) {σ : ℝ} (hσ : 0 ≤ σ)
    (h : eLpNorm f (ENNReal.ofReal (k : ℝ)) μ ≤ ENNReal.ofReal σ) :
    ∫ ω, f ω ^ k ∂μ ≤ σ ^ k := by
  rw [ENNReal.ofReal_natCast] at h
  have hmem : MemLp f k μ := h.trans_lt ENNReal.ofReal_lt_top
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [hmem.eLpNorm_eq_integral_rpow_norm hk0 ENNReal.coe_ne_top,
    ENNReal.ofReal_le_ofReal_iff hσ] at h
  have hkr : ((k : ℝ≥0∞)).toReal = (k : ℝ) := by simp
  rw [hkr] at h
  set I := ∫ a, ‖f a‖ ^ (k : ℝ) ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => by positivity
  have hIk : I ≤ σ ^ k := by
    have h' := pow_le_pow_left₀ (by positivity) h k
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hI0, inv_mul_cancel₀ (by exact_mod_cast
      (show k ≠ 0 by omega)), Real.rpow_one] at h'
  have hIeq : ∫ ω, f ω ^ k ∂μ = I := by
    rw [hI]
    refine integral_congr_ae ?_
    filter_upwards [hf0] with ω hω
    rw [Real.rpow_natCast, Real.norm_of_nonneg hω]
  rw [hIeq]; exact hIk

/-- `0 ≤ f ≤ B` and `∫ fⁿ ≤ A` give `‖f‖_n ≤ A^{1/n}`. -/
theorem mp_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hf0 : ∀ ω, 0 ≤ f ω) {B : ℝ}
    (hfB : ∀ ω, f ω ≤ B) (n : ℕ) (hn : 1 ≤ n) {A : ℝ} (hI : ∫ ω, f ω ^ n ∂μ ≤ A) :
    eLpNorm f n μ ≤ ENNReal.ofReal (A ^ (n : ℝ)⁻¹) := by
  have hmem : MemLp f n μ := MemLp.of_bound hf B (ae_of_all _ fun ω => by
    rw [Real.norm_of_nonneg (hf0 ω)]; exact hfB ω)
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [hmem.eLpNorm_eq_integral_rpow_norm hn0 ENNReal.coe_ne_top]
  have hnr : ((n : ℝ≥0∞)).toReal = (n : ℝ) := by simp
  rw [hnr]
  have heq : ∫ a, ‖f a‖ ^ (n : ℝ) ∂μ = ∫ ω, f ω ^ n ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [Real.rpow_natCast, Real.norm_of_nonneg (hf0 ω)]
  rw [heq]
  have h0 : 0 ≤ ∫ ω, f ω ^ n ∂μ := integral_nonneg fun ω => pow_nonneg (hf0 ω) n
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow h0 hI (by positivity))

end BlockBand.Transmission.SourceMixing
