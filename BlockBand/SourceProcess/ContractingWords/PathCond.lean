module

public import BlockBand.Transmission.Bridge.Fresh
public import BlockBand.Transmission.PathScalar.AbsorbedStep
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditioning on the past: integration over the fresh layer

`μ = growthPathLaw W b`, `𝓕_j = growthSigma W j`,
`pc = pastCoords W j`, `fs = freshSample W j`; `(pc, fs)` has law `pastLaw ⊗ freshLaw`.

* `condExp_past_fresh`: for jointly measurable `Ψ` with `Ψ(pc, fs)` integrable,
  `E[Ψ(pc, fs) | 𝓕_j] = ∫ Ψ(pc, y) dfresh(y)` a.s. (the Lean form of "conditioning on the old
  path is integration over the fresh layer at a deterministic old state");
* `eLpNorm_indicator_fresh_le`: if `‖Ψ(x,·) - ∫Ψ(x,·)‖_{L^p(fresh)} ≤ B(x)` on a past event
  `A'`, then `‖1_{pc⁻¹A'}(Ψ(pc,fs) - ∫Ψ(pc,·))‖_{L^p(μ)} ≤ ‖1_{pc⁻¹A'}B(pc)‖_{L^p(μ)}` (Fubini).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar
open scoped ENNReal

variable {W : ℕ}

/-- **Conditional expectation over one fresh layer** (integrable, complex, past-dependent). -/
theorem condExp_past_fresh (b : ℝ) (j : ℕ)
    {Ψ : PastSample W j × LayerSample W .oneBlockOnePort → ℂ} (hΨ : Measurable Ψ)
    (hint : Integrable (fun ω => Ψ (pastCoords W j ω, freshSample W j ω)) (growthPathLaw W b)) :
    (growthPathLaw W b)[fun ω => Ψ (pastCoords W j ω, freshSample W j ω) | growthSigma W j] =ᵐ[
      growthPathLaw W b] fun ω => ∫ y, Ψ (pastCoords W j ω, y) ∂freshLaw W b := by
  set μ := growthPathLaw W b
  set ρ := (pastLaw W j b).prod (freshLaw W b)
  have hT := (measurable_pastCoords W j).prodMk (measurable_freshSample W j)
  have hmap : μ.map (fun ω => (pastCoords W j ω, freshSample W j ω)) = ρ :=
    growthPathLaw_map_past_fresh W j b
  have hΨi : Integrable Ψ ρ := by
    rw [← hmap]; exact (integrable_map_measure hΨ.aestronglyMeasurable hT.aemeasurable).mpr hint
  set G : PastSample W j → ℂ := fun x => ∫ y, Ψ (x, y) ∂freshLaw W b
  have hG : Measurable G := (hΨ.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable
  have hGi : Integrable G (pastLaw W j b) := hΨi.integral_prod_left
  have hm : growthSigma W j ≤ (inferInstance : MeasurableSpace (GrowthPath W)) := by
    rw [growthSigma_eq_comap]; exact (measurable_pastCoords W j).comap_le
  have hGμ : Integrable (fun ω => G (pastCoords W j ω)) μ := by
    have h := (integrable_map_measure hG.aestronglyMeasurable
      (measurable_pastCoords W j).aemeasurable).mp (by rw [growthPathLaw_map_pastCoords]; exact hGi)
    exact h
  have hgm : Measurable[growthSigma W j] fun ω => G (pastCoords W j ω) :=
    hG.comp (comap_measurable (pastCoords W j))
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hint (fun s _ _ => hGμ.integrableOn)
    (fun s hs _ => ?_) hgm.aestronglyMeasurable).symm
  obtain ⟨B, hB, rfl⟩ := hs
  change ∫ ω in pastCoords W j ⁻¹' B, G (pastCoords W j ω) ∂μ =
    ∫ ω in pastCoords W j ⁻¹' B, Ψ (pastCoords W j ω, freshSample W j ω) ∂μ
  have hind : ∀ f : GrowthPath W → ℂ, ∫ ω in pastCoords W j ⁻¹' B, f ω ∂μ =
      ∫ ω, (pastCoords W j ⁻¹' B).indicator f ω ∂μ := fun f =>
    (integral_indicator (measurable_pastCoords W j hB)).symm
  rw [hind, hind]
  set Φ : PastSample W j × LayerSample W .oneBlockOnePort → ℂ :=
    fun z => B.indicator (fun _ => (1 : ℂ)) z.1 * Ψ z
  have hΦ : Measurable Φ := ((measurable_const.indicator hB).comp measurable_fst).mul hΨ
  have hΦi : Integrable Φ ρ := by
    refine hΨi.norm.mono' hΦ.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    by_cases hz : z.1 ∈ B <;> simp [Φ, hz]
  have e1 : ∫ ω, (pastCoords W j ⁻¹' B).indicator
      (fun ω => Ψ (pastCoords W j ω, freshSample W j ω)) ω ∂μ = ∫ z, Φ z ∂ρ := by
    rw [← hmap, integral_map hT.aemeasurable hΦ.aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : pastCoords W j ω ∈ B
    · simp [Φ, hω]
    · simp [Φ, hω]
  have e2 : ∫ ω, (pastCoords W j ⁻¹' B).indicator (fun ω => G (pastCoords W j ω)) ω ∂μ =
      ∫ x, B.indicator G x ∂pastLaw W j b := by
    rw [← growthPathLaw_map_pastCoords W j b, integral_map (measurable_pastCoords W j).aemeasurable
      (hG.indicator hB).aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : pastCoords W j ω ∈ B
    · simp [hω]
    · simp [hω]
  rw [e1, e2, integral_prod Φ hΦi]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ B <;> simp [Φ, G, hx]

/-- **Fubini for the centered part on a past event.** -/
theorem eLpNorm_indicator_fresh_le (b : ℝ) (j : ℕ)
    {Ψ : PastSample W j × LayerSample W .oneBlockOnePort → ℂ} (hΨ : Measurable Ψ)
    {A' : Set (PastSample W j)} (hA' : MeasurableSet A') {p : ℝ} (hp : 1 ≤ p)
    {B : PastSample W j → ℝ} (hBm : Measurable B) (hB0 : ∀ x, 0 ≤ B x)
    (hB : ∀ x ∈ A', eLpNorm (fun y => Ψ (x, y) - ∫ y', Ψ (x, y') ∂freshLaw W b)
      (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal (B x)) :
    eLpNorm ((pastCoords W j ⁻¹' A').indicator fun ω =>
        Ψ (pastCoords W j ω, freshSample W j ω) - ∫ y, Ψ (pastCoords W j ω, y) ∂freshLaw W b)
      (ENNReal.ofReal p) (growthPathLaw W b) ≤
      eLpNorm ((pastCoords W j ⁻¹' A').indicator fun ω => B (pastCoords W j ω))
        (ENNReal.ofReal p) (growthPathLaw W b) := by
  set μ := growthPathLaw W b
  set ρ := (pastLaw W j b).prod (freshLaw W b)
  have hT := (measurable_pastCoords W j).prodMk (measurable_freshSample W j)
  have hpc := measurable_pastCoords (W := W) j
  have hmap : μ.map (fun ω => (pastCoords W j ω, freshSample W j ω)) = ρ :=
    growthPathLaw_map_past_fresh W j b
  set G : PastSample W j → ℂ := fun x => ∫ y, Ψ (x, y) ∂freshLaw W b
  have hG : Measurable G := (hΨ.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable
  set F : PastSample W j × LayerSample W .oneBlockOnePort → ℂ :=
    fun z => A'.indicator (fun x => Ψ (x, z.2) - G x) z.1
  have hF : Measurable F := by
    refine Measurable.ite (hA'.preimage measurable_fst) (hΨ.sub (hG.comp measurable_fst))
      measurable_const
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by linarith)
  have eL : (pastCoords W j ⁻¹' A').indicator (fun ω =>
      Ψ (pastCoords W j ω, freshSample W j ω) - ∫ y, Ψ (pastCoords W j ω, y) ∂freshLaw W b) =
      fun ω => F (pastCoords W j ω, freshSample W j ω) := by
    funext ω; by_cases hω : pastCoords W j ω ∈ A' <;> simp [F, G, hω]
  set Bc : PastSample W j → ℝ := A'.indicator B
  have hBc : Measurable Bc := hBm.indicator hA'
  have eR : (pastCoords W j ⁻¹' A').indicator (fun ω => B (pastCoords W j ω)) =
      fun ω => Bc (pastCoords W j ω) := by
    funext ω; by_cases hω : pastCoords W j ω ∈ A' <;> simp [Bc, hω]
  have hm1 : Measurable fun ω => F (pastCoords W j ω, freshSample W j ω) := hF.comp hT
  have hm2 : Measurable fun ω => Bc (pastCoords W j ω) := hBc.comp hpc
  rw [eL, eR, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hm1.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hm2.aestronglyMeasurable, hpr]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  have hFe : Measurable fun z => ‖F z‖ₑ ^ p := hF.enorm.pow_const _
  have hBe : Measurable fun x => ‖Bc x‖ₑ ^ p := hBc.enorm.pow_const _
  have l1 : ∫⁻ ω, ‖F (pastCoords W j ω, freshSample W j ω)‖ₑ ^ p ∂μ = ∫⁻ z, ‖F z‖ₑ ^ p ∂ρ := by
    rw [← hmap, lintegral_map hFe hT]
  have l2 : ∫⁻ ω, ‖Bc (pastCoords W j ω)‖ₑ ^ p ∂μ = ∫⁻ x, ‖Bc x‖ₑ ^ p ∂pastLaw W j b := by
    rw [← growthPathLaw_map_pastCoords W j b, lintegral_map hBe hpc]
  rw [l1, l2, lintegral_prod _ hFe.aemeasurable]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ A'
  · have h := hB x hx
    have hmx : Measurable fun y => Ψ (x, y) - ∫ y', Ψ (x, y') ∂freshLaw W b :=
      (hΨ.comp measurable_prodMk_left).sub measurable_const
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hmx.aestronglyMeasurable, hpr] at h
    have h2 := ENNReal.rpow_le_rpow h (by positivity : (0 : ℝ) ≤ p)
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by linarith), ENNReal.rpow_one] at h2
    simp only [F, Bc, Set.indicator_of_mem hx]
    refine h2.trans (le_of_eq ?_)
    rw [Real.enorm_eq_ofReal (hB0 x)]
  · simp [F, Bc, hx]

end BlockBand.SourceProcess.ContractingWords
