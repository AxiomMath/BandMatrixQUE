module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Conditional expectation given the past when a fresh coordinate is independent

On a probability space `(Ω, μ)`, let `π : Ω → P` (the past) and `φ : Ω → F` (the fresh
layer) have joint law `ν ⊗ λ`. For a strongly measurable `D : P × F → ℝ`, integrable for
`ν ⊗ λ`, the conditional expectation of `ω ↦ D(π ω, φ ω)` given `σ(π)` is a.e. the fresh
average `ω ↦ ∫ D(π ω, y) dλ(y)` (`condExp_comp_ae_eq`), and the second moment of the
martingale difference is the `ν ⊗ λ`-integral of `(D(p, y) - ∫ D(p, ·) dλ)²`
(`integral_sub_condExp_sq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont.OneLayer

open MeasureTheory

variable {Ω P F : Type*} [MeasurableSpace Ω] [MeasurableSpace P] [MeasurableSpace F]
  {μ : Measure Ω} {ν : Measure P} {ρ : Measure F}

/-- The fresh average `p ↦ ∫ D(p, y) dρ(y)`. -/
def freshAvg (ρ : Measure F) (D : P × F → ℝ) (p : P) : ℝ := ∫ y, D (p, y) ∂ρ

theorem map_fst_of_law [IsProbabilityMeasure ρ] {π : Ω → P} {φ : Ω → F} (hπ : Measurable π)
    (hφ : Measurable φ) (hlaw : μ.map (fun ω => (π ω, φ ω)) = ν.prod ρ) [SFinite ν] :
    μ.map π = ν := by
  have h : (μ.map (fun ω => (π ω, φ ω))).map Prod.fst = (ν.prod ρ).map Prod.fst := by
    rw [hlaw]
  rw [Measure.map_map measurable_fst (hπ.prodMk hφ), Measure.map_fst_prod, measure_univ,
    one_smul] at h
  exact h

/-- **Conditional expectation given the past** = the fresh average. -/
theorem condExp_comp_ae_eq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] {π : Ω → P} {φ : Ω → F} (hπ : Measurable π) (hφ : Measurable φ)
    (hlaw : μ.map (fun ω => (π ω, φ ω)) = ν.prod ρ) {D : P × F → ℝ}
    (hDm : StronglyMeasurable D) (hD : Integrable D (ν.prod ρ)) :
    μ[fun ω => D (π ω, φ ω) | MeasurableSpace.comap π inferInstance] =ᵐ[μ]
      fun ω => freshAvg ρ D (π ω) := by
  have hm : MeasurableSpace.comap π inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    hπ.comap_le
  have hπφ : Measurable fun ω => (π ω, φ ω) := hπ.prodMk hφ
  have hmapπ := map_fst_of_law hπ hφ hlaw
  have hGm : StronglyMeasurable (freshAvg ρ D) := hDm.integral_prod_right'
  have hGi : Integrable (freshAvg ρ D) ν := hD.integral_prod_left
  have hf : Integrable (fun ω => D (π ω, φ ω)) μ := by
    rw [← hlaw] at hD
    exact hD.comp_measurable hπφ
  have hg : Integrable (fun ω => freshAvg ρ D (π ω)) μ := by
    rw [← hmapπ] at hGi
    exact hGi.comp_measurable hπ
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hf (fun s _ _ => hg.integrableOn)
    (fun s hs _ => ?_) ?_).symm
  · obtain ⟨t, ht, rfl⟩ := hs
    have e1 : ∫ x in π ⁻¹' t, freshAvg ρ D (π x) ∂μ = ∫ p in t, freshAvg ρ D p ∂ν := by
      rw [← setIntegral_map ht (hmapπ ▸ hGm.aestronglyMeasurable) hπ.aemeasurable, hmapπ]
    have hpre : (fun ω => (π ω, φ ω)) ⁻¹' (t ×ˢ Set.univ) = π ⁻¹' t := by
      ext x; simp
    have e2 : ∫ x in π ⁻¹' t, D (π x, φ x) ∂μ = ∫ q in t ×ˢ Set.univ, D q ∂(ν.prod ρ) := by
      rw [← hlaw, setIntegral_map (ht.prod MeasurableSet.univ)
        (hlaw ▸ hDm.aestronglyMeasurable) hπφ.aemeasurable, hpre]
    rw [e1, e2, setIntegral_prod D hD.integrableOn]
    simp [freshAvg]
  · exact (hGm.comp_measurable (comap_measurable π)).aestronglyMeasurable

/-- **The martingale difference** has second moment
`∫ (D(p,y) - ∫ D(p,·) dρ)² d(ν ⊗ ρ)`. -/
theorem integral_sub_condExp_sq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] {π : Ω → P} {φ : Ω → F} (hπ : Measurable π) (hφ : Measurable φ)
    (hlaw : μ.map (fun ω => (π ω, φ ω)) = ν.prod ρ) {D : P × F → ℝ}
    (hDm : StronglyMeasurable D) (hD : Integrable D (ν.prod ρ)) :
    ∫ ω, (D (π ω, φ ω) - μ[fun ω => D (π ω, φ ω) | MeasurableSpace.comap π inferInstance] ω) ^ 2
        ∂μ = ∫ q, (D q - freshAvg ρ D q.1) ^ 2 ∂(ν.prod ρ) := by
  have hπφ : Measurable fun ω => (π ω, φ ω) := hπ.prodMk hφ
  have hae := condExp_comp_ae_eq hπ hφ hlaw hDm hD
  rw [integral_congr_ae (hae.mono fun ω h => by rw [h])]
  have hGm : StronglyMeasurable (freshAvg ρ D) := hDm.integral_prod_right'
  have hsm : StronglyMeasurable fun q : P × F => (D q - freshAvg ρ D q.1) ^ 2 :=
    (hDm.sub (hGm.comp_measurable measurable_fst)).pow 2
  rw [← hlaw, integral_map hπφ.aemeasurable (hlaw ▸ hsm.aestronglyMeasurable)]

/-- `L¹` norm of the conditional expectation = `∫ |∫ D(p,·) dρ| dν`. -/
theorem integral_abs_condExp [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] {π : Ω → P} {φ : Ω → F} (hπ : Measurable π) (hφ : Measurable φ)
    (hlaw : μ.map (fun ω => (π ω, φ ω)) = ν.prod ρ) {D : P × F → ℝ}
    (hDm : StronglyMeasurable D) (hD : Integrable D (ν.prod ρ)) :
    ∫ ω, |μ[fun ω => D (π ω, φ ω) | MeasurableSpace.comap π inferInstance] ω| ∂μ =
      ∫ p, |freshAvg ρ D p| ∂ν := by
  have hae := condExp_comp_ae_eq hπ hφ hlaw hDm hD
  rw [integral_congr_ae (hae.mono fun ω h => by rw [h])]
  have hmapπ := map_fst_of_law hπ hφ hlaw
  have hGm : StronglyMeasurable (freshAvg ρ D) := hDm.integral_prod_right'
  rw [← hmapπ, integral_map hπ.aemeasurable (hmapπ ▸ hGm.norm.aestronglyMeasurable)]

end BlockBand.SourceProcess.LengthCont.OneLayer
