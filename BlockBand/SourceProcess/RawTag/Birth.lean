module

public import BlockBand.SourceProcess.RawTag.BirthTools

/-!
# The birth values of the raw forms

Bounds on the raw forms at a birth: the norm of a unit tag (`vecNorm_unitTag_one`), moment bounds
under the law of the probe transferred to product measures (`momBd_tag`), and the norms of
`1 + ΔR`, `1 + RΔ` and `R + RΔR` at a passive input (`norm_one_add_mul_le`, `norm_res_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.FullSource
open scoped Matrix ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem vecNorm_unitTag_one (g : Fin W → ℂ) :
    vecNorm (unitTag W 1 0 g) = vecNorm (unitVec W g) := by
  simp only [vecNorm, unitTag, unitVec]
  congr 1
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp

/-- A bound under the law of `g` is a bound under `μ ⊗ ν` for `w ↦ F(g w.2)`. -/
theorem momBd_tag {Γ : Type} [MeasurableSpace Γ] {ν : Measure Γ} [IsProbabilityMeasure ν]
    {μ : Measure (GrowthPath W)} [IsProbabilityMeasure μ] {g : Γ → Fin W → ℂ}
    (hg : Measurable g) (hlaw : ν.map g = circularVectorLaw (Fin W)) {F : (Fin W → ℂ) → ℝ}
    {r C : ℝ} (hF : MomBd (circularVectorLaw (Fin W)) F r C) :
    MomBd (μ.prod ν) (fun w => F (g w.2)) r C := by
  have h1 : MomBd ν (fun γ => F (g γ)) r C := by
    refine ⟨?_, ?_⟩
    · exact (hlaw ▸ hF.1).comp_aemeasurable hg.aemeasurable
    · rw [show (fun γ => F (g γ)) = F ∘ g from rfl, ← eLpNorm_map_measure (hlaw ▸ hF.1)
        hg.aemeasurable, hlaw]
      exact hF.2
  exact MomBd.comp_snd (μ := μ) h1

/-- The norm of `1 + ΔR` and of `R + RΔR` at a passive input. -/
theorem norm_one_add_mul_le {M R : Matrix (Fin W) (Fin W) ℂ} {e : ℝ} (hR : ‖R‖ ≤ e) :
    ‖1 + M * R‖ ≤ 1 + ‖M‖ * e :=
  (norm_add_le _ _).trans (add_le_add norm_one_matrix_le
    ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left hR (norm_nonneg _))))

theorem norm_one_add_mul_le' {M R : Matrix (Fin W) (Fin W) ℂ} {e : ℝ} (hR : ‖R‖ ≤ e) :
    ‖1 + R * M‖ ≤ 1 + ‖M‖ * e := by
  refine (norm_add_le _ _).trans (add_le_add norm_one_matrix_le
    ((Matrix.l2_opNorm_mul _ _).trans ?_))
  rw [mul_comm]; exact mul_le_mul_of_nonneg_left hR (norm_nonneg _)

theorem norm_res_le {M R : Matrix (Fin W) (Fin W) ℂ} {e : ℝ} (he : 0 ≤ e) (hR : ‖R‖ ≤ e) :
    ‖R + R * M * R‖ ≤ e + ‖M‖ * e ^ 2 := by
  refine (norm_add_le _ _).trans (add_le_add hR ?_)
  calc ‖R * M * R‖ ≤ ‖R * M‖ * ‖R‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖R‖ * ‖M‖) * ‖R‖ := mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _)
        (norm_nonneg _)
    _ ≤ (e * ‖M‖) * e := mul_le_mul (mul_le_mul_of_nonneg_right hR (norm_nonneg _)) hR
        (norm_nonneg _) (by positivity)
    _ = ‖M‖ * e ^ 2 := by ring

end BlockBand.SourceProcess.RawTag
