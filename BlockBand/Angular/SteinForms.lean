module

public import BlockBand.Angular.Stein
public import BlockBand.Angular.LongitudinalCoefficient

/-!
# The contrast and longitudinal Stein identities; positivity of the longitudinal coefficient

* `contrast_stein` — the contrast Stein identity (`A = J` Hermitian, `j = v*Jv`,
  `j_* = N⁻¹ Tr ΓJ`, `b_J = Re(v*K₀ΓJv) - r_J u₁`);
* `longitudinal_stein` — the longitudinal Stein identity (`A = K₀`, `g = 1 - V_Γ/s`,
  `V_Γ = u₂ - u₁²/u₀`), using `N⁻¹ Tr ΓK₀ = a_*`;
* `positive_longitudinal` — `g = (u₀/s)((u₁/u₀ - a_*/2)² + y²) > 0`
  off the origin (from `Angular.LongitudinalCoefficient`).
The determinant term `ν[F Re(H*W_A)]` is written `ν[e^{q} F DZ[W_A]]` (`H = ∇ log 𝔷`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Stein

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.ConeDivergence
open BlockBand.Angular.DegreeZero BlockBand.Angular.ProjectiveStein BlockBand.Angular.Reference
open scoped ComplexConjugate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace AngularData

variable (D : AngularData ι)

/-- `j_* = N⁻¹ Tr ΓJ` (real part; `Tr ΓJ` is real for Hermitian `J`). -/
def jStar (J : Matrix ι ι ℂ) : ℝ := (Fintype.card ι : ℝ)⁻¹ * ((D.Γ * J).trace).re

/-- `V_Γ = u₂ - u₁²/u₀`. -/
def varGamma (v : ι → ℂ) : ℝ := D.u₂ v - D.u₁ v ^ 2 / D.u₀ v

/-- `g = 1 - V_Γ/s`. -/
def gLong (v : ι → ℂ) : ℝ := 1 - D.varGamma v / D.s

/-- **The contrast Stein identity**. -/
theorem contrast_stein [Nonempty ι] (J : Matrix ι ι ℂ) (hJ : J.IsHermitian)
    (Z F : (ι → ℂ) → ℝ) (hZm : Measurable Z) (hFm : Measurable F)
    (hZi : IsScaleInvariant Z) (hFi : IsScaleInvariant F)
    (hZc : ContDiffOn ℝ 1 Z {z | z ≠ 0}) (hFc : ContDiffOn ℝ 1 F {z | z ≠ 0}) :
    2 * (Fintype.card ι : ℝ) * ∫ v, Real.exp (D.expo v) * Z v * F v *
        (quadQuot J v - D.jStar J) ∂projectiveHaar ι =
      (∫ v, Real.exp (D.expo v) * (Z v * fderiv ℝ F v (D.field J v) +
          F v * fderiv ℝ Z v (D.field J v)) ∂projectiveHaar ι) -
        (∫ v, Real.exp (D.expo v) * Z v * F v * fderiv ℝ (D.ratio J) v (D.Γ *ᵥ v)
          ∂projectiveHaar ι) +
        2 * (Fintype.card ι : ℝ) / D.s * ∫ v, Real.exp (D.expo v) * Z v * F v *
          ((D.a v - aStar D.ζ) * D.corr J v) ∂projectiveHaar ι :=
  D.angular_stein J hJ Z F hZm hFm hZi hFi hZc hFc

theorem trace_Γ_K_re : ((D.Γ * D.K).trace).re = (Fintype.card ι : ℝ) * aStar D.ζ := by
  rw [Matrix.trace_mul_comm, Γ, trace_K_mul_angularGamma D.hK D.hs.ne' D.hroot]
  simp

theorem ratio_K {v : ι → ℂ} : D.ratio D.K v = D.u₁ v / D.u₀ v := by
  rw [ratio, u₁, ← D.K_mul_Γ]

theorem corr_K {v : ι → ℂ} : D.corr D.K v = D.varGamma v := by
  rw [corr, varGamma, D.ratio_K, u₂, u₁]
  have : D.K * D.Γ * D.K = D.K * D.K * D.Γ := by
    rw [Matrix.mul_assoc, ← D.K_mul_Γ, ← Matrix.mul_assoc]
  rw [this]; ring

/-- **Positivity of the longitudinal coefficient**: off the origin
`g = (u₀/s)((u₁/u₀ - a_*/2)² + y²)`, `y = Im ζ`, hence `g > 0`. -/
theorem positive_longitudinal {v : ι → ℂ} (hv : v ≠ 0) :
    D.gLong v = D.u₀ v / D.s * ((D.u₁ v / D.u₀ v - aStar D.ζ / 2) ^ 2 + D.ζ.im ^ 2) ∧
      0 < D.gLong v := by
  have hu := D.u₀_pos hv
  have href : D.u₂ v = D.s + aStar D.ζ * D.u₁ v - (aStar D.ζ ^ 2 / 4 + D.ζ.im ^ 2) * D.u₀ v := by
    have hS := normSqSum_pos hv
    unfold u₂ u₁ u₀
    rw [quadQuot_eq, quadQuot_eq, quadQuot_eq, D.KK_mul_Γ, quadNum_sub, quadNum_add,
      quadNum_real_smul, quadNum_real_smul, quadNum_real_smul, quadNum_one]
    have hc : aStar D.ζ ^ 2 / 4 + D.ζ.im ^ 2 = cStar D.ζ := by
      rw [aStar, cStar, Complex.normSq_apply]; ring
    rw [hc]
    field_simp
  refine ⟨?_, ?_⟩
  · unfold gLong varGamma
    exact BlockBand.Angular.longitudinal_coefficient_identity D.s (D.u₀ v) (D.u₁ v) (D.u₂ v)
      (aStar D.ζ) D.ζ.im D.hs.ne' hu.ne' href
  · unfold gLong varGamma
    exact BlockBand.Angular.longitudinal_coefficient_pos D.s (D.u₀ v) (D.u₁ v) (D.u₂ v)
      (aStar D.ζ) D.ζ.im D.hs hu D.hroot.1 href

/-- **The longitudinal Stein identity**:
`2N ν[g (a - a_*) F] = ν[W_{K₀}F + F Re(H*W_{K₀}) - F Δ_{K₀}]`, `ν(f) = ν_N[e^{q} 𝔷 f]`. -/
theorem longitudinal_stein [Nonempty ι] (Z F : (ι → ℂ) → ℝ) (hZm : Measurable Z)
    (hFm : Measurable F) (hZi : IsScaleInvariant Z) (hFi : IsScaleInvariant F)
    (hZc : ContDiffOn ℝ 1 Z {z | z ≠ 0}) (hFc : ContDiffOn ℝ 1 F {z | z ≠ 0}) :
    2 * (Fintype.card ι : ℝ) * ∫ v, Real.exp (D.expo v) * Z v * F v *
        (D.gLong v * (D.a v - aStar D.ζ)) ∂projectiveHaar ι =
      (∫ v, Real.exp (D.expo v) * (Z v * fderiv ℝ F v (D.field D.K v) +
          F v * fderiv ℝ Z v (D.field D.K v)) ∂projectiveHaar ι) -
        (∫ v, Real.exp (D.expo v) * Z v * F v * fderiv ℝ (D.ratio D.K) v (D.Γ *ᵥ v)
          ∂projectiveHaar ι) := by
  have h := D.angular_stein D.K D.hK Z F hZm hFm hZi hFi hZc hFc
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN0 : N ≠ 0 := by
    rw [hN]; exact_mod_cast Fintype.card_ne_zero
  have hs0 := D.hs.ne'
  set E : (ι → ℂ) → ℝ := fun v => Real.exp (D.expo v) with hE
  have hEi : IsScaleInvariant E := fun z r hr => by simp only [hE, D.expo_inv z r hr]
  have hEc : ContDiffOn ℝ 1 E {z | z ≠ 0} := Real.contDiff_exp.comp_contDiffOn D.expo_c1
  have hEm : Measurable E := Real.measurable_exp.comp D.expo_meas
  have hρb : Bdd (fun v => E v * Z v * F v) :=
    ((bdd_of_scaleInvariant hEi hEc).mul (bdd_of_scaleInvariant hZi hZc)).mul
      (bdd_of_scaleInvariant hFi hFc)
  have hρm : Measurable (fun v => E v * Z v * F v) := (hEm.mul hZm).mul hFm
  have hab : Bdd (fun v => D.a v - aStar D.ζ) :=
    (bdd_of_scaleInvariant (quadQuot_inv _) (contDiffOn_quadQuot _)).sub (bdd_const _)
  have habm : Measurable (fun v => D.a v - aStar D.ζ) :=
    (measurable_quadQuot _).sub measurable_const
  have hVb : Bdd (D.corr D.K) := bdd_of_scaleInvariant (D.corr_inv _) (D.corr_c1 _)
  have i1 : Integrable (fun v => E v * Z v * F v * (D.a v - aStar D.ζ)) (projectiveHaar ι) :=
    (hρb.mul hab).integrable (hρm.mul habm)
  have i2 : Integrable (fun v => E v * Z v * F v * ((D.a v - aStar D.ζ) * D.corr D.K v))
      (projectiveHaar ι) := (hρb.mul (hab.mul hVb)).integrable (hρm.mul (habm.mul (D.corr_meas _)))
  -- rewrite the general identity
  have e1 : (∫ v, E v * Z v * F v * (quadQuot D.K v - N⁻¹ * ((D.Γ * D.K).trace).re)
      ∂projectiveHaar ι) = ∫ v, E v * Z v * F v * (D.a v - aStar D.ζ) ∂projectiveHaar ι := by
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [D.trace_Γ_K_re, ← hN]
    rw [show N⁻¹ * (N * aStar D.ζ) = aStar D.ζ by field_simp]; rfl
  have e2 : (∫ v, E v * Z v * F v * (D.gLong v * (D.a v - aStar D.ζ)) ∂projectiveHaar ι) =
      (∫ v, E v * Z v * F v * (D.a v - aStar D.ζ) ∂projectiveHaar ι) -
        D.s⁻¹ * ∫ v, E v * Z v * F v * ((D.a v - aStar D.ζ) * D.corr D.K v) ∂projectiveHaar ι := by
    rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul _)]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [gLong, ← D.corr_K]
    field_simp
  simp only [hE] at e1 e2 h ⊢
  rw [e1] at h
  rw [e2]
  have : 2 * N * ((∫ v, Real.exp (D.expo v) * Z v * F v * (D.a v - aStar D.ζ) ∂projectiveHaar ι) -
      D.s⁻¹ * ∫ v, Real.exp (D.expo v) * Z v * F v * ((D.a v - aStar D.ζ) * D.corr D.K v)
        ∂projectiveHaar ι) =
      2 * N * (∫ v, Real.exp (D.expo v) * Z v * F v * (D.a v - aStar D.ζ) ∂projectiveHaar ι) -
        2 * N / D.s * ∫ v, Real.exp (D.expo v) * Z v * F v *
          ((D.a v - aStar D.ζ) * D.corr D.K v) ∂projectiveHaar ι := by ring
  rw [this]
  linarith

end AngularData

end BlockBand.Angular.Stein
