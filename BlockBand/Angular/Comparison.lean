module

public import BlockBand.Angular.ComparisonPointwise

/-!
# The angular comparison for `C¹` reconstruction tests

`angular_comparison_C1`: for `Φ(v) = φ(𝓛v/‖𝓛v‖)` with `|φ| ≤ M`, `φ` `L_φ`-Lipschitz
(`ReconLip`), and in addition `Φ` `C¹` off the origin,
`|ν[χ(j - j_*)Φ]| ≤ C(M + L_φ)/N · {Z + r + ν(χ‖H‖)}`
with `C = compConst σ Y Zb C₀ χ`, which depends only on `σ ≥ s, s⁻¹`, `Y ≥ (Im ζ)⁻¹`,
`Zb ≥ |ζ|`, `C₀` and the cutoff data `R₁, M₀ ≥ χ, M₁ ≥ |χ'|`; it is independent of `N`, of
`𝓛` (only injectivity is used), of `J`, of `𝔷` and of `r`.

Proof: the contrast Stein identity with `F = χΦ`; its last term `(2N/s)ν[(a - a_*)b_J F]` equals
`2N ν[g(a - a_*)F']` with `F' = χ (b_J/(sg)) Φ`, which the longitudinal Stein identity
rewrites. The remaining terms are bounded pointwise (`ComparisonPointwise`) and integrated
with the angular ratio lemma (`angular_ratio`, for `A = J, I, K₀`). Conventions:
`ν(f) = ∫ e^{q} 𝔷 f dν_N`, `ν(χ‖H‖) = ∫ e^{q} χ(b₂) ‖∇𝔷‖ dν_N`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Ratio

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.DegreeZero
open BlockBand.Angular.ProjectiveStein BlockBand.Angular.Reference BlockBand.Angular.Stein
open BlockBand.Angular.Stein.AngularData (reInner quadNum reInner_comm normSqSum_eq_reInner
  reInner_mulVec_herm quadNum_real_smul quadQuot_of_unit)
open scoped ComplexConjugate

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- `recon 𝓛 (rv) = recon 𝓛 v` for `r > 0`. -/
theorem recon_smul (L : Matrix κ ι ℂ) (z : ι → ℂ) {r : ℝ} (hr : 0 < r) :
    recon L (r • z) = recon L z := by
  unfold recon
  rw [mulVec_smul, ← complex_smul_eq_real_smul, l2Norm_smul', Complex.norm_real,
    Real.norm_of_nonneg hr.le, smul_smul]
  congr 1
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  rw [mul_inv, mul_comm (r : ℂ)⁻¹, mul_assoc, inv_mul_cancel₀ hr', mul_one]

/-- A reconstruction-Lipschitz test is scale-invariant. -/
theorem reconLip_scaleInvariant {L : Matrix κ ι ℂ} {Φ : (ι → ℂ) → ℝ} {Lφ : ℝ}
    (hlip : ReconLip L Φ Lφ) : IsScaleInvariant Φ := fun z r hr => by
  by_cases hz : z = 0
  · rw [hz, smul_zero]
  have h := hlip (r • z) z (smul_ne_zero hr.ne' hz) hz
  rw [recon_smul L z hr, sub_self, show l2Norm (0 : κ → ℂ) = 0 by simp [l2Norm_eq, normSqSum],
    mul_zero] at h
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h)

theorem abs_integral_le_of_pw [Nonempty ι] {f G : (ι → ℂ) → ℝ}
    (hG : Integrable G (projectiveHaar ι)) (h : ∀ v, normSqSum v = 1 → |f v| ≤ G v) :
    |∫ v, f v ∂projectiveHaar ι| ≤ ∫ v, G v ∂projectiveHaar ι := by
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (ae_of_all _ fun _ => abs_nonneg _) hG ?_)
  filter_upwards [ae_projectiveHaar_unit] with v hv using h v hv

theorem integral_lin4 {f1 f2 f3 f4 : (ι → ℂ) → ℝ} {μ : Measure (ι → ℂ)} (h1 : Integrable f1 μ)
    (h2 : Integrable f2 μ) (h3 : Integrable f3 μ) (h4 : Integrable f4 μ) (c1 c2 c3 c4 : ℝ) :
    ∫ v, (c1 * f1 v + c2 * f2 v + c3 * f3 v + c4 * f4 v) ∂μ =
      c1 * ∫ v, f1 v ∂μ + c2 * ∫ v, f2 v ∂μ + c3 * ∫ v, f3 v ∂μ + c4 * ∫ v, f4 v ∂μ := by
  have i12 : Integrable (fun v => c1 * f1 v + c2 * f2 v) μ :=
    (h1.const_mul c1).add (h2.const_mul c2)
  have i123 : Integrable (fun v => c1 * f1 v + c2 * f2 v + c3 * f3 v) μ :=
    i12.add (h3.const_mul c3)
  rw [integral_add i123 (h4.const_mul c4), integral_add i12 (h3.const_mul c3),
    integral_add (h1.const_mul c1) (h2.const_mul c2), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul]

/-- The final bookkeeping of the proof of the angular comparison. -/
theorem comp_arith {N T TA TB TC TD M Lφ Zm S Hn IJ I1 IK M₀ M₁ Kb KΔ Kh Kdh KW Kr CR : ℝ}
    (hN : 1 ≤ N) (hT : 2 * N * T = TA - TB + (TC - TD))
    (hTA : |TA| ≤ M₁ * Kb * M * Zm + 2 * Lφ * IJ + 2 * Lφ * Kr * I1 + M * KW * Hn)
    (hTB : |TB| ≤ M₀ * M * KΔ * Zm)
    (hTC : |TC| ≤ (M₁ * Kb * (Kh * M) + M₀ * Kdh * M) * Zm + Kh * (2 * Lφ) * IK +
      Kh * (2 * Lφ * Kr) * I1 + Kh * M * KW * Hn)
    (hTD : |TD| ≤ M₀ * (Kh * M) * KΔ * Zm)
    (hIJ : IJ ≤ CR * S) (hI1 : I1 ≤ CR * S) (hIK : IK ≤ CR * S)
    (hZS : Zm ≤ S) (hHS : Hn ≤ S) (hM : 0 ≤ M) (hLφ : 0 ≤ Lφ) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hKb : 0 ≤ Kb) (hKΔ : 0 ≤ KΔ) (hKh : 0 ≤ Kh) (hKdh : 0 ≤ Kdh) (hKW : 0 ≤ KW) (hKr : 0 ≤ Kr)
    (hCR : 0 ≤ CR) (hS : 0 ≤ S) :
    |T| ≤ (M₁ * Kb + M₀ * KΔ + M₁ * Kb * Kh + M₀ * Kdh + M₀ * Kh * KΔ + KW * (1 + Kh) +
      2 * CR * (1 + Kr) * (1 + Kh)) * (M + Lφ) / N * S := by
  have hN0 : 0 < N := by linarith
  have h2N : 2 * N * |T| ≤ |TA| + |TB| + |TC| + |TD| := by
    have : |2 * N * T| = 2 * N * |T| := by rw [abs_mul, abs_of_pos (by linarith)]
    rw [← this, hT]
    refine (abs_add_le _ _).trans ?_
    have := abs_sub TA TB; have := abs_sub TC TD; linarith
  have a1 : M₁ * Kb * M * Zm ≤ M₁ * Kb * M * S := mul_le_mul_of_nonneg_left hZS (by positivity)
  have a2 : 2 * Lφ * IJ ≤ 2 * Lφ * (CR * S) := mul_le_mul_of_nonneg_left hIJ (by positivity)
  have a3 : 2 * Lφ * Kr * I1 ≤ 2 * Lφ * Kr * (CR * S) :=
    mul_le_mul_of_nonneg_left hI1 (by positivity)
  have a4 : M * KW * Hn ≤ M * KW * S := mul_le_mul_of_nonneg_left hHS (by positivity)
  have b1 : M₀ * M * KΔ * Zm ≤ M₀ * M * KΔ * S := mul_le_mul_of_nonneg_left hZS (by positivity)
  have c1 : (M₁ * Kb * (Kh * M) + M₀ * Kdh * M) * Zm ≤ (M₁ * Kb * (Kh * M) + M₀ * Kdh * M) * S :=
    mul_le_mul_of_nonneg_left hZS (by positivity)
  have c2 : Kh * (2 * Lφ) * IK ≤ Kh * (2 * Lφ) * (CR * S) :=
    mul_le_mul_of_nonneg_left hIK (by positivity)
  have c3 : Kh * (2 * Lφ * Kr) * I1 ≤ Kh * (2 * Lφ * Kr) * (CR * S) :=
    mul_le_mul_of_nonneg_left hI1 (by positivity)
  have c4 : Kh * M * KW * Hn ≤ Kh * M * KW * S := mul_le_mul_of_nonneg_left hHS (by positivity)
  have d1 : M₀ * (Kh * M) * KΔ * Zm ≤ M₀ * (Kh * M) * KΔ * S :=
    mul_le_mul_of_nonneg_left hZS (by positivity)
  have e1 : 0 ≤ M * (2 * CR * (1 + Kr) * (1 + Kh)) * S := by positivity
  have e2 : 0 ≤ Lφ * (M₁ * Kb + M₀ * KΔ + M₁ * Kb * Kh + M₀ * Kdh + M₀ * Kh * KΔ +
      KW * (1 + Kh)) * S := by positivity
  have hfin : 2 * N * |T| ≤ (M₁ * Kb + M₀ * KΔ + M₁ * Kb * Kh + M₀ * Kdh + M₀ * Kh * KΔ +
      KW * (1 + Kh) + 2 * CR * (1 + Kr) * (1 + Kh)) * (M + Lφ) * S := by
    nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hN0]
  have := abs_nonneg T
  nlinarith

/-- The constant of the angular comparison bound. -/
def compConst (σ Y Zb C₀ : ℝ) (X : Cutoff) : ℝ :=
  X.M₁ * Kb σ Y Zb X.R₁ + X.M₀ * KDelta σ Y Zb X.R₁ + X.M₁ * Kb σ Y Zb X.R₁ * Kh σ Y Zb X.R₁ +
    X.M₀ * Kdh σ Y Zb X.R₁ + X.M₀ * Kh σ Y Zb X.R₁ * KDelta σ Y Zb X.R₁ +
    KW σ Y Zb X.R₁ * (1 + Kh σ Y Zb X.R₁) +
    2 * ratioConst σ Y Zb (cAll Y Zb) C₀ X * (1 + Kr Y Zb X.R₁) * (1 + Kh σ Y Zb X.R₁)

variable {D : AngularData ι} {σ Y Zb : ℝ}

/-- `χ|D(h̃Φ)[W_{K₀}]| ≤ M₀K_{dh}M + K_h(2L_φ ν-ratio(K₀) + 2L_φK_r ν-ratio(I))`. -/
theorem pw_DΨ (S : Scales D σ Y Zb) {L : Matrix κ ι ℂ} (hL : ∀ x, L *ᵥ x = 0 → x = 0)
    (X : Cutoff) {J : Matrix ι ι ℂ} (hJ : IsContraction J) {Φ : (ι → ℂ) → ℝ} {M Lφ : ℝ}
    (hM : ∀ v, v ≠ 0 → |Φ v| ≤ M) (hLφ : 0 ≤ Lφ) (hlip : ReconLip L Φ Lφ)
    (hΦc : ContDiffOn ℝ 1 Φ {z | z ≠ 0}) {v : ι → ℂ} (hv : normSqSum v = 1) :
    X.χ (D.b₂ v) * |fderiv ℝ (fun y => D.htil J y * Φ y) v (D.field D.K v)| ≤
      X.M₀ * Kdh σ Y Zb X.R₁ * M + Kh σ Y Zb X.R₁ *
        (2 * Lφ * ratF D L X D.K v + 2 * Lφ * Kr Y Zb X.R₁ * ratF D L X 1 v) := by
  have hv0 := ne_zero_of_unit hv
  have hMv := hM v hv0
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hMv
  have hΦd := dAt hΦc hv0
  have hhd := dAt (D.htil_c1 J) hv0
  have hχ0 := X.nonneg (D.b₂ v)
  have hR := ratF_nonneg D L X D.K v
  have hR1 := ratF_nonneg D L X 1 v
  have hKh := S.Kh_nonneg X.R₁
  have hKdh := S.Kdh_nonneg X.R₁
  have hKr := S.Kr_nonneg' X.R₁
  have hM₀ := X.M₀_nonneg
  by_cases hb : D.b₂ v ≤ X.R₁
  · rw [fderiv_mul_apply hhd hΦd]
    have hDΦ := pw_DΦ D hL X hLφ hlip hv0 hΦd D.K (K := Kr Y Zb X.R₁)
      (fun _ => S.abs_ratio_K_le hv hb)
    have h1 : |fderiv ℝ (D.htil J) v (D.field D.K v) * Φ v| ≤ Kdh σ Y Zb X.R₁ * M :=
      abs_mul_le_of (S.abs_fderiv_htil_le hJ hv hb) hMv
    have h2 : |D.htil J v * fderiv ℝ Φ v (D.field D.K v)| ≤
        Kh σ Y Zb X.R₁ * |fderiv ℝ Φ v (D.field D.K v)| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (S.abs_htil_le hJ hv hb) (abs_nonneg _)
    have h3 : X.χ (D.b₂ v) * (Kdh σ Y Zb X.R₁ * M) ≤ X.M₀ * (Kdh σ Y Zb X.R₁ * M) :=
      mul_le_mul_of_nonneg_right (X.le _) (by positivity)
    have h4 : Kh σ Y Zb X.R₁ * (X.χ (D.b₂ v) * |fderiv ℝ Φ v (D.field D.K v)|) ≤
        Kh σ Y Zb X.R₁ * (2 * Lφ * ratF D L X D.K v + 2 * Lφ * Kr Y Zb X.R₁ * ratF D L X 1 v) :=
      mul_le_mul_of_nonneg_left hDΦ hKh
    calc X.χ (D.b₂ v) * |fderiv ℝ (D.htil J) v (D.field D.K v) * Φ v +
          D.htil J v * fderiv ℝ Φ v (D.field D.K v)| ≤
        X.χ (D.b₂ v) * (Kdh σ Y Zb X.R₁ * M + Kh σ Y Zb X.R₁ *
          |fderiv ℝ Φ v (D.field D.K v)|) :=
          mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h1 h2)) hχ0
      _ = X.χ (D.b₂ v) * (Kdh σ Y Zb X.R₁ * M) +
          Kh σ Y Zb X.R₁ * (X.χ (D.b₂ v) * |fderiv ℝ Φ v (D.field D.K v)|) := by ring
      _ ≤ _ := by linarith
  · push Not at hb
    rw [X.supp _ hb, zero_mul]
    positivity

/-- **The angular comparison** for `C¹` tests. Let `𝓛` be injective,
`J` a Hermitian contraction, `χ` a cutoff, `𝔷 ≥ 0` scale-invariant and `C¹` off `0`, and assume
the angular first-moment bound in the tested form of `angular_ratio`. Let `Φ` be `C¹` off the
origin, `|Φ| ≤ M` off the origin, and `L_φ`-Lipschitz in the reconstructed direction
`𝓛v/‖𝓛v‖` (`ReconLip`). Then
`|ν[χ(b₂)(j - j_*)Φ]| ≤ C(M + L_φ)/N · {Z + r + ν(χ‖H‖)}`,
`j = Re v*Jv`, `j_* = N⁻¹ Re Tr ΓJ`, with `C = compConst σ Y Zb C₀ χ` depending only on
`σ, Y, Zb, C₀` and the cutoff data. -/
theorem angular_comparison_C1 [Nonempty ι] (D : AngularData ι) {L : Matrix κ ι ℂ}
    (hL : ∀ x, L *ᵥ x = 0 → x = 0) {J : Matrix ι ι ℂ} (hJ : IsContraction J)
    {σ Y Zb : ℝ} (hs1 : D.s ≤ σ) (hs2 : D.s⁻¹ ≤ σ) (hY : D.ζ.im⁻¹ ≤ Y) (hZb : ‖D.ζ‖ ≤ Zb)
    (X : Cutoff) {Zf : (ι → ℂ) → ℝ} (hZm : Measurable Zf) (hZi : IsScaleInvariant Zf)
    (hZc : ContDiffOn ℝ 1 Zf {z | z ≠ 0}) (hZ0 : ∀ v, 0 ≤ Zf v)
    {C₀ r : ℝ} (hC₀ : 0 ≤ C₀) (hr : 0 ≤ r)
    (hFM : ∀ w : ι → ℂ, ∫ v, Real.exp (D.expo v) * Zf v * ‖star w ⬝ᵥ v‖ ^ 2 ∂projectiveHaar ι ≤
      C₀ * ((∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar ι) + r) / Fintype.card ι *
        (star w ⬝ᵥ (D.Γ *ᵥ w)).re)
    {Φ : (ι → ℂ) → ℝ} (hΦc : ContDiffOn ℝ 1 Φ {z | z ≠ 0}) {M Lφ : ℝ}
    (hM : ∀ v, v ≠ 0 → |Φ v| ≤ M) (hLφ : 0 ≤ Lφ) (hlip : ReconLip L Φ Lφ) :
    |∫ v, Real.exp (D.expo v) * Zf v * (X.χ (D.b₂ v) * (quadQuot J v - D.jStar J) * Φ v)
        ∂projectiveHaar ι| ≤
      compConst σ Y Zb C₀ X * (M + Lφ) / Fintype.card ι *
        ((∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar ι) + r +
          ∫ v, Real.exp (D.expo v) * X.χ (D.b₂ v) * gradNorm Zf v ∂projectiveHaar ι) := by
  have S : Scales D σ Y Zb := ⟨hs1, hs2, hY, hZb⟩
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast Fintype.card_pos
  set Zm := ∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar ι with hZmdef
  set Hn := ∫ v, Real.exp (D.expo v) * X.χ (D.b₂ v) * gradNorm Zf v ∂projectiveHaar ι
    with hHndef
  set CR := ratioConst σ Y Zb (cAll Y Zb) C₀ X with hCR
  -- regularity
  have hΦm : Measurable Φ :=
    measurable_of_continuousOn_compl_singleton 0 (hΦc.continuousOn.mono fun z hz => hz)
  have hΦi : IsScaleInvariant Φ := reconLip_scaleInvariant hlip
  have hM0 : 0 ≤ M := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have hne : (Pi.single i (1 : ℂ) : ι → ℂ) ≠ 0 := Function.ne_iff.2 ⟨i, by simp⟩
    exact (abs_nonneg _).trans (hM _ hne)
  have hχc1 : ContDiffOn ℝ 1 (fun v => X.χ (D.b₂ v)) {z | z ≠ 0} :=
    X.smooth.comp_contDiffOn (b₂_c1 D)
  have hχm : Measurable (fun v => X.χ (D.b₂ v)) :=
    X.smooth.continuous.measurable.comp (measurable_quadQuot _)
  have hχi : IsScaleInvariant (fun v => X.χ (D.b₂ v)) := fun z c hc => by
    simp only [AngularData.b₂, quadQuot_scale _ z hc]
  have hFc : ContDiffOn ℝ 1 (fun y => X.χ (D.b₂ y) * Φ y) {z | z ≠ 0} := hχc1.mul hΦc
  have hFm : Measurable (fun y => X.χ (D.b₂ y) * Φ y) := hχm.mul hΦm
  have hFi : IsScaleInvariant (fun y => X.χ (D.b₂ y) * Φ y) := fun z c hc => by
    simp only [hχi z c hc, hΦi z c hc]
  have hF'c : ContDiffOn ℝ 1 (fun y => X.χ (D.b₂ y) * (D.htil J y * Φ y)) {z | z ≠ 0} :=
    hχc1.mul ((D.htil_c1 J).mul hΦc)
  have hF'm : Measurable (fun y => X.χ (D.b₂ y) * (D.htil J y * Φ y)) :=
    hχm.mul ((D.htil_meas J).mul hΦm)
  have hF'i : IsScaleInvariant (fun y => X.χ (D.b₂ y) * (D.htil J y * Φ y)) := fun z c hc => by
    simp only [hχi z c hc, D.htil_inv J z c hc, hΦi z c hc]
  -- the two Stein identities
  have hC := D.contrast_stein J hJ.1 Zf _ hZm hFm hZi hFi hZc hFc
  have hLg := D.longitudinal_stein Zf _ hZm hF'm hZi hF'i hZc hF'c
  -- the longitudinal elimination
  have hEl : (∫ v, Real.exp (D.expo v) * Zf v * (X.χ (D.b₂ v) * (D.htil J v * Φ v)) *
      (D.gLong v * (D.a v - aStar D.ζ)) ∂projectiveHaar ι) =
      D.s⁻¹ * ∫ v, Real.exp (D.expo v) * Zf v * (X.χ (D.b₂ v) * Φ v) *
        ((D.a v - aStar D.ζ) * D.corr J v) ∂projectiveHaar ι := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_projectiveHaar_ne_zero] with v hv
    have h := D.htil_mul_gLong J hv
    have hs := D.hs.ne'
    rw [div_eq_mul_inv] at h
    linear_combination (Real.exp (D.expo v) * Zf v * X.χ (D.b₂ v) * Φ v *
      (D.a v - aStar D.ζ)) * h
  set TA := ∫ v, Real.exp (D.expo v) * (Zf v * fderiv ℝ (fun y => X.χ (D.b₂ y) * Φ y) v
      (D.field J v) + X.χ (D.b₂ v) * Φ v * fderiv ℝ Zf v (D.field J v)) ∂projectiveHaar ι
    with hTA
  set TB := ∫ v, Real.exp (D.expo v) * Zf v * (X.χ (D.b₂ v) * Φ v) *
      fderiv ℝ (D.ratio J) v (D.Γ *ᵥ v) ∂projectiveHaar ι with hTB
  set TC := ∫ v, Real.exp (D.expo v) * (Zf v * fderiv ℝ (fun y => X.χ (D.b₂ y) *
      (D.htil J y * Φ y)) v (D.field D.K v) + X.χ (D.b₂ v) * (D.htil J v * Φ v) *
        fderiv ℝ Zf v (D.field D.K v)) ∂projectiveHaar ι with hTC
  set TD := ∫ v, Real.exp (D.expo v) * Zf v * (X.χ (D.b₂ v) * (D.htil J v * Φ v)) *
      fderiv ℝ (D.ratio D.K) v (D.Γ *ᵥ v) ∂projectiveHaar ι with hTD
  set T := ∫ v, Real.exp (D.expo v) * Zf v * (X.χ (D.b₂ v) * (quadQuot J v - D.jStar J) * Φ v)
    ∂projectiveHaar ι with hT
  have hTe : T = ∫ v, Real.exp (D.expo v) * Zf v * (X.χ (D.b₂ v) * Φ v) *
      (quadQuot J v - D.jStar J) ∂projectiveHaar ι :=
    integral_congr_ae (ae_of_all _ fun v => by ring)
  have hId : 2 * N * T = TA - TB + (TC - TD) := by
    rw [hTe, hC, ← hLg, hEl]
    have hs := D.hs.ne'
    field_simp
  -- integrability
  have hI : ∀ {G : (ι → ℂ) → ℝ}, ContinuousOn G {z | z ≠ 0} → Integrable G (projectiveHaar ι) :=
    fun hG => integrable_of_continuousOn hG
  have hEc : ContinuousOn (fun v => Real.exp (D.expo v)) {z | z ≠ 0} :=
    Real.continuous_exp.comp_continuousOn D.expo_c1.continuousOn
  have hρc : ContinuousOn (fun v => Real.exp (D.expo v) * Zf v) {z | z ≠ 0} :=
    hEc.mul hZc.continuousOn
  have iρ : Integrable (fun v => Real.exp (D.expo v) * Zf v) (projectiveHaar ι) := hI hρc
  have iR : ∀ A : Matrix ι ι ℂ, Integrable (fun v => Real.exp (D.expo v) * Zf v *
      ratF D L X A v) (projectiveHaar ι) := fun A => hI (hρc.mul (ratF_contOn D hL X A))
  have iH : Integrable (fun v => Real.exp (D.expo v) * X.χ (D.b₂ v) * gradNorm Zf v)
      (projectiveHaar ι) :=
    hI ((hEc.mul hχc1.continuousOn).mul (continuousOn_gradNorm hZc))
  -- the ratio bounds
  have hRJ : (∫ v, Real.exp (D.expo v) * Zf v * ratF D L X J v ∂projectiveHaar ι) ≤
      CR * (Zm + r + Hn) :=
    angular_ratio D L hL (Or.inl hJ) hs1 hs2 hY hZb X hZm hZi hZc hZ0 hC₀ hr hFM
  have hR1 : (∫ v, Real.exp (D.expo v) * Zf v * ratF D L X 1 v ∂projectiveHaar ι) ≤
      CR * (Zm + r + Hn) :=
    angular_ratio D L hL (Or.inr (Or.inl rfl)) hs1 hs2 hY hZb X hZm hZi hZc hZ0 hC₀ hr hFM
  have hRK : (∫ v, Real.exp (D.expo v) * Zf v * ratF D L X D.K v ∂projectiveHaar ι) ≤
      CR * (Zm + r + Hn) :=
    angular_ratio D L hL (Or.inr (Or.inr rfl)) hs1 hs2 hY hZb X hZm hZi hZc hZ0 hC₀ hr hFM
  -- constants
  have hKb := S.Kb_nonneg X.R₁
  have hKW := S.KW_nonneg X.R₁
  have hKr := S.Kr_nonneg' X.R₁
  have hKΔ := S.KDelta_nonneg X.R₁
  have hKh := S.Kh_nonneg X.R₁
  have hKdh := S.Kdh_nonneg X.R₁
  have hM₀ := X.M₀_nonneg
  have hM₁ := X.M₁_nonneg
  -- cutoff facts
  have cutJ : ∀ v, normSqSum v = 1 → D.b₂ v ≤ X.R₁ →
      |fderiv ℝ D.b₂ v (D.field J v)| ≤ Kb σ Y Zb X.R₁ := fun v hv hb =>
    S.abs_fderiv_b₂_field_le hJ.1 hv (S.abs_quadQuot_J_le hJ hv hb) (S.abs_ratio_J_le hv hb hJ)
      (S.abs_corr_le hv (S.abs_quadQuot_JΓK_le hJ hv) (S.abs_ratio_J_le hv hb hJ))
  have cutK : ∀ v, normSqSum v = 1 → D.b₂ v ≤ X.R₁ →
      |fderiv ℝ D.b₂ v (D.field D.K v)| ≤ Kb σ Y Zb X.R₁ := fun v hv hb =>
    S.abs_fderiv_b₂_field_le D.hK hv (S.abs_quadQuot_K_le hv hb) (S.abs_ratio_K_le hv hb)
      (S.abs_corr_le hv (S.abs_quadQuot_KΓK_le hv) (S.abs_ratio_K_le hv hb))
  have supp : ∀ v, X.χ (D.b₂ v) ≠ 0 → D.b₂ v ≤ X.R₁ := fun v h => by
    by_contra hb; push Not at hb; exact h (X.supp _ hb)
  -- T_A
  have bTA : |TA| ≤ X.M₁ * Kb σ Y Zb X.R₁ * M * Zm + 2 * Lφ *
      (∫ v, Real.exp (D.expo v) * Zf v * ratF D L X J v ∂projectiveHaar ι) +
      2 * Lφ * Kr Y Zb X.R₁ * (∫ v, Real.exp (D.expo v) * Zf v * ratF D L X 1 v ∂projectiveHaar ι) +
      M * KW σ Y Zb X.R₁ * Hn := by
    rw [hTA, hZmdef, hHndef, ← integral_lin4 iρ (iR J) (iR 1) iH]
    refine abs_integral_le_of_pw ((((iρ.const_mul _).add ((iR J).const_mul _)).add
      ((iR 1).const_mul _)).add (iH.const_mul _)) fun v hv => ?_
    have hv0 := ne_zero_of_unit hv
    have h1 := pw_main S X hv (hZ0 v) (dAt hΦc hv0) hM0 (W := D.field J v) fun hb =>
      ⟨cutJ v hv hb, hM v hv0, S.l2_field_J_le hJ hv hb⟩
    have h2 := pw_DΦ D hL X hLφ hlip hv0 (dAt hΦc hv0) J (K := Kr Y Zb X.R₁)
      fun h => S.abs_ratio_J_le hv (supp v h) hJ
    have hρ : 0 ≤ Real.exp (D.expo v) * Zf v := by have := Real.exp_pos (D.expo v); have := hZ0 v; positivity
    have h3 := mul_le_mul_of_nonneg_left h2 hρ
    refine h1.trans ?_
    linarith
  -- T_B
  have bTB : |TB| ≤ X.M₀ * M * KDelta σ Y Zb X.R₁ * Zm := by
    rw [hTB, hZmdef, ← integral_const_mul]
    refine abs_integral_le_of_pw (iρ.const_mul _) fun v hv => ?_
    exact pw_Delta (Δ := fun v => fderiv ℝ (D.ratio J) v (D.Γ *ᵥ v)) X (hZ0 v) hM0 hKΔ
      fun hb => ⟨hM v (ne_zero_of_unit hv), S.abs_Delta_le (S.opB_ΓJ hJ) hv hb⟩
  -- T_C
  have bTC : |TC| ≤ (X.M₁ * Kb σ Y Zb X.R₁ * (Kh σ Y Zb X.R₁ * M) + X.M₀ * Kdh σ Y Zb X.R₁ * M) * Zm +
      Kh σ Y Zb X.R₁ * (2 * Lφ) *
        (∫ v, Real.exp (D.expo v) * Zf v * ratF D L X D.K v ∂projectiveHaar ι) +
      Kh σ Y Zb X.R₁ * (2 * Lφ * Kr Y Zb X.R₁) *
        (∫ v, Real.exp (D.expo v) * Zf v * ratF D L X 1 v ∂projectiveHaar ι) +
      Kh σ Y Zb X.R₁ * M * KW σ Y Zb X.R₁ * Hn := by
    rw [hTC, hZmdef, hHndef, ← integral_lin4 iρ (iR D.K) (iR 1) iH]
    refine abs_integral_le_of_pw ((((iρ.const_mul _).add ((iR D.K).const_mul _)).add
      ((iR 1).const_mul _)).add (iH.const_mul _)) fun v hv => ?_
    have hv0 := ne_zero_of_unit hv
    have hΨd : DifferentiableAt ℝ (fun y => D.htil J y * Φ y) v :=
      (dAt (D.htil_c1 J) hv0).mul (dAt hΦc hv0)
    have h1 := pw_main S X hv (hZ0 v) hΨd (mul_nonneg hKh hM0) (W := D.field D.K v) fun hb =>
      ⟨cutK v hv hb, abs_mul_le_of (S.abs_htil_le hJ hv hb) (hM v hv0), S.l2_field_K_le hv hb⟩
    have h2 := pw_DΨ S hL X hJ hM hLφ hlip hΦc hv
    have hρ : 0 ≤ Real.exp (D.expo v) * Zf v := by have := Real.exp_pos (D.expo v); have := hZ0 v; positivity
    have h3 := mul_le_mul_of_nonneg_left h2 hρ
    refine h1.trans ?_
    linarith
  -- T_D
  have bTD : |TD| ≤ X.M₀ * (Kh σ Y Zb X.R₁ * M) * KDelta σ Y Zb X.R₁ * Zm := by
    rw [hTD, hZmdef, ← integral_const_mul]
    refine abs_integral_le_of_pw (iρ.const_mul _) fun v hv => ?_
    exact pw_Delta (Ψ := fun y => D.htil J y * Φ y)
      (Δ := fun v => fderiv ℝ (D.ratio D.K) v (D.Γ *ᵥ v)) X (hZ0 v)
      (mul_nonneg hKh hM0) hKΔ fun hb => ⟨abs_mul_le_of (S.abs_htil_le hJ hv hb)
        (hM v (ne_zero_of_unit hv)), S.abs_Delta_le S.opB_ΓK hv hb⟩
  -- assembly
  have hZm0 : 0 ≤ Zm := integral_nonneg fun v => mul_nonneg (Real.exp_pos _).le (hZ0 v)
  have hHn0 : 0 ≤ Hn := integral_nonneg fun v =>
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (X.nonneg _)) (gradNorm_nonneg _ _)
  have hCR0 : 0 ≤ CR := by
    rw [hCR]; unfold ratioConst K1c K4c Λc cAll
    have := S.σ_pos; have := S.Y_pos; have := S.Zb_nonneg
    positivity
  have := comp_arith (T := T) hN1 hId bTA bTB bTC bTD hRJ hR1 hRK (by linarith) (by linarith)
    hM0 hLφ hM₀ hM₁ hKb hKΔ hKh hKdh hKW hKr hCR0 (by linarith)
  simpa only [compConst] using this

end BlockBand.Angular.Ratio
