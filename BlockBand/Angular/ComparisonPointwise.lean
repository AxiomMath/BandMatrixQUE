module

public import BlockBand.Angular.ComparisonDeriv

/-!
# Pointwise majorants for the angular comparison

For a test `F = χ(b₂)Ψ` and a field `W` the Stein integrand `e^{q}(𝔷 DF[W] + F D𝔷[W])` is
bounded at each unit vector by (`pw_main`)
`M₁K_b B_Ψ e^{q}𝔷 + e^{q}𝔷 χ|DΨ[W]| + B_Ψ K_W e^{q}χ‖∇𝔷‖`
whenever `|Db₂[W]| ≤ K_b`, `|Ψ| ≤ B_Ψ`, `‖W‖ ≤ K_W` on the cutoff `b₂ ≤ R₁` (off the cutoff
`χ = χ' = 0`). For `Ψ = Φ` reconstruction-Lipschitz, `χ|DΦ[W_A]|` is bounded by the ratios of
the angular ratio lemma (`pw_DΦ`); `pw_Delta` bounds the `Δ_A` terms. The constants on the
cutoff are those of `ComparisonBounds` and `ComparisonDeriv`.
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

/-- The weighted reconstruction ratio `χ(b₂)‖𝓛ΓAv‖/‖𝓛v‖` of the angular ratio bound. -/
def ratF (D : AngularData ι) (L : Matrix κ ι ℂ) (X : Cutoff) (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    ℝ :=
  X.χ (D.b₂ v) * (l2Norm (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) / l2Norm (L *ᵥ v))

theorem ratF_nonneg (D : AngularData ι) (L : Matrix κ ι ℂ) (X : Cutoff) (A : Matrix ι ι ℂ)
    (v : ι → ℂ) : 0 ≤ ratF D L X A v := by
  unfold ratF
  have := X.nonneg (D.b₂ v); have := l2Norm_nonneg (L *ᵥ (D.Γ *ᵥ (A *ᵥ v)))
  have := l2Norm_nonneg (L *ᵥ v)
  positivity

theorem ratF_contOn (D : AngularData ι) {L : Matrix κ ι ℂ} (hL : ∀ x, L *ᵥ x = 0 → x = 0)
    (X : Cutoff) (A : Matrix ι ι ℂ) : ContinuousOn (ratF D L X A) {z | z ≠ 0} := by
  unfold ratF
  refine (X.smooth.continuous.comp_continuousOn (b₂_c1 D).continuousOn).mul ?_
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (continuous_l2Norm.comp ((continuous_mulVec' L).comp
      ((continuous_mulVec' D.Γ).comp (continuous_mulVec' A)))).continuousOn
  · exact (continuous_l2Norm.comp (continuous_mulVec' L)).continuousOn
  · intro z hz; exact (ConeDivergence.l2Norm_pos fun h => hz (hL z h)).ne'

namespace Scales

variable {D : AngularData ι} {σ Y Zb : ℝ} (S : Scales D σ Y Zb) (R₁ : ℝ)
include S

theorem Pc_nonneg : 0 ≤ Pc Zb R₁ := add_nonneg (Real.sqrt_nonneg _) S.Zb_nonneg

theorem Kr_nonneg' : 0 ≤ Kr Y Zb R₁ := by
  unfold Kr; have := S.Pc_nonneg R₁; have := S.Y_pos; have := S.cOne_pos; positivity

theorem KW_nonneg : 0 ≤ KW σ Y Zb R₁ := by
  unfold KW; have := S.mOp_nonneg; have := S.Kr_nonneg' R₁; positivity

theorem Kcorr_nonneg : 0 ≤ Kcorr σ Y Zb R₁ := by
  unfold Kcorr; have := S.σ_pos; have := S.mOp_nonneg; have := S.Kr_nonneg' R₁
  have := S.Zb_nonneg; positivity

theorem Kb_nonneg : 0 ≤ Kb σ Y Zb R₁ := by
  unfold Kb; have := S.σ_pos; have := S.Pc_nonneg R₁; have := S.Kr_nonneg' R₁
  have := S.Kcorr_nonneg R₁; have := S.Zb_nonneg; positivity

theorem ell0_nonneg : 0 ≤ ell0 σ Zb R₁ := by unfold ell0; have := S.σ_pos; positivity

theorem KDelta_nonneg : 0 ≤ KDelta σ Y Zb R₁ := by
  unfold KDelta; have := S.mOp_nonneg; have := S.ell0_nonneg R₁; positivity

theorem dW_nonneg : 0 ≤ dW σ Y Zb R₁ := by
  unfold dW; have := S.mOp_nonneg; have := S.KW_nonneg R₁; positivity

theorem ellh_nonneg : 0 ≤ ellh σ Y Zb R₁ := by
  unfold ellh; have := S.ell0_nonneg R₁; have := S.Y_pos; positivity

theorem Kh_nonneg : 0 ≤ Kh σ Y Zb R₁ := by
  unfold Kh Bnum; have := S.mOp_nonneg; have := S.ellh_nonneg R₁; positivity

theorem Kdh_nonneg : 0 ≤ Kdh σ Y Zb R₁ := by
  unfold Kdh Bnum Bnum' Bden'; have := S.mOp_nonneg; have := S.ellh_nonneg R₁
  have := S.dW_nonneg R₁; have := S.Zb_nonneg; positivity

end Scales

/-- `D(χ(b₂)Ψ)[w] = χ'(b₂) Db₂[w] Ψ + χ(b₂) DΨ[w]`. -/
theorem fderiv_cut (D : AngularData ι) (X : Cutoff) {Ψ : (ι → ℂ) → ℝ} {v : ι → ℂ} (hv : v ≠ 0)
    (hΨ : DifferentiableAt ℝ Ψ v) (w : ι → ℂ) :
    fderiv ℝ (fun y => X.χ (D.b₂ y) * Ψ y) v w =
      deriv X.χ (D.b₂ v) * fderiv ℝ D.b₂ v w * Ψ v + X.χ (D.b₂ v) * fderiv ℝ Ψ v w := by
  have hb : HasFDerivAt D.b₂ (fderiv ℝ D.b₂ v) v := (dAt (b₂_c1 D) hv).hasFDerivAt
  have hχ : HasDerivAt X.χ (deriv X.χ (D.b₂ v)) (D.b₂ v) :=
    ((X.smooth.differentiable one_ne_zero) _).hasDerivAt
  have h : HasFDerivAt (fun y => X.χ (D.b₂ y) * Ψ y) _ v :=
    (hχ.comp_hasFDerivAt v hb).mul hΨ.hasFDerivAt
  rw [h.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    Function.comp_apply]
  ring

/-- `D(h̃Φ)[w] = Dh̃[w] Φ + h̃ DΦ[w]`. -/
theorem fderiv_mul_apply {G H : (ι → ℂ) → ℝ} {v : ι → ℂ} (hG : DifferentiableAt ℝ G v)
    (hH : DifferentiableAt ℝ H v) (w : ι → ℂ) :
    fderiv ℝ (fun y => G y * H y) v w = fderiv ℝ G v w * H v + G v * fderiv ℝ H v w := by
  have h : HasFDerivAt (fun y => G y * H y) _ v := hG.hasFDerivAt.mul hH.hasFDerivAt
  rw [h.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

variable {D : AngularData ι} {σ Y Zb : ℝ}

/-- **Pointwise majorant of the Stein integrand** for `F = χ(b₂)Ψ` along a field `W`. -/
theorem pw_main (S : Scales D σ Y Zb) (X : Cutoff) {Zf Ψ : (ι → ℂ) → ℝ} {v : ι → ℂ}
    (hv : normSqSum v = 1) (hZ0 : 0 ≤ Zf v) (hΨd : DifferentiableAt ℝ Ψ v) {W : ι → ℂ}
    {BΨ : ℝ} (hB0 : 0 ≤ BΨ)
    (hcut : D.b₂ v ≤ X.R₁ → |fderiv ℝ D.b₂ v W| ≤ Kb σ Y Zb X.R₁ ∧ |Ψ v| ≤ BΨ ∧
      l2Norm W ≤ KW σ Y Zb X.R₁) :
    |Real.exp (D.expo v) * (Zf v * fderiv ℝ (fun y => X.χ (D.b₂ y) * Ψ y) v W +
        X.χ (D.b₂ v) * Ψ v * fderiv ℝ Zf v W)| ≤
      X.M₁ * Kb σ Y Zb X.R₁ * BΨ * (Real.exp (D.expo v) * Zf v) +
        Real.exp (D.expo v) * Zf v * (X.χ (D.b₂ v) * |fderiv ℝ Ψ v W|) +
        BΨ * KW σ Y Zb X.R₁ * (Real.exp (D.expo v) * X.χ (D.b₂ v) * gradNorm Zf v) := by
  rw [fderiv_cut D X (ne_zero_of_unit hv) hΨd W]
  have hE : 0 < Real.exp (D.expo v) := Real.exp_pos _
  have hKb := S.Kb_nonneg X.R₁
  have hKW := S.KW_nonneg X.R₁
  have hM1 := X.M₁_nonneg
  have hχ0 := X.nonneg (D.b₂ v)
  have hρ : 0 ≤ Real.exp (D.expo v) * Zf v := by positivity
  by_cases hb : D.b₂ v ≤ X.R₁
  · obtain ⟨h1, h2, h3⟩ := hcut hb
    have hz : |fderiv ℝ Zf v W| ≤ KW σ Y Zb X.R₁ * gradNorm Zf v :=
      (abs_fderiv_le_gradNorm _ _ _).trans (mul_le_mul_of_nonneg_right h3 (gradNorm_nonneg _ _))
    have e : Real.exp (D.expo v) * (Zf v * (deriv X.χ (D.b₂ v) * fderiv ℝ D.b₂ v W * Ψ v +
        X.χ (D.b₂ v) * fderiv ℝ Ψ v W) + X.χ (D.b₂ v) * Ψ v * fderiv ℝ Zf v W) =
        (Real.exp (D.expo v) * Zf v) * (deriv X.χ (D.b₂ v) * fderiv ℝ D.b₂ v W * Ψ v) +
          (Real.exp (D.expo v) * Zf v) * (X.χ (D.b₂ v) * fderiv ℝ Ψ v W) +
          (Real.exp (D.expo v) * X.χ (D.b₂ v)) * (Ψ v * fderiv ℝ Zf v W) := by ring
    rw [e]
    have hEχ : 0 ≤ Real.exp (D.expo v) * X.χ (D.b₂ v) := by positivity
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_mul, abs_of_nonneg hρ]
      have := abs_mul_le_of (abs_mul_le_of (X.deriv_le (D.b₂ v)) h1) h2
      calc Real.exp (D.expo v) * Zf v * |deriv X.χ (D.b₂ v) * fderiv ℝ D.b₂ v W * Ψ v| ≤
          Real.exp (D.expo v) * Zf v * (X.M₁ * Kb σ Y Zb X.R₁ * BΨ) :=
            mul_le_mul_of_nonneg_left this hρ
        _ = _ := by ring
    · rw [abs_mul, abs_of_nonneg hρ, abs_mul, abs_of_nonneg hχ0]
    · rw [abs_mul, abs_of_nonneg hEχ]
      have := abs_mul_le_of h2 hz
      calc Real.exp (D.expo v) * X.χ (D.b₂ v) * |Ψ v * fderiv ℝ Zf v W| ≤
          Real.exp (D.expo v) * X.χ (D.b₂ v) * (BΨ * (KW σ Y Zb X.R₁ * gradNorm Zf v)) :=
            mul_le_mul_of_nonneg_left this hEχ
        _ = _ := by ring
  · push Not at hb
    rw [X.supp _ hb, X.deriv_eq_zero hb]
    simp only [zero_mul, mul_zero, add_zero, abs_zero]
    positivity

/-- **Direct differentiation bound** under `χ`: `χ|DΦ[W_A]| ≤ 2L_φ ν-ratio(A) + 2L_φK ν-ratio(I)`
when `|r_A| ≤ K` on the support of `χ`. -/
theorem pw_DΦ (D : AngularData ι) {L : Matrix κ ι ℂ} (hL : ∀ x, L *ᵥ x = 0 → x = 0)
    (X : Cutoff) {Φ : (ι → ℂ) → ℝ} {Lφ : ℝ} (hLφ : 0 ≤ Lφ) (hlip : ReconLip L Φ Lφ)
    {v : ι → ℂ} (hv : v ≠ 0) (hd : DifferentiableAt ℝ Φ v) (A : Matrix ι ι ℂ) {K : ℝ}
    (hr : X.χ (D.b₂ v) ≠ 0 → |D.ratio A v| ≤ K) :
    X.χ (D.b₂ v) * |fderiv ℝ Φ v (D.field A v)| ≤
      2 * Lφ * ratF D L X A v + 2 * Lφ * K * ratF D L X 1 v := by
  have h := abs_fderiv_field_le D hL hLφ hlip hv hd A
  have hc := X.nonneg (D.b₂ v)
  have hpos : 0 < l2Norm (L *ᵥ v) := ConeDivergence.l2Norm_pos fun h => hv (hL v h)
  unfold ratF; rw [one_mulVec]
  by_cases h0 : X.χ (D.b₂ v) = 0
  · rw [h0]; simp
  · have hr' := hr h0
    have h1 : |D.ratio A v| * l2Norm (L *ᵥ (D.Γ *ᵥ v)) ≤ K * l2Norm (L *ᵥ (D.Γ *ᵥ v)) :=
      mul_le_mul_of_nonneg_right hr' (l2Norm_nonneg _)
    have h2 : 2 * Lφ * (l2Norm (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) + |D.ratio A v| *
        l2Norm (L *ᵥ (D.Γ *ᵥ v))) / l2Norm (L *ᵥ v) ≤
        2 * Lφ * (l2Norm (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) + K * l2Norm (L *ᵥ (D.Γ *ᵥ v))) /
          l2Norm (L *ᵥ v) := by
      refine div_le_div_of_nonneg_right ?_ hpos.le
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc X.χ (D.b₂ v) * |fderiv ℝ Φ v (D.field A v)| ≤
        X.χ (D.b₂ v) * (2 * Lφ * (l2Norm (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) + K *
          l2Norm (L *ᵥ (D.Γ *ᵥ v))) / l2Norm (L *ᵥ v)) :=
          mul_le_mul_of_nonneg_left (h.trans h2) hc
      _ = _ := by ring

/-- The `Δ_A` term: `|e^{q}𝔷 χΨ Δ| ≤ M₀ B_Ψ K_Δ e^{q}𝔷` when `|Ψ| ≤ B_Ψ, |Δ| ≤ K_Δ` on the cutoff. -/
theorem pw_Delta (X : Cutoff) {Zf Ψ Δ : (ι → ℂ) → ℝ} {v : ι → ℂ} (hZ0 : 0 ≤ Zf v) {BΨ KΔ : ℝ}
    (hB0 : 0 ≤ BΨ) (hK0 : 0 ≤ KΔ)
    (hcut : D.b₂ v ≤ X.R₁ → |Ψ v| ≤ BΨ ∧ |Δ v| ≤ KΔ) :
    |Real.exp (D.expo v) * Zf v * (X.χ (D.b₂ v) * Ψ v) * Δ v| ≤
      X.M₀ * BΨ * KΔ * (Real.exp (D.expo v) * Zf v) := by
  have hE : 0 < Real.exp (D.expo v) := Real.exp_pos _
  have hρ : 0 ≤ Real.exp (D.expo v) * Zf v := by positivity
  have hM0 := X.M₀_nonneg
  by_cases hb : D.b₂ v ≤ X.R₁
  · obtain ⟨h1, h2⟩ := hcut hb
    have hχ : |X.χ (D.b₂ v)| ≤ X.M₀ := by rw [abs_of_nonneg (X.nonneg _)]; exact X.le _
    have := abs_mul_le_of (abs_mul_le_of hχ h1) h2
    rw [mul_assoc, abs_mul, abs_of_nonneg hρ]
    calc Real.exp (D.expo v) * Zf v * |X.χ (D.b₂ v) * Ψ v * Δ v| ≤
        Real.exp (D.expo v) * Zf v * (X.M₀ * BΨ * KΔ) := mul_le_mul_of_nonneg_left this hρ
      _ = _ := by ring
  · push Not at hb
    rw [X.supp _ hb]
    simp only [zero_mul, mul_zero, abs_zero]
    positivity

end BlockBand.Angular.Ratio
