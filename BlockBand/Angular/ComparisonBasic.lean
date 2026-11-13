module

public import BlockBand.Angular.Ratio

/-!
# Reconstructed-direction tests for the angular comparison

A test `Φ(v) = φ(𝓛v/‖𝓛v‖)` with `φ` `L_φ`-Lipschitz on the unit sphere of `Ran 𝓛` is
encoded intrinsically by `ReconLip L Φ L_φ`:
`|Φ v - Φ v'| ≤ L_φ ‖𝓛v/‖𝓛v‖ - 𝓛v'/‖𝓛v'‖‖` for `v, v' ≠ 0` (Euclidean norms); conversely
every such `Φ` factors through `v ↦ 𝓛v/‖𝓛v‖`. For such `Φ`, differentiable at `v ≠ 0`,
`|DΦ(v)[w]| ≤ 2 L_φ ‖𝓛w‖/‖𝓛v‖` (`abs_fderiv_le_of_reconLip`), with no lower bound on any
singular value of `𝓛`. With `w = W_A = Γ(A - r_A)v` this gives the field bound
(`abs_fderiv_field_le`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Ratio

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.DegreeZero
open BlockBand.Angular.ProjectiveStein BlockBand.Angular.Reference BlockBand.Angular.Stein
open scoped ComplexConjugate

section Normalize

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `‖x/‖x‖ - y/‖y‖‖ ≤ 2‖x - y‖/‖x‖` for `x ≠ 0` (any `y`, with `0⁻¹ = 0`). -/
theorem norm_normalize_sub_le {x : E} (hx : x ≠ 0) (y : E) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ / ‖x‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have e : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y = ‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y := by
    rw [smul_sub, sub_smul]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hn]
  have h2 : |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ ≤ ‖x - y‖ / ‖x‖ := by
    rcases (norm_nonneg y).lt_or_eq with hy | hy
    · have : |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ = |‖y‖ - ‖x‖| / ‖x‖ := by
        rw [show ‖x‖⁻¹ - ‖y‖⁻¹ = (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) by field_simp, abs_div,
          abs_of_pos (mul_pos hn hy)]
        field_simp
      rw [this]
      exact div_le_div_of_nonneg_right (by rw [abs_sub_comm]; exact abs_norm_sub_norm_le x y)
        hn.le
    · rw [← hy, mul_zero]; positivity
  calc ‖x‖⁻¹ * ‖x - y‖ + |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ ≤ ‖x - y‖ / ‖x‖ + ‖x - y‖ / ‖x‖ := by
        rw [inv_mul_eq_div]; linarith
    _ = 2 * ‖x - y‖ / ‖x‖ := by ring

end Normalize

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem l2Norm_eq_norm (x : κ → ℂ) : l2Norm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ κ)‖ := by
  rw [EuclideanSpace.norm_eq]; rfl

/-- The reconstructed direction `𝓛v/‖𝓛v‖` (Euclidean normalization). -/
def recon (L : Matrix κ ι ℂ) (v : ι → ℂ) : κ → ℂ := ((l2Norm (L *ᵥ v))⁻¹ : ℂ) • (L *ᵥ v)

/-- `Φ` is an `L_φ`-Lipschitz function of the reconstructed direction. -/
def ReconLip (L : Matrix κ ι ℂ) (Φ : (ι → ℂ) → ℝ) (Lφ : ℝ) : Prop :=
  ∀ v v' : ι → ℂ, v ≠ 0 → v' ≠ 0 → |Φ v - Φ v'| ≤ Lφ * l2Norm (recon L v - recon L v')

theorem l2Norm_recon_sub_le (L : Matrix κ ι ℂ) {v : ι → ℂ} (hv : L *ᵥ v ≠ 0) (v' : ι → ℂ) :
    l2Norm (recon L v - recon L v') ≤ 2 * l2Norm (L *ᵥ v - L *ᵥ v') / l2Norm (L *ᵥ v) := by
  set x : EuclideanSpace ℂ κ := WithLp.toLp 2 (L *ᵥ v)
  set y : EuclideanSpace ℂ κ := WithLp.toLp 2 (L *ᵥ v')
  have hx : x ≠ 0 := fun h => hv (by simpa [x] using congrArg (WithLp.ofLp) h)
  have e : WithLp.toLp 2 (recon L v - recon L v') = ‖x‖⁻¹ • x - ‖y‖⁻¹ • y := by
    simp only [recon, l2Norm_eq_norm, WithLp.toLp_sub, WithLp.toLp_smul, x, y]
    rw [← Complex.coe_smul, ← Complex.coe_smul]; push_cast; rfl
  rw [l2Norm_eq_norm, e, l2Norm_eq_norm, l2Norm_eq_norm, WithLp.toLp_sub]
  exact norm_normalize_sub_le hx y

/-- **Direct differentiation** (in the proof of the angular comparison): for `Φ` Lipschitz in the
reconstructed direction and differentiable at `v ≠ 0`, `|DΦ(v)[w]| ≤ 2L_φ ‖𝓛w‖/‖𝓛v‖`. -/
theorem abs_fderiv_le_of_reconLip {L : Matrix κ ι ℂ} (hL : ∀ x, L *ᵥ x = 0 → x = 0)
    {Φ : (ι → ℂ) → ℝ} {Lφ : ℝ} (hLφ : 0 ≤ Lφ) (hlip : ReconLip L Φ Lφ) {v : ι → ℂ}
    (hv : v ≠ 0) (hd : DifferentiableAt ℝ Φ v) (w : ι → ℂ) :
    |fderiv ℝ Φ v w| ≤ 2 * Lφ * l2Norm (L *ᵥ w) / l2Norm (L *ᵥ v) := by
  have hLv : L *ᵥ v ≠ 0 := fun h => hv (hL v h)
  have hpos : 0 < l2Norm (L *ᵥ v) := ConeDivergence.l2Norm_pos hLv
  have hline : HasDerivAt (fun τ : ℝ => v + τ • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  have hf : HasDerivAt (fun τ : ℝ => Φ (v + τ • w)) (fderiv ℝ Φ v w) 0 := by
    have hD : HasFDerivAt Φ (fderiv ℝ Φ v) (v + (0 : ℝ) • w) := by simpa using hd.hasFDerivAt
    exact hD.comp_hasDerivAt (0 : ℝ) hline
  have hev : ∀ᶠ τ in nhds (0 : ℝ), v + τ • w ≠ 0 := by
    have hc : Continuous fun τ : ℝ => v + τ • w := by fun_prop
    exact hc.continuousAt.eventually_ne (by simpa using hv)
  have hC : 0 ≤ 2 * Lφ * l2Norm (L *ᵥ w) / l2Norm (L *ᵥ v) := by
    have := l2Norm_nonneg (L *ᵥ w); positivity
  have hb := hf.le_of_lip' hC (by
    filter_upwards [hev] with τ hτ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, zero_smul, add_zero, sub_zero, abs_sub_comm]
    refine (hlip v (v + τ • w) hv hτ).trans ?_
    have h1 := l2Norm_recon_sub_le L hLv (v + τ • w)
    have h2 : L *ᵥ v - L *ᵥ (v + τ • w) = ((-τ : ℝ) : ℂ) • (L *ᵥ w) := by
      rw [mulVec_add, mulVec_smul, ← complex_smul_eq_real_smul]; push_cast
      rw [neg_smul]; abel
    have h3 : l2Norm (((-τ : ℝ) : ℂ) • (L *ᵥ w)) = |τ| * l2Norm (L *ᵥ w) := by
      rw [l2Norm_eq, l2Norm_eq, normSqSum_real_smul, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq_eq_abs, abs_neg]
    rw [h2, h3] at h1
    calc Lφ * l2Norm (recon L v - recon L (v + τ • w))
        ≤ Lφ * (2 * (|τ| * l2Norm (L *ᵥ w)) / l2Norm (L *ᵥ v)) :=
          mul_le_mul_of_nonneg_left h1 hLφ
      _ = 2 * Lφ * l2Norm (L *ᵥ w) / l2Norm (L *ᵥ v) * |τ| := by ring)
  rwa [Real.norm_eq_abs] at hb

/-- The field bound `|W_AΦ| ≤ 2L_φ (‖𝓛ΓAv‖ + |r_A| ‖𝓛Γv‖)/‖𝓛v‖`, `W_A = Γ(A - r_A)v`. -/
theorem abs_fderiv_field_le (D : AngularData ι) {L : Matrix κ ι ℂ}
    (hL : ∀ x, L *ᵥ x = 0 → x = 0) {Φ : (ι → ℂ) → ℝ} {Lφ : ℝ} (hLφ : 0 ≤ Lφ)
    (hlip : ReconLip L Φ Lφ) {v : ι → ℂ} (hv : v ≠ 0) (hd : DifferentiableAt ℝ Φ v)
    (A : Matrix ι ι ℂ) :
    |fderiv ℝ Φ v (D.field A v)| ≤ 2 * Lφ * (l2Norm (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) +
      |D.ratio A v| * l2Norm (L *ᵥ (D.Γ *ᵥ v))) / l2Norm (L *ᵥ v) := by
  refine (abs_fderiv_le_of_reconLip hL hLφ hlip hv hd _).trans ?_
  have hpos : 0 < l2Norm (L *ᵥ v) := ConeDivergence.l2Norm_pos fun h => hv (hL v h)
  refine div_le_div_of_nonneg_right ?_ hpos.le
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [AngularData.field, mulVec_sub, mulVec_smul]
  have e : ∀ x y : κ → ℂ, l2Norm (x - y) ≤ l2Norm x + l2Norm y := fun x y => by
    rw [l2Norm_eq_norm, l2Norm_eq_norm, l2Norm_eq_norm, WithLp.toLp_sub]; exact norm_sub_le _ _
  refine (e _ _).trans (add_le_add le_rfl (le_of_eq ?_))
  rw [l2Norm_eq, l2Norm_eq, normSqSum_real_smul, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs]

end BlockBand.Angular.Ratio
