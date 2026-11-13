module

public import BlockBand.Native.CEH.ETH.ZigPathCoreWindow
public import BlockBand.Native.CEH.ETH.ZigGlueWindow
public import BlockBand.Native.CEH.ETH.ZigGlueFTC
public import BlockBand.Native.CEH.ETH.ZigTailFamily
public import BlockBand.Native.CEH.ETH.BracketsFlowZ

/-!
# CEH ETH: generic facts for the assembly of the zig closure

Continuity of the flow resolvent paths, the heights in both constellations, the cross-term bound in
the form required by the path core, and the splitting of complex set integrals. The only measure
is Lebesgue measure on `ℝ`; all statements are pathwise.

* `zcl_continuous_normalizedTrace`, `zcl_continuous_imaginaryPart`: continuity of `⟨·⟩` and
  `Im`.
* `zcl_abs_im_flowSpectral_cz`: in both constellations (`ztl_cz b`), on `[0, s]`,
  `|Im z_{r}| = zigHeight |Im z| |Im m| s r`.
* `zcl_norm_cross_le`: **the cross-term bound in the form of the path core** (`cross_le`): if the
  four chains `⟨R₁^{(a)} A R₂^{(b)}⟩` all have modulus `≤ x`, then `|zgl_cross R₁ R₂ A| ≤ 4x²`
  (each of the two products of `zgl_cross_eq` is at most `2x²`).
* `zcl_integral_Ioc_eq_mk`: for an integrable `f : ℝ → ℂ`,
  `∫_{(0,t]} f = ⟨∫_{(0,t]} Re f, ∫_{(0,t]} Im f⟩`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory Matrix Set
open BlockBand.Native.CEH.Flow BlockBand.Native.CEH.Zig BlockBand.Native.CEH.LocalLaw
open BlockBand.External.CEH (normalizedTrace)
open scoped NNReal ENNReal ComplexConjugate

variable {N : ℕ}

/-!
## Continuity
-/

theorem zcl_continuous_normalizedTrace :
    Continuous (normalizedTrace : Matrix (Fin N) (Fin N) ℂ → ℂ) := by
  unfold normalizedTrace
  exact continuous_const.mul continuous_id.matrix_trace

theorem zcl_continuous_imaginaryPart :
    Continuous (External.CEH.imaginaryPart : Matrix (Fin N) (Fin N) ℂ →
      Matrix (Fin N) (Fin N) ℂ) := by
  unfold External.CEH.imaginaryPart
  fun_prop

/-- **The sample path of a flow resolvent is continuous on `[0, s]`** (any `m` with
`Im z · Im m ≥ 0`). -/
theorem zcl_continuousOn_pathR {Ω : Type} {F : Matrix (Fin N) (Fin N) ℂ}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {ω : Ω}
    (hH : ∀ σ, (F + G σ ω).IsHermitian) (hGc : Continuous fun t => G t ω) {z m : ℂ}
    (hz : z.im ≠ 0) (hm : 0 ≤ z.im * m.im) (s : ℝ≥0) :
    ContinuousOn (pathR F G z m s ω) (Icc 0 (s : ℝ)) := by
  have hA : Continuous fun t : ℝ => F + G t.toNNReal ω -
      flowSpectral z m s t.toNNReal • (1 : Matrix (Fin N) (Fin N) ℂ) :=
    (continuous_const.add (hGc.comp continuous_real_toNNReal)).sub
      ((continuous_flowSpectral_toNNReal z m s).smul continuous_const)
  intro t ht
  have hσ : ((t.toNNReal : ℝ≥0) : ℝ) ≤ (s : ℝ) := by
    rw [Real.coe_toNNReal _ ht.1]; exact ht.2
  have hdet := (Phase1.isUnit_det_sub_smul (hH t.toNNReal)
    (flowSpectral_im_ne_zero hz hm hσ)).ne_zero
  have hinv := continuousAt_matrix_inv (F + G t.toNNReal ω -
      flowSpectral z m s t.toNNReal • (1 : Matrix (Fin N) (Fin N) ℂ))
    (NormedRing.inverse_continuousAt (Units.mk0 _ hdet))
  exact (ContinuousAt.comp (g := fun X : Matrix (Fin N) (Fin N) ℂ => X⁻¹)
    (f := fun t : ℝ => F + G t.toNNReal ω -
      flowSpectral z m s t.toNNReal • (1 : Matrix (Fin N) (Fin N) ℂ)) (x := t) hinv
    hA.continuousAt).continuousWithinAt

/-- The sample path is `Phase1.resolvent` at the characteristic. -/
theorem zcl_pathR_eq_resolvent {Ω : Type} (F : Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (z m : ℂ) (s : ℝ≥0) (ω : Ω) (t : ℝ) :
    pathR F G z m s ω t =
      Phase1.resolvent (F + G t.toNNReal ω) (flowSpectral z m s t.toNNReal) := rfl

/-!
## Heights in both constellations
-/

theorem zcl_abs_cz_im (b : Bool) (w : ℂ) : |(ztl_cz b w).im| = |w.im| := by
  cases b <;> simp [ztl_cz]

/-- `|Im z_r| = zigHeight |Im z| |Im m| s r` in both constellations, for `r ∈ [0, s]`. -/
theorem zcl_abs_im_flowSpectral_cz (b : Bool) {z m : ℂ} (hm : 0 ≤ z.im * m.im) {s : ℝ≥0}
    {r : ℝ} (hr : r ∈ Icc 0 (s : ℝ)) :
    |(flowSpectral (ztl_cz b z) (ztl_cz b m) s r.toNNReal).im| =
      zigHeight |z.im| |m.im| s r := by
  have hσ : ((r.toNNReal : ℝ≥0) : ℝ) ≤ (s : ℝ) := by
    rw [Real.coe_toNNReal _ hr.1]; exact hr.2
  rw [zgl_abs_im_flowSpectral (ztl_cz_hm b hm) hσ, zcl_abs_cz_im, zcl_abs_cz_im,
    Real.coe_toNNReal _ hr.1]

theorem zcl_flowSpectral_cz_im_ne_zero (b : Bool) {z m : ℂ} (hz : z.im ≠ 0)
    (hm : 0 ≤ z.im * m.im) {s : ℝ≥0} {r : ℝ} (hr : r ∈ Icc 0 (s : ℝ)) :
    (flowSpectral (ztl_cz b z) (ztl_cz b m) s r.toNNReal).im ≠ 0 := by
  have hσ : ((r.toNNReal : ℝ≥0) : ℝ) ≤ (s : ℝ) := by
    rw [Real.coe_toNNReal _ hr.1]; exact hr.2
  exact flowSpectral_im_ne_zero (ztl_cz_im_ne_zero b hz) (ztl_cz_hm b hm) hσ

/-!
## The cross-term bound in the form of the path core
-/

/-- Scalar core: with all four chains of modulus `≤ x`, the polarized cross term is `≤ 4x²`. -/
theorem zcl_cross_scalar_le {x₁₁ x₁₂ x₂₁ x₂₂ : ℂ} {x : ℝ} (h₁₁ : ‖x₁₁‖ ≤ x) (h₁₂ : ‖x₁₂‖ ≤ x)
    (h₂₁ : ‖x₂₁‖ ≤ x) (h₂₂ : ‖x₂₂‖ ≤ x) :
    ‖conj x₂₁ * (-(1 / 4 : ℂ) * (x₁₁ - x₁₂ - x₂₁ + x₂₂)) +
        x₂₁ * conj (-(1 / 4 : ℂ) * (x₁₁ - x₁₂ - x₂₁ + x₂₂)) +
        (2 * Complex.I)⁻¹ * (x₁₁ - x₂₁) * conj ((2 * Complex.I)⁻¹ * (x₂₁ - x₂₂)) +
        conj ((2 * Complex.I)⁻¹ * (x₁₁ - x₂₁)) * ((2 * Complex.I)⁻¹ * (x₂₁ - x₂₂))‖ ≤
      4 * x ^ 2 := by
  have hx : 0 ≤ x := (norm_nonneg _).trans h₁₁
  have hT : ‖-(1 / 4 : ℂ) * (x₁₁ - x₁₂ - x₂₁ + x₂₂)‖ ≤ x := by
    rw [norm_mul, norm_neg, norm_div, norm_one, Complex.norm_ofNat]
    have : ‖x₁₁ - x₁₂ - x₂₁ + x₂₂‖ ≤ 4 * x := by
      refine (norm_add_le _ _).trans ?_
      have h1 := norm_sub_le (x₁₁ - x₁₂) x₂₁
      have h2 := norm_sub_le x₁₁ x₁₂
      linarith
    linarith
  have hp : ‖(2 * Complex.I)⁻¹ * (x₁₁ - x₂₁)‖ ≤ x := by
    rw [norm_mul, zgl_norm_two_I_inv]
    have := norm_sub_le x₁₁ x₂₁
    linarith
  have hq : ‖(2 * Complex.I)⁻¹ * (x₂₁ - x₂₂)‖ ≤ x := by
    rw [norm_mul, zgl_norm_two_I_inv]
    have := norm_sub_le x₂₁ x₂₂
    linarith
  set T := -(1 / 4 : ℂ) * (x₁₁ - x₁₂ - x₂₁ + x₂₂)
  set p := (2 * Complex.I)⁻¹ * (x₁₁ - x₂₁)
  set q := (2 * Complex.I)⁻¹ * (x₂₁ - x₂₂)
  have hsum : ‖conj x₂₁ * T + x₂₁ * conj T + p * conj q + conj p * q‖ ≤
      2 * (‖x₂₁‖ * ‖T‖) + 2 * (‖p‖ * ‖q‖) := by
    refine norm_add₄_le.trans (le_of_eq ?_)
    simp only [norm_mul, Complex.norm_conj]
    ring
  refine hsum.trans ?_
  have e1 : ‖x₂₁‖ * ‖T‖ ≤ x * x := mul_le_mul h₂₁ hT (norm_nonneg _) hx
  have e2 : ‖p‖ * ‖q‖ ≤ x * x := mul_le_mul hp hq (norm_nonneg _) hx
  nlinarith

/-- **Cross-term bound, path-core form**: if `|⟨R₁^{(a)} A R₂^{(b)}⟩| ≤ x` in all four constellations, then
`|zgl_cross R₁ R₂ A| ≤ 4x²`. -/
theorem zcl_norm_cross_le (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) {x : ℝ}
    (h₁₁ : ‖normalizedTrace (R₁ * A * R₂)‖ ≤ x) (h₁₂ : ‖normalizedTrace (R₁ * A * R₂ᴴ)‖ ≤ x)
    (h₂₁ : ‖normalizedTrace (R₁ᴴ * A * R₂)‖ ≤ x) (h₂₂ : ‖normalizedTrace (R₁ᴴ * A * R₂ᴴ)‖ ≤ x) :
    ‖zgl_cross R₁ R₂ A‖ ≤ 4 * x ^ 2 := by
  rw [zgl_cross_eq]
  exact zcl_cross_scalar_le h₁₁ h₁₂ h₂₁ h₂₂

/-!
## Complex set integrals
-/

/-- `∫_{(0,t]} f = ⟨∫_{(0,t]} Re f, ∫_{(0,t]} Im f⟩` for integrable `f : ℝ → ℂ`. -/
theorem zcl_integral_Ioc_eq_mk {f : ℝ → ℂ} {t : ℝ} (hf : IntegrableOn f (Ioc 0 t)) :
    ∫ r in Ioc 0 t, f r = ⟨∫ r in Ioc 0 t, (f r).re, ∫ r in Ioc 0 t, (f r).im⟩ := by
  have h1 := integral_re (μ := volume.restrict (Ioc 0 t)) hf
  have h2 := integral_im (μ := volume.restrict (Ioc 0 t)) hf
  apply Complex.ext
  · simp only [RCLike.re_to_complex] at h1
    exact h1.symm
  · simp only [RCLike.im_to_complex] at h2
    exact h2.symm

end BlockBand.Native.CEH.ETH
