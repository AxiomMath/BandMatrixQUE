module

public import BlockBand.Endpoints.Poisson.PhaseFractionalScalar
public import BlockBand.Endpoints.Poisson.PhaseFractionalLaw

/-!
# Core of the projected fractional inverse: phase averaging for an arbitrary law

* `collarHat U = [[U, 0], [0, 0]]`, `twistedV V v θ = V (I + (e^{iθ} - 1) v v*)`;
* `fullQuad t U V v = v*(I - t Û V)⁻¹ v` (radial regulator `t`; `t = 1` is the boundary value);
* `lintegral_fullQuad_rpow_le`: for `0 ≤ t < 1`, `0 < p < 1`, unitary `V`, unit `v`, if for every
  twist angle `∫⁻ (2 Re q_θ - 1) dμ ≤ B` (`q_θ = fullQuad t U (twistedV V v θ) v`; the integrand
  is the quadratic form of the Poisson kernel of `t Û V_θ`), then
  `∫⁻ |fullQuad t U V v|^p dμ ≤ phaseConst p · B`, `phaseConst p < ∞`.

Steps 1–4 are those of the proof of the phase fractional-inverse lemma.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints.PhaseFractional

open MeasureTheory Matrix Filter Set Complex
open scoped ComplexOrder ComplexConjugate ENNReal Real Topology

/-!
## Scalar facts
-/

/-- `C_p = (2π)⁻¹ 2^p / cos(pπ/2) ∫_{(0,2π)} |1 - e^{iθ}|^{-p} dθ`. -/
def phaseConst (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * π)⁻¹ * 2 ^ p / Real.cos (p * π / 2)) *
    ∫⁻ θ in Ioo 0 (2 * π), ENNReal.ofReal (‖1 - circleMap 0 1 θ‖ ^ (-p))

theorem phaseConst_lt_top {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : phaseConst p < ∞ :=
  ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_boundaryWeight_lt_top hp0.le hp1)

theorem cos_pos_of_lt_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < Real.cos (p * π / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]

/-- The scalar Poisson majorant without the `cos(pπ/2)` factor. -/
theorem ofReal_rpow_le_lintegral {ζ : ℂ} (hζ : ‖ζ‖ < 1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ENNReal.ofReal (‖1 - ζ‖ ^ (-p)) ≤
      ENNReal.ofReal ((2 * π)⁻¹ * 2 ^ p / Real.cos (p * π / 2)) *
        ∫⁻ θ in Ioo 0 (2 * π), ENNReal.ofReal (_root_.poissonKernel 0 ζ (circleMap 0 1 θ)) *
          ENNReal.ofReal (‖1 - circleMap 0 1 θ‖ ^ (-p)) := by
  have hc := cos_pos_of_lt_one hp0 hp1
  have h := ofReal_cos_mul_rpow_le_lintegral hζ hp0 hp1
  have hsplit : ENNReal.ofReal ((2 * π)⁻¹ * 2 ^ p / Real.cos (p * π / 2)) =
      ENNReal.ofReal (Real.cos (p * π / 2))⁻¹ * ENNReal.ofReal ((2 * π)⁻¹ * 2 ^ p) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
    congr 1; field_simp
  have hcos : ENNReal.ofReal (‖1 - ζ‖ ^ (-p)) =
      ENNReal.ofReal (Real.cos (p * π / 2))⁻¹ *
        ENNReal.ofReal (Real.cos (p * π / 2) * ‖1 - ζ‖ ^ (-p)) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), ← mul_assoc, inv_mul_cancel₀ hc.ne',
      one_mul]
  rw [hcos, hsplit, mul_assoc]
  gcongr

/-- The point `ζ = 1 - q⁻¹`, which lies in the unit disk when `Re q > 1/2`. -/
def diskPoint (q : ℂ) : ℂ := 1 - q⁻¹

theorem norm_diskPoint_lt_one {q : ℂ} (hq : 1 / 2 < q.re) : ‖diskPoint q‖ < 1 := by
  have hq0 : q ≠ 0 := by intro h; rw [h] at hq; norm_num at hq
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have h1 : diskPoint q = (q - 1) / q := by rw [diskPoint]; field_simp
  rw [h1, norm_div, div_lt_one hn]
  have h2 : ‖q - 1‖ ^ 2 < ‖q‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2

theorem one_sub_diskPoint {q : ℂ} : 1 - diskPoint q = q⁻¹ := by rw [diskPoint]; ring

theorem norm_rpow_eq_one_sub_diskPoint (q : ℂ) (p : ℝ) :
    ‖q‖ ^ p = ‖1 - diskPoint q‖ ^ (-p) := by
  rw [one_sub_diskPoint, norm_inv, Real.inv_rpow (norm_nonneg _), Real.rpow_neg (norm_nonneg _),
    inv_inv]

/-- The Poisson weight of the twisted quadratic form: for
`|z| = 1`, `q ≠ 0`, `ζ = 1 - q⁻¹` in the disk, `D = 1 - (z̄ - 1)(q - 1) ≠ 0` and
`2 Re (q/D) - 1 = P_ζ(z)`. -/
theorem twist_poisson_weight {q z : ℂ} (hq : 1 / 2 < q.re) (hz : ‖z‖ = 1) :
    1 - (conj z - 1) * (q - 1) ≠ 0 ∧
      2 * (q / (1 - (conj z - 1) * (q - 1))).re - 1 =
        _root_.poissonKernel 0 (diskPoint q) z := by
  have hq0 : q ≠ 0 := by intro h; rw [h] at hq; norm_num at hq
  have hζ := norm_diskPoint_lt_one hq
  have hzζ : z - diskPoint q ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h] at hz; linarith
  have hzz : conj z * z = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]; simp
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hD : 1 - (conj z - 1) * (q - 1) = q * conj z * (z - diskPoint q) := by
    have hqq : q * q⁻¹ = 1 := mul_inv_cancel₀ hq0
    rw [diskPoint]
    linear_combination (-q) * hzz + (-conj z) * hqq
  have hconj0 : conj z ≠ 0 := by
    intro h; rw [h, zero_mul] at hzz; exact zero_ne_one hzz
  refine ⟨by rw [hD]; exact mul_ne_zero (mul_ne_zero hq0 hconj0) hzζ, ?_⟩
  have hquot : q / (1 - (conj z - 1) * (q - 1)) = z / (z - diskPoint q) := by
    rw [hD, div_eq_div_iff (mul_ne_zero (mul_ne_zero hq0 hconj0) hzζ) hzζ]
    linear_combination (-(q * (z - diskPoint q))) * hzz
  rw [hquot, poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
    herglotzRieszKernel_def]
  simp only [sub_zero]
  have : (z + diskPoint q) / (z - diskPoint q) = 2 * (z / (z - diskPoint q)) - 1 := by
    field_simp; ring
  rw [this]
  simp

/-!
## The collar compression and the twisted quadratic forms
-/

section Core

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- `Û = U ⊕ 0` on `Ran P ⊕ Ran P^⊥`. -/
def collarHat (U : Matrix α α ℂ) : Matrix (α ⊕ β) (α ⊕ β) ℂ := fromBlocks U 0 0 0

/-- The rank-one twist `V exp(iθ v v*) = V (I + (e^{iθ} - 1) v v*)` (unit `v`). -/
def twistedV (V : Matrix (α ⊕ β) (α ⊕ β) ℂ) (v : α ⊕ β → ℂ) (θ : ℝ) :
    Matrix (α ⊕ β) (α ⊕ β) ℂ :=
  V * rankOneTwist v (Complex.exp (θ * Complex.I))

/-- `v*(I - t Û V)⁻¹ v` (`t = 1` gives the boundary quantity of the phase fractional-inverse
lemma). -/
def fullQuad (t : ℝ) (U : Matrix α α ℂ) (V : Matrix (α ⊕ β) (α ⊕ β) ℂ) (v : α ⊕ β → ℂ) : ℂ :=
  resolventQuad ((t : ℂ) • (collarHat U * V)) v

theorem quadNorm_eq_one {κ : Type*} [Fintype κ] {v : κ → ℂ} (hv : star v ⬝ᵥ v = 1) :
    quadNorm v = 1 := by
  rw [quadNorm, hv]; simp

theorem exp_neg_mul_I_eq_conj (θ : ℝ) :
    Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) = conj (circleMap 0 1 θ) := by
  rw [circleMap_zero, Complex.ofReal_one, one_mul, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

theorem norm_exp_mul_I (θ : ℝ) : ‖Complex.exp (θ * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

/-- Pointwise Steps 1–4 for one collar sample. -/
theorem fullQuad_pointwise {U : Matrix α α ℂ} (hU : IsContraction U)
    {V : Matrix (α ⊕ β) (α ⊕ β) ℂ} (hV : Vᴴ * V = 1) {v : α ⊕ β → ℂ} (hv : star v ⬝ᵥ v = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    1 / 2 < (fullQuad t U V v).re ∧
      ∀ θ : ℝ, 2 * (fullQuad t U (twistedV V v (-θ)) v).re - 1 =
        _root_.poissonKernel 0 (diskPoint (fullQuad t U V v)) (circleMap 0 1 θ) := by
  have hc : IsContraction (collarHat (β := β) U * V) :=
    (isContraction_fromBlocks_zero hU).mul (isContraction_of_unitary hV)
  have hs := hc.smul_strict ht0 ht1
  have hX := hs.isUnit_det
  have hq : 1 / 2 < (fullQuad t U V v).re := by
    have h1 := two_re_quad_sub_eq _ hX v
    rw [quadNorm_eq_one hv] at h1
    set y := (1 - (t : ℂ) • (collarHat U * V))⁻¹ *ᵥ v with hy
    have hy0 : y ≠ 0 := by
      intro h0
      have := eq_sub_mulVec_inv hX v
      rw [← hy, h0] at this
      simp only [mulVec_zero, sub_zero] at this
      rw [this] at hv
      simp at hv
    have := hs y hy0
    rw [fullQuad]
    linarith
  refine ⟨hq, fun θ => ?_⟩
  set z := circleMap 0 1 θ with hz
  have hz1 : ‖z‖ = 1 := norm_circleMap_zero_one θ
  have hw := twist_poisson_weight hq hz1
  have htw : ((t : ℂ) • (collarHat U * twistedV V v (-θ))) =
      ((t : ℂ) • (collarHat U * V)) * rankOneTwist v (conj z) := by
    rw [twistedV, exp_neg_mul_I_eq_conj, ← hz, smul_mul_assoc, Matrix.mul_assoc]
  have hc' : IsContraction (collarHat (β := β) U * twistedV V v (-θ)) := by
    apply (isContraction_fromBlocks_zero hU).mul
    apply (isContraction_of_unitary hV).mul
    apply isContraction_of_unitary
    exact rankOneTwist_unitary hv (norm_exp_mul_I _)
  have hX' := (hc'.smul_strict ht0 ht1).isUnit_det
  rw [htw] at hX'
  rw [fullQuad, htw, quad_twist_eq hX hv hX' hw.1]
  exact hw.2

/-!
## Measurability
-/

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
theorem measurable_collarHat {Ω : Type*} [MeasurableSpace Ω] {U : Ω → Matrix α α ℂ}
    (hU : Measurable U) : Measurable (fun ω => collarHat (β := β) (U ω)) := by
  rw [Matrix.measurable_iff] at *
  rintro (i | i) (j | j)
  · exact hU i j
  all_goals simp only [collarHat, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.zero_apply]
  all_goals exact measurable_const

theorem measurable_quadForm {κ : Type*} [Fintype κ] {Ω : Type*} [MeasurableSpace Ω]
    {M : Ω → Matrix κ κ ℂ} (hM : Measurable M) (v : κ → ℂ) :
    Measurable (fun ω => star v ⬝ᵥ (M ω *ᵥ v)) := by
  simp only [dotProduct, mulVec]
  rw [Matrix.measurable_iff] at hM
  exact Finset.measurable_sum _ fun i _ => measurable_const.mul
    (Finset.measurable_sum _ fun j _ => (hM i j).mul measurable_const)

theorem measurable_fullQuad {Ω : Type*} [MeasurableSpace Ω] {U : Ω → Matrix α α ℂ}
    (hU : Measurable U) (t : ℝ) (V : Matrix (α ⊕ β) (α ⊕ β) ℂ) (v : α ⊕ β → ℂ) :
    Measurable (fun ω => fullQuad t (U ω) V v) := by
  unfold fullQuad resolventQuad
  apply measurable_quadForm
  apply measurable_matrix_inv'.comp
  apply measurable_matrix_sub measurable_const
  apply measurable_matrix_smul
  exact measurable_matrix_mul (measurable_collarHat hU) measurable_const

theorem measurable_poissonKernel_uncurry :
    Measurable (fun x : ℂ × ℂ => _root_.poissonKernel 0 x.1 x.2) := by
  have : (fun x : ℂ × ℂ => _root_.poissonKernel 0 x.1 x.2) =
      fun x => (‖x.2 - 0‖ ^ 2 - ‖x.1 - 0‖ ^ 2) / ‖(x.2 - 0) - (x.1 - 0)‖ ^ 2 :=
    funext fun x => poissonKernel_def 0 x.1 x.2
  rw [this]
  apply Measurable.div <;> fun_prop

theorem measurable_boundaryWeight (p : ℝ) :
    Measurable (fun θ : ℝ => ‖1 - circleMap 0 1 θ‖ ^ (-p)) :=
  (by fun_prop : Continuous fun θ : ℝ => ‖1 - circleMap 0 1 θ‖).measurable.pow_const _

/-- **Phase averaging for an arbitrary law** (Steps 1–4, radial form). -/
theorem lintegral_fullQuad_rpow_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {U : Ω → Matrix α α ℂ} (hUm : Measurable U) (hUc : ∀ᵐ ω ∂μ, IsContraction (U ω))
    {V : Matrix (α ⊕ β) (α ⊕ β) ℂ} (hV : Vᴴ * V = 1) {v : α ⊕ β → ℂ} (hv : star v ⬝ᵥ v = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {B : ℝ≥0∞}
    (hB : ∀ θ : ℝ, ∫⁻ ω, ENNReal.ofReal (2 * (fullQuad t (U ω) (twistedV V v θ) v).re - 1) ∂μ
      ≤ B) :
    ∫⁻ ω, ENNReal.ofReal (‖fullQuad t (U ω) V v‖ ^ p) ∂μ ≤ phaseConst p * B := by
  set c : ℝ := (2 * π)⁻¹ * 2 ^ p / Real.cos (p * π / 2) with hc
  set ζ : Ω → ℂ := fun ω => diskPoint (fullQuad t (U ω) V v) with hζ
  have hζm : Measurable ζ := measurable_const.sub ((measurable_fullQuad hUm t V v).inv)
  set w : ℝ → ℝ≥0∞ := fun θ => ENNReal.ofReal (‖1 - circleMap 0 1 θ‖ ^ (-p)) with hw
  have hwm : Measurable w := ENNReal.measurable_ofReal.comp (measurable_boundaryWeight p)
  set F : Ω → ℝ → ℝ≥0∞ := fun ω θ =>
    ENNReal.ofReal (_root_.poissonKernel 0 (ζ ω) (circleMap 0 1 θ)) * w θ with hF
  have hFm : Measurable (Function.uncurry F) := by
    show Measurable (fun x : Ω × ℝ =>
      ENNReal.ofReal (_root_.poissonKernel 0 (ζ x.1) (circleMap 0 1 x.2)) * w x.2)
    apply Measurable.fun_mul
    · apply ENNReal.measurable_ofReal.comp
      exact measurable_poissonKernel_uncurry.comp
        ((hζm.comp measurable_fst).prodMk ((by fun_prop : Continuous fun θ : ℝ =>
          circleMap 0 1 θ).measurable.comp measurable_snd))
    · exact hwm.comp measurable_snd
  -- Step 1: pointwise majorant
  have h1 : ∫⁻ ω, ENNReal.ofReal (‖fullQuad t (U ω) V v‖ ^ p) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal c * (∫⁻ θ in Ioo 0 (2 * π), F ω θ) ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [hUc] with ω hω
    have hpt := fullQuad_pointwise hω hV hv ht0 ht1
    rw [norm_rpow_eq_one_sub_diskPoint]
    exact ofReal_rpow_le_lintegral (norm_diskPoint_lt_one hpt.1) hp0 hp1
  -- Steps 2–3: Tonelli
  have h2 : ∫⁻ ω, ENNReal.ofReal c * (∫⁻ θ in Ioo 0 (2 * π), F ω θ) ∂μ =
      ENNReal.ofReal c * ∫⁻ θ in Ioo 0 (2 * π), ∫⁻ ω, F ω θ ∂μ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    exact lintegral_lintegral_swap hFm.aemeasurable
  -- Step 4: the kernel bound for each angle
  have h3 : ∀ θ, ∫⁻ ω, F ω θ ∂μ ≤ B * w θ := by
    intro θ
    rw [hF]
    simp only
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    gcongr
    calc ∫⁻ ω, ENNReal.ofReal (_root_.poissonKernel 0 (ζ ω) (circleMap 0 1 θ)) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (2 * (fullQuad t (U ω) (twistedV V v (-θ)) v).re - 1) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [hUc] with ω hω
          rw [(fullQuad_pointwise hω hV hv ht0 ht1).2 θ]
      _ ≤ B := hB (-θ)
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ ENNReal.ofReal c * ∫⁻ θ in Ioo 0 (2 * π), B * w θ := by
        gcongr with θ
        exact h3 θ
    _ = phaseConst p * B := by
        rw [lintegral_const_mul _ hwm, phaseConst, ← hc]
        ring

end Core

end BlockBand.Endpoints.PhaseFractional
