module

public import BlockBand.Endpoints.Response.PassDerivativeUpdate
public import BlockBand.Endpoints.Response.PassDerivativeRatio

/-!
# The deterministic difference-quotient bound for a port determinant ratio

Abstract pencil as in `PassDerivativeUpdate` (`M - M* = 2iηVV*`, `M` invertible, `η ≥ 0`) and a
port compression `J : p × w` with `‖J‖ ≤ 1` (the inclusion of one lead's channels). The
reflection block is `s_κ = J* 𝕊_κ J`, the reflection defect `T(κ) = I - s_κ* s_κ`
(`pencilPortDefect`), its zero-source derivative
`Ṫ = -(ṡ* s₀ + s₀* ṡ)`, `ṡ = J*(-2η 𝕊₀B)J` (`pencilPortDefectDeriv`).

* `pencilPortDefect_band`: `0 ⪯ T(κ) ⪯ I` for every `κ ≥ 0` (also for singular `M`).
* `pencilRatio_pass_bound`: for `κ ≥ 0`, `x ≥ 0`, `0 ≤ y < 1`,
  `‖F(T(κ)) - F(T(0)) - κ DF(T(0))[Ṫ]‖ ≤ κ (4c₁η Tr B · min(2, κ‖K‖) + κ(36c₁ + 576c₂)η²(Tr B)²)`.
* `pencilRatio_sq_bound`, `hasDerivWithinAt_Ici_of_sq_bound`: the error is `O(κ²)`, so
  `κ ↦ F(T(κ))` has right derivative `DF(T(0))[Ṫ]` at `0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix Filter Topology
open scoped Matrix.Norms.L2Operator ComplexConjugate

variable {ι p w : Type*} [Fintype ι] [DecidableEq ι] [Fintype p] [DecidableEq p]
  [Fintype w] [DecidableEq w]

/-- The reflection defect `I - (J*SJ)*(J*SJ)` of the compression `J*SJ`. -/
def portDefectOf (S : Matrix p p ℂ) (J : Matrix p w ℂ) : Matrix w w ℂ :=
  1 - (Jᴴ * S * J)ᴴ * (Jᴴ * S * J)

/-- `T(κ)`: reflection defect of the absorbed pencil `M + iκR*R` at the port `J`. -/
def pencilPortDefect (η : ℝ) (V : Matrix ι p ℂ) (M R : Matrix ι ι ℂ) (J : Matrix p w ℂ)
    (κ : ℝ) : Matrix w w ℂ :=
  portDefectOf (pencilScattering η V (absorbedPencil M R κ)) J

/-- The zero-source derivative `Ṫ = -(ṡ* s₀ + s₀* ṡ)`, `s₀ = J*𝕊₀J`, `ṡ = J*(-2η𝕊₀B)J`. -/
def pencilPortDefectDeriv (η : ℝ) (V : Matrix ι p ℂ) (M R : Matrix ι ι ℂ) (J : Matrix p w ℂ) :
    Matrix w w ℂ :=
  -((Jᴴ * (-(((2 * η : ℝ) : ℂ)) • (pencilScattering η V M * pencilSourceGram M R V)) * J)ᴴ *
      (Jᴴ * pencilScattering η V M * J) +
    (Jᴴ * pencilScattering η V M * J)ᴴ *
      (Jᴴ * (-(((2 * η : ℝ) : ℂ)) • (pencilScattering η V M * pencilSourceGram M R V)) * J))

omit [DecidableEq ι] in
theorem absorbedPencil_zero (M R : Matrix ι ι ℂ) : absorbedPencil M R 0 = M := by
  simp [absorbedPencil]

theorem norm_compression_le_one {S : Matrix p p ℂ} (hS : ‖S‖ ≤ 1) {J : Matrix p w ℂ}
    (hJ : ‖J‖ ≤ 1) : ‖Jᴴ * S * J‖ ≤ 1 := by
  calc ‖Jᴴ * S * J‖ ≤ ‖Jᴴ * S‖ * ‖J‖ := l2_opNorm_mul _ _
    _ ≤ (‖Jᴴ‖ * ‖S‖) * ‖J‖ := mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * 1) * 1 := by
        rw [l2_opNorm_conjTranspose]
        gcongr
    _ = 1 := by ring

omit [DecidableEq p] in
/-- A contraction has band defect: `‖s‖ ≤ 1 ⇒ 0 ⪯ I - s*s ⪯ I`. -/
theorem isUnitBand_one_sub_gram {s : Matrix w w ℂ} (hs : ‖s‖ ≤ 1) :
    IsUnitBand (1 - sᴴ * s) := by
  refine ⟨?_, fun v => ?_⟩
  · unfold IsHermitian
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose]
  · have e : (star v ⬝ᵥ ((1 - sᴴ * s) *ᵥ v)).re = vecNormSq v - vecNormSq (s *ᵥ v) := by
      rw [sub_mulVec, one_mulVec, dotProduct_sub, star_dotProduct_self,
        star_dotProduct_gram_mulVec, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re]
    rw [e]
    have h1 := vecNormSq_mulVec_le s v
    have h2 : ‖s‖ ^ 2 ≤ 1 := by
      have := norm_nonneg s
      nlinarith
    have h3 := vecNormSq_nonneg v
    have h4 := vecNormSq_nonneg (s *ᵥ v)
    constructor <;> nlinarith

/-- The absorbed scattering matrix is a contraction for every `κ ≥ 0`. -/
theorem absorbedScattering_norm_le_one {η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    {V : Matrix ι p ℂ} {M R : Matrix ι ι ℂ}
    (hW : M - Mᴴ = (((2 * η : ℝ) : ℂ) * Complex.I) • (V * Vᴴ)) :
    ‖pencilScattering η V (absorbedPencil M R κ)‖ ≤ 1 :=
  l2_opNorm_le_one_of_contraction fun v =>
    pencilScattering_contraction hη hκ (by rw [absorbedPencil_sub_conjTranspose, hW]) v

/-- `0 ⪯ T(κ) ⪯ I` for every `κ ≥ 0`. -/
theorem pencilPortDefect_band {η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    {V : Matrix ι p ℂ} {M R : Matrix ι ι ℂ}
    (hW : M - Mᴴ = (((2 * η : ℝ) : ℂ) * Complex.I) • (V * Vᴴ)) {J : Matrix p w ℂ}
    (hJ : ‖J‖ ≤ 1) : IsUnitBand (pencilPortDefect η V M R J κ) :=
  isUnitBand_one_sub_gram (norm_compression_le_one (absorbedScattering_norm_le_one hη hκ hW) hJ)

/-- **Deterministic pass bound.** For `κ ≥ 0`, `x ≥ 0`, `0 ≤ y < 1`:
`‖F(T(κ)) - F(T(0)) - κ DF(T(0))[Ṫ]‖ ≤
  κ (4c₁η Tr B · min(2, κ‖K‖) + κ(36c₁ + 576c₂)η²(Tr B)²)`. -/
theorem pencilRatio_pass_bound {η κ x y : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ) (hx : 0 ≤ x)
    (hy0 : 0 ≤ y) (hy1 : y < 1) {V : Matrix ι p ℂ} {M R : Matrix ι ι ℂ}
    (hM : IsUnit M.det) (hW : M - Mᴴ = (((2 * η : ℝ) : ℂ) * Complex.I) • (V * Vᴴ))
    {J : Matrix p w ℂ} (hJ : ‖J‖ ≤ 1) :
    ‖ratioDetC x y (pencilPortDefect η V M R J κ) - ratioDetC x y (pencilPortDefect η V M R J 0) -
        (κ : ℂ) * ratioDetDeriv x y (pencilPortDefect η V M R J 0)
          (pencilPortDefectDeriv η V M R J)‖ ≤
      κ * (4 * ratioC1 x y * η * (pencilSourceGram M R V).trace.re *
          min 2 (κ * ‖sourceKernel M R‖) +
        κ * (36 * ratioC1 x y + 576 * ratioC2 x y) * η ^ 2 *
          (pencilSourceGram M R V).trace.re ^ 2) := by
  set S₀ := pencilScattering η V M
  set Sκ := pencilScattering η V (absorbedPencil M R κ)
  set B := pencilSourceGram M R V
  set b := B.trace.re
  set m := min 2 (κ * ‖sourceKernel M R‖)
  set Sd : Matrix p p ℂ := -(((2 * η : ℝ) : ℂ)) • (S₀ * B)
  set s₀ := Jᴴ * S₀ * J
  set sκ := Jᴴ * Sκ * J
  set sd := Jᴴ * Sd * J
  set d := sκ - s₀
  set e := Jᴴ * (Sκ - S₀ + (((2 * η * κ : ℝ) : ℂ)) • (S₀ * B)) * J
  have hb : 0 ≤ b := by
    simp only [b, B, pencilSourceGram]
    rw [trace_conjTranspose_mul_self_re_eq_hsSq]; exact hsSq_nonneg _
  have hm0 : 0 ≤ m := le_min zero_le_two (mul_nonneg hκ (norm_nonneg _))
  have hm2 : m ≤ 2 := min_le_left _ _
  have hS₀ : ‖S₀‖ ≤ 1 := pencilScattering_norm_le_one hη hW
  have hSκ : ‖Sκ‖ ≤ 1 := absorbedScattering_norm_le_one hη hκ hW
  have hs₀ : ‖s₀‖ ≤ 1 := norm_compression_le_one hS₀ hJ
  have hsκ : ‖sκ‖ ≤ 1 := norm_compression_le_one hSκ hJ
  have hJH : ‖Jᴴ‖ ≤ 1 := by rw [l2_opNorm_conjTranspose]; exact hJ
  have hJJ : ‖Jᴴ‖ * ‖J‖ ≤ 1 := by
    have := norm_nonneg J
    nlinarith [norm_nonneg Jᴴ]
  -- trace-norm bounds
  have tE := signedSource_error_mul (R := R) hη hκ hM hW
  have te : TraceBound e (2 * η * κ * b * m) := by
    have := tE.mul_mul Jᴴ J
    refine this.mono ?_
    have h0 : 0 ≤ 2 * η * κ * b * m := by positivity
    nlinarith
  have tB : TraceBound (S₀ * B) b := by
    have hg := traceBound_gram (sourceFrame M R V) (1 : Matrix ι ι ℂ)
    rw [Matrix.mul_one] at hg
    have h1 := (hg.mono (mul_le_of_le_one_left hb l2_opNorm_one_le)).mul_left S₀
    exact h1.mono (mul_le_of_le_one_left hb hS₀)
  have tsd : TraceBound sd (2 * η * b) := by
    have h1 := (tB.smul (-(((2 * η : ℝ) : ℂ)))).mul_mul Jᴴ J
    refine h1.mono ?_
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h0 : 0 ≤ 2 * η * b := by positivity
    nlinarith
  have hde : d = e + (κ : ℂ) • sd := by
    simp only [d, e, sκ, s₀, sd, Sd]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul]
    have : (κ : ℂ) * -(((2 * η : ℝ) : ℂ)) = -(((2 * η * κ : ℝ) : ℂ)) := by push_cast; ring
    rw [this, neg_smul]
    abel
  have td : TraceBound d (6 * η * κ * b) := by
    rw [hde]
    have h1 := te.add (tsd.smul (κ : ℂ))
    refine h1.mono ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ]
    have : 2 * η * κ * b * m ≤ 2 * η * κ * b * 2 :=
      mul_le_mul_of_nonneg_left hm2 (by positivity)
    nlinarith
  have hdn : ‖d‖ ≤ 2 := by
    calc ‖d‖ ≤ ‖sκ‖ + ‖s₀‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hsκ hs₀
      _ = 2 := by norm_num
  -- the defect difference
  set T0 := pencilPortDefect η V M R J 0
  set Tκ := pencilPortDefect η V M R J κ
  set Td := pencilPortDefectDeriv η V M R J
  have hT0 : T0 = 1 - s₀ᴴ * s₀ := by
    simp only [T0, pencilPortDefect, portDefectOf, absorbedPencil_zero, s₀, S₀]
  have hTκ : Tκ = 1 - sκᴴ * sκ := rfl
  have hTd : Td = -(sdᴴ * s₀ + s₀ᴴ * sd) := rfl
  have hsκ' : sκ = s₀ + d := by simp only [d]; abel
  have hH : Tκ - T0 = -(dᴴ * s₀ + s₀ᴴ * d + dᴴ * d) := by
    rw [hTκ, hT0, hsκ', conjTranspose_add]
    simp only [Matrix.add_mul, Matrix.mul_add]
    abel
  have hHd : Tκ - T0 - (κ : ℂ) • Td = -(eᴴ * s₀ + s₀ᴴ * e + dᴴ * d) := by
    have hdH : dᴴ = eᴴ + (κ : ℂ) • sdᴴ := by
      rw [hde, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
    have hlin : dᴴ * s₀ + s₀ᴴ * d =
        eᴴ * s₀ + s₀ᴴ * e + (κ : ℂ) • (sdᴴ * s₀ + s₀ᴴ * sd) := by
      rw [hdH, hde]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add]
      abel
    rw [hH, hTd, hlin, smul_neg]
    abel
  have tH : TraceBound (Tκ - T0) (24 * η * κ * b) := by
    rw [hH]
    have h1 := td.conjTranspose.mul_right s₀
    have h2 := td.mul_left s₀ᴴ
    have h3 := td.mul_left dᴴ
    have := ((h1.add h2).add h3).neg
    refine this.mono ?_
    rw [l2_opNorm_conjTranspose, l2_opNorm_conjTranspose]
    have h0 : 0 ≤ 6 * η * κ * b := by positivity
    nlinarith
  have tHd : TraceBound (Tκ - T0 - (κ : ℂ) • Td)
      (2 * (2 * η * κ * b * m) + (6 * η * κ * b) ^ 2) := by
    rw [hHd]
    have h1 := te.conjTranspose.mul_right s₀
    have h2 := te.mul_left s₀ᴴ
    have h3 := td.mul_left dᴴ
    have := ((h1.add h2).add h3).neg
    refine this.mono ?_
    rw [l2_opNorm_conjTranspose, l2_opNorm_conjTranspose]
    have hdn' : ‖d‖ ≤ 6 * η * κ * b := td.norm_le
    have h0 : 0 ≤ 2 * η * κ * b * m := by positivity
    have h0' : 0 ≤ 6 * η * κ * b := by positivity
    have : ‖d‖ * (6 * η * κ * b) ≤ (6 * η * κ * b) ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hdn' h0'
    nlinarith
  -- combine
  have hb0 : IsUnitBand T0 := by
    have := pencilPortDefect_band (R := R) hη le_rfl hW hJ
    simpa [T0] using this
  have hbκ : IsUnitBand Tκ := pencilPortDefect_band hη hκ hW hJ
  have h2nd := ratioDetC_second_order hx hy0 hy1 hb0 hbκ tH
  have h1st := norm_ratioDetDeriv_le hx hy0 hy1 hb0 tHd
  have hsplit : ratioDetC x y Tκ - ratioDetC x y T0 - (κ : ℂ) * ratioDetDeriv x y T0 Td =
      (ratioDetC x y Tκ - ratioDetC x y T0 - ratioDetDeriv x y T0 (Tκ - T0)) +
        ratioDetDeriv x y T0 (Tκ - T0 - (κ : ℂ) • Td) := by
    rw [ratioDetDeriv_sub x y T0 (Tκ - T0) ((κ : ℂ) • Td), ratioDetDeriv_smul]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hc1 := ratioC1_nonneg hx hy0 hy1
  have hc2 := ratioC2_nonneg x y
  calc _ ≤ ratioC2 x y * (24 * η * κ * b) ^ 2 +
        ratioC1 x y * (2 * (2 * η * κ * b * m) + (6 * η * κ * b) ^ 2) := add_le_add h2nd h1st
    _ = _ := by ring

/-- A difference quotient with a quadratic error bound has the right derivative. -/
theorem hasDerivWithinAt_Ici_of_sq_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} {g' : E} {C : ℝ}
    (h : ∀ κ : ℝ, 0 ≤ κ → ‖g κ - g 0 - κ • g'‖ ≤ C * κ ^ 2) :
    HasDerivWithinAt g g' (Set.Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hC1 : 0 < |C| + 1 := by positivity
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < c / (|C| + 1) by positivity))]
    with κ hκ0 hκ1
  simp only [Set.mem_Ici] at hκ0
  simp only [Set.mem_Iio] at hκ1
  simp only [sub_zero, Real.norm_eq_abs, abs_of_nonneg hκ0]
  calc ‖g κ - g 0 - κ • g'‖ ≤ C * κ ^ 2 := h κ hκ0
    _ ≤ (|C| + 1) * κ * κ := by
        rw [sq, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          ((le_abs_self C).trans (by linarith)) hκ0) hκ0
    _ ≤ c * κ := by
        have : (|C| + 1) * κ ≤ c := by
          rw [lt_div_iff₀ hC1] at hκ1; linarith
        exact mul_le_mul_of_nonneg_right this hκ0

/-- Pointwise right-derivative bound in the form used for `κ ↦ F(T(κ))`:
`‖F(T(κ)) - F(T(0)) - κ DF‖ ≤ C_ω κ²` with `C_ω = 4c₁η Tr B ‖K‖ + (36c₁ + 576c₂)η²(Tr B)²`. -/
theorem pencilRatio_sq_bound {η x y : ℝ} (hη : 0 ≤ η) (hx : 0 ≤ x)
    (hy0 : 0 ≤ y) (hy1 : y < 1) {V : Matrix ι p ℂ} {M R : Matrix ι ι ℂ}
    (hM : IsUnit M.det) (hW : M - Mᴴ = (((2 * η : ℝ) : ℂ) * Complex.I) • (V * Vᴴ))
    {J : Matrix p w ℂ} (hJ : ‖J‖ ≤ 1) (κ : ℝ) (hκ : 0 ≤ κ) :
    ‖ratioDetC x y (pencilPortDefect η V M R J κ) - ratioDetC x y (pencilPortDefect η V M R J 0) -
        (κ : ℂ) * ratioDetDeriv x y (pencilPortDefect η V M R J 0)
          (pencilPortDefectDeriv η V M R J)‖ ≤
      (4 * ratioC1 x y * η * (pencilSourceGram M R V).trace.re * ‖sourceKernel M R‖ +
        (36 * ratioC1 x y + 576 * ratioC2 x y) * η ^ 2 * (pencilSourceGram M R V).trace.re ^ 2) *
        κ ^ 2 := by
  refine (pencilRatio_pass_bound hη hκ hx hy0 hy1 hM hW hJ).trans (le_of_eq_of_le rfl ?_)
  have hb : 0 ≤ (pencilSourceGram M R V).trace.re := by
    simp only [pencilSourceGram]; rw [trace_conjTranspose_mul_self_re_eq_hsSq]; exact hsSq_nonneg _
  have hc1 := ratioC1_nonneg hx hy0 hy1
  have hm : min 2 (κ * ‖sourceKernel M R‖) ≤ κ * ‖sourceKernel M R‖ := min_le_right _ _
  have h0 : 0 ≤ 4 * ratioC1 x y * η * (pencilSourceGram M R V).trace.re := by positivity
  have := mul_le_mul_of_nonneg_left hm h0
  nlinarith

/-- The zero-source defect derivative is trace-norm bounded: `‖Ṫ‖₁ ≤ 4η Tr B`. -/
theorem pencilPortDefectDeriv_traceBound {η : ℝ} (hη : 0 ≤ η) {V : Matrix ι p ℂ}
    {M R : Matrix ι ι ℂ} (hW : M - Mᴴ = (((2 * η : ℝ) : ℂ) * Complex.I) • (V * Vᴴ))
    {J : Matrix p w ℂ} (hJ : ‖J‖ ≤ 1) :
    TraceBound (pencilPortDefectDeriv η V M R J) (4 * η * (pencilSourceGram M R V).trace.re) := by
  set S₀ := pencilScattering η V M
  set b := (pencilSourceGram M R V).trace.re
  have hb : 0 ≤ b := by
    simp only [b, pencilSourceGram]
    rw [trace_conjTranspose_mul_self_re_eq_hsSq]; exact hsSq_nonneg _
  have hS₀ : ‖S₀‖ ≤ 1 := pencilScattering_norm_le_one hη hW
  have hs₀ : ‖Jᴴ * S₀ * J‖ ≤ 1 := norm_compression_le_one hS₀ hJ
  have hJJ : ‖Jᴴ‖ * ‖J‖ ≤ 1 := by
    rw [l2_opNorm_conjTranspose]
    have := norm_nonneg J
    nlinarith
  have tB : TraceBound (S₀ * pencilSourceGram M R V) b := by
    have hg := traceBound_gram (sourceFrame M R V) (1 : Matrix ι ι ℂ)
    rw [Matrix.mul_one] at hg
    have h1 := (hg.mono (mul_le_of_le_one_left hb l2_opNorm_one_le)).mul_left S₀
    exact h1.mono (mul_le_of_le_one_left hb hS₀)
  have tsd : TraceBound (Jᴴ * (-(((2 * η : ℝ) : ℂ)) • (S₀ * pencilSourceGram M R V)) * J)
      (2 * η * b) := by
    have h1 := (tB.smul (-(((2 * η : ℝ) : ℂ)))).mul_mul Jᴴ J
    refine h1.mono ?_
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h0 : 0 ≤ 2 * η * b := by positivity
    nlinarith
  have h1 := tsd.conjTranspose.mul_right (Jᴴ * S₀ * J)
  have h2 := tsd.mul_left (Jᴴ * S₀ * J)ᴴ
  have := (h1.add h2).neg
  refine this.mono ?_
  rw [l2_opNorm_conjTranspose]
  have h0 : 0 ≤ 2 * η * b := by positivity
  nlinarith

end BlockBand.Endpoints
