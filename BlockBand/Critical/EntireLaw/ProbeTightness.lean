module

public import BlockBand.Critical.EntireLaw.PhaseBounds
public import BlockBand.Critical.EntireLaw.PhasePassage

/-!
# The entire law: one-probe tightness controls `Tr A` and `‖A‖_HS`

Setting: a probability space `(Ω, μ)`, a measurable random matrix `A : Ω → Matrix ι ι ℂ`,
Hermitian `μ`-a.s., and `X = g^* A g` under `μ ⊗ circularVectorLaw ι` (one independent standard
circular Gaussian probe). With `S_X = P(‖X‖ > M)`, `M ≥ 0`:

* `norm_one_sub_integral_probeExp_le`: `‖1 - E e^{-itX}‖ ≤ 2 S_X + |t| M`;
* `measureReal_hsSq_gt_le`: `P(‖A‖²_HS > K²) ≤ 4 (2 S_X + M/K)`;
* `measureReal_trace_gt_le`: `P(|Re Tr A| > L) ≤ 2 (2 S_X + 2M/L + 2 P(‖A‖²_HS > K²) + 4K²/L²)`
  for `4K² ≤ L²` (Mathlib's `measureReal_abs_gt_le_integral_charFun` for the law of `Re Tr A`);
* `probe_hsSq_tail`, `probe_trace_tail`: the same with explicit levels `probeLevelK η M`,
  `probeLevelL η M` depending only on `(η, M)` (uniformity along any family).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory ProbabilityTheory Matrix Filter Set
open BlockBand.Internal.Contracts.CoareaPalm

section Probe

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The one-probe quadratic form `g^* A g`. -/
def probeForm (A : Matrix ι ι ℂ) (g : ι → ℂ) : ℂ := star g ⬝ᵥ (A *ᵥ g)

omit [DecidableEq ι] in
theorem continuous_probeForm :
    Continuous fun x : Matrix ι ι ℂ × (ι → ℂ) => probeForm x.1 x.2 := by
  unfold probeForm
  fun_prop

/-- The one-probe phase `exp(-i t g^* A g)`. -/
def probeExp (t : ℝ) (A : Matrix ι ι ℂ) (g : ι → ℂ) : ℂ :=
  Complex.exp (-(Complex.I * t) * probeForm A g)

omit [DecidableEq ι] in
theorem norm_probeExp {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ) (g : ι → ℂ) :
    ‖probeExp t A g‖ = 1 := by
  have h := im_star_dotProduct_mulVec_self hA g
  rw [probeExp, Complex.norm_exp]
  simp [probeForm, Complex.mul_re, h]

omit [DecidableEq ι] in
/-- `‖1 - e^{-itX}‖ ≤ |t| ‖X‖` and `≤ 2` for the real quadratic form of a Hermitian matrix. -/
theorem norm_one_sub_probeExp_le {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ) (g : ι → ℂ) :
    ‖1 - probeExp t A g‖ ≤ |t| * ‖probeForm A g‖ ∧ ‖1 - probeExp t A g‖ ≤ 2 := by
  refine ⟨?_, ?_⟩
  · have h : (probeForm A g).im = 0 := im_star_dotProduct_mulVec_self hA g
    have hX : probeForm A g = (((probeForm A g).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simpa using h)
    have heq : -(Complex.I * t) * probeForm A g =
        Complex.I * ((-(t * (probeForm A g).re) : ℝ) : ℂ) := by
      conv_lhs => rw [hX]
      push_cast; ring
    rw [probeExp, heq, norm_sub_rev]
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_neg, abs_mul]
    conv_rhs => rw [hX]
    rw [Complex.norm_real, Real.norm_eq_abs]
  · refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_probeExp hA]
    norm_num

/-- The Gaussian average over the probe, `E_g exp(-i t g^* A g)`. -/
def probePhase (A : Matrix ι ι ℂ) (t : ℝ) : ℂ :=
  ∫ g, probeExp t A g ∂circularVectorLaw ι

theorem probePhase_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ) :
    probePhase A t = hermitianPhase hA t :=
  integral_circularVectorLaw_hermitian_phase hA t

variable (μ : Measure Ω) [IsProbabilityMeasure μ] {A : Ω → Matrix ι ι ℂ}

omit [DecidableEq ι] in
theorem measurable_probeForm_comp (hAm : Measurable A) :
    Measurable fun x : Ω × (ι → ℂ) => probeForm (A x.1) x.2 :=
  continuous_probeForm.measurable.comp ((hAm.comp measurable_fst).prodMk measurable_snd)

omit [DecidableEq ι] in
theorem measurable_probeExp_comp (hAm : Measurable A) (t : ℝ) :
    Measurable fun x : Ω × (ι → ℂ) => probeExp t (A x.1) x.2 :=
  Complex.measurable_exp.comp (measurable_const.mul (measurable_probeForm_comp hAm))

omit [DecidableEq ι] [IsProbabilityMeasure μ] in
theorem ae_isHermitian_prod (hAh : ∀ᵐ ω ∂μ, (A ω).IsHermitian) :
    ∀ᵐ x ∂μ.prod (circularVectorLaw ι), (A x.1).IsHermitian :=
  Measure.quasiMeasurePreserving_fst.ae hAh

omit [DecidableEq ι] in
theorem integrable_probeExp (hAm : Measurable A) (hAh : ∀ᵐ ω ∂μ, (A ω).IsHermitian) (t : ℝ) :
    Integrable (fun x : Ω × (ι → ℂ) => probeExp t (A x.1) x.2) (μ.prod (circularVectorLaw ι)) := by
  refine Integrable.of_bound (measurable_probeExp_comp hAm t).aestronglyMeasurable 1 ?_
  filter_upwards [ae_isHermitian_prod μ hAh] with x hx
  exact (norm_probeExp hx t x.2).le

omit [DecidableEq ι] in
theorem stronglyMeasurable_probePhase (hAm : Measurable A) (t : ℝ) :
    StronglyMeasurable fun ω => probePhase (A ω) t :=
  (measurable_probeExp_comp hAm t).stronglyMeasurable.integral_prod_right'
    (f := fun x : Ω × (ι → ℂ) => probeExp t (A x.1) x.2)

omit [IsProbabilityMeasure μ] in
theorem norm_probePhase_le {B : Matrix ι ι ℂ} (hB : B.IsHermitian) (t : ℝ) :
    ‖probePhase B t‖ ≤ 1 := by
  rw [probePhase_eq hB]
  exact norm_hermitianPhase_le_one hB t

omit [DecidableEq ι] in
theorem continuous_hsSq : Continuous (hsSq : Matrix ι ι ℂ → ℝ) := by
  unfold hsSq
  fun_prop

omit [DecidableEq ι] in
/-- The trace of a Hermitian matrix is real. -/
theorem trace_eq_ofReal_re {B : Matrix ι ι ℂ} (hB : B.IsHermitian) :
    B.trace = ((B.trace.re : ℝ) : ℂ) := by
  classical
  rw [hB.trace_eq_sum_eigenvalues]
  apply Complex.ext <;> simp

omit [DecidableEq ι] in
/-- **Fubini for the one-probe phase**: `E_{(ω,g)} e^{-itX} = E_ω E_g e^{-itX}`. -/
theorem integral_probeExp_prod (hAm : Measurable A) (hAh : ∀ᵐ ω ∂μ, (A ω).IsHermitian) (t : ℝ) :
    ∫ x, probeExp t (A x.1) x.2 ∂μ.prod (circularVectorLaw ι) =
      ∫ ω, probePhase (A ω) t ∂μ :=
  integral_prod _ (integrable_probeExp μ hAm hAh t)

omit [DecidableEq ι] in
/-- **Tightness of the probe ⇒ the characteristic function is close to one**:
`‖1 - E e^{-itX}‖ ≤ 2 P(‖X‖ > M) + |t| M`. -/
theorem norm_one_sub_integral_probeExp_le (hAm : Measurable A)
    (hAh : ∀ᵐ ω ∂μ, (A ω).IsHermitian) (t : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    ‖1 - ∫ x, probeExp t (A x.1) x.2 ∂μ.prod (circularVectorLaw ι)‖ ≤
      2 * (μ.prod (circularVectorLaw ι)).real {x | M < ‖probeForm (A x.1) x.2‖} + |t| * M := by
  set S := {x : Ω × (ι → ℂ) | M < ‖probeForm (A x.1) x.2‖}
  have hS : MeasurableSet S :=
    measurableSet_lt measurable_const (measurable_probeForm_comp hAm).norm
  have hint := integrable_probeExp μ hAm hAh t
  have h1 : 1 - ∫ x, probeExp t (A x.1) x.2 ∂μ.prod (circularVectorLaw ι) =
      ∫ x, (1 - probeExp t (A x.1) x.2) ∂μ.prod (circularVectorLaw ι) := by
    rw [integral_sub (integrable_const 1) hint]
    simp
  rw [h1]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hbound : ∀ᵐ x ∂μ.prod (circularVectorLaw ι), ‖1 - probeExp t (A x.1) x.2‖ ≤
      S.indicator (fun _ => (2 : ℝ)) x + |t| * M := by
    filter_upwards [ae_isHermitian_prod μ hAh] with x hx
    obtain ⟨h1, h2⟩ := norm_one_sub_probeExp_le hx t x.2
    by_cases hxS : x ∈ S
    · simp only [Set.indicator_of_mem hxS]
      have := mul_nonneg (abs_nonneg t) hM
      linarith
    · rw [Set.indicator_of_notMem hxS, zero_add]
      have : ‖probeForm (A x.1) x.2‖ ≤ M := not_lt.mp hxS
      exact h1.trans (mul_le_mul_of_nonneg_left this (abs_nonneg t))
  have hint2 : Integrable (fun x => S.indicator (fun _ => (2 : ℝ)) x + |t| * M)
      (μ.prod (circularVectorLaw ι)) :=
    ((integrable_const 2).indicator hS).add (integrable_const _)
  refine (integral_mono_ae ((integrable_const 1).sub hint).norm hint2 hbound).trans (le_of_eq ?_)
  rw [integral_add ((integrable_const 2).indicator hS) (integrable_const _),
    integral_indicator_const _ hS, integral_const]
  simp only [smul_eq_mul, probReal_univ, one_mul]
  ring

theorem integrable_probePhase (hAm : Measurable A) (hAh : ∀ᵐ ω ∂μ, (A ω).IsHermitian) (t : ℝ) :
    Integrable (fun ω => probePhase (A ω) t) μ :=
  Integrable.of_bound (stronglyMeasurable_probePhase hAm t).aestronglyMeasurable 1
    (by filter_upwards [hAh] with ω hω; exact norm_probePhase_le hω t)

/-- **Hilbert–Schmidt tail from one-probe tightness** (characteristic-function form of the
converse probe-tightness bound): `P(‖A‖²_HS > K²) ≤ 4 (2 P(‖X‖ > M) + M/K)`, `X = g^*Ag`. -/
theorem measureReal_hsSq_gt_le (hAm : Measurable A) (hAh : ∀ᵐ ω ∂μ, (A ω).IsHermitian)
    {K M : ℝ} (hK : 0 < K) (hM : 0 ≤ M) :
    μ.real {ω | K ^ 2 < hsSq (A ω)} ≤
      4 * (2 * (μ.prod (circularVectorLaw ι)).real {x | M < ‖probeForm (A x.1) x.2‖} +
        M / K) := by
  set t : ℝ := K⁻¹
  set Sh := {ω | K ^ 2 < hsSq (A ω)}
  have hShm : MeasurableSet Sh :=
    measurableSet_lt measurable_const (continuous_hsSq.measurable.comp hAm)
  have hφi := integrable_probePhase μ hAm hAh t
  have hre : Integrable (fun ω => (1 - probePhase (A ω) t).re) μ :=
    ((integrable_const 1).sub hφi).re
  have hkey : 4⁻¹ * μ.real Sh ≤ (1 - ∫ ω, probePhase (A ω) t ∂μ).re := by
    have h1 : 1 - ∫ ω, probePhase (A ω) t ∂μ = ∫ ω, (1 - probePhase (A ω) t) ∂μ := by
      rw [integral_sub (integrable_const 1) hφi]
      simp
    have hI : Integrable (fun ω => 1 - probePhase (A ω) t) μ := (integrable_const 1).sub hφi
    have h2 := integral_re hI
    simp only [RCLike.re_to_complex] at h2
    rw [h1, ← h2]
    calc 4⁻¹ * μ.real Sh = ∫ ω, Sh.indicator (fun _ => (4⁻¹ : ℝ)) ω ∂μ := by
          rw [integral_indicator_const _ hShm, smul_eq_mul, mul_comm]
      _ ≤ ∫ ω, (1 - probePhase (A ω) t).re ∂μ := by
          refine integral_mono_ae ((integrable_const _).indicator hShm) hre ?_
          filter_upwards [hAh] with ω hω
          rw [probePhase_eq hω]
          have hn := normSq_hermitianPhase_mul_le hω t
          have hle1 := norm_hermitianPhase_le_one hω t
          have hrel := Complex.re_le_norm (hermitianPhase hω t)
          simp only [Complex.sub_re, Complex.one_re]
          by_cases hωS : ω ∈ Sh
          · rw [Set.indicator_of_mem hωS]
            have hgt : 1 < t ^ 2 * hsSq (A ω) := by
              have hK2 : 0 < K ^ 2 := by positivity
              have : t ^ 2 * hsSq (A ω) = hsSq (A ω) / K ^ 2 := by
                simp only [t, inv_pow]; ring
              rw [this, one_lt_div hK2]
              exact hωS
            have hn2 : ‖hermitianPhase hω t‖ ^ 2 * 2 ≤ 1 := by
              have : ‖hermitianPhase hω t‖ ^ 2 * 2 ≤
                  ‖hermitianPhase hω t‖ ^ 2 * (1 + t ^ 2 * hsSq (A ω)) :=
                mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
              linarith
            nlinarith [norm_nonneg (hermitianPhase hω t)]
          · rw [Set.indicator_of_notMem hωS]
            linarith
  have hfub := integral_probeExp_prod μ hAm hAh t
  have hb := norm_one_sub_integral_probeExp_le μ hAm hAh t (M := M) hM
  rw [hfub] at hb
  have hre_le := Complex.re_le_norm (1 - ∫ ω, probePhase (A ω) t ∂μ)
  have htM : |t| * M = M / K := by
    simp only [t, abs_inv, abs_of_pos hK]; ring
  rw [htM] at hb
  linarith

/-- **Trace tail from one-probe tightness** (characteristic-function form): with
`T = Re Tr A`, `P(|T| > L) ≤ 2 (2 P(‖X‖ > M) + 2M/L + 2 P(‖A‖²_HS > K²) + 4K²/L²)` whenever
`4K² ≤ L²`, `M ≥ 0`. Uses the small-source expansion `E_g e^{-itX} ≈ e^{-it Tr A}` and Mathlib's
tail bound `measureReal_abs_gt_le_integral_charFun`. -/
theorem measureReal_trace_gt_le (hAm : Measurable A) (hAh : ∀ᵐ ω ∂μ, (A ω).IsHermitian)
    {K L M : ℝ} (hL : 0 < L) (hKL : 4 * K ^ 2 ≤ L ^ 2) (hM : 0 ≤ M) :
    μ.real {ω | L < |(A ω).trace.re|} ≤
      2 * (2 * (μ.prod (circularVectorLaw ι)).real {x | M < ‖probeForm (A x.1) x.2‖} +
        2 * M / L + 2 * μ.real {ω | K ^ 2 < hsSq (A ω)} + 4 * K ^ 2 / L ^ 2) := by
  set SX := (μ.prod (circularVectorLaw ι)).real {x | M < ‖probeForm (A x.1) x.2‖}
  set Sh := {ω | K ^ 2 < hsSq (A ω)}
  have hShm : MeasurableSet Sh :=
    measurableSet_lt measurable_const (continuous_hsSq.measurable.comp hAm)
  set T : Ω → ℝ := fun ω => (A ω).trace.re
  have hT : Measurable T :=
    (Complex.continuous_re.comp continuous_id.matrix_trace).measurable.comp hAm
  set ρ := μ.map T
  have : IsProbabilityMeasure ρ := inferInstance
  set C := 2 * SX + 2 * M / L + 2 * μ.real Sh + 4 * K ^ 2 / L ^ 2
  have hC : ∀ t : ℝ, |t| ≤ 2 * L⁻¹ → ‖1 - charFun ρ t‖ ≤ C := by
    intro t ht
    have ht2 : t ^ 2 ≤ 4 / L ^ 2 := by
      have h0 : 0 ≤ |t| := abs_nonneg t
      have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      rw [this]
      calc |t| ^ 2 ≤ (2 * L⁻¹) ^ 2 := pow_le_pow_left₀ h0 ht 2
        _ = 4 / L ^ 2 := by field_simp; norm_num
    have hcont : Continuous fun x : ℝ => Complex.exp (t * x * Complex.I) := by fun_prop
    have hchar : charFun ρ t = ∫ ω, Complex.exp (t * T ω * Complex.I) ∂μ := by
      rw [charFun_apply_real, integral_map hT.aemeasurable hcont.aestronglyMeasurable]
    have hφi := integrable_probePhase μ hAm hAh (-t)
    have hei : Integrable (fun ω => Complex.exp (t * T ω * Complex.I)) μ :=
      Integrable.of_bound (hcont.measurable.comp hT).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => by
          rw [Complex.norm_exp]
          simp)
    have hsplit : 1 - charFun ρ t = (1 - ∫ ω, probePhase (A ω) (-t) ∂μ) +
        ∫ ω, (probePhase (A ω) (-t) - Complex.exp (t * T ω * Complex.I)) ∂μ := by
      rw [hchar, integral_sub hφi hei]
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have hA1 : ‖1 - ∫ ω, probePhase (A ω) (-t) ∂μ‖ ≤ 2 * SX + 2 * M / L := by
      rw [← integral_probeExp_prod μ hAm hAh]
      refine (norm_one_sub_integral_probeExp_le μ hAm hAh (-t) (M := M) hM).trans ?_
      rw [abs_neg]
      have : |t| * M ≤ 2 * L⁻¹ * M := mul_le_mul_of_nonneg_right ht hM
      have h2 : 2 * L⁻¹ * M = 2 * M / L := by ring
      linarith
    have hA2 : ‖∫ ω, (probePhase (A ω) (-t) - Complex.exp (t * T ω * Complex.I)) ∂μ‖ ≤
        2 * μ.real Sh + 4 * K ^ 2 / L ^ 2 := by
      refine (norm_integral_le_integral_norm _).trans ?_
      have hbound : ∀ᵐ ω ∂μ, ‖probePhase (A ω) (-t) - Complex.exp (t * T ω * Complex.I)‖ ≤
          Sh.indicator (fun _ => (2 : ℝ)) ω + 4 * K ^ 2 / L ^ 2 := by
        filter_upwards [hAh] with ω hω
        have hK2 : 0 ≤ 4 * K ^ 2 / L ^ 2 := by positivity
        rw [probePhase_eq hω]
        have hexp : Complex.exp (t * T ω * Complex.I) =
            Complex.exp (-(Complex.I * (((-t : ℝ) : ℂ) * (A ω).trace))) := by
          rw [trace_eq_ofReal_re hω]
          congr 1
          push_cast
          ring
        rw [hexp]
        by_cases hωS : ω ∈ Sh
        · rw [Set.indicator_of_mem hωS]
          have hn1 := norm_hermitianPhase_le_one hω (-t)
          have hn2 : ‖Complex.exp (-(Complex.I * (((-t : ℝ) : ℂ) * (A ω).trace)))‖ = 1 := by
            rw [← hexp, Complex.norm_exp]
            simp
          have := norm_sub_le (hermitianPhase hω (-t))
            (Complex.exp (-(Complex.I * (((-t : ℝ) : ℂ) * (A ω).trace))))
          linarith
        · rw [Set.indicator_of_notMem hωS, zero_add]
          have hhs : hsSq (A ω) ≤ K ^ 2 := not_lt.mp hωS
          have hle : (-t) ^ 2 * hsSq (A ω) ≤ 4 * K ^ 2 / L ^ 2 := by
            rw [neg_sq]
            calc t ^ 2 * hsSq (A ω) ≤ (4 / L ^ 2) * K ^ 2 :=
                  mul_le_mul ht2 hhs (hsSq_nonneg _) (by positivity)
              _ = 4 * K ^ 2 / L ^ 2 := by ring
          have hle1 : (-t) ^ 2 * hsSq (A ω) ≤ 1 := by
            refine hle.trans ?_
            rw [div_le_one (by positivity)]
            exact hKL
          exact (norm_hermitianPhase_sub_exp_trace_le hω hle1).trans hle
      have hint2 : Integrable (fun ω => Sh.indicator (fun _ => (2 : ℝ)) ω + 4 * K ^ 2 / L ^ 2) μ :=
        ((integrable_const 2).indicator hShm).add (integrable_const _)
      refine (integral_mono_ae (hφi.sub hei).norm hint2 hbound).trans (le_of_eq ?_)
      rw [integral_add ((integrable_const 2).indicator hShm) (integrable_const _),
        integral_indicator_const _ hShm, integral_const]
      simp only [smul_eq_mul, probReal_univ, one_mul]
      ring
    simp only [C]
    linarith
  have hmain := measureReal_abs_gt_le_integral_charFun (μ := ρ) hL
  have hle : -2 * L⁻¹ ≤ 2 * L⁻¹ := by
    have : 0 ≤ L⁻¹ := inv_nonneg.mpr hL.le
    linarith
  have hint_bound : ‖∫ t in (-2 * L⁻¹)..(2 * L⁻¹), 1 - charFun ρ t‖ ≤
      C * |2 * L⁻¹ - -2 * L⁻¹| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => hC t ?_
    rw [Set.uIoc_of_le hle] at ht
    exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have habs : |2 * L⁻¹ - -2 * L⁻¹| = 4 * L⁻¹ := by
    rw [abs_of_nonneg (by linarith)]
    ring
  rw [habs] at hint_bound
  have hset : ρ.real {x | L < |x|} = μ.real {ω | L < |(A ω).trace.re|} :=
    map_measureReal_apply hT (measurableSet_lt measurable_const continuous_abs.measurable)
  rw [hset] at hmain
  refine hmain.trans ((mul_le_mul_of_nonneg_left hint_bound (by positivity)).trans
    (le_of_eq ?_))
  field_simp
  ring

/-- The Hilbert–Schmidt level `K(η, M) = 8M/η + 1`. -/
def probeLevelK (η M : ℝ) : ℝ := 8 * M / η + 1

/-- The trace level `L(η, M) = 32M/η + 8K' + 8K'/η + 1`, `K' = K(η/8, M)`. -/
def probeLevelL (η M : ℝ) : ℝ :=
  32 * M / η + 8 * probeLevelK (η / 8) M + 8 * probeLevelK (η / 8) M / η + 1

theorem probeLevelK_pos {η M : ℝ} (hη : 0 < η) (hM : 0 ≤ M) : 0 < probeLevelK η M := by
  unfold probeLevelK; positivity

/-- **Uniform Hilbert–Schmidt tail**: if `P(‖X‖ > M) ≤ η/64` then
`P(‖A‖²_HS > K(η,M)²) ≤ η`; the level depends only on `η` and `M`. -/
theorem probe_hsSq_tail (hAm : Measurable A) (hAh : ∀ᵐ ω ∂μ, (A ω).IsHermitian) {η M : ℝ}
    (hη : 0 < η) (hM : 0 ≤ M)
    (hX : (μ.prod (circularVectorLaw ι)).real {x | M < ‖probeForm (A x.1) x.2‖} ≤ η / 64) :
    μ.real {ω | probeLevelK η M ^ 2 < hsSq (A ω)} ≤ η := by
  have hK := probeLevelK_pos hη hM
  refine (measureReal_hsSq_gt_le μ hAm hAh hK hM).trans ?_
  have h1 : M / probeLevelK η M ≤ η / 8 := by
    rw [div_le_iff₀ hK]
    unfold probeLevelK
    have : η / 8 * (8 * M / η + 1) = M + η / 8 := by field_simp
    rw [this]
    linarith
  linarith

/-- **Uniform trace tail**: if `P(‖X‖ > M) ≤ η/512` then `P(|Re Tr A| > L(η,M)) ≤ η`. -/
theorem probe_trace_tail (hAm : Measurable A) (hAh : ∀ᵐ ω ∂μ, (A ω).IsHermitian) {η M : ℝ}
    (hη : 0 < η) (hM : 0 ≤ M)
    (hX : (μ.prod (circularVectorLaw ι)).real {x | M < ‖probeForm (A x.1) x.2‖} ≤ η / 512) :
    μ.real {ω | probeLevelL η M < |(A ω).trace.re|} ≤ η := by
  set K := probeLevelK (η / 8) M
  set L := probeLevelL η M
  have hK : 0 < K := probeLevelK_pos (by positivity) hM
  have hLdef : L = 32 * M / η + 8 * K + 8 * K / η + 1 := rfl
  have hL : 0 < L := by rw [hLdef]; positivity
  have hL1 : 32 * M / η ≤ L := by
    rw [hLdef]; have : 0 ≤ 8 * K / η := by positivity
    linarith
  have hL2 : 8 * K ≤ L := by
    rw [hLdef]; have : 0 ≤ 32 * M / η := by positivity
    have : 0 ≤ 8 * K / η := by positivity
    linarith
  have hL3 : 8 * K / η ≤ L := by
    rw [hLdef]; have : 0 ≤ 32 * M / η := by positivity
    linarith
  have hKL : 4 * K ^ 2 ≤ L ^ 2 := by nlinarith
  have hhs := probe_hsSq_tail μ hAm hAh (η := η / 8) (M := M) (by positivity) hM
    (by have : η / 8 / 64 = η / 512 := by ring
        rw [this]; exact hX)
  have htr := measureReal_trace_gt_le μ hAm hAh hL hKL hM
  have hML : M / L ≤ η / 32 := by
    rw [div_le_iff₀ hL]
    calc M = η / 32 * (32 * M / η) := by field_simp
      _ ≤ η / 32 * L := by gcongr
  have hKL2 : K ^ 2 / L ^ 2 ≤ η / 64 := by
    rw [div_le_iff₀ (by positivity)]
    calc K ^ 2 = η / 64 * ((8 * K) * (8 * K / η)) := by field_simp; ring
      _ ≤ η / 64 * (L * L) := by
          gcongr
      _ = η / 64 * L ^ 2 := by ring
  have e1 : 2 * M / L = 2 * (M / L) := by ring
  have e2 : 4 * K ^ 2 / L ^ 2 = 4 * (K ^ 2 / L ^ 2) := by ring
  rw [e1, e2] at htr
  linarith

end Probe

end BlockBand.Critical.EntireLaw
