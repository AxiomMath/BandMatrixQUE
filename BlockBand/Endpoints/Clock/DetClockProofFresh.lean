module

public import BlockBand.Endpoints.Clock.DetClockProofStep
public import BlockBand.Endpoints.Clock.DetClockProofWard
public import BlockBand.Endpoints.Clock.ClockMixing

/-!
# The deterministic-clock lemma: the conditional expectation of one step

We expand the expectation of one step of the clock determinant for an abstract fresh layer.

Setting: a probability space `(Ω, ν)` (in the lemma: one fresh layer, the past being a
deterministic `(X, Q)`), a random `L`, a random PSD injection `C`, `U = LL*`, `M = E U - I`,
`U⁰ = U - E U`, a deterministic `Q ⪰ 0`, `a ≥ 0`, `κ ≥ 0`, `A = A_a(Q)`. Hypotheses: the
centered bilinear entries of `U` have `L³` norm `≤ c‖u‖‖v‖`; `‖Tr C‖₃ ≤ m_β`, `‖‖C‖‖₃ ≤ m_C`.

`fresh_expand` (the expectation of `step_expansion`):
* `|E F_a(L*QL + κC) - F_a(Q) - (-F_a(Q) Re Tr(AM) + F_a(Q)(Eτ² + Eσ)/2 - aκF_a(Q) E Tr C)|
   ≤ a²(κ²m_β² + κ m_C (1 + ‖M‖ + c)γ) + 8aκ(‖M‖ + c)Tr A · m_β + 800((‖M‖ + c)Tr A)³`;
* `|Eτ² - Re E(Tr AU⁰)²| ≤ ‖M‖Tr A (2c Tr A + ‖M‖ Tr A)` and the same for
  `|Eσ - Re E Tr(AU⁰AU⁰)|` (the mean part of `U` is split off from the centered part).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator

namespace DetClockProof

open ClockMixingAlg ClockMixingProb

/-!
## 1. From `L^p` bounds to integrals
-/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
/-- `‖g‖_r ≤ m` gives `∫|g|^r ≤ m^r` and integrability of `|g|^r` (`r ≥ 1`). -/
theorem integral_rpow_le {g : Ω → ℝ} {r m : ℝ} (hr : 1 ≤ r) (hm : 0 ≤ m)
    (h : eLpNorm g (ENNReal.ofReal r) ν ≤ ENNReal.ofReal m) :
    Integrable (fun x => |g x| ^ r) ν ∧ ∫ x, |g x| ^ r ∂ν ≤ m ^ r := by
  have hr0 : ENNReal.ofReal r ≠ 0 := by simp; linarith
  have hmem : MemLp g (ENNReal.ofReal r) ν := memLp_iff.mpr (lt_of_le_of_lt h ENNReal.ofReal_lt_top)
  have hint := hmem.integrable_norm_rpow hr0 ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal (by linarith)] at hint
  simp only [Real.norm_eq_abs] at hint
  refine ⟨hint, ?_⟩
  have he := hmem.eLpNorm_eq_integral_rpow_norm hr0 ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal (by linarith)] at he
  simp only [Real.norm_eq_abs] at he
  rw [he] at h
  have hI : 0 ≤ ∫ x, |g x| ^ r ∂ν := integral_nonneg fun x => by positivity
  have h2 : (∫ x, |g x| ^ r ∂ν) ^ r⁻¹ ≤ m :=
    (ENNReal.ofReal_le_ofReal_iff hm).mp h
  have h3 := Real.rpow_le_rpow (by positivity) h2 (by linarith : 0 ≤ r)
  rwa [← Real.rpow_mul hI, inv_mul_cancel₀ (by linarith), Real.rpow_one] at h3

/-- Natural powers `k ≤ 3` from an `L³` bound. -/
theorem integral_pow_le {g : Ω → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (h : eLpNorm g (ENNReal.ofReal 3) ν ≤ ENNReal.ofReal m) {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    Integrable (fun x => |g x| ^ k) ν ∧ ∫ x, |g x| ^ k ∂ν ≤ m ^ k := by
  have hk : eLpNorm g (ENNReal.ofReal k) ν ≤ ENNReal.ofReal m :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by exact_mod_cast hk3))).trans h
  have := integral_rpow_le (r := k) (by exact_mod_cast hk1) hm hk
  simp only [Real.rpow_natCast] at this
  exact this

/-- Hölder `(2, 2; 1)` from two `L³` bounds. -/
theorem integral_mul_le {g h : Ω → ℝ} {m₁ m₂ : ℝ} (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (hg : eLpNorm g (ENNReal.ofReal 3) ν ≤ ENNReal.ofReal m₁)
    (hh : eLpNorm h (ENNReal.ofReal 3) ν ≤ ENNReal.ofReal m₂) :
    Integrable (fun x => g x * h x) ν ∧ ∫ x, |g x * h x| ∂ν ≤ m₁ * m₂ := by
  have hgm := aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hg)
  have hhm := aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hh)
  have h23 : ENNReal.ofReal 2 ≤ ENNReal.ofReal 3 := ENNReal.ofReal_le_ofReal (by norm_num)
  have hg2 := (eLpNorm_le_eLpNorm_of_exponent_le (μ := ν) (f := g) h23).trans hg
  have hh2 := (eLpNorm_le_eLpNorm_of_exponent_le (μ := ν) (f := h) h23).trans hh
  have hgh := eLpNorm_mul_le_two hgm hhm (p := 1) one_pos
  rw [show (2 : ℝ) * 1 = 2 by norm_num] at hgh
  have h1 : eLpNorm (fun x => g x * h x) (ENNReal.ofReal 1) ν ≤ ENNReal.ofReal (m₁ * m₂) := by
    refine hgh.trans ?_
    rw [ENNReal.ofReal_mul hm₁]
    exact mul_le_mul' hg2 hh2
  have := integral_rpow_le (r := 1) le_rfl (by positivity) h1
  simp only [Real.rpow_one] at this
  refine ⟨?_, this.2⟩
  exact (this.1.congr (ae_of_all _ fun x => rfl)).mono' (hgm.mul hhm)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs])

end Moments

/-!
## 2. Traces of expectations
-/

section Traces

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {W : ℕ}

theorem integral_trace_mul (A : Matrix (Fin W) (Fin W) ℂ) {V : Ω → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i j, Integrable (fun ω => V ω i j) ν) :
    ∫ ω, (A * V ω).trace ∂ν = (A * matrixExpect ν V).trace := by
  have e1 : (fun ω => (A * V ω).trace) = fun ω => ∑ i, ∑ j, A i j * V ω j i := by
    funext ω; simp [trace, Matrix.mul_apply]
  have e2 : (A * matrixExpect ν V).trace = ∑ i, ∑ j, A i j * ∫ ω, V ω j i ∂ν := by
    simp [trace, Matrix.mul_apply, mE_apply]
  rw [e1, e2]
  calc ∫ ω, ∑ i, ∑ j, A i j * V ω j i ∂ν = ∑ i, ∫ ω, ∑ j, A i j * V ω j i ∂ν :=
        integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hV j i).const_mul _
    _ = ∑ i, ∑ j, ∫ ω, A i j * V ω j i ∂ν :=
        Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => (hV j i).const_mul _
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => integral_const_mul _ _

theorem integrable_trace_mul (A : Matrix (Fin W) (Fin W) ℂ) {V : Ω → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ i j, Integrable (fun ω => V ω i j) ν) :
    Integrable (fun ω => (A * V ω).trace) ν := by
  have e1 : (fun ω => (A * V ω).trace) = fun ω => ∑ i, ∑ j, A i j * V ω j i := by
    funext ω; simp [trace, Matrix.mul_apply]
  rw [e1]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => (hV k i).const_mul _

theorem trace_mul_im_eq_zero {A N : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian)
    (hN : N.IsHermitian) : (A * N).trace.im = 0 := by
  have h : star (A * N).trace = (A * N).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, hA.eq, hN.eq, trace_mul_comm]
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

theorem matrixExpect_isHermitian {V : Ω → Matrix (Fin W) (Fin W) ℂ}
    (hV : ∀ ω, (V ω).IsHermitian) : (matrixExpect ν V).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [← mE_conjTranspose]
  congr 1; funext ω; exact (hV ω).eq

end Traces

/-!
## 3. The expected one-step expansion
-/

section Expand

variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] {W : ℕ}

/-- **The expected one-step expansion** (see the module docstring). -/
theorem fresh_expand {L C : Ω → Matrix (Fin W) (Fin W) ℂ} (hL : Measurable L)
    (hC : Measurable C) (hCp : ∀ ω, (C ω).PosSemidef) {Q : Matrix (Fin W) (Fin W) ℂ}
    (hQ : Q.PosSemidef) {a κ c mβ mC : ℝ} (ha : 0 ≤ a) (hκ : 0 ≤ κ) (hc : 0 ≤ c) (hmβ : 0 ≤ mβ)
    (hmC : 0 ≤ mC)
    (hUi : ∀ i j, Integrable (fun ω => (L ω * (L ω)ᴴ) i j) ν)
    (hfl : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (L ω * (L ω)ᴴ -
        matrixExpect ν (fun ω => L ω * (L ω)ᴴ)) v) (ENNReal.ofReal 3) ν ≤
      ENNReal.ofReal (c * vecNorm u * vecNorm v))
    (hβ : eLpNorm (fun ω => (C ω).trace.re) (ENNReal.ofReal 3) ν ≤ ENNReal.ofReal mβ)
    (hCn : eLpNorm (fun ω => ‖C ω‖) (ENNReal.ofReal 3) ν ≤ ENNReal.ofReal mC) :
    let U := fun ω => L ω * (L ω)ᴴ
    let EU := matrixExpect ν U
    let M := EU - 1
    let A := resolventWeight Q a
    let F := detLaplace Q a
    Integrable (fun ω => detLaplace ((L ω)ᴴ * Q * L ω + ((κ : ℝ) : ℂ) • C ω) a) ν ∧
    Integrable (fun ω => tauA Q (L ω) a ^ 2) ν ∧ Integrable (fun ω => sigA Q (L ω) a) ν ∧
    Integrable (fun ω => (C ω).trace.re) ν ∧
    |(∫ ω, detLaplace ((L ω)ᴴ * Q * L ω + ((κ : ℝ) : ℂ) • C ω) a ∂ν) - F -
        (-(F * (A * M).trace.re) +
          F * ((∫ ω, tauA Q (L ω) a ^ 2 ∂ν) + ∫ ω, sigA Q (L ω) a ∂ν) / 2 -
          a * F * (κ * ∫ ω, (C ω).trace.re ∂ν))| ≤
      a ^ 2 * (κ ^ 2 * mβ ^ 2 + κ * (mC * ((1 + ‖M‖ + c) * Q.trace.re))) +
        8 * a * κ * ((‖M‖ + c) * A.trace.re) * mβ +
        800 * ((‖M‖ + c) * A.trace.re) ^ 3 ∧
    |(∫ ω, tauA Q (L ω) a ^ 2 ∂ν) - (∫ ω, (A * (U ω - EU)).trace ^ 2 ∂ν).re| ≤
      ‖M‖ * A.trace.re * (2 * c * A.trace.re + ‖M‖ * A.trace.re) ∧
    |(∫ ω, sigA Q (L ω) a ∂ν) - (∫ ω, (A * (U ω - EU) * A * (U ω - EU)).trace ∂ν).re| ≤
      ‖M‖ * A.trace.re * (2 * c * A.trace.re + ‖M‖ * A.trace.re) := by
  intro U EU M A F
  have hA : A.PosSemidef := resolventWeight_posSemidef hQ ha
  have hTA : 0 ≤ A.trace.re := trace_re_nonneg hA
  have hγ : 0 ≤ Q.trace.re := trace_re_nonneg hQ
  have hM0 := norm_nonneg M
  have hF0 : 0 < F := detLaplace_pos hQ ha
  have hF1 : F ≤ 1 := detLaplace_le_one hQ ha
  have hUm : Measurable U := meas_mul hL (meas_conjTranspose hL)
  have hτm : Measurable (fun ω => tauA Q (L ω) a) := by
    unfold tauA
    exact Complex.measurable_re.comp (meas_trace (meas_mul measurable_const
      ((hUm).sub measurable_const)))
  have hσm : Measurable (fun ω => sigA Q (L ω) a) := by
    unfold sigA
    exact Complex.measurable_re.comp (meas_trace (meas_mul (meas_mul (meas_mul measurable_const
      (hUm.sub measurable_const)) measurable_const) (hUm.sub measurable_const)))
  have hβm : Measurable (fun ω => (C ω).trace.re) := Complex.measurable_re.comp (meas_trace hC)
  have hτ0m : Measurable (fun ω => (A * (U ω - EU)).trace.re) :=
    Complex.measurable_re.comp (meas_trace (meas_mul measurable_const
      (hUm.sub measurable_const)))
  have hQUm : Measurable (fun ω => (Q * U ω).trace.re) :=
    Complex.measurable_re.comp (meas_trace (meas_mul measurable_const hUm))
  have hUh : ∀ ω, (U ω).IsHermitian := fun ω => isHermitian_mul_conjTranspose_self _
  have hEUh : EU.IsHermitian := matrixExpect_isHermitian hUh
  have hp3 : (1 : ℝ) ≤ 3 := by norm_num
  set mτ := (‖M‖ + c) * A.trace.re with hmτ
  have hmτ0 : 0 ≤ mτ := by positivity
  -- conditional moment bounds
  have hτ3 : eLpNorm (fun ω => tauA Q (L ω) a) (ENNReal.ofReal 3) ν ≤ ENNReal.ofReal mτ := by
    have h := condTrace_le (ν := ν) hA 1 1 (T := U) hp3 hc hfl
    rw [one_smul] at h
    refine le_trans (eLpNorm_mono hτm.aestronglyMeasurable fun ω => ?_) h
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  have hσ3 : eLpNorm (fun ω => Real.sqrt (sigA Q (L ω) a)) (ENNReal.ofReal 3) ν ≤
      ENNReal.ofReal mτ := by
    have h := condHS_le (ν := ν) hA 1 1 hUm hp3 le_rfl (by norm_num) hc hfl
    rw [one_smul] at h
    refine le_trans (le_of_eq ?_) h
    congr 1; funext ω; exact sqrt_sigA hQ ha (L ω)
  have hτ03 : eLpNorm (fun ω => (A * (U ω - EU)).trace.re) (ENNReal.ofReal 3) ν ≤
      ENNReal.ofReal (c * A.trace.re) := by
    have h := condTrace_le (ν := ν) hA EU 1 (T := U) hp3 hc hfl
    rw [one_smul, sub_self, norm_zero, zero_add] at h
    refine le_trans (eLpNorm_mono hτ0m.aestronglyMeasurable fun ω => ?_) h
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  have hh03 : eLpNorm (fun ω => hsSandwich A (U ω - EU)) (ENNReal.ofReal 3) ν ≤
      ENNReal.ofReal (c * A.trace.re) := by
    have h := condHS_le (ν := ν) hA EU 1 hUm hp3 le_rfl (by norm_num) hc hfl
    rwa [one_smul, sub_self, norm_zero, zero_add] at h
  have hEUn : ‖EU‖ ≤ 1 + ‖M‖ := by
    have : EU = M + 1 := by simp [M]
    rw [this]
    have := BlockBand.Layers.lct_norm_one_le (n := Fin W)
    exact (norm_add_le _ _).trans (by linarith)
  set mQ := (1 + ‖M‖ + c) * Q.trace.re with hmQ
  have hQU3 : eLpNorm (fun ω => (Q * U ω).trace.re) (ENNReal.ofReal 3) ν ≤ ENNReal.ofReal mQ := by
    have h := condTrace_le (ν := ν) hQ 0 0 (T := U) hp3 hc hfl
    simp only [smul_zero, sub_zero] at h
    refine le_trans (eLpNorm_mono hQUm.aestronglyMeasurable fun ω => ?_)
      (h.trans (ENNReal.ofReal_le_ofReal ?_))
    · rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
    · exact mul_le_mul_of_nonneg_right (by linarith) hγ
  have hmQ0 : 0 ≤ mQ := by positivity
  -- integrability and integral bounds
  obtain ⟨iτ1, _⟩ := integral_pow_le hmτ0 hτ3 (k := 1) le_rfl (by norm_num)
  obtain ⟨iτ2, _⟩ := integral_pow_le hmτ0 hτ3 (k := 2) (by norm_num) (by norm_num)
  obtain ⟨iτ3, Iτ3⟩ := integral_pow_le hmτ0 hτ3 (k := 3) (by norm_num) le_rfl
  obtain ⟨iσ2, _⟩ := integral_pow_le hmτ0 hσ3 (k := 2) (by norm_num) (by norm_num)
  obtain ⟨iσ3, Iσ3⟩ := integral_pow_le hmτ0 hσ3 (k := 3) (by norm_num) le_rfl
  obtain ⟨iβ1, _⟩ := integral_pow_le hmβ hβ (k := 1) le_rfl (by norm_num)
  obtain ⟨iβ2, Iβ2⟩ := integral_pow_le hmβ hβ (k := 2) (by norm_num) (by norm_num)
  obtain ⟨iCQ, ICQ⟩ := integral_mul_le hmC hmQ0 hCn hQU3
  obtain ⟨iτβ, Iτβ⟩ := integral_mul_le hmτ0 hmβ hτ3 hβ
  obtain ⟨iσβ, Iσβ⟩ := integral_mul_le hmτ0 hmβ hσ3 hβ
  obtain ⟨iτ01, Iτ01⟩ := integral_pow_le (by positivity) hτ03 (k := 1) le_rfl (by norm_num)
  obtain ⟨iτ02, _⟩ := integral_pow_le (by positivity) hτ03 (k := 2) (by norm_num) (by norm_num)
  obtain ⟨ih01, Ih01⟩ := integral_pow_le (by positivity) hh03 (k := 1) le_rfl (by norm_num)
  obtain ⟨ih02, _⟩ := integral_pow_le (by positivity) hh03 (k := 2) (by norm_num) (by norm_num)
  have iτabs : Integrable (fun ω => |tauA Q (L ω) a|) ν := by simpa using iτ1
  have iτ : Integrable (fun ω => tauA Q (L ω) a) ν :=
    iτabs.mono' hτm.aestronglyMeasurable (ae_of_all _ fun ω => by rw [Real.norm_eq_abs])
  have iτsq : Integrable (fun ω => tauA Q (L ω) a ^ 2) ν := by simpa [sq_abs] using iτ2
  have iσ : Integrable (fun ω => sigA Q (L ω) a) ν := by
    refine iσ2.congr (ae_of_all _ fun ω => ?_)
    simp only [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sq_sqrt (sigA_nonneg hQ ha (L ω))
  have iβabs : Integrable (fun ω => |(C ω).trace.re|) ν := by simpa using iβ1
  have iβ : Integrable (fun ω => (C ω).trace.re) ν :=
    iβabs.mono' hβm.aestronglyMeasurable (ae_of_all _ fun ω => by rw [Real.norm_eq_abs])
  have hBm : Measurable (fun ω => detLaplace ((L ω)ᴴ * Q * L ω + ((κ : ℝ) : ℂ) • C ω) a) := by
    unfold detLaplace
    refine Measurable.inv (Complex.measurable_re.comp ?_)
    refine (Continuous.measurable (continuous_id.matrix_det)).comp ?_
    exact measurable_const.add (meas_smul _ ((meas_mul (meas_mul (meas_conjTranspose hL)
      measurable_const) hL).add (meas_smul _ hC)))
  have hLQL : ∀ ω, ((L ω)ᴴ * Q * L ω).PosSemidef := fun ω => by
    have h1 := hQ.conjTranspose_mul_mul_same (L ω)
    simpa [Matrix.mul_assoc] using h1
  have hPB : ∀ ω, ((L ω)ᴴ * Q * L ω + ((κ : ℝ) : ℂ) • C ω).PosSemidef := fun ω =>
    (hLQL ω).add ((hCp ω).smul (Complex.zero_le_real.mpr hκ))
  have iF : Integrable (fun ω => detLaplace ((L ω)ᴴ * Q * L ω + ((κ : ℝ) : ℂ) • C ω) a) ν := by
    refine Integrable.of_bound hBm.aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (detLaplace_pos (hPB ω) ha)]
    exact detLaplace_le_one (hPB ω) ha
  have hQUe : ∀ ω, ((L ω)ᴴ * Q * L ω).trace = (Q * U ω).trace := by
    intro ω
    simp only [U]
    rw [← Matrix.mul_assoc, trace_mul_comm (Q * L ω), Matrix.mul_assoc]
  refine ⟨iF, iτsq, iσ, iβ, ?_, ?_, ?_⟩
  · -- the expansion
    have hpt : ∀ ω, |detLaplace ((L ω)ᴴ * Q * L ω + ((κ : ℝ) : ℂ) • C ω) a - F -
        (-(F * tauA Q (L ω) a) + F * (tauA Q (L ω) a ^ 2 + sigA Q (L ω) a) / 2 -
          a * F * (κ * (C ω).trace.re))| ≤
        a ^ 2 * (κ ^ 2 * |(C ω).trace.re| ^ 2 + κ * |‖C ω‖ * (Q * U ω).trace.re|) +
          4 * a * κ * (|tauA Q (L ω) a * (C ω).trace.re| +
            |Real.sqrt (sigA Q (L ω) a) * (C ω).trace.re|) +
          400 * (|Real.sqrt (sigA Q (L ω) a)| ^ 3 + |tauA Q (L ω) a| ^ 3) := by
      intro ω
      have hB : (((κ : ℝ) : ℂ) • C ω).PosSemidef := (hCp ω).smul (Complex.zero_le_real.mpr hκ)
      have h := step_expansion hQ hB ha (L ω)
      have hTB : (((κ : ℝ) : ℂ) • C ω).trace.re = κ * (C ω).trace.re := by
        rw [trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      have hnB : ‖((κ : ℝ) : ℂ) • C ω‖ = κ * ‖C ω‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ]
      have hP : ((L ω)ᴴ * Q * L ω).trace.re = (Q * U ω).trace.re := by rw [hQUe ω]
      rw [hTB, hnB, hP] at h
      have hβ0 : 0 ≤ (C ω).trace.re := trace_re_nonneg (hCp ω)
      have hQU0 : 0 ≤ (Q * U ω).trace.re := by
        rw [← hQUe ω]; exact trace_re_nonneg (hLQL ω)
      refine h.trans (le_of_eq ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hβ0, abs_of_nonneg hQU0, abs_norm,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      ring
    have iT1 : Integrable (fun ω => a ^ 2 * (κ ^ 2 * |(C ω).trace.re| ^ 2 +
        κ * |‖C ω‖ * (Q * U ω).trace.re|)) ν :=
      ((iβ2.const_mul (κ ^ 2)).add (iCQ.abs.const_mul κ)).const_mul (a ^ 2)
    have iT2 : Integrable (fun ω => 4 * a * κ * (|tauA Q (L ω) a * (C ω).trace.re| +
        |Real.sqrt (sigA Q (L ω) a) * (C ω).trace.re|)) ν :=
      (iτβ.abs.add iσβ.abs).const_mul (4 * a * κ)
    have iT3 : Integrable (fun ω => 400 * (|Real.sqrt (sigA Q (L ω) a)| ^ 3 +
        |tauA Q (L ω) a| ^ 3)) ν := (iσ3.add iτ3).const_mul 400
    have IT1 : ∫ ω, a ^ 2 * (κ ^ 2 * |(C ω).trace.re| ^ 2 +
        κ * |‖C ω‖ * (Q * U ω).trace.re|) ∂ν ≤ a ^ 2 * (κ ^ 2 * mβ ^ 2 + κ * (mC * mQ)) := by
      rw [integral_const_mul, integral_add (iβ2.const_mul (κ ^ 2)) (iCQ.abs.const_mul κ),
        integral_const_mul, integral_const_mul]
      have k1 := mul_le_mul_of_nonneg_left Iβ2 (sq_nonneg κ)
      have k2 := mul_le_mul_of_nonneg_left ICQ hκ
      exact mul_le_mul_of_nonneg_left (add_le_add k1 k2) (sq_nonneg a)
    have IT2 : ∫ ω, 4 * a * κ * (|tauA Q (L ω) a * (C ω).trace.re| +
        |Real.sqrt (sigA Q (L ω) a) * (C ω).trace.re|) ∂ν ≤ 8 * a * κ * mτ * mβ := by
      rw [integral_const_mul, integral_add iτβ.abs iσβ.abs]
      have := mul_le_mul_of_nonneg_left (add_le_add Iτβ Iσβ) (by positivity : 0 ≤ 4 * a * κ)
      linarith
    have IT3 : ∫ ω, 400 * (|Real.sqrt (sigA Q (L ω) a)| ^ 3 + |tauA Q (L ω) a| ^ 3) ∂ν ≤
        800 * mτ ^ 3 := by
      rw [integral_const_mul, integral_add iσ3 iτ3]
      linarith
    have iτσ : Integrable (fun ω => tauA Q (L ω) a ^ 2 + sigA Q (L ω) a) ν := iτsq.add iσ
    have i1 : Integrable (fun ω => -(F * tauA Q (L ω) a)) ν := (iτ.const_mul F).neg
    have i2 : Integrable (fun ω => F * (tauA Q (L ω) a ^ 2 + sigA Q (L ω) a) / 2) ν :=
      (iτσ.const_mul F).div_const 2
    have i3 : Integrable (fun ω => a * F * (κ * (C ω).trace.re)) ν :=
      (iβ.const_mul κ).const_mul (a * F)
    have i12 : Integrable (fun ω => -(F * tauA Q (L ω) a) +
        F * (tauA Q (L ω) a ^ 2 + sigA Q (L ω) a) / 2) ν := i1.add i2
    have iG : Integrable (fun ω => -(F * tauA Q (L ω) a) +
        F * (tauA Q (L ω) a ^ 2 + sigA Q (L ω) a) / 2 - a * F * (κ * (C ω).trace.re)) ν :=
      i12.sub i3
    have IG : ∫ ω, (-(F * tauA Q (L ω) a) + F * (tauA Q (L ω) a ^ 2 + sigA Q (L ω) a) / 2 -
        a * F * (κ * (C ω).trace.re)) ∂ν =
        -(F * ∫ ω, tauA Q (L ω) a ∂ν) +
          F * ((∫ ω, tauA Q (L ω) a ^ 2 ∂ν) + ∫ ω, sigA Q (L ω) a ∂ν) / 2 -
          a * F * (κ * ∫ ω, (C ω).trace.re ∂ν) := by
      rw [integral_sub i12 i3, integral_add i1 i2, integral_neg, integral_const_mul, integral_div,
        integral_const_mul, integral_add iτsq iσ, integral_const_mul, integral_const_mul]
    have hmean : ∫ ω, tauA Q (L ω) a ∂ν = (A * M).trace.re := by
      have h1 : ∀ ω, tauA Q (L ω) a = (A * U ω).trace.re - A.trace.re := by
        intro ω
        unfold tauA
        rw [Matrix.mul_sub, Matrix.mul_one, trace_sub, Complex.sub_re]
      simp_rw [h1]
      have iAU : Integrable (fun ω => (A * U ω).trace.re) ν := (integrable_trace_mul A hUi).re
      have hre : ∫ ω, (A * U ω).trace.re ∂ν = (∫ ω, (A * U ω).trace ∂ν).re := by
        have := integral_re (integrable_trace_mul A hUi)
        simpa using this
      rw [integral_sub iAU (integrable_const _), integral_const,
        smul_eq_mul, probReal_univ, one_mul, hre, integral_trace_mul A hUi]
      simp only [M, Matrix.mul_sub, Matrix.mul_one, trace_sub, Complex.sub_re]
      rfl
    have hdiff : (∫ ω, detLaplace ((L ω)ᴴ * Q * L ω + ((κ : ℝ) : ℂ) • C ω) a ∂ν) - F -
        (-(F * (A * M).trace.re) +
          F * ((∫ ω, tauA Q (L ω) a ^ 2 ∂ν) + ∫ ω, sigA Q (L ω) a ∂ν) / 2 -
          a * F * (κ * ∫ ω, (C ω).trace.re ∂ν)) =
        ∫ ω, (detLaplace ((L ω)ᴴ * Q * L ω + ((κ : ℝ) : ℂ) • C ω) a - F -
          (-(F * tauA Q (L ω) a) + F * (tauA Q (L ω) a ^ 2 + sigA Q (L ω) a) / 2 -
            a * F * (κ * (C ω).trace.re))) ∂ν := by
      have iFc : Integrable (fun ω => detLaplace ((L ω)ᴴ * Q * L ω + ((κ : ℝ) : ℂ) • C ω) a - F)
          ν := iF.sub (integrable_const F)
      rw [integral_sub iFc iG, integral_sub iF (integrable_const F),
        integral_const, smul_eq_mul, probReal_univ, one_mul, IG, hmean]
    rw [hdiff]
    refine (abs_integral_le_integral_abs).trans ?_
    have iT12 : Integrable (fun ω => a ^ 2 * (κ ^ 2 * |(C ω).trace.re| ^ 2 +
        κ * |‖C ω‖ * (Q * U ω).trace.re|) +
        4 * a * κ * (|tauA Q (L ω) a * (C ω).trace.re| +
          |Real.sqrt (sigA Q (L ω) a) * (C ω).trace.re|)) ν := iT1.add iT2
    have iT : Integrable (fun ω => a ^ 2 * (κ ^ 2 * |(C ω).trace.re| ^ 2 +
        κ * |‖C ω‖ * (Q * U ω).trace.re|) +
        4 * a * κ * (|tauA Q (L ω) a * (C ω).trace.re| +
          |Real.sqrt (sigA Q (L ω) a) * (C ω).trace.re|) +
        400 * (|Real.sqrt (sigA Q (L ω) a)| ^ 3 + |tauA Q (L ω) a| ^ 3)) ν := iT12.add iT3
    have iρ : Integrable (fun ω => |detLaplace ((L ω)ᴴ * Q * L ω + ((κ : ℝ) : ℂ) • C ω) a - F -
        (-(F * tauA Q (L ω) a) + F * (tauA Q (L ω) a ^ 2 + sigA Q (L ω) a) / 2 -
          a * F * (κ * (C ω).trace.re))|) ν := ((iF.sub (integrable_const F)).sub iG).abs
    have hle := integral_mono iρ iT hpt
    rw [integral_add iT12 iT3, integral_add iT1 iT2] at hle
    refine hle.trans ?_
    rw [hmQ, hmτ] at *
    linarith
  · -- the second moment of `τ`
    set m := (A * M).trace.re with hm
    have hmb : |m| ≤ ‖M‖ * A.trace.re := by
      rw [hm]
      exact (Complex.abs_re_le_norm _).trans (norm_trace_mul_le hA M)
    have hsplit : ∀ ω, tauA Q (L ω) a = (A * (U ω - EU)).trace.re + m := by
      intro ω
      unfold tauA
      rw [hm]
      have : L ω * (L ω)ᴴ - 1 = (U ω - EU) + M := by simp [U, M]
      rw [this, Matrix.mul_add, trace_add, Complex.add_re]
    have hreal : ∀ ω, (A * (U ω - EU)).trace = (((A * (U ω - EU)).trace.re : ℝ) : ℂ) := by
      intro ω
      apply Complex.ext
      · simp
      · simp only [Complex.ofReal_im]
        exact trace_mul_im_eq_zero hA.1 ((hUh ω).sub hEUh)
    have hcplx : (∫ ω, (A * (U ω - EU)).trace ^ 2 ∂ν).re =
        ∫ ω, (A * (U ω - EU)).trace.re ^ 2 ∂ν := by
      have : (fun ω => (A * (U ω - EU)).trace ^ 2) =
          fun ω => (((A * (U ω - EU)).trace.re ^ 2 : ℝ) : ℂ) := by
        funext ω; rw [hreal ω]; push_cast; simp
      rw [this, integral_complex_ofReal, Complex.ofReal_re]
    rw [hcplx]
    have iτ0sq : Integrable (fun ω => (A * (U ω - EU)).trace.re ^ 2) ν := by
      simpa [sq_abs] using iτ02
    have iτ0 : Integrable (fun ω => |(A * (U ω - EU)).trace.re|) ν := by simpa using iτ01
    rw [← integral_sub iτsq iτ0sq]
    have hpt : ∀ ω, |tauA Q (L ω) a ^ 2 - (A * (U ω - EU)).trace.re ^ 2| ≤
        2 * |m| * |(A * (U ω - EU)).trace.re| + |m| ^ 2 := by
      intro ω
      rw [hsplit ω]
      have : ((A * (U ω - EU)).trace.re + m) ^ 2 - (A * (U ω - EU)).trace.re ^ 2 =
          2 * m * (A * (U ω - EU)).trace.re + m ^ 2 := by ring
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_two, abs_pow]
    refine (abs_integral_le_integral_abs).trans ?_
    have iA : Integrable (fun ω => |tauA Q (L ω) a ^ 2 - (A * (U ω - EU)).trace.re ^ 2|) ν :=
      (iτsq.sub iτ0sq).abs
    have iB1 : Integrable (fun ω => 2 * |m| * |(A * (U ω - EU)).trace.re|) ν :=
      iτ0.const_mul (2 * |m|)
    have iB : Integrable (fun ω => 2 * |m| * |(A * (U ω - EU)).trace.re| + |m| ^ 2) ν :=
      iB1.add (integrable_const _)
    refine (integral_mono iA iB hpt).trans ?_
    rw [integral_add iB1 (integrable_const _), integral_const_mul, integral_const,
      smul_eq_mul, probReal_univ, one_mul]
    have hI : ∫ ω, |(A * (U ω - EU)).trace.re| ∂ν ≤ c * A.trace.re := by
      have := Iτ01; simpa using this
    have h1 := mul_le_mul_of_nonneg_left hI (by positivity : 0 ≤ 2 * |m|)
    have h2 : |m| ^ 2 ≤ (‖M‖ * A.trace.re) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hmb 2
    have h3 : 2 * |m| * (c * A.trace.re) ≤ 2 * (‖M‖ * A.trace.re) * (c * A.trace.re) := by
      have : 0 ≤ c * A.trace.re := by positivity
      have := mul_le_mul_of_nonneg_right hmb this
      linarith
    have e : ‖M‖ * A.trace.re * (2 * c * A.trace.re + ‖M‖ * A.trace.re) =
        2 * (‖M‖ * A.trace.re) * (c * A.trace.re) + (‖M‖ * A.trace.re) ^ 2 := by ring
    rw [e]
    linarith
  · -- the mean of `σ`
    set h := hsSandwich A M with hh
    have hhb : h ≤ ‖M‖ * A.trace.re := hsSandwich_le hA M
    have hh0 : 0 ≤ h := hsSandwich_nonneg _ _
    have hsq : ∀ ω, sigA Q (L ω) a = hsSandwich A (U ω - 1) ^ 2 := fun ω => sigA_eq_sq hQ ha (L ω)
    have hU0h : ∀ ω, (U ω - EU)ᴴ = U ω - EU := fun ω => ((hUh ω).sub hEUh).eq
    have hcplx : ∀ ω, (A * (U ω - EU) * A * (U ω - EU)).trace =
        ((hsSandwich A (U ω - EU) ^ 2 : ℝ) : ℂ) := by
      intro ω
      rw [hsSandwich_eq_sqrt hA.1, Real.sq_sqrt (sandwichSum_nonneg hA _), ←
        trace_sandwich_eq_sum, hU0h]
    have hcI : (∫ ω, (A * (U ω - EU) * A * (U ω - EU)).trace ∂ν).re =
        ∫ ω, hsSandwich A (U ω - EU) ^ 2 ∂ν := by
      simp_rw [hcplx]
      rw [integral_complex_ofReal, Complex.ofReal_re]
    rw [hcI]
    have ih0sq : Integrable (fun ω => hsSandwich A (U ω - EU) ^ 2) ν := by
      simpa [sq_abs] using ih02
    have ih0 : Integrable (fun ω => hsSandwich A (U ω - EU)) ν := by
      simpa [abs_of_nonneg (hsSandwich_nonneg _ _)] using ih01
    rw [← integral_sub iσ ih0sq]
    have hpt : ∀ ω, |sigA Q (L ω) a - hsSandwich A (U ω - EU) ^ 2| ≤
        h * (2 * hsSandwich A (U ω - EU) + h) := by
      intro ω
      rw [hsq ω]
      set x := hsSandwich A (U ω - 1)
      set y := hsSandwich A (U ω - EU)
      have hx0 : 0 ≤ x := hsSandwich_nonneg _ _
      have hy0 : 0 ≤ y := hsSandwich_nonneg _ _
      have e1 : U ω - 1 = (U ω - EU) + M := by simp [M]
      have h1 : x ≤ y + h := by
        simp only [x, y, hh]; rw [e1]; exact hsSandwich_add_le hA _ _
      have h2 : y ≤ x + h := by
        have e2 : U ω - EU = (U ω - 1) + (-1 : ℂ) • M := by simp [M]
        simp only [x, y, hh]
        rw [e2]
        refine (hsSandwich_add_le hA _ _).trans ?_
        rw [hsSandwich_smul hA.1, norm_neg, norm_one, one_mul]
      have : |x ^ 2 - y ^ 2| = |x - y| * (x + y) := by
        rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul,
          abs_of_nonneg (show 0 ≤ x + y by linarith)]
      rw [this]
      have hxy : |x - y| ≤ h := abs_le.mpr ⟨by linarith, by linarith⟩
      calc |x - y| * (x + y) ≤ h * (x + y) := mul_le_mul_of_nonneg_right hxy (by linarith)
        _ ≤ h * (2 * y + h) := mul_le_mul_of_nonneg_left (by linarith) hh0
    refine (abs_integral_le_integral_abs).trans ?_
    have iA : Integrable (fun ω => |sigA Q (L ω) a - hsSandwich A (U ω - EU) ^ 2|) ν :=
      (iσ.sub ih0sq).abs
    have iB1 : Integrable (fun ω => 2 * h * hsSandwich A (U ω - EU)) ν := ih0.const_mul (2 * h)
    have iB : Integrable (fun ω => 2 * h * hsSandwich A (U ω - EU) + h * h) ν :=
      iB1.add (integrable_const _)
    refine (integral_mono iA iB (fun ω => (hpt ω).trans (le_of_eq (by ring)))).trans ?_
    rw [integral_add iB1 (integrable_const _), integral_const_mul, integral_const,
      smul_eq_mul, probReal_univ, one_mul]
    have hI : ∫ ω, hsSandwich A (U ω - EU) ∂ν ≤ c * A.trace.re := by
      have := Ih01; simpa [abs_of_nonneg (hsSandwich_nonneg _ _)] using this
    have h1 := mul_le_mul_of_nonneg_left hI (by positivity : 0 ≤ 2 * h)
    have h3 : 2 * h * (c * A.trace.re) ≤ 2 * (‖M‖ * A.trace.re) * (c * A.trace.re) := by
      have : 0 ≤ c * A.trace.re := by positivity
      have := mul_le_mul_of_nonneg_right hhb this
      linarith
    have h4 : h * h ≤ (‖M‖ * A.trace.re) * (‖M‖ * A.trace.re) :=
      mul_le_mul hhb hhb hh0 (by positivity)
    have e : ‖M‖ * A.trace.re * (2 * c * A.trace.re + ‖M‖ * A.trace.re) =
        2 * (‖M‖ * A.trace.re) * (c * A.trace.re) + (‖M‖ * A.trace.re) * (‖M‖ * A.trace.re) := by
      ring
    rw [e]
    linarith

end Expand

end DetClockProof

end BlockBand.Endpoints.Clock
