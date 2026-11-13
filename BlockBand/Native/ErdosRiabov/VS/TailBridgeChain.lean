module

public import BlockBand.Native.ErdosRiabov.VS.TailBridge

set_option autoImplicit false

/-!
# `combMg` by integration by parts against the single-chain martingales

The martingale part of a combination of chains with time-dependent coefficients, expressed by
integration by parts through the martingale parts of the single chains.

* `chainMg A₀ zf B K α t x = M^{Re}_t + i M^{Im}_t`: the complex martingale part `𝓜^α` of the
  single chain `F_α(t, Y_t) = tr(K_α C_α(t, Y_t))` (`Re F_α` is `chainTestT … (K_α)`, `Im F_α` is
  `chainTestT … (-i K_α)`; compensated parts for the Itô drift).
  `chainMg_zero`: `𝓜^α_0 = 0`.
* **`combMg_eq_ibp`**: a.s., for every `t`,
  `combMg A₀ zf B K c t = ∑_α (c_α(t) 𝓜^α_t - ∫_0^t c_α'(s) 𝓜^α_s ds)`
  (`C²` coefficients `c_α : ℝ → ℂ`). By `itoDrift_linComb`, `ibp_martingalePart` and
  `smCompensated_linComb_vs`, applied to the real and imaginary parts.
* `intervalIntegrable_chainMg`: a.s. `s ↦ 𝓜^α_s` is interval integrable on every `[0, t]`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open MeasureTheory Set Filter Topology Matrix Function
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.CEH.Flow
open scoped NNReal

/-!
### Generic facts
-/

section Generic

variable {Ω : Type*} {d : ℕ}

theorem itoDrift_neg (φ : ℝ × (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) (t : ℝ≥0) (b : Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) :
    itoDrift (fun q => -φ q) y t b A = -itoDrift φ y t b A := by
  have h1 : fderiv ℝ (fun q => -φ q) = fun q => -fderiv ℝ φ q := funext fun q => fderiv_neg
  have h2 : fderiv ℝ (fderiv ℝ (fun q => -φ q)) = fun q => -fderiv ℝ (fderiv ℝ φ) q := by
    rw [h1]
    exact funext fun q => fderiv_neg
  simp only [itoDrift, partialTime, partialSpace, partialSpace2]
  rw [h2, h1]
  simp only [_root_.neg_apply, mul_neg, Finset.sum_neg_distrib]
  ring

theorem smCompensated_testProc_neg (φ : ℝ × (Fin d → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (t : ℝ≥0) (ω : Ω) :
    smCompensated (testProc (fun q => -φ q) Y) (testDrift (fun q => -φ q) Y A) 0 t ω =
      -smCompensated (testProc φ Y) (testDrift φ Y A) 0 t ω := by
  simp only [smCompensated, testProc, testDrift, itoDrift_neg, integral_neg]
  ring

/-- On a continuous path with integrable drift, `s ↦ M_s` is interval integrable on `[0, t]`. -/
theorem intervalIntegrable_smCompensated_path (Y : ℝ≥0 → Ω → Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) {ω : Ω} (hY : Continuous fun t => Y t ω)
    {φ : ℝ × (Fin d → ℝ) → ℝ} (hφ : Continuous φ) (t : ℝ≥0)
    (hβ : IntegrableOn (fun s : ℝ => itoDrift φ (Y s.toNNReal ω) s.toNNReal 0 A) (Ioc 0 t)) :
    IntervalIntegrable (fun s : ℝ => smCompensated (testProc φ Y) (testDrift φ Y A) 0
      s.toNNReal ω) volume 0 t := by
  have ht0 : (0 : ℝ) ≤ t := t.2
  set f : ℝ → ℝ := fun s => φ ((s.toNNReal : ℝ), Y s.toNNReal ω) with hf
  set b : ℝ → ℝ := fun s => itoDrift φ (Y s.toNNReal ω) s.toNNReal 0 A with hb
  have hfc : Continuous f :=
    hφ.comp ((NNReal.continuous_coe.comp continuous_real_toNNReal).prodMk
      (hY.comp continuous_real_toNNReal))
  have hbI : IntegrableOn b (uIcc 0 t) volume := by
    rw [uIcc_of_le ht0, integrableOn_Icc_iff_integrableOn_Ioc]
    exact hβ
  have hcont : ContinuousOn (fun s => f s - f 0 - ∫ r in (0 : ℝ)..s, b r) (uIcc 0 t) :=
    (hfc.continuousOn.sub continuousOn_const).sub
      (intervalIntegral.continuousOn_primitive_interval hbI)
  refine (hcont.congr fun s hs => ?_).intervalIntegrable
  rw [uIcc_of_le ht0] at hs
  simp only [smCompensated, testProc, testDrift, hf, hb, Real.toNNReal_zero, NNReal.coe_zero]
  rw [integral_Ioc_toNNReal_eq hs.1]

theorem intervalIntegral_ofReal_add_mul_I {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    ∫ s in a..b, ((f s : ℂ) + (g s : ℂ) * Complex.I) =
      ((∫ s in a..b, f s : ℝ) : ℂ) + ((∫ s in a..b, g s : ℝ) : ℂ) * Complex.I := by
  have hf' : IntervalIntegrable (fun s => (f s : ℂ)) volume a b := ⟨hf.1.ofReal, hf.2.ofReal⟩
  have hg' : IntervalIntegrable (fun s => (g s : ℂ)) volume a b := ⟨hg.1.ofReal, hg.2.ofReal⟩
  rw [intervalIntegral.integral_add hf' (hg'.mul_const _), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]

theorem deriv_re_comp {c : ℝ → ℂ} {s : ℝ} (hc : DifferentiableAt ℝ c s) :
    deriv (fun r => (c r).re) s = (deriv c s).re :=
  (Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hc.hasDerivAt).deriv

theorem deriv_im_comp {c : ℝ → ℂ} {s : ℝ} (hc : DifferentiableAt ℝ c s) :
    deriv (fun r => (c r).im) s = (deriv c s).im :=
  (Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hc.hasDerivAt).deriv

end Generic

/-!
### Single-chain martingales
-/

variable {p : BlockBand.Parameters} {k : ℕ} {ι : Type*} [Fintype ι]

/-- Real part `M^{Re}` of the single-chain martingale `𝓜^α`. -/
def chainMgRe (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) (α : ι) : ℝ≥0 → RingSample p → ℝ :=
  smCompensated (testProc (chainTestT A₀ (ringMatrixFin p) (zf α) (B α) (K α)) (vsNoise p))
    (testDrift (chainTestT A₀ (ringMatrixFin p) (zf α) (B α) (K α)) (vsNoise p)
      (diagonal (ringVariance p))) 0

/-- Imaginary part `M^{Im}` of `𝓜^α` (weight `-i K_α`). -/
def chainMgIm (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) (α : ι) : ℝ≥0 → RingSample p → ℝ :=
  smCompensated
    (testProc (chainTestT A₀ (ringMatrixFin p) (zf α) (B α) (-Complex.I • K α)) (vsNoise p))
    (testDrift (chainTestT A₀ (ringMatrixFin p) (zf α) (B α) (-Complex.I • K α)) (vsNoise p)
      (diagonal (ringVariance p))) 0

/-- **The single-chain complex martingale** `𝓜^α_t = M^{Re}_t + i M^{Im}_t`, the martingale part
of `tr(K_α C_α(t, Y_t))`. -/
def chainMg (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) (α : ι) (t : ℝ≥0) (x : RingSample p) : ℂ :=
  (chainMgRe A₀ zf B K α t x : ℂ) + (chainMgIm A₀ zf B K α t x : ℂ) * Complex.I

omit [Fintype ι] in
theorem chainMg_zero (A₀ : RingMat p) (zf : ι → Fin k → ℝ → ℂ) (B : ι → Fin k → RingMat p)
    (K : ι → RingMat p) (α : ι) (x : RingSample p) : chainMg A₀ zf B K α 0 x = 0 := by
  simp [chainMg, chainMgRe, chainMgIm, smCompensated]

theorem chainTestT_I_smul (A₀ : RingMat p) (z : Fin k → ℝ → ℂ) (B : Fin k → RingMat p)
    (K : RingMat p) :
    chainTestT A₀ (ringMatrixFin p) z B (Complex.I • K) =
      fun q => -chainTestT A₀ (ringMatrixFin p) z B (-Complex.I • K) q := by
  funext q
  simp only [chainTestT, chainTest, reTr, Matrix.smul_mul, trace_smul, smul_eq_mul, neg_mul,
    Complex.neg_re, neg_neg]

/-- A.s. along `Y_t - Y_0`, the drift of a Borel `C²` test function is locally integrable and
its martingale part is interval integrable in time. -/
theorem ae_vs_integrable {φ : ℝ × (Fin (ringDim p) → ℝ) → ℝ} (μ : Measure p.SiteMatrix)
    [IsProbabilityMeasure μ] (hφm : Measurable φ) (hφ : ContDiff ℝ 2 φ) :
    ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ t : ℝ≥0,
      IntervalIntegrable (fun s : ℝ => smCompensated (testProc φ (vsNoise p))
        (testDrift φ (vsNoise p) (diagonal (ringVariance p))) 0 s.toNNReal x) volume 0 t := by
  have H := vsNoise_itoFormula μ isOpen_univ (ae_of_all _ fun _ _ => Set.mem_univ _) hφm
    hφ.contDiffOn
  filter_upwards [H.integrable] with x hx t
  exact intervalIntegrable_smCompensated_path (vsNoise p) _ (continuous_vsNoise p x)
    hφ.continuous t ((hx t).1 0)

variable {A₀ : RingMat p} (hA₀ : A₀.IsHermitian) {zf : ι → Fin k → ℝ → ℂ}
  (hzC : ∀ α j, ContDiff ℝ 2 (zf α j)) (hzim : ∀ α j t, (zf α j t).im ≠ 0)

include hA₀ hzC hzim in
/-- A.s., every single-chain martingale is interval integrable in time on every `[0, t]`. -/
theorem intervalIntegrable_chainMg (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    (B : ι → Fin k → RingMat p) (K : ι → RingMat p) :
    ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ α, ∀ t : ℝ≥0,
      IntervalIntegrable (fun s : ℝ => chainMgRe A₀ zf B K α s.toNNReal x) volume 0 t ∧
      IntervalIntegrable (fun s : ℝ => chainMgIm A₀ zf B K α s.toNNReal x) volume 0 t := by
  rw [ae_all_iff]
  intro α
  filter_upwards [ae_vs_integrable μ (measurable_chainTestT_ring hzC (B α) (K α) α)
      (contDiff_chainTestT_ring hA₀ hzC hzim (B α) (K α) α),
    ae_vs_integrable μ (measurable_chainTestT_ring hzC (B α) (-Complex.I • K α) α)
      (contDiff_chainTestT_ring hA₀ hzC hzim (B α) (-Complex.I • K α) α)] with x h1 h2 t
  exact ⟨h1 t, h2 t⟩

include hA₀ hzC hzim in
/-- **`combMg` by integration by parts.** For `C²` coefficients `c_α : ℝ → ℂ`, a.s., for
every `t`: `combMg A₀ zf B K c t = ∑_α (c_α(t) 𝓜^α_t - ∫_0^t c_α'(s) 𝓜^α_s ds)`. -/
theorem combMg_eq_ibp (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    (B : ι → Fin k → RingMat p) (K : ι → RingMat p) (c : ι → ℝ → ℂ)
    (hc : ∀ α, ContDiff ℝ 2 (c α)) :
    ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ t : ℝ≥0,
      combMg A₀ zf B K c t x = ∑ α, (c α t * chainMg A₀ zf B K α t x -
        ∫ s in (0 : ℝ)..t, deriv (c α) s * chainMg A₀ zf B K α s.toNNReal x) := by
  have hcc : ∀ ab, ContDiff ℝ 2 (combCoef c ab) := fun
    | (α, false) => Complex.reCLM.contDiff.comp (hc α)
    | (α, true) => Complex.imCLM.contDiff.comp (hc α)
  have hTR : ∀ ab, ContDiff ℝ 2 (combTestRe A₀ zf B K ab) := fun
    | (α, false) => contDiff_chainTestT_ring hA₀ hzC hzim (B α) (K α) α
    | (α, true) => contDiff_chainTestT_ring hA₀ hzC hzim (B α) (Complex.I • K α) α
  have hTRm : ∀ ab, Measurable (combTestRe A₀ zf B K ab) := fun
    | (α, false) => measurable_chainTestT_ring hzC (B α) (K α) α
    | (α, true) => measurable_chainTestT_ring hzC (B α) (Complex.I • K α) α
  have hTI : ∀ ab, ContDiff ℝ 2 (combTestIm A₀ zf B K ab) := fun
    | (α, false) => contDiff_chainTestT_ring hA₀ hzC hzim (B α) (-Complex.I • K α) α
    | (α, true) => contDiff_chainTestT_ring hA₀ hzC hzim (B α) (K α) α
  have hTIm : ∀ ab, Measurable (combTestIm A₀ zf B K ab) := fun
    | (α, false) => measurable_chainTestT_ring hzC (B α) (-Complex.I • K α) α
    | (α, true) => measurable_chainTestT_ring hzC (B α) (K α) α
  have hd : ∀ α s, DifferentiableAt ℝ (c α) s := fun α s =>
    (hc α).differentiable (by norm_num) s
  filter_upwards [smCompensated_linComb_vs μ hcc hTRm hTR, smCompensated_linComb_vs μ hcc hTIm hTI,
    intervalIntegrable_chainMg hA₀ hzC hzim μ B K] with x hRe hIm hint t
  -- identify the four martingale parts per index
  have eRf : ∀ α (r : ℝ≥0), smCompensated (testProc (combTestRe A₀ zf B K (α, false)) (vsNoise p))
      (testDrift (combTestRe A₀ zf B K (α, false)) (vsNoise p) (diagonal (ringVariance p))) 0
        r x = chainMgRe A₀ zf B K α r x := fun _ _ => rfl
  have eRt : ∀ α (r : ℝ≥0), smCompensated (testProc (combTestRe A₀ zf B K (α, true)) (vsNoise p))
      (testDrift (combTestRe A₀ zf B K (α, true)) (vsNoise p) (diagonal (ringVariance p))) 0
        r x = -chainMgIm A₀ zf B K α r x := fun α r => by
    have e : combTestRe A₀ zf B K (α, true) =
        fun q => -chainTestT A₀ (ringMatrixFin p) (zf α) (B α) (-Complex.I • K α) q :=
      chainTestT_I_smul A₀ (zf α) (B α) (K α)
    rw [e, smCompensated_testProc_neg]
    rfl
  have eIf : ∀ α (r : ℝ≥0), smCompensated (testProc (combTestIm A₀ zf B K (α, false)) (vsNoise p))
      (testDrift (combTestIm A₀ zf B K (α, false)) (vsNoise p) (diagonal (ringVariance p))) 0
        r x = chainMgIm A₀ zf B K α r x := fun _ _ => rfl
  have eIt : ∀ α (r : ℝ≥0), smCompensated (testProc (combTestIm A₀ zf B K (α, true)) (vsNoise p))
      (testDrift (combTestIm A₀ zf B K (α, true)) (vsNoise p) (diagonal (ringVariance p))) 0
        r x = chainMgRe A₀ zf B K α r x := fun _ _ => rfl
  have dRe : ∀ α, deriv (fun r => (c α r).re) = fun s => (deriv (c α) s).re := fun α =>
    funext fun s => deriv_re_comp (hd α s)
  have dIm : ∀ α, deriv (fun r => (c α r).im) = fun s => (deriv (c α) s).im := fun α =>
    funext fun s => deriv_im_comp (hd α s)
  have hR := hRe t
  have hI := hIm t
  rw [Fintype.sum_prod_type] at hR hI
  simp only [Fintype.sum_bool, eRf, eRt, eIf, eIt, combCoef] at hR hI
  simp only [dRe, dIm] at hR hI
  -- the complex integral, split into four real integrals
  set Rf : ι → ℝ → ℝ := fun α s => chainMgRe A₀ zf B K α s.toNNReal x with hRf
  set If : ι → ℝ → ℝ := fun α s => chainMgIm A₀ zf B K α s.toNNReal x with hIf
  have hdc : ∀ α, Continuous (deriv (c α)) := fun α => (hc α).continuous_deriv (by norm_num)
  have iRr : ∀ α, IntervalIntegrable (fun s => (deriv (c α) s).re * Rf α s) volume 0 t :=
    fun α => (hint α t).1.continuousOn_mul (Complex.continuous_re.comp (hdc α)).continuousOn
  have iIr : ∀ α, IntervalIntegrable (fun s => (deriv (c α) s).im * If α s) volume 0 t :=
    fun α => (hint α t).2.continuousOn_mul (Complex.continuous_im.comp (hdc α)).continuousOn
  have iRi : ∀ α, IntervalIntegrable (fun s => (deriv (c α) s).im * Rf α s) volume 0 t :=
    fun α => (hint α t).1.continuousOn_mul (Complex.continuous_im.comp (hdc α)).continuousOn
  have iIi : ∀ α, IntervalIntegrable (fun s => (deriv (c α) s).re * If α s) volume 0 t :=
    fun α => (hint α t).2.continuousOn_mul (Complex.continuous_re.comp (hdc α)).continuousOn
  have hsplit : ∀ α, ∫ s in (0 : ℝ)..t, deriv (c α) s * chainMg A₀ zf B K α s.toNNReal x =
      (((∫ s in (0 : ℝ)..t, (deriv (c α) s).re * Rf α s) -
          ∫ s in (0 : ℝ)..t, (deriv (c α) s).im * If α s : ℝ) : ℂ) +
        (((∫ s in (0 : ℝ)..t, (deriv (c α) s).re * If α s) +
          ∫ s in (0 : ℝ)..t, (deriv (c α) s).im * Rf α s : ℝ) : ℂ) * Complex.I := by
    intro α
    have e : (fun s => deriv (c α) s * chainMg A₀ zf B K α s.toNNReal x) = fun s =>
        (((deriv (c α) s).re * Rf α s - (deriv (c α) s).im * If α s : ℝ) : ℂ) +
          (((deriv (c α) s).re * If α s + (deriv (c α) s).im * Rf α s : ℝ) : ℂ) *
            Complex.I := by
      funext s
      apply Complex.ext
      · simp [chainMg, hRf, hIf, Complex.mul_re]
      · simp [chainMg, hRf, hIf, Complex.mul_im]
    rw [e, intervalIntegral_ofReal_add_mul_I ((iRr α).sub (iIr α)) ((iIi α).add (iRi α)),
      intervalIntegral.integral_sub (iRr α) (iIr α),
      intervalIntegral.integral_add (iIi α) (iRi α)]
  have hneg : ∀ α, ∫ s in (0 : ℝ)..t, (deriv (c α) s).im * -If α s =
      -∫ s in (0 : ℝ)..t, (deriv (c α) s).im * If α s := fun α => by
    simp only [mul_neg, intervalIntegral.integral_neg]
  rw [Finset.sum_congr rfl fun α _ => by rw [hneg α]] at hR
  simp only [combMg, hR, hI, hsplit]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.re_sum, Complex.sub_re, chainMg, Complex.add_im, Complex.mul_im]
    simp only [mul_zero, mul_one, sub_zero, add_zero, sub_neg_eq_add]
    simp only [hRf, hIf]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  · simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.im_sum, Complex.sub_im, chainMg, Complex.add_re, Complex.mul_re]
    simp only [mul_zero, mul_one, sub_zero, add_zero, zero_add]
    simp only [hRf, hIf]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring

end BlockBand.Native.ErdosRiabov.VS
