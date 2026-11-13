module

public import BlockBand.Native.ErdosRiabov.VS.TailBridgeProp

set_option autoImplicit false

/-!
# Uniform-in-time forms of `combMg_eq_ibp` and a.s. continuity of `chainMg`

Versions of the integration-by-parts identities with the null set chosen uniformly in the
coefficients and the time, and the almost sure continuity of the single-chain martingales.

* `smCompensated_linComb_vs_uniform`: `∀ᵐ x, ∀ c, (∀ α, c_α ∈ C²) → ∀ t, …` (the identity of
  `smCompensated_linComb_vs` with the quantifiers over `c` and `t` inside the a.s.).
* **`combMg_eq_ibp_uniform`**: `∀ᵐ x, ∀ c, (∀ α, c_α ∈ C²) → ∀ t, combMg … c t x =
  ∑_α (c_α(t) 𝓜^α_t - ∫_0^t c_α'(s) 𝓜^α_s ds)`.
* **`combMg_vsPropagator_uniform`**: `∀ᵐ x, ∀ t ≤ 1, ∀ u, combMg … (P̂_{·,t}(u, ·)) t x =
  vsPropNoise … t u x`.
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
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.CEH.Flow
open scoped NNReal

/-!
### Continuity of martingale parts along continuous paths
-/

section Path

variable {Ω : Type*} {d : ℕ}

/-- On a continuous path with locally integrable drift, `t ↦ M_t` is continuous on `ℝ≥0`. -/
theorem continuous_smCompensated_path (Y : ℝ≥0 → Ω → Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) {ω : Ω} (hY : Continuous fun t => Y t ω)
    {φ : ℝ × (Fin d → ℝ) → ℝ} (hφ : Continuous φ)
    (hβ : ∀ T : ℝ≥0, IntegrableOn (fun s : ℝ => itoDrift φ (Y s.toNNReal ω) s.toNNReal 0 A)
      (Ioc 0 T)) :
    Continuous fun t : ℝ≥0 => smCompensated (testProc φ Y) (testDrift φ Y A) 0 t ω := by
  set f : ℝ → ℝ := fun s => φ ((s.toNNReal : ℝ), Y s.toNNReal ω) with hf
  set b : ℝ → ℝ := fun s => itoDrift φ (Y s.toNNReal ω) s.toNNReal 0 A with hb
  set g : ℝ → ℝ := fun s => f s - f 0 - ∫ r in (0 : ℝ)..s, b r with hg
  have hfc : Continuous f :=
    hφ.comp ((NNReal.continuous_coe.comp continuous_real_toNNReal).prodMk
      (hY.comp continuous_real_toNNReal))
  have hgT : ∀ T : ℝ≥0, ContinuousOn g (Icc 0 T) := fun T => by
    have hbI : IntegrableOn b (uIcc 0 T) volume := by
      rw [uIcc_of_le (NNReal.coe_nonneg T), integrableOn_Icc_iff_integrableOn_Ioc]
      exact hβ T
    have h : ContinuousOn g (uIcc 0 T) :=
      (hfc.continuousOn.sub continuousOn_const).sub
        (intervalIntegral.continuousOn_primitive_interval hbI)
    rwa [uIcc_of_le (NNReal.coe_nonneg T)] at h
  have hgI : ContinuousOn g (Ici 0) := fun s hs => by
    have hs0 : (0 : ℝ) ≤ s := hs
    have h := hgT (s + 1).toNNReal s ⟨hs0, by
      rw [Real.coe_toNNReal _ (by linarith)]
      linarith⟩
    refine h.mono_of_mem_nhdsWithin ?_
    have e : Icc (0 : ℝ) ((s + 1).toNNReal : ℝ) = Ici 0 ∩ Iic ((s + 1).toNNReal : ℝ) := by
      ext r
      simp
    rw [e]
    refine inter_mem_nhdsWithin _ (Iic_mem_nhds ?_)
    rw [Real.coe_toNNReal _ (by linarith)]
    linarith
  have hcomp : Continuous (g ∘ fun t : ℝ≥0 => (t : ℝ)) :=
    hgI.comp_continuous NNReal.continuous_coe fun t => t.2
  refine hcomp.congr fun t => ?_
  simp only [Function.comp_apply, hg, hf, hb, smCompensated, testProc, testDrift,
    Real.toNNReal_coe, Real.toNNReal_zero, NNReal.coe_zero]
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]

end Path

variable {p : BlockBand.Parameters} {ι : Type*} [Fintype ι]

/-- **Uniform form of `smCompensated_linComb_vs`**: the null set depends only on the `φ_α`. -/
theorem smCompensated_linComb_vs_uniform (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    {φ : ι → ℝ × (Fin (ringDim p) → ℝ) → ℝ} (hφm : ∀ α, Measurable (φ α))
    (hφ : ∀ α, ContDiff ℝ 2 (φ α)) :
    ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ c : ι → ℝ → ℝ, (∀ α, ContDiff ℝ 2 (c α)) →
      ∀ t : ℝ≥0,
      smCompensated (testProc (linComb c φ) (vsNoise p))
          (testDrift (linComb c φ) (vsNoise p) (diagonal (ringVariance p))) 0 t x =
        ∑ α, (c α t * smCompensated (testProc (φ α) (vsNoise p))
            (testDrift (φ α) (vsNoise p) (diagonal (ringVariance p))) 0 t x -
          ∫ s in (0 : ℝ)..t, deriv (c α) s * smCompensated (testProc (φ α) (vsNoise p))
            (testDrift (φ α) (vsNoise p) (diagonal (ringVariance p))) 0 s.toNNReal x) := by
  have hall : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ α, ∀ t : ℝ≥0,
      IntegrableOn (fun s : ℝ => itoDrift (φ α) (vsNoise p s.toNNReal x) s.toNNReal 0
        (diagonal (ringVariance p))) (Ioc 0 t) := by
    rw [ae_all_iff]
    intro α
    have H := vsNoise_itoFormula μ isOpen_univ (ae_of_all _ fun _ _ => Set.mem_univ _) (hφm α)
      (hφ α).contDiffOn
    filter_upwards [H.integrable] with x hx t
    exact (hx t).1 0
  filter_upwards [hall] with x hx c hc t
  exact smCompensated_linComb_path (vsNoise p) _ (continuous_vsNoise p x) hc hφ t
    fun α => hx α t

section Chains

variable {k : ℕ} {A₀ : RingMat p} (hA₀ : A₀.IsHermitian) {zf : ι → Fin k → ℝ → ℂ}
  (hzC : ∀ α j, ContDiff ℝ 2 (zf α j)) (hzim : ∀ α j t, (zf α j t).im ≠ 0)

include hA₀ hzC hzim in
/-- **A.s. continuity of the single-chain martingales**: a.s., for every `α`,
`t ↦ 𝓜^α_t` is continuous on `ℝ≥0`. -/
theorem continuous_chainMg (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    (B : ι → Fin k → RingMat p) (K : ι → RingMat p) :
    ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ α,
      Continuous fun t : ℝ≥0 => chainMg A₀ zf B K α t x := by
  rw [ae_all_iff]
  intro α
  have H₁ := vsNoise_itoFormula μ isOpen_univ (ae_of_all _ fun _ _ => Set.mem_univ _)
    (measurable_chainTestT_ring hzC (B α) (K α) α)
    (contDiff_chainTestT_ring hA₀ hzC hzim (B α) (K α) α).contDiffOn
  have H₂ := vsNoise_itoFormula μ isOpen_univ (ae_of_all _ fun _ _ => Set.mem_univ _)
    (measurable_chainTestT_ring hzC (B α) (-Complex.I • K α) α)
    (contDiff_chainTestT_ring hA₀ hzC hzim (B α) (-Complex.I • K α) α).contDiffOn
  filter_upwards [H₁.integrable, H₂.integrable] with x h1 h2
  have c1 := continuous_smCompensated_path (vsNoise p) (diagonal (ringVariance p))
    (continuous_vsNoise p x) (contDiff_chainTestT_ring hA₀ hzC hzim (B α) (K α) α).continuous
    fun T => (h1 T).1 0
  have c2 := continuous_smCompensated_path (vsNoise p) (diagonal (ringVariance p))
    (continuous_vsNoise p x)
    (contDiff_chainTestT_ring hA₀ hzC hzim (B α) (-Complex.I • K α) α).continuous
    fun T => (h2 T).1 0
  exact (Complex.continuous_ofReal.comp c1).add
    ((Complex.continuous_ofReal.comp c2).mul continuous_const)

include hA₀ hzC hzim in
/-- **Uniform `combMg_eq_ibp`**: a.s., simultaneously for all `C²`
coefficients `c` and all times `t`,
`combMg A₀ zf B K c t = ∑_α (c_α(t) 𝓜^α_t - ∫_0^t c_α'(s) 𝓜^α_s ds)`. -/
theorem combMg_eq_ibp_uniform (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    (B : ι → Fin k → RingMat p) (K : ι → RingMat p) :
    ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ c : ι → ℝ → ℂ, (∀ α, ContDiff ℝ 2 (c α)) →
      ∀ t : ℝ≥0, combMg A₀ zf B K c t x = ∑ α, (c α t * chainMg A₀ zf B K α t x -
        ∫ s in (0 : ℝ)..t, deriv (c α) s * chainMg A₀ zf B K α s.toNNReal x) := by
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
  filter_upwards [smCompensated_linComb_vs_uniform μ hTRm hTR,
    smCompensated_linComb_vs_uniform μ hTIm hTI,
    intervalIntegrable_chainMg hA₀ hzC hzim μ B K] with x hRe0 hIm0 hint c hc t
  have hcc : ∀ ab, ContDiff ℝ 2 (combCoef c ab) := fun
    | (α, false) => Complex.reCLM.contDiff.comp (hc α)
    | (α, true) => Complex.imCLM.contDiff.comp (hc α)
  have hd : ∀ α s, DifferentiableAt ℝ (c α) s := fun α s =>
    (hc α).differentiable (by norm_num) s
  have hRe := hRe0 (combCoef c) hcc
  have hIm := hIm0 (combCoef c) hcc
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

end Chains

/-- **Uniform Duhamel-noise identification**: a.s., for every `t ≤ 1` and
every `u`, `combMg A₀ zf B K (P̂_{·,t}(u, ·)) t = vsPropNoise … t u`. -/
theorem combMg_vsPropagator_uniform {k N : ℕ} {S : Matrix (Fin N) (Fin N) ℝ}
    (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] {A₀ : RingMat p}
    (hA₀ : A₀.IsHermitian) {zf : Fin N → Fin k → ℝ → ℂ}
    (hzC : ∀ α j, ContDiff ℝ 2 (zf α j)) (hzim : ∀ α j t, (zf α j t).im ≠ 0)
    (B : Fin N → Fin k → RingMat p) (K : Fin N → RingMat p) (hS : StochasticSymm S)
    {μ₁ μ₂ : ℂ} (h₁ : ‖μ₁‖ < 1) (h₂ : ‖μ₂‖ < 1) :
    ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ u : Fin N,
      combMg A₀ zf B K (fun α s => vsPropagator S μ₁ μ₂ s t u α) t x =
        vsPropNoise S μ₁ μ₂ A₀ zf B K t u x := by
  filter_upwards [combMg_eq_ibp_uniform hA₀ hzC hzim μ B K] with x hx t ht u
  have ht0 : (0 : ℝ) ≤ t := t.2
  rw [hx _ (fun α => contDiff_vsPropagator_left μ₁ μ₂ t u α) t, vsPropNoise]
  have hself : vsPropagator S μ₁ μ₂ t t = 1 :=
    vsPropagator_self hS (norm_smul_lt_one h₁ h₂ ht0 ht)
  simp only [hself, sub_eq_add_neg]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ α, (1 : Matrix (Fin N) (Fin N) ℂ) u α * chainMg A₀ zf B K α t x =
      chainMg A₀ zf B K u t x := by
    simp [Matrix.one_apply]
  rw [h1]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht0] at hs
  rw [deriv_vsPropagator_left hS h₁ h₂ hs.1 (hs.2.trans ht) ht0 ht u α]
  ring

end BlockBand.Native.ErdosRiabov.VS
