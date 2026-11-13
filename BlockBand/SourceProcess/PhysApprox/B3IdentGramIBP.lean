module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramKGen

/-!
# Integration by parts for tested increments

Abstract measure theory. Measure: a finite measure `Q`; filtration: the raw natural filtration
`pastFiltration obs`.

* `integral_cmul_eq_zero_of_tested`: tested increments integrate to `0` against a complex test
  `g`, `pastSigma obs a`-measurable and a.s. bounded (real and imaginary parts of a clipped `g`).
* **`isTestedMart_ibp`**: if `X` has tested increments (strongly measurable, continuous for every
  `ω`, a.s. bounded on every `[0, t]`) and `β` is adapted, jointly measurable and a.s. bounded,
  with `B_t = ∫_0^t β` past-measurable, then `D_t = ∫_0^t β_r X_r dr − B_t X_t` has tested
  increments: `D_t − D_s = ∫_s^t β_r (X_r − X_t) dr − B_s (X_t − X_s)`, each term vanishing by
  the tested identity (Fubini for the first).

This is the step `X_e X_{e'} − ∫ cov = (Ŷ_e Ŷ_{e'} − ∫ (b_e Ŷ_{e'} + Ŷ_e b_{e'} + cov)) + D + D'`
that removes the drift integral `A` from the bracket generator.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.ClosedLimit
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {I : Type*} {Q : Measure Ω}
  {obs : I → ℝ≥0 → Ω → ℂ} {X : ℝ≥0 → Ω → ℂ}

/-- **Tested increments against bounded past-measurable complex tests.** -/
theorem integral_cmul_eq_zero_of_tested [IsFiniteMeasure Q]
    (hobs : ∀ i u, Measurable (obs i u)) (hX : IsTestedMart Q obs X) {a b : ℝ≥0} (hab : a ≤ b)
    {g : Ω → ℂ} (hg : StronglyMeasurable[pastSigma obs a] g) {C : ℝ}
    (hC : ∀ᵐ ω ∂Q, ‖g ω‖ ≤ C) : ∫ ω, g ω * (X b ω - X a ω) ∂Q = 0 := by
  set g' : Ω → ℂ := fun ω => if ‖g ω‖ ≤ C then g ω else 0 with hg'_def
  have hg' : StronglyMeasurable[pastSigma obs a] g' := by
    let _ : MeasurableSpace Ω := pastSigma obs a
    exact StronglyMeasurable.ite (measurableSet_le hg.norm.measurable measurable_const) hg
      stronglyMeasurable_const
  have hC' : ∀ ω, ‖g' ω‖ ≤ max C 0 := fun ω => by
    by_cases h : ‖g ω‖ ≤ C
    · simp only [hg'_def, h, ↓reduceIte]; exact h.trans (le_max_left _ _)
    · simp only [hg'_def, h, ↓reduceIte, norm_zero]; exact le_max_right _ _
  have hae : (fun ω => g ω * (X b ω - X a ω)) =ᵐ[Q] fun ω => g' ω * (X b ω - X a ω) :=
    hC.mono fun ω h => by simp only [hg'_def, h, ↓reduceIte]
  rw [integral_congr_ae hae]
  have hle : pastSigma obs a ≤ mΩ := (pastFiltration obs hobs).le a
  have hre : StronglyMeasurable[pastSigma obs a] fun ω => (g' ω).re :=
    Complex.continuous_re.comp_stronglyMeasurable hg'
  have him : StronglyMeasurable[pastSigma obs a] fun ω => (g' ω).im :=
    Complex.continuous_im.comp_stronglyMeasurable hg'
  have hbre : ∀ ω, ‖(g' ω).re‖ ≤ max C 0 := fun ω => by
    rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hC' ω)
  have hbim : ∀ ω, ‖(g' ω).im‖ ≤ max C 0 := fun ω => by
    rw [Real.norm_eq_abs]; exact (Complex.abs_im_le_norm _).trans (hC' ω)
  have h1 := integral_smul_eq_zero_of_tested hobs hX hab hre hbre
  have h2 := integral_smul_eq_zero_of_tested hobs hX hab him hbim
  have hint : Integrable (fun ω => X b ω - X a ω) Q := (hX.1 b).sub (hX.1 a)
  have hi1 : Integrable (fun ω => (g' ω).re • (X b ω - X a ω)) Q :=
    hint.bdd_smul (max C 0) (hre.mono hle).aestronglyMeasurable (Eventually.of_forall hbre)
  have hi2 : Integrable (fun ω => (g' ω).im • (X b ω - X a ω)) Q :=
    hint.bdd_smul (max C 0) (him.mono hle).aestronglyMeasurable (Eventually.of_forall hbim)
  have e : (fun ω => g' ω * (X b ω - X a ω)) = fun ω =>
      (g' ω).re • (X b ω - X a ω) + Complex.I * ((g' ω).im • (X b ω - X a ω)) := by
    funext ω
    simp only [Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im (g' ω)]
    ring
  rw [e, integral_add hi1 (hi2.const_mul _), integral_const_mul, h1, h2]
  simp

/-- **Integration by parts against a tested process.** -/
theorem isTestedMart_ibp [IsFiniteMeasure Q] (hobs : ∀ i u, Measurable (obs i u))
    (hX : IsTestedMart Q obs X) (hXm : ∀ t, StronglyMeasurable (X t))
    (hXc : ∀ ω, Continuous fun t => X t ω)
    (hXb : ∀ t, ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ v ≤ t, ‖X v ω‖ ≤ C) {β : ℝ≥0 → Ω → ℂ}
    (hβp : ∀ r, StronglyMeasurable[pastSigma obs r] (β r))
    (hβB : ∀ t, StronglyMeasurable[pastSigma obs t] fun ω => ∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω)
    (hβj : StronglyMeasurable fun p : ℝ × Ω => β p.1.toNNReal p.2)
    (hβb : ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ r, ‖β r ω‖ ≤ C) :
    IsTestedMart Q obs (fun t ω => (∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω * X u.toNNReal ω) -
      (∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω) * X t ω) := by
  obtain ⟨Cβ, hCβ⟩ := hβb
  have hXj : StronglyMeasurable fun p : ℝ × Ω => X p.1.toNNReal p.2 :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun (r : ℝ) ω => X r.toNNReal ω)
      (fun ω => (hXc ω).comp continuous_real_toNNReal)
      (fun r => (hXm _).measurable)).stronglyMeasurable
  have hInt : ∀ (F : ℝ × Ω → ℂ), StronglyMeasurable F → ∀ t : ℝ≥0,
      StronglyMeasurable fun ω => ∫ u in Ioc (0 : ℝ) t, F (u, ω) := fun F hF t =>
    (hF.comp_measurable measurable_swap).integral_prod_right'
  have hB : ∀ t : ℝ≥0, ∀ᵐ ω ∂Q, ‖∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω‖ ≤ Cβ * t := fun t =>
    hCβ.mono fun ω hω => by
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) t)
        (f := fun u => β u.toNNReal ω) (C := Cβ) measure_Ioc_lt_top fun u _ => hω _
      rwa [Real.volume_real_Ioc, sub_zero, max_eq_left (NNReal.coe_nonneg t)] at h
  have hBX : ∀ t : ℝ≥0, ∃ C : ℝ, ∀ᵐ ω ∂Q,
      ‖∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω * X u.toNNReal ω‖ ≤ C := fun t => by
    obtain ⟨CX, hCX⟩ := hXb t
    refine ⟨Cβ * CX * t, (hCβ.and hCX).mono fun ω hω => ?_⟩
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) t)
      (f := fun u => β u.toNNReal ω * X u.toNNReal ω) (C := Cβ * CX) measure_Ioc_lt_top
      fun u hu => by
        rw [norm_mul]
        exact mul_le_mul (hω.1 _) (hω.2 _ (Real.toNNReal_le_iff_le_coe.2 hu.2)) (norm_nonneg _)
          ((norm_nonneg _).trans (hω.1 0))
    rwa [Real.volume_real_Ioc, sub_zero, max_eq_left (NNReal.coe_nonneg t)] at h
  obtain ⟨D, hD⟩ : ∃ D : ℝ≥0 → Ω → ℂ, D = fun (t : ℝ≥0) ω =>
      (∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω * X u.toNNReal ω) -
        (∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω) * X t ω := ⟨_, rfl⟩
  rw [← hD]
  have hDint : ∀ t, Integrable (D t) Q := fun t => by
    obtain ⟨C1, h1⟩ := hBX t
    obtain ⟨CX, hCX⟩ := hXb t
    have hm : AEStronglyMeasurable (D t) Q := by
      rw [hD]
      refine AEStronglyMeasurable.congr ((hInt
          (fun p : ℝ × Ω => β p.1.toNNReal p.2 * X p.1.toNNReal p.2) (hβj.mul hXj) t).sub
          ((hInt (fun p : ℝ × Ω => β p.1.toNNReal p.2) hβj t).mul (hXm t))).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      simp
    refine Integrable.of_bound hm (C1 + Cβ * t * CX)
      ((h1.and ((hB t).and hCX)).mono fun ω hω => ?_)
    simp only [hD]
    refine (norm_sub_le _ _).trans (add_le_add hω.1 ?_)
    rw [norm_mul]
    exact mul_le_mul hω.2.1 (hω.2.2 t le_rfl) (norm_nonneg _)
      ((norm_nonneg _).trans hω.2.1)
  refine ⟨hDint, fun s t hst m i u hu φ => ?_⟩
  set ψ : Ω → ℝ := fun ω => φ (fun l => obs (i l) (u l) ω) with hψ
  have hψm : ∀ k : ℝ≥0, s ≤ k → StronglyMeasurable[pastSigma obs k] ψ := fun k hk => by
    let _ : MeasurableSpace Ω := pastSigma obs k
    exact (φ.continuous.measurable.comp
      (measurable_cyl obs i u fun l => (hu l).trans hk)).stronglyMeasurable
  have hψb : ∀ ω, ‖ψ ω‖ ≤ ‖φ‖ := fun ω => φ.norm_coe_le_norm _
  have hψa : StronglyMeasurable ψ := (hψm s le_rfl).mono ((pastFiltration obs hobs).le s)
  -- the decomposition, on the set where `β` is bounded
  have hdec : ∀ᵐ ω ∂Q, D t ω - D s ω =
      (∫ r in Ioc (s : ℝ) t, β r.toNNReal ω * (X r.toNNReal ω - X t ω)) -
        (∫ u in Ioc (0 : ℝ) s, β u.toNNReal ω) * (X t ω - X s ω) := by
    filter_upwards [hCβ] with ω hω
    have hfi : ∀ (f : ℝ → ℂ), AEStronglyMeasurable f volume → (∀ T : ℝ, ∃ C, ∀ r, r ≤ T →
        ‖f r‖ ≤ C) → ∀ a c : ℝ, IntervalIntegrable f volume a c := fun f hf hb a c => by
      obtain ⟨C, hC⟩ := hb (max a c)
      refine (intervalIntegrable_iff).2 (Measure.integrableOn_of_bounded (M := C)
        (lt_of_le_of_lt (measure_mono Set.uIoc_subset_uIcc) isCompact_uIcc.measure_lt_top).ne
        hf ?_)
      exact (ae_restrict_mem measurableSet_uIoc).mono fun r hr => hC r hr.2
    have hXbd : ∀ T : ℝ, ∃ C, ∀ r : ℝ, r ≤ T → ‖X r.toNNReal ω‖ ≤ C := fun T => by
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T.toNNReal))
        |>.exists_bound_of_continuousOn (hXc ω).continuousOn
      exact ⟨C, fun r hr => hC _ ⟨zero_le, Real.toNNReal_le_toNNReal hr⟩⟩
    have hβm : AEStronglyMeasurable (fun r : ℝ => β r.toNNReal ω) volume :=
      (hβj.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    have hXm' : AEStronglyMeasurable (fun r : ℝ => X r.toNNReal ω) volume :=
      ((hXc ω).comp continuous_real_toNNReal).aestronglyMeasurable
    have hi1 : ∀ a c : ℝ, IntervalIntegrable (fun r => β r.toNNReal ω * X r.toNNReal ω)
        volume a c := hfi _ (hβm.mul hXm') fun T => by
      obtain ⟨C, hC⟩ := hXbd T
      exact ⟨Cβ * C, fun r hr => by
        rw [norm_mul]
        exact mul_le_mul (hω _) (hC r hr) (norm_nonneg _) ((norm_nonneg _).trans (hω 0))⟩
    have hi2 : ∀ a c : ℝ, IntervalIntegrable (fun r => β r.toNNReal ω) volume a c :=
      hfi _ hβm fun T => ⟨Cβ, fun r _ => hω _⟩
    have e1 : ∀ (f : ℝ → ℂ) (x : ℝ≥0), ∫ r in Ioc (0 : ℝ) x, f r = ∫ r in (0 : ℝ)..x, f r :=
      fun f x => (intervalIntegral.integral_of_le x.2).symm
    have e2 : ∀ (f : ℝ → ℂ), ∫ r in Ioc (s : ℝ) t, f r = ∫ r in (s : ℝ)..t, f r :=
      fun f => (intervalIntegral.integral_of_le (NNReal.coe_le_coe.2 hst)).symm
    simp only [hD, e1, e2]
    have h1 := intervalIntegral.integral_add_adjacent_intervals (hi1 0 s) (hi1 s t)
    have h2 := intervalIntegral.integral_add_adjacent_intervals (hi2 0 s) (hi2 s t)
    beta_reduce at h1 h2
    have e3 : ∫ r in (s : ℝ)..t, β r.toNNReal ω * (X r.toNNReal ω - X t ω) =
        (∫ r in (s : ℝ)..t, β r.toNNReal ω * X r.toNNReal ω) -
          (∫ r in (s : ℝ)..t, β r.toNNReal ω) * X t ω := by
      simp only [mul_sub]
      rw [intervalIntegral.integral_sub (hi1 s t) ((hi2 s t).mul_const _),
        intervalIntegral.integral_mul_const]
    rw [e3]
    linear_combination (-1 : ℂ) * h1 + X t ω * h2
  -- the second term vanishes
  have hsecond : ∫ ω, ψ ω • ((∫ u in Ioc (0 : ℝ) s, β u.toNNReal ω) * (X t ω - X s ω)) ∂Q = 0 := by
    have h := integral_cmul_eq_zero_of_tested hobs hX hst
      (g := fun ω => (ψ ω : ℂ) * ∫ u in Ioc (0 : ℝ) s, β u.toNNReal ω)
      ((Complex.continuous_ofReal.comp_stronglyMeasurable (hψm s le_rfl)).mul (hβB s))
      (C := ‖φ‖ * (Cβ * s)) ((hB s).mono fun ω hω => by
        rw [norm_mul, Complex.norm_real]
        exact mul_le_mul (hψb ω) hω (norm_nonneg _) (norm_nonneg _))
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [Complex.real_smul]
    ring
  -- the first term vanishes (Fubini)
  have hfirst : ∫ ω, ψ ω • (∫ r in Ioc (s : ℝ) t, β r.toNNReal ω * (X r.toNNReal ω - X t ω)) ∂Q =
      0 := by
    obtain ⟨CX, hCX⟩ := hXb t
    have hν : IsFiniteMeasure (volume.restrict (Ioc (s : ℝ) t)) :=
      isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    set F : Ω → ℝ → ℂ := fun ω r => (ψ ω : ℂ) * (β r.toNNReal ω * (X r.toNNReal ω - X t ω))
    have hFm : StronglyMeasurable (Function.uncurry F) := by
      have h1 : StronglyMeasurable fun p : Ω × ℝ => β p.2.toNNReal p.1 :=
        hβj.comp_measurable measurable_swap
      have h2 : StronglyMeasurable fun p : Ω × ℝ => X p.2.toNNReal p.1 :=
        hXj.comp_measurable measurable_swap
      have h3 : StronglyMeasurable fun p : Ω × ℝ => X t p.1 :=
        (hXm t).comp_measurable measurable_fst
      have h4 : StronglyMeasurable fun p : Ω × ℝ => (ψ p.1 : ℂ) :=
        (Complex.continuous_ofReal.comp_stronglyMeasurable hψa).comp_measurable measurable_fst
      exact h4.mul (h1.mul (h2.sub h3))
    have hFb : ∀ᵐ p ∂(Q.prod (volume.restrict (Ioc (s : ℝ) t))),
        ‖Function.uncurry F p‖ ≤ ‖φ‖ * (Cβ * (CX + CX)) := by
      have hb : ∀ᵐ ω ∂Q, ∀ r ∈ Ioc (s : ℝ) t, ‖F ω r‖ ≤ ‖φ‖ * (Cβ * (CX + CX)) :=
        (hCβ.and hCX).mono fun ω hω r hr => by
          simp only [F, norm_mul, Complex.norm_real]
          refine mul_le_mul (hψb ω) (mul_le_mul (hω.1 _) ((norm_sub_le _ _).trans
            (add_le_add (hω.2 _ (Real.toNNReal_le_iff_le_coe.2 hr.2)) (hω.2 _ le_rfl)))
            (norm_nonneg _) ((norm_nonneg _).trans (hω.1 0))) (by positivity) (norm_nonneg _)
      have hr : ∀ᵐ p ∂(Q.prod (volume.restrict (Ioc (s : ℝ) t))), p.2 ∈ Ioc (s : ℝ) t :=
        Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd)
          (ae_restrict_mem measurableSet_Ioc)
      filter_upwards [Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst) hb,
        hr] with p h1 h2
      exact h1 p.2 h2
    have hFi : Integrable (Function.uncurry F) (Q.prod (volume.restrict (Ioc (s : ℝ) t))) :=
      Integrable.of_bound hFm.aestronglyMeasurable _ hFb
    have hswap := integral_integral_swap hFi
    have e : ∀ ω, ψ ω • (∫ r in Ioc (s : ℝ) t, β r.toNNReal ω * (X r.toNNReal ω - X t ω)) =
        ∫ r, F ω r ∂(volume.restrict (Ioc (s : ℝ) t)) := fun ω => by
      rw [Complex.real_smul, ← integral_const_mul]
    simp only [e]
    rw [hswap]
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hrs : s ≤ r.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ((NNReal.coe_nonneg s).trans hr.1.le)]
      exact hr.1.le
    have hrt : r.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hr.2
    have h := integral_cmul_eq_zero_of_tested hobs hX hrt
      (g := fun ω => (ψ ω : ℂ) * β r.toNNReal ω)
      ((Complex.continuous_ofReal.comp_stronglyMeasurable (hψm _ hrs)).mul (hβp _))
      (C := ‖φ‖ * Cβ) (hCβ.mono fun ω hω => by
        rw [norm_mul, Complex.norm_real]
        exact mul_le_mul (hψb ω) (hω _) (norm_nonneg _) (norm_nonneg _))
    rw [show (0 : ℂ) = -0 by simp, ← h, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [F]
    ring
  rw [integral_congr_ae (hdec.mono fun ω hω => by rw [hω])]
  have hi1 : Integrable (fun ω => ψ ω •
      (∫ r in Ioc (s : ℝ) t, β r.toNNReal ω * (X r.toNNReal ω - X t ω))) Q := by
    have hInt' : Integrable (fun ω => ∫ r in Ioc (s : ℝ) t,
        β r.toNNReal ω * (X r.toNNReal ω - X t ω)) Q := by
      have h1 := hDint t
      have h2 := hDint s
      have h3 : Integrable (fun ω => (∫ u in Ioc (0 : ℝ) s, β u.toNNReal ω) *
          (X t ω - X s ω)) Q := by
        obtain ⟨CX, hCX⟩ := hXb t
        refine Integrable.of_bound (((hInt _ hβj s).mul ((hXm t).sub (hXm s))).aestronglyMeasurable)
          (Cβ * s * (CX + CX)) (((hB s).and hCX).mono fun ω hω => ?_)
        rw [norm_mul]
        exact mul_le_mul hω.1 ((norm_sub_le _ _).trans (add_le_add (hω.2 t le_rfl)
          (hω.2 s hst))) (norm_nonneg _) ((norm_nonneg _).trans hω.1)
      refine ((h1.sub h2).add h3).congr (hdec.mono fun ω hω => ?_)
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [hω]; ring
    exact hInt'.bdd_smul ‖φ‖ hψa.aestronglyMeasurable (Eventually.of_forall hψb)
  have hi2 : Integrable (fun ω => ψ ω •
      ((∫ u in Ioc (0 : ℝ) s, β u.toNNReal ω) * (X t ω - X s ω))) Q := by
    obtain ⟨CX, hCX⟩ := hXb t
    refine Integrable.bdd_smul ?_ ‖φ‖ hψa.aestronglyMeasurable (Eventually.of_forall hψb)
    refine Integrable.of_bound (((hInt _ hβj s).mul ((hXm t).sub (hXm s))).aestronglyMeasurable)
      (Cβ * s * (CX + CX)) (((hB s).and hCX).mono fun ω hω => ?_)
    rw [norm_mul]
    exact mul_le_mul hω.1 ((norm_sub_le _ _).trans (add_le_add (hω.2 t le_rfl)
      (hω.2 s hst))) (norm_nonneg _) ((norm_nonneg _).trans hω.1)
  simp only [smul_sub]
  rw [integral_sub hi1 hi2, hfirst, hsecond, sub_zero]

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram
