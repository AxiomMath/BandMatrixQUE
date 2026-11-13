module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Tools
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Adapted
public import BlockBand.Internal.Contracts.Transmission
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Martingale times a progressive Lebesgue integral

Setting: probability space `(Ω, Q)`, raw filtration `𝓖`. `N` is a `𝓖`-martingale, locally
bounded in time (`|N_u| ≤ C_T` a.s. for each `u ≤ T`); `β` is a bounded strongly progressive
process; `Ñ` is a strongly progressive process with `β_u Ñ_u = β_u N_u` a.s. for each `u`
(a progressive substitute for `N` where `β ≠ 0`, needed because `N` itself need not be jointly
measurable).

`hasMartingaleModification_mul_integral`: the process
`N_t ∫_0^t β_u du - ∫_0^t β_u Ñ_u du` has a `𝓖`-martingale modification (the classical
"`M A - ∫ M dA`" identity for an absolutely continuous `A`, proved by Fubini and the
martingale property at each time `u`).
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m₀}

/-- A progressive process, held constant after `T`, is jointly measurable on `ℝ × Ω`. -/
theorem stronglyMeasurable_prod_of_progressive {f : ℝ≥0 → Ω → ℝ}
    (hf : IsStronglyProgressive 𝓖 f) (T : ℝ≥0) :
    StronglyMeasurable fun p : ℝ × Ω => f (min p.1.toNNReal T) p.2 := by
  set c : ℝ → Set.Iic T := fun s => ⟨min s.toNNReal T, min_le_right _ _⟩
  have hc : Measurable c := (measurable_real_toNNReal.min measurable_const).subtype_mk
  have hg : Measurable[_, Subtype.instMeasurableSpace.prod (𝓖 T)]
      fun p : ℝ × Ω => (c p.1, p.2) :=
    (hc.comp measurable_fst).prodMk (measurable_snd.mono le_rfl (𝓖.le T))
  exact (hf T).comp_measurable hg

omit m₀ in
theorem abs_setIntegral_le_mul {g : ℝ → ℝ} {C : ℝ} (hg : ∀ u, |g u| ≤ C) (s t : ℝ) (hst : s ≤ t) :
    |∫ u in Ioc s t, g u| ≤ C * (t - s) := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc s t) (f := g)
    measure_Ioc_lt_top (fun u _ => by rw [Real.norm_eq_abs]; exact hg u)
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hst)]

variable {Q : Measure Ω} [IsProbabilityMeasure Q]

/-- The product integrand `g(ω) β_u(ω) Ñ_u(ω)` (held constant after `T`) is integrable on
`(s, t] × Ω`, for bounded measurable `g`. -/
theorem integrable_prod_mul {β Ñ N : ℝ≥0 → Ω → ℝ} (hβ : IsStronglyProgressive 𝓖 β)
    (hÑ : IsStronglyProgressive 𝓖 Ñ) {C : ℝ} (hβC : ∀ u ω, |β u ω| ≤ C)
    (hN : ∀ u, Integrable (N u) Q) {T : ℝ≥0} {C' : ℝ} (hNb : ∀ u ≤ T, ∀ᵐ ω ∂Q, |N u ω| ≤ C')
    (hÑN : ∀ u, (fun ω => β u ω * Ñ u ω) =ᵐ[Q] fun ω => β u ω * N u ω)
    {g : Ω → ℝ} (hg : StronglyMeasurable g) (hg1 : ∀ ω, |g ω| ≤ 1) (s t : ℝ) :
    Integrable (fun p : ℝ × Ω => g p.2 * (β (min p.1.toNNReal T) p.2 * Ñ (min p.1.toNNReal T) p.2))
      ((volume.restrict (Ioc s t)).prod Q) := by
  have hF : StronglyMeasurable fun p : ℝ × Ω =>
      g p.2 * (β (min p.1.toNNReal T) p.2 * Ñ (min p.1.toNNReal T) p.2) :=
    (hg.comp_measurable measurable_snd).mul ((stronglyMeasurable_prod_of_progressive hβ T).mul
      (stronglyMeasurable_prod_of_progressive hÑ T))
  rw [integrable_prod_iff hF.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun u => ?_, ?_⟩
  · have hi : Integrable (fun ω => g ω * (β (min u.toNNReal T) ω * N (min u.toNNReal T) ω)) Q := by
      refine ((hN _).bdd_mul (c := C) ((hβ.stronglyAdapted _).mono (𝓖.le _)).aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hβC _ _)).bdd_mul (c := 1)
        (hg.aestronglyMeasurable) (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hg1 ω)
    refine hi.congr ?_
    filter_upwards [hÑN (min u.toNNReal T)] with ω hω
    simp only [hω]
  · have hm : AEStronglyMeasurable (fun u : ℝ => ∫ ω, ‖g ω * (β (min u.toNNReal T) ω *
        Ñ (min u.toNNReal T) ω)‖ ∂Q) (volume.restrict (Ioc s t)) :=
      hF.aestronglyMeasurable.norm.integral_prod_right'
    refine Integrable.of_bound hm (C * C') (ae_of_all _ fun u => ?_)
    have hle : ∫ ω, ‖g ω * (β (min u.toNNReal T) ω * Ñ (min u.toNNReal T) ω)‖ ∂Q ≤ C * C' := by
      have hb : ∀ᵐ ω ∂Q, ‖g ω * (β (min u.toNNReal T) ω * Ñ (min u.toNNReal T) ω)‖ ≤ C * C' := by
        filter_upwards [hÑN (min u.toNNReal T), hNb _ (min_le_right _ _)] with ω h1 h2
        rw [h1, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |g ω| * (|β (min u.toNNReal T) ω| * |N (min u.toNNReal T) ω|)
            ≤ 1 * (C * C') :=
              mul_le_mul (hg1 ω) (mul_le_mul (hβC _ _) h2 (abs_nonneg _)
                ((abs_nonneg (β (min u.toNNReal T) ω)).trans (hβC _ ω))) (by positivity)
                zero_le_one
          _ = C * C' := one_mul _
      have := integral_mono_of_nonneg (ae_of_all _ fun ω => norm_nonneg _)
        (integrable_const (C * C')) hb
      simpa using this
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hle

/-- On `(0, T]`, freezing after `T` does nothing. -/
theorem min_toNNReal_eq {T : ℝ≥0} {u s : ℝ} (hu : u ∈ Ioc s (T : ℝ)) :
    min u.toNNReal T = u.toNNReal :=
  min_eq_left (by rw [Real.toNNReal_le_iff_le_coe]; exact hu.2)

omit [IsProbabilityMeasure Q] in
/-- Pathwise: a section of a progressive process is integrable on `(s, t]` when bounded. -/
theorem integrableOn_section {β : ℝ≥0 → Ω → ℝ} (hβ : IsStronglyProgressive 𝓖 β) {C : ℝ}
    (hβC : ∀ u ω, |β u ω| ≤ C) (ω : Ω) {s : ℝ} {t : ℝ≥0} :
    IntegrableOn (fun u : ℝ => β u.toNNReal ω) (Ioc s t) := by
  have hm : StronglyMeasurable fun u : ℝ => β (min u.toNNReal t) ω :=
    (stronglyMeasurable_prod_of_progressive hβ t).comp_measurable
      (measurable_id.prodMk measurable_const)
  have hi : IntegrableOn (fun u : ℝ => β (min u.toNNReal t) ω) (Ioc s t) :=
    Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne hm.aestronglyMeasurable
      (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact hβC _ _)
  refine hi.congr_fun (fun u hu => ?_) measurableSet_Ioc
  simp only [min_toNNReal_eq hu]

/-- **Martingale times a progressive integral.** For a `𝓖`-martingale `N` (locally bounded
in time), a bounded strongly progressive `β` and a strongly progressive `Ñ` with
`β_u Ñ_u = β_u N_u` a.s. for every `u`, the process `N_t ∫_0^t β - ∫_0^t β Ñ` has a
`𝓖`-martingale modification. -/
theorem hasMartingaleModification_mul_integral {N : ℝ≥0 → Ω → ℝ} (hN : Martingale N 𝓖 Q)
    (hNb : ∀ T, ∃ C', ∀ u ≤ T, ∀ᵐ ω ∂Q, |N u ω| ≤ C')
    {β Ñ : ℝ≥0 → Ω → ℝ} (hβ : IsStronglyProgressive 𝓖 β) {C : ℝ} (hβC : ∀ u ω, |β u ω| ≤ C)
    (hÑ : IsStronglyProgressive 𝓖 Ñ)
    (hÑN : ∀ u, (fun ω => β u ω * Ñ u ω) =ᵐ[Q] fun ω => β u ω * N u ω) :
    HasMartingaleModification Q 𝓖 (fun t ω => N t ω * (∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω) -
      ∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω * Ñ u.toNNReal ω) := by
  set B : ℝ≥0 → Ω → ℝ := fun t ω => ∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω with hBdef
  set I : ℝ≥0 → Ω → ℝ := fun t ω => ∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω * Ñ u.toNNReal ω
    with hIdef
  have hβÑ : IsStronglyProgressive 𝓖 fun t ω => β t ω * Ñ t ω := hβ.mul hÑ
  have mB : ∀ t, StronglyMeasurable[𝓖 t] (B t) := fun t =>
    stronglyMeasurable_integral_of_progressive hβ t
  have mI : ∀ t, StronglyMeasurable[𝓖 t] (I t) := fun t =>
    stronglyMeasurable_integral_of_progressive hβÑ t
  have bB : ∀ (s t : ℝ≥0), s ≤ t → ∀ ω, |∫ u in Ioc (s : ℝ) t, β u.toNNReal ω| ≤ C * (t - s) :=
    fun s t hst ω => abs_setIntegral_le_mul (fun u => hβC _ _) _ _ (NNReal.coe_le_coe.2 hst)
  have bB0 : ∀ t ω, |B t ω| ≤ C * t := fun t ω => by
    simpa using bB 0 t zero_le ω
  -- the product integrand held constant after `T`, and its integrability
  set F : ℝ≥0 → ℝ × Ω → ℝ := fun T p => β (min p.1.toNNReal T) p.2 * Ñ (min p.1.toNNReal T) p.2
  have hFint : ∀ (T : ℝ≥0) (s t : ℝ) {g : Ω → ℝ}, StronglyMeasurable g → (∀ ω, |g ω| ≤ 1) →
      Integrable (fun p : ℝ × Ω => g p.2 * F T p) ((volume.restrict (Ioc s t)).prod Q) := by
    intro T s t g hg hg1
    obtain ⟨C', hC'⟩ := hNb T
    exact integrable_prod_mul hβ hÑ hβC hN.integrable hC' hÑN hg hg1 s t
  have one_le : ∀ ω : Ω, |(fun _ : Ω => (1 : ℝ)) ω| ≤ 1 := fun _ => by simp
  -- integrals of the stopped integrand over `(s, t]` are the true ones
  have hIst : ∀ (s t : ℝ≥0) ω, ∫ u in Ioc (s : ℝ) t, F t (u, ω) =
      ∫ u in Ioc (s : ℝ) t, β u.toNNReal ω * Ñ u.toNNReal ω := fun s t ω =>
    setIntegral_congr_fun measurableSet_Ioc fun u hu => by
      simp only [F, min_toNNReal_eq hu]
  have iI : ∀ t, Integrable (I t) Q := fun t => by
    have := (hFint t 0 t stronglyMeasurable_const one_le).integral_prod_right
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp only [one_mul]
    exact_mod_cast hIst 0 t ω
  have iNB : ∀ t, Integrable (fun ω => N t ω * B t ω) Q := fun t =>
    (hN.integrable t).mul_bdd (c := C * t) ((mB t).mono (𝓖.le t)).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact bB0 t ω)
  -- a.e. additivity of the pathwise integrals
  have addB : ∀ (s t : ℝ≥0), s ≤ t → ∀ ω,
      B t ω = B s ω + ∫ u in Ioc (s : ℝ) t, β u.toNNReal ω := fun s t hst ω => by
    simp only [hBdef]
    rw [← Ioc_union_Ioc_eq_Ioc (NNReal.coe_nonneg s) (NNReal.coe_le_coe.2 hst),
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (integrableOn_section hβ hβC ω) (integrableOn_section hβ hβC ω)]
  have addI : ∀ (s t : ℝ≥0), s ≤ t → ∀ᵐ ω ∂Q,
      I t ω = I s ω + ∫ u in Ioc (s : ℝ) t, β u.toNNReal ω * Ñ u.toNNReal ω := by
    intro s t hst
    have h1 := (hFint t 0 t stronglyMeasurable_const one_le).prod_left_ae
    filter_upwards [h1] with ω hω
    have hint : IntegrableOn (fun u : ℝ => β u.toNNReal ω * Ñ u.toNNReal ω) (Ioc 0 t) := by
      have hω' : IntegrableOn (fun u : ℝ => F t (u, ω)) (Ioc 0 t) :=
        hω.congr (ae_of_all _ fun u => by simp)
      refine hω'.congr_fun (fun u hu => ?_) measurableSet_Ioc
      simp only [F, min_toNNReal_eq hu]
    simp only [hIdef]
    rw [← Ioc_union_Ioc_eq_Ioc (NNReal.coe_nonneg s) (NNReal.coe_le_coe.2 hst)] at hint ⊢
    rw [setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hint.mono_set subset_union_left) (hint.mono_set subset_union_right)]
  have hgoal : (fun t ω => N t ω * (∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω) -
      ∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω * Ñ u.toNNReal ω) =
      fun t ω => N t ω * B t ω - I t ω := by simp only [hBdef, hIdef]
  rw [hgoal]
  refine exists_martingale_modification (fun t => (iNB t).sub (iI t))
    (fun t => (((hN.1 t).mul (mB t)).sub (mI t)).aestronglyMeasurable) ?_
  intro s t hst A hA
  have hAm : MeasurableSet A := 𝓖.le s A hA
  set ι : Ω → ℝ := A.indicator fun _ => (1 : ℝ) with hι
  have mιs : StronglyMeasurable[𝓖 s] ι := stronglyMeasurable_const.indicator hA
  have mι : StronglyMeasurable ι := mιs.mono (𝓖.le s)
  have bι : ∀ ω, |ι ω| ≤ 1 := fun ω => by by_cases h : ω ∈ A <;> simp [ι, h]
  have setI : ∀ f : Ω → ℝ, ∫ ω in A, f ω ∂Q = ∫ ω, ι ω * f ω ∂Q := fun f => by
    rw [← integral_indicator hAm]
    congr 1; funext ω; by_cases h : ω ∈ A <;> simp [ι, h]
  -- the three pieces
  set ΔB : Ω → ℝ := fun ω => ∫ u in Ioc (s : ℝ) t, β u.toNNReal ω
  set ΔI : Ω → ℝ := fun ω => ∫ u in Ioc (s : ℝ) t, β u.toNNReal ω * Ñ u.toNNReal ω
  have e1 : ∫ ω, ι ω * B s ω * (N t ω - N s ω) ∂Q = 0 :=
    martingale_integral_mul_sub_eq_zero hN hst (mιs.mul (mB s)).aestronglyMeasurable
      (C := C * s) (ae_of_all _ fun ω => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |ι ω| * |B s ω| ≤ 1 * (C * s) :=
              mul_le_mul (bι ω) (bB0 s ω) (abs_nonneg _) zero_le_one
          _ = C * s := one_mul _)
  -- Fubini, first swap: `E[ι N_t ΔB] = ∫_s^t E[ι N_t β_u] du`
  set G : ℝ × Ω → ℝ := fun p => ι p.2 * N t p.2 * β (min p.1.toNNReal t) p.2
  have hGm : StronglyMeasurable G :=
    ((mι.comp_measurable measurable_snd).mul (((hN.1 t).mono (𝓖.le t)).comp_measurable
      measurable_snd)).mul (stronglyMeasurable_prod_of_progressive hβ t)
  have hGi : Integrable G ((volume.restrict (Ioc (s : ℝ) t)).prod Q) := by
    have hdom : Integrable (fun p : ℝ × Ω => C * |N t p.2|)
        ((volume.restrict (Ioc (s : ℝ) t)).prod Q) := by
      have := (integrable_const (μ := volume.restrict (Ioc (s : ℝ) t)) C).mul_prod
        (hN.integrable t).abs
      simpa using this
    refine hdom.mono' hGm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |ι p.2| * |N t p.2| * |β (min p.1.toNNReal t) p.2| ≤ 1 * |N t p.2| * C := by
          gcongr
          · exact bι _
          · exact hβC _ _
      _ = C * |N t p.2| := by ring
  have e2 : ∫ ω, ι ω * N t ω * ΔB ω ∂Q =
      ∫ ω, ι ω * ΔI ω ∂Q := by
    have s1 : ∫ ω, ι ω * N t ω * ΔB ω ∂Q =
        ∫ ω, ∫ u in Ioc (s : ℝ) t, G (u, ω) ∂volume ∂Q := by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only [G, ΔB]
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      simp only [min_toNNReal_eq hu]
    have s2 : ∫ ω, ∫ u in Ioc (s : ℝ) t, G (u, ω) ∂volume ∂Q =
        ∫ u in Ioc (s : ℝ) t, ∫ ω, G (u, ω) ∂Q := by
      have := integral_integral_swap (μ := volume.restrict (Ioc (s : ℝ) t)) (ν := Q)
        (f := fun u ω => G (u, ω)) hGi
      exact this.symm
    have s3 : ∫ u in Ioc (s : ℝ) t, ∫ ω, G (u, ω) ∂Q =
        ∫ u in Ioc (s : ℝ) t, ∫ ω, ι ω * F t (u, ω) ∂Q := by
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      simp only [G, F, min_toNNReal_eq hu]
      have hsu : s ≤ u.toNNReal := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ((NNReal.coe_nonneg s).trans hu.1.le)]
        exact hu.1.le
      have hut : u.toNNReal ≤ t := by rw [Real.toNNReal_le_iff_le_coe]; exact hu.2
      have hg : AEStronglyMeasurable[𝓖 u.toNNReal] (fun ω => ι ω * β u.toNNReal ω) Q :=
        ((mιs.mono (𝓖.mono hsu)).mul (hβ.stronglyAdapted _)).aestronglyMeasurable
      have hz := martingale_integral_mul_sub_eq_zero hN hut hg (C := C) (ae_of_all _ fun ω => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |ι ω| * |β u.toNNReal ω| ≤ 1 * C :=
              mul_le_mul (bι ω) (hβC _ _) (abs_nonneg _) zero_le_one
          _ = C := one_mul _)
      have hi1 : Integrable (fun ω => ι ω * β u.toNNReal ω * N t ω) Q :=
        (hN.integrable t).bdd_mul (c := C) (hg.mono (𝓖.le _)) (ae_of_all _ fun ω => by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          calc |ι ω| * |β u.toNNReal ω| ≤ 1 * C :=
                mul_le_mul (bι ω) (hβC _ _) (abs_nonneg _) zero_le_one
            _ = C := one_mul _)
      have hi2 : Integrable (fun ω => ι ω * β u.toNNReal ω * N u.toNNReal ω) Q :=
        (hN.integrable _).bdd_mul (c := C) (hg.mono (𝓖.le _)) (ae_of_all _ fun ω => by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          calc |ι ω| * |β u.toNNReal ω| ≤ 1 * C :=
                mul_le_mul (bι ω) (hβC _ _) (abs_nonneg _) zero_le_one
            _ = C := one_mul _)
      have h1 : ∫ ω, ι ω * β u.toNNReal ω * N t ω ∂Q =
          ∫ ω, ι ω * β u.toNNReal ω * N u.toNNReal ω ∂Q := by
        have h := hz
        simp only [mul_sub] at h
        rw [integral_sub hi1 hi2] at h
        linarith
      calc ∫ ω, ι ω * N t ω * β u.toNNReal ω ∂Q = ∫ ω, ι ω * β u.toNNReal ω * N t ω ∂Q := by
            congr 1; funext ω; ring
        _ = ∫ ω, ι ω * β u.toNNReal ω * N u.toNNReal ω ∂Q := h1
        _ = _ := integral_congr_ae (by
            filter_upwards [hÑN u.toNNReal] with ω hω
            rw [mul_assoc, ← hω])
    have s4 : ∫ u in Ioc (s : ℝ) t, ∫ ω, ι ω * F t (u, ω) ∂Q =
        ∫ ω, ∫ u in Ioc (s : ℝ) t, ι ω * F t (u, ω) ∂volume ∂Q :=
      integral_integral_swap (μ := volume.restrict (Ioc (s : ℝ) t)) (ν := Q)
        (f := fun u ω => ι ω * F t (u, ω)) (hFint t s t mι bι)
    have s5 : ∫ ω, ∫ u in Ioc (s : ℝ) t, ι ω * F t (u, ω) ∂volume ∂Q =
        ∫ ω, ι ω * ΔI ω ∂Q := by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only [ΔI]
      rw [integral_const_mul, hIst s t ω]
    rw [s1, s2, s3, s4, s5]
  rw [setI, setI]
  have bι' : ∀ᵐ ω ∂Q, ‖ι ω‖ ≤ 1 := ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact bι ω
  have hiKs : Integrable (fun ω => ι ω * (N s ω * B s ω - I s ω)) Q :=
    ((iNB s).sub (iI s)).bdd_mul mι.aestronglyMeasurable bι'
  have mΔB : StronglyMeasurable ΔB := by
    have e : ΔB = fun ω => B t ω - B s ω := funext fun ω => by
      simp only [ΔB]; rw [addB s t hst ω]; ring
    rw [e]; exact ((mB t).mono (𝓖.le t)).sub ((mB s).mono (𝓖.le s))
  have hi1 : Integrable (fun ω => ι ω * B s ω * (N t ω - N s ω)) Q :=
    ((hN.integrable t).sub (hN.integrable s)).bdd_mul (c := C * s)
      (mι.mul ((mB s).mono (𝓖.le s))).aestronglyMeasurable (ae_of_all _ fun ω => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |ι ω| * |B s ω| ≤ 1 * (C * s) :=
              mul_le_mul (bι ω) (bB0 s ω) (abs_nonneg _) zero_le_one
          _ = C * s := one_mul _)
  have hi2 : Integrable (fun ω => ι ω * N t ω * ΔB ω) Q := by
    have := ((hN.integrable t).mul_bdd (c := C * (t - s)) mΔB.aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact bB s t hst ω)).bdd_mul
      mι.aestronglyMeasurable bι'
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp only; ring
  have hi3 : Integrable (fun ω => ι ω * ΔI ω) Q := by
    have hΔ : Integrable ΔI Q := ((iI t).sub (iI s)).congr (by
      filter_upwards [addI s t hst] with ω hω
      simp only [Pi.sub_apply, hω, ΔI]; ring)
    exact hΔ.bdd_mul mι.aestronglyMeasurable bι'
  have hpt : (fun ω => ι ω * (N t ω * B t ω - I t ω)) =ᵐ[Q] fun ω =>
      ι ω * (N s ω * B s ω - I s ω) +
        (ι ω * B s ω * (N t ω - N s ω) + (ι ω * N t ω * ΔB ω - ι ω * ΔI ω)) := by
    filter_upwards [addI s t hst] with ω hω
    rw [addB s t hst ω, hω]
    simp only [ΔB, ΔI]; ring
  have hi23 : Integrable (fun ω => ι ω * N t ω * ΔB ω - ι ω * ΔI ω) Q := hi2.sub hi3
  have hi123 : Integrable (fun ω => ι ω * B s ω * (N t ω - N s ω) +
      (ι ω * N t ω * ΔB ω - ι ω * ΔI ω)) Q := hi1.add hi23
  rw [integral_congr_ae hpt, integral_add hiKs hi123, integral_add hi1 hi23,
    integral_sub hi2 hi3, e1, e2]
  ring

end BlockBand.Diffusion
