module

public import BlockBand.Critical.Herglotz.RealConstant

/-!
# The real-constant step: `FarPartSmall` from the hypotheses of the Herglotz tail lemma

`HerglotzTailHypotheses.farPartSmall`: under the hypotheses of the Herglotz tail lemma and for a
decorated sine process `Ξ`, the far part `v^* (F_N - near_{N,n})(iY) v` is small in probability for
large `Y`, large windows `n` and large `N` (`FarPartSmall`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Metric Set Complex
open scoped Matrix NNReal ENNReal ComplexOrder ComplexConjugate

namespace BlockBand.Critical.Herglotz

open scoped JV
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)

variable {r : ℕ}

section Hyp

variable {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)}
  [∀ N, IsProbabilityMeasure (P N)] {F : ∀ N, Ω N → AtomicHerglotz r} {Ω' : Type*}
  [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))}

/-- **Law of the near quadratic form at `iY`** (the near-part law at `K = {iY}`, no real points). -/
theorem HerglotzTailHypotheses.tendstoInDistribution_quad_nearPart
    (h : HerglotzTailHypotheses r P F P' Ξ) (hΞ : IsDecoratedSineProcess r P' Ξ) {Y : ℝ}
    (hY : 0 < Y) (n : ℕ) (v : Fin r → ℂ) :
    TendstoInDistribution (fun N ω => quad (nearPart (atomMeasure (F N ω)) n ((Y : ℂ) * I)) v)
      atTop (fun ω => quad (nearPart (canonMeasure (Ξ ω)) n ((Y : ℂ) * I)) v) P P' := by
  set K : Set ℂ := {(Y : ℂ) * I} with hKdef
  have hK : IsCompact K := isCompact_singleton
  have hKs : K ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz; rw [hKdef, mem_singleton_iff] at hz; rw [hz]; simpa using hY
  have hKc : ∀ z ∈ K, Y ≤ z.im := by
    intro z hz; rw [hKdef, mem_singleton_iff] at hz; rw [hz]; simp
  have hKR : ∀ z ∈ K, ‖z‖ ≤ Y := by
    intro z hz; rw [hKdef, mem_singleton_iff] at hz
    rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
  set x : Fin 0 → ℝ := fun a => a.elim0
  have T := h.tendstoInDistribution_nearPart hΞ (Nat.cast_nonneg n) x hK hKs
  set z₀ : K := ⟨(Y : ℂ) * I, rfl⟩
  have hΦ : Continuous fun p : JointValues r 0 K => quad (p.2 z₀) v :=
    (continuous_quad v).comp ((continuous_eval_const z₀).comp continuous_snd)
  have T2 := T.continuous_comp hΦ
  have hfun : ∀ ν : Measure (ℝ × Matrix (Fin r) (Fin r) ℂ),
      (fun p : JointValues r 0 K => quad (p.2 z₀) v) (jointValues (nearPart ν n) x K) =
        quad (nearPart ν n ((Y : ℂ) * I)) v := by
    intro ν
    show quad (restrictTo (nearPart ν n) K z₀) v = _
    rw [restrictTo_apply (continuousOn_nearPart ν n hY hKc hKR)]
  simp only [Function.comp_def, hfun] at T2
  exact T2

/-- `w ↦ min 1 (max 0 (2‖w - c‖/δ - 1))`: `1` on `‖w - c‖ ≥ δ`, `0` on `‖w - c‖ ≤ δ/2`. -/
def farTest (c : ℂ) {δ : ℝ} (_hδ : 0 < δ) : BoundedContinuousFunction ℂ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun w => min 1 (max 0 (2 * ‖w - c‖ / δ - 1)), by fun_prop⟩ 1 (fun a b => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_le]
      have h1 := min_le_left 1 (max 0 (2 * ‖a - c‖ / δ - 1))
      have h2 := min_le_left 1 (max 0 (2 * ‖b - c‖ / δ - 1))
      have h3 := le_min zero_le_one (le_max_left 0 (2 * ‖a - c‖ / δ - 1))
      have h4 := le_min zero_le_one (le_max_left 0 (2 * ‖b - c‖ / δ - 1))
      constructor <;> linarith)

theorem farTest_apply (c : ℂ) {δ : ℝ} (hδ : 0 < δ) (w : ℂ) :
    farTest c hδ w = min 1 (max 0 (2 * ‖w - c‖ / δ - 1)) := rfl

theorem farTest_nonneg (c : ℂ) {δ : ℝ} (hδ : 0 < δ) (w : ℂ) : 0 ≤ farTest c hδ w := by
  rw [farTest_apply]; exact le_min zero_le_one (le_max_left _ _)

theorem farTest_le_sq (c : ℂ) {δ : ℝ} (hδ : 0 < δ) (w : ℂ) :
    farTest c hδ w ≤ 4 / δ ^ 2 * ‖w - c‖ ^ 2 := by
  rw [farTest_apply]
  by_cases hw : 2 * ‖w - c‖ / δ - 1 ≤ 0
  · rw [max_eq_left hw, min_eq_right zero_le_one]; positivity
  · push Not at hw
    have h1 : 1 < 2 * ‖w - c‖ / δ := by linarith
    have h2 : 1 ≤ 4 / δ ^ 2 * ‖w - c‖ ^ 2 := by
      have : 4 / δ ^ 2 * ‖w - c‖ ^ 2 = (2 * ‖w - c‖ / δ) ^ 2 := by field_simp; ring
      rw [this]; nlinarith
    exact (min_le_left _ _).trans h2

theorem one_le_farTest (c : ℂ) {δ : ℝ} (hδ : 0 < δ) {w : ℂ} (hw : δ ≤ ‖w - c‖) :
    1 ≤ farTest c hδ w := by
  rw [farTest_apply]
  have : 1 ≤ 2 * ‖w - c‖ / δ - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hδ]; linarith
  rw [max_eq_right (by linarith), min_eq_left this]

set_option maxHeartbeats 1600000 in
/-- **The far part at `iY` is small in probability** (`C = 0` and no escaped mass, at finite
`N`). Law: hypotheses of the Herglotz tail lemma for `F_N` on `(Ω N, P N)`, `Ξ` decorated
sine. For every `v`, `ε, η > 0` there is `Y > 0` such that eventually in the window `n`,
eventually in `N`, `P_N*(|v^* (F_N - near_{N,n})(iY) v| ≥ ε) ≤ η`. -/
theorem HerglotzTailHypotheses.farPartSmall (h : HerglotzTailHypotheses r P F P' Ξ)
    (hΞ : IsDecoratedSineProcess r P' Ξ) : FarPartSmall P F := by
  intro v ε η hε hη
  set s : ℝ := (euclidSqNorm v : ℝ) with hsdef
  have hs0 : 0 ≤ s := (euclidSqNorm v).2
  set T : ℝ := 4 / ε with hTdef
  have hT : 0 < T := by positivity
  set E₀ : ℝ := Real.exp (T * s) with hE₀def
  have hE₀ : 1 ≤ E₀ := Real.one_le_exp (by positivity)
  set ε₁ : ℝ := η / 8 with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  set δ₁ : ℝ := ε₁ / (4 * E₀ * T) with hδ₁
  have hδ₁0 : 0 < δ₁ := by positivity
  set δ₂ : ℝ := ε₁ / (8 * T) with hδ₂
  have hδ₂0 : 0 < δ₂ := by positivity
  set Cv : ℝ := (∑ k, ‖v k‖) ^ 2 + 1 with hCv
  have hCv0 : 0 < Cv := by positivity
  set Q4 : ℝ := ∫ g, quadMark v g ^ 2 ∂circularVectorLaw (Fin r) with hQ4
  have hQ40 : 0 ≤ Q4 := integral_nonneg fun g => sq_nonneg _
  set is : ℂ := (s : ℂ) * I with his
  -- choice of `Y`
  obtain ⟨Y, hY, hYsmall⟩ : ∃ Y : ℝ, 0 < Y ∧
      4 / δ₁ ^ 2 * (4 * (Real.pi * Y)⁻¹ * Q4) < ε₁ / (32 * E₀) := by
    have hlim : Tendsto (fun Y : ℝ => 4 / δ₁ ^ 2 * (4 * (Real.pi * Y)⁻¹ * Q4)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun Y : ℝ => (Real.pi * Y)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atTop Real.pi_pos)
      have := ((h1.const_mul 4).mul_const Q4).const_mul (4 / δ₁ ^ 2)
      simpa using this
    obtain ⟨Y, hY1, hY2⟩ := ((hlim.eventually (gt_mem_nhds (by positivity :
      (0 : ℝ) < ε₁ / (32 * E₀)))).and (eventually_gt_atTop 0)).exists
    exact ⟨Y, hY2, hY1⟩
  refine ⟨Y, hY, ?_⟩
  set z : ℂ := (Y : ℂ) * I with hz
  have hzim : z.im = Y := by simp [hz]
  set t₀ : ℝ := min δ₂ (ε / 2) / (Cv * 8 * Y) with ht₀
  have ht₀0 : 0 < t₀ := by positivity
  -- conditions on the window `n`
  have hn1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ n ∧ 2 * Y ≤ n := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 : ℝ),
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * Y)] with n h1 h2
    exact ⟨h1, h2⟩
  have hn2 : ∀ᶠ n : ℕ in atTop,
      4 / δ₁ ^ 2 * (s ^ 2 * (1 - ∫ x, cutoffImWeight n Y x) ^ 2) < ε₁ / (32 * E₀) := by
    have hlim := (tendsto_integral_smoothCutoff_mul_poissonKernel hY).comp
      tendsto_natCast_atTop_atTop
    have hc : Tendsto (fun n : ℕ => 4 / δ₁ ^ 2 * (s ^ 2 * (1 - ∫ x, cutoffImWeight n Y x) ^ 2))
        atTop (𝓝 (4 / δ₁ ^ 2 * (s ^ 2 * (1 - 1) ^ 2))) :=
      (((tendsto_const_nhds.sub hlim).pow 2).const_mul _).const_mul _
    rw [sub_self, zero_pow two_ne_zero, mul_zero, mul_zero] at hc
    exact hc.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hn1, hn2, h.eventually_measure_tailMass_le hΞ ht₀0 (by positivity :
    (0 : ℝ) < ε₁ / 16)] with n hn1 hn2 hn3
  -- the canonical near form
  have Tq := h.tendstoInDistribution_quad_nearPart hΞ hY n v
  have hcan : ∫ ω, farTest is hδ₁0 (quad (nearPart (canonMeasure (Ξ ω)) n z) v) ∂P' ≤
      ε₁ / (16 * E₀) := by
    obtain ⟨-, hsm, hsi, hsE⟩ := smoothQuadCauchy_L2 hΞ hY (n : ℝ) v
    have hae := ae_quad_nearPart_canon hΞ (n : ℝ) (by rw [hzim]; exact hY) v
    have hs' : (∑ i, ‖v i‖ ^ 2 : ℝ) = s := rfl
    rw [hs'] at hsi hsE
    have hgi : Integrable (fun ω => farTest is hδ₁0 (quad (nearPart (canonMeasure (Ξ ω)) n z)
        v)) P' :=
      ((farTest is hδ₁0).integrable (P'.map _)).comp_aemeasurable Tq.aemeasurable_limit
    calc ∫ ω, farTest is hδ₁0 (quad (nearPart (canonMeasure (Ξ ω)) n z) v) ∂P'
        ≤ ∫ ω, 4 / δ₁ ^ 2 * ‖smoothQuadCauchy (Ξ ω) n v z - is‖ ^ 2 ∂P' := by
          refine integral_mono_ae hgi (hsi.const_mul _) ?_
          filter_upwards [hae] with ω hω
          rw [hω]
          exact farTest_le_sq is hδ₁0 _
      _ = 4 / δ₁ ^ 2 * ∫ ω, ‖smoothQuadCauchy (Ξ ω) n v z - is‖ ^ 2 ∂P' :=
          integral_const_mul _ _
      _ ≤ 4 / δ₁ ^ 2 * (4 * (Real.pi * Y)⁻¹ * Q4 + s ^ 2 * (1 - ∫ x, cutoffImWeight n Y x) ^ 2) :=
          mul_le_mul_of_nonneg_left hsE (by positivity)
      _ ≤ ε₁ / (16 * E₀) := by
          have : ε₁ / (16 * E₀) = ε₁ / (32 * E₀) + ε₁ / (32 * E₀) := by field_simp; ring
          rw [this, mul_add]
          linarith
  -- convergence of the test along `N`
  have hTq := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ Tq.forall_aemeasurable
    Tq.aemeasurable_limit).1 Tq (farTest is hδ₁0)
  have hN2 := hTq.eventually (gt_mem_nhds (lt_of_le_of_lt hcan
    (lt_add_of_pos_right _ (by positivity : (0 : ℝ) < ε₁ / (16 * E₀)))))
  -- bounded analytic means, integrated in `t`
  have hq_meas : ∀ N, Measurable fun ω => quad ((F N ω).eval z) v := by
    intro N
    have := measurable_quadForm_affine (h.measurable_eval N) v 0 0
    have hm : ∀ i j, Measurable fun ω => (F N ω).eval z i j :=
      fun i j => measurable_eval_at (h.measurable_eval N) z i j
    rw [show (fun ω => quad ((F N ω).eval z) v) = fun ω => ∑ k, ∑ l,
      conj (v k) * (F N ω).eval z k l * v l from funext fun ω => quad_eq _ v]
    exact Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ =>
      (measurable_const.mul (hm k l)).mul measurable_const
  set φq : ℕ → ℝ → ℂ := fun N t => ∫ ω, cexp (I * t * quad ((F N ω).eval z) v) ∂P N with hφq
  have hφq_meas : ∀ N, Measurable (φq N) := by
    intro N
    have hg : Measurable fun p : ℝ × Ω N => cexp (I * p.1 * quad ((F N p.2).eval z) v) :=
      Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp
        measurable_fst)).mul ((hq_meas N).comp measurable_snd))
    exact (hg.stronglyMeasurable.integral_prod_right' (ν := P N)).measurable
  have hDCT : Tendsto (fun N => ∫ t in Ioc 0 T,
      ‖((Real.exp (-(s * t)) : ℝ) : ℂ) - φq N t‖) atTop (𝓝 0) := by
    have hlim : ∀ᵐ t ∂(volume.restrict (Ioc 0 T)), Tendsto (fun N =>
        ‖((Real.exp (-(s * t)) : ℝ) : ℂ) - φq N t‖) atTop (𝓝 0) := by
      refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => ?_)
      have := h.tendsto_integral_cexp_quadForm v ht.1.le (z := z) (by rw [hzim]; exact hY)
      have h2 := (tendsto_const_nhds (x := ((Real.exp (-(s * t)) : ℝ) : ℂ))).sub this
      rw [sub_self] at h2
      simpa [AtomicHerglotz.quadForm, quad, hφq] using h2.norm
    have hbd : ∀ N, ∀ᵐ t ∂(volume.restrict (Ioc 0 T)),
        ‖‖((Real.exp (-(s * t)) : ℝ) : ℂ) - φq N t‖‖ ≤ 2 := by
      intro N
      refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => ?_)
      rw [norm_norm]
      refine (norm_sub_le _ _).trans ?_
      have h1 : ‖((Real.exp (-(s * t)) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.2 (by nlinarith [ht.1])
      have h2 : ‖φq N t‖ ≤ 1 := by
        have := norm_integral_le_of_norm_le_const (μ := P N) (C := (1 : ℝ))
          (f := fun ω => cexp (I * t * quad ((F N ω).eval z) v))
          (Eventually.of_forall fun ω => norm_cexp_I_mul_le_one ht.1.le
            (AtomicHerglotz.quadForm_im_nonneg (F N ω) v (by rw [hzim]; exact hY.le)))
        simpa using this
      linarith
    have hem : Measurable fun t : ℝ => ((Real.exp (-(s * t)) : ℝ) : ℂ) :=
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg)).measurable
    have hFm : ∀ N, AEStronglyMeasurable (fun t => ‖((Real.exp (-(s * t)) : ℝ) : ℂ) - φq N t‖)
        (volume.restrict (Ioc 0 T)) := fun N => (hem.sub (hφq_meas N)).norm.aestronglyMeasurable
    have := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc 0 T))
      (fun _ => (2 : ℝ)) hFm (integrable_const _) hbd hlim
    simpa using this
  have hTε : (0 : ℝ) < T * ε₁ / (4 * E₀) := by positivity
  filter_upwards [hn3, hN2, hDCT.eventually (ge_mem_nhds hTε)] with N hNT hNφ hNI
  -- notation at fixed `N`
  set q : Ω N → ℂ := fun ω => quad ((F N ω).eval z) v with hqdef
  set a : Ω N → ℂ := fun ω => quad (nearPart (atomMeasure (F N ω)) n z) v with hadef
  set R : Ω N → ℂ := fun ω => quad (farPart (F N ω) n z) v with hRdef
  have hRqa : ∀ ω, R ω = q ω - a ω := fun ω => quad_eval_sub _ _ _ _
  have ha_m : AEMeasurable a (P N) := Tq.forall_aemeasurable N
  have hq_m : AEMeasurable q (P N) := (hq_meas N).aemeasurable
  have hR_m : AEMeasurable R (P N) :=
    (hq_m.sub ha_m).congr (ae_of_all _ fun ω => (hRqa ω).symm)
  set X : Ω N → ℝ := fun ω => (R ω).re with hXdef
  have hX_m : AEMeasurable X (P N) := Complex.measurable_re.comp_aemeasurable hR_m
  have hXc_m : AEMeasurable (fun ω => (X ω : ℂ)) (P N) :=
    Complex.measurable_ofReal.comp_aemeasurable hX_m
  have hzim0 : 0 ≤ z.im := by rw [hzim]; exact hY.le
  have hRim : ∀ ω, 0 ≤ (R ω).im := fun ω => im_quad_farPart_nonneg _ _ hzim0 v
  have hqim : ∀ ω, 0 ≤ (q ω).im := fun ω => AtomicHerglotz.quadForm_im_nonneg _ v hzim0
  -- the imaginary part of the far part
  have hRX : ∀ ω, ‖R ω - (X ω : ℂ)‖ ≤ Cv * (8 * Y * tailMass (F N ω) n) := by
    intro ω
    have h1 : R ω - (X ω : ℂ) = ((R ω).im : ℂ) * I := by
      apply Complex.ext <;> simp [hXdef]
    rw [h1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hRim ω)]
    refine (im_quad_farPart_le (F N ω) hY hn1.1 hn1.2 v).trans ?_
    have hT0 := tailMass_nonneg (F N ω) n
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hp₂ : ∀ δ : ℝ, min δ₂ (ε / 2) ≤ δ →
      (P N {ω | δ ≤ ‖R ω - (X ω : ℂ)‖}).toReal ≤ ε₁ / 16 := by
    intro δ hδ
    have hsub : {ω | δ ≤ ‖R ω - (X ω : ℂ)‖} ⊆ {ω | t₀ ≤ tailMass (F N ω) n} := by
      intro ω hω
      simp only [mem_ofPred_eq] at hω ⊢
      have h1 := hω.trans (hRX ω)
      rw [ht₀, div_le_iff₀ (by positivity)]
      nlinarith
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) ((measure_mono hsub).trans hNT)
  -- the near quadratic form
  have hp₁ : (P N {ω | δ₁ ≤ ‖q ω - (R ω + is)‖}).toReal ≤ ε₁ / (8 * E₀) := by
    set G : Ω N → ℝ := fun ω => farTest is hδ₁0 (a ω) with hG
    have hGi : Integrable G (P N) := ((farTest is hδ₁0).integrable ((P N).map a)).comp_aemeasurable
      ha_m
    have hsub : {ω | δ₁ ≤ ‖q ω - (R ω + is)‖} ⊆ {ω | 1 ≤ G ω} := by
      intro ω hω
      simp only [mem_ofPred_eq] at hω ⊢
      have : q ω - (R ω + is) = a ω - is := by rw [hRqa]; ring
      rw [this] at hω
      exact one_le_farTest is hδ₁0 hω
    have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => farTest_nonneg is hδ₁0 _)
      hGi 1
    rw [one_mul] at hmk
    have hlt : ∫ ω, G ω ∂P N < ε₁ / (16 * E₀) + ε₁ / (16 * E₀) := lt_of_lt_of_le hNφ (by linarith)
    have h2 : (P N {ω | δ₁ ≤ ‖q ω - (R ω + is)‖}).toReal ≤ (P N).real {ω | 1 ≤ G ω} :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    have h3 : ε₁ / (16 * E₀) + ε₁ / (16 * E₀) = ε₁ / (8 * E₀) := by field_simp; ring
    linarith
  set p₁ : ℝ := (P N {ω | δ₁ ≤ ‖q ω - (R ω + is)‖}).toReal with hp₁def
  set p₂ : ℝ := (P N {ω | δ₂ ≤ ‖R ω - (X ω : ℂ)‖}).toReal with hp₂def
  have hp₂' : p₂ ≤ ε₁ / 16 := hp₂ δ₂ (min_le_left _ _)
  -- pointwise bound on the characteristic function of `X`
  have hbt : ∀ t ∈ Ioc (0 : ℝ) T, ‖1 - ∫ ω, cexp (I * t * X ω) ∂P N‖ ≤
      E₀ * (‖((Real.exp (-(s * t)) : ℝ) : ℂ) - φq N t‖ + (T * δ₁ + 2 * p₁)) +
        (T * δ₂ + 2 * p₂) := by
    intro t ht
    have ht0 := ht.1.le
    have hA := norm_integral_cexp_sub_le hR_m hXc_m hRim (fun ω => by simp) ht0 hδ₂0.le
    have hB := norm_integral_cexp_sub_le hq_m (hR_m.add_const is) hqim
      (fun ω => by simp only [Complex.add_im, his, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_zero]; linarith [hRim ω])
      ht0 hδ₁0.le
    have hshift : (∫ ω, cexp (I * t * (R ω + is)) ∂P N) =
        (∫ ω, cexp (I * t * R ω) ∂P N) * ((Real.exp (-(s * t)) : ℝ) : ℂ) := by
      rw [← integral_mul_const]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only
      rw [mul_add, Complex.exp_add, Complex.ofReal_exp]
      congr 2
      rw [his]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    set φR := ∫ ω, cexp (I * t * R ω) ∂P N
    set φX := ∫ ω, cexp (I * t * (X ω : ℂ)) ∂P N
    set e : ℝ := Real.exp (-(s * t)) with he
    have he0 : 0 < e := Real.exp_pos _
    have hee : Real.exp (s * t) * e = 1 := by rw [he, ← Real.exp_add]; simp
    have hst : Real.exp (s * t) ≤ E₀ := by
      rw [hE₀def]; exact Real.exp_le_exp.2 (by nlinarith [ht.2])
    have h1R : ‖1 - φR‖ ≤ Real.exp (s * t) * (‖(e : ℂ) - φq N t‖ + (t * δ₁ + 2 * p₁)) := by
      have : (1 : ℂ) - φR = ((Real.exp (s * t) : ℝ) : ℂ) * ((e : ℂ) - φR * (e : ℂ)) := by
        have hc : ((Real.exp (s * t) : ℝ) : ℂ) * (e : ℂ) = 1 := by exact_mod_cast hee
        linear_combination (1 - φR) * hc.symm
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      rw [← hshift]
      refine (norm_sub_le_norm_sub_add_norm_sub _ (φq N t) _).trans (add_le_add le_rfl ?_)
      exact hB
    calc ‖1 - φX‖ ≤ ‖1 - φR‖ + ‖φR - φX‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ Real.exp (s * t) * (‖(e : ℂ) - φq N t‖ + (t * δ₁ + 2 * p₁)) + (t * δ₂ + 2 * p₂) :=
          add_le_add h1R hA
      _ ≤ E₀ * (‖(e : ℂ) - φq N t‖ + (T * δ₁ + 2 * p₁)) + (T * δ₂ + 2 * p₂) := by
          have hp10 : 0 ≤ p₁ := ENNReal.toReal_nonneg
          have htT := ht.2
          have k1 : ‖(e : ℂ) - φq N t‖ + (t * δ₁ + 2 * p₁) ≤
              ‖(e : ℂ) - φq N t‖ + (T * δ₁ + 2 * p₁) := by
            have := mul_le_mul_of_nonneg_right htT hδ₁0.le
            linarith
          have k2 : 0 ≤ ‖(e : ℂ) - φq N t‖ + (t * δ₁ + 2 * p₁) := by
            have := norm_nonneg ((e : ℂ) - φq N t)
            have := mul_nonneg ht0 hδ₁0.le
            linarith
          have k3 := mul_le_mul hst k1 k2 (by linarith)
          have k4 := mul_le_mul_of_nonneg_right htT hδ₂0.le
          linarith
  -- integrability and integral of the bound
  have hem : Measurable fun t : ℝ => ((Real.exp (-(s * t)) : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul continuous_id).neg)).measurable
  have hfi : Integrable (fun t => ‖((Real.exp (-(s * t)) : ℝ) : ℂ) - φq N t‖)
      (volume.restrict (Ioc 0 T)) := by
    refine Integrable.mono' (integrable_const (2 : ℝ))
      (hem.sub (hφq_meas N)).norm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => ?_)
    rw [norm_norm]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖((Real.exp (-(s * t)) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (by nlinarith [ht.1])
    have h2 : ‖φq N t‖ ≤ 1 := by
      have := norm_integral_le_of_norm_le_const (μ := P N) (C := (1 : ℝ))
        (f := fun ω => cexp (I * t * quad ((F N ω).eval z) v))
        (Eventually.of_forall fun ω => norm_cexp_I_mul_le_one ht.1.le (hqim ω))
      simpa using this
    linarith
  set b : ℝ → ℝ := fun t => E₀ * (‖((Real.exp (-(s * t)) : ℝ) : ℂ) - φq N t‖ +
    (T * δ₁ + 2 * p₁)) + (T * δ₂ + 2 * p₂) with hbdef
  have hc1 : Integrable (fun t : ℝ => ‖((Real.exp (-(s * t)) : ℝ) : ℂ) - φq N t‖ +
      (T * δ₁ + 2 * p₁)) (volume.restrict (Ioc 0 T)) :=
    hfi.add (integrable_const (T * δ₁ + 2 * p₁))
  have hc2 : Integrable (fun t : ℝ => E₀ * (‖((Real.exp (-(s * t)) : ℝ) : ℂ) - φq N t‖ +
      (T * δ₁ + 2 * p₁))) (volume.restrict (Ioc 0 T)) := hc1.const_mul E₀
  have hbi : Integrable b (volume.restrict (Ioc 0 T)) :=
    hc2.add (integrable_const (T * δ₂ + 2 * p₂))
  have hvol : (volume.restrict (Ioc (0 : ℝ) T)).real univ = T := by
    rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  have hbint : ∫ t in Ioc 0 T, b t ≤ T * ε₁ := by
    rw [hbdef, integral_add hc2 (integrable_const _), integral_const_mul,
      integral_add hfi (integrable_const _), integral_const, integral_const,
      smul_eq_mul, smul_eq_mul, hvol]
    have hp10 : 0 ≤ p₁ := ENNReal.toReal_nonneg
    have h1 : E₀ * (T * δ₁) = ε₁ / 4 := by rw [hδ₁]; field_simp
    have h2 : T * δ₂ = ε₁ / 8 := by rw [hδ₂]; field_simp
    have h3 : E₀ * (2 * p₁) ≤ ε₁ / 4 := by
      have := mul_le_mul_of_nonneg_left hp₁ (by linarith : (0 : ℝ) ≤ 2 * E₀)
      have h4 : 2 * E₀ * (ε₁ / (8 * E₀)) = ε₁ / 4 := by field_simp; ring
      nlinarith
    have h5 : E₀ * ∫ t in Ioc 0 T, ‖((Real.exp (-(s * t)) : ℝ) : ℂ) - φq N t‖ ≤ T * ε₁ / 4 := by
      have := mul_le_mul_of_nonneg_left hNI (by linarith : (0 : ℝ) ≤ E₀)
      have h6 : E₀ * (T * ε₁ / (4 * E₀)) = T * ε₁ / 4 := by field_simp
      linarith
    have e1 : E₀ * (T * (T * δ₁ + 2 * p₁)) ≤ T * (ε₁ / 2) := by
      rw [show E₀ * (T * (T * δ₁ + 2 * p₁)) = T * (E₀ * (T * δ₁) + E₀ * (2 * p₁)) by ring]
      exact mul_le_mul_of_nonneg_left (by linarith) hT.le
    have e2 : T * (T * δ₂ + 2 * p₂) ≤ T * (ε₁ / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) hT.le
    calc E₀ * ((∫ t in Ioc 0 T, ‖((Real.exp (-(s * t)) : ℝ) : ℂ) - φq N t‖) +
          T * (T * δ₁ + 2 * p₁)) + T * (T * δ₂ + 2 * p₂)
        = E₀ * (∫ t in Ioc 0 T, ‖((Real.exp (-(s * t)) : ℝ) : ℂ) - φq N t‖) +
          E₀ * (T * (T * δ₁ + 2 * p₁)) + T * (T * δ₂ + 2 * p₂) := by ring
      _ ≤ T * ε₁ := by linarith
  -- the integrated criterion for `X`
  have hD8 : (P N).real {ω | 2 / T ≤ |X ω|} ≤ 2 * ε₁ := by
    set X' := hX_m.mk X
    have hXX : X =ᵐ[P N] X' := hX_m.ae_eq_mk
    have hset : {ω | 2 / T ≤ |X ω|} =ᵐ[P N] {ω | 2 / T ≤ |X' ω|} :=
      hXX.mono fun ω hω => by
        show (2 / T ≤ |X ω|) = (2 / T ≤ |X' ω|)
        rw [hω]
    rw [measureReal_congr hset]
    refine measureReal_two_div_le_abs_le_of_integral hX_m.measurable_mk hT hbi hbint
      fun t ht => ?_
    have heq : (∫ ω, cexp (I * t * X' ω) ∂P N) = ∫ ω, cexp (I * t * X ω) ∂P N :=
      integral_congr_ae (hXX.mono fun ω hω => by simp only [hω])
    rw [heq]
    exact hbt t ht
  -- conclusion
  have hsub : {ω | ε ≤ ‖quad (farPart (F N ω) n z) v‖} ⊆
      {ω | 2 / T ≤ |X ω|} ∪ {ω | ε / 2 ≤ ‖R ω - (X ω : ℂ)‖} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union] at hω ⊢
    by_contra hcon
    push Not at hcon
    have h1 : ‖R ω - (X ω : ℂ)‖ = |(R ω).im| := by
      have : R ω - (X ω : ℂ) = ((R ω).im : ℂ) * I := by
        apply Complex.ext <;> simp [hXdef]
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have h2 := Complex.norm_le_abs_re_add_abs_im (R ω)
    have h3 : 2 / T = ε / 2 := by rw [hTdef]; field_simp; ring
    rw [h3] at hcon
    rw [h1] at hcon
    have : ‖R ω‖ < ε := by linarith [hcon.1, hcon.2]
    exact absurd hω (not_le.2 this)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hX1 : P N {ω | 2 / T ≤ |X ω|} ≤ ENNReal.ofReal (2 * ε₁) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (P N) _)]
    exact ENNReal.ofReal_le_ofReal hD8
  have hX2 : P N {ω | ε / 2 ≤ ‖R ω - (X ω : ℂ)‖} ≤ ENNReal.ofReal (ε₁ / 8) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (P N) _)]
    exact ENNReal.ofReal_le_ofReal ((hp₂ (ε / 2) (min_le_right _ _)).trans (by linarith))
  refine (add_le_add hX1 hX2).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hε₁]
  linarith

end Hyp

end BlockBand.Critical.Herglotz
