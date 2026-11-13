module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Isometry
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Doob
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The continuous stochastic integral process

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, `h : IsL2Integrator Q 𝓖 N α`,
horizon `T`, integrand `H ∈ PredL2 𝓖 ν_T` (`ν_T = α ds ⊗ Q` on `(0,T] × Ω`).

Construction: simple integrands `x_n = h.approx T H n` with `‖x_n - H‖_{L²(ν_T)} < 4⁻ⁿ`; their
elementary integral processes `h.approxProc T H n = elemProc N x_n` have continuous paths
wherever `N` does. By the weak Doob inequality in modification form
(`measure_maximal_le_of_modification`) and Borel–Cantelli, a.s. eventually
`sup_{t ≤ T} |approxProc (n+1) - approxProc n| < 2⁻ⁿ`, so the processes converge uniformly in
`t` a.s.; `h.contIntegral T H t ω` is the pointwise limit (`limUnder`).

Main result `contIntegral_spec`: `t ↦ ∫_0^t H dN` has a.s. continuous paths, is in `L²(Q)` at
every time, has a `𝓖`-martingale modification, equals `stochIntegral h T H` a.s. at time
`T`, and is constant after `T`. `eLpNorm_approxProc_sub_contIntegral_le` gives the `L²` rate.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

/-- **Uniform Cauchy criterion.** If `|F_{n+1} - F_n| ≤ 2⁻ⁿ` uniformly for `n ≥ n₀`, then `F_n`
converges uniformly to its pointwise `limUnder`. -/
theorem tendstoUniformly_limUnder_of_le_geometric {β : Type*} {F : ℕ → β → ℝ} {n₀ : ℕ}
    (hF : ∀ n ≥ n₀, ∀ t, |F (n + 1) t - F n t| ≤ (1 / 2 : ℝ) ^ n) :
    TendstoUniformly F (fun t => limUnder atTop fun n => F n t) atTop := by
  set C : ℝ := 2 * (1 / 2 : ℝ) ^ n₀
  have hg : ∀ t k, dist (F (k + n₀) t) (F (k + 1 + n₀) t) ≤ C / 2 / 2 ^ k := by
    intro t k
    rw [dist_comm, Real.dist_eq]
    have := hF (k + n₀) (Nat.le_add_left _ _) t
    rw [show k + 1 + n₀ = k + n₀ + 1 by ring]
    calc _ ≤ (1 / 2 : ℝ) ^ (k + n₀) := this
      _ = C / 2 / 2 ^ k := by simp only [C, pow_add, one_div, inv_pow]; field_simp
  have hlim : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (limUnder atTop fun n => F n t)) := by
    intro t
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two (hg t))
    have hL' : Tendsto (fun n => F n t) atTop (𝓝 L) :=
      (tendsto_add_atTop_iff_nat (f := fun n => F n t) n₀).1 hL
    rwa [hL'.limUnder_eq]
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨k, hk⟩ : ∃ k : ℕ, C / 2 ^ k < ε := by
    have : Tendsto (fun k : ℕ => C / 2 ^ k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    exact (this.eventually (gt_mem_nhds hε)).exists
  filter_upwards [eventually_ge_atTop (k + n₀)] with n hn t
  obtain ⟨j, rfl⟩ : ∃ j, n = j + n₀ := ⟨n - n₀, by omega⟩
  have hb := dist_le_of_le_geometric_two_of_tendsto (hg t)
    ((tendsto_add_atTop_iff_nat (f := fun n => F n t) n₀).2 (hlim t)) j
  rw [dist_comm]
  calc _ ≤ C / 2 ^ j := hb
    _ ≤ C / 2 ^ k := by
        gcongr
        · norm_num
        · omega
    _ < ε := hk

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 mΩ} {N α : ℝ≥0 → Ω → ℝ}

omit [IsFiniteMeasure Q] in
theorem eLpNorm_Lp_eq (f : Lp ℝ 2 Q) : eLpNorm f 2 Q = ENNReal.ofReal ‖f‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]

/-- A martingale-criterion helper: an a.e.-adapted integrable process with the martingale
set-integral identity has a martingale modification (finite measure). -/
theorem exists_martingale_modification' {X : ℝ≥0 → Ω → ℝ} (hint : ∀ t, Integrable (X t) Q)
    (hmeas : ∀ t, AEStronglyMeasurable[𝓖 t] (X t) Q)
    (hset : ∀ s t, s ≤ t → ∀ A, MeasurableSet[𝓖 s] A →
      ∫ ω in A, X t ω ∂Q = ∫ ω in A, X s ω ∂Q) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M 𝓖 Q ∧ ∀ t, M t =ᵐ[Q] X t := by
  refine ⟨fun t => Q[X t | 𝓖 t], ⟨fun t => stronglyMeasurable_condExp, fun i j hij => ?_⟩,
    fun t => condExp_of_aestronglyMeasurable' (𝓖.le t) (hmeas t) (hint t)⟩
  have h1 := condExp_condExp_of_le (μ := Q) (f := X j) (𝓖.mono hij) (𝓖.le j)
  have h2 : X i =ᵐ[Q] Q[X j | 𝓖 i] :=
    ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le i) (hint j)
      (fun s _ _ => (hint i).integrableOn) (fun s hs _ => (hset i j hij s hs).symm) (hmeas i)
  exact h1.trans (h2.symm.trans (condExp_of_aestronglyMeasurable' (𝓖.le i) (hmeas i)
    (hint i)).symm)

namespace IsL2Integrator

variable (h : IsL2Integrator Q 𝓖 N α) (T : ℝ≥0)

/-- `L²` size of an elementary integral at any time, by the isometry and `L²` contraction of
the martingale modification. -/
theorem eLpNorm_elemProc_le (x : Rect 𝓖 T →₀ ℝ) (t : ℝ≥0) :
    eLpNorm (elemProc N x t) 2 Q ≤ ENNReal.ofReal ‖h.integrandLin T x‖ := by
  have hT : eLpNorm (elemProc N x T) 2 Q = ENNReal.ofReal ‖h.integrandLin T x‖ := by
    rw [← h.norm_valueLin, ← eLpNorm_Lp_eq]
    exact eLpNorm_congr_ae ((elemProc_ae h.mart_ae x T).symm.trans (h.valueLin_ae T x).symm)
  rcases le_total t T with ht | ht
  · rw [← hT]
    have hmart := elemProc_martingale h.mart_martingale x
    calc eLpNorm (elemProc N x t) 2 Q = eLpNorm (elemProc h.mart x t) 2 Q :=
          eLpNorm_congr_ae (elemProc_ae h.mart_ae x t).symm
      _ = eLpNorm (Q[elemProc h.mart x T | 𝓖 t]) 2 Q :=
          eLpNorm_congr_ae (hmart.condExp_ae_eq ht).symm
      _ ≤ eLpNorm (elemProc h.mart x T) 2 Q := eLpNorm_condExp_le_eLpNorm _ one_le_two
      _ = eLpNorm (elemProc N x T) 2 Q := eLpNorm_congr_ae (elemProc_ae h.mart_ae x T)
  · rw [elemProc_of_le N x ht, hT]

variable (H : PredL2 𝓖 (bracketMeasure Q α T))

theorem exists_approx (n : ℕ) :
    ∃ x : Rect 𝓖 T →₀ ℝ, ‖h.integrandLin T x - H‖ < (1 / 4 : ℝ) ^ n := by
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.1 (h.denseRange_integrandLin T) H _
    (by positivity : (0 : ℝ) < (1 / 4) ^ n)
  exact ⟨x, by rwa [dist_comm, dist_eq_norm] at hx⟩

/-- Fast simple approximations of `H`. -/
def approx (n : ℕ) : Rect 𝓖 T →₀ ℝ := (h.exists_approx T H n).choose

theorem approx_spec (n : ℕ) : ‖h.integrandLin T (h.approx T H n) - H‖ < (1 / 4 : ℝ) ^ n :=
  (h.exists_approx T H n).choose_spec

/-- Approximating elementary integral processes (continuous where `N` is). -/
def approxProc (n : ℕ) : ℝ≥0 → Ω → ℝ := elemProc N (h.approx T H n)

/-- **The continuous stochastic integral** `t ↦ ∫_0^t H dN` (pointwise limit). -/
def contIntegral (t : ℝ≥0) (ω : Ω) : ℝ := limUnder atTop fun n => h.approxProc T H n t ω

theorem norm_integrandLin_sub {k n : ℕ} (hkn : k ≤ n) :
    ‖h.integrandLin T (h.approx T H n - h.approx T H k)‖ ≤ 2 * (1 / 4 : ℝ) ^ k := by
  rw [map_sub]
  have h1 := h.approx_spec T H n
  have h2 := h.approx_spec T H k
  have h3 : (1 / 4 : ℝ) ^ n ≤ (1 / 4) ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num) hkn
  calc _ = ‖(h.integrandLin T (h.approx T H n) - H) - (h.integrandLin T (h.approx T H k) - H)‖ := by
        congr 1; abel
    _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := by linarith

theorem approxProc_sub (n k : ℕ) (t : ℝ≥0) :
    (fun ω => h.approxProc T H n t ω - h.approxProc T H k t ω) =
      elemProc N (h.approx T H n - h.approx T H k) t := by
  funext ω; simp [approxProc, map_sub]

theorem eLpNorm_approxProc_sub_le {k n : ℕ} (hkn : k ≤ n) (t : ℝ≥0) :
    eLpNorm (fun ω => h.approxProc T H n t ω - h.approxProc T H k t ω) 2 Q ≤
      ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ k) := by
  rw [approxProc_sub]
  exact (h.eLpNorm_elemProc_le T _ t).trans
    (ENNReal.ofReal_le_ofReal (h.norm_integrandLin_sub T H hkn))

theorem memLp_approxProc (n : ℕ) (t : ℝ≥0) : MemLp (h.approxProc T H n t) 2 Q :=
  elemProc_memLp h.memLp _ t

/-- The Borel–Cantelli events: `sup_{t ≤ T} |approxProc (n+1) - approxProc n| ≥ 2⁻ⁿ`. -/
def badEvent (n : ℕ) : Set Ω :=
  {ω | ∃ t ≤ T, ((((1 / 2 : ℝ≥0) ^ n : ℝ≥0)) : ℝ) ≤
    |h.approxProc T H (n + 1) t ω - h.approxProc T H n t ω|}

theorem measure_badEvent_le (n : ℕ) :
    Q (h.badEvent T H n) ≤ ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ n) := by
  set y := h.approx T H (n + 1) - h.approx T H n
  have hd := h.approxProc_sub T H (n + 1) n
  have hcont : ∀ᵐ ω ∂Q, Continuous fun t => elemProc N y t ω := by
    filter_upwards [h.continuous] with ω hω using elemProc_continuous hω y
  have hdoob := measure_maximal_le_of_modification (elemProc_martingale h.mart_martingale y)
    (elemProc_ae h.mart_ae y) T hcont ((1 / 2 : ℝ≥0) ^ n)
  have hev : h.badEvent T H n =
      {ω | ∃ t ≤ T, ((((1 / 2 : ℝ≥0) ^ n : ℝ≥0)) : ℝ) ≤ |elemProc N y t ω|} := by
    ext ω
    simp only [badEvent, mem_ofPred_eq]
    refine exists_congr fun t => ?_
    rw [show h.approxProc T H (n + 1) t ω - h.approxProc T H n t ω = elemProc N y t ω from
      congrFun (hd t) ω]
  have hrhs : ∫⁻ ω, ‖elemProc N y T ω‖ₑ ^ 2 ∂Q ≤ ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ n) ^ 2 := by
    rw [SDE.lintegral_enorm_sq_eq_eLpNorm_sq (elemProc_memLp h.memLp y T).aestronglyMeasurable]
    gcongr
    rw [← hd T]
    exact h.eLpNorm_approxProc_sub_le T H (Nat.le_succ n) T
  rw [← hev] at hdoob
  have hl : (((1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((1 / 4 : ℝ) ^ n) := by
    rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal]
    congr 1
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hr : ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ n) ^ 2 =
      ENNReal.ofReal ((1 / 4 : ℝ) ^ n) * ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ n) := by
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hl] at hdoob
  have h0 : ENNReal.ofReal ((1 / 4 : ℝ) ^ n) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  exact (ENNReal.mul_le_mul_iff_right h0 ENNReal.ofReal_ne_top).1
    (hdoob.trans (hrhs.trans hr.le))

theorem ae_eventually_good : ∀ᵐ ω ∂Q, ∀ᶠ n in atTop, ω ∉ h.badEvent T H n := by
  apply ae_eventually_notMem
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum (h.measure_badEvent_le T H))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 4)]
  exact ENNReal.ofReal_ne_top

/-- Pathwise: a.s. the approximations converge uniformly in time to `contIntegral`. -/
theorem ae_tendstoUniformly : ∀ᵐ ω ∂Q, (Continuous fun t => N t ω) ∧
    TendstoUniformly (fun n t => h.approxProc T H n t ω)
      (fun t => h.contIntegral T H t ω) atTop := by
  filter_upwards [h.continuous, h.ae_eventually_good T H] with ω hω hgood
  refine ⟨hω, ?_⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hgood
  refine tendstoUniformly_limUnder_of_le_geometric (n₀ := n₀) fun n hn t => ?_
  have hnot := hn₀ n hn
  have key : ∀ u ≤ T, |h.approxProc T H (n + 1) u ω - h.approxProc T H n u ω| ≤
      (1 / 2 : ℝ) ^ n := by
    intro u hu
    by_contra hc
    exact hnot ⟨u, hu, by push_cast; exact (lt_of_not_ge hc).le⟩
  rcases le_total t T with ht | ht
  · exact key t ht
  · simp only [approxProc, elemProc_of_le N _ ht]
    exact key T le_rfl

theorem contIntegral_continuous : ∀ᵐ ω ∂Q, Continuous fun t => h.contIntegral T H t ω := by
  filter_upwards [h.ae_tendstoUniformly T H] with ω hω
  exact hω.2.continuous (Frequently.of_forall fun _ => elemProc_continuous hω.1 _)

theorem ae_tendsto (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, Tendsto (fun n => h.approxProc T H n t ω) atTop (𝓝 (h.contIntegral T H t ω)) := by
  filter_upwards [h.ae_tendstoUniformly T H] with ω hω using hω.2.tendsto_at t

theorem aestronglyMeasurable_contIntegral (t : ℝ≥0) :
    AEStronglyMeasurable[𝓖 t] (h.contIntegral T H t) Q :=
  Semimartingale.aestronglyMeasurable_of_tendsto_ae_sub
    (f := fun n => h.approxProc T H n t)
    (fun _ => ((elemProc_martingale h.mart_martingale _).stronglyMeasurable t).aestronglyMeasurable.congr
      (elemProc_ae h.mart_ae _ t))
    (h.ae_tendsto T H t)

/-- **`L²` rate**: `‖approxProc k t - ∫_0^t H dN‖_{L²} ≤ 2 · 4⁻ᵏ`. -/
theorem eLpNorm_approxProc_sub_contIntegral_le (k : ℕ) (t : ℝ≥0) :
    eLpNorm (fun ω => h.approxProc T H k t ω - h.contIntegral T H t ω) 2 Q ≤
      ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ k) := by
  have hlim : ∀ᵐ ω ∂Q, Tendsto (fun n => h.approxProc T H k t ω - h.approxProc T H n t ω)
      atTop (𝓝 (h.approxProc T H k t ω - h.contIntegral T H t ω)) := by
    filter_upwards [h.ae_tendsto T H t] with ω hω using hω.const_sub _
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm
    (fun n => ((h.memLp_approxProc T H k t).sub (h.memLp_approxProc T H n t)).aestronglyMeasurable)
    _ ((h.memLp_approxProc T H k t).aestronglyMeasurable.sub
      ((h.aestronglyMeasurable_contIntegral T H t).mono (𝓖.le t))) hlim).trans ?_
  refine liminf_le_of_frequently_le' ((eventually_ge_atTop k).frequently.mono fun n hn => ?_)
  have hneg : (h.approxProc T H k t - h.approxProc T H n t) =
      -(fun ω => h.approxProc T H n t ω - h.approxProc T H k t ω) := by
    funext ω; simp
  rw [hneg, eLpNorm_neg]
  exact h.eLpNorm_approxProc_sub_le T H hn t

theorem memLp_contIntegral (t : ℝ≥0) : MemLp (h.contIntegral T H t) 2 Q := by
  have h1 : MemLp (fun ω => h.approxProc T H 0 t ω - h.contIntegral T H t ω) 2 Q :=
    (h.eLpNorm_approxProc_sub_contIntegral_le T H 0 t).trans_lt ENNReal.ofReal_lt_top
  have h2 := (h.memLp_approxProc T H 0 t).sub h1
  convert h2 using 1
  funext ω; simp

theorem tendsto_ofReal_geom (c : ℝ) :
    Tendsto (fun k : ℕ => ENNReal.ofReal (c * (1 / 4 : ℝ) ^ k)) atTop (𝓝 0) := by
  have : Tendsto (fun k : ℕ => c * (1 / 4 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num)
      (by norm_num)).const_mul c
  simpa using ENNReal.tendsto_ofReal this

theorem tendsto_setIntegral_approxProc (t : ℝ≥0) (B : Set Ω) :
    Tendsto (fun k => ∫ ω in B, h.approxProc T H k t ω ∂Q) atTop
      (𝓝 (∫ ω in B, h.contIntegral T H t ω ∂Q)) := by
  refine tendsto_setIntegral_of_L1' _
    (Eventually.of_forall fun k => (h.memLp_approxProc T H k t).integrable one_le_two) ?_ B
  have hb : ∀ k, eLpNorm (h.approxProc T H k t - h.contIntegral T H t) 1 Q ≤
      ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ k) * Q univ ^ (1 / 2 : ℝ) := by
    intro k
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num)
      ((h.memLp_approxProc T H k t).aestronglyMeasurable.sub
        ((h.aestronglyMeasurable_contIntegral T H t).mono (𝓖.le t)))).trans ?_
    have he : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
    rw [he]
    exact mul_le_mul_left (h.eLpNorm_approxProc_sub_contIntegral_le T H k t) _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun k => zero_le) hb
  simpa using ENNReal.Tendsto.mul_const (tendsto_ofReal_geom 2)
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top Q univ)))

theorem setIntegral_contIntegral_eq {u v : ℝ≥0} (huv : u ≤ v) {B : Set Ω}
    (hB : MeasurableSet[𝓖 u] B) :
    ∫ ω in B, h.contIntegral T H v ω ∂Q = ∫ ω in B, h.contIntegral T H u ω ∂Q := by
  have heq : ∀ k, ∫ ω in B, h.approxProc T H k v ω ∂Q = ∫ ω in B, h.approxProc T H k u ω ∂Q := by
    intro k
    have hm := elemProc_martingale h.mart_martingale (h.approx T H k)
    unfold approxProc
    rw [setIntegral_congr_ae (𝓖.le u B hB)
        ((elemProc_ae h.mart_ae (h.approx T H k) v).mono fun ω h _ => h.symm),
      setIntegral_congr_ae (𝓖.le u B hB)
        ((elemProc_ae h.mart_ae (h.approx T H k) u).mono fun ω h _ => h.symm)]
    exact (hm.setIntegral_eq huv hB).symm
  exact tendsto_nhds_unique ((h.tendsto_setIntegral_approxProc T H v B).congr heq)
    (h.tendsto_setIntegral_approxProc T H u B)

theorem contIntegral_T : h.contIntegral T H T =ᵐ[Q] h.stochIntegral T H := by
  have hm : AEStronglyMeasurable (fun ω => h.contIntegral T H T ω - h.stochIntegral T H ω) Q :=
    (h.memLp_contIntegral T H T).aestronglyMeasurable.sub (Lp.aestronglyMeasurable _)
  have hb : ∀ k, eLpNorm (fun ω => h.contIntegral T H T ω - h.stochIntegral T H ω) 2 Q ≤
      ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ k) + ENNReal.ofReal (1 * (1 / 4 : ℝ) ^ k) := by
    intro k
    have e2 : eLpNorm (fun ω => h.approxProc T H k T ω - h.stochIntegral T H ω) 2 Q ≤
        ENNReal.ofReal (1 * (1 / 4 : ℝ) ^ k) := by
      have hae : (fun ω => h.approxProc T H k T ω - h.stochIntegral T H ω) =ᵐ[Q]
          ⇑(h.stochIntegral T (h.integrandLin T (h.approx T H k)) - h.stochIntegral T H) := by
        filter_upwards [h.stochIntegral_integrandLin_ae T (h.approx T H k),
          Lp.coeFn_sub (h.stochIntegral T (h.integrandLin T (h.approx T H k)))
            (h.stochIntegral T H)] with ω h1 h2
        rw [h2, Pi.sub_apply, h1]; rfl
      rw [eLpNorm_congr_ae hae, eLpNorm_Lp_eq, ← map_sub, LinearIsometry.norm_map, one_mul]
      exact ENNReal.ofReal_le_ofReal (h.approx_spec T H k).le
    have hneg : eLpNorm (fun ω => h.contIntegral T H T ω - h.approxProc T H k T ω) 2 Q ≤
        ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ k) := by
      have : (fun ω => h.contIntegral T H T ω - h.approxProc T H k T ω) =
          -(fun ω => h.approxProc T H k T ω - h.contIntegral T H T ω) := by funext ω; simp
      rw [this, eLpNorm_neg]; exact h.eLpNorm_approxProc_sub_contIntegral_le T H k T
    calc _ = eLpNorm ((fun ω => h.contIntegral T H T ω - h.approxProc T H k T ω) +
          (fun ω => h.approxProc T H k T ω - h.stochIntegral T H ω)) 2 Q := by
          congr 1; funext ω; simp
      _ ≤ _ := eLpNorm_add_le one_le_two
      _ ≤ _ := add_le_add hneg e2
  have h0 : eLpNorm (fun ω => h.contIntegral T H T ω - h.stochIntegral T H ω) 2 Q = 0 := by
    have ht : Tendsto (fun k : ℕ => ENNReal.ofReal (2 * (1 / 4 : ℝ) ^ k) +
        ENNReal.ofReal (1 * (1 / 4 : ℝ) ^ k)) atTop (𝓝 0) := by
      simpa using (tendsto_ofReal_geom 2).add (tendsto_ofReal_geom 1)
    exact le_antisymm (ge_of_tendsto' ht hb) zero_le
  rw [eLpNorm_eq_zero_iff two_ne_zero] at h0
  filter_upwards [h0] with ω hω
  simpa [sub_eq_zero] using hω

theorem contIntegral_of_le {t : ℝ≥0} (ht : T ≤ t) : h.contIntegral T H t = h.contIntegral T H T := by
  funext ω
  simp only [contIntegral, approxProc, elemProc_of_le N _ ht]

/-- **The continuous stochastic integral `t ↦ ∫_0^t H dN`** for `H ∈ PredL2 𝓖 ν_T`:
a.s. continuous paths, `L²(Q)` at every time, a `𝓖`-martingale modification, terminal value
`stochIntegral h T H` a.s., constant after `T`. -/
theorem contIntegral_spec :
    (∀ᵐ ω ∂Q, Continuous fun t => h.contIntegral T H t ω) ∧
    (∀ t, MemLp (h.contIntegral T H t) 2 Q) ∧
    (∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y 𝓖 Q ∧ ∀ t, Y t =ᵐ[Q] h.contIntegral T H t) ∧
    h.contIntegral T H T =ᵐ[Q] h.stochIntegral T H ∧
    (∀ t, T ≤ t → h.contIntegral T H t = h.contIntegral T H T) :=
  ⟨h.contIntegral_continuous T H, h.memLp_contIntegral T H,
    exists_martingale_modification' (fun t => (h.memLp_contIntegral T H t).integrable one_le_two)
      (h.aestronglyMeasurable_contIntegral T H)
      (fun _ _ huv _ hB => h.setIntegral_contIntegral_eq T H huv hB),
    h.contIntegral_T T H, fun _ ht => h.contIntegral_of_le T H ht⟩

end IsL2Integrator

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
