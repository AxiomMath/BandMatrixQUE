module

public import BlockBand.Transmission.Dual.LevelPath
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.OptionalMain

/-!
# The level step of `conservative`

For a realization of `IsDualDeletionProcess` that is a deletion path at every `ω` (after
`exists_normalized`), with `R₀ < K`, `ρ = T ∧ τ_K` (`τ_K` the hitting time of `{R ≥ K}`) and
`1 ≤ q ≤ p`, `levelStep` states `E[R_{ρ∧σ_{q-1}} − R_{ρ∧σ_q}] = 0` (and the increment is
integrable).

Proof: the martingale `dualMartingale D₀ q f_n` with `f_n = u_{n+1}·R` (smooth exhaustion
`u_n`, `exists_chamber_exhaustion`) has continuous paths (`continuous_dualMartingale`), so it
can be stopped at `ρ ∧ θ_n` (`exists_martingale_stoppedProcess`), `θ_n` the hitting time of
`{P_n ≤ 1/2}`; its stopped value is `R_{ρ∧θ_n} − R_{σ_q}` on `{σ_q ≤ ρ∧θ_n, σ_q < θ_n}`
(`dualMartingale_eq_of_le_hit`); dominated convergence (`|·| ≤ K`) and `tendsto_level_gap`
give the claim.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

section Meas

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem measurable_dualCoordOf_comp {a b : Ω → ℕ → ℝ} (ha : Measurable a) (hb : Measurable b)
    (q : ℕ) : Measurable fun ω => dualCoordOf q (a ω) (b ω) := by
  unfold dualCoordOf
  exact Measurable.prodMk (f := fun ω (i : Fin q) => a ω i) (g := fun ω (i : Fin q) => b ω i)
    (measurable_pi_iff.2 fun i => measurable_pi_iff.1 ha (i : ℕ))
    (measurable_pi_iff.2 fun i => measurable_pi_iff.1 hb (i : ℕ))

theorem measurable_dualLift_comp {q : ℕ} {F : DualCoord q → ℝ} (hF : Measurable F)
    {n : Ω → ℕ} {a b : Ω → ℕ → ℝ} (hn : Measurable n) (ha : Measurable a)
    (hb : Measurable b) : Measurable fun ω => dualLift F (n ω) (a ω) (b ω) := by
  unfold dualLift
  exact Measurable.ite (hn (measurableSet_singleton q))
    (hF.comp (measurable_dualCoordOf_comp ha hb q)) measurable_const

theorem measurable_testVal_comp {q : ℕ} {F : DualCoord q → ℝ} (hF : Measurable F)
    {n : Ω → ℕ} {a b : Ω → ℕ → ℝ} (hn : Measurable n) (ha : Measurable a)
    (hb : Measurable b) : Measurable fun ω => testVal q F (n ω) (a ω) (b ω) := by
  unfold testVal
  exact (measurable_dualLift_comp hF hn ha hb).add
    (Measurable.ite (hn measurableSet_Ioi) measurable_const measurable_const)

theorem measurable_dualTotal_comp {n : Ω → ℕ} {a b : Ω → ℕ → ℝ} (hn : Measurable n)
    (ha : Measurable a) (hb : Measurable b) :
    Measurable fun ω => dualTotal (n ω) (a ω) (b ω) := by
  have hF : Measurable fun z : Ω × ℕ => dualTotal z.2 (a z.1) (b z.1) :=
    measurable_from_prod_countable_left fun k => by
      show Measurable fun x => ∑ i ∈ Finset.range k, (a x i + b x i)
      exact Finset.measurable_fun_sum _ fun i _ =>
        (measurable_pi_iff.1 ha i).fun_add (measurable_pi_iff.1 hb i)
  exact hF.comp (measurable_id.prodMk hn)

end Meas

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 m} {D0 : ℝ} {p : ℕ} {x y : Fin p → ℝ}
  {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

/-- `τ_K`: first time `R ≥ K`. -/
def capHit (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (K : ℝ) : Ω → WithTop ℝ≥0 :=
  hitLe (fun t ω => -dualTotal (N t ω) (X t ω) (Y t ω)) (-K)

/-- `ρ = T ∧ τ_K` as a real time. -/
def capTime (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (K : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (min (T : WithTop ℝ≥0) (capHit N X Y K ω)).untopA

/-- `R_{ρ ∧ σ_j}`. -/
def stopTotal (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (K : ℝ) (T : ℝ≥0) (j : ℕ)
    (ω : Ω) : ℝ :=
  pathTotal (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)
    (min (capTime N X Y K T ω : WithTop ℝ≥0) (entryTime (fun t => N t ω) j)).untopA

omit m in
theorem coe_capTime (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (K : ℝ) (T : ℝ≥0) (ω : Ω) :
    (capTime N X Y K T ω : WithTop ℝ≥0) = min (T : WithTop ℝ≥0) (capHit N X Y K ω) :=
  coe_untopA_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))

/-- **Level step**: `E[R_{ρ∧σ_{q-1}} − R_{ρ∧σ_q}] = 0`. -/
theorem levelStep (h : IsDualDeletionProcess P 𝓕 D0 x y N X Y)
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (hstart : ∀ ω, N 0 ω = p) {K : ℝ} (hK : ∀ ω, dualTotal (N 0 ω) (X 0 ω) (Y 0 ω) < K)
    (T : ℝ≥0) {q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    Integrable (fun ω => stopTotal N X Y K T (q - 1) ω - stopTotal N X Y K T q ω) P ∧
      ∫ ω, (stopTotal N X Y K T (q - 1) ω - stopTotal N X Y K T q ω) ∂P = 0 := by
  obtain ⟨u, hsm, hcs, hts, hu01, hO, hex⟩ := exists_chamber_exhaustion q
  have hNm : ∀ t, Measurable[𝓕 t] (N t) := fun t => (h.adapted t).1
  have hXm : ∀ t, Measurable[𝓕 t] (X t) := fun t => (h.adapted t).2.1
  have hYm : ∀ t, Measurable[𝓕 t] (Y t) := fun t => (h.adapted t).2.2
  have hq0 : ∀ ω, q ≤ N 0 ω := fun ω => (hstart ω).symm ▸ hqp
  -- the cap `ρ = T ∧ τ_K`
  have hτ : IsStoppingTime 𝓕 (capHit N X Y K) := by
    refine isStoppingTime_hitLe (fun t => (measurable_dualTotal_comp (mΩ := 𝓕 t) (hNm t)
      (hXm t) (hYm t)).neg) (fun ω t => ?_) (fun ω => ?_) (-K)
    · exact (((continuous_total (hpath ω)).neg).tendsto t).mono_left nhdsWithin_le_nhds
    · exact ((continuous_total (hpath ω)).neg).lowerSemicontinuous
  have hρ : IsStoppingTime 𝓕 fun ω => min (T : WithTop ℝ≥0) (capHit N X Y K ω) :=
    (isStoppingTime_const 𝓕 T).min hτ
  -- the localizing times `θ_k`
  set θ : ℕ → Ω → WithTop ℝ≥0 :=
    fun k => hitLe (fun t ω => testVal q (u k) (N t ω) (X t ω) (Y t ω)) (1 / 2) with hθdef
  have hθ : ∀ k, IsStoppingTime 𝓕 (θ k) := fun k =>
    isStoppingTime_hitLe (fun t => measurable_testVal_comp (mΩ := 𝓕 t)
      (hsm k).continuous.measurable (hNm t) (hXm t) (hYm t))
      (fun ω t => tendsto_testVal_right (hpath ω) (hsm k).continuous t)
      (fun ω => lowerSemicontinuous_testVal (hpath ω) (hsm k).continuous
        (fun z hz => image_eq_zero_of_notMem_tsupport fun h' => hz (hts k h'))
        (fun z => (hu01 k z).2) hq) (1 / 2)
  -- the stopped increments
  set g : ℕ → Ω → ℝ := fun k ω =>
    if entryTime (fun t => N t ω) q ≤
        ((min (capTime N X Y K T ω : WithTop ℝ≥0) (θ k ω)).untopA : WithTop ℝ≥0) ∧
        entryTime (fun t => N t ω) q < θ k ω then
      pathTotal (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)
          (min (capTime N X Y K T ω : WithTop ℝ≥0) (θ k ω)).untopA -
        pathTotal (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)
          (entryTime (fun t => N t ω) q).untopA
    else 0 with hgdef
  -- Claim A: each `g k` is a.e.-measurable with integral `0`
  have hA : ∀ k, AEStronglyMeasurable (g k) P ∧ ∫ ω, g k ω ∂P = 0 := by
    intro k
    obtain ⟨O, hOo, hOs, hO1⟩ := hO k
    set f : DualCoord q → ℝ := fun z => u (k + 1) z * totalFun q z with hfdef
    have htot : totalFun q = ⇑(totalCLM q) := funext fun z => (totalCLM_apply z).symm
    have hfsm : ContDiff ℝ (⊤ : ℕ∞) f := by
      rw [hfdef, htot]; exact (hsm (k + 1)).mul (totalCLM q).contDiff
    have hfc : HasCompactSupport f := (hcs (k + 1)).mul_right
    have hfs : tsupport f ⊆ dualChamber q := tsupport_mul_subset_left.trans (hts (k + 1))
    have hfO : EqOn f (totalFun q) O := fun z hz => by
      simp only [hfdef, hO1 z hz, one_mul]
    have hhO : ∀ z, 1 / 2 ≤ u k z → z ∈ O := fun z hz =>
      hOs (show u k z ≠ 0 by intro e; rw [e] at hz; norm_num at hz)
    have hh0 : ∀ z ∉ dualChamber q, u k z = 0 := fun z hz =>
      image_eq_zero_of_notMem_tsupport fun h' => hz (hts k h')
    have hM := h.martingale q hq hqp f hfsm hfc hfs
    have hcont : ∀ ω, Continuous fun t => dualMartingale D0 q f N X Y t ω := fun ω =>
      continuous_dualMartingale (hpath ω) D0 hq (hfsm.of_le (by norm_cast))
        hfc hfs
    have hρk : IsStoppingTime 𝓕 fun ω => min (min (T : WithTop ℝ≥0) (capHit N X Y K ω))
        (θ k ω) := hρ.min (hθ k)
    obtain ⟨M', hM', hM'e⟩ := exists_martingale_stoppedProcess hM
      (fun t => EventuallyEq.rfl) (ae_of_all _ hcont) hρk
    have hval : ∀ ω (r : ℝ≥0), (r : WithTop ℝ≥0) ≤ θ k ω →
        dualMartingale D0 q f N X Y r ω =
          if entryTime (fun t => N t ω) q ≤ r ∧ entryTime (fun t => N t ω) q < θ k ω then
            dualTotal (N r ω) (X r ω) (Y r ω) - dualTotal
              (N (entryTime (fun t => N t ω) q).untopA ω)
              (X (entryTime (fun t => N t ω) q).untopA ω)
              (Y (entryTime (fun t => N t ω) q).untopA ω)
          else 0 := fun ω r hr =>
      dualMartingale_eq_of_le_hit (hpath ω) D0 hq (hq0 ω) (hsm k).continuous hh0 hOo hhO hfO
        (fun v hv => lt_hitLe hv) hr
    have hT : ∀ ω, stoppedProcess (dualMartingale D0 q f N X Y)
        (fun ω => min (min (T : WithTop ℝ≥0) (capHit N X Y K ω)) (θ k ω)) T ω = g k ω := by
      intro ω
      have hle : min (min (T : WithTop ℝ≥0) (capHit N X Y K ω)) (θ k ω) ≤ T :=
        (min_le_left _ _).trans (min_le_left _ _)
      simp only [stoppedProcess, min_eq_right hle]
      rw [← coe_capTime]
      have hfin : min (capTime N X Y K T ω : WithTop ℝ≥0) (θ k ω) ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
      have hr : (((min (capTime N X Y K T ω : WithTop ℝ≥0) (θ k ω)).untopA : ℝ≥0) :
          WithTop ℝ≥0) ≤ θ k ω := by
        rw [coe_untopA_of_ne_top hfin]; exact min_le_right _ _
      rw [hval ω _ hr]
      rfl
    have h0 : ∀ ω, stoppedProcess (dualMartingale D0 q f N X Y)
        (fun ω => min (min (T : WithTop ℝ≥0) (capHit N X Y K ω)) (θ k ω)) 0 ω = 0 := by
      intro ω
      have hz : ∀ a : WithTop ℝ≥0, ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ a := fun a => by
        rw [WithTop.coe_zero]; exact zero_le
      simp only [stoppedProcess]
      rw [min_eq_left (hz _), show ((0 : ℝ≥0) : WithTop ℝ≥0).untopA = 0 from rfl,
        hval ω 0 (hz _)]
      split_ifs with hc
      · have hE0 : entryTime (fun t => N t ω) q = 0 :=
          le_antisymm (by exact_mod_cast hc.1) zero_le
        rw [hE0]; simp
      · rfl
    have hgT : g k =ᵐ[P] M' T := by
      filter_upwards [hM'e T] with ω hω
      rw [← hT ω, hω]
    refine ⟨((hM'.stronglyMeasurable T).mono (𝓕.le T)).aestronglyMeasurable.congr hgT.symm, ?_⟩
    rw [integral_congr_ae hgT]
    have h1 := hM'.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h1
    rw [← h1, integral_congr_ae (hM'e 0)]
    calc _ = ∫ ω, (0 : ℝ) ∂P := integral_congr_ae (ae_of_all _ h0)
      _ = 0 := integral_zero _ _
  -- Claim B: pointwise convergence
  have hB : ∀ ω, Tendsto (fun k => g k ω) atTop
      (𝓝 (stopTotal N X Y K T (q - 1) ω - stopTotal N X Y K T q ω)) := fun ω =>
    tendsto_level_gap (hpath ω) hq (hq0 ω) (capTime N X Y K T ω) (fun k => θ k ω)
      (fun e he k => hit_le_entry_pred (hpath ω) hq he)
      (fun t ht1 ht2 => eventually_lt_hit (hpath ω) (fun k => (hsm k).continuous) hex ht1 ht2)
  -- Claim C: the bound `K`
  have hKbound : ∀ ω (v : ℝ≥0), (v : WithTop ℝ≥0) ≤ capTime N X Y K T ω →
      0 ≤ pathTotal (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω) v ∧
        pathTotal (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω) v ≤ K := by
    intro ω v hv
    refine ⟨dualTotal_nonneg (hpath ω) v, total_le_of_le_hit (hpath ω) (hK ω) ?_⟩
    exact hv.trans ((coe_capTime N X Y K T ω).le.trans (min_le_right _ _))
  have hC : ∀ k ω, ‖g k ω‖ ≤ K := by
    intro k ω
    have hfin : min (capTime N X Y K T ω : WithTop ℝ≥0) (θ k ω) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    show ‖(if entryTime (fun t => N t ω) q ≤
        ((min (capTime N X Y K T ω : WithTop ℝ≥0) (θ k ω)).untopA : WithTop ℝ≥0) ∧
        entryTime (fun t => N t ω) q < θ k ω then
      pathTotal (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)
          (min (capTime N X Y K T ω : WithTop ℝ≥0) (θ k ω)).untopA -
        pathTotal (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)
          (entryTime (fun t => N t ω) q).untopA
      else 0)‖ ≤ K
    split_ifs with hc
    · have hle : (((min (capTime N X Y K T ω : WithTop ℝ≥0) (θ k ω)).untopA : ℝ≥0) :
          WithTop ℝ≥0) ≤ capTime N X Y K T ω := by
        rw [coe_untopA_of_ne_top hfin]; exact min_le_left _ _
      obtain ⟨a1, a2⟩ := hKbound ω _ hle
      have hEfin : entryTime (fun t => N t ω) q ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top hc.1
      obtain ⟨b1, b2⟩ := hKbound ω (entryTime (fun t => N t ω) q).untopA
        (by rw [coe_untopA_of_ne_top hEfin]; exact hc.1.trans hle)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    · have := hK ω
      have h0 := dualTotal_nonneg (hpath ω) 0
      simp only [norm_zero]
      linarith
  -- dominated convergence
  have hmeas : ∀ k, AEStronglyMeasurable (g k) P := fun k => (hA k).1
  have hlim := tendsto_integral_of_dominated_convergence (fun _ => K) hmeas
    (integrable_const K) (fun k => ae_of_all _ (hC k)) (ae_of_all _ hB)
  have hzero : (fun k => ∫ ω, g k ω ∂P) = fun _ => 0 := funext fun k => (hA k).2
  rw [hzero] at hlim
  have hmeasT := aestronglyMeasurable_of_tendsto_ae atTop hmeas (ae_of_all _ hB)
  have hbT : ∀ ω, ‖stopTotal N X Y K T (q - 1) ω - stopTotal N X Y K T q ω‖ ≤ K := fun ω =>
    le_of_tendsto ((continuous_norm.tendsto _).comp (hB ω))
      (Eventually.of_forall fun k => hC k ω)
  exact ⟨Integrable.of_bound hmeasT K (ae_of_all _ hbT),
    tendsto_nhds_unique hlim tendsto_const_nhds⟩

end BlockBand.Transmission.Dual
