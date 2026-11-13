module

public import BlockBand.Transmission.DualFeller.AbsLyap

/-!
# Optional stopping for the absorption Lyapunov function

Setting: any `S : Type`, probability `μ`, driver space `LΩ S` with law `LP μ` and the augmented
filtration, `D₀ > 0`, an admissible start `ξ` and one lifted family `F`. Fix a radius `m`, a
level `ε`, a horizon `T`, and write `h = hitS_m(ε)`, `a = T ∧ h`.
* `absDrift F m = 1{t ≤ e_m} L₁u(Yf m t)`: the drift of `u(Yf m)` (Itô's formula, `isCSM_G`);
  `−absDrift ≥ 0` everywhere (`neg_absDrift_nonneg`).
* `absK F m ε T = ∫_a^T (−absDrift)`: the time spent in `[a, T ∧ e_m]`, weighted by `−L₁u`.
* `integral_absK_le`: if `u ≤ c` on `{S ≤ ε}` (strip), then `E[K] ≤ c`. Proof: optional
  stopping for the martingale part of `u(Yf m)` at `h` and at `T` gives
  `E[K] = E[u(Y_a) − u(Y_T)]`, and `u(Y_a) ≤ c` when `h ≤ T`, `u ≥ 0`.
* `measure_absK_ge`: Markov, `P(K ≥ b) ≤ c/b`.
* `le_absK`: pathwise, if `−absDrift ≥ c'` on `[a, b] ⊆ [a, T]`, then `c'(b − a) ≤ K` (at every
  path where the drift is locally integrable, an a.s. property: `ae_integrableOn_absDrift`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualFeller

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.Transmission
open BlockBand.Transmission.DualLift BlockBand.Transmission.Dual
  BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

theorem min_coe_ne_top (T : ℝ≥0) (x : WithTop ℝ≥0) : min (T : WithTop ℝ≥0) x ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)

theorem untopA_min_le (T : ℝ≥0) (x : WithTop ℝ≥0) :
    (((min (T : WithTop ℝ≥0) x).untopA : ℝ≥0) : ℝ) ≤ T :=
  NNReal.coe_le_coe.2 ((WithTop.untopA_le_iff (min_coe_ne_top T x)).2 (min_le_left _ _))

theorem untopA_ofNN (s : ℝ≥0) : (s : WithTop ℝ≥0).untopA = s := rfl

theorem untopA_min_mono (T : ℝ≥0) {x y : WithTop ℝ≥0} (h : x ≤ y) :
    (((min (T : WithTop ℝ≥0) x).untopA : ℝ≥0) : ℝ) ≤ ((min (T : WithTop ℝ≥0) y).untopA : ℝ≥0) := by
  refine NNReal.coe_le_coe.2 ((WithTop.le_untopA_iff (min_coe_ne_top T y)).2 ?_)
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.1 (min_coe_ne_top T x)
  rw [← hv, untopA_ofNN, hv]
  exact min_le_min_left _ h

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ} (F : LiftFamily μ D0 ξ)

/-- The drift `1{t ≤ e_m} L₁u(Yf m t)` of `u(Yf m)`. -/
def absDrift (m : ℕ) : ℝ≥0 → LΩ S → ℝ :=
  switchOff (F.e m) (fun t ω => L₁ D0 absLyap (F.Yf m t ω))

/-- The start of the clock, `T ∧ hitS_m(ε)`. -/
def absStart (m : ℕ) (ε : ℝ) (T : ℝ≥0) (ω : LΩ S) : ℝ :=
  ((min (T : WithTop ℝ≥0) (F.hitS m ε ω)).untopA : ℝ≥0)

/-- `K = ∫_{T ∧ hitS_m(ε)}^T (−L₁u)(Yf m s) 1{s ≤ e_m} ds`. -/
def absK (m : ℕ) (ε : ℝ) (T : ℝ≥0) (ω : LΩ S) : ℝ :=
  ∫ s in absStart F m ε T ω..(T : ℝ), -absDrift F m s.toNNReal ω

theorem absStart_nonneg (m : ℕ) (ε : ℝ) (T : ℝ≥0) (ω : LΩ S) : 0 ≤ absStart F m ε T ω :=
  NNReal.coe_nonneg _

theorem absStart_le (m : ℕ) (ε : ℝ) (T : ℝ≥0) (ω : LΩ S) : absStart F m ε T ω ≤ T :=
  untopA_min_le T _

theorem neg_absDrift_nonneg (hD0 : 0 ≤ D0) (hξ : IsLiftStart μ ξ) (m : ℕ) (t : ℝ≥0)
    (ω : LΩ S) : 0 ≤ -absDrift F m t ω := by
  unfold absDrift switchOff
  split_ifs
  · exact neg_L₁_absLyap_nonneg hD0 (F.Yf_mem_strip hξ m t ω)
  · simp

theorem absK_nonneg (hD0 : 0 ≤ D0) (hξ : IsLiftStart μ ξ) (m : ℕ) (ε : ℝ) (T : ℝ≥0)
    (ω : LΩ S) : 0 ≤ absK F m ε T ω :=
  intervalIntegral.integral_nonneg (absStart_le F m ε T ω) fun _ _ =>
    neg_absDrift_nonneg F hD0 hξ m _ ω

theorem ae_integrableOn_absDrift (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (m : ℕ) :
    ∀ᵐ ω ∂LP μ, ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => absDrift F m s.toNNReal ω) (Ioc 0 t) := by
  filter_upwards [(F.isCSM_G hD0 hξ m measurable_absLyap contDiffOn_absLyap).integrable] with
    ω h t
  have h' := (h t).1 0
  exact h'

/-- **Pathwise lower bound for `K`.** -/
theorem le_absK (m : ℕ) (ε : ℝ) (T : ℝ≥0) {ω : LΩ S} (hD0 : 0 ≤ D0) (hξ : IsLiftStart μ ξ)
    (hi : IntegrableOn (fun s : ℝ => absDrift F m s.toNNReal ω) (Ioc 0 T)) {b c : ℝ}
    (hab : absStart F m ε T ω ≤ b) (hbT : b ≤ T)
    (hc : ∀ s ∈ Icc (absStart F m ε T ω) b, c ≤ -absDrift F m s.toNNReal ω) :
    c * (b - absStart F m ε T ω) ≤ absK F m ε T ω := by
  set a := absStart F m ε T ω with ha
  have ha0 : 0 ≤ a := absStart_nonneg F m ε T ω
  have hi' := hi.neg
  have h1 : IntervalIntegrable (fun s : ℝ => -absDrift F m s.toNNReal ω) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 (hi'.mono_set (Ioc_subset_Ioc ha0 hbT))
  have h2 : IntervalIntegrable (fun s : ℝ => -absDrift F m s.toNNReal ω) volume b T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hbT).2
      (hi'.mono_set (Ioc_subset_Ioc (ha0.trans hab) le_rfl))
  have e := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hn : 0 ≤ ∫ s in b..(T : ℝ), -absDrift F m s.toNNReal ω :=
    intervalIntegral.integral_nonneg hbT fun s _ => neg_absDrift_nonneg F hD0 hξ m _ ω
  have hm := intervalIntegral.integral_mono_on hab intervalIntegrable_const h1 hc
  rw [intervalIntegral.integral_const, smul_eq_mul] at hm
  unfold absK
  rw [← ha, ← e]
  linarith

/-- **Optional stopping: `E[K] ≤ c`.** -/
theorem integral_absK_le (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (m : ℕ) (ε : ℝ) (T : ℝ≥0)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ y ∈ flatStrip, tot y ≤ ε → absLyap y ≤ c) :
    Integrable (absK F m ε T) (LP μ) ∧ ∫ ω, absK F m ε T ω ∂LP μ ≤ c := by
  have H := F.isCSM_G hD0 hξ m measurable_absLyap contDiffOn_absLyap
  obtain ⟨M, hM, hMX⟩ := F.hasMart_G hD0 hξ m measurable_absLyap contDiffOn_absLyap
    (continuousOn_L₁_absLyap D0)
  set X : ℝ≥0 → LΩ S → ℝ := fun t ω => absLyap (F.Yf m t ω) - absLyap (F.Yf m 0 ω) -
    ∫ s in Ioc (0 : ℝ) t, absDrift F m s.toNNReal ω with hXdef
  have hMX' : ∀ t, M t =ᵐ[LP μ] X t := hMX
  have hcont : ∀ᵐ ω ∂LP μ, Continuous fun t => X t ω := by
    filter_upwards [H.continuous, H.integrable] with ω hω hi
    exact Semimartingale.continuous_smCompensated (i := 0)
      (Y := fun t ω (_ : Fin 1) => absLyap (F.Yf m t ω))
      (β := fun t ω (_ : Fin 1) => absDrift F m t ω) hω fun t => (hi t).1 0
  have hh := F.isStoppingTime_hitS hD0 hξ m ε
  obtain ⟨M', hM', hM'e⟩ := Semimartingale.exists_martingale_stoppedProcess hM hMX' hcont hh
  have hX0 : ∀ ω, X 0 ω = 0 := fun ω => by simp [hXdef]
  have hst0 : ∀ ω, stoppedProcess X (F.hitS m ε) 0 ω = 0 := fun ω => by
    simp only [stoppedProcess]
    rw [min_eq_left (by rw [WithTop.coe_zero]; exact bot_le)]
    exact hX0 ω
  have mean0 : ∀ {N : ℝ≥0 → LΩ S → ℝ} {Y : LΩ S → ℝ}, Martingale N (L𝓖 μ) (LP μ) →
      N 0 =ᵐ[LP μ] 0 → N T =ᵐ[LP μ] Y → ∫ ω, Y ω ∂LP μ = 0 := by
    intro N Y hN h0 hT
    have e := hN.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T) (MeasurableSet.univ)
    simp only [Measure.restrict_univ] at e
    rw [← integral_congr_ae hT, ← e, integral_congr_ae h0]
    simp
  have E1 : ∫ ω, X T ω ∂LP μ = 0 :=
    mean0 hM ((hMX' 0).trans (Eventually.of_forall fun ω => hX0 ω)) (hMX' T)
  have E2 : ∫ ω, stoppedProcess X (F.hitS m ε) T ω ∂LP μ = 0 :=
    mean0 hM' ((hM'e 0).trans (Eventually.of_forall fun ω => hst0 ω)) (hM'e T)
  have iX : Integrable (X T) (LP μ) := (hM.integrable T).congr (hMX' T)
  have iS : Integrable (stoppedProcess X (F.hitS m ε) T) (LP μ) :=
    (hM'.integrable T).congr (hM'e T)
  -- the bounded part `u(Y_a) − u(Y_T)`
  set D : LΩ S → ℝ := fun ω => absLyap (F.Yf m (min (T : WithTop ℝ≥0) (F.hitS m ε ω)).untopA ω) -
    absLyap (F.Yf m T ω) with hDdef
  have hpA : StronglyMeasurable fun ω =>
      absLyap (F.Yf m (min (T : WithTop ℝ≥0) (F.hitS m ε ω)).untopA ω) :=
    (continuous_apply 0).comp_stronglyMeasurable
      ((H.progressive.stronglyAdapted_stoppedProcess hh T).mono ((L𝓖 μ).le T))
  have hpT : StronglyMeasurable fun ω => absLyap (F.Yf m T ω) :=
    (continuous_apply 0).comp_stronglyMeasurable ((H.adapted T).mono ((L𝓖 μ).le T))
  have iD : Integrable D (LP μ) := by
    refine Integrable.of_bound (hpA.sub hpT).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    have h1 := absLyap_nonneg (F.Yf_mem_strip hξ m (min (T : WithTop ℝ≥0) (F.hitS m ε ω)).untopA ω)
    have h2 := absLyap_le_one (F.Yf_mem_strip hξ m (min (T : WithTop ℝ≥0) (F.hitS m ε ω)).untopA ω)
    have h3 := absLyap_nonneg (F.Yf_mem_strip hξ m T ω)
    have h4 := absLyap_le_one (F.Yf_mem_strip hξ m T ω)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> simp only [hDdef] <;> linarith
  have hDc : ∀ ω, D ω ≤ c := fun ω => by
    simp only [hDdef]
    rcases le_total (T : WithTop ℝ≥0) (F.hitS m ε ω) with hle | hle
    · rw [min_eq_left hle]; simp only [untopA_ofNN, sub_self]; exact hc0
    · obtain ⟨h₀, hh₀⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
      rw [min_eq_right hle, ← hh₀, untopA_ofNN]
      have hRc : ∀ t, Tendsto (fun u => F.Sp m u ω) (𝓝[≥] t) (𝓝 (F.Sp m t ω)) := fun t =>
        SolFamily.tendsto_nhdsGE_of_continuous (F.continuous_Sp m ω) t
      have hS₀ : F.Sp m h₀ ω ≤ ε := hitLe_attained hRc hh₀.symm
      have := hc _ (F.Yf_mem_strip hξ m h₀ ω) hS₀
      have := absLyap_nonneg (F.Yf_mem_strip hξ m T ω)
      linarith
  -- the pathwise identity `K = X_T − X_a + D`
  have hK : absK F m ε T =ᵐ[LP μ] fun ω => X T ω - stoppedProcess X (F.hitS m ε) T ω + D ω := by
    filter_upwards [ae_integrableOn_absDrift F hD0 hξ m] with ω hi
    set a := absStart F m ε T ω with ha
    have ha0 : 0 ≤ a := absStart_nonneg F m ε T ω
    have haT : a ≤ T := absStart_le F m ε T ω
    have h1 : IntervalIntegrable (fun s : ℝ => absDrift F m s.toNNReal ω) volume 0 a :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ha0).2
        ((hi T).mono_set (Ioc_subset_Ioc le_rfl haT))
    have h2 : IntervalIntegrable (fun s : ℝ => absDrift F m s.toNNReal ω) volume a T :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le haT).2
        ((hi T).mono_set (Ioc_subset_Ioc ha0 le_rfl))
    have e := intervalIntegral.integral_add_adjacent_intervals h1 h2
    rw [intervalIntegral.integral_of_le ha0, intervalIntegral.integral_of_le (NNReal.coe_nonneg T)]
      at e
    have eK : absK F m ε T ω = -∫ s in a..(T : ℝ), absDrift F m s.toNNReal ω := by
      unfold absK; rw [← ha, intervalIntegral.integral_neg]
    rw [eK]
    have ha' : (((min (T : WithTop ℝ≥0) (F.hitS m ε ω)).untopA : ℝ≥0) : ℝ) = a := rfl
    simp only [stoppedProcess, hXdef, hDdef, ha']
    linarith
  have iK : Integrable (absK F m ε T) (LP μ) := ((iX.sub iS).add iD).congr hK.symm
  refine ⟨iK, ?_⟩
  have e1 : ∫ ω, (X T ω - stoppedProcess X (F.hitS m ε) T ω + D ω) ∂LP μ =
      ∫ ω, (X T ω - stoppedProcess X (F.hitS m ε) T ω) ∂LP μ + ∫ ω, D ω ∂LP μ :=
    integral_add (iX.sub iS) iD
  have e2 : ∫ ω, (X T ω - stoppedProcess X (F.hitS m ε) T ω) ∂LP μ =
      ∫ ω, X T ω ∂LP μ - ∫ ω, stoppedProcess X (F.hitS m ε) T ω ∂LP μ := integral_sub iX iS
  rw [integral_congr_ae hK, e1, e2, E1, E2]
  have := integral_mono iD (integrable_const c) hDc
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
  linarith

/-- **Markov: `P(K ≥ b) ≤ c/b`.** -/
theorem measure_absK_ge (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (m : ℕ) (ε : ℝ) (T : ℝ≥0)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ y ∈ flatStrip, tot y ≤ ε → absLyap y ≤ c) {b : ℝ}
    (hb : 0 < b) : LP μ {ω | b ≤ absK F m ε T ω} ≤ ENNReal.ofReal (c / b) := by
  obtain ⟨hI, hle⟩ := integral_absK_le F hD0 hξ m ε T hc0 hc
  have h := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => absK_nonneg F hD0.le hξ m ε T ω) hI b
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (div_nonneg hc0 hb.le),
    le_div_iff₀ hb]
  rw [measureReal_def] at h
  linarith

end BlockBand.Transmission.DualFeller
