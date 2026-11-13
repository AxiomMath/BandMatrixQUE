module
public import BlockBand.Diffusion.Duality.NonAttain
public import BlockBand.Diffusion.Duality.EdgeTest
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The edges of the strip are entrance-type: null boundary time and immediate entry

## Main results

* `IsExBaseDiffusion.forall_mem_exOpenStrip`: if `z ∈ exOpenStrip`, a.s.
  `Z_s ∈ exOpenStrip` for all `s ≥ 0` (any real `D0`).
* `IsExBaseDiffusion.volume_boundary_eq_zero` (null boundary time): if `0 < D0`, a.s.
  for every `T`, the set of times `r ∈ (0, T]` with `Z_r ∉ exOpenStrip` is Lebesgue-null.
* `IsExBaseDiffusion.forall_pos_mem_exOpenStrip` (entrance): if `0 < D0`, a.s.
  `Z_s ∈ exOpenStrip` for all `s > 0` (boundary and corner starts included).
* `IsExBaseDiffusion.duality`, `IsExBaseDiffusion.condExp_duality`: space-time duality for the
  base diffusion from any start in the closed strip.
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

/-!
### A generic "approximate test" lemma
-/

section Generic

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
  {Zf : ℝ≥0 → Ω → Fin d → ℝ}

theorem isInteriorDomain_ball_univ (R : ℝ) :
    IsInteriorDomain (Metric.ball (0 : Fin d → ℝ) R) univ :=
  ⟨Metric.isOpen_ball, (isCompact_closedBall 0 R).of_isClosed_subset isClosed_closure
    Metric.closure_ball_subset_closedBall, subset_univ _⟩

/-- **Approximate tests.** If `φ_k ∈ C²` are uniformly small, their generators are bounded on a
set `S` containing the paths and converge there to `g ≥ 0`, then a.s.
`∫_{(0,T]} g(Z_r) dr = 0`. -/
theorem ae_setIntegral_eq_zero_of_approx (hZ : IsMPSolutionOn Q 𝓖 b a univ Zf)
    (hb : Continuous b) (ha : Continuous a) {S : Set (Fin d → ℝ)}
    (hpath : ∀ᵐ ω ∂Q, ∀ r, Zf r ω ∈ S) {φ : ℕ → (Fin d → ℝ) → ℝ}
    (hφ : ∀ k, ContDiff ℝ 2 (φ k)) {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) {C₀ : ℝ}
    (hcb : ∀ k, c k ≤ C₀) (hφc : ∀ k y, |φ k y| ≤ c k) {B : ℝ}
    (hB : ∀ k, ∀ y ∈ S, |mpGenerator b a (φ k) y| ≤ B)
    (hgc : ∀ k, Continuous (mpGenerator b a (φ k))) {g : (Fin d → ℝ) → ℝ}
    (hg0 : ∀ y ∈ S, 0 ≤ g y)
    (hlim : ∀ y ∈ S, Tendsto (fun k => mpGenerator b a (φ k) y) atTop (𝓝 (g y))) (T : ℝ≥0) :
    ∀ᵐ ω ∂Q, ∫ r in Ioc (0 : ℝ) T, g (Zf r.toNNReal ω) = 0 := by
  set L : ℕ → (Fin d → ℝ) → ℝ := fun k => mpGenerator b a (φ k) with hLdef
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hBS : ∀ k, ∀ y ∈ S, |L k y| ≤ B' := fun k y hy => (hB k y hy).trans (le_max_left _ _)
  have hc0 : ∀ k, 0 ≤ c k := fun k => (abs_nonneg _).trans (hφc k 0)
  -- the target values
  set Y : ℕ → Ω → ℝ := fun k ω => φ k (Zf T ω) - φ k (Zf 0 ω) -
    ∫ r in Ioc (0 : ℝ) T, L k (Zf r.toNNReal ω) with hYdef
  have hgood : ∀ᵐ ω ∂Q, Continuous (fun r => Zf r ω) ∧ ∀ r, Zf r ω ∈ S := by
    filter_upwards [hZ.continuous, hpath] with ω h1 h2 using ⟨h1, h2⟩
  -- first, `E[Y_k] = 0` and `Y_k` is a.e. strongly measurable
  have step1 : ∀ k, AEStronglyMeasurable (Y k) Q ∧ ∫ ω, Y k ω ∂Q = 0 := by
    intro k
    have hM : ∀ R : ℕ, ∃ M : ℝ≥0 → Ω → ℝ, Martingale M 𝓖 Q ∧ ∀ t,
        M t =ᵐ[Q] stoppedProcess (fun t ω => φ k (Zf t ω) - φ k (Zf 0 ω) -
          ∫ s in Ioc (0 : ℝ) t, mpGenerator b a (φ k) (Zf s.toNNReal ω))
          (exitTimeFrom (Metric.ball 0 R) Zf) t := fun R =>
      GramUniqueness.martingaleProblemItoU_holds d Ω Q 𝓖 b a univ isOpen_univ hb.continuousOn
        ha.continuousOn Zf hZ (φ k) (hφ k).contDiffOn _ (isInteriorDomain_ball_univ R)
    choose M hM hMe using hM
    set X : ℕ → Ω → ℝ := fun R ω => stoppedProcess (fun t ω => φ k (Zf t ω) - φ k (Zf 0 ω) -
      ∫ s in Ioc (0 : ℝ) t, mpGenerator b a (φ k) (Zf s.toNNReal ω))
      (exitTimeFrom (Metric.ball 0 R) Zf) T ω with hXdef
    have hXm : ∀ R, AEStronglyMeasurable (X R) Q := fun R =>
      (((hM R).1 T).mono (𝓖.le T)).aestronglyMeasurable.congr (hMe R T)
    have hX0 : ∀ R, ∫ ω, X R ω ∂Q = 0 := fun R => by
      have h1 : ∫ ω, M R T ω ∂Q = ∫ ω, M R 0 ω ∂Q := by
        have := (hM R).setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T) (MeasurableSet.univ (m := 𝓖 0))
        simpa only [Measure.restrict_univ] using this.symm
      have h0 : ∫ ω, M R 0 ω ∂Q = 0 := by
        rw [integral_congr_ae (hMe R 0)]
        simp [stoppedProcess_eq_stopTime, stopTime_zero]
      rw [integral_congr_ae (EventuallyEq.symm (hMe R T)), h1, h0]
    have hpw : ∀ ω, Continuous (fun r => Zf r ω) → (∀ r, Zf r ω ∈ S) →
        Tendsto (fun R : ℕ => X R ω) atTop (𝓝 (Y k ω)) ∧
          ∀ R, |X R ω| ≤ 2 * C₀ + B' * T := by
      intro ω hc hS
      refine ⟨?_, fun R => ?_⟩
      · obtain ⟨Bp, hBp⟩ :=
          (isCompact_Icc (a := (0 : ℝ≥0)) (b := T + 1)).exists_bound_of_continuousOn
            hc.continuousOn
        obtain ⟨R₀, hR₀⟩ := exists_nat_gt Bp
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop R₀] with R hR
        have hlt : ((T : ℝ≥0) : WithTop ℝ≥0) < exitTimeFrom (Metric.ball 0 R) Zf ω := by
          refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 (lt_add_one T)) (le_iInf₂ fun r hr => ?_)
          by_contra hlt
          push Not at hlt
          have hb := hBp r ⟨zero_le, (WithTop.coe_lt_coe.1 hlt).le⟩
          apply hr
          rw [Metric.mem_ball, dist_zero_right]
          have : (R₀ : ℝ) ≤ R := by exact_mod_cast hR
          linarith
        simp only [hXdef, hYdef, hLdef, stoppedProcess_eq_stopTime, stopTime_of_lt hlt]
      · simp only [hXdef, stoppedProcess_eq_stopTime]
        set σ := stopTime (exitTimeFrom (Metric.ball 0 R) Zf ω) T
        have h1 : |φ k (Zf σ ω)| ≤ C₀ := (hφc k _).trans (hcb k)
        have h2 : |φ k (Zf 0 ω)| ≤ C₀ := (hφc k _).trans (hcb k)
        have h3 : ‖∫ s in Ioc (0 : ℝ) σ, mpGenerator b a (φ k) (Zf s.toNNReal ω)‖ ≤
            B' * volume.real (Ioc (0 : ℝ) σ) :=
          norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top fun r _ => by
            rw [Real.norm_eq_abs]; exact hBS k _ (hS _)
        have h4 : volume.real (Ioc (0 : ℝ) σ) ≤ T := by
          simp only [Measure.real, Real.volume_Ioc, sub_zero,
            ENNReal.toReal_ofReal (NNReal.coe_nonneg _)]
          exact_mod_cast stopTime_le _ _
        rw [Real.norm_eq_abs] at h3
        have h5 : B' * volume.real (Ioc (0 : ℝ) σ) ≤ B' * T := mul_le_mul_of_nonneg_left h4 hB'0
        calc _ ≤ |φ k (Zf σ ω)| + |φ k (Zf 0 ω)| +
              |∫ s in Ioc (0 : ℝ) σ, mpGenerator b a (φ k) (Zf s.toNNReal ω)| := by
              have := abs_sub (φ k (Zf σ ω) - φ k (Zf 0 ω))
                (∫ s in Ioc (0 : ℝ) σ, mpGenerator b a (φ k) (Zf s.toNNReal ω))
              have := abs_sub (φ k (Zf σ ω)) (φ k (Zf 0 ω))
              linarith
          _ ≤ 2 * C₀ + B' * T := by linarith
    have hlimX : ∀ᵐ ω ∂Q, Tendsto (fun R : ℕ => X R ω) atTop (𝓝 (Y k ω)) :=
      hgood.mono fun ω h => (hpw ω h.1 h.2).1
    have hYm : AEStronglyMeasurable (Y k) Q := aestronglyMeasurable_of_tendsto_ae atTop hXm hlimX
    refine ⟨hYm, ?_⟩
    have hT := tendsto_integral_of_dominated_convergence (μ := Q) (fun _ => 2 * C₀ + B' * T)
      hXm (integrable_const _) (fun R => hgood.mono fun ω h => by
        rw [Real.norm_eq_abs]; exact (hpw ω h.1 h.2).2 R) hlimX
    simp only [hX0] at hT
    exact tendsto_nhds_unique hT tendsto_const_nhds
  -- then let `k → ∞`
  set F : Ω → ℝ := fun ω => ∫ r in Ioc (0 : ℝ) T, g (Zf r.toNNReal ω) with hFdef
  have hgB : ∀ y ∈ S, |g y| ≤ B' := fun y hy =>
    le_of_tendsto' ((continuous_abs.tendsto _).comp (hlim y hy)) fun k => hBS k y hy
  have hpw2 : ∀ ω, Continuous (fun r => Zf r ω) → (∀ r, Zf r ω ∈ S) →
      Tendsto (fun k => Y k ω) atTop (𝓝 (-F ω)) := by
    intro ω hcont hS
    have hφ0 : ∀ y, Tendsto (fun k => φ k y) atTop (𝓝 0) := fun y =>
      squeeze_zero_norm (fun k => by rw [Real.norm_eq_abs]; exact hφc k y) hc
    have hpath : Continuous fun r : ℝ => Zf r.toNNReal ω := hcont.comp continuous_real_toNNReal
    have hI : Tendsto (fun k => ∫ r in Ioc (0 : ℝ) T, L k (Zf r.toNNReal ω)) atTop (𝓝 (F ω)) :=
      tendsto_integral_of_dominated_convergence (fun _ => B')
        (fun k => ((hgc k).comp hpath).aestronglyMeasurable) (integrable_const _)
        (fun k => Eventually.of_forall fun r => by
          rw [Real.norm_eq_abs]; exact hBS k _ (hS _))
        (Eventually.of_forall fun r => hlim _ (hS _))
    have := ((hφ0 (Zf T ω)).sub (hφ0 (Zf 0 ω))).sub hI
    simpa [hYdef] using this
  have hlimY : ∀ᵐ ω ∂Q, Tendsto (fun k => Y k ω) atTop (𝓝 (-F ω)) :=
    hgood.mono fun ω h => hpw2 ω h.1 h.2
  have hIb : ∀ ω, (∀ r, Zf r ω ∈ S) → ∀ {G : (Fin d → ℝ) → ℝ}, (∀ y ∈ S, |G y| ≤ B') →
      |∫ r in Ioc (0 : ℝ) T, G (Zf r.toNNReal ω)| ≤ B' * T := fun ω hS G hG => by
    have h3 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) T)
      (f := fun r => G (Zf r.toNNReal ω)) measure_Ioc_lt_top fun r _ => by
        rw [Real.norm_eq_abs]; exact hG _ (hS _)
    simpa only [Real.norm_eq_abs, Measure.real, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal (NNReal.coe_nonneg _)] using h3
  have hYb : ∀ k, ∀ᵐ ω ∂Q, ‖Y k ω‖ ≤ 2 * C₀ + B' * T := fun k => hgood.mono fun ω h => by
    rw [Real.norm_eq_abs]
    have h1 : |φ k (Zf T ω)| ≤ C₀ := (hφc k _).trans (hcb k)
    have h2 : |φ k (Zf 0 ω)| ≤ C₀ := (hφc k _).trans (hcb k)
    have h3 := hIb ω h.2 (G := L k) (hBS k)
    have := abs_sub (φ k (Zf T ω) - φ k (Zf 0 ω)) (∫ r in Ioc (0 : ℝ) T, L k (Zf r.toNNReal ω))
    have := abs_sub (φ k (Zf T ω)) (φ k (Zf 0 ω))
    simp only [hYdef]
    linarith
  have hFm : AEStronglyMeasurable F Q := by
    have h := (aestronglyMeasurable_of_tendsto_ae atTop (fun k => (step1 k).1) hlimY).neg
    exact h.congr (ae_of_all _ fun ω => by simp)
  have hT := tendsto_integral_of_dominated_convergence (μ := Q) (fun _ => 2 * C₀ + B' * T)
    (fun k => (step1 k).1) (integrable_const _) hYb hlimY
  have e : (fun k => ∫ ω, Y k ω ∂Q) = fun _ => 0 := funext fun k => (step1 k).2
  rw [e] at hT
  have hint : ∫ ω, -F ω ∂Q = 0 := tendsto_nhds_unique hT tendsto_const_nhds
  have hF0 : 0 ≤ᵐ[Q] F := hgood.mono fun ω h =>
    setIntegral_nonneg measurableSet_Ioc fun r _ => hg0 _ (h.2 _)
  have hFi : Integrable F Q := Integrable.of_bound hFm (B' * T) (hgood.mono fun ω h => by
    rw [Real.norm_eq_abs]; exact hIb ω h.2 hgB)
  have hF : ∫ ω, F ω ∂Q = 0 := by
    rw [integral_neg] at hint; linarith
  exact (integral_eq_zero_iff_of_nonneg_ae hF0 hFi).1 hF

end Generic

/-!
### Edge tests: uniform bounds and the limit `(D₀/2) 1{ℓ = 0}`
-/

/-- The closed strip in `Fin 2` coordinates. -/
def closedStripFin : Set (Fin 2 → ℝ) := {y | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 1 ≤ 1}

theorem edge_bound_limit {S : Set (Fin 2 → ℝ)} {ℓ c1 c2 : (Fin 2 → ℝ) → ℝ}
    {F : ℝ → (Fin 2 → ℝ) → ℝ}
    (hF : ∀ ε, 0 < ε → ∀ y ∈ S, F ε y = c1 y * deriv edgePsi (ℓ y / ε) +
      c2 y * (ℓ y / ε * deriv (deriv edgePsi) (ℓ y / ε)))
    (hℓ : ∀ y ∈ S, 0 ≤ ℓ y) {K : ℝ} (hK : ∀ y ∈ S, ℓ y ≤ 2 → |c1 y| ≤ K ∧ |c2 y| ≤ K)
    {κ : ℝ} (hκ : ∀ y ∈ S, ℓ y = 0 → c1 y = κ) :
    (∃ B, ∀ k : ℕ, ∀ y ∈ S, |F (1 / ((k : ℝ) + 1)) y| ≤ B) ∧
      ∀ y ∈ S, Tendsto (fun k : ℕ => F (1 / ((k : ℝ) + 1)) y) atTop
        (𝓝 ({z | ℓ z = 0}.indicator (fun _ => κ) y)) := by
  obtain ⟨C1, hC10, hC1⟩ := exists_bound_deriv_edgePsi
  obtain ⟨C2, hC20, hC2⟩ := exists_bound_mul_deriv2_edgePsi
  have hεpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hεle : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hzero : ∀ ε, 0 < ε → ∀ y ∈ S, 2 < ℓ y / ε → F ε y = 0 := fun ε hε y hy hs => by
    have hs' : 2 < |ℓ y / ε| := by rwa [abs_of_nonneg (div_nonneg (hℓ y hy) hε.le)]
    rw [hF ε hε y hy, deriv_edgePsi_eq_zero hs', deriv2_edgePsi_eq_zero hs']
    ring
  refine ⟨⟨|K| * C1 + |K| * C2, fun k y hy => ?_⟩, fun y hy => ?_⟩
  · set ε := 1 / ((k : ℝ) + 1)
    by_cases hs : 2 < ℓ y / ε
    · rw [hzero ε (hεpos k) y hy hs, abs_zero]; positivity
    · push Not at hs
      have hl : ℓ y ≤ 2 := by
        have := (div_le_iff₀ (hεpos k)).1 hs
        nlinarith [hεle k, hℓ y hy]
      obtain ⟨h1, h2⟩ := hK y hy hl
      rw [hF ε (hεpos k) y hy]
      calc _ ≤ |c1 y * deriv edgePsi (ℓ y / ε)| +
            |c2 y * (ℓ y / ε * deriv (deriv edgePsi) (ℓ y / ε))| := abs_add_le _ _
        _ ≤ |K| * C1 + |K| * C2 := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul (h1.trans (le_abs_self _)) (hC1 _) (abs_nonneg _)
            (abs_nonneg _)) (mul_le_mul (h2.trans (le_abs_self _)) (hC2 _) (abs_nonneg _)
            (abs_nonneg _))
  · by_cases h0 : ℓ y = 0
    · rw [indicator_of_mem (show y ∈ {z | ℓ z = 0} from h0)]
      refine tendsto_const_nhds.congr fun k => ?_
      rw [hF _ (hεpos k) y hy, h0, zero_div, deriv_edgePsi_zero, hκ y hy h0]
      ring
    · rw [indicator_of_notMem (show y ∉ {z | ℓ z = 0} from h0)]
      have hpos : 0 < ℓ y := lt_of_le_of_ne (hℓ y hy) (Ne.symm h0)
      obtain ⟨k₀, hk₀⟩ := exists_nat_gt (2 / ℓ y)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop k₀] with k hk
      refine (hzero _ (hεpos k) y hy ?_).symm
      rw [div_div_eq_mul_div, div_one]
      have : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
      rw [div_lt_iff₀ hpos] at hk₀
      nlinarith

section Edge

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ}
  {Zf : ℝ≥0 → Ω → Fin 2 → ℝ}

/-- **Null time on one edge.** -/
theorem ae_volume_edge_eq_zero (hZ : IsMPSolutionOn Q 𝓖 (baseDrift D0) (baseCov D0) univ Zf)
    (hD0 : 0 < D0) (hpath : ∀ᵐ ω ∂Q, ∀ r, Zf r ω ∈ closedStripFin)
    {ℓ c1 c2 : (Fin 2 → ℝ) → ℝ} (hℓc : Continuous ℓ) {φ : ℝ → (Fin 2 → ℝ) → ℝ}
    (hφ : ∀ ε, ContDiff ℝ 2 (φ ε)) {Cφ : ℝ} (hφb : ∀ ε, 0 < ε → ∀ y, |φ ε y| ≤ ε * Cφ)
    (hgc : ∀ ε, 0 < ε → Continuous (mpGenerator (baseDrift D0) (baseCov D0) (φ ε)))
    (hF : ∀ ε, 0 < ε → ∀ y ∈ closedStripFin, mpGenerator (baseDrift D0) (baseCov D0) (φ ε) y =
      c1 y * deriv edgePsi (ℓ y / ε) + c2 y * (ℓ y / ε * deriv (deriv edgePsi) (ℓ y / ε)))
    (hℓ : ∀ y ∈ closedStripFin, 0 ≤ ℓ y) {K : ℝ}
    (hK : ∀ y ∈ closedStripFin, ℓ y ≤ 2 → |c1 y| ≤ K ∧ |c2 y| ≤ K)
    (hκ : ∀ y ∈ closedStripFin, ℓ y = 0 → c1 y = D0 / 2) (T : ℝ≥0) :
    ∀ᵐ ω ∂Q, volume ({r : ℝ | ℓ (Zf r.toNNReal ω) = 0} ∩ Ioc 0 T) = 0 := by
  obtain ⟨⟨B, hB⟩, hlim⟩ := edge_bound_limit (F := fun ε => mpGenerator (baseDrift D0)
    (baseCov D0) (φ ε)) hF hℓ hK hκ
  have hεpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hCφ : 0 ≤ Cφ := by
    have := (abs_nonneg _).trans (hφb 1 one_pos 0)
    linarith
  have hlimc : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1) * Cφ) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).mul_const Cφ
    simpa using this
  have hmain := ae_setIntegral_eq_zero_of_approx hZ (continuous_baseDrift D0)
    (continuous_baseCov D0) hpath (φ := fun k => φ (1 / ((k : ℝ) + 1))) (fun k => hφ _) hlimc
    (C₀ := Cφ) (fun k => by
      have : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
      nlinarith)
    (fun k y => hφb _ (hεpos k) y) hB (fun k => hgc _ (hεpos k))
    (g := {z | ℓ z = 0}.indicator fun _ => D0 / 2)
    (fun y _ => by
      by_cases h : y ∈ {z | ℓ z = 0}
      · rw [indicator_of_mem h]; positivity
      · rw [indicator_of_notMem h])
    hlim T
  filter_upwards [hmain, hZ.continuous] with ω hω hc
  have hpc : Continuous fun r : ℝ => Zf r.toNNReal ω := hc.comp continuous_real_toNNReal
  have hms : MeasurableSet {r : ℝ | ℓ (Zf r.toNNReal ω) = 0} :=
    (isClosed_eq (hℓc.comp hpc) continuous_const).measurableSet
  have e : (fun r : ℝ => ({z | ℓ z = 0}.indicator (fun _ => D0 / 2)) (Zf r.toNNReal ω)) =
      {r : ℝ | ℓ (Zf r.toNNReal ω) = 0}.indicator fun _ => D0 / 2 := by
    funext r; simp [indicator_apply]
  rw [e, integral_indicator_const _ hms, Measure.real, Measure.restrict_apply hms,
    smul_eq_mul, mul_eq_zero] at hω
  rcases hω with h | h
  · exact (ENNReal.toReal_eq_zero_iff _).1 h |>.resolve_right
      (ne_of_lt ((measure_mono inter_subset_right).trans_lt measure_Ioc_lt_top))
  · linarith

end Edge

/-!
### Main results for the base diffusion
-/

/-- The open strip `(0, ∞) × (0, 1)`. -/
def exOpenStrip : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioo 0 1

theorem baseFin_mem_openStripFin_iff {Ω : Type*} {Z : ℝ≥0 → Ω → ℝ × ℝ} {s : ℝ≥0} {ω : Ω} :
    baseFin Z s ω ∈ openStripFin ↔ Z s ω ∈ exOpenStrip := Iff.rfl

theorem baseFin_mem_closedStripFin_iff {Ω : Type*} {Z : ℝ≥0 → Ω → ℝ × ℝ} {s : ℝ≥0} {ω : Ω} :
    baseFin Z s ω ∈ closedStripFin ↔ Z s ω ∈ exBaseStrip := Iff.rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {z : ℝ × ℝ}
  {Z : ℝ≥0 → Ω → ℝ × ℝ}

/-- **The open strip is invariant.** From a start in the open strip, the base diffusion stays in the open strip. -/
theorem IsExBaseDiffusion.forall_mem_exOpenStrip (h : IsExBaseDiffusion P 𝓖 D0 z Z)
    (hz : z ∈ exOpenStrip) : ∀ᵐ ω ∂P, ∀ s, Z s ω ∈ exOpenStrip := by
  have := h.prob
  filter_upwards [stays_openStripFin h.isTestMPSolution 0, h.start] with ω h1 h2 s
  exact h1 (by rw [baseFin_mem_openStripFin_iff, h2]; exact hz) s zero_le

/-- **Null boundary time**: for `D₀ > 0`, a.s. for every `T` the set of times `r ∈ (0, T]` with
`Z_r ∉ exOpenStrip` is Lebesgue-null. -/
theorem IsExBaseDiffusion.volume_boundary_eq_zero (h : IsExBaseDiffusion P 𝓖 D0 z Z)
    (hD0 : 0 < D0) : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      volume ({r : ℝ | Z r.toNNReal ω ∉ exOpenStrip} ∩ Ioc 0 T) = 0 := by
  have := h.prob
  have hT := h.isTestMPSolution
  have hM := hT.isMPSolutionOn isOpen_univ (continuous_baseDrift D0).continuousOn
    (continuous_baseCov D0).continuousOn fun y _ i j => baseCov_symm D0 y i j
  have hpath : ∀ᵐ ω ∂P, ∀ r, baseFin Z r ω ∈ closedStripFin :=
    h.paths.mono fun ω hω r => hω.2 r
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_bound_edgePsi
  have hb : ∀ ε, 0 < ε → ∀ x, |ε * edgePsi x| ≤ ε * Cψ := fun ε hε x => by
    rw [abs_mul, abs_of_pos hε]; exact mul_le_mul_of_nonneg_left (hCψ _) hε.le
  -- the three edges
  have hX : ∀ T : ℝ≥0, ∀ᵐ ω ∂P,
      volume ({r : ℝ | (fun y : Fin 2 → ℝ => y 0) (baseFin Z r.toNNReal ω) = 0} ∩ Ioc 0 T) = 0 :=
    fun T => ae_volume_edge_eq_zero hM hD0 hpath (continuous_apply 0) (φ := edgeFunX)
      contDiff_edgeFunX (Cφ := Cψ) (fun ε hε y => by
        simpa [edgeFunX] using hb ε hε ((1 * y 0 + 0) / ε))
      (fun ε hε => by
        rw [show mpGenerator (baseDrift D0) (baseCov D0) (edgeFunX ε) = fun y =>
          D0 / 2 * (1 + 2 * y 0) * deriv edgePsi (y 0 / ε) +
            1 / 2 * (D0 * (y 0 * (1 + y 0)) * (deriv (deriv edgePsi) (y 0 / ε) / ε)) from
          funext (mpGenerator_edgeFunX D0 ε hε.ne')]
        have h1 := continuous_deriv_edgePsi
        have h2 := continuous_deriv2_edgePsi
        fun_prop)
      (c1 := fun y => D0 / 2 * (1 + 2 * y 0)) (c2 := fun y => D0 / 2 * (1 + y 0))
      (fun ε hε y _ => by rw [mpGenerator_edgeFunX D0 ε hε.ne']; ring)
      (fun y hy => hy.1) (K := 3 * |D0|)
      (fun y hy hl => by
        have h0 := hy.1
        constructor
        · rw [abs_mul, abs_div, abs_two, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + 2 * y 0)]
          nlinarith [abs_nonneg D0]
        · rw [abs_mul, abs_div, abs_two, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + y 0)]
          nlinarith [abs_nonneg D0])
      (fun y _ h0 => by have h0' : y 0 = 0 := h0; rw [h0']; ring) T
  have hY0 : ∀ T : ℝ≥0, ∀ᵐ ω ∂P,
      volume ({r : ℝ | (fun y : Fin 2 → ℝ => y 1) (baseFin Z r.toNNReal ω) = 0} ∩ Ioc 0 T) = 0 :=
    fun T => ae_volume_edge_eq_zero hM hD0 hpath (continuous_apply 1) (φ := edgeFunY0)
      contDiff_edgeFunY0 (Cφ := Cψ) (fun ε hε y => by
        simpa [edgeFunY0] using hb ε hε ((1 * y 1 + 0) / ε))
      (fun ε hε => by
        rw [show mpGenerator (baseDrift D0) (baseCov D0) (edgeFunY0 ε) = fun y =>
          D0 / 2 * (1 - 2 * y 1) * deriv edgePsi (y 1 / ε) +
            1 / 2 * (D0 * (y 1 * (1 - y 1)) * (deriv (deriv edgePsi) (y 1 / ε) / ε)) from
          funext (mpGenerator_edgeFunY0 D0 ε hε.ne')]
        have h1 := continuous_deriv_edgePsi
        have h2 := continuous_deriv2_edgePsi
        fun_prop)
      (c1 := fun y => D0 / 2 * (1 - 2 * y 1)) (c2 := fun y => D0 / 2 * (1 - y 1))
      (fun ε hε y _ => by rw [mpGenerator_edgeFunY0 D0 ε hε.ne']; ring)
      (fun y hy => hy.2.1) (K := |D0|)
      (fun y hy _ => by
        obtain ⟨-, h1, h2⟩ := hy
        constructor
        · rw [abs_mul, abs_div, abs_two]
          have : |1 - 2 * y 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
          nlinarith [abs_nonneg D0, abs_nonneg (1 - 2 * y 1)]
        · rw [abs_mul, abs_div, abs_two, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - y 1)]
          nlinarith [abs_nonneg D0])
      (fun y _ h0 => by have h0' : y 1 = 0 := h0; rw [h0']; ring) T
  have hY1 : ∀ T : ℝ≥0, ∀ᵐ ω ∂P,
      volume ({r : ℝ | (fun y : Fin 2 → ℝ => 1 - y 1) (baseFin Z r.toNNReal ω) = 0} ∩
        Ioc 0 T) = 0 :=
    fun T => ae_volume_edge_eq_zero hM hD0 hpath (ℓ := fun y => 1 - y 1)
      (continuous_const.sub (continuous_apply 1)) (φ := edgeFunY1) contDiff_edgeFunY1 (Cφ := Cψ)
      (fun ε hε y => by
        simpa [edgeFunY1] using hb ε hε ((-1 * y 1 + 1) / ε))
      (fun ε hε => by
        rw [show mpGenerator (baseDrift D0) (baseCov D0) (edgeFunY1 ε) = fun y =>
          -(D0 / 2 * (1 - 2 * y 1) * deriv edgePsi ((1 - y 1) / ε)) +
            1 / 2 * (D0 * (y 1 * (1 - y 1)) * (deriv (deriv edgePsi) ((1 - y 1) / ε) / ε)) from
          funext (mpGenerator_edgeFunY1 D0 ε hε.ne')]
        have h1 := continuous_deriv_edgePsi
        have h2 := continuous_deriv2_edgePsi
        fun_prop)
      (c1 := fun y => -(D0 / 2 * (1 - 2 * y 1))) (c2 := fun y => D0 / 2 * y 1)
      (fun ε hε y _ => by rw [mpGenerator_edgeFunY1 D0 ε hε.ne']; ring)
      (fun y hy => by have := hy.2.2; linarith) (K := |D0|)
      (fun y hy _ => by
        obtain ⟨-, h1, h2⟩ := hy
        constructor
        · rw [abs_neg, abs_mul, abs_div, abs_two]
          have : |1 - 2 * y 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
          nlinarith [abs_nonneg D0, abs_nonneg (1 - 2 * y 1)]
        · rw [abs_mul, abs_div, abs_two, abs_of_nonneg h1]
          nlinarith [abs_nonneg D0])
      (fun y _ h0 => by
        have h0' : y 1 = 1 := by have : 1 - y 1 = 0 := h0; linarith
        rw [h0']; ring) T
  have hall : ∀ᵐ ω ∂P, ∀ T : ℕ,
      volume ({r : ℝ | (fun y : Fin 2 → ℝ => y 0) (baseFin Z r.toNNReal ω) = 0} ∩
        Ioc 0 (T : ℝ≥0)) = 0 ∧
      volume ({r : ℝ | (fun y : Fin 2 → ℝ => y 1) (baseFin Z r.toNNReal ω) = 0} ∩
        Ioc 0 (T : ℝ≥0)) = 0 ∧
      volume ({r : ℝ | (fun y : Fin 2 → ℝ => 1 - y 1) (baseFin Z r.toNNReal ω) = 0} ∩
        Ioc 0 (T : ℝ≥0)) = 0 :=
    ae_all_iff.2 fun T => ((hX T).and ((hY0 T).and (hY1 T)))
  filter_upwards [hall, h.paths] with ω hω hp T
  obtain ⟨N, hN⟩ := exists_nat_ge (T : ℝ)
  obtain ⟨h0, h1, h2⟩ := hω N
  set A0 := {r : ℝ | baseFin Z r.toNNReal ω 0 = 0} ∩ Ioc 0 ((N : ℝ≥0) : ℝ)
  set A1 := {r : ℝ | baseFin Z r.toNNReal ω 1 = 0} ∩ Ioc 0 ((N : ℝ≥0) : ℝ)
  set A2 := {r : ℝ | 1 - baseFin Z r.toNNReal ω 1 = 0} ∩ Ioc 0 ((N : ℝ≥0) : ℝ)
  have hsub : {r : ℝ | Z r.toNNReal ω ∉ exOpenStrip} ∩ Ioc 0 T ⊆ A0 ∪ A1 ∪ A2 := ?_
  · refine le_antisymm ?_ zero_le
    calc volume ({r : ℝ | Z r.toNNReal ω ∉ exOpenStrip} ∩ Ioc 0 T)
        ≤ volume (A0 ∪ A1 ∪ A2) := measure_mono hsub
      _ ≤ volume (A0 ∪ A1) + volume A2 := measure_union_le _ _
      _ ≤ volume A0 + volume A1 + volume A2 := by gcongr; exact measure_union_le _ _
      _ = 0 := by
        have e0 : volume A0 = 0 := h0
        have e1 : volume A1 = 0 := h1
        have e2 : volume A2 = 0 := h2
        rw [e0, e1, e2]; simp
  rintro r ⟨hr, hrT⟩
  have hrN : r ∈ Ioc (0 : ℝ) ((N : ℝ≥0) : ℝ) := ⟨hrT.1, hrT.2.trans (by simpa using hN)⟩
  have hcl := hp.2 r.toNNReal
  simp only [mem_ofPred_eq] at hr
  rw [← baseFin_mem_openStripFin_iff] at hr
  rw [← baseFin_mem_closedStripFin_iff] at hcl
  obtain ⟨c0, c1, c2⟩ := hcl
  simp only [openStripFin, mem_ofPred_eq, not_and_or, not_lt] at hr
  rcases hr with h | h | h
  · exact Or.inl (Or.inl ⟨le_antisymm h c0, hrN⟩)
  · exact Or.inl (Or.inr ⟨le_antisymm h c1, hrN⟩)
  · exact Or.inr ⟨by simp only [mem_ofPred_eq]; linarith, hrN⟩

/-- **Entrance.** For `D₀ > 0`, from any start in the closed strip, a.s. the base
diffusion is in the open strip at every positive time. -/
theorem IsExBaseDiffusion.forall_pos_mem_exOpenStrip (h : IsExBaseDiffusion P 𝓖 D0 z Z)
    (hD0 : 0 < D0) : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s → Z s ω ∈ exOpenStrip := by
  have := h.prob
  have hrest : ∀ᵐ ω ∂P, ∀ q : ℚ, baseFin Z (q : ℝ).toNNReal ω ∈ openStripFin →
      ∀ r, (q : ℝ).toNNReal ≤ r → baseFin Z r ω ∈ openStripFin :=
    ae_all_iff.2 fun q => stays_openStripFin h.isTestMPSolution _
  filter_upwards [hrest, h.volume_boundary_eq_zero hD0, h.paths] with ω hq hvol hp s hs
  have hpc : Continuous fun r : ℝ => Z r.toNNReal ω := hp.1.comp continuous_real_toNNReal
  -- some time in `(0, s)` is spent in the open strip
  have hne : ∃ r ∈ Ioo (0 : ℝ) s, Z r.toNNReal ω ∈ exOpenStrip := by
    by_contra hcon
    push Not at hcon
    have hsub : Ioo (0 : ℝ) s ⊆ {r : ℝ | Z r.toNNReal ω ∉ exOpenStrip} ∩ Ioc 0 s :=
      fun r hr => ⟨hcon r hr, hr.1, hr.2.le⟩
    have := measure_mono (μ := volume) hsub
    rw [hvol s, Real.volume_Ioo, sub_zero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
    exact absurd hs (not_lt.2 (by exact_mod_cast this))
  obtain ⟨r₀, hr₀, hr₀O⟩ := hne
  have hGo : IsOpen {r : ℝ | Z r.toNNReal ω ∈ exOpenStrip} :=
    ((isOpen_Ioi.prod isOpen_Ioo).preimage hpc)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hGo.inter isOpen_Ioo) r₀ ⟨hr₀O, hr₀⟩
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right r₀ hδ)
  have hqm : (q : ℝ) ∈ {r : ℝ | Z r.toNNReal ω ∈ exOpenStrip} ∩ Ioo 0 (s : ℝ) := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
    linarith)
  have hqs : (q : ℝ).toNNReal ≤ s := by
    rw [Real.toNNReal_le_iff_le_coe]; exact hqm.2.2.le
  exact hq q hqm.1 s hqs

/-!
### Space-time duality for the base diffusion
-/

theorem IsExBaseDiffusion.isTestMP_args (h : IsExBaseDiffusion P 𝓖 D0 z Z) (hD0 : 0 < D0)
    (t : ℝ≥0) :
    IsTestMPSolution P 𝓖 (baseDrift D0) (baseCov D0) univ (baseFin Z) ∧
      (∀ᵐ ω ∂P, baseFin Z 0 ω = finProd.symm z) ∧
      ∀ᵐ ω ∂P, ∀ r, 0 < r → r ≤ t → baseFin Z r ω ∈ openStripFin :=
  ⟨h.isTestMPSolution, h.start.mono fun ω hω => by simp [baseFin, hω],
    (h.forall_pos_mem_exOpenStrip hD0).mono fun ω hω r hr _ => hω r hr⟩

section BaseDuality

variable (h : IsExBaseDiffusion P 𝓖 D0 z Z) (hD0 : 0 < D0) {t : ℝ≥0}
  {u : ℝ × (Fin 2 → ℝ) → ℝ} (hu2 : ContDiffOn ℝ 2 u (Ioo 0 (t : ℝ) ×ˢ openStripFin))
  (hpde : ∀ p ∈ Ioo 0 (t : ℝ) ×ˢ openStripFin, stGen (baseDrift D0) (baseCov D0) u p = 0)
  (hcont : ContinuousOn u (Ioc 0 (t : ℝ) ×ˢ openStripFin))
  (hu0 : ContinuousWithinAt u (Ioc 0 (t : ℝ) ×ˢ openStripFin) (0, finProd.symm z))
  {C : ℝ} (hC : ∀ p ∈ Ioc 0 (t : ℝ) ×ˢ openStripFin, |u p| ≤ C)
include h hD0 hu2 hpde hcont hu0 hC

/-- **Space-time duality for the base diffusion** (start anywhere in the closed strip, `D₀ > 0`):
`E[u(t, Z_t)] = u(0, z)` in `Fin 2` coordinates, for `u` jointly `C²` on `(0, t) × open strip`
solving `∂_s u + 𝒟₀ u = 0` there, continuous on `(0, t] × open strip` and at `(0, z)`, and
bounded. -/
theorem IsExBaseDiffusion.duality (ht : 0 < t) :
    ∫ ω, u ((t : ℝ), baseFin Z t ω) ∂P = u (0, finProd.symm z) := by
  have := h.prob
  obtain ⟨hT, hz, hin⟩ := h.isTestMP_args hD0 t
  exact hT.duality isOpen_univ (continuous_baseDrift D0).continuousOn
    (continuous_baseCov D0).continuousOn (fun y _ i j => baseCov_symm D0 y i j)
    isOpen_openStripFin (subset_univ _) (mem_univ _) hz hin hu2 hpde hcont hu0 hC ht

/-- **Space-time duality for the base diffusion, conditional form.** For `s < t`,
`E[u(t, Z_t) | 𝓖_s] = u(s, Z_s)` a.s. -/
theorem IsExBaseDiffusion.condExp_duality {s : ℝ≥0} (hst : s < t) :
    P[fun ω => u ((t : ℝ), baseFin Z t ω) | 𝓖 s] =ᵐ[P] fun ω => u ((s : ℝ), baseFin Z s ω) := by
  have := h.prob
  obtain ⟨hT, hz, hin⟩ := h.isTestMP_args hD0 t
  exact hT.condExp_duality isOpen_univ (continuous_baseDrift D0).continuousOn
    (continuous_baseCov D0).continuousOn (fun y _ i j => baseCov_symm D0 y i j)
    isOpen_openStripFin (subset_univ _) (mem_univ _) hz hin hu2 hpde hcont hu0 hC hst

end BaseDuality

end BlockBand.Diffusion
