module

public import BlockBand.Endpoints.Clock.OpenClockDual
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Probability.CDF

/-!
# Riemann sums of the dual killing and the exit probability of the dual

We prove the convergence of the killing Riemann sums of the discrete dual to the Feynman–Kac
functional, and that the dual stays in a compact interval with high probability.

* `openClockLaplace D c q t a = E exp{-a c ∫₀^t q(t-s) exp(√D B_s - D s/2) ds}` on the
  constructed Wiener space: the Feynman–Kac (Laplace) functional of the clock Laplace transform
  (`d = c`, `D₀ = D`). Bounds `0 < · ≤ 1` (`openClockLaplace_pos`, `openClockLaplace_le_one`).
* `tendsto_riemann_sum`: left Riemann sums `h Σ_{i<N} Φ(s, i h)` of a jointly continuous `Φ`
  converge to `∫₀^t Φ(t, u) du` when `h → 0`, `s → t`, `N h → t` inside `[0, T]`.
* `tendsto_integral_dualKill`: `E κ_N → openClockLaplace D c q t a` along `h = 1/W`,
  `s = n/W → t`, `N = n - j₀`, `j₀/W → 0` (dominated convergence; `ω(0) = 0` a.s.).
* `exists_dualAlive_ge`: for every `ε > 0` there is `K ≥ 1` with `a ∈ [K⁻¹, K]` and
  `1 - E A_N ≤ ε` for **every** mesh `h` and `N` with `N h ≤ T` (the sup of a continuous path on
  `[0, T]` is finite; no quantitative Brownian estimate is needed).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock
namespace OpenClock

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open BlockBand.SourceProcess
open scoped NNReal ENNReal

/-- **The Feynman–Kac Laplace functional** the clock Laplace transform:
`f(t,a) = E exp{-a c ∫₀^t q(t-s) exp(√D B_s - D s/2) ds}` (`c = d`, `D = D₀`), on the
constructed Wiener space. -/
def openClockLaplace (D c : ℝ) (q : ℝ → ℝ) (t a : ℝ) : ℝ :=
  ∫ ω, exp (-(a * (c * ∫ s in (0 : ℝ)..t,
    q (t - s) * exp (Real.sqrt D * ω s.toNNReal - D * s / 2)))) ∂canonicalWienerLaw

/-- The path functional `∫₀^t q(t-s) exp(√D ω_s - D s/2) ds`. -/
def openClockIntegral (D : ℝ) (q : ℝ → ℝ) (t : ℝ) (ω : CanonicalWienerPath) : ℝ :=
  ∫ s in (0 : ℝ)..t, q (t - s) * exp (Real.sqrt D * ω s.toNNReal - D * s / 2)

theorem continuous_openClockIntegral (D : ℝ) {q : ℝ → ℝ} (hq : Continuous q) (t : ℝ) :
    Continuous (openClockIntegral D q t) := by
  unfold openClockIntegral
  have hev : Continuous (fun p : CanonicalWienerPath × ℝ => p.1 p.2.toNNReal) :=
    continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (ω : CanonicalWienerPath) (s : ℝ) =>
      q (t - s) * exp (Real.sqrt D * ω s.toNNReal - D * s / 2))
    ((hq.comp (continuous_const.sub continuous_snd)).mul
      (continuous_exp.comp ((continuous_const.mul hev).sub
        ((continuous_const.mul continuous_snd).div_const _)))) 0 t

theorem openClockIntegral_nonneg (D : ℝ) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x) {t : ℝ}
    (ht : 0 ≤ t) (ω : CanonicalWienerPath) : 0 ≤ openClockIntegral D q t ω :=
  intervalIntegral.integral_nonneg ht fun _ _ => mul_nonneg (hq0 _) (exp_pos _).le

theorem openClockLaplace_eq (D c : ℝ) (q : ℝ → ℝ) (t a : ℝ) :
    openClockLaplace D c q t a =
      ∫ ω, exp (-(a * (c * openClockIntegral D q t ω))) ∂canonicalWienerLaw := rfl

theorem openClockLaplace_le_one (D : ℝ) {c : ℝ} (hc : 0 ≤ c) {q : ℝ → ℝ} (hq : Continuous q)
    (hq0 : ∀ x, 0 ≤ q x) {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) :
    openClockLaplace D c q t a ≤ 1 := by
  rw [openClockLaplace_eq]
  have hle : ∀ ω, exp (-(a * (c * openClockIntegral D q t ω))) ≤ 1 := fun ω => by
    rw [exp_le_one_iff, neg_nonpos]
    exact mul_nonneg ha (mul_nonneg hc (openClockIntegral_nonneg D hq0 ht ω))
  have hm : Measurable (fun ω => exp (-(a * (c * openClockIntegral D q t ω)))) :=
    (continuous_exp.comp (continuous_const.mul (continuous_const.mul
      (continuous_openClockIntegral D hq t))).neg).measurable
  calc ∫ ω, exp (-(a * (c * openClockIntegral D q t ω))) ∂canonicalWienerLaw
      ≤ ∫ _ω, (1 : ℝ) ∂canonicalWienerLaw :=
        integral_mono (integrable_of_abs_le hm 1 fun ω => by
          rw [abs_of_pos (exp_pos _)]; exact hle ω) (integrable_const 1) hle
    _ = 1 := by simp

theorem openClockLaplace_pos (D : ℝ) {c : ℝ} (hc : 0 ≤ c) {q : ℝ → ℝ} (hq : Continuous q)
    (hq0 : ∀ x, 0 ≤ q x) {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) :
    0 < openClockLaplace D c q t a := by
  rw [openClockLaplace_eq]
  have hm : Measurable (fun ω => exp (-(a * (c * openClockIntegral D q t ω)))) :=
    (continuous_exp.comp (continuous_const.mul (continuous_const.mul
      (continuous_openClockIntegral D hq t))).neg).measurable
  refine integral_exp_pos (integrable_of_abs_le hm 1 fun ω => ?_)
  rw [abs_of_pos (exp_pos _), exp_le_one_iff, neg_nonpos]
  exact mul_nonneg ha (mul_nonneg hc (openClockIntegral_nonneg D hq0 ht ω))

theorem indicator_mem' (L x : ℝ) :
    0 ≤ (Iic L).indicator (fun _ => (1 : ℝ)) x ∧ (Iic L).indicator (fun _ => (1 : ℝ)) x ≤ 1 := by
  by_cases h : x ∈ Iic L
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-!
## Riemann sums
-/

/-- Left Riemann sums of a jointly continuous `Φ` with moving base point. -/
theorem tendsto_riemann_sum {Φ : ℝ × ℝ → ℝ} (hΦ : Continuous Φ) {T t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) {h s : ℕ → ℝ} {N : ℕ → ℕ} (hpos : ∀ W, 0 ≤ h W)
    (hh : Tendsto h atTop (𝓝 0)) (hs : Tendsto s atTop (𝓝 t)) (hs0 : ∀ W, 0 ≤ s W)
    (hsT : ∀ W, s W ≤ T) (hN : Tendsto (fun W => (N W : ℝ) * h W) atTop (𝓝 t))
    (hNT : ∀ W, (N W : ℝ) * h W ≤ T) :
    Tendsto (fun W => h W * ∑ i ∈ Finset.range (N W), Φ (s W, i * h W)) atTop
      (𝓝 (∫ u in (0 : ℝ)..t, Φ (t, u))) := by
  set S : Set (ℝ × ℝ) := Icc (0 : ℝ) T ×ˢ Icc 0 T
  have hSc : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hSc.exists_bound_of_continuousOn hΦ.continuousOn
  have huc := hSc.uniformContinuousOn_of_continuous hΦ.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hT0 : 0 ≤ T := ht0.trans htT
  set η := ε / (4 * (T + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨δ, hδ, hUC⟩ := huc η hη0
  set ρ := ε / (4 * (|M| + 1)) with hρ
  have hρ0 : 0 < ρ := by positivity
  have e1 : ∀ᶠ W in atTop, h W < δ := hh.eventually (gt_mem_nhds hδ)
  have e2 : ∀ᶠ W in atTop, dist (s W) t < δ := (Metric.tendsto_nhds.mp hs) δ hδ
  have e3 : ∀ᶠ W in atTop, dist ((N W : ℝ) * h W) t < ρ := (Metric.tendsto_nhds.mp hN) ρ hρ0
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp (e1.and (e2.and e3))
  refine ⟨W₀, fun W hW => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hW₀ W hW
  set hW := h W
  set sW := s W
  set NW := N W
  have hh0 := hpos W
  set aa : ℕ → ℝ := fun k => k * hW with haa
  have hint : ∀ k < NW, IntervalIntegrable (fun u => Φ (t, u)) volume (aa k) (aa (k + 1)) :=
    fun k _ => (hΦ.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hsum2 : ∑ k ∈ Finset.range NW, ∫ u in aa k..aa (k + 1), Φ (t, u)
      = ∫ u in (0 : ℝ)..(NW * hW), Φ (t, u) := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hint]; simp [haa]
  have hsum1 : hW * ∑ i ∈ Finset.range NW, Φ (sW, i * hW)
      = ∑ k ∈ Finset.range NW, ∫ _u in aa k..aa (k + 1), Φ (sW, aa k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const, smul_eq_mul]
    simp only [haa]; push_cast; ring
  have hdiff : hW * ∑ i ∈ Finset.range NW, Φ (sW, i * hW) - ∫ u in (0 : ℝ)..(NW * hW), Φ (t, u)
      = ∑ k ∈ Finset.range NW, ∫ u in aa k..aa (k + 1), (Φ (sW, aa k) - Φ (t, u)) := by
    rw [hsum1, ← hsum2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hint k (Finset.mem_range.mp hk))]
  have hpiece : ∀ k ∈ Finset.range NW,
      |∫ u in aa k..aa (k + 1), (Φ (sW, aa k) - Φ (t, u))| ≤ η * hW := by
    intro k hk
    have hk' : k + 1 ≤ NW := Finset.mem_range.mp hk
    have hlen : |aa (k + 1) - aa k| = hW := by
      simp only [haa]; push_cast; rw [show ((k : ℝ) + 1) * hW - k * hW = hW by ring,
        abs_of_nonneg hh0]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := aa k) (b := aa (k + 1))
      (C := η) (f := fun u => Φ (sW, aa k) - Φ (t, u)) (fun u hu => ?_)
    · rw [hlen] at hb; simpa [Real.norm_eq_abs] using hb
    · have hle : aa k ≤ aa (k + 1) := by
        simp only [haa]; push_cast; nlinarith
      rw [uIoc_of_le hle] at hu
      have hNk : aa (k + 1) ≤ T := by
        calc aa (k + 1) = ((k + 1 : ℕ) : ℝ) * hW := rfl
          _ ≤ NW * hW := mul_le_mul_of_nonneg_right (by exact_mod_cast hk') hh0
          _ ≤ T := hNT W
      have hak0 : 0 ≤ aa k := mul_nonneg (Nat.cast_nonneg _) hh0
      have hmem1 : (sW, aa k) ∈ S := ⟨⟨hs0 W, hsT W⟩, ⟨hak0, hle.trans hNk⟩⟩
      have hmem2 : (t, u) ∈ S := ⟨⟨ht0, htT⟩, ⟨hak0.trans hu.1.le, hu.2.trans hNk⟩⟩
      have hdist : dist (sW, aa k) (t, u) < δ := by
        rw [Prod.dist_eq, max_lt_iff]
        refine ⟨h2, ?_⟩
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hu.1])]
        have : u - aa k ≤ hW := by
          have := hu.2; simp only [haa] at this ⊢; push_cast at this; linarith
        linarith
      have := hUC _ hmem1 _ hmem2 hdist
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]; exact this.le
  have hfirst : |hW * ∑ i ∈ Finset.range NW, Φ (sW, i * hW) - ∫ u in (0 : ℝ)..(NW * hW), Φ (t, u)|
      ≤ ε / 4 := by
    rw [hdiff]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hpiece).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (NW : ℝ) * (η * hW) = η * (NW * hW) := by ring
    rw [this]
    calc η * (NW * hW) ≤ η * T := mul_le_mul_of_nonneg_left (hNT W) hη0.le
      _ ≤ η * (T + 1) := by nlinarith
      _ = ε / 4 := by rw [hη]; field_simp
  have hsecond : |(∫ u in (0 : ℝ)..(NW * hW), Φ (t, u)) - ∫ u in (0 : ℝ)..t, Φ (t, u)| ≤ ε / 4 := by
    have hII : ∀ x y : ℝ, IntervalIntegrable (fun u => Φ (t, u)) volume x y := fun x y =>
      (hΦ.comp (continuous_const.prodMk continuous_id)).intervalIntegrable x y
    rw [intervalIntegral.integral_interval_sub_left (hII _ _) (hII _ _)]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := NW * hW)
      (C := |M|) (f := fun u => Φ (t, u)) (fun u hu => ?_)
    · rw [Real.norm_eq_abs] at hb
      refine hb.trans ?_
      have h3' : |(NW : ℝ) * hW - t| < ρ := by rw [← Real.dist_eq]; exact h3
      calc |M| * |(NW : ℝ) * hW - t| ≤ (|M| + 1) * ρ := by
            have : |M| * |(NW : ℝ) * hW - t| ≤ |M| * ρ :=
              mul_le_mul_of_nonneg_left h3'.le (abs_nonneg _)
            nlinarith [abs_nonneg M]
        _ = ε / 4 := by rw [hρ]; field_simp
    · have hNW0 : 0 ≤ (NW : ℝ) * hW := mul_nonneg (Nat.cast_nonneg _) hh0
      have hu' : u ∈ Icc (0 : ℝ) T := by
        rcases le_total t (NW * hW) with hle | hle
        · rw [uIoc_of_le hle] at hu; exact ⟨ht0.trans hu.1.le, hu.2.trans (hNT W)⟩
        · rw [uIoc_of_ge hle] at hu; exact ⟨hNW0.trans hu.1.le, hu.2.trans htT⟩
      exact (hM (t, u) ⟨⟨ht0, htT⟩, hu'⟩).trans (le_abs_self M)
  rw [Real.dist_eq]
  calc |hW * ∑ i ∈ Finset.range NW, Φ (sW, i * hW) - ∫ u in (0 : ℝ)..t, Φ (t, u)|
      ≤ |hW * ∑ i ∈ Finset.range NW, Φ (sW, i * hW) - ∫ u in (0 : ℝ)..(NW * hW), Φ (t, u)| +
        |(∫ u in (0 : ℝ)..(NW * hW), Φ (t, u)) - ∫ u in (0 : ℝ)..t, Φ (t, u)| := abs_sub_le _ _ _
    _ ≤ ε / 4 + ε / 4 := add_le_add hfirst hsecond
    _ < ε := by linarith

/-!
## The killing converges to the Feynman–Kac functional
-/

/-- The integrand `q(s - u) a exp(√D (ω_u - ω_0) - D u/2)` of the dual killing. -/
def riemannIntegrand (D a : ℝ) (q : ℝ → ℝ) (ω : CanonicalWienerPath) (p : ℝ × ℝ) : ℝ :=
  q (p.1 - p.2) * (a * exp (Real.sqrt D * (ω p.2.toNNReal - ω 0) - D * p.2 / 2))

theorem continuous_riemannIntegrand (D a : ℝ) {q : ℝ → ℝ} (hq : Continuous q)
    (ω : CanonicalWienerPath) : Continuous (riemannIntegrand D a q ω) := by
  unfold riemannIntegrand
  have hev : Continuous (fun p : ℝ × ℝ => ω p.2.toNNReal) :=
    ω.continuous.comp (continuous_real_toNNReal.comp continuous_snd)
  exact (hq.comp (continuous_fst.sub continuous_snd)).mul (continuous_const.mul
    (continuous_exp.comp ((continuous_const.mul (hev.sub continuous_const)).sub
      ((continuous_const.mul continuous_snd).div_const _))))

theorem dualKill_eq_riemann (D a c : ℝ) (q : ℝ → ℝ) (t : ℝ) (hh : ℝ≥0)
    (ω : CanonicalWienerPath) (N : ℕ) :
    dualKill D a c q t hh (sampleW hh ω) N =
      exp (-(c * ((hh : ℝ) * ∑ i ∈ Finset.range N, riemannIntegrand D a q ω (t, i * hh)))) := by
  unfold dualKill dualB sampleW riemannIntegrand
  congr 2
  rw [← mul_assoc]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hto : ((i : ℝ) * (hh : ℝ)).toNNReal = (i : ℝ≥0) * hh := by
    rw [show (i : ℝ) * (hh : ℝ) = (((i : ℝ≥0) * hh : ℝ≥0) : ℝ) by push_cast; ring,
      Real.toNNReal_coe]
  simp only [hto, Nat.cast_zero, zero_mul]

/-- `E κ_N → openClockLaplace D c q t a` along `h = 1/W`, `t_W = n/W → t`, `N = n - j₀`. -/
theorem tendsto_integral_dualKill {D a c : ℝ} {q : ℝ → ℝ} (hq : Continuous q)
    (hq0 : ∀ x, 0 ≤ q x) (ha : 0 < a) (hc : 0 ≤ c) {T t : ℝ} (ht0 : 0 < t) (htT : t ≤ T)
    {n j₀ : ℕ → ℕ} (hn : Tendsto (fun W => (n W : ℝ) / W) atTop (𝓝 t))
    (hnT : ∀ W, (n W : ℝ) ≤ T * W) (hj₀ : Tendsto (fun W => (j₀ W : ℝ) / W) atTop (𝓝 0)) :
    Tendsto (fun W : ℕ => ∫ ω, dualKill D a c q ((n W : ℝ) / W) ((W : ℝ≥0)⁻¹)
        (sampleW ((W : ℝ≥0)⁻¹) ω) (n W - j₀ W) ∂canonicalWienerLaw) atTop
      (𝓝 (openClockLaplace D c q t a)) := by
  set P := canonicalWienerLaw
  have hT0 : 0 ≤ T := ht0.le.trans htT
  set Φ : CanonicalWienerPath → ℝ × ℝ → ℝ := riemannIntegrand D a q with hΦ
  have hΦc : ∀ ω, Continuous (Φ ω) := continuous_riemannIntegrand D a hq
  set h : ℕ → ℝ := fun W => ((W : ℝ≥0)⁻¹ : ℝ≥0) with hhdef
  have hhW : ∀ W : ℕ, h W = (W : ℝ)⁻¹ := fun W => by
    show (((W : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) = (W : ℝ)⁻¹
    push_cast; rfl
  have hpos : ∀ W, 0 ≤ h W := fun W => (((W : ℝ≥0)⁻¹ : ℝ≥0)).2
  have hh0 : Tendsto h atTop (𝓝 0) := by
    have e : h = fun W : ℕ => (W : ℝ)⁻¹ := funext hhW
    rw [e]; exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hs0 : ∀ W, 0 ≤ (n W : ℝ) / W := fun W => by positivity
  have hsT : ∀ W, (n W : ℝ) / W ≤ T := by
    intro W
    rcases Nat.eq_zero_or_pos W with h0 | h0
    · subst h0; simp [hT0]
    · rw [div_le_iff₀ (by exact_mod_cast h0)]; exact hnT W
  have hdiffT : Tendsto (fun W => (n W : ℝ) / W - (j₀ W : ℝ) / W) atTop (𝓝 t) := by
    simpa using hn.sub hj₀
  have hev : ∀ᶠ W in atTop, j₀ W ≤ n W := by
    have := hdiffT.eventually (lt_mem_nhds ht0)
    filter_upwards [this] with W hW
    by_contra hlt
    push Not at hlt
    have : (n W : ℝ) / W - (j₀ W : ℝ) / W ≤ 0 := by
      rw [sub_nonpos]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hlt.le) (Nat.cast_nonneg _)
    linarith
  have hN : Tendsto (fun W => ((n W - j₀ W : ℕ) : ℝ) * h W) atTop (𝓝 t) := by
    refine hdiffT.congr' ?_
    filter_upwards [hev] with W hW
    rw [Nat.cast_sub hW, hhW]; ring
  have hNT : ∀ W, ((n W - j₀ W : ℕ) : ℝ) * h W ≤ T := by
    intro W
    have h1 : ((n W - j₀ W : ℕ) : ℝ) ≤ n W := by exact_mod_cast Nat.sub_le _ _
    calc ((n W - j₀ W : ℕ) : ℝ) * h W ≤ n W * h W := mul_le_mul_of_nonneg_right h1 (hpos W)
      _ = (n W : ℝ) / W := by rw [hhW]; ring
      _ ≤ T := hsT W
  -- pathwise convergence
  have hlim : ∀ ω, Tendsto (fun W => dualKill D a c q ((n W : ℝ) / W) ((W : ℝ≥0)⁻¹)
      (sampleW ((W : ℝ≥0)⁻¹) ω) (n W - j₀ W)) atTop
      (𝓝 (exp (-(c * ∫ u in (0 : ℝ)..t, Φ ω (t, u))))) := by
    intro ω
    have hR := tendsto_riemann_sum (hΦc ω) ht0.le htT hpos hh0 hn hs0 hsT hN hNT
    have hcont : Continuous (fun x : ℝ => exp (-(c * x))) :=
      continuous_exp.comp (continuous_const.mul continuous_id).neg
    have := (hcont.tendsto _).comp hR
    refine this.congr fun W => ?_
    simp only [Function.comp_apply]
    rw [dualKill_eq_riemann]
  have hmeas : ∀ W : ℕ, AEStronglyMeasurable (fun ω => dualKill D a c q ((n W : ℝ) / W)
      ((W : ℝ≥0)⁻¹) (sampleW ((W : ℝ≥0)⁻¹) ω) (n W - j₀ W)) P := fun W =>
    ((measurable_dualKill (n W - j₀ W)).comp (measurable_sampleW _)).aestronglyMeasurable
  have hbound : ∀ W : ℕ, ∀ᵐ ω ∂P, ‖dualKill D a c q ((n W : ℝ) / W) ((W : ℝ≥0)⁻¹)
      (sampleW ((W : ℝ≥0)⁻¹) ω) (n W - j₀ W)‖ ≤ 1 := fun W =>
    Filter.Eventually.of_forall fun ω => by
      have := dualKill_mem (D := D) (t := (n W : ℝ) / W) (hh := (W : ℝ≥0)⁻¹) ha hc hq0
        (sampleW ((W : ℝ≥0)⁻¹) ω) (n W - j₀ W)
      rw [Real.norm_eq_abs, abs_of_pos this.1]; exact this.2
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hmeas
    (integrable_const 1) hbound (Filter.Eventually.of_forall hlim)
  have heq : openClockLaplace D c q t a = ∫ ω, exp (-(c * ∫ u in (0 : ℝ)..t, Φ ω (t, u))) ∂P := by
    rw [openClockLaplace_eq]
    have h0 : ∀ᵐ ω ∂P, ω 0 = 0 :=
      canonicalWiener_isBrownian.toIsPreBrownianReal.eval_zero_ae_eq_zero
    refine integral_congr_ae (h0.mono fun ω hω => ?_)
    simp only [hΦ, riemannIntegrand, hω, sub_zero]
    congr 2
    unfold openClockIntegral
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    ring
  rw [heq]
  exact hDCT

/-!
## The dual stays in `[K⁻¹, K]` with high probability, uniformly in the mesh
-/

/-- For every `ε > 0` there is `K ≥ 1` with `a ∈ [K⁻¹, K]` and `1 - E A_N ≤ ε` for **every**
mesh `h` and every `N` with `N h ≤ T`. -/
theorem exists_dualAlive_ge (D : ℝ) {a : ℝ} (ha : 0 < a) {T : ℝ} (hT : 0 ≤ T) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ a ∈ Icc K⁻¹ K ∧ ∀ (hh : ℝ≥0) (N : ℕ), (N : ℝ) * hh ≤ T →
      1 - ∫ ω, dualAlive D a K hh (sampleW hh ω) N ∂canonicalWienerLaw ≤ ε := by
  set P := canonicalWienerLaw
  set T' : ℝ≥0 := T.toNNReal
  set R : CanonicalWienerPath → ℝ := fun ω => ‖ω.restrict (Icc (0 : ℝ≥0) T')‖ with hR
  have hRc : Continuous R := continuous_norm.comp (ContinuousMap.continuous_restrict _)
  set V : CanonicalWienerPath → ℝ := fun ω => 2 * Real.sqrt D * R ω + |D| * T / 2 with hV
  have hVm : Measurable V := ((continuous_const.mul hRc).add continuous_const).measurable
  have hcdf := tendsto_cdf_atTop (μ := P.map V)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (hcdf.eventually (lt_mem_nhds (by linarith :
    1 - ε < 1)))
  set L := max L₀ 0
  have hL : 1 - ε < cdf (P.map V) L := hL₀ L (le_max_left _ _)
  have hL0 : 0 ≤ L := le_max_right _ _
  set K := exp (|Real.log a| + L) with hK
  have hK1 : 1 ≤ K := one_le_exp (by positivity)
  have hKinv : K⁻¹ = exp (-(|Real.log a| + L)) := by rw [hK, exp_neg]
  have hmemK : ∀ y : ℝ, |y| ≤ L → a * exp y ∈ Icc K⁻¹ K := by
    intro y hy
    have hae : a * exp y = exp (Real.log a + y) := by rw [exp_add, exp_log ha]
    rw [hae, hKinv]
    have h1 := neg_abs_le (Real.log a)
    have h2 := le_abs_self (Real.log a)
    rw [abs_le] at hy
    exact ⟨exp_le_exp.mpr (by linarith), exp_le_exp.mpr (by linarith)⟩
  refine ⟨K, hK1, by simpa using hmemK 0 (by simpa using hL0), fun hh N hN => ?_⟩
  -- pointwise: on `{V ≤ L}` the dual is alive
  have hpt : ∀ ω, (Iic L).indicator (fun _ => (1 : ℝ)) (V ω) ≤
      dualAlive D a K hh (sampleW hh ω) N := by
    intro ω
    by_cases hω : V ω ≤ L
    · rw [Set.indicator_of_mem (show V ω ∈ Iic L from hω)]
      unfold dualAlive
      rw [Finset.prod_eq_one]
      intro i hi
      have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hu : (i : ℝ≥0) * hh ≤ T' := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hT]
        push_cast
        calc (i : ℝ) * hh ≤ N * hh := mul_le_mul_of_nonneg_right (by exact_mod_cast hiN) hh.2
          _ ≤ T := hN
      have hb1 : |ω ((i : ℝ≥0) * hh)| ≤ R ω := by
        have := ContinuousMap.norm_coe_le_norm (ω.restrict (Icc (0 : ℝ≥0) T'))
          ⟨(i : ℝ≥0) * hh, ⟨by positivity, hu⟩⟩
        simpa [Real.norm_eq_abs] using this
      have hb0 : |ω 0| ≤ R ω := by
        have := ContinuousMap.norm_coe_le_norm (ω.restrict (Icc (0 : ℝ≥0) T'))
          ⟨0, ⟨le_rfl, by positivity⟩⟩
        simpa [Real.norm_eq_abs] using this
      have hiT : (i : ℝ) * hh ≤ T := by
        calc (i : ℝ) * hh ≤ N * hh := mul_le_mul_of_nonneg_right (by exact_mod_cast hiN) hh.2
          _ ≤ T := hN
      have hi0 : 0 ≤ (i : ℝ) * hh := mul_nonneg (Nat.cast_nonneg _) hh.2
      have hsq : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
      have hY : |Real.sqrt D * (sampleW hh ω i - sampleW hh ω 0) - D * ((i : ℝ) * hh) / 2| ≤ L := by
        have e0 : sampleW hh ω 0 = ω 0 := by simp [sampleW]
        rw [e0]
        have h1 : |Real.sqrt D * (sampleW hh ω i - ω 0)| ≤ Real.sqrt D * (2 * R ω) := by
          rw [abs_mul, abs_of_nonneg hsq]
          refine mul_le_mul_of_nonneg_left ?_ hsq
          calc |sampleW hh ω i - ω 0| ≤ |sampleW hh ω i| + |ω 0| := abs_sub _ _
            _ ≤ R ω + R ω := add_le_add hb1 hb0
            _ = 2 * R ω := by ring
        have h2 : |D * ((i : ℝ) * hh) / 2| ≤ |D| * T / 2 := by
          rw [abs_div, abs_mul, abs_of_nonneg hi0, abs_two]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hiT (abs_nonneg D))
            zero_le_two
        calc _ ≤ |Real.sqrt D * (sampleW hh ω i - ω 0)| + |D * ((i : ℝ) * hh) / 2| := abs_sub _ _
          _ ≤ Real.sqrt D * (2 * R ω) + |D| * T / 2 := add_le_add h1 h2
          _ = V ω := by simp only [hV]; ring
          _ ≤ L := hω
      exact Set.indicator_of_mem (hmemK _ hY) _
    · rw [Set.indicator_of_notMem (show V ω ∉ Iic L from hω)]
      exact (dualAlive_mem _ _).1
  have hAm : Measurable (fun ω => dualAlive D a K hh (sampleW hh ω) N) :=
    (measurable_dualAlive N).comp (measurable_sampleW hh)
  have hAI : Integrable (fun ω => dualAlive D a K hh (sampleW hh ω) N) P :=
    integrable_of_abs_le hAm 1 fun ω => by
      rw [abs_of_nonneg (dualAlive_mem _ _).1]; exact (dualAlive_mem _ _).2
  have hindI : Integrable (fun ω => (Iic L).indicator (fun _ => (1 : ℝ)) (V ω)) P :=
    integrable_of_abs_le ((measurable_const.indicator measurableSet_Iic).comp hVm) 1
      fun ω => by
        have := indicator_mem' L (V ω)
        rw [abs_of_nonneg this.1]; exact this.2
  have hind : ∫ ω, (Iic L).indicator (fun _ => (1 : ℝ)) (V ω) ∂P = cdf (P.map V) L := by
    rw [cdf_eq_real, map_measureReal_apply hVm measurableSet_Iic]
    have : (fun ω => (Iic L).indicator (fun _ => (1 : ℝ)) (V ω)) =
        (V ⁻¹' Iic L).indicator (fun _ => (1 : ℝ)) := by
      funext ω; simp [Set.indicator, Set.mem_preimage]
    rw [this, integral_indicator_const (1 : ℝ) (hVm measurableSet_Iic), smul_eq_mul, mul_one]
  have := integral_mono hindI hAI hpt
  rw [hind] at this
  linarith

end OpenClock
end BlockBand.Endpoints.Clock
