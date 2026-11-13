module

public import BlockBand.Diffusion.Heat.Cutoff

/-!
# The forward equation for `e^{-l(x+y)}`

**Main result (`ch_chP_chExp`).** For `D₀ > 0`, `z ∈ exBaseStrip`, `t > 0`, `l > 0`:
`P_t e_l(z) = e_l(z) + ∫_{(0,t]} P_u(𝒟₀e_l)(z) du`, `e_l = chExp l`,
`𝒟₀e_l = chGen D0 l = (D₀/2)(1+x-y)(l²(x+y) - 2l)e^{-l(x+y)}`.

Proof. Run the base diffusion from `z` (`hasExBaseDiffusion`) and take a good
version `W` (`ChGoodVersion`). Dynkin's formula holds for the `C_c^∞` truncations
`chF (n+1) l`. As `n → ∞`, pathwise on `[0, t]` (a compact piece of a
continuous path has bounded `x`-coordinate) the truncation and its generator eventually agree
with `e_l` and `chGen D0 l` along the whole path, and everything is bounded uniformly in `n`
(`|chF| ≤ 1`, `|𝒟₀chF| ≤ chCb D0 l B`), so dominated convergence in `ω` gives Dynkin's formula
for `e_l`. Fubini in `(ω, u)` and the transition law `E g(W_u) = P_u g(z)` conclude.

Also `ch_abs_chGen_le`: `|chGen D0 l| ≤ (D₀/2)(3l + 4)` on the strip for `l ≥ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

theorem ch_continuous_chExp (l : ℝ) : Continuous (chExp l) := by
  unfold chExp; fun_prop

theorem ch_continuous_chGen (D0 l : ℝ) : Continuous (chGen D0 l) := by
  unfold chGen; fun_prop

theorem ch_abs_chExp_le {l : ℝ} (hl : 0 ≤ l) {w : ℝ × ℝ} (hw : w ∈ exBaseStrip) :
    |chExp l w| ≤ 1 := by
  have hs : 0 ≤ w.1 + w.2 := add_nonneg hw.1 hw.2.1
  rw [chExp, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by nlinarith)

/-- `|𝒟₀ e_l| ≤ (D₀/2)(3l + 4)` on the strip, uniformly in `l ≥ 0`. -/
theorem ch_abs_chGen_le {D0 : ℝ} (hD0 : 0 < D0) {l : ℝ} (hl : 0 ≤ l) {w : ℝ × ℝ}
    (hw : w ∈ exBaseStrip) : |chGen D0 l w| ≤ D0 / 2 * (3 * l + 4) := by
  have hx : 0 ≤ w.1 := hw.1
  have hy0 : 0 ≤ w.2 := hw.2.1
  have hy1 : w.2 ≤ 1 := hw.2.2
  set s := w.1 + w.2 with hs_def
  have hs : 0 ≤ s := add_nonneg hx hy0
  set v := l * s with hv_def
  have hv : 0 ≤ v := mul_nonneg hl hs
  have hE1 : v ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
  have hE2 : v ^ 2 ≤ 2 * Real.exp v := by nlinarith [Real.quadratic_le_exp_of_nonneg hv]
  have hE0 : 1 ≤ Real.exp v := Real.one_le_exp hv
  have ha : |1 + w.1 - w.2| ≤ 1 + s := by
    rw [abs_of_nonneg (by linarith)]; linarith
  have hb : |l ^ 2 * s - 2 * l| ≤ l ^ 2 * s + 2 * l := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg l]
  have hkey : (1 + s) * (l ^ 2 * s + 2 * l) ≤ (3 * l + 4) * Real.exp v := by
    have e : (1 + s) * (l ^ 2 * s + 2 * l) = l * v + 2 * l + v ^ 2 + 2 * v := by
      rw [hv_def]; ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hE1 hl, mul_le_mul_of_nonneg_left hE0 hl]
  have hD : 0 ≤ D0 / 2 := by positivity
  unfold chGen
  rw [← hs_def, abs_mul, abs_of_nonneg hD, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ?_ hD
  have hev : Real.exp (-(l * s)) = (Real.exp v)⁻¹ := by rw [Real.exp_neg]
  rw [hev]
  calc |1 + w.1 - w.2| * |l ^ 2 * s - 2 * l| * (Real.exp v)⁻¹
      ≤ (1 + s) * (l ^ 2 * s + 2 * l) * (Real.exp v)⁻¹ := by gcongr
    _ ≤ (3 * l + 4) * Real.exp v * (Real.exp v)⁻¹ := by gcongr
    _ = 3 * l + 4 := by rw [mul_assoc, mul_inv_cancel₀ (Real.exp_pos v).ne', mul_one]

/-- **The forward equation for `e^{-l(x+y)}`** (Dynkin's formula along the base diffusion). -/
theorem ch_chP_chExp {D0 : ℝ} (hD0 : 0 < D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip) {t : ℝ}
    (ht : 0 < t) {l : ℝ} (hl : 0 < l) :
    chP D0 t (chExp l) z = chExp l z + ∫ u in Ioc 0 t, chP D0 u (chGen D0 l) z := by
  obtain ⟨Ω, m, 𝓖, P, Z, h⟩ := hasExBaseDiffusion D0 hD0 z hz
  obtain ⟨W, hW⟩ := h.exists_chGoodVersion hz
  have := h.prob
  obtain ⟨B, -, hB⟩ := ch_st_bound
  set T := t.toNNReal with hT_def
  have hT : (T : ℝ) = t := Real.coe_toNNReal t ht.le
  have hTpos : 0 < T := Real.toNNReal_pos.2 ht
  have hn1 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  -- Dynkin for the truncations
  have hdyn : ∀ n : ℕ, ∫ ω, chF ((n : ℝ) + 1) l (W T ω) ∂P = chF ((n : ℝ) + 1) l z +
      ∫ ω, (∫ u in Ioc (0 : ℝ) t,
        exBaseGenerator D0 (chF ((n : ℝ) + 1) l) (W u.toNNReal ω)) ∂P := fun n => by
    have := hW.dynkin h (ch_contDiff_chF ((n : ℝ) + 1) l) (ch_hasCompactSupport_chF (hn1 n) l) T
    rwa [hT] at this
  -- eventually `x < n + 1`
  have hev : ∀ a : ℝ, ∀ᶠ n : ℕ in atTop, a < (n : ℝ) + 1 := fun a =>
    (eventually_ge_atTop ⌈a⌉₊).mono fun n hn => by
      have h1 : a ≤ ⌈a⌉₊ := Nat.le_ceil a
      have h2 : (⌈a⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
  have hL1 : Tendsto (fun n : ℕ => ∫ ω, chF ((n : ℝ) + 1) l (W T ω) ∂P) atTop
      (𝓝 (∫ ω, chExp l (W T ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun n => ((ch_contDiff_chF _ l).continuous.measurable.comp (hW.meas T)).aestronglyMeasurable)
      (integrable_const 1) (fun n => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact ch_abs_chF_le hl.le (hW.strip T ω))
      (ae_of_all _ fun ω => tendsto_const_nhds.congr' ?_)
    filter_upwards [hev (W T ω).1] with n hn
    exact (ch_chF_of_lt (hn1 n) l (hW.strip T ω) hn).symm
  have hL2 : Tendsto (fun n : ℕ => chF ((n : ℝ) + 1) l z) atTop (𝓝 (chExp l z)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev z.1] with n hn
    exact (ch_chF_of_lt (hn1 n) l hz hn).symm
  have hL3 : Tendsto (fun n : ℕ => ∫ ω, (∫ u in Ioc (0 : ℝ) t,
      exBaseGenerator D0 (chF ((n : ℝ) + 1) l) (W u.toNNReal ω)) ∂P) atTop
      (𝓝 (∫ ω, (∫ u in Ioc (0 : ℝ) t, chGen D0 l (W u.toNNReal ω)) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => chCb D0 l B * t)
      (fun n => ?_) (integrable_const _) (fun n => ae_of_all _ fun ω => ?_)
      (ae_of_all _ fun ω => ?_)
    · have hm : Measurable fun p : Ω × ℝ =>
          exBaseGenerator D0 (chF ((n : ℝ) + 1) l) (W p.2.toNNReal p.1) :=
        (continuous_exBaseGenerator ((ch_contDiff_chF _ l).of_le (by simp)) D0).measurable.comp
          hW.measurable_uncurry'
      exact (hm.stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Ioc (0 : ℝ) t))).aestronglyMeasurable
    · have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) t)
        (f := fun u => exBaseGenerator D0 (chF ((n : ℝ) + 1) l) (W u.toNNReal ω))
        (C := chCb D0 l B) measure_Ioc_lt_top (fun u _ => by
          rw [Real.norm_eq_abs]
          exact ch_abs_gen_chF_le hD0 (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) hl hB
            (hW.strip _ ω))
      simpa [Real.volume_real_Ioc_of_le ht.le] using this
    · obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) t)).exists_bound_of_continuousOn
        (f := fun u : ℝ => (W u.toNNReal ω).1)
        (continuous_fst.comp ((hW.cont ω).comp continuous_real_toNNReal)).continuousOn
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev C] with n hn
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      have hu' := hC u (Ioc_subset_Icc_self hu)
      rw [Real.norm_eq_abs] at hu'
      exact (ch_gen_chF_of_lt D0 (hn1 n) l (hW.strip _ ω)
        (lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt hu' hn))).symm
  have hlim := tendsto_nhds_unique hL1 ((hL2.add hL3).congr fun n => (hdyn n).symm)
  -- back to the kernel
  have hgm : Measurable (chGen D0 l) := (ch_continuous_chGen D0 l).measurable
  rw [hW.integral_comp h hD0 hz hTpos (ch_continuous_chExp l).measurable, hT,
    hW.integral_setIntegral_swap hgm (fun w hw => ch_abs_chGen_le hD0 hl.le hw) t] at hlim
  rw [hlim]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  rw [hW.integral_comp h hD0 hz (Real.toNNReal_pos.2 hu.1) hgm, Real.coe_toNNReal _ hu.1.le]

end BlockBand.Diffusion
