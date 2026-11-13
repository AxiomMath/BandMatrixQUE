module

public import BlockBand.Density.UnitIntensityFinite

/-!
# The unit-intensity consequence of the critical density estimate

Law: the physical marked laws `(R (φ j)).markedLaw E` along any strictly increasing subsequence
of a critical sequence (`W → ∞`, `n/W → τ > 0`), bond `b ∈ (0,1/2)`, bulk energy `E² < 4`, and any
weak limit `ν`.

`criticalUnitIntensity_of_estimate`: the density estimate (clause 2 of
`Internal.Contracts.Inputs.CriticalDensityEstimate`) and `PSSS.SourceContract` imply
`Internal.Contracts.Inputs.CriticalUnitIntensity`. Proof:
`E F_g = ∫ g(u) ρ_{n,W}(E + u/(Nρ(E)))/ρ(E) du → ∫ g` (estimate at `κ = (2-|E|)/2`, `T = τ + 1`,
plus continuity of `ρ` at `E`; eventually `4⌈W^{15/16}⌉ ≤ n ≤ TW`), and the uniform
second-moment bound (PSSS factorial moments of orders 1, 2) passes the mean through the weak
limit.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open MeasureTheory Set Filter BlockBand.Counting BlockBand.External
open scoped ENNReal NNReal Topology

theorem integral_comp_affine (g : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫ x, g (a * (x - c)) = a⁻¹ * ∫ x, g x := by
  have h1 := integral_sub_right_eq_self (μ := (volume : Measure ℝ)) (fun x => g (a * x)) c
  rw [h1, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr ha), smul_eq_mul]

theorem hasCompactSupport_comp_affine {g : ℝ → ℝ} (hg : HasCompactSupport g) {a : ℝ}
    (ha : a ≠ 0) (c : ℝ) : HasCompactSupport (fun x => g (a * (x - c))) := by
  have := hg.comp_homeomorph ((Homeomorph.addRight (-c)).trans (Homeomorph.mulLeft₀ a ha))
  convert this using 1
  funext x
  simp [sub_eq_add_neg]

theorem semicircleDensity_continuous : Continuous Parameters.semicircleDensity := by
  unfold Parameters.semicircleDensity
  fun_prop

theorem tendsto_of_forall_eventually_le {u : ℕ → ℝ} {l M : ℝ} (hM : 0 ≤ M)
    (h : ∀ ε > 0, ∀ᶠ j in atTop, |u j - l| ≤ ε * M) : Tendsto u atTop (𝓝 l) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  filter_upwards [h (δ / (M + 1)) (by positivity)] with j hj
  rw [Real.dist_eq]
  calc |u j - l| ≤ δ / (M + 1) * M := hj
    _ < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith

/-- Eventually `4⌈W^{15/16}⌉ ≤ n` when `n ≥ (τ/2) W`, `W → ∞`. -/
theorem eventually_ceil_le {τ : ℝ} (hτ : 0 < τ) {n W : ℕ → ℕ}
    (hW : Tendsto (fun j => (W j : ℝ)) atTop atTop)
    (hn : ∀ᶠ j in atTop, τ / 2 * (W j : ℝ) ≤ n j) :
    ∀ᶠ j in atTop, 4 * ⌈(W j : ℝ) ^ ((15 : ℝ) / 16)⌉₊ ≤ n j := by
  have h16 : ∀ᶠ j in atTop, 16 / τ ≤ (W j : ℝ) ^ ((1 : ℝ) / 16) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp hW).eventually_ge_atTop _
  have h1 : ∀ᶠ j in atTop, (1 : ℝ) ≤ W j := hW.eventually_ge_atTop 1
  filter_upwards [h16, h1, hn] with j hj h1j hnj
  have hW0 : (0 : ℝ) ≤ W j := by linarith
  have hsplit : (W j : ℝ) = (W j : ℝ) ^ ((15 : ℝ) / 16) * (W j : ℝ) ^ ((1 : ℝ) / 16) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hp1 : (1 : ℝ) ≤ (W j : ℝ) ^ ((15 : ℝ) / 16) := Real.one_le_rpow h1j (by norm_num)
  have hceil : (⌈(W j : ℝ) ^ ((15 : ℝ) / 16)⌉₊ : ℝ) < (W j : ℝ) ^ ((15 : ℝ) / 16) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have key : ((4 * ⌈(W j : ℝ) ^ ((15 : ℝ) / 16)⌉₊ : ℕ) : ℝ) ≤ n j := by
    push_cast
    have h8 : 8 * (W j : ℝ) ^ ((15 : ℝ) / 16) ≤ τ / 2 * (W j : ℝ) := by
      calc 8 * (W j : ℝ) ^ ((15 : ℝ) / 16)
          = τ / 2 * (W j : ℝ) ^ ((15 : ℝ) / 16) * (16 / τ) := by field_simp; ring
        _ ≤ τ / 2 * (W j : ℝ) ^ ((15 : ℝ) / 16) * (W j : ℝ) ^ ((1 : ℝ) / 16) :=
          mul_le_mul_of_nonneg_left hj (by positivity)
        _ = τ / 2 * (W j : ℝ) := by rw [mul_assoc, ← hsplit]
    linarith
  exact_mod_cast key

/-- **Convergence of the mean spectral test** along a critical subsequence, from the estimate. -/
theorem tendsto_integral_spectralTest (hest : Internal.Contracts.Inputs.CriticalDensityEstimate)
    {τ : ℝ} (s : CriticalSequence τ) (hτ : 0 < τ) (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (hE : E ^ 2 < 4) (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (g : CompactlySupportedContinuousMap ℝ ℝ) :
    Tendsto (fun j => ∫ ξ, spectralTest g ξ ∂((R (φ j)).markedLaw E : Measure MarkedPointMeasure))
      atTop (𝓝 (∫ x, g x)) := by
  set ρ := Parameters.semicircleDensity E with hρdef
  have hρ : 0 < ρ := by
    unfold ρ Parameters.semicircleDensity
    exact div_pos (Real.sqrt_pos.mpr (by linarith)) (by positivity [Real.pi_pos])
  have hE2 : |E| < 2 := abs_lt_of_sq_lt_sq (by norm_num; linarith) (by norm_num)
  set κ := (2 - |E|) / 2 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  obtain ⟨C, hC0, hC⟩ := hest.2 b κ (τ + 1) hb hb' hκ0 (by linarith)
  -- support and integrability of g
  obtain ⟨r, hr⟩ := (g.hasCompactSupport.isCompact.isBounded).subset_closedBall 0
  set L := max r 0
  have hsupp : ∀ x, L < |x| → g x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxs
    have := hr hxs
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith [le_max_left r 0]
  set M := ∫ x, |g x| with hMdef
  have hgint : Integrable (fun x => g x) := g.continuous.integrable_of_hasCompactSupport
    g.hasCompactSupport
  have hM0 : 0 ≤ M := integral_nonneg fun _ => abs_nonneg _
  -- sequences
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hWt : Tendsto (fun j => (s.W (φ j) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (s.width_tendsto.comp hφt)
  have hrat : Tendsto (fun j => (s.n (φ j) : ℝ) / (s.W (φ j) : ℝ)) atTop (𝓝 τ) :=
    s.ratio_tendsto.comp hφt
  have hWpos : ∀ j, (0 : ℝ) < s.W (φ j) := fun j => by exact_mod_cast s.W_pos (φ j)
  have hup : ∀ᶠ j in atTop, (s.n (φ j) : ℝ) ≤ (τ + 1) * (s.W (φ j) : ℝ) := by
    filter_upwards [hrat.eventually (gt_mem_nhds (by linarith : τ < τ + 1))] with j hj
    have := (div_lt_iff₀ (hWpos j)).mp hj
    linarith
  have hlow : ∀ᶠ j in atTop, τ / 2 * (s.W (φ j) : ℝ) ≤ (s.n (φ j) : ℝ) := by
    filter_upwards [hrat.eventually (lt_mem_nhds (by linarith : τ / 2 < τ))] with j hj
    have := (lt_div_iff₀ (hWpos j)).mp hj
    linarith
  have hceil := eventually_ceil_le hτ hWt hlow
  have hN : ∀ j, (s.W (φ j) : ℝ) ≤ ((s.parameters b hb hb' (φ j)).N : ℝ) := by
    intro j
    change (s.W (φ j) : ℝ) ≤ ((s.n (φ j) * s.W (φ j) : ℕ) : ℝ)
    push_cast
    have : (1 : ℝ) ≤ s.n (φ j) := by exact_mod_cast (le_trans (by norm_num) (s.n_ge_four (φ j)))
    nlinarith [hWpos j]
  have hNt : Tendsto (fun j => ((s.parameters b hb hb' (φ j)).N : ℝ)) atTop atTop :=
    tendsto_atTop_mono hN hWt
  apply tendsto_of_forall_eventually_le (M := M / ρ) (div_nonneg hM0 hρ.le)
  intro ε hε
  -- continuity of the semicircle density at `E`
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp semicircleDensity_continuous.continuousAt
    (ε / 2) (by positivity)
  set δ' := min (δ / 2) κ
  have hδ' : 0 < δ' := lt_min (by positivity) hκ0
  have hsmall : ∀ᶠ j in atTop, C * (s.W (φ j) : ℝ) ^ (-(1 : ℝ) / 32) ≤ ε / 2 := by
    have h0 : Tendsto (fun j => C * (s.W (φ j) : ℝ) ^ (-(1 : ℝ) / 32)) atTop (𝓝 (C * 0)) := by
      apply Tendsto.const_mul
      have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 32)).comp hWt
      simpa [neg_div, Function.comp_def] using this
    rw [mul_zero] at h0
    exact h0.eventually (ge_mem_nhds (by positivity))
  have hscale : ∀ᶠ j in atTop, L / (((s.parameters b hb hb' (φ j)).N : ℝ) * ρ) ≤ δ' := by
    have : Tendsto (fun j => L / (((s.parameters b hb hb' (φ j)).N : ℝ) * ρ)) atTop (𝓝 0) :=
      (hNt.atTop_mul_const hρ).const_div_atTop L
    exact this.eventually (ge_mem_nhds hδ')
  filter_upwards [hceil, hup, hsmall, hscale] with j hcj hupj hsj hscj
  set p := s.parameters b hb hb' (φ j)
  set a := (p.N : ℝ) * ρ
  have ha : 0 < a := mul_pos (by exact_mod_cast p.N_pos) hρ
  set ρj := meanDensity p (R (φ j)).model
  -- pointwise density bound on the relevant window
  have hwin : ∀ x, g (a * (x - E)) ≠ 0 → |ρj x - ρ| ≤ ε := by
    intro x hx
    have hxa : |a * (x - E)| ≤ L := by
      by_contra hcon; exact hx (hsupp _ (not_le.mp hcon))
    have hxE : |x - E| ≤ δ' := by
      rw [abs_mul, abs_of_pos ha] at hxa
      calc |x - E| = a * |x - E| / a := by field_simp
        _ ≤ L / a := div_le_div_of_nonneg_right hxa ha.le
        _ ≤ δ' := hscj
    have hxb : |x| ≤ 2 - κ := by
      have := abs_sub_abs_le_abs_sub x E
      have : δ' ≤ κ := min_le_right _ _
      rw [hκ] at *
      linarith
    have hest1 := hC (s.n (φ j)) (s.W (φ j)) (s.n_ge_four (φ j)) (s.W_pos (φ j)) hcj hupj
      (R (φ j)).model ρj (contDiff_meanDensity p (R (φ j)).model).continuous
      (meanEmpiricalMeasure_eq_withDensity p (R (φ j)).model) x hxb
    have hest2 : |Parameters.semicircleDensity x - ρ| < ε / 2 := by
      have := hδε (show dist x E < δ by
        rw [Real.dist_eq]; linarith [min_le_left (δ / 2) κ])
      rwa [Real.dist_eq] at this
    calc |ρj x - ρ| ≤ |ρj x - Parameters.semicircleDensity x| +
          |Parameters.semicircleDensity x - ρ| := abs_sub_le _ _ _
      _ ≤ ε / 2 + ε / 2 := by
          have : |ρj x - Parameters.semicircleDensity x| ≤ ε / 2 := hest1.trans hsj
          linarith
      _ = ε := by ring
  -- the integral identity and the bound
  rw [integral_spectralTest_markedLaw (R (φ j)) E g]
  have hcs : HasCompactSupport (fun x => g (a * (x - E))) :=
    hasCompactSupport_comp_affine g.hasCompactSupport ha.ne' E
  have hgc : Continuous (fun x => g (a * (x - E))) := g.continuous.comp (by fun_prop)
  have hi1 : Integrable (fun x => ρj x * g (a * (x - E))) :=
    ((contDiff_meanDensity p (R (φ j)).model).continuous.mul hgc).integrable_of_hasCompactSupport
      hcs.mul_left
  have hi2 : Integrable (fun x => ρ * g (a * (x - E))) :=
    (continuous_const.mul hgc).integrable_of_hasCompactSupport hcs.mul_left
  have hig : ∫ x, g x = (p.N : ℝ) * ∫ x, ρ * g (a * (x - E)) := by
    rw [integral_const_mul, integral_comp_affine (fun x => g x) ha E,
      show a = (p.N : ℝ) * ρ from rfl]
    have hN0 : (p.N : ℝ) ≠ 0 := by exact_mod_cast p.N_pos.ne'
    field_simp
  have habs : ∫ x, |g (a * (x - E))| = a⁻¹ * M := integral_comp_affine (fun x => |g x|) ha E
  rw [hig, ← mul_sub, ← integral_sub hi1 hi2, abs_mul, abs_of_pos (by exact_mod_cast p.N_pos)]
  have hbound : |∫ x, (ρj x * g (a * (x - E)) - ρ * g (a * (x - E)))| ≤
      ∫ x, ε * |g (a * (x - E))| := by
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le ((hgc.abs.integrable_of_hasCompactSupport hcs.abs).const_mul ε)
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
    by_cases hx : g (a * (x - E)) = 0
    · rw [hx]; simp
    · exact mul_le_mul_of_nonneg_right (hwin x hx) (abs_nonneg _)
  rw [integral_const_mul, habs] at hbound
  calc (p.N : ℝ) * |∫ x, (ρj x * g (a * (x - E)) - ρ * g (a * (x - E)))|
      ≤ (p.N : ℝ) * (ε * (a⁻¹ * M)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ε * (M / ρ) := by
        have hN0 : (p.N : ℝ) ≠ 0 := by exact_mod_cast p.N_pos.ne'
        simp only [a]
        field_simp

/-- `g ↦ max g 0` on `C_c(ℝ)`. -/
def posPart (g : CompactlySupportedContinuousMap ℝ ℝ) : CompactlySupportedContinuousMap ℝ ℝ where
  toFun x := max (g x) 0
  continuous_toFun := g.continuous.max continuous_const
  hasCompactSupport' := g.hasCompactSupport.comp_left (g := fun t : ℝ => max t 0) (by simp)

theorem spectralTest_nonneg (g : CompactlySupportedContinuousMap ℝ ℝ) (hg : ∀ x, 0 ≤ g x)
    (ξ : MarkedPointMeasure) : 0 ≤ spectralTest g ξ :=
  integral_nonneg hg

/-- The mean spectral test of a nonnegative `g` passes to every critical subsequential limit. -/
theorem integral_spectralTest_limit_of_nonneg (source : PSSS.SourceContract.{0})
    (hest : Internal.Contracts.Inputs.CriticalDensityEstimate)
    {τ : ℝ} (s : CriticalSequence τ) (hτ : 0 < τ) (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (hE : E ^ 2 < 4) (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (ν : ProbabilityMeasure MarkedPointMeasure)
    (hlim : Tendsto (fun j => (R (φ j)).markedLaw E) atTop (𝓝 ν))
    (g : CompactlySupportedContinuousMap ℝ ℝ) (hg : ∀ x, 0 ≤ g x) :
    Integrable (spectralTest g) (ν : Measure MarkedPointMeasure) ∧
      ∫ ξ, spectralTest g ξ ∂(ν : Measure MarkedPointMeasure) = ∫ x, g x := by
  have hρ : 0 < Parameters.semicircleDensity E := by
    unfold Parameters.semicircleDensity
    exact div_pos (Real.sqrt_pos.mpr (by linarith)) (by positivity [Real.pi_pos])
  obtain ⟨B, hB⟩ := g.continuous.bounded_above_of_compact_support g.hasCompactSupport
  obtain ⟨r, hr⟩ := (g.hasCompactSupport.isCompact.isBounded).subset_closedBall 0
  set L := max r 0
  have hL : 0 ≤ L := le_max_right _ _
  have hsupp : ∀ x, x ∉ Icc (-L) L → g x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxs
    have := hr hxs
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    apply hx
    rw [mem_Icc]
    constructor <;> linarith [le_max_left r 0, abs_le.mp this]
  have hB' : ∀ x, |g x| ≤ B := fun x => by rw [← Real.norm_eq_abs]; exact hB x
  set K₀ := source.C / (Real.sqrt (1 - 2 * b) * Parameters.semicircleDensity E)
  have hsq : ∀ j, Integrable (fun ξ => spectralTest g ξ ^ 2)
      ((R (φ j)).markedLaw E : Measure MarkedPointMeasure) ∧
      ∫ ξ, spectralTest g ξ ^ 2 ∂((R (φ j)).markedLaw E : Measure MarkedPointMeasure) ≤
        B ^ 2 * ((K₀ * (2 * L)) ^ 2 + K₀ * (2 * L)) := fun j =>
    spectralTest_sq_bound source (R (φ j)) E hρ g hB' hL hsupp
  have hint : ∀ j, Integrable (spectralTest g)
      ((R (φ j)).markedLaw E : Measure MarkedPointMeasure) := by
    intro j
    refine ((integrable_const (1 : ℝ)).add (hsq j).1).mono'
      (continuous_spectralTest g).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]
    show |spectralTest g ξ| ≤ 1 + spectralTest g ξ ^ 2
    have := abs_nonneg (spectralTest g ξ)
    have h2 := sq_abs (spectralTest g ξ)
    nlinarith [sq_nonneg (|spectralTest g ξ| - 1)]
  exact integrable_and_integral_eq_of_tendsto hlim (continuous_spectralTest g)
    (spectralTest_nonneg g hg) hint (fun j => (hsq j).1) (fun j => (hsq j).2)
    (tendsto_integral_spectralTest hest s hτ b E hb hb' hE R φ hφ g)

/-- **The critical density theorem, unit-intensity consequence**: for every critical sequence
(ratio `τ > 0`), bond `b ∈ (0,1/2)`, bulk energy `E² < 4`, all finite realizations, every strictly
increasing subsequence and every weak limit `ν` of the physical marked laws, `ν` has unit spectral
intensity. Hypotheses: `PSSS.SourceContract` (uniform count moments) and the estimate
`CriticalDensityEstimate` (only its clause 2 is used). -/
theorem criticalUnitIntensity_of_estimate (source : PSSS.SourceContract.{0})
    (hest : Internal.Contracts.Inputs.CriticalDensityEstimate) :
    Internal.Contracts.Inputs.CriticalUnitIntensity := by
  intro τ s hτ b E hb hb' hE R φ hφ ν hlim f
  set fp := posPart f
  set fm := posPart (-f)
  have hp := integral_spectralTest_limit_of_nonneg source hest s hτ b E hb hb' hE R φ hφ ν hlim
    fp (fun x => le_max_right _ _)
  have hm := integral_spectralTest_limit_of_nonneg source hest s hτ b E hb hb' hE R φ hφ ν hlim
    fm (fun x => le_max_right _ _)
  have hpt : ∀ x, f x = fp x - fm x := by
    intro x
    change f x = max (f x) 0 - max ((-f) x) 0
    simp only [CompactlySupportedContinuousMap.coe_neg, Pi.neg_apply]
    rcases le_total (f x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hξ : ∀ ξ : MarkedPointMeasure, ∫ x, f x ∂ξ.spectral.measure =
      spectralTest fp ξ - spectralTest fm ξ := by
    intro ξ
    unfold spectralTest
    rw [← integral_sub (f := fun x => fp x) (g := fun x => fm x)
      (fp.continuous.integrable_of_hasCompactSupport fp.hasCompactSupport)
      (fm.continuous.integrable_of_hasCompactSupport fm.hasCompactSupport)]
    exact integral_congr_ae (Eventually.of_forall hpt)
  simp_rw [hξ]
  rw [integral_sub hp.1 hm.1, hp.2, hm.2,
    ← integral_sub (f := fun x => fp x) (g := fun x => fm x)
      (fp.continuous.integrable_of_hasCompactSupport fp.hasCompactSupport)
      (fm.continuous.integrable_of_hasCompactSupport fm.hasCompactSupport)]
  exact integral_congr_ae (Eventually.of_forall fun x => (hpt x).symm)

end BlockBand.Density
