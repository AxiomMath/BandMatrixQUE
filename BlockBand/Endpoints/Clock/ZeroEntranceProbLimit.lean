module

public import BlockBand.Endpoints.Clock.ZeroEntranceProbDeriv
public import BlockBand.Endpoints.Clock.ZeroEntranceProbPert

/-!
# The zero-entrance lemma: the limiting measures `μ_J` and `G_{μ_J} = m_{J+1}`

We construct the limiting measures of the zero-entrance lemma and prove the convergence in
probability of the empirical laws.

* `chainPort b e J z'`: the port value `m_{J+1}` of a solution of the finite Dyson equation with
  port parameter `z'` (it exists, `portChain_exists`, and is unique,
  `portChain_port_unique`).
* `exists_limitMeasure`: for `0 < b < 1/2`, `-2 < e < 2` and every `J` there is a probability
  measure `μ_J` with `G_{μ_J}(ζ) = chainPort b e J ζ` on the whole upper half-plane. Proof: the
  expected empirical laws `ν_W` of `X_J` (`exists_expectedSpectral`) have Stieltjes transforms
  `E h_J(ζ) → m_{J+1}(ζ)` (`meanBound_all`), and `(iy) m_{J+1}(iy) → 1` (from the port equation
  and the bound `|m_J| ≤ (1-2b)^{-1/2}`); Prokhorov (`exists_prob_of_stieltjes_tendsto`) gives `μ_J`.
  Tightness comes from the Stieltjes transforms, instead of from a count bound for deformed
  Gaussian matrices.
* `prob_zeTrace_le`: convergence in probability, in the Stieltjes form of
  `ZeroEntranceStatement`, with the quantitative bound `P(|h_J(ζ) - G_{μ_J}(ζ)| ≥ δ) ≤
  (C√2 + C')/(δW)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology Metric
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Real

namespace ZeroEntranceProb

open Classical in
/-- The port value `m_{J+1}` of the chain with port parameter `z'` (a chosen solution). -/
def chainPort (b e : ℝ) (J : ℕ) (z' : ℂ) : ℂ :=
  if h : 0 < b ∧ 0 < 1 - 2 * b ∧ 0 < z'.im then
    Classical.choose (portChain_exists h.1 h.2.1 e J h.2.2) (J + 1)
  else 0

theorem chainPort_spec {b e : ℝ} (hb : 0 < b) (hc : 0 < 1 - 2 * b) (J : ℕ) {z' : ℂ}
    (hz : 0 < z'.im) : ∃ m : ℕ → ℂ, IsPortChain b e J z' m ∧ m (J + 1) = chainPort b e J z' := by
  have h : 0 < b ∧ 0 < 1 - 2 * b ∧ 0 < z'.im := ⟨hb, hc, hz⟩
  refine ⟨Classical.choose (portChain_exists hb hc e J hz),
    Classical.choose_spec (portChain_exists hb hc e J hz), ?_⟩
  unfold chainPort
  split_ifs with h'
  · rfl
  · exact absurd h h'

/-- The compact parameter set containing a given admissible `(b, e)`. -/
def kappaOf (b e : ℝ) : ℝ := min (min b (1 - 2 * b)) (4 - e ^ 2)

theorem kappaOf_facts {b e : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (he0 : -2 < e) (he1 : e < 2) :
    0 < kappaOf b e ∧ zeParam (kappaOf b e) b e := by
  have h4 : 0 < 4 - e ^ 2 := by nlinarith
  refine ⟨lt_min (lt_min hb0 (by linarith)) h4, ?_, ?_, ?_⟩
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact min_le_right _ _

/-- Uniqueness of the port value of chain solutions (from `meanBound_all`). -/
theorem portChain_port_unique (hU : CavityLayerUniform) {κ : ℝ} (hκ : 0 < κ) {b e : ℝ}
    (hbe : zeParam κ b e) {J : ℕ} {z' : ℂ} (hz : 0 < z'.im) {m m' : ℕ → ℂ}
    (hm : IsPortChain b e J z' m) (hm' : IsPortChain b e J z' m') : m (J + 1) = m' (J + 1) := by
  obtain ⟨C, hC, hMB⟩ := meanBound_all hU hκ J z'.im ‖z'‖ hz
  by_contra hne
  have hpos : 0 < ‖m (J + 1) - m' (J + 1)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨W, hW⟩ := exists_nat_gt (2 * C / ‖m (J + 1) - m' (J + 1)‖)
  have hW0 : 0 < W := by
    have : (0 : ℝ) < W := lt_of_le_of_lt (by positivity) hW
    exact_mod_cast this
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  have h1 := hMB W hW0 b e hbe z' le_rfl le_rfl m hm
  have h2 := hMB W hW0 b e hbe z' le_rfl le_rfl m' hm'
  have h3 : ‖m (J + 1) - m' (J + 1)‖ ≤ 2 * C / W := by
    have h4 := norm_sub_le_norm_sub_add_norm_sub (m (J + 1))
      (meanTrace b e (0 : Matrix (Fin W) (Fin W) ℂ) J z') (m' (J + 1))
    have h5 : ‖m (J + 1) - meanTrace b e (0 : Matrix (Fin W) (Fin W) ℂ) J z'‖ ≤ C / W := by
      rw [norm_sub_rev]; exact h1
    have : 2 * C / W = C / W + C / W := by ring
    linarith
  rw [div_lt_iff₀ hpos] at hW
  rw [le_div_iff₀ hWr] at h3
  nlinarith

theorem chainPort_eq_of {b e : ℝ} (hU : CavityLayerUniform) {κ : ℝ} (hκ : 0 < κ)
    (hbe : zeParam κ b e) {J : ℕ} {z' : ℂ} (hz : 0 < z'.im) {m : ℕ → ℂ}
    (hm : IsPortChain b e J z' m) : chainPort b e J z' = m (J + 1) := by
  obtain ⟨hb0, hb1, -, -, -, -, -⟩ := zeParam_facts hκ hbe
  obtain ⟨m', hm', hm'e⟩ := chainPort_spec (e := e) hb0 (by linarith) J hz
  rw [← hm'e]
  exact portChain_port_unique hU hκ hbe hz hm' hm

/-- `(iy) m_{J+1}(iy) → 1` as `y → ∞`. -/
theorem tendsto_chainPort_imag {b e : ℝ} (hb : 0 < b) (hc : 0 < 1 - 2 * b) (J : ℕ) :
    Tendsto (fun y : ℝ => ((y : ℂ) * Complex.I) * chainPort b e J ((y : ℂ) * Complex.I)) atTop
      (𝓝 1) := by
  set K₀ := 1 / Real.sqrt (1 - 2 * b) with hK₀
  have hK0 : 0 ≤ K₀ := by positivity
  have hmJ : ∀ m : ℕ → ℂ, ∀ z', IsPortChain b e J z' m → ‖m J‖ ≤ K₀ := by
    intro m z' hm
    rcases Nat.eq_zero_or_pos J with hJ | hJ
    · subst hJ; rw [hm.zero, norm_zero]; exact hK0
    · have h1 := portChain_phys_bound hm hb.le (ℓ := J) hJ le_rfl
      have h2 : ‖m J‖ ^ 2 ≤ 1 / (1 - 2 * b) := by rw [le_div_iff₀ hc]; linarith
      rw [hK₀, ← Real.sqrt_sq (norm_nonneg (m J)), one_div, ← Real.sqrt_inv]
      exact Real.sqrt_le_sqrt (by rw [← one_div]; exact h2)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ᶠ y : ℝ in atTop, ‖((y : ℂ) * Complex.I) * chainPort b e J ((y : ℂ) * Complex.I) - 1‖ ≤
      2 * (b * K₀) / y := by
    filter_upwards [eventually_ge_atTop (2 * (b * K₀) + 1)] with y hy
    have hy0 : 0 < y := by have : 0 ≤ b * K₀ := by positivity
                           linarith
    have hzi : 0 < ((y : ℂ) * Complex.I).im := by simp [hy0]
    obtain ⟨m, hm, hme⟩ := chainPort_spec (e := e) hb hc J hzi
    rw [← hme]
    have hport := hm.port
    have hmJn := hmJ m _ hm
    set w := (y : ℂ) * Complex.I - b * m J with hw
    have hwn : y - b * K₀ ≤ ‖w‖ := by
      have h1 : ‖(y : ℂ) * Complex.I‖ = y := by
        rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hy0.le, mul_one]
      have h2 : ‖(b : ℂ) * m J‖ ≤ b * K₀ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
        exact mul_le_mul_of_nonneg_left hmJn hb.le
      have := norm_sub_norm_le ((y : ℂ) * Complex.I) ((b : ℂ) * m J)
      linarith
    have hwpos : 0 < ‖w‖ := by have : 0 ≤ b * K₀ := by positivity
                               linarith
    have hm1 : m (J + 1) = w⁻¹ := by rw [← hport, inv_inv]
    have hwne : w ≠ 0 := norm_pos_iff.mp hwpos
    have hid : ((y : ℂ) * Complex.I) * w⁻¹ - 1 = (b * m J) * w⁻¹ := by
      field_simp; rw [hw]; ring
    rw [hm1, hid, norm_mul, norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
    have h3 : b * ‖m J‖ ≤ b * K₀ := mul_le_mul_of_nonneg_left hmJn hb.le
    have h4 : ‖w‖⁻¹ ≤ 2 / y := by
      rw [inv_le_comm₀ hwpos (by positivity)]
      have : y / 2 ≤ ‖w‖ := by linarith
      calc (2 / y)⁻¹ = y / 2 := by rw [inv_div]
        _ ≤ ‖w‖ := this
    calc b * ‖m J‖ * ‖w‖⁻¹ ≤ b * K₀ * (2 / y) :=
          mul_le_mul h3 h4 (by positivity) (by positivity)
      _ = 2 * (b * K₀) / y := by ring
  have hlim : Tendsto (fun y : ℝ => 2 * (b * K₀) / y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hlim

/-- **The limiting measure.** -/
theorem exists_limitMeasure (hU : CavityLayerUniform) {b e : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (he0 : -2 < e) (he1 : e < 2) (J : ℕ) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ ζ : ℂ, 0 < ζ.im → stieltjesG μ ζ = chainPort b e J ζ := by
  obtain ⟨hκ, hbe⟩ := kappaOf_facts hb0 hb1 he0 he1
  have hc : 0 < 1 - 2 * b := by linarith
  have hex : ∀ W : ℕ, ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ ζ : ℂ, 0 < ζ.im →
      stieltjesG ν ζ = meanTrace b e (0 : Matrix (Fin (W + 1)) (Fin (W + 1)) ℂ) J ζ := by
    intro W
    obtain ⟨ν, hν, hG⟩ := exists_expectedSpectral (oneEndedLaw (W + 1) b J) (Nat.succ_pos W)
      (measurable_X e (0 : Matrix (Fin (W + 1)) (Fin (W + 1)) ℂ) J)
      (ae_X_isHermitian b e Matrix.isHermitian_zero J)
    exact ⟨ν, hν, fun ζ hζ => (hG ζ hζ).trans rfl⟩
  choose ν hν hνG using hex
  refine exists_prob_of_stieltjes_tendsto hν (fun ζ hζ => ?_) (tendsto_chainPort_imag hb0 hc J)
  obtain ⟨C, hC, hMB⟩ := meanBound_all hU hκ J ζ.im ‖ζ‖ hζ
  obtain ⟨m, hm, hme⟩ := chainPort_spec (e := e) hb0 hc J hζ
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbd : ∀ W : ℕ, ‖stieltjesG (ν W) ζ - chainPort b e J ζ‖ ≤ C / ((W : ℝ) + 1) := by
    intro W
    rw [hνG W ζ hζ, ← hme]
    have := hMB (W + 1) (Nat.succ_pos W) b e hbe ζ le_rfl le_rfl m hm
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) hbd ?_
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

/-- **Convergence in probability** (Stieltjes form), quantitative. -/
theorem prob_zeTrace_le (hU : CavityLayerUniform) {κ : ℝ} (hκ : 0 < κ) (J : ℕ) {η M : ℝ}
    (hη : 0 < η) : ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → 0 < W → ∀ b e : ℝ,
      zeParam κ b e → ∀ ζ : ℂ, η ≤ ζ.im → ‖ζ‖ ≤ M → ∀ δ : ℝ, 0 < δ →
        oneEndedLaw W b J {ω | δ ≤ ‖zeTrace e (0 : Matrix (Fin W) (Fin W) ℂ) J ζ ω -
          chainPort b e J ζ‖} ≤ ENNReal.ofReal (K / (δ * W)) := by
  obtain ⟨a, CF, ha, hCF, hFB⟩ := fluctBound_all hU hκ J η M hη
  obtain ⟨CM, hCM, hMB⟩ := meanBound_all hU hκ J η M hη
  refine ⟨CF * Real.sqrt 2 + CM, ⌈2 / a⌉₊, by positivity, ?_⟩
  intro W hW hW0 b e hbe ζ hz hzM δ hδ
  obtain ⟨hb0, hb1, -, -, -, -, -⟩ := zeParam_facts hκ hbe
  have hz0 : 0 < ζ.im := hη.trans_le hz
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  have h2a : (2 : ℝ) ≤ a * W := by
    have h1 : (⌈2 / a⌉₊ : ℝ) ≤ W := by exact_mod_cast hW
    have h2 : 2 / a ≤ W := (Nat.le_ceil _).trans h1
    rw [div_le_iff₀ ha] at h2; linarith
  obtain ⟨m, hm, hme⟩ := chainPort_spec (e := e) hb0 (by linarith) J hz0
  have hD0 : (0 : Matrix (Fin W) (Fin W) ℂ).IsHermitian := Matrix.isHermitian_zero
  set h := zeTrace e (0 : Matrix (Fin W) (Fin W) ℂ) J ζ with hhdef
  set P := oneEndedLaw W b J
  have hmeas : Measurable h := measurable_zeTrace e _ J ζ
  have hset : {ω | δ ≤ ‖h ω - chainPort b e J ζ‖} =
      {ω | ENNReal.ofReal δ ≤ ‖h ω - chainPort b e J ζ‖ₑ} := by
    ext ω
    show δ ≤ _ ↔ ENNReal.ofReal δ ≤ _
    rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
  rw [hset]
  refine (meas_ge_le_lintegral_div ((hmeas.sub_const _).enorm).aemeasurable
    (by simpa using hδ) ENNReal.ofReal_ne_top).trans ?_
  have hsplit : (fun ω => h ω - chainPort b e J ζ) =
      (fun ω => h ω - ∫ ω', h ω' ∂P) + fun _ => (∫ ω', h ω' ∂P) - chainPort b e J ζ := by
    funext ω; simp only [Pi.add_apply]; ring
  have hL1 : ∫⁻ ω, ‖h ω - chainPort b e J ζ‖ₑ ∂P ≤
      ENNReal.ofReal (CF * Real.sqrt 2 / W) + ENNReal.ofReal (CM / W) := by
    rw [← eLpNorm_one_eq_lintegral_enorm, hsplit]
    refine (eLpNorm_add_le le_rfl).trans (add_le_add ?_ ?_)
    · have hfl := hFB W hW0 b e hbe 0 hD0 ζ hz hzM 2 le_rfl h2a
      have hle : eLpNorm (fun ω => h ω - ∫ ω', h ω' ∂P) 1 P ≤
          eLpNorm (fun ω => h ω - ∫ ω', h ω' ∂P) (ENNReal.ofReal 2) P :=
        eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.one_le_ofReal.mpr (by norm_num))
      exact hle.trans hfl
    · rw [eLpNorm_const _ one_ne_zero (IsProbabilityMeasure.ne_zero P), measure_univ,
        ENNReal.one_rpow, mul_one, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← hme]
      exact hMB W hW0 b e hbe ζ hz hzM m hm
    · exact (hmeas.sub_const _).aestronglyMeasurable
  calc (∫⁻ ω, ‖h ω - chainPort b e J ζ‖ₑ ∂P) / ENNReal.ofReal δ
      ≤ (ENNReal.ofReal (CF * Real.sqrt 2 / W) + ENNReal.ofReal (CM / W)) / ENNReal.ofReal δ := by
        gcongr
    _ = ENNReal.ofReal ((CF * Real.sqrt 2 + CM) / (δ * W)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_div_of_pos hδ]
        congr 1
        field_simp

end ZeroEntranceProb

end BlockBand.Endpoints.Clock
