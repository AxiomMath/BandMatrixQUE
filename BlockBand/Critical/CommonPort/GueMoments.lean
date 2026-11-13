module

public import BlockBand.Layers.BondMoments
public import BlockBand.Palm.GoodEventNet
public import BlockBand.GaussianCalculus.LpGradient

/-!
# Common-port mean: operator-norm moments of the fresh GUE blocks

Law: the fresh layer `layerLaw W b σ` (any shape `σ`), whose block `ω.1 a` has law
`GUE_W(c/W)`, `c = 1 - 2b` (`gueMeasure (Fin W) (Real.toNNReal ((1-2b)/W))`).
Norm: Euclidean operator norm (`Matrix.Norms.L2Operator`).

* `layerLaw_block_preimage`: the marginal of `ω.1 a` under `layerLaw` is `GUE_W(c/W)`.
* `layerLaw_block_tail`: `P(r < ‖ω.1 a‖) ≤ (K √c / r)^W` (`r > 0`, `W ≥ 1`, `0 ≤ c`), from the
  GUE operator-norm tail `BlockBand.Palm.GoodEvent.opB_tail_gue` applied to
  `gaussianLpGradient_holds`.
* `gueBlock_lintegral_rpow_le`, `gueBlock_eLpNorm_le`: there is `C_A` (depending only on the
  absolute constant `K`) such that for every `0 ≤ c ≤ 1`, i.e. `0 ≤ b ≤ 1/2`, every shape, every
  block `a`, and real `1 ≤ q ≤ W - 1`: `‖1 + ‖ω.1 a‖‖_{L^q(layerLaw W b σ)} ≤ C_A`
  (dyadic layer cake, as in `bond_lintegral_rpow_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

open MeasureTheory Matrix BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-- The Palm operator norm `opB` is the `ℓ²` operator norm. -/
theorem opB_eq_norm {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) :
    BlockBand.Palm.GoodEvent.opB M = ‖M‖ := rfl

/-- **Marginal of one fresh block.** Under `layerLaw W b σ`, `ω.1 a ~ GUE_W(c/W)`. -/
theorem layerLaw_block_preimage (W : ℕ) (b : ℝ) (σ : LayerShape) (a : Fin σ.blocks)
    {S : Set (Matrix (Fin W) (Fin W) ℂ)} (hS : MeasurableSet S) :
    layerLaw W b σ {ω | ω.1 a ∈ S} =
      gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)) S := by
  have := fun t => BlockBand.Layers.isProbabilityMeasure_gueMeasure W t
  have hset : {ω : LayerSample W σ | ω.1 a ∈ S} = (Function.eval a ⁻¹' S) ×ˢ Set.univ := by
    ext ω; simp
  rw [hset]
  unfold layerLaw
  rw [Measure.prod_prod, measure_univ, mul_one]
  exact (measurePreserving_eval _ a).measure_preimage hS.nullMeasurableSet

/-- **Operator-norm tail of one fresh block** (law `layerLaw W b σ`, `W ≥ 1`, `0 ≤ 1-2b`):
`P(r < ‖ω.1 a‖) ≤ (K √(1-2b) / r)^W` for every `r > 0`, `K` absolute. -/
theorem layerLaw_block_tail : ∃ K : ℝ, 0 < K ∧ ∀ (W : ℕ), 0 < W → ∀ (b : ℝ), b ≤ 1 / 2 →
    ∀ (σ : LayerShape) (a : Fin σ.blocks) (r : ℝ), 0 < r →
      layerLaw W b σ {ω | r < ‖ω.1 a‖} ≤
        ENNReal.ofReal ((K * Real.sqrt (1 - 2 * b) / r) ^ W) := by
  obtain ⟨K, hK, h⟩ := BlockBand.Palm.GoodEvent.opB_tail_gue
    BlockBand.GaussianCalculus.gaussianLpGradient_holds
  refine ⟨K, hK, fun W hW b hb σ a r hr => ?_⟩
  have hS : MeasurableSet {M : Matrix (Fin W) (Fin W) ℂ | r < ‖M‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have := layerLaw_block_preimage W b σ a hS
  simp only [Set.mem_ofPred_eq] at this
  rw [this]
  exact h W hW (1 - 2 * b) (by linarith) r hr

/-- The block moment constant `C_A = 6 (2 + 2K)` (`K` from `layerLaw_block_tail`). -/
def gueBlockConst (K : ℝ) : ℝ := 6 * (1 + (2 * K + 1))

/-- One dyadic term: `(2^{n+1}(1+a₀))^q ((1/2)^n)^W ≤ (2(1+a₀))^q (1/2)^n` for
`0 ≤ a₀`, `0 ≤ q ≤ W - 1`. -/
theorem gue_dyadic_term_le {W : ℕ} {a₀ q : ℝ} (ha : 0 ≤ a₀) (hq0 : 0 ≤ q)
    (hqW : q ≤ (W : ℝ) - 1) (n : ℕ) :
    ((2 : ℝ) ^ (n + 1) * (1 + a₀)) ^ q * ((1 / 2 : ℝ) ^ n) ^ W ≤
      (2 * (1 + a₀)) ^ q * (1 / 2) ^ n := by
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have h2n0 : (0 : ℝ) < 2 ^ n := by positivity
  have hsplit : ((2 : ℝ) ^ (n + 1) * (1 + a₀)) ^ q = (2 * (1 + a₀)) ^ q * ((2 : ℝ) ^ n) ^ q := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1; rw [pow_succ]; ring
  rw [hsplit]
  have hmono : ((2 : ℝ) ^ n) ^ q ≤ ((2 : ℝ) ^ n) ^ ((W : ℝ) - 1) :=
    Real.rpow_le_rpow_of_exponent_le h2n hqW
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hid : ((2 : ℝ) ^ n) ^ ((W : ℝ) - 1) * ((1 / 2 : ℝ) ^ n) ^ W = (1 / 2) ^ n := by
    rw [Real.rpow_sub_one h2n0.ne', Real.rpow_natCast, _root_.one_div_pow, _root_.one_div_pow]
    have : (0 : ℝ) < ((2 : ℝ) ^ n) ^ W := by positivity
    field_simp
  calc (2 * (1 + a₀)) ^ q * ((2 : ℝ) ^ n) ^ q * ((1 / 2 : ℝ) ^ n) ^ W
      ≤ (2 * (1 + a₀)) ^ q * ((2 : ℝ) ^ n) ^ ((W : ℝ) - 1) * ((1 / 2 : ℝ) ^ n) ^ W := by
        gcongr
    _ = (2 * (1 + a₀)) ^ q * (1 / 2) ^ n := by rw [mul_assoc, hid]

/-- **Moments of one fresh block** (law `layerLaw W b σ`, `0 ≤ b ≤ 1/2`, operator norm):
with `K` of `layerLaw_block_tail`, for every real `1 ≤ q ≤ W - 1`, every shape and block,
`E (1 + ‖ω.1 a‖)^q ≤ (gueBlockConst K)^q`. Uniform in `W`, `b`, `σ`, `a`, `q`. -/
theorem gueBlock_lintegral_rpow_le {K : ℝ} (hK : 0 < K)
    (htail : ∀ (W : ℕ), 0 < W → ∀ (b : ℝ), b ≤ 1 / 2 →
      ∀ (σ : LayerShape) (a : Fin σ.blocks) (r : ℝ), 0 < r →
        layerLaw W b σ {ω | r < ‖ω.1 a‖} ≤
          ENNReal.ofReal ((K * Real.sqrt (1 - 2 * b) / r) ^ W))
    {W : ℕ} {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2) (σ : LayerShape) (a : Fin σ.blocks) {q : ℝ}
    (hq1 : 1 ≤ q) (hqW : q ≤ (W : ℝ) - 1) :
    ∫⁻ ω, ENNReal.ofReal ((1 + ‖ω.1 a‖) ^ q) ∂layerLaw W b σ ≤
      ENNReal.ofReal (gueBlockConst K ^ q) := by
  have hW : 0 < W := by
    have : (2 : ℝ) ≤ W := by linarith
    exact_mod_cast (show (0 : ℝ) < W by linarith)
  have := BlockBand.Layers.bond_isProbabilityMeasure_layerLaw W b σ
  set μ := layerLaw W b σ with hμ
  set A : LayerSample W σ → ℝ := fun ω => ‖ω.1 a‖ with hA
  set a₀ : ℝ := 2 * K + 1 with ha₀
  have ha0 : 0 < a₀ := by positivity
  have hq0 : 0 ≤ q := by linarith
  have hAm : Measurable A :=
    continuous_norm.measurable.comp ((measurable_pi_apply a).comp measurable_fst)
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hsc : Real.sqrt (1 - 2 * b) ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith
  set S : ℕ → Set (LayerSample W σ) := fun n => {ω | (2 : ℝ) ^ n * a₀ ≤ A ω} with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n => measurableSet_le measurable_const hAm
  set d : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (((2 : ℝ) ^ (n + 1) * (1 + a₀)) ^ q) with hd
  set D : ℝ := (2 * (1 + a₀)) ^ q with hD
  have hpt : ∀ ω, ENNReal.ofReal ((1 + A ω) ^ q) ≤
      ENNReal.ofReal ((1 + a₀) ^ q) + ∑' n, (S n).indicator (fun _ => d n) ω := by
    intro ω
    refine (BlockBand.Layers.bond_rpow_le_tsum (norm_nonneg _) ha0 hq0).trans (le_of_eq ?_)
    congr 1
  have hterm : ∀ n, d n * μ (S n) ≤ ENNReal.ofReal D * 2⁻¹ ^ n := by
    intro n
    have hr : 0 < (2 : ℝ) ^ n * a₀ / 2 := by positivity
    have hsub : S n ⊆ {ω | (2 : ℝ) ^ n * a₀ / 2 < A ω} := by
      intro ω hω
      simp only [hS, Set.mem_ofPred_eq] at hω ⊢
      have : (2 : ℝ) ^ n * a₀ / 2 < (2 : ℝ) ^ n * a₀ := by
        have : 0 < (2 : ℝ) ^ n * a₀ := by positivity
        linarith
      linarith
    have htl := (measure_mono hsub).trans (htail W hW b hb σ a _ hr)
    have hratio : K * Real.sqrt (1 - 2 * b) / ((2 : ℝ) ^ n * a₀ / 2) ≤ (1 / 2) ^ n := by
      rw [div_le_iff₀ hr, _root_.one_div_pow]
      have h2n0 : (0 : ℝ) < 2 ^ n := by positivity
      have : (1 : ℝ) / 2 ^ n * ((2 : ℝ) ^ n * a₀ / 2) = a₀ / 2 := by field_simp
      rw [this]
      have : K * Real.sqrt (1 - 2 * b) ≤ K := by nlinarith
      linarith
    have hpow : (K * Real.sqrt (1 - 2 * b) / ((2 : ℝ) ^ n * a₀ / 2)) ^ W ≤ ((1 / 2 : ℝ) ^ n) ^ W :=
      pow_le_pow_left₀ (by positivity) hratio W
    calc d n * μ (S n)
        ≤ ENNReal.ofReal (((2 : ℝ) ^ (n + 1) * (1 + a₀)) ^ q) *
            ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ W) := by
          gcongr
          exact htl.trans (ENNReal.ofReal_le_ofReal hpow)
      _ = ENNReal.ofReal (((2 : ℝ) ^ (n + 1) * (1 + a₀)) ^ q * ((1 / 2 : ℝ) ^ n) ^ W) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (D * (1 / 2) ^ n) :=
          ENNReal.ofReal_le_ofReal (gue_dyadic_term_le ha0.le hq0 hqW n)
      _ = ENNReal.ofReal D * 2⁻¹ ^ n := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), one_div,
            ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  calc ∫⁻ ω, ENNReal.ofReal ((1 + A ω) ^ q) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal ((1 + a₀) ^ q) + ∑' n, (S n).indicator (fun _ => d n) ω) ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal ((1 + a₀) ^ q) * μ Set.univ +
          ∑' n, ∫⁻ ω, (S n).indicator (fun _ => d n) ω ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const,
          lintegral_tsum fun n => (measurable_const.indicator (hSm n)).aemeasurable]
    _ = ENNReal.ofReal ((1 + a₀) ^ q) + ∑' n, d n * μ (S n) := by
        rw [measure_univ, mul_one]
        congr 1
        exact tsum_congr fun n => lintegral_indicator_const (hSm n) _
    _ ≤ ENNReal.ofReal ((1 + a₀) ^ q) + ∑' n, ENNReal.ofReal D * 2⁻¹ ^ n := by
        exact add_le_add le_rfl (ENNReal.tsum_le_tsum hterm)
    _ = ENNReal.ofReal ((1 + a₀) ^ q + 2 * D) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat, mul_comm (2 : ℝ≥0∞)]
    _ ≤ ENNReal.ofReal (gueBlockConst K ^ q) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (1 + a₀) ^ q ≤ D := Real.rpow_le_rpow (by positivity) (by linarith) hq0
        have h3 : (3 : ℝ) ≤ 3 ^ q := by
          calc (3 : ℝ) = 3 ^ (1 : ℝ) := (Real.rpow_one 3).symm
            _ ≤ 3 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq1
        have hC : gueBlockConst K ^ q = 3 ^ q * D := by
          rw [hD, ← Real.mul_rpow (by norm_num) (by positivity)]
          unfold gueBlockConst
          congr 1
          ring
        have hD0 : 0 ≤ D := by positivity
        rw [hC]
        nlinarith

/-- **`L^q` form of the block moments** (law `layerLaw W b σ`, `0 ≤ b ≤ 1/2`, operator norm):
there is an absolute `C_A > 0` such that for every `W`, every real `1 ≤ q ≤ W - 1`, every shape
`σ` and block `a`: `‖1 + ‖ω.1 a‖‖_{L^q} ≤ C_A`. -/
theorem gueBlock_eLpNorm_le : ∃ CA : ℝ, 0 < CA ∧ ∀ (W : ℕ) (b : ℝ), 0 ≤ b → b ≤ 1 / 2 →
    ∀ (σ : LayerShape) (a : Fin σ.blocks) (q : ℝ), 1 ≤ q → q ≤ (W : ℝ) - 1 →
      eLpNorm (fun ω : LayerSample W σ => 1 + ‖ω.1 a‖) (ENNReal.ofReal q) (layerLaw W b σ) ≤
        ENNReal.ofReal CA := by
  obtain ⟨K, hK, htail⟩ := layerLaw_block_tail
  have hC0 : 0 < gueBlockConst K := by unfold gueBlockConst; positivity
  refine ⟨gueBlockConst K, hC0, fun W b hb0 hb σ a q hq1 hqW => ?_⟩
  have hq0 : 0 < q := by linarith
  have hp0 : ENNReal.ofReal q ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq0
  have hm : Measurable (fun ω : LayerSample W σ => 1 + ‖ω.1 a‖) :=
    measurable_const.add
      (continuous_norm.measurable.comp ((measurable_pi_apply a).comp measurable_fst))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hq0.le]
  have hint : ∫⁻ ω, ‖1 + ‖ω.1 a‖‖ₑ ^ q ∂layerLaw W b σ =
      ∫⁻ ω, ENNReal.ofReal ((1 + ‖ω.1 a‖) ^ q) ∂layerLaw W b σ := by
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
  rw [hint]
  calc (∫⁻ ω, ENNReal.ofReal ((1 + ‖ω.1 a‖) ^ q) ∂layerLaw W b σ) ^ (1 / q)
      ≤ ENNReal.ofReal (gueBlockConst K ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow (gueBlock_lintegral_rpow_le hK htail hb0 hb σ a hq1 hqW)
          (by positivity)
    _ = ENNReal.ofReal (gueBlockConst K) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← Real.rpow_mul hC0.le, mul_one_div_cancel hq0.ne', Real.rpow_one]

end BlockBand.Critical.CommonPort
