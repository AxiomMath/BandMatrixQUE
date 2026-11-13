module

public import BlockBand.SourceProcess.PhysApprox.B3FracMomPin
public import BlockBand.SourceProcess.PhysApprox.B3FracMomOde

/-!
# The path recursion for `E (Tr T_r^α)^q` and its uniform bound

* `young_pow`: `x^a y^b ≤ θ^b x^{a+b} + θ^{-a} y^{a+b}` (`x, y ≥ 0`, `θ > 0`);
* `powN_of_eLpNorm`: `‖f‖_n ≤ C` gives `E f^n ≤ C^n` (`f ≥ 0`);
* **`fracPow_rec`**: `FracPowStep α q`, `MatchedTracesContract`, `GaussianAbsorptionContract`
  and `GaussianLpGradient` give, on `ε'W ≤ r ≤ TW`,
  `E P_{r+1}^q ≤ E P_r^q - (c/W) E P_r^{q+1} + K/W` (with `c ≤ 1`);
* **`fracPow_bound`** (proved in a sibling module): `E P_{⌊Wt⌋}^q ≤ C` for `W ≥ W₀`, every
  `t > 0` (the sharp comparison `ode_iter` over the last `⌊Wt/2⌋` layers, started from the trivial
  `E P^q ≤ W^q`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.FracMom

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission BlockBand.Transmission.FractionalBulk BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-!
## Elementary inequalities
-/

/-- `x^a y^b ≤ θ^b x^{a+b} + θ^{-a} y^{a+b}` for `x, y ≥ 0`, `θ > 0`. -/
theorem young_pow {x y θ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hθ : 0 < θ) (a b : ℕ) :
    x ^ a * y ^ b ≤ θ ^ b * x ^ (a + b) + (θ ^ a)⁻¹ * y ^ (a + b) := by
  rcases le_total y (θ * x) with h | h
  · have h1 : y ^ b ≤ (θ * x) ^ b := pow_le_pow_left₀ hy h b
    have h2 : 0 ≤ (θ ^ a)⁻¹ * y ^ (a + b) := by positivity
    calc x ^ a * y ^ b ≤ x ^ a * (θ * x) ^ b := mul_le_mul_of_nonneg_left h1 (pow_nonneg hx a)
      _ = θ ^ b * x ^ (a + b) := by rw [mul_pow, pow_add]; ring
      _ ≤ _ := le_add_of_nonneg_right h2
  · have hx' : x ≤ y / θ := by rw [le_div_iff₀ hθ]; linarith [mul_comm θ x]
    have h1 : x ^ a ≤ (y / θ) ^ a := pow_le_pow_left₀ hx hx' a
    have h2 : 0 ≤ θ ^ b * x ^ (a + b) := by positivity
    calc x ^ a * y ^ b ≤ (y / θ) ^ a * y ^ b := mul_le_mul_of_nonneg_right h1 (pow_nonneg hy b)
      _ = (θ ^ a)⁻¹ * y ^ (a + b) := by rw [div_pow, pow_add, div_eq_mul_inv]; ring
      _ ≤ _ := le_add_of_nonneg_left h2

/-- `‖f‖_n ≤ C` gives `E f^n ≤ C^n` and the integrability of `f^n`, for `f ≥ 0`. -/
theorem powN_of_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hf0 : ∀ ω, 0 ≤ f ω) {n : ℕ} (hn : 1 ≤ n)
    {C : ℝ} (hC : 0 ≤ C) (h : eLpNorm f (ENNReal.ofReal n) μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => f ω ^ n) μ ∧ ∫ ω, f ω ^ n ∂μ ≤ C ^ n := by
  have hlt : eLpNorm f (ENNReal.ofReal n) μ < ∞ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hmem : MemLp f (n : ℝ≥0∞) μ := by
    rw [← ENNReal.ofReal_natCast]; exact hlt
  have hint : Integrable (fun ω => f ω ^ n) μ := by
    have := hmem.integrable_norm_pow'
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]
  refine ⟨hint, ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := SourceMixing.cm_lintegral_le hf (p := n) hn0 hC h
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => pow_nonneg (hf0 ω) n)
    hint.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (le_trans (le_of_eq ?_) (hl.trans
    (le_of_eq (by rw [Real.rpow_natCast]))))
  refine lintegral_congr fun ω => ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hn0.le, Real.rpow_natCast,
    Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]

/-- Linearity of the integral of the eight-term bound. -/
theorem integral_eight {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Ω → ℝ} (a₂ a₃ a₄ a₅ a₆ a₇ a₈ : ℝ) (h₁ : Integrable f₁ μ)
    (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ) (h₄ : Integrable f₄ μ) (h₅ : Integrable f₅ μ)
    (h₆ : Integrable f₆ μ) (h₇ : Integrable f₇ μ) :
    ∫ ω, (f₁ ω + a₂ * f₂ ω + a₃ * f₃ ω + a₄ * f₄ ω + a₅ * f₅ ω + a₆ * f₆ ω + a₇ * f₇ ω + a₈) ∂μ =
      (∫ ω, f₁ ω ∂μ) + a₂ * (∫ ω, f₂ ω ∂μ) + a₃ * (∫ ω, f₃ ω ∂μ) + a₄ * (∫ ω, f₄ ω ∂μ) +
        a₅ * (∫ ω, f₅ ω ∂μ) + a₆ * (∫ ω, f₆ ω ∂μ) + a₇ * (∫ ω, f₇ ω ∂μ) + a₈ := by
  have i2 := h₂.const_mul a₂
  have i3 := h₃.const_mul a₃
  have i4 := h₄.const_mul a₄
  have i5 := h₅.const_mul a₅
  have i6 := h₆.const_mul a₆
  have i7 := h₇.const_mul a₇
  have j2 : Integrable (fun ω => f₁ ω + a₂ * f₂ ω) μ := h₁.add i2
  have j3 : Integrable (fun ω => f₁ ω + a₂ * f₂ ω + a₃ * f₃ ω) μ := j2.add i3
  have j4 : Integrable (fun ω => f₁ ω + a₂ * f₂ ω + a₃ * f₃ ω + a₄ * f₄ ω) μ := j3.add i4
  have j5 : Integrable (fun ω => f₁ ω + a₂ * f₂ ω + a₃ * f₃ ω + a₄ * f₄ ω + a₅ * f₅ ω) μ :=
    j4.add i5
  have j6 : Integrable (fun ω => f₁ ω + a₂ * f₂ ω + a₃ * f₃ ω + a₄ * f₄ ω + a₅ * f₅ ω +
      a₆ * f₆ ω) μ := j5.add i6
  have j7 : Integrable (fun ω => f₁ ω + a₂ * f₂ ω + a₃ * f₃ ω + a₄ * f₄ ω + a₅ * f₅ ω +
      a₆ * f₆ ω + a₇ * f₇ ω) μ := j6.add i7
  rw [integral_add j7 (integrable_const a₈), integral_add j6 i7, integral_add j5 i6,
    integral_add j4 i5, integral_add j3 i4, integral_add j2 i3, integral_add h₁ i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const]
  simp

/-- `W^q (C/W)^{q+1} = C^{q+1}/W`. -/
theorem pow_mul_div_pow_succ {Wr : ℝ} (hW : 0 < Wr) (C : ℝ) (q : ℕ) :
    Wr ^ q * (C / Wr) ^ (q + 1) = C ^ (q + 1) / Wr := by
  rw [div_pow, pow_succ Wr]; field_simp

/-- `W^q (C/W)^{2q} ≤ C^{2q}/W` for `W ≥ 1`, `q ≥ 1`. -/
theorem pow_mul_div_pow_two_mul_le {Wr : ℝ} (hW : 1 ≤ Wr) (C : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    Wr ^ q * (C / Wr) ^ (2 * q) ≤ C ^ (2 * q) / Wr := by
  have hW0 : 0 < Wr := by linarith
  have hC : 0 ≤ C ^ (2 * q) := by rw [pow_mul]; positivity
  have e : Wr ^ q * (C / Wr) ^ (2 * q) = C ^ (2 * q) / Wr ^ q := by
    rw [div_pow, two_mul, pow_add Wr]; field_simp
  rw [e]
  exact div_le_div_of_nonneg_left hC hW0 (le_self_pow₀ hW (by omega))

/-!
## The path recursion
-/

/-- `y_r = E (Tr T_r^α)^q` on the open path. -/
def pathPow (α b E : ℝ) (W r q : ℕ) : ℝ :=
  ∫ ω, fracTrace α (pathTransmission b E (fun _ => 0) W r ω) ^ q ∂growthPathLaw W b

theorem pathPow_nonneg (α b E : ℝ) (r q : ℕ) : 0 ≤ pathPow α b E W r q :=
  integral_nonneg fun _ => pow_nonneg (fracTrace_nonneg' _ _) _

/-- Integrability and the bound `0 ≤ E P_r^n ≤ W^n`. -/
theorem pathFrac_pow_facts {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {b : ℝ} (hb : b < 1 / 2) {E : ℝ}
    (h1 : -2 < E) (h2 : E < 2) (r n : ℕ) :
    Integrable (fun ω => fracTrace α (pathTransmission b E (fun _ => 0) W r ω) ^ n)
      (growthPathLaw W b) ∧ pathPow α b E W r n ≤ (W : ℝ) ^ n := by
  obtain ⟨hm, hb'⟩ := pathFrac_facts (W := W) hα0 hα1 hb h1 h2 r
  have hi : Integrable (fun ω => fracTrace α (pathTransmission b E (fun _ => 0) W r ω) ^ n)
      (growthPathLaw W b) :=
    Integrable.of_bound (hm.pow n) ((W : ℝ) ^ n) (by
      filter_upwards [hb'] with ω h
      rw [Real.norm_of_nonneg (pow_nonneg h.1 n)]
      exact pow_le_pow_left₀ h.1 h.2 n)
  refine ⟨hi, ?_⟩
  have := Transmission.Bridge.isProbabilityMeasure_growthPathLaw W b
  calc pathPow α b E W r n ≤ ∫ _ω, (W : ℝ) ^ n ∂growthPathLaw W b :=
        integral_mono_ae hi (integrable_const _) (by
          filter_upwards [hb'] with ω h
          exact pow_le_pow_left₀ h.1 h.2 n)
    _ = (W : ℝ) ^ n := by simp

set_option maxHeartbeats 1000000 in
/-- **The recursion for `E P_r^q`.** -/
theorem fracPow_rec (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {q : ℕ} (hq : 1 ≤ q)
    (hS : FracPowStep α q) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ (c K : ℝ), 0 < c ∧ c ≤ 1 ∧ 0 ≤ K ∧ ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ r : ℕ, 1 ≤ r → ε' * W ≤ r → (r : ℝ) ≤ T * W →
        pathPow α b E W (r + 1) q ≤ pathPow α b E W r q -
          c / W * pathPow α b E W r (q + 1) + K / W := by
  obtain ⟨c, A, B, d, γ, W₁, hc, hA, hB, hd, hγ, hSt⟩ := hS b E hb0 hb h1 h2
  obtain ⟨hκ, hEκ⟩ := bulk_of_lt' h1 h2
  set κ := min (2 + E) (2 - E)
  have hLU := LengthUniform.transmissionLengthUniform_holds hMT hGA hLp
  have hq1 : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by norm_cast; omega
  have hq2 : (1 : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by norm_cast; omega
  obtain ⟨Cg1, hCg1⟩ := hLU.conductance b hb0 hb κ ε' _ hκ hε' hq1
  obtain ⟨Cg2, hCg2⟩ := hLU.conductance b hb0 hb κ ε' _ hκ hε' hq2
  obtain ⟨Cj1, hCj1⟩ := hLU.jet b hb0 hb κ ε' _ hκ hε' hq1
  obtain ⟨Cj2, hCj2⟩ := hLU.jet b hb0 hb κ ε' _ hκ hε' hq2
  set Cg1' := max Cg1 0
  set Cg2' := max Cg2 0
  set Cj1' := max Cj1 0
  set Cj2' := max Cj2 0
  set K := A * Cj1' ^ (q + 1) + A + A * Cg1' +
    (B / d ^ (2 * q) * Cj2' ^ (2 * q) + B / d ^ (2 * q) * Cj2' ^ (2 * q) +
      B / γ ^ (2 * q) * Cg2') with hKdef
  have hK0 : 0 ≤ K := by
    have : 0 ≤ Cj2' ^ (2 * q) := by rw [pow_mul]; positivity
    positivity
  refine ⟨min c 1, K, lt_min hc one_pos, min_le_right _ _, hK0, fun T => ?_⟩
  obtain ⟨Wg1, hWg1⟩ := hCg1 T
  obtain ⟨Wg2, hWg2⟩ := hCg2 T
  obtain ⟨Wj1, hWj1⟩ := hCj1 T
  obtain ⟨Wj2, hWj2⟩ := hCj2 T
  refine ⟨max (max (max W₁ 1) (max Wg1 Wg2)) (max Wj1 Wj2),
    fun W hW r hr1 hεr hrT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW₁, hW1⟩, hWg1', hWg2'⟩, hWj1', hWj2'⟩ := hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWp : (0 : ℝ) < W := by linarith
  obtain ⟨s, hs⟩ := PassiveCovariance.stationaryJet_exists hb0 hb h1 h2
  set μ := growthPathLaw W b
  have := Transmission.Bridge.isProbabilityMeasure_growthPathLaw W b
  set X := pathX b E W r
  have hXm : Measurable X := PathJet.measurable_pathX b E r
  have hpas := mm_ae_passive (W := W) (b := b) (by linarith) h1 h2 r
  -- the moments on the path
  set Pf := fun ω => fracTrace α (pathTransmission b E (fun _ => 0) W r ω)
  obtain ⟨hPqi, -⟩ := pathFrac_pow_facts (W := W) hα0 hα1 hb h1 h2 r q
  obtain ⟨hPq1i, -⟩ := pathFrac_pow_facts (W := W) hα0 hα1 hb h1 h2 r (q + 1)
  set gf := fun ω => conductanceOf (passiveTransmission b E (X ω))
  have hgm : Measurable gf := measurable_pathConductance b E r
  have hgb : ∀ᵐ ω ∂μ, 0 ≤ gf ω ∧ gf ω ≤ W := by
    filter_upwards [pathPower_mem (W := W) (b := b) (by linarith) h1 h2] with ω h
    obtain ⟨-, -, h3⟩ := h 1 r le_rfl
    exact ⟨(h 1 r le_rfl).1.trans (h 1 r le_rfl).2.1, h3⟩
  have hgn : ∀ n : ℕ, Integrable (fun ω => gf ω ^ n) μ := fun n =>
    Integrable.of_bound (hgm.pow_const n).aestronglyMeasurable ((W : ℝ) ^ n) (by
      filter_upwards [hgb] with ω h
      rw [Real.norm_of_nonneg (pow_nonneg h.1 n)]
      exact pow_le_pow_left₀ h.1 h.2 n)
  have hgmom : ∀ (n : ℕ) (Cg : ℝ), 0 ≤ Cg →
      ∫⁻ ω, ‖gf ω‖ₑ ^ ((n : ℕ) : ℝ) ∂μ ≤ ENNReal.ofReal Cg → ∫ ω, gf ω ^ n ∂μ ≤ Cg :=
    fun n Cg hCg h => integral_pow_le_of_lintegral hgm (by filter_upwards [hgb] with ω h; exact h.1)
      n hCg h
  have hg1 : ∫ ω, gf ω ^ (q + 1) ∂μ ≤ Cg1' :=
    hgmom _ _ (le_max_right _ _) ((hWg1 W hWg1' E hEκ r hεr hrT).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hg2 : ∫ ω, gf ω ^ (2 * q) ∂μ ≤ Cg2' :=
    hgmom _ _ (le_max_right _ _) ((hWg2 W hWg2' E hEκ r hεr hrT).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hδ0m : AEStronglyMeasurable (fun ω => jetDistance0 b E (X ω)) μ :=
    ((PathScalar.measurable_jetDistance0 b E).comp hXm).aestronglyMeasurable
  have hδ1m : AEStronglyMeasurable (fun ω => jetDistance1 b E s (X ω)) μ :=
    (PathJet.measurable_pathJetV b E s r).aestronglyMeasurable.congr
      (Filter.EventuallyEq.symm (PathJet.pathJet1_ae_eq (W := W) (b := b) (by linarith) h1 h2 s r))
  have hjet1 := hWj1 W hWj1' E hEκ s hs r hεr hrT
  have hjet2 := hWj2 W hWj2' E hEκ s hs r hεr hrT
  have hC1 : ENNReal.ofReal (Cj1 / W) ≤ ENNReal.ofReal (Cj1' / W) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hWp.le)
  have hC2 : ENNReal.ofReal (Cj2 / W) ≤ ENNReal.ofReal (Cj2' / W) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hWp.le)
  have hn1 : 1 ≤ q + 1 := by omega
  have hn2 : 1 ≤ 2 * q := by omega
  obtain ⟨hd01i, hd01⟩ := powN_of_eLpNorm hδ0m (fun ω => norm_nonneg _) hn1 (by positivity)
    ((le_self_add.trans hjet1).trans hC1)
  obtain ⟨hd02i, hd02⟩ := powN_of_eLpNorm hδ0m (fun ω => norm_nonneg _) hn2 (by positivity)
    ((le_self_add.trans hjet2).trans hC2)
  obtain ⟨hd12i, hd12⟩ := powN_of_eLpNorm hδ1m (fun ω => norm_nonneg _) hn2 (by positivity)
    ((le_add_self.trans hjet2).trans hC2)
  -- the step
  set Ψ : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort → ℝ :=
    fun z => stepFrac α b E z.1 z.2 ^ q
  have hΨm : Measurable Ψ := (measurable_stepFrac α b E).pow_const q
  have hΨb : ∀ z, |Ψ z| ≤ (W : ℝ) ^ q := fun z => by
    rw [abs_of_nonneg (pow_nonneg (stepFrac_nonneg _ _ _ _ _) _)]
    exact pow_le_pow_left₀ (stepFrac_nonneg _ _ _ _ _) (stepFrac_le _ _ _ _ _) q
  have hinner : Measurable fun ω => ∫ y, Ψ (X ω, y) ∂freshLaw W b :=
    (hΨm.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable.comp hXm
  have hini : Integrable (fun ω => ∫ y, Ψ (X ω, y) ∂freshLaw W b) μ :=
    Integrable.of_bound hinner.aestronglyMeasurable ((W : ℝ) ^ q)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        calc |∫ y, Ψ (X ω, y) ∂freshLaw W b| ≤ ∫ y, |Ψ (X ω, y)| ∂freshLaw W b :=
              abs_integral_le_integral_abs
          _ ≤ ∫ _y, (W : ℝ) ^ q ∂freshLaw W b :=
              integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
                (integrable_const _) (Filter.Eventually.of_forall fun y => hΨb _)
          _ = (W : ℝ) ^ q := by simp)
  have hsucc : pathPow α b E W (r + 1) q = ∫ ω, (∫ y, Ψ (X ω, y) ∂freshLaw W b) ∂μ := by
    rw [pathPow]
    rw [integral_congr_ae ((ae_pathFrac_succ hα0 hα1 hb hW1 h1 h2 hr1).mono fun ω h => by rw [h])]
    exact integral_fresh_eq b E hΨm hΨb r
  -- the coefficients
  set a₂ := -(c / W)
  set a₃ := A * (W : ℝ) ^ q
  set a₄ := A / W
  set a₅ := B * (W : ℝ) ^ q / d ^ (2 * q)
  set a₆ := B * (W : ℝ) ^ q / d ^ (2 * q)
  set a₇ := B * (W : ℝ) ^ q / (γ * W) ^ (2 * q)
  have hbnd : ∀ᵐ ω ∂μ, ∫ y, Ψ (X ω, y) ∂freshLaw W b ≤
      Pf ω ^ q + a₂ * Pf ω ^ (q + 1) + a₃ * jetDistance0 b E (X ω) ^ (q + 1) +
        a₄ * gf ω ^ (q + 1) + a₅ * jetDistance0 b E (X ω) ^ (2 * q) +
        a₆ * jetDistance1 b E s (X ω) ^ (2 * q) + a₇ * gf ω ^ (2 * q) + A / W := by
    filter_upwards [hpas] with ω hω
    have h := hSt W hW₁ s hs (X ω) hω
    have e : Pf ω = fracTrace α (passiveTransmission b E (X ω)) := rfl
    rw [e]
    refine h.trans (le_of_eq ?_)
    simp only [a₂, a₃, a₄, a₅, a₆, a₇, gf, div_pow]
    ring
  have hRi : Integrable (fun ω => Pf ω ^ q + a₂ * Pf ω ^ (q + 1) +
      a₃ * jetDistance0 b E (X ω) ^ (q + 1) + a₄ * gf ω ^ (q + 1) +
      a₅ * jetDistance0 b E (X ω) ^ (2 * q) + a₆ * jetDistance1 b E s (X ω) ^ (2 * q) +
      a₇ * gf ω ^ (2 * q) + A / W) μ :=
    ((((((hPqi.add (hPq1i.const_mul _)).add (hd01i.const_mul _)).add ((hgn _).const_mul _)).add
      (hd02i.const_mul _)).add (hd12i.const_mul _)).add ((hgn _).const_mul _)).add
      (integrable_const _)
  have hle := integral_mono_ae hini hRi hbnd
  rw [integral_eight _ _ _ _ _ _ _ hPqi hPq1i hd01i (hgn _) hd02i hd12i (hgn _)] at hle
  rw [hsucc]
  have hyq : pathPow α b E W r q = ∫ ω, Pf ω ^ q ∂μ := rfl
  have hyq1 : pathPow α b E W r (q + 1) = ∫ ω, Pf ω ^ (q + 1) ∂μ := rfl
  rw [hyq, hyq1]
  have hP1 : 0 ≤ ∫ ω, Pf ω ^ (q + 1) ∂μ :=
    integral_nonneg fun _ => pow_nonneg (fracTrace_nonneg' _ _) _
  -- the error terms
  have ha₃ : 0 ≤ a₃ := by positivity
  have ha₄ : 0 ≤ a₄ := by positivity
  have ha₅ : 0 ≤ a₅ := by positivity
  have ha₇ : 0 ≤ a₇ := by positivity
  have k3 : a₃ * ∫ ω, jetDistance0 b E (X ω) ^ (q + 1) ∂μ ≤ A * Cj1' ^ (q + 1) / W := by
    calc a₃ * ∫ ω, jetDistance0 b E (X ω) ^ (q + 1) ∂μ ≤ a₃ * (Cj1' / W) ^ (q + 1) :=
          mul_le_mul_of_nonneg_left hd01 ha₃
      _ = A * Cj1' ^ (q + 1) / W := by
          simp only [a₃]; rw [mul_assoc, pow_mul_div_pow_succ hWp]; ring
  have k4 : a₄ * ∫ ω, gf ω ^ (q + 1) ∂μ ≤ A * Cg1' / W := by
    calc a₄ * ∫ ω, gf ω ^ (q + 1) ∂μ ≤ a₄ * Cg1' := mul_le_mul_of_nonneg_left hg1 ha₄
      _ = A * Cg1' / W := by simp only [a₄]; ring
  have k5 : ∀ Z : ℝ, Z ≤ (Cj2' / W) ^ (2 * q) →
      a₅ * Z ≤ B / d ^ (2 * q) * Cj2' ^ (2 * q) / W := by
    intro Z hZ
    calc a₅ * Z ≤ a₅ * (Cj2' / W) ^ (2 * q) := mul_le_mul_of_nonneg_left hZ ha₅
      _ = B / d ^ (2 * q) * ((W : ℝ) ^ q * (Cj2' / W) ^ (2 * q)) := by simp only [a₅]; ring
      _ ≤ B / d ^ (2 * q) * (Cj2' ^ (2 * q) / W) :=
          mul_le_mul_of_nonneg_left (pow_mul_div_pow_two_mul_le hWr _ hq) (by positivity)
      _ = B / d ^ (2 * q) * Cj2' ^ (2 * q) / W := by ring
  have k7 : a₇ * ∫ ω, gf ω ^ (2 * q) ∂μ ≤ B / γ ^ (2 * q) * Cg2' / W := by
    calc a₇ * ∫ ω, gf ω ^ (2 * q) ∂μ ≤ a₇ * Cg2' := mul_le_mul_of_nonneg_left hg2 ha₇
      _ = B / γ ^ (2 * q) * Cg2' * ((W : ℝ) ^ q / (W : ℝ) ^ (2 * q)) := by
          simp only [a₇, mul_pow]; ring
      _ ≤ B / γ ^ (2 * q) * Cg2' * (1 / W) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_div_iff₀ (by positivity) hWp, one_mul, two_mul, pow_add]
          have : (W : ℝ) ≤ (W : ℝ) ^ q := le_self_pow₀ hWr (by omega)
          nlinarith [pow_pos hWp q]
      _ = B / γ ^ (2 * q) * Cg2' / W := by ring
  have k56 := k5 _ hd02
  have k66 : a₆ * ∫ ω, jetDistance1 b E s (X ω) ^ (2 * q) ∂μ ≤
      B / d ^ (2 * q) * Cj2' ^ (2 * q) / W := k5 _ hd12
  have kc : -(c / W) * ∫ ω, Pf ω ^ (q + 1) ∂μ ≤ -(min c 1 / W) * ∫ ω, Pf ω ^ (q + 1) ∂μ := by
    have : min c 1 / W ≤ c / W := div_le_div_of_nonneg_right (min_le_left _ _) hWp.le
    have := mul_le_mul_of_nonneg_right this hP1
    linarith
  have hKW : A * Cj1' ^ (q + 1) / W + A / W + A * Cg1' / W +
      (B / d ^ (2 * q) * Cj2' ^ (2 * q) / W + B / d ^ (2 * q) * Cj2' ^ (2 * q) / W +
        B / γ ^ (2 * q) * Cg2' / W) = K / W := by
    rw [hKdef]; ring
  have e2 : min c 1 / W * ∫ ω, Pf ω ^ (q + 1) ∂μ = -(-(min c 1 / W) * ∫ ω, Pf ω ^ (q + 1) ∂μ) :=
    by ring
  rw [e2]
  linarith

end BlockBand.SourceProcess.PhysApprox.B3.FracMom
