module

public import BlockBand.Transmission.Absorbed.ShiftLayer
public import BlockBand.Transmission.Absorbed.PathStep
public import BlockBand.Transmission.Generator.ModPath

/-!
# The absorbed modulus: one absorbed step at path level

* `absPower b E κ W k r = Re Tr (T^κ_r)^k` (so `absorbedPowerTrace … t = absPower … ⌊Wt⌋₊`);
  `stronglyMeasurable_absPower` (adapted), `ae_abs_absPower_le` (`|·| ≤ W` a.s.);
* `condExp_fresh_past`: `condExp_fresh` for any measurable function `S` of the past
  coordinates (`E[Ψ(S(past_j), fresh_j) ∣ 𝓕_j] = ∫ Ψ(S(past_j), y) dfresh(y)` a.s.);
* `absStep` (clamped `Ψ(X, y) = cl Tr T(freshSchur(X - iε_j, y))^k - cl Tr T(X)^k`) and
  `ae_modInc_absPower` (`Δ_j = Ψ(X_j, fresh_j)` a.s., `j ≥ 1`; the absorbed step identity);
* **`integral_absInc_pow_four_le`**: a layer bound `∫Ψ(X, ·)⁴ ≤ G(X)` at passive inputs gives
  `E Δ_j⁴ ≤ E G(X_j)` (`abs_integral_path_le`);
* **`ae_abs_condExp_absInc_le`**: a layer bound `|∫Ψ(X, ·)| ≤ G(X)` at passive inputs gives
  `|E[Δ_j ∣ 𝓕_j]| ≤ G(X_j)` a.s.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.LawFinite BlockBand.Transmission.Generator
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- `Re Tr (T^κ_r)^k`. -/
def absPower (b E : ℝ) (κ : ℝ → ℝ) (W k r : ℕ) (ω : GrowthPath W) : ℝ :=
  ((pathTransmission b E κ W r ω) ^ k).trace.re

theorem absorbedPowerTrace_eq (b E : ℝ) (κ : ℝ → ℝ) (W k : ℕ) (t : ℝ) (ω : GrowthPath W) :
    LawDuality.absorbedPowerTrace b E κ W k t ω = absPower b E κ W k ⌊(W : ℝ) * t⌋₊ ω := rfl

theorem stronglyMeasurable_absPower (b E : ℝ) (κ : ℝ → ℝ) (k r : ℕ) :
    StronglyMeasurable[growthFiltration W r] (absPower b E κ W k r) :=
  ((measurable_trace_pow_transmission b E k).comp
    (pathNearSchur_adapted b E κ W r)).stronglyMeasurable

theorem ae_abs_absPower_le {b E : ℝ} {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) (hb : b < 1)
    (h1 : -2 < E) (h2 : E < 2) {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, |absPower b E κ W k r ω| ≤ W := by
  filter_upwards [ae_passiveSample W hκ hb h1 h2] with ω hP
  obtain ⟨a0, a1⟩ := trace_pow_le_card (b := b) hb h1 h2 (pathNearSchur_passive hP r) hk
  rw [absPower, pathTransmission, abs_of_nonneg a0]; exact a1

/-- **Conditional expectation over one fresh layer, any measurable input of the past.** -/
theorem condExp_fresh_past (b : ℝ) {j : ℕ} {S : PastSample W j → Matrix (Fin W) (Fin W) ℂ}
    (hS : Measurable S)
    {Ψ : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort → ℝ} (hΨ : Measurable Ψ)
    {M : ℝ} (hΨM : ∀ x, |Ψ x| ≤ M) :
    (growthPathLaw W b)[fun ω => Ψ (S (pastCoords W j ω), freshSample W j ω) | growthSigma W j]
      =ᵐ[growthPathLaw W b] fun ω => ∫ y, Ψ (S (pastCoords W j ω), y) ∂freshLaw W b := by
  set μ := growthPathLaw W b
  set G : Matrix (Fin W) (Fin W) ℂ → ℝ := fun X => ∫ y, Ψ (X, y) ∂freshLaw W b
  have hG : Measurable G :=
    (hΨ.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable
  have hGM : ∀ X, |G X| ≤ M := fun X => by
    have := norm_integral_le_of_norm_le_const (μ := freshLaw W b) (f := fun y => Ψ (X, y))
      (C := M) (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hΨM _)
    simpa [Real.norm_eq_abs, Measure.real, measure_univ] using this
  have hm : growthSigma W j ≤ (inferInstance : MeasurableSpace (GrowthPath W)) :=
    growthSigma_le W j
  have hT := (measurable_pastCoords W j).prodMk (measurable_freshSample W j)
  have hXm : Measurable fun ω => S (pastCoords W j ω) := hS.comp (measurable_pastCoords W j)
  have hf : Integrable (fun ω => Ψ (S (pastCoords W j ω), freshSample W j ω)) μ :=
    Integrable.of_bound ((hΨ.comp (hXm.prodMk (measurable_freshSample W j))).aestronglyMeasurable)
      M (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hΨM _)
  have hgm : Measurable[growthSigma W j] fun ω => G (S (pastCoords W j ω)) :=
    (hG.comp hS).comp (comap_measurable (pastCoords W j))
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hf (fun s _ _ => ?_) (fun s hs _ => ?_)
    hgm.aestronglyMeasurable).symm
  · exact (Integrable.of_bound ((hG.comp hXm).aestronglyMeasurable) M
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hGM _)).integrableOn
  obtain ⟨B, hB, rfl⟩ := hs
  show ∫ x in pastCoords W j ⁻¹' B, G (S (pastCoords W j x)) ∂μ =
    ∫ x in pastCoords W j ⁻¹' B, Ψ (S (pastCoords W j x), freshSample W j x) ∂μ
  set Φ : PastSample W j × LayerSample W .oneBlockOnePort → ℝ :=
    fun x => B.indicator (fun _ => (1 : ℝ)) x.1 * Ψ (S x.1, x.2)
  have hΦ : Measurable Φ :=
    ((measurable_const.indicator hB).comp measurable_fst).mul
      (hΨ.comp ((hS.comp measurable_fst).prodMk measurable_snd))
  have hΦi : Integrable Φ ((pastLaw W j b).prod (freshLaw W b)) := by
    refine Integrable.of_bound hΦ.aestronglyMeasurable M (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hx : x.1 ∈ B
    · simp only [Set.indicator_of_mem hx, abs_one, one_mul]; exact hΨM _
    · simp only [Set.indicator_of_notMem hx, abs_zero, zero_mul]
      exact (abs_nonneg _).trans (hΨM (S x.1, x.2))
  have e1 : ∫ ω in pastCoords W j ⁻¹' B, Ψ (S (pastCoords W j ω), freshSample W j ω) ∂μ =
      ∫ x, Φ x ∂((pastLaw W j b).prod (freshLaw W b)) := by
    rw [← integral_indicator (measurable_pastCoords W j hB), ← growthPathLaw_map_past_fresh,
      integral_map hT.aemeasurable hΦ.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    by_cases hω : pastCoords W j ω ∈ B
    · simp [Φ, Set.indicator_of_mem hω, Set.indicator_of_mem (show ω ∈ pastCoords W j ⁻¹' B
        from hω)]
    · simp [Φ, Set.indicator_of_notMem hω, Set.indicator_of_notMem (show ω ∉ pastCoords W j ⁻¹' B
        from hω)]
  have e2 : ∫ ω in pastCoords W j ⁻¹' B, G (S (pastCoords W j ω)) ∂μ =
      ∫ p, B.indicator (fun _ => (1 : ℝ)) p * G (S p) ∂pastLaw W j b := by
    rw [← integral_indicator (measurable_pastCoords W j hB), ← growthPathLaw_map_pastCoords,
      integral_map (f := fun p => B.indicator (fun _ => (1 : ℝ)) p * G (S p))
        (measurable_pastCoords W j).aemeasurable
        (((measurable_const.indicator hB).mul (hG.comp hS)).aestronglyMeasurable)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    by_cases hω : pastCoords W j ω ∈ B
    · simp [Set.indicator_of_mem hω, Set.indicator_of_mem (show ω ∈ pastCoords W j ⁻¹' B
        from hω)]
    · simp [Set.indicator_of_notMem hω, Set.indicator_of_notMem (show ω ∉ pastCoords W j ⁻¹' B
        from hω)]
  rw [e2, e1, integral_prod Φ hΦi]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [Φ, G]
  rw [integral_const_mul]

/-- The clamped absorbed step `Ψ(X, y) = cl Tr T(freshSchur(X - iε, y))^k - cl Tr T(X)^k`. -/
def absStep (b E ε : ℝ) (k : ℕ) (x : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort) :
    ℝ :=
  freshPow b E k (absorbedInput x.1 ε, x.2) -
    clampW W ((passiveTransmission b E x.1) ^ k).trace.re

theorem measurable_absStep (b E ε : ℝ) (k : ℕ) : Measurable (absStep (W := W) b E ε k) := by
  have hc : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => absorbedInput X ε :=
    continuous_id.sub continuous_const
  exact ((measurable_freshPow b E k).comp ((hc.measurable.comp measurable_fst).prodMk
    measurable_snd)).sub (continuous_clampW.measurable.comp
      ((measurable_trace_pow_transmission b E k).comp measurable_fst))

theorem abs_absStep_le (b E ε : ℝ) (k : ℕ)
    (x : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort) :
    |absStep b E ε k x| ≤ W :=
  abs_clampW_sub_le _ _

/-- At a passive input, the clamps are inactive for a.e. fresh layer. -/
theorem ae_absStep_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) {ε : ℝ}
    (hε : 0 ≤ ε) {k : ℕ} (hk : 1 ≤ k) :
    ∀ᵐ y ∂freshLaw W b, absStep b E ε k (X, y) =
      ((passiveTransmission b E (freshSchur E (absorbedInput X ε) y)) ^ k).trace.re -
        ((passiveTransmission b E X) ^ k).trace.re := by
  filter_upwards [PassiveLayer.ae_good W hb0 hW] with y hy
  have hY := PathScalar.passiveY_freshSchur E (LawFinite.passiveY_absorbedInput hX hε) y hy.1
  obtain ⟨a0, a1⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2 hY hk
  obtain ⟨c0, c1⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2 hX hk
  simp only [absStep, freshPow]
  rw [clampW_of_mem a0 a1, clampW_of_mem c0 c1]

/-- **The absorbed increment through one fresh layer**, a.s., `j ≥ 1`. -/
theorem ae_modInc_absPower {b E : ℝ} (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (hW : 1 ≤ W)
    {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) {k : ℕ} (hk : 1 ≤ k) {j : ℕ} (hj : 1 ≤ j) :
    ∀ᵐ ω ∂growthPathLaw W b, modInc (absPower b E κ W k) j ω =
      absStep b E (layerAbsorption W κ (j + 1) 0) k
        (pastX b E κ W j (pastCoords W j ω), freshSample W j ω) := by
  filter_upwards [ae_pathNearSchur_succ_abs (W := W) (b := b) hb h1 h2 hW hκ,
    ae_passiveSample W hκ (by linarith) h1 h2] with ω hω hP
  have hj1 := pathNearSchur_passive hP (j + 1)
  have hj0 := pathNearSchur_passive hP j
  obtain ⟨a0, a1⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2 hj1 hk
  obtain ⟨c0, c1⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2 hj0 hk
  rw [hω j hj] at a0 a1
  simp only [modInc, Pi.sub_apply, absPower, pathTransmission, absStep, freshPow,
    ← pathNearSchur_eq_past]
  rw [hω j hj, clampW_of_mem c0 c1]
  exact congrArg (· - _) (clampW_of_mem a0 a1).symm

/-- **The path-level fourth moment of one absorbed step.** -/
theorem integral_absInc_pow_four_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) (hW : 1 ≤ W) {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) {k : ℕ} (hk : 1 ≤ k) {j : ℕ}
    (hj : 1 ≤ j) {G : Matrix (Fin W) (Fin W) ℂ → ℝ} (hG : Measurable G)
    (hGi : Integrable (fun ω => G (pathNearSchur b E κ W j ω)) (growthPathLaw W b))
    (hL : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∫ y, (((passiveTransmission b E (freshSchur E (absorbedInput X
        (layerAbsorption W κ (j + 1) 0)) y)) ^ k).trace.re -
          ((passiveTransmission b E X) ^ k).trace.re) ^ 4 ∂freshLaw W b ≤ G X) :
    ∫ ω, modInc (absPower b E κ W k) j ω ^ 4 ∂growthPathLaw W b ≤
      ∫ ω, G (pathNearSchur b E κ W j ω) ∂growthPathLaw W b := by
  set ε := layerAbsorption W κ (j + 1) 0
  have hε : 0 ≤ ε := div_nonneg (hκ _) (sq_nonneg _)
  have hΨ : Measurable fun x : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort =>
      absStep b E ε k x ^ 4 := (measurable_absStep b E ε k).pow_const 4
  have hΨM : ∀ x, ‖absStep b E ε k x ^ 4‖ ≤ (W : ℝ) ^ 4 := fun x => by
    rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_absStep_le _ _ _ _ _) 4
  have hGi' : Integrable (fun ω => (G ∘ pastX b E κ W j) (pastCoords W j ω)) (growthPathLaw W b) :=
    hGi.congr (ae_of_all _ fun ω => by simp only [Function.comp, pathNearSchur_eq_past])
  have hmain := abs_integral_path_le (b := b) (measurable_pastX b E κ j) hΨ hΨM
    (hG.comp (measurable_pastX b E κ j)) hGi' fun p hp => by
      have hY := passiveY_pastX (b := b) (by linarith) h1 h2 hκ hp
      refine le_of_eq_of_le (integral_congr_ae ?_) (hL _ hY)
      filter_upwards [ae_absStep_eq hb0 hb h1 h2 hW hY hε hk] with y hy
      rw [hy]
  refine le_of_eq_of_le (integral_congr_ae ?_) (hmain.trans_eq (integral_congr_ae
    (ae_of_all _ fun ω => by simp only [Function.comp, pathNearSchur_eq_past])))
  filter_upwards [ae_modInc_absPower hb h1 h2 hW hκ hk hj] with ω hω
  rw [hω]

/-- **The conditional mean of one absorbed step, a.s.** -/
theorem ae_abs_condExp_absInc_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) (hW : 1 ≤ W) {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) {k : ℕ} (hk : 1 ≤ k) {j : ℕ}
    (hj : 1 ≤ j) {G : Matrix (Fin W) (Fin W) ℂ → ℝ}
    (hL : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      |∫ y, (((passiveTransmission b E (freshSchur E (absorbedInput X
        (layerAbsorption W κ (j + 1) 0)) y)) ^ k).trace.re -
          ((passiveTransmission b E X) ^ k).trace.re) ∂freshLaw W b| ≤ G X) :
    ∀ᵐ ω ∂growthPathLaw W b,
      |((growthPathLaw W b)[modInc (absPower b E κ W k) j | growthFiltration W j]) ω| ≤
        G (pathNearSchur b E κ W j ω) := by
  set ε := layerAbsorption W κ (j + 1) 0
  have hε : 0 ≤ ε := div_nonneg (hκ _) (sq_nonneg _)
  have hc1 : (growthPathLaw W b)[modInc (absPower b E κ W k) j | growthFiltration W j] =ᵐ[
      growthPathLaw W b] (growthPathLaw W b)[fun ω => absStep b E ε k
        (pastX b E κ W j (pastCoords W j ω), freshSample W j ω) | growthSigma W j] :=
    condExp_congr_ae (ae_modInc_absPower hb h1 h2 hW hκ hk hj)
  have hc2 := condExp_fresh_past (W := W) b (measurable_pastX b E κ j) (measurable_absStep b E ε k)
    (abs_absStep_le b E ε k)
  filter_upwards [hc1, hc2, ae_passiveSample W hκ (by linarith) h1 h2] with ω e1 e2 hP
  have hY := pathNearSchur_passive hP j
  rw [e1, e2, ← pathNearSchur_eq_past]
  refine le_of_eq_of_le (congrArg abs (integral_congr_ae ?_)) (hL _ hY)
  filter_upwards [ae_absStep_eq hb0 hb h1 h2 hW hY hε hk] with y hy
  rw [hy]

end BlockBand.Transmission.Absorbed
