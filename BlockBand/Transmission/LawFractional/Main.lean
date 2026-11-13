module

public import BlockBand.Transmission.LawFractional.Rec
public import BlockBand.Transmission.LawFractional.Logistic
public import BlockBand.Transmission.FractionalBulk.Main
public import BlockBand.Transmission.EnergyUniform.Window
public import BlockBand.Internal.Contracts.TransmissionLaws

/-!
# The fractional transmission bound with the constant `C_p(1 + t⁻¹)`

Homogeneous (`κ ≡ 0`) near-end-grown path `growthPathLaw W b`, `T_r = pathTransmission b E 0 W r`,
`Tr T^p = fracTrace p T`. Hypotheses `MatchedTracesContract`, `GaussianAbsorptionContract`,
`GaussianLpGradient` and `GaussianPoincare`.

* **`fractional_bulk hMT hGA hLp hP`**: `b`, a bulk margin `κI`, `0 < p < 1` first; then one
  `C ≥ 0`; for every `t > 0` there is `W₀` with `E Tr T_{⌊Wt⌋}^p ≤ C(1 + t⁻¹)` for all
  `W ≥ W₀` and all `E ∈ bulkInterval κI`.
* **`fractional_holds`**: the field `TransmissionLawContract.fractional` (margin
  `min(E+2, 2-E)`).
* **`fractional_moving_holds`**: the field `TransmissionLawEnergyUniformContract.fractional`
  (moving energies `|e_W - E| ≤ C_e W⁻²`; margin halved, `EnergyUniform.window_mem_bulkInterval`).

Proof. `pathRec_explicit` at time floor `t/4` and length `t` gives the recursion with forcing
`F = K₀ + K₁(1 + 4/t)² ≤ 16(K₀ + K₁)(1 + t⁻¹)²`. Run it for `m = ⌊Wt/2⌋ ≥ Wt/4` steps ending at
`⌊Wt⌋` (the window of `fractionalBulk_holds`, with `ε = t`). `logistic_scaled` with
`M = m₀(1 + t⁻¹)`, `m₀ = 16(K₀ + K₁)/c + 1` (so `F ≤ cM²`) gives
`y_{⌊Wt⌋} ≤ max(2M + F/W, 8/(ct)) ≤ (2m₀ + 1 + 8/c)(1 + t⁻¹)` once `W ≥ F`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFractional

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.FractionalBulk
open scoped ENNReal

/-- The time window: `r₀ + m = ⌊x⌋`, `m ≥ 1`, `x/4 ≤ r₀` and `x ≤ 4m`, for `x > 8`. -/
theorem window_split {x : ℝ} (hx8 : 8 < x) :
    ∃ r₀ m : ℕ, r₀ + m = ⌊x⌋₊ ∧ 1 ≤ m ∧ x / 4 ≤ r₀ ∧ x ≤ 4 * m ∧ ((r₀ + m : ℕ) : ℝ) ≤ x := by
  have hx0 : 0 ≤ x := by linarith
  set r₁ := ⌊x⌋₊
  set m := ⌊x / 2⌋₊
  have hmle : (m : ℝ) ≤ x / 2 := Nat.floor_le (by positivity)
  have hmge : x / 2 - 1 < m := by have := Nat.lt_floor_add_one (x / 2); linarith
  have hr₁le : (r₁ : ℝ) ≤ x := Nat.floor_le hx0
  have hr₁ge : x - 1 < r₁ := by have := Nat.lt_floor_add_one x; linarith
  have hmr₁ : m ≤ r₁ := by
    have : (m : ℝ) < r₁ + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  refine ⟨r₁ - m, m, Nat.sub_add_cancel hmr₁, ?_, ?_, by linarith, ?_⟩
  · have : (1 : ℝ) < m := by linarith
    exact_mod_cast this.le
  · rw [Nat.cast_sub hmr₁]; linarith
  · rw [Nat.sub_add_cancel hmr₁]; exact hr₁le

/-- The scale `M = m₀(1 + t⁻¹)`, `m₀ = 16(K₀ + K₁)/c + 1`, dominates the forcing:
`K₀ + K₁(1 + (t/4)⁻¹)² ≤ cM²`. -/
theorem forcing_le {c K₀ K₁ t : ℝ} (hc : 0 < c) (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (ht : 0 < t) :
    K₀ + K₁ * (1 + (t / 4)⁻¹) ^ 2 ≤ c * ((16 * (K₀ + K₁) / c + 1) * (1 + t⁻¹)) ^ 2 := by
  set m₀ := 16 * (K₀ + K₁) / c + 1 with hm₀def
  have hu : 0 ≤ t⁻¹ := by positivity
  have hF16 : K₀ + K₁ * (1 + (t / 4)⁻¹) ^ 2 ≤ 16 * (K₀ + K₁) * (1 + t⁻¹) ^ 2 := by
    have e4 : (t / 4)⁻¹ = 4 * t⁻¹ := by field_simp
    have hq : (1 + (t / 4)⁻¹) ^ 2 ≤ 16 * (1 + t⁻¹) ^ 2 := by rw [e4]; nlinarith
    have hsq : 1 ≤ (1 + t⁻¹) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hq hK₁]
  have hcm : c * m₀ = 16 * (K₀ + K₁) + c := by rw [hm₀def]; field_simp
  have hm₀ : 1 ≤ m₀ := by
    have : 0 ≤ 16 * (K₀ + K₁) / c := by positivity
    linarith
  have hcm2 : 16 * (K₀ + K₁) ≤ c * m₀ ^ 2 := by nlinarith
  calc K₀ + K₁ * (1 + (t / 4)⁻¹) ^ 2 ≤ 16 * (K₀ + K₁) * (1 + t⁻¹) ^ 2 := hF16
    _ ≤ c * m₀ ^ 2 * (1 + t⁻¹) ^ 2 := mul_le_mul_of_nonneg_right hcm2 (by positivity)
    _ = c * (m₀ * (1 + t⁻¹)) ^ 2 := by ring

/-- The final arithmetic: `max(2M + F/W, 2/((c/W)m)) ≤ (2m₀ + 1 + 8/c)(1 + t⁻¹)`. -/
theorem final_le {c m₀ t F w m : ℝ} (hc : 0 < c) (hm₀ : 0 ≤ m₀) (ht : 0 < t) (hw : 0 < w)
    (hFw : F ≤ w) (hm : w * t ≤ 4 * m) (hm0 : 0 < m) :
    max (2 * (m₀ * (1 + t⁻¹)) + F / w) (2 / (c / w * m)) ≤ (2 * m₀ + 1 + 8 / c) * (1 + t⁻¹) := by
  have hu : 0 ≤ t⁻¹ := by positivity
  have hFW1 : F / w ≤ 1 := by rw [div_le_one hw]; exact hFw
  have h2m : 2 / (c / w * m) ≤ 8 / c * t⁻¹ := by
    have e : 2 / (c / w * m) = 2 * w / (c * m) := by field_simp
    have e' : 8 / c * t⁻¹ = 8 / (c * t) := by field_simp
    rw [e, e', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h8 : 0 ≤ 8 / c := by positivity
  refine max_le ?_ (h2m.trans ?_)
  · nlinarith
  · nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * m₀ + 1) (by positivity : 0 ≤ 1 + t⁻¹)]

/-- **The fractional bound `C(1 + t⁻¹)` at finite `W`, uniformly on `bulkInterval κI`.** -/
theorem fractional_bulk (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∀ p : ℝ, 0 < p → p < 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∫⁻ ω, ENNReal.ofReal (fracTrace p (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
        ∂growthPathLaw W b ≤ ENNReal.ofReal (C * (1 + t⁻¹)) := by
  intro b hb0 hb κI hκ p hp0 hp1
  obtain ⟨c, K₀, K₁, hc, hK₀, hK₁, hR⟩ := pathRec_explicit hMT hGA hLp hP hp0 hp1 hb0 hb hκ
  have hm₀ : 0 ≤ 16 * (K₀ + K₁) / c + 1 := by positivity
  refine ⟨2 * (16 * (K₀ + K₁) / c + 1) + 1 + 8 / c, by positivity, fun t ht => ?_⟩
  obtain ⟨W₁, hW₁⟩ := hR (t / 4) (by positivity) t
  refine ⟨max W₁ (max (⌈8 / t⌉₊ + 1) ⌈K₀ + K₁ * (1 + (t / 4)⁻¹) ^ 2⌉₊), fun W hW E hE => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨hWW₁, hW8, hWF⟩ := hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hWr : (8 / t : ℝ) < W := by
    have := Nat.le_ceil (8 / t)
    have : ((⌈8 / t⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW8
    push_cast at this; linarith
  have hWp : (0 : ℝ) < W := lt_of_le_of_lt (by positivity) hWr
  have hFW : K₀ + K₁ * (1 + (t / 4)⁻¹) ^ 2 ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWF)
  have hx8 : 8 < (W : ℝ) * t := by rwa [div_lt_iff₀ ht] at hWr
  obtain ⟨r₀, m, hsum, hm1, hr₀ge, hm4, hrm⟩ := window_split hx8
  have hrec : ∀ k, k < m → pathFrac p b E W (r₀ + k + 1) ≤
      pathFrac p b E W (r₀ + k) - c / W * pathFrac p b E W (r₀ + k) ^ 2 +
        (K₀ + K₁ * (1 + (t / 4)⁻¹) ^ 2) / W := by
    intro k hk
    have hr1 : 1 ≤ r₀ + k := by
      have : (1 : ℝ) ≤ r₀ := by linarith
      have : 1 ≤ r₀ := by exact_mod_cast this
      omega
    have hk' : ((r₀ + k : ℕ) : ℝ) ≤ ((r₀ + m : ℕ) : ℝ) := by exact_mod_cast (by omega : r₀ + k ≤ r₀ + m)
    have hrε : t / 4 * W ≤ ((r₀ + k : ℕ) : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith
    exact hW₁ W hWW₁ E hE (r₀ + k) hr1 hrε (by linarith)
  have hFM' : (K₀ + K₁ * (1 + (t / 4)⁻¹) ^ 2) / W ≤
      c / W * ((16 * (K₀ + K₁) / c + 1) * (1 + t⁻¹)) ^ 2 := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (forcing_le hc hK₀ hK₁ ht) hWp.le
  have hlog := logistic_scaled (y := fun r => pathFrac p b E W r) (a := c / W)
    (by positivity) (by positivity) (by positivity) hFM' r₀ m
    (fun k => pathFrac_nonneg p b E _) hrec m hm1 le_rfl
  rw [hsum] at hlog
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hyb := hlog.trans (final_le hc hm₀ ht hWp hFW hm4 hm0)
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_pathFrac hp0 hp1 hb h1 h2 _)
    (Filter.Eventually.of_forall fun ω => fracTrace_nonneg' _ _)]
  exact ENNReal.ofReal_le_ofReal hyb

/-- **The field `TransmissionLawContract.fractional`.** -/
theorem fractional_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∃ C : ℝ, ∀ t : ℝ, 0 < t →
      limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
          (fracTrace p (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
          ∂growthPathLaw W b) atTop ≤ ENNReal.ofReal (C * (1 + t⁻¹)) := by
  intro b hb0 hb E h1 h2 p hp0 hp1
  have hκ : 0 < min (E + 2) (2 - E) := lt_min (by linarith) (by linarith)
  have hE : E ∈ bulkInterval (min (E + 2) (2 - E)) :=
    ⟨by have := min_le_left (E + 2) (2 - E); linarith,
      by have := min_le_right (E + 2) (2 - E); linarith⟩
  obtain ⟨C, -, hC⟩ := fractional_bulk hMT hGA hLp hP b hb0 hb _ hκ p hp0 hp1
  refine ⟨C, fun t ht => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC t ht
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop W₀] with W hW
  exact hW₀ W hW E hE

/-- **The field `TransmissionLawEnergyUniformContract.fractional`** (moving energies). -/
theorem fractional_moving_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∃ C : ℝ, ∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e →
      ∀ t : ℝ, 0 < t →
        limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
            (fracTrace p (pathTransmission b (e W) (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
            ∂growthPathLaw W b) atTop ≤ ENNReal.ofReal (C * (1 + t⁻¹)) := by
  intro b hb0 hb E h1 h2 p hp0 hp1
  set κI := min (E + 2) (2 - E)
  have hκ : 0 < κI := lt_min (by linarith) (by linarith)
  have hE : E ∈ bulkInterval κI :=
    ⟨by have := min_le_left (E + 2) (2 - E); linarith,
      by have := min_le_right (E + 2) (2 - E); linarith⟩
  obtain ⟨C, -, hC⟩ := fractional_bulk hMT hGA hLp hP b hb0 hb (κI / 2) (by positivity) p hp0 hp1
  refine ⟨C, fun Ce e he t ht => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC t ht
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop (max (max W₀ (EnergyUniform.windowWidth κI Ce)) 1)]
    with W hW
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW0, hWw⟩, hW1⟩ := hW
  exact hW₀ W hW0 (e W)
    (EnergyUniform.window_mem_bulkInterval hκ hWw hE (he W (by omega)))

end BlockBand.Transmission.LawFractional
