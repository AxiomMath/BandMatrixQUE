module

public import BlockBand.Transmission.FractionalBulk.PathRec
public import BlockBand.Transmission.FractionalBulk.Logistic
public import BlockBand.SourceProcess.FullSourceStops.FractionalAssembly

/-!
# The fractional transmission bound, uniformly on compact bulk sets

* **`fractionalBulk_holds hMT hGA hLp hP`**: `b`, the bulk margin `κI`, `0 < p < 1` and `ε > 0`
  first; then `C`; for every `t ≥ ε` there is `W₀` with
  `E Tr T_{⌊Wt⌋}^p ≤ C` for all `W ≥ W₀` and all `E ∈ bulkInterval κI`, under `growthPathLaw W b`
  (homogeneous, `κ ≡ 0`).
* **`fractionalTransmissionUniformGeneral_holds`**: the same as `limsup_W sup_E ≤ C`.
* **`fractionalTransmissionUniform_holds hMT hGA hLp hP : FullSourceStops.FractionalTransmissionUniform`**
  (the case `p = 1/2`, `t = ε`).
* `fullSourceStopsEnergyUniform_holds`, `fullSourceStops_holds`: the energy-uniform and the
  fixed-`E` full-source stop contracts, through `fullSourceStopsEnergyUniform_holds_of_fractional`
  and `fullSourceStops_holds_of_fractional`.

Hypotheses `MatchedTracesContract`, `GaussianAbsorptionContract`, `GaussianLpGradient`,
`GaussianPoincare`, and `ScalarRecursionContract` for the last two results only.

Proof of the bound: start at `r₀ = ⌊Wt⌋ - ⌊Wε/2⌋ ≥ Wε/4` and run the logistic recursion
`pathRec_bulk` (time floor `ε/4`, length `t`) for `m₀ = ⌊Wε/2⌋ ≥ Wε/4` steps; `logistic_bound`
gives `y_{⌊Wt⌋} ≤ max(max(1, 2K/c) + K, 8/(cε))`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform2
open scoped ENNReal

variable {W : ℕ}

theorem pathFrac_nonneg (p b E : ℝ) (r : ℕ) : 0 ≤ pathFrac p b E W r :=
  integral_nonneg fun _ => fracTrace_nonneg' _ _

theorem integrable_pathFrac {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {b : ℝ} (hb : b < 1 / 2) {E : ℝ}
    (h1 : -2 < E) (h2 : E < 2) (r : ℕ) :
    Integrable (fun ω => fracTrace p (pathTransmission b E (fun _ => 0) W r ω)) (growthPathLaw W b) := by
  obtain ⟨hm, hb'⟩ := pathFrac_facts (W := W) hp0 hp1 hb h1 h2 r
  exact Integrable.of_bound hm W (by
    filter_upwards [hb'] with ω h; rw [Real.norm_of_nonneg h.1]; exact h.2)

/-- **The fractional bound at finite `W`, uniformly on `bulkInterval κI`, for `t ≥ ε`.** -/
theorem fractionalBulk_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∀ p : ℝ, 0 < p → p < 1 →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, ε ≤ t → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI,
        ∫⁻ ω, ENNReal.ofReal (fracTrace p (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
          ∂growthPathLaw W b ≤ ENNReal.ofReal C := by
  intro b hb0 hb κI hκ p hp0 hp1 ε hε
  obtain ⟨c, K, hc, hK, hR⟩ := pathRec_bulk hMT hGA hLp hP hp0 hp1 hb0 hb hκ
    (ε' := ε / 4) (by positivity)
  set M := max 1 (2 * K / c)
  refine ⟨max (M + K) (8 / (c * ε)), fun t ht => ?_⟩
  obtain ⟨W₁, hW₁⟩ := hR t
  refine ⟨max W₁ (⌈8 / ε⌉₊ + 1), fun W hW E hE => ?_⟩
  have hWW₁ : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW8 : ⌈8 / ε⌉₊ + 1 ≤ W := le_trans (le_max_right _ _) hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hWr : (8 / ε : ℝ) < W := by
    have := Nat.le_ceil (8 / ε)
    have : ((⌈8 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW8
    push_cast at this; linarith
  have hWp : (0 : ℝ) < W := lt_of_le_of_lt (by positivity) hWr
  set x := (W : ℝ) * ε with hx
  have hx8 : 8 < x := by rw [hx]; rwa [div_lt_iff₀ hε] at hWr
  set r₁ := ⌊(W : ℝ) * t⌋₊
  set m₀ := ⌊(W : ℝ) * ε / 2⌋₊
  have hm₀le : (m₀ : ℝ) ≤ x / 2 := Nat.floor_le (by positivity)
  have hm₀ge : x / 2 - 1 < m₀ := by
    have := Nat.lt_floor_add_one ((W : ℝ) * ε / 2); rw [← hx] at this; linarith
  have hr₁le : (r₁ : ℝ) ≤ W * t := Nat.floor_le (by nlinarith)
  have hr₁ge : (W : ℝ) * t - 1 < r₁ := by have := Nat.lt_floor_add_one ((W : ℝ) * t); linarith
  have hWt : x ≤ (W : ℝ) * t := by rw [hx]; exact mul_le_mul_of_nonneg_left ht hWp.le
  have hm₀r₁ : m₀ ≤ r₁ := by
    have : (m₀ : ℝ) < r₁ + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  set r₀ := r₁ - m₀
  have hr₀ : (r₀ : ℝ) = r₁ - m₀ := by rw [Nat.cast_sub hm₀r₁]
  have hr₀ge : x / 4 ≤ r₀ := by rw [hr₀]; linarith
  have hsum : r₀ + m₀ = r₁ := Nat.sub_add_cancel hm₀r₁
  -- the recursion on `[r₀, r₁]`
  have hrec : ∀ m, m < m₀ → pathFrac p b E W (r₀ + m + 1) ≤
      pathFrac p b E W (r₀ + m) - c / W * pathFrac p b E W (r₀ + m) ^ 2 + K / W := by
    intro m hm
    have hr1 : 1 ≤ r₀ + m := by
      have : (1 : ℝ) ≤ r₀ := by linarith
      have : 1 ≤ r₀ := by exact_mod_cast this
      omega
    have hrε : ε / 4 * W ≤ ((r₀ + m : ℕ) : ℝ) := by
      push_cast
      have : ε / 4 * W = x / 4 := by rw [hx]; ring
      rw [this]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      linarith
    have hrT : ((r₀ + m : ℕ) : ℝ) ≤ t * W := by
      have : r₀ + m < r₁ := by omega
      have : ((r₀ + m : ℕ) : ℝ) < r₁ := by exact_mod_cast this
      nlinarith
    exact hW₁ W hWW₁ E hE (r₀ + m) hr1 hrε hrT
  have hm₀1 : 1 ≤ m₀ := by
    have : (1 : ℝ) < m₀ := by linarith
    exact_mod_cast this.le
  have hlog := logistic_bound (y := fun r => pathFrac p b E W r) (a := c / W) (K := K / W)
    (by positivity) (by positivity) r₀ m₀ (fun m => pathFrac_nonneg p b E _) hrec
    m₀ hm₀1 le_rfl
  simp only [hsum] at hlog
  have hM' : max 1 (2 * (K / W) / (c / W)) = M := by
    congr 1; field_simp
  rw [hM'] at hlog
  have hW1 : (1 : ℝ) ≤ W := by
    have : 1 ≤ W := le_trans (Nat.le_add_left 1 _) hW8
    exact_mod_cast this
  have hKW : K / W ≤ K := div_le_self hK hW1
  have h2m : 2 / (c / W * m₀) ≤ 8 / (c * ε) := by
    have hm0 : (0 : ℝ) < m₀ := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : W * ε ≤ 4 * m₀ := by rw [← hx]; linarith
    have e : 8 * (c / W * m₀) = 2 * c * (4 * m₀) / W := by ring
    rw [e, le_div_iff₀ hWp]
    nlinarith
  have hyb : pathFrac p b E W r₁ ≤ max (M + K) (8 / (c * ε)) :=
    hlog.trans (max_le_max (by linarith) h2m)
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_pathFrac hp0 hp1 hb h1 h2 r₁)
    (Filter.Eventually.of_forall fun ω => fracTrace_nonneg' _ _)]
  exact ENNReal.ofReal_le_ofReal hyb

/-- **The fractional transmission bound uniformly on `bulkInterval κI`**, every `0 < p < 1`,
every time `t ≥ ε` (one constant `C = C(b, κI, p, ε)`): `limsup_W sup_E E Tr T_{⌊Wt⌋}^p ≤ C`. -/
theorem fractionalTransmissionUniformGeneral_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∀ p : ℝ, 0 < p → p < 1 →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, ε ≤ t →
      limsup (fun W : ℕ => ⨆ (E : ℝ) (_ : E ∈ bulkInterval κI),
        ∫⁻ ω, ENNReal.ofReal
          (fracTrace p (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
          ∂growthPathLaw W b) atTop ≤ ENNReal.ofReal C := by
  intro b hb0 hb κI hκ p hp0 hp1 ε hε
  obtain ⟨C, hC⟩ := fractionalBulk_holds hMT hGA hLp hP b hb0 hb κI hκ p hp0 hp1 ε hε
  refine ⟨C, fun t ht => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC t ht
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop W₀] with W hW
  exact iSup₂_le fun E hE => hW₀ W hW E hE

/-- **`FullSourceStops.FractionalTransmissionUniform`** (the case `p = 1/2`, `t = ε`), from
`MatchedTracesContract`, `GaussianAbsorptionContract`, `GaussianLpGradient`, `GaussianPoincare`. -/
theorem fractionalTransmissionUniform_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    SourceProcess.FullSourceStops.FractionalTransmissionUniform := by
  intro b hb0 hb κI hκ ε hε
  obtain ⟨C, hC⟩ := fractionalTransmissionUniformGeneral_holds hMT hGA hLp hP b hb0 hb κI hκ
    (1 / 2) (by norm_num) (by norm_num) ε hε
  exact ⟨C, hC ε le_rfl⟩

/-- **The energy-uniform `FullSourceStopsEnergyUniformContract`** from the input hypotheses
only (`fullSourceStopsEnergyUniform_holds_of_fractional` with `fractionalTransmissionUniform_holds`).
-/
theorem fullSourceStopsEnergyUniform_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hP : GaussianPoincare) :
    FullSourceStopsEnergyUniformContract :=
  SourceProcess.FullSourceStops.fullSourceStopsEnergyUniform_holds_of_fractional hMT hGA hLp hSR
    (fractionalTransmissionUniform_holds hMT hGA hLp hP)

/-- The fixed-`E` `FullSourceStopsContract`, from the same input hypotheses. -/
theorem fullSourceStops_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hP : GaussianPoincare) :
    FullSourceStopsContract :=
  SourceProcess.FullSourceStops.fullSourceStops_holds_of_fractional hMT hGA hLp hSR
    (fractionalTransmissionUniform_holds hMT hGA hLp hP)

end BlockBand.Transmission.FractionalBulk
