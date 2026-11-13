module

public import BlockBand.Transmission.Absorbed.PathStep
public import BlockBand.Transmission.Absorbed.DeltaUniform
public import BlockBand.Transmission.SourceMixing.Conductance
public import BlockBand.Transmission.LengthUniform.BulkMassMoment

/-!
# The absorbed, length-uniform, bulk-uniform conductance moments

`g^κ_r = Re Tr T^κ_r = 4η q(X^κ_r)` (`absorbedConductance_eq_mass`). For `n = ⌈p⌉`,
`x_r = E qc(X^κ_r)ⁿ`:
* the path step `abs_path_step` (sibling module) with the absorbed layer step
  `absorbedLayer_step_bulk` and the absorbed `δ₀` moments `absorbedDeltaUniform_holds` gives, for
  `1 ≤ j < TW` and `l ≥ 2n/c`, `x_{j+1} ≤ x_j(1 - cl/W) + (clⁿ⁺¹ + D)/W`; `c, D` do not depend on
  `T`, `E`, `κ`;
* `x_1 ≤ ((4η_L)⁻¹(1+W))ⁿ`; `logistic_bound_from` (`logistic_bound` with the step
  needed only for `l ≥ 2n/c`) gives `x_r ≤ K'(1+W/r)ⁿ` for `1 ≤ r ≤ TW`;
* **`absorbedMassMoment_bulk`**: `‖q(X^κ_r)‖_p ≤ K(1 + W/r)`, `K` before `T`;
* **`absorbedConductance_bulk`**: for `εW ≤ r ≤ TW`, `E (g^κ_r)^p ≤ C = (4K(1+ε⁻¹))^p`.

Law `growthPathLaw W b`. Hypotheses `MatchedTracesContract`, `GaussianAbsorptionContract` and
`GaussianLpGradient`. Quantifier order: `b, κ_I, ε, p, K` first; then `C`; then `T`; then `W₀`;
then `W`, `E ∈ bulkInterval κ_I`, every profile `0 ≤ κ ≤ K`, and `r`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.SourceMixing
open BlockBand.Transmission.LawFinite
open scoped NNReal ENNReal ComplexOrder

variable {W : ℕ}

/-- **Logistic comparison, from the step for `l ≥ 2n/c` only** (`logistic_bound`, whose
proof uses the step only at `l = (2n/c)(1 + W/r)`). -/
theorem logistic_bound_from (n : ℕ) (hn : 1 ≤ n) {c D K₀ : ℝ} (hc : 0 < c) (hD : 0 ≤ D)
    (hK₀ : 0 ≤ K₀) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (W : ℝ), 1 ≤ W → ∀ (x : ℕ → ℝ) (N : ℕ),
      (∀ r, 0 ≤ x r) → x 1 ≤ K₀ * (1 + W) ^ n →
      (∀ r, 1 ≤ r → r < N → ∀ l : ℝ, 2 * n / c ≤ l →
        x (r + 1) ≤ x r * (1 - c * l / W) + (c * l ^ (n + 1) + D) / W) →
      ∀ r, 1 ≤ r → r ≤ N → x r ≤ K * (1 + W / r) ^ n := by
  set K := max K₀ (2 ^ (n + 1) * c * (2 * n / c) ^ (n + 1) + D)
  refine ⟨K, le_max_of_le_left hK₀, fun W hW x N hx0 hx1 hrec r hr hrN => ?_⟩
  have hW0 : 0 ≤ W := by linarith
  induction r, hr using Nat.le_induction with
  | base =>
    calc x 1 ≤ K₀ * (1 + W) ^ n := hx1
      _ ≤ K * (1 + W) ^ n := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = K * (1 + W / ((1 : ℕ) : ℝ)) ^ n := by simp
  | succ r hr ih =>
    have ih' := ih (by omega)
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hr0 : (0 : ℝ) < r := by linarith
    have hcast : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    set v := 1 + W / r with hv
    set v' := 1 + W / ((r : ℝ) + 1) with hv'
    have hl : 2 * (n : ℝ) / c ≤ 2 * (n : ℝ) / c * v := by
      have : 0 ≤ W / r := div_nonneg hW0 hr0.le
      exact le_mul_of_one_le_right (by positivity) (by linarith)
    refine ma_step hn hc hD hW ?_ ?_ ?_ ?_ ?_ (le_max_right _ _) (hx0 r)
      (ih'.trans (le_of_eq rfl)) (hrec r hr (by omega) _ hl)
    · have : 0 ≤ W / ((r : ℝ) + 1) := div_nonneg hW0 (by linarith)
      linarith
    · have : W / ((r : ℝ) + 1) ≤ W / r := div_le_div_of_nonneg_left hW0 hr0 (by linarith)
      linarith
    · have : W / r ≤ W := div_le_self hW0 hr1
      linarith
    · have : W / r ≤ 2 * (W / ((r : ℝ) + 1)) := by
        rw [mul_div_assoc', div_le_div_iff₀ hr0 (by linarith)]
        nlinarith
      linarith
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hvv' : v' ≤ v := by
        have : W / ((r : ℝ) + 1) ≤ W / r := div_le_div_of_nonneg_left hW0 hr0 (by linarith)
        linarith
      have hv'0 : 0 ≤ v' := by
        have : 0 ≤ W / ((r : ℝ) + 1) := div_nonneg hW0 (by linarith)
        linarith
      have h1 := ma_pow_sub_pow_le m hv'0 hvv'
      have hWpos : 0 < W := by linarith
      have hd : v - v' ≤ v ^ 2 / W := by
        have e : v - v' = W / (r * (r + 1)) := by
          rw [hv, hv']; field_simp; ring
        have e2 : (W / r) ^ 2 / W = W / (r * r) := by field_simp
        have t1 : W / (r * (r + 1)) ≤ W / (r * r) :=
          div_le_div_of_nonneg_left hW0 (by positivity) (by nlinarith)
        have t2 : (W / r) ^ 2 / W ≤ v ^ 2 / W := by
          refine div_le_div_of_nonneg_right ?_ hWpos.le
          have : 0 ≤ W / r := div_nonneg hW0 hr0.le
          rw [hv]; nlinarith
        linarith
      have hvm : 0 ≤ ((m : ℝ) + 1) * v ^ m := by
        have : 0 ≤ v := hv'0.trans hvv'
        positivity
      calc v ^ (m + 1) - v' ^ (m + 1) ≤ (m + 1) * v ^ m * (v - v') := h1
        _ ≤ (m + 1) * v ^ m * (v ^ 2 / W) := mul_le_mul_of_nonneg_left hd hvm
        _ = ((m + 1 : ℕ) : ℝ) * v ^ (m + 1 + 1) / W := by push_cast; ring

theorem measurable_pathNearSchur' (b E : ℝ) (κ : ℝ → ℝ) (r : ℕ) :
    Measurable fun ω : GrowthPath W => pathNearSchur b E κ W r ω := by
  have e : (fun ω => pathNearSchur b E κ W r ω) = pastX b E κ W r ∘ pastCoords W r := by
    funext ω; simp only [Function.comp, pathNearSchur_eq_past]
  rw [e]; exact (measurable_pastX b E κ r).comp (measurable_pastCoords W r)

/-- **The `T`-free absorbed mass moment bound, uniform on `bulkInterval κ'` and over the
profiles `0 ≤ κ ≤ K`.** -/
theorem absorbedMassMoment_bulk (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b κ' K : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ' : 0 < κ')
    (hK : 0 ≤ K) (p : ℝ) (hp : 1 ≤ p) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ',
      ∀ κ : ℝ → ℝ, (∀ s, 0 ≤ κ s ∧ κ s ≤ K) → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W →
        eLpNorm (fun ω => passiveMass b E (pathNearSchur b E κ W r ω)) (ENNReal.ofReal p)
          (growthPathLaw W b) ≤ ENNReal.ofReal (K' * (1 + W / r)) := by
  set n := ⌈p⌉₊
  have hpn : p ≤ n := Nat.le_ceil p
  have hn : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := hp.trans hpn
    exact_mod_cast this
  have hA := PassiveLayer.passiveBounds_holds hGA hLp
  obtain ⟨c, D₁, D₂, W₁, hc, hD₁, hD₂, hstep⟩ := absorbedLayer_step_bulk hA hb0 hb hκ' hK n hn
  obtain ⟨Cδ, hCδ, hδT⟩ := absorbedDeltaUniform_holds hMT hGA hLp b hb0 hb κ' K
    (((n + 1 : ℕ) : ℝ)) hκ' hK (by norm_cast; omega)
  set ηL := etaLow b κ'
  have hηL : 0 < ηL := etaLow_pos (by linarith) hκ'
  set D := D₁ + D₂ * Cδ ^ (n + 1)
  have hD : 0 ≤ D := by positivity
  obtain ⟨K', hK', hlog⟩ := logistic_bound_from n hn hc hD
    (by positivity : 0 ≤ ((4 * ηL)⁻¹) ^ n)
  refine ⟨K' ^ (n : ℝ)⁻¹, by positivity, fun T => ?_⟩
  obtain ⟨Wδ, hδW⟩ := hδT T
  refine ⟨max (max W₁ Wδ) 1, fun W hW E hE κ hκK r hr1 hrT => ?_⟩
  obtain ⟨h1, h2⟩ := bulk_bounds hκ' hE
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hWδ⟩, hW1⟩ := hW
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hκ0 : ∀ s, 0 ≤ κ s := fun s => (hκK s).1
  set P := growthPathLaw W b
  set x : ℕ → ℝ := fun r => ∫ ω, qc b E (pathNearSchur b E κ W r ω) ^ n ∂P
  have hx0 : ∀ r, 0 ≤ x r := fun r => integral_nonneg fun ω => pow_nonneg (qc_nonneg b E _) n
  have hx1 : x 1 ≤ ((4 * ηL)⁻¹) ^ n * (1 + W) ^ n := by
    have hbd : ∀ ω, qc b E (pathNearSchur b E κ W 1 ω) ^ n ≤ ((4 * ηL)⁻¹ * (1 + W)) ^ n :=
      fun ω => by
        refine pow_le_pow_left₀ (qc_nonneg b E _)
          ((LengthUniform.qc_le_bulk hb0 hb hκ' hE _).trans ?_) n
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc x 1 ≤ ∫ _ω, ((4 * ηL)⁻¹ * (1 + W)) ^ n ∂P :=
          integral_mono (abs_integrable_qc (by linarith) h1 h2 κ n 1) (integrable_const _) hbd
      _ = ((4 * ηL)⁻¹) ^ n * (1 + W) ^ n := by
          rw [integral_const, probReal_univ, one_smul, mul_pow]
  have hrec : ∀ j, 1 ≤ j → j < ⌊T * W⌋₊ → ∀ l : ℝ, 2 * n / c ≤ l →
      x (j + 1) ≤ x j * (1 - c * l / W) + (c * l ^ (n + 1) + D) / W := by
    intro j hj hjN l hl
    have hTW : (1 : ℝ) ≤ T * W := Nat.floor_pos.mp (by omega)
    have hjT : (j : ℝ) ≤ T * W :=
      (Nat.cast_le.mpr hjN.le).trans (Nat.floor_le (by linarith))
    have hδj := hδW W hWδ E hE κ hκK j hj hjT
    have hδint := mp_integral_pow_le (ae_of_all _ fun ω => absorbedDelta_nonneg b E κ j ω)
      (n + 1) (by omega) (by positivity) hδj
    exact abs_path_step hb0 hb h1 h2 hκ0 (fun s => (hκK s).2) hD₂ hW1
      (fun X hX ε hε hεK => hstep W hW₁ E hE X hX ε hε hεK l hl) hj hδint
  have hxr := hlog (W : ℝ) hW1' x ⌊T * W⌋₊ hx0 hx1 hrec r hr1 (Nat.le_floor hrT)
  have hpn' : ENNReal.ofReal p ≤ (n : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hpn
  have hcongr : eLpNorm (fun ω => passiveMass b E (pathNearSchur b E κ W r ω)) (n : ℝ≥0∞) P =
      eLpNorm (fun ω => qc b E (pathNearSchur b E κ W r ω)) (n : ℝ≥0∞) P := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [ae_passiveSample W hκ0 (by linarith) h1 h2] with ω hω
    exact (qc_eq (pathNearSchur_passive hω r)).symm
  have hv : 0 ≤ 1 + (W : ℝ) / r := by positivity
  refine (eLpNorm_le_eLpNorm_of_exponent_le hpn').trans ?_
  rw [hcongr]
  refine (mp_eLpNorm_le ((measurable_qc b E).comp
    (measurable_pathNearSchur' b E κ r)).aestronglyMeasurable (fun ω => qc_nonneg b E _)
    (fun ω => qc_le (by linarith) h1 h2 _) n hn hxr).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Real.mul_rpow hK' (by positivity), Real.pow_rpow_inv_natCast hv (by omega)]

/-- `g^κ_r = Re Tr T^κ_r`, the conductance of the path with profile `κ`. -/
def absorbedConductance (b E : ℝ) (κ : ℝ → ℝ) (W r : ℕ) (ω : GrowthPath W) : ℝ :=
  conductanceOf (pathTransmission b E κ W r ω)

theorem absorbedConductance_eq_mass (b E : ℝ) (κ : ℝ → ℝ) (r : ℕ) (ω : GrowthPath W) :
    absorbedConductance b E κ W r ω =
      4 * etaZ b E * passiveMass b E (pathNearSchur b E κ W r ω) := by
  rw [absorbedConductance, conductanceOf, pathTransmission, passiveTransmission, trace_smul,
    passiveMass, smul_eq_mul, Complex.re_ofReal_mul]

theorem measurable_absorbedConductance (b E : ℝ) (κ : ℝ → ℝ) (r : ℕ) :
    Measurable (absorbedConductance (W := W) b E κ r) := by
  have h : absorbedConductance (W := W) b E κ r =
      fun ω => 4 * etaZ b E * passiveMass b E (pathNearSchur b E κ W r ω) :=
    funext (absorbedConductance_eq_mass b E κ r)
  rw [h]
  exact ((measurable_passiveMass b E).comp (measurable_pathNearSchur' b E κ r)).const_mul _

/-- **The absorbed conductance moments** (`absorbedConductance_bulk`): the absorbed analogue of
the `TransmissionLengthUniformContract.conductance`, uniform over the profiles
`0 ≤ κ ≤ K`, with `C` chosen before `T`.
-/
theorem absorbedConductance_bulk (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI ε p K : ℝ, 0 < κI → 0 < ε → 1 ≤ p → 0 ≤ K →
      ∃ C : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
        ∀ κ : ℝ → ℝ, (∀ s, 0 ≤ κ s ∧ κ s ≤ K) → ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
          ∫⁻ ω, ‖absorbedConductance b E κ W r ω‖ₑ ^ p ∂growthPathLaw W b ≤
            ENNReal.ofReal C := by
  intro b hb0 hb κI ε p K hκ hε hp hK
  obtain ⟨K', hK', hKT⟩ := absorbedMassMoment_bulk hMT hGA hLp hb0 hb hκ hK p hp
  have hp0 : 0 < p := by linarith
  refine ⟨(4 * K' * (1 + ε⁻¹)) ^ p, fun T => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hKT T
  refine ⟨max W₀ 1, fun W hW E hE κ hκK r hεr hrT => ?_⟩
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hWW : W₀ ≤ W := le_of_max_le_left hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hW
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by nlinarith) hεr
  have hr1 : 1 ≤ r := by
    have : 0 < r := by exact_mod_cast hr0
    omega
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hη1 : etaZ b E ≤ 1 := bulk_eta_le_one hb0 hκ hE
  set P := growthPathLaw W b
  have hq := hW₀ W hWW E hE κ hκK r hr1 hrT
  have hgL : eLpNorm (absorbedConductance b E κ W r) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (4 * etaZ b E * (K' * (1 + W / r))) := by
    have e : absorbedConductance b E κ W r =
        (4 * etaZ b E) • fun ω => passiveMass b E (pathNearSchur b E κ W r ω) := by
      funext ω; rw [absorbedConductance_eq_mass]; rfl
    rw [e, eLpNorm_const_smul, ENNReal.ofReal_mul (by positivity), Real.enorm_eq_ofReal_abs,
      abs_of_pos (by positivity)]
    exact mul_le_mul_right hq _
  have hWr : (W : ℝ) / r ≤ ε⁻¹ := by
    rw [div_le_iff₀ hr0, inv_mul_eq_div, le_div_iff₀ hε]; linarith
  have hle : 4 * etaZ b E * (K' * (1 + W / r)) ≤ 4 * K' * (1 + ε⁻¹) := by
    have h3 : K' * (1 + W / r) ≤ K' * (1 + ε⁻¹) := mul_le_mul_of_nonneg_left (by linarith) hK'
    have h4 : 0 ≤ K' * (1 + W / r) := by positivity
    nlinarith
  have hg := (measurable_absorbedConductance (W := W) b E κ r).aestronglyMeasurable (μ := P)
  refine (cm_lintegral_le hg hp0 (by positivity) hgL).trans (ENNReal.ofReal_le_ofReal ?_)
  exact Real.rpow_le_rpow (by positivity) hle hp0.le

end BlockBand.Transmission.Absorbed
