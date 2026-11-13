module

public import BlockBand.Transmission.LawForced.RatioL1
public import BlockBand.Transmission.Generator.Moments

/-!
# `RatioDriftSummable` at `κ ≡ 0`

**`ratioDriftSummable_zero hMT hGA hLp hP`**: the body of `RatioDriftSummable` at the
profile `κ ≡ 0`, for every `b ∈ (0,1/2)`, `E ∈ (−2,2)`, chamber point `z` and `0 < ε ≤ T`:
`Σ_{⌊εW⌋ ≤ r < ⌊TW⌋} E|ratioDriftError b E 0 W z r| ≤ T·K/√W → 0`
(`ratioDriftError_zero_L1` at `ε/2`, `T + 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Generator

/-- **`RatioDriftSummable` at `κ ≡ 0`.** -/
theorem ratioDriftSummable_zero (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ (p : ℕ) (z : DualCoord p), z ∈ dualChamber p → ∀ ε T : ℝ, 0 < ε → ε ≤ T →
        Tendsto (fun W : ℕ => ∑ r ∈ Finset.Ico ⌊(W : ℝ) * ε⌋₊ ⌊(W : ℝ) * T⌋₊,
          ∫ ω, |ratioDriftError b E (fun _ => 0) W z r ω| ∂growthPathLaw W b) atTop (𝓝 0) := by
  intro b hb0 hb E hE1 hE2 p z hz ε T hε hεT
  obtain ⟨hκ, hEb⟩ := mem_bulk_min hE1 hE2
  obtain ⟨K, W₀, hL⟩ := ratioDriftError_zero_L1 hMT hGA hLp hP (κ := min (2 + E) (2 - E))
    (ε := ε / 2) (T := T + 1) hb0 hb hκ (by positivity) (by linarith) hz
  have hT0 : 0 < T := by linarith
  set K' := max K 0
  have hU : Tendsto (fun W : ℕ => T * K' * (Real.sqrt W)⁻¹) atTop (𝓝 0) := by
    have hs : Tendsto (fun W : ℕ => (Real.sqrt W)⁻¹) atTop (𝓝 0) :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    simpa using hs.const_mul (T * K')
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
    (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ =>
      abs_nonneg _) ?_
  filter_upwards [eventually_ge_atTop (max W₀ ⌈2 / ε⌉₊)] with W hW
  simp only [max_le_iff] at hW
  obtain ⟨hW0, hW2⟩ := hW
  have hWε : 2 / ε ≤ (W : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hW2)
  have hεW : 2 ≤ ε * W := by rw [div_le_iff₀ hε] at hWε; linarith
  have hWpos : (0 : ℝ) < W := by nlinarith
  have hs0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWpos
  have hb' : ∀ r ∈ Finset.Ico ⌊(W : ℝ) * ε⌋₊ ⌊(W : ℝ) * T⌋₊,
      ∫ ω, |ratioDriftError b E (fun _ => 0) W z r ω| ∂growthPathLaw W b ≤
        K' * (Real.sqrt W)⁻¹ ^ 3 := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have h1 := Nat.lt_floor_add_one ((W : ℝ) * ε)
    have h2 : (⌊(W : ℝ) * ε⌋₊ : ℝ) ≤ r := by exact_mod_cast hr.1
    have hr2 : ε / 2 * W ≤ r := by nlinarith
    have hr1 : 1 ≤ r := by
      have : (1 : ℝ) ≤ r := by nlinarith
      exact_mod_cast this
    have hr3 : (r : ℝ) ≤ (T + 1) * W := by
      have h3 : (r : ℝ) < ⌊(W : ℝ) * T⌋₊ := by exact_mod_cast hr.2
      have h4 := Nat.floor_le (mul_nonneg hWpos.le hT0.le)
      nlinarith
    exact (hL W hW0 E hEb r hr1 hr2 hr3).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity))
  refine (Finset.sum_le_sum hb').trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.Ico ⌊(W : ℝ) * ε⌋₊ ⌊(W : ℝ) * T⌋₊).card : ℝ) ≤ T * W := by
    rw [Nat.card_Ico]
    have h4 := Nat.floor_le (mul_nonneg hWpos.le hT0.le)
    have : ((⌊(W : ℝ) * T⌋₊ - ⌊(W : ℝ) * ε⌋₊ : ℕ) : ℝ) ≤ (⌊(W : ℝ) * T⌋₊ : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    linarith
  have hK0 : 0 ≤ K' * (Real.sqrt W)⁻¹ ^ 3 := by positivity
  have hsW : (W : ℝ) * (Real.sqrt W)⁻¹ ^ 3 = (Real.sqrt W)⁻¹ := by
    set q := Real.sqrt W
    have h2 : (W : ℝ) = q ^ 2 := (Real.sq_sqrt hWpos.le).symm
    rw [h2]
    have hq : q ≠ 0 := hs0.ne'
    field_simp
  calc ((Finset.Ico ⌊(W : ℝ) * ε⌋₊ ⌊(W : ℝ) * T⌋₊).card : ℝ) * (K' * (Real.sqrt W)⁻¹ ^ 3)
      ≤ T * W * (K' * (Real.sqrt W)⁻¹ ^ 3) := mul_le_mul_of_nonneg_right hcard hK0
    _ = T * K' * ((W : ℝ) * (Real.sqrt W)⁻¹ ^ 3) := by ring
    _ = T * K' * (Real.sqrt W)⁻¹ := by rw [hsW]

end BlockBand.Transmission.LawForced
