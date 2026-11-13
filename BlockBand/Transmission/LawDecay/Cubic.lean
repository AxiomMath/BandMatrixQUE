module

public import BlockBand.Transmission.LawDecay.Errors

/-!
# The summed cubic Taylor remainders vanish

**`stepCubic_sum_tendsto`**: along a moving energy, `Σ_{W ≤ r < ⌊Wt⌋} E(|Δ¹_r|³ + (Δ¹_r)²|Δ²_r|) → 0`.
Per length, `|x|³ ≤ s x⁴ + s⁻³` (`s = √W`) and `a²b ≤ a³ + b³` give
`E(|Δ¹|³ + (Δ¹)²|Δ²|) ≤ 2sE(Δ¹)⁴ + sE(Δ²)⁴ + 3s⁻³ ≤ (2K₁ + K₂ + 3)/s³` by
`fourth_increment_bound` (`E(Δ^k_r)⁴ ≤ K_k/W²` on `W/2 ≤ r ≤ tW`, bulk-uniform); there are at most
`tW` lengths, so the sum is `≤ t(2K₁ + K₂ + 3)/√W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDecay

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Generator

theorem cube_le {x s : ℝ} (hs : 0 < s) : |x| ^ 3 ≤ s * x ^ 4 + (s ^ 3)⁻¹ := by
  have h4 : 0 ≤ s * x ^ 4 := by positivity
  by_cases h : |x| ≤ s⁻¹
  · have := pow_le_pow_left₀ (abs_nonneg x) h 3
    rw [inv_pow] at this; linarith
  · replace h := not_le.mp h
    have h1 : 1 ≤ s * |x| := by
      rw [inv_lt_iff_one_lt_mul₀ hs] at h; linarith
    have hx4 : x ^ 4 = |x| ^ 3 * |x| := by
      rw [show |x| ^ 3 * |x| = |x| ^ 4 by ring, ← abs_pow, abs_of_nonneg (by positivity)]
    have : |x| ^ 3 ≤ s * x ^ 4 := by
      rw [hx4]; nlinarith [pow_nonneg (abs_nonneg x) 3]
    have : 0 ≤ (s ^ 3)⁻¹ := by positivity
    linarith

theorem sq_abs_le {a b : ℝ} : a ^ 2 * |b| ≤ |a| ^ 3 + |b| ^ 3 := by
  rw [← sq_abs a]
  rcases le_total |b| |a| with h | h
  · nlinarith [sq_nonneg |a|, abs_nonneg b, pow_nonneg (abs_nonneg b) 3]
  · nlinarith [sq_nonneg |b|, abs_nonneg a, pow_nonneg (abs_nonneg a) 3,
      mul_le_mul h h (abs_nonneg a) (abs_nonneg b)]

variable {W : ℕ}

theorem abs_powerIncrement_le {b E' : ℝ} (hb : b < 1) (h1 : -2 < E') (h2 : E' < 2) {k : ℕ}
    (hk : 1 ≤ k) (r : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, |powerIncrement b E' W k r ω| ≤ 2 * W := by
  filter_upwards [pathPower_bound (W := W) hb h1 h2 hk (r + 1),
    pathPower_bound (W := W) hb h1 h2 hk r] with ω ha hb'
  exact (abs_sub _ _).trans (by linarith)

theorem integrable_powerIncrement_pow {b E' : ℝ} (hb : b < 1) (h1 : -2 < E') (h2 : E' < 2)
    {k : ℕ} (hk : 1 ≤ k) (r n : ℕ) :
    Integrable (fun ω => powerIncrement b E' W k r ω ^ n) (growthPathLaw W b) :=
  integrable_of_abs_le (((measurable_pathPower b E' k (r + 1)).sub
    (measurable_pathPower b E' k r)).pow_const n) (C := (2 * W) ^ n)
    ((abs_powerIncrement_le hb h1 h2 hk r).mono fun ω h => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h n)

/-- **One length**: `E(|Δ¹|³ + (Δ¹)²|Δ²|) ≤ (2K₁ + K₂ + 3)/√W³`. -/
theorem stepCubic_le {b E' : ℝ} (hb : b < 1) (h1 : -2 < E') (h2 : E' < 2) (hW : 1 ≤ W) (r : ℕ)
    {K₁ K₂ : ℝ}
    (hK₁ : ∫ ω, powerIncrement b E' W 1 r ω ^ 4 ∂growthPathLaw W b ≤ K₁ / (W : ℝ) ^ 2)
    (hK₂ : ∫ ω, powerIncrement b E' W 2 r ω ^ 4 ∂growthPathLaw W b ≤ K₂ / (W : ℝ) ^ 2) :
    stepCubic b E' W r ≤ (2 * K₁ + K₂ + 3) / Real.sqrt W ^ 3 := by
  set s := Real.sqrt W
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hs : 0 < s := Real.sqrt_pos.2 hW0
  have hs2 : s ^ 2 = W := Real.sq_sqrt hW0.le
  set μ := growthPathLaw W b
  have i1 := integrable_powerIncrement_pow (W := W) hb h1 h2 le_rfl r 4
  have i2 := integrable_powerIncrement_pow (W := W) hb h1 h2 (by norm_num : 1 ≤ 2) r 4
  have j1 : Integrable (fun ω => 2 * s * powerIncrement b E' W 1 r ω ^ 4) μ := i1.const_mul _
  have j2 : Integrable (fun ω => s * powerIncrement b E' W 2 r ω ^ 4) μ := i2.const_mul _
  have j12 : Integrable (fun ω => 2 * s * powerIncrement b E' W 1 r ω ^ 4 +
      s * powerIncrement b E' W 2 r ω ^ 4) μ := j1.add j2
  have hR : Integrable (fun ω => 2 * s * powerIncrement b E' W 1 r ω ^ 4 +
      s * powerIncrement b E' W 2 r ω ^ 4 + 3 * (s ^ 3)⁻¹) μ := j12.add (integrable_const _)
  have hle := integral_mono_of_nonneg (μ := μ)
    (f := fun ω => |powerIncrement b E' W 1 r ω| ^ 3 +
      powerIncrement b E' W 1 r ω ^ 2 * |powerIncrement b E' W 2 r ω|)
    (Eventually.of_forall fun ω => by positivity) hR (Eventually.of_forall fun ω => by
      have c1 := cube_le (x := powerIncrement b E' W 1 r ω) hs
      have c2 := cube_le (x := powerIncrement b E' W 2 r ω) hs
      have c3 := sq_abs_le (a := powerIncrement b E' W 1 r ω) (b := powerIncrement b E' W 2 r ω)
      show _ ≤ 2 * s * _ + s * _ + 3 * (s ^ 3)⁻¹
      linarith)
  rw [integral_add j12 (integrable_const _), integral_add j1 j2, integral_const_mul,
    integral_const_mul, integral_const] at hle
  simp only [probReal_univ, one_smul] at hle
  refine hle.trans ?_
  have hW2 : (W : ℝ) ^ 2 = s ^ 4 := by rw [← hs2]; ring
  rw [hW2] at hK₁ hK₂
  have e1 : 2 * s * (K₁ / s ^ 4) = 2 * K₁ / s ^ 3 := by field_simp
  have e2 : s * (K₂ / s ^ 4) = K₂ / s ^ 3 := by field_simp
  have : (2 * K₁ + K₂ + 3) / s ^ 3 = 2 * K₁ / s ^ 3 + K₂ / s ^ 3 + 3 * (s ^ 3)⁻¹ := by
    field_simp
  rw [this, ← e1, ← e2]
  have := mul_le_mul_of_nonneg_left hK₁ (by positivity : (0 : ℝ) ≤ 2 * s)
  have := mul_le_mul_of_nonneg_left hK₂ hs.le
  linarith

theorem lengthWindow_one (t : ℝ) (W : ℕ) : lengthWindow 1 t W = Finset.Ico W ⌊(W : ℝ) * t⌋₊ := by
  simp [lengthWindow]

theorem mem_window {t : ℝ} (ht : 0 ≤ t) {W r : ℕ} (hr : r ∈ lengthWindow 1 t W) :
    W ≤ r ∧ (r : ℝ) ≤ t * W := by
  rw [lengthWindow_one, Finset.mem_Ico] at hr
  refine ⟨hr.1, ?_⟩
  have := Nat.floor_le (by positivity : (0 : ℝ) ≤ (W : ℝ) * t)
  have h2 : (r : ℝ) < ⌊(W : ℝ) * t⌋₊ := by exact_mod_cast hr.2
  linarith

theorem card_window_le {t : ℝ} (ht : 0 ≤ t) (W : ℕ) :
    ((lengthWindow 1 t W).card : ℝ) ≤ t * W := by
  rw [lengthWindow_one, Nat.card_Ico]
  have := Nat.floor_le (by positivity : (0 : ℝ) ≤ (W : ℝ) * t)
  have : ((⌊(W : ℝ) * t⌋₊ - W : ℕ) : ℝ) ≤ ⌊(W : ℝ) * t⌋₊ := by
    exact_mod_cast Nat.sub_le _ _
  linarith

/-- **The summed cubic remainders vanish** (along a moving energy). -/
theorem stepCubic_sum_tendsto (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e) {t : ℝ} (ht : 1 < t) :
    Tendsto (fun W : ℕ => ∑ r ∈ lengthWindow 1 t W, stepCubic b (e W) W r) atTop (𝓝 0) := by
  set κI := min (E + 2) (2 - E)
  have hκ : 0 < κI := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval κI :=
    ⟨by have := min_le_left (E + 2) (2 - E); linarith,
      by have := min_le_right (E + 2) (2 - E); linarith⟩
  obtain ⟨K₁, W₁, hK₁0, hK₁⟩ := fourth_increment_bound hMT hGA hLp (κ := κI / 2) (ε := 1 / 2)
    (T := t) hb0 hb (by positivity) (by norm_num) (by linarith) 0
  obtain ⟨K₂, W₂, hK₂0, hK₂⟩ := fourth_increment_bound hMT hGA hLp (κ := κI / 2) (ε := 1 / 2)
    (T := t) hb0 hb (by positivity) (by norm_num) (by linarith) 1
  set C := 2 * K₁ + K₂ + 3
  have hlim : Tendsto (fun W : ℕ => t * C * (Real.sqrt W)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      tendsto_natCast_atTop_atTop)).const_mul (t * C)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun W => Finset.sum_nonneg fun r _ =>
    integral_nonneg fun ω => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop (max (max W₁ W₂) (max (EnergyUniform.windowWidth κI Ce) 1))]
    with W hW
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hW₂⟩, hWw, hW1⟩ := hW
  have hWb := EnergyUniform.window_mem_bulkInterval hκ hWw hEb (he W (by omega))
  have h1' : -2 < e W := by have := hWb.1; linarith
  have h2' : e W < 2 := by have := hWb.2; linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hstep : ∀ r ∈ lengthWindow 1 t W, stepCubic b (e W) W r ≤ C / Real.sqrt W ^ 3 := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := mem_window (by linarith) hr
    have hr0 : 1 ≤ r := le_trans hW1 hr1
    have hrW : 1 / 2 * (W : ℝ) ≤ r := by
      have : (W : ℝ) ≤ r := by exact_mod_cast hr1
      linarith
    exact stepCubic_le (by linarith) h1' h2' hW1 r (by simpa using hK₁ W hW₁ (e W) hWb r hr0 hrW hr2)
      (hK₂ W hW₂ (e W) hWb r hr0 hrW hr2)
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hs : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
  have hs2 : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW0.le
  have hC : 0 ≤ C := by positivity
  calc ((lengthWindow 1 t W).card : ℝ) * (C / Real.sqrt W ^ 3) ≤ t * W * (C / Real.sqrt W ^ 3) :=
        mul_le_mul_of_nonneg_right (card_window_le (by linarith) W) (by positivity)
    _ = t * Real.sqrt W ^ 2 * (C / Real.sqrt W ^ 3) := by rw [hs2]
    _ = t * C * (Real.sqrt W)⁻¹ := by field_simp

end BlockBand.Transmission.LawDecay
