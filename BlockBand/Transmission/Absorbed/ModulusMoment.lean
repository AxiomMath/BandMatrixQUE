module

public import BlockBand.Transmission.Absorbed.ModulusCond
public import BlockBand.Transmission.Absorbed.DeltaUniform
public import BlockBand.Transmission.Generator.ModMoment

/-!
# The absorbed modulus: moments of the majorant along the absorbed path

**`absorbed_modY_moment hMT hGA hLp`**: at fixed `b ∈ (0,1/2)`, `E ∈ (-2,2)`, for `K ≥ 0`,
`ε > 0` and `T`: `∃ M W₀`, for `W ≥ W₀`, every profile `0 ≤ κ ≤ K` and `εW ≤ r ≤ TW`,
`E Y'(X^κ_r)¹² ≤ M` (and integrable), `Y' = modY = (g+1)(Wδ₀+1)`.

Route: `Y'¹² ≤ (g+1)²⁴ + (Wδ₀+1)²⁴`; `absorbedConductance_bulk` (`p = 24`, `moment_shift`)
and `absorbedDeltaUniform_holds` (`p = 24`, `shifted_moment`). No mixing or `δ₁` moments.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.Generator
open scoped ENNReal ComplexOrder

variable {W : ℕ}

theorem mul_pow_twelve_le (x y : ℝ) :
    (x * y) ^ 12 ≤ x ^ 24 + y ^ 24 := by
  have h := two_mul_le_add_sq (x ^ 12) (y ^ 12)
  have e : (x * y) ^ 12 = x ^ 12 * y ^ 12 := mul_pow _ _ _
  have e2 : (x ^ 12) ^ 2 = x ^ 24 := by rw [← pow_mul]
  have e3 : (y ^ 12) ^ 2 = y ^ 24 := by rw [← pow_mul]
  rw [e2, e3] at h
  have : 0 ≤ x ^ 12 * y ^ 12 := by positivity
  rw [e]; linarith

/-- **`E Y'(X^κ_r)¹² ≤ M`** along the absorbed path, uniform over `0 ≤ κ ≤ K`. -/
theorem absorbed_modY_moment (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ} (h1 : -2 < E)
    (h2 : E < 2) {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) (T : ℝ) :
    ∃ (M : ℝ) (W₀ : ℕ), 0 ≤ M ∧ ∀ W : ℕ, W₀ ≤ W → ∀ κ : ℝ → ℝ, (∀ s, 0 ≤ κ s ∧ κ s ≤ K) →
      ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
        Integrable (fun ω => modY b E (pathNearSchur b E κ W r ω) ^ 12) (growthPathLaw W b) ∧
        ∫ ω, modY b E (pathNearSchur b E κ W r ω) ^ 12 ∂growthPathLaw W b ≤ M := by
  have hκI : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hE := PassiveLayer.mem_bulkInterval_min E
  obtain ⟨Cg, hCg⟩ := absorbedConductance_bulk hMT hGA hLp b hb0 hb _ ε ((24 : ℕ) : ℝ) K hκI hε
    (by norm_num) hK
  obtain ⟨Wg, hg⟩ := hCg T
  obtain ⟨Cδ, hCδ, hδT⟩ := absorbedDeltaUniform_holds hMT hGA hLp b hb0 hb _ K ((24 : ℕ) : ℝ)
    hκI hK (by norm_num)
  obtain ⟨Wδ, hδ⟩ := hδT T
  set Cg' := max Cg 0
  refine ⟨2 ^ 24 * (Cg' + 1) + 2 ^ 24 * (Cδ ^ 24 + 1), max (max Wg Wδ) 1, by positivity,
    fun W hW κ hκK r hεr hrT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWg, hWδ⟩, hW1⟩ := hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hr1 : 1 ≤ r := by
    have : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hεr
    exact_mod_cast this
  have hκ0 : ∀ s, 0 ≤ κ s := fun s => (hκK s).1
  set μ := growthPathLaw W b
  have hXm := measurable_pathNearSchur' (W := W) b E κ r
  -- the conductance factor
  set g : GrowthPath W → ℝ := absorbedConductance b E κ W r
  have hgm : Measurable g := measurable_absorbedConductance b E κ r
  have hgB : ∀ᵐ ω ∂μ, 0 ≤ g ω ∧ g ω ≤ W := by
    filter_upwards [ae_passiveSample W hκ0 (by linarith : b < 1) h1 h2] with ω hP
    obtain ⟨a0, a1⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2
      (pathNearSchur_passive hP r) (le_refl 1)
    simp only [pow_one] at a0 a1
    exact ⟨a0, a1⟩
  have hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω := hgB.mono fun _ h => h.1
  have hgi := integral_pow_le_of_lintegral (μ := μ) hgm hg0 24 (le_max_right Cg 0)
    ((hg W hWg E hE κ hκK r hεr hrT).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have mG : ∫ ω, (g ω + 1) ^ 24 ∂μ ≤ 2 ^ 24 * (Cg' + 1) :=
    (moment_shift hgm hg0 (hgB.mono fun _ h => h.2) 24).trans (by gcongr)
  have iG : Integrable (fun ω => (g ω + 1) ^ 24) μ :=
    integrable_of_bdd ((hgm.add_const 1).pow_const 24) (B := ((W : ℝ) + 1) ^ 24) (by
      filter_upwards [hgB] with ω h
      rw [abs_of_nonneg (by have := h.1; positivity)]
      exact pow_le_pow_left₀ (by linarith [h.1]) (by linarith [h.2]) 24)
  -- the jet factor
  have hδm : AEStronglyMeasurable (absorbedDelta b E κ W r) μ :=
    ((measurable_jetDistance0 b E).comp hXm).aestronglyMeasurable
  obtain ⟨iA, mA⟩ := shifted_moment hδm (ae_of_all _ fun _ => norm_nonneg _) 24 (by norm_num)
    hCδ hW0 (hδ W hWδ E hE κ hκK r hr1 hrT)
  -- assemble
  have hpt : ∀ᵐ ω ∂μ, modY b E (pathNearSchur b E κ W r ω) ^ 12 ≤
      (g ω + 1) ^ 24 + ((W : ℝ) * absorbedDelta b E κ W r ω + 1) ^ 24 := by
    exact ae_of_all _ fun ω => mul_pow_twelve_le _ _
  have iS := iG.add iA
  have hYm : AEStronglyMeasurable (fun ω => modY b E (pathNearSchur b E κ W r ω) ^ 12) μ :=
    (((measurable_modY b E).comp hXm).pow_const 12).aestronglyMeasurable
  have iY : Integrable (fun ω => modY b E (pathNearSchur b E κ W r ω) ^ 12) μ :=
    Integrable.mono' iS hYm (by
      filter_upwards [hpt] with ω h
      rw [Real.norm_of_nonneg (by positivity)]
      exact h)
  have e := integral_add iG iA
  refine ⟨iY, (integral_mono_ae iY iS hpt).trans ?_⟩
  exact le_of_eq_of_le e (add_le_add mG mA)

end BlockBand.Transmission.Absorbed
