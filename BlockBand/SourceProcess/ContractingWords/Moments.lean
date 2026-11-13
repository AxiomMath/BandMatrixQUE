module

public import BlockBand.SourceProcess.ContractingWords.WordAll
public import BlockBand.SourceProcess.ContractingWords.Theta
public import BlockBand.SourceProcess.FullSourceStops.LoadMoments

/-!
# Moments of admitted products, uniformly on the bulk

`productValue_eLpNorm_le`: admitted products of bounded degree have `‖Z_j‖_p ≤ C` uniformly for
`E` in the bulk, in the tag births and in `εW ≤ j ≤ TW`; in particular they are integrable
(`productValue_integrable`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.FullSourceStops BlockBand.Transmission.Bridge
open scoped ENNReal

/-- **`‖Z_j‖_p ≤ C`** uniformly on the bulk, in the births and in `εW ≤ j ≤ TW`. -/
theorem productValue_eLpNorm_le (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q → ∀ (d : ℕ) (ε T p : ℝ),
    0 < ε → ε < T → 1 ≤ p → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI, ∀ (k : Fin nT → ℕ) (j : ℕ), ε * W ≤ j → (j : ℝ) ≤ T * W →
      ∀ Zs : List (TraceWord nT nI), IsAdmittedProduct Zs → productDegree Zs ≤ d →
        eLpNorm (fun ω => productValue b E k q W j ω Zs) (ENNReal.ofReal p)
          (growthPathLaw W b) ≤ ENNReal.ofReal C := by
  intro b hb0 hb κI hκ nT nI q hq d ε T p hε hεT hp
  set n : ℕ := ⌈(d : ℝ) * p⌉₊ + 1
  obtain ⟨CL, WL, hCL, hL⟩ := lintegral_wordLoad_pow_le hMT hGA hLp hSR b hb0 hb κI hκ nT nI q hq
    ε T hε hεT n (by omega)
  refine ⟨(CL ^ (1 / p)).toReal, max WL 1, fun W hW E hE k j hj1 hj2 Zs hZ hd => ?_⟩
  obtain ⟨h1, h2, -⟩ := mem_bulk_bounds hκ hE
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hp0 : 0 < p := by linarith
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  rw [ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg (by positivity) hCL),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
      (measurable_productValue b E k q j Zs).aestronglyMeasurable, hpr]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  refine le_trans (lintegral_mono_ae ?_) (hL W (le_of_max_le_left hW) E hE k j hj1 hj2)
  filter_upwards [ae_norm_productValue_le hb h1 h2 hW1 (nT := nT) q hq,
    ae_scattering_unitary hb h1 h2 hW1] with ω hω hU
  have hL1 := one_le_wordLoad b E k q hq j ω (hU j).2
  set L := wordLoad b E k q W j ω
  have hZ' : ‖productValue b E k q W j ω Zs‖ₑ ≤ ENNReal.ofReal L ^ d := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (by linarith)]
    exact ENNReal.ofReal_le_ofReal ((hω j k Zs hZ).trans (pow_le_pow_right₀ hL1 hd))
  have hL1' : 1 ≤ ENNReal.ofReal L := by simpa using ENNReal.ofReal_le_ofReal hL1
  calc ‖productValue b E k q W j ω Zs‖ₑ ^ p ≤ (ENNReal.ofReal L ^ d) ^ p :=
        ENNReal.rpow_le_rpow hZ' hp0.le
    _ = ENNReal.ofReal L ^ ((d : ℝ) * p) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    _ ≤ ENNReal.ofReal L ^ (n : ℝ) := by
        refine ENNReal.rpow_le_rpow_of_exponent_le hL1' ?_
        have := Nat.le_ceil ((d : ℝ) * p)
        simp only [n, Nat.cast_add, Nat.cast_one]; linarith
    _ = ENNReal.ofReal L ^ n := ENNReal.rpow_natCast _ _

/-- Admitted products in the window are integrable. -/
theorem productValue_integrable (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q → ∀ (d : ℕ) (ε T : ℝ),
    0 < ε → ε < T → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI, ∀ (k : Fin nT → ℕ) (j : ℕ), ε * W ≤ j → (j : ℝ) ≤ T * W →
      ∀ Zs : List (TraceWord nT nI), IsAdmittedProduct Zs → productDegree Zs ≤ d →
        Integrable (fun ω => productValue b E k q W j ω Zs) (growthPathLaw W b) := by
  intro b hb0 hb κI hκ nT nI q hq d ε T hε hεT
  obtain ⟨C, W₀, hC⟩ := productValue_eLpNorm_le hMT hGA hLp hSR b hb0 hb κI hκ nT nI q hq d ε T 1
    hε hεT le_rfl
  refine ⟨W₀, fun W hW E hE k j hj1 hj2 Zs hZ hd => ?_⟩
  rw [← memLp_one_iff_integrable]
  have := hC W hW E hE k j hj1 hj2 Zs hZ hd
  rw [ENNReal.ofReal_one] at this
  exact lt_of_le_of_lt this ENNReal.ofReal_lt_top

end BlockBand.SourceProcess.ContractingWords
