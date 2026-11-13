module

public import BlockBand.Transmission.LengthUniform.JetMoments
public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# The `jet` field of `TransmissionLengthUniformContract`

The `L^p` norms of the jet distances `δ₀, δ₁` along the growth path on `εW ≤ r ≤ TW` are
`O(1/W)` with a constant chosen before `T` (`lengthUniform_jet_of`, `lengthUniform_jet_holds`).

* `deltaZeroExit_of_uniform`: the `δ₀` exit bound from `DeltaZeroLengthUniform`
  (`exit_of_moment`). The exit
  has no constant; its `W₀` depends on `T` necessarily (union over `TW` lengths).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LengthUniform

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.PathScalar BlockBand.Transmission.PathJet
open scoped ENNReal

/-- `c log W ≤ εW` for all large `W` (`log W ≤ 2√W`). -/
theorem log_le_eps_mul (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → c * Real.log W ≤ ε * W := by
  set a := 2 * |c| / ε with ha
  have ha0 : 0 ≤ a := by positivity
  refine ⟨⌈a ^ 2⌉₊ + 1, fun W hW => ?_⟩
  have hx1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hx0 : (0 : ℝ) < W := by linarith
  set x : ℝ := (W : ℝ) with hx
  have hax : a ^ 2 ≤ x := (Nat.le_ceil _).trans (by
    have : ((⌈a ^ 2⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (by omega : ⌈a ^ 2⌉₊ ≤ W)
    exact this)
  set s := Real.sqrt x with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hx0
  have hss : s * s = x := Real.mul_self_sqrt hx0.le
  have has : a ≤ s := by
    rw [hs, ← Real.sqrt_sq ha0]; exact Real.sqrt_le_sqrt hax
  have hlog : Real.log x ≤ 2 * s := by
    have h1 : Real.log s = Real.log x / 2 := Real.log_sqrt hx0.le
    have h2 := Real.log_le_sub_one_of_pos hs0
    linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hc : c * Real.log x ≤ |c| * Real.log x :=
    mul_le_mul_of_nonneg_right (le_abs_self c) hlog0
  have h2c : 2 * |c| ≤ ε * s := by
    have : 2 * |c| = ε * a := by rw [ha]; field_simp
    rw [this]; exact mul_le_mul_of_nonneg_left has hε.le
  calc c * Real.log x ≤ |c| * Real.log x := hc
    _ ≤ |c| * (2 * s) := mul_le_mul_of_nonneg_left hlog (abs_nonneg c)
    _ = (2 * |c|) * s := by ring
    _ ≤ (ε * s) * s := mul_le_mul_of_nonneg_right h2c hs0.le
    _ = ε * x := by rw [mul_assoc, hss]

/-- **The `jet` field from the length-uniform `PassiveJetMoments`.** -/
theorem lengthUniform_jet_of (hU : PassiveJetMomentsUniform) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI ε p : ℝ, 0 < κI → 0 < ε → 1 ≤ p →
      ∃ C : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
        ∀ s : ℂ, IsStationaryJet b E s → ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
          eLpNorm (fun ω => jetDistance0 b E (pathX b E W r ω)) (ENNReal.ofReal p)
              (growthPathLaw W b) +
            eLpNorm (fun ω => jetDistance1 b E s (pathX b E W r ω)) (ENNReal.ofReal p)
              (growthPathLaw W b) ≤
            ENNReal.ofReal (C / W) := by
  intro b hb0 hb κI ε p hκ hε hp
  obtain ⟨C₁, C, hC⟩ := hU b hb0 hb κI p hκ hp
  refine ⟨C, fun T => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC T
  obtain ⟨W₁, hlog⟩ := log_le_eps_mul C₁ hε
  refine ⟨max (max W₀ W₁) 1, fun W hW E hE s hs r hεr hrT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW0, hW1⟩, hW1'⟩ := hW
  have hx : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hr1 : 1 ≤ r := by
    have : (0 : ℝ) < r := lt_of_lt_of_le (mul_pos hε hx) hεr
    exact_mod_cast this
  exact hW₀ W hW0 E hE s hs r hr1 ((hlog W hW1).trans hεr) hrT

/-- **`TransmissionLengthUniformContract.jet` from the input hypotheses**
`MatchedTracesContract`, `GaussianAbsorptionContract` and `GaussianLpGradient`.
-/
theorem lengthUniform_jet_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI ε p : ℝ, 0 < κI → 0 < ε → 1 ≤ p →
      ∃ C : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
        ∀ s : ℂ, IsStationaryJet b E s → ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
          eLpNorm (fun ω => jetDistance0 b E (pathX b E W r ω)) (ENNReal.ofReal p)
              (growthPathLaw W b) +
            eLpNorm (fun ω => jetDistance1 b E s (pathX b E W r ω)) (ENNReal.ofReal p)
              (growthPathLaw W b) ≤
            ENNReal.ofReal (C / W) :=
  lengthUniform_jet_of
    (passiveJetMomentsUniform_of (deltaZeroLengthUniform_holds hMT hGA hLp) hGA hLp)

example (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (H : TransmissionLengthUniformContract) :
    TransmissionLengthUniformContract :=
  { H with jet := lengthUniform_jet_holds hMT hGA hLp }

example (H : TransmissionLengthUniformContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI ε p : ℝ, 0 < κI → 0 < ε → 1 ≤ p →
      ∃ C : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
        ∀ s : ℂ, IsStationaryJet b E s → ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
          eLpNorm (fun ω => jetDistance0 b E (pathX b E W r ω)) (ENNReal.ofReal p)
              (growthPathLaw W b) +
            eLpNorm (fun ω => jetDistance1 b E s (pathX b E W r ω)) (ENNReal.ofReal p)
              (growthPathLaw W b) ≤
            ENNReal.ofReal (C / W) :=
  H.jet

/-- **The `δ₀` exit clause from length-uniform moments** (as in `PathScalar.exit_of_moment`; same form as
`PassiveInitialScalarContract.exit`).
-/
theorem deltaZeroExit_of_uniform (hδ : DeltaZeroLengthUniform) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T d D : ℝ, 0 < κ → 0 < d → 0 < D →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        growthPathLaw W b {ω | ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ T * W ∧
          d < jetDistance0 b E (pathX b E W r ω)} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) :=
  exit_of_moment fun b hb hb' κ T p hκ hp => by
    obtain ⟨C, -, hC⟩ := hδ b hb hb' κ p hκ hp
    obtain ⟨W₀, hW₀⟩ := hC T
    exact ⟨C, W₀, hW₀⟩

end BlockBand.Transmission.LengthUniform
