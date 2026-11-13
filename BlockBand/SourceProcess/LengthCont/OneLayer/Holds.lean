module

public import BlockBand.SourceProcess.LengthCont.OneLayer.PastBound
public import BlockBand.SourceProcess.LengthCont.Split
public import BlockBand.SourceProcess.RawTag.Holds
public import BlockBand.SourceProcess.RawTag.DeltaBounds

/-!
# `LayerDriftBounds` holds

```
theorem layerDriftBounds_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) : LayerDriftBounds
```

Hypotheses: exactly those of `RawTag.rawTagMoments_holds` (`GaussianAbsorptionContract`,
`ScalarRecursionContract`, `MatchedTracesContract`, `GaussianLpGradient`). Window:
`δ = (T - max τ)/2`, so every probe is born before `(T - δ)W`.
For `W ≥ W₀` and `(T-δ)W ≤ n ≤ (T+δ)W`, `window_step` (conditioning on the fresh layer)
reduces the drift and the martingale difference to past integrals of the fresh sizes, which
`drift_integral` / `var_integral` bound by `C/W` with:
* the one-layer `Δ` bounds `RawTag.delta_fresh_bounds hGA hLp` (`p = 4`);
* `‖δ₀‖_q ≤ C_q/W`, `LengthUniform.deltaZeroLengthUniform_holds hMT hGA hLp`;
* frame moments, `RawTag.momBd_frame` with `EnergyUniform.fullSourceMomentsEnergyUniform_holds`;
* conductance moments, `SourceMixing.conductanceMomentBound_holds hMT hGA hLp`
  (with `W/(n+1) ≤ 1/(T-δ)` on the window);
* the `L²` increment (integrability) from `RawTag.rawTagMoments_holds` through
  `memLp_incr_of_rawTagMoments`.

Corollaries: `LayerIncrementBounds`, `LengthContinuity` and
`ComplexSourceLimitSequenceContract` from the same four hypotheses.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont.OneLayer

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionSequences BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ComplexSourceLaw
open scoped ENNReal

/-- `W/(n+1) ≤ 1/a` when `aW ≤ n`, `a > 0`. -/
theorem div_succ_le {a : ℝ} (ha : 0 < a) {W n : ℕ} (hn : a * W ≤ n) :
    (W : ℝ) / ((n : ℝ) + 1) ≤ 1 / a := by
  rw [div_le_div_iff₀ (by positivity) ha]
  nlinarith

/-- **`LayerDriftBounds` holds** from the four input hypotheses. -/
theorem layerDriftBounds_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) : LayerDriftBounds := by
  intro b E np τ m T hdom
  have hdom' := hdom
  obtain ⟨hb0, hb1, hE1, hE2, -, hτ0, hm, hτT⟩ := hdom
  rcases Nat.eq_zero_or_pos np with hnp | hnp
  · subst hnp
    exact ⟨1, one_pos, 0, 0, fun _ _ _ _ _ _ i => i.elim0⟩
  have hne : (Finset.univ : Finset (Fin np)).Nonempty := ⟨⟨0, hnp⟩, Finset.mem_univ _⟩
  set τmax := Finset.univ.sup' hne τ
  have hτle : ∀ j, τ j ≤ τmax := fun j => Finset.le_sup' τ (Finset.mem_univ j)
  have hτmaxT : τmax < T := (Finset.sup'_lt_iff hne).2 fun j _ => hτT j
  have hτmax0 : 0 < τmax := lt_of_lt_of_le (hτ0 ⟨0, hnp⟩) (hτle _)
  set δ := (T - τmax) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hTδ : T - δ = τmax + δ := by simp only [δ]; ring
  have hTδ0 : 0 < T - δ := by rw [hTδ]; linarith
  set T' := T + δ + 1
  set κ := min (2 + E) (2 - E)
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hEκ : E ∈ bulkInterval κ :=
    ⟨by linarith [min_le_left (2 + E) (2 - E)], by linarith [min_le_right (2 + E) (2 - E)]⟩
  -- the inputs
  obtain ⟨Cm, Cf, W₁, hCm, hCf, hdf⟩ :=
    BlockBand.SourceProcess.RawTag.delta_fresh_bounds hGA hLp b hb0 hb1 κ hκ 4 (by norm_num)
  have hR := BlockBand.SourceProcess.RawTag.rawTagMoments_holds hGA hLp hSR hMT
  obtain ⟨W₂, hW₂⟩ := memLp_incr_of_rawTagMoments hR b E τ m T hdom' T'
  have hδU := BlockBand.Transmission.LengthUniform.deltaZeroLengthUniform_holds hMT hGA hLp
  obtain ⟨D2, hD2, hD2T⟩ := delta_moment hδU hb0 hb1 hκ 2 (by norm_num)
  obtain ⟨W₃, hW₃⟩ := hD2T T'
  obtain ⟨D4, hD4, hD4T⟩ := delta_moment hδU hb0 hb1 hκ 4 (by norm_num)
  obtain ⟨W₄, hW₄⟩ := hD4T T'
  obtain ⟨D8, hD8, hD8T⟩ := delta_moment hδU hb0 hb1 hκ 8 (by norm_num)
  obtain ⟨W₅, hW₅⟩ := hD8T T'
  have hFS := BlockBand.Transmission.EnergyUniform.fullSourceMomentsEnergyUniform_holds hGA hLp hSR
  obtain ⟨A8, W₆, hA8, hF8⟩ := frame_moment hFS hb0 hb1 hκ T' 8 (by norm_num)
  obtain ⟨A16, W₇, hA16, hF16⟩ := frame_moment hFS hb0 hb1 hκ T' 16 (by norm_num)
  have hCM := BlockBand.Transmission.SourceMixing.conductanceMomentBound_holds hMT hGA hLp
  obtain ⟨CH4, hCH4, hH4⟩ := hFun_moment hCM hb0 hb1 hE1 hE2 T' 4 (by norm_num)
  obtain ⟨CH8, hCH8, hH8⟩ := hFun_moment hCM hb0 hb1 hE1 hE2 T' 8 (by norm_num)
  -- the constants
  set H4b := 2 ^ 4 * (1 + ((2 * etaZ b E ^ 2) ^ 4)⁻¹ * CH4 * (1 + (1 / (T - δ)) ^ 4))
  set H8b := 2 ^ 8 * (1 + ((2 * etaZ b E ^ 2) ^ 8)⁻¹ * CH8 * (1 + (1 / (T - δ)) ^ 8))
  have hH4b : 0 ≤ H4b := by positivity
  have hH8b : 0 ≤ H8b := by positivity
  set M := ∑ j, m j
  set Cd := M * sizeK b E * (Cm + 2 * (Cm + Cf) ^ 2) *
    (3 / 2 * D2 ^ 2 + 3 / 2 * D4 ^ 4 + 3 / 2 + 128 * A8 ^ 8 + 1 / 4 * H4b)
  set Cv := 3 * M ^ 2 * sizeK b E ^ 2 * (Cf + 2 * (Cm + Cf) ^ 2) ^ 2 *
    (3 / 2 + 3 / 2 * D4 ^ 4 + 3 / 2 * D8 ^ 8 + 2 ^ 15 * A16 ^ 16 + 1 / 4 * H8b)
  refine ⟨δ, hδ, max Cd Cv, max (max (max W₁ W₂) (max W₃ W₄)) (max (max W₅ W₆) (max W₇ 1)),
    fun W hW n hn1 hn2 r i k s => ?_⟩
  have hW1 : W₁ ≤ W := by omega
  have hW2 : W₂ ≤ W := by omega
  have hW3 : W₃ ≤ W := by omega
  have hW4 : W₄ ≤ W := by omega
  have hW5 : W₅ ≤ W := by omega
  have hW6 : W₆ ≤ W := by omega
  have hW7 : W₇ ≤ W := by omega
  have hWone : 1 ≤ W := by omega
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hWone
  have hW0 : (0 : ℝ) < W := by linarith
  -- the window
  have hβ : ∀ j, birth W τ j < n := by
    intro j
    have h1 : (birth W τ j : ℝ) ≤ W * τ j :=
      Nat.floor_le (mul_nonneg hW0.le (hτ0 j).le)
    have h2 : (W : ℝ) * τ j ≤ W * τmax := mul_le_mul_of_nonneg_left (hτle j) hW0.le
    have h3 : (W : ℝ) * τmax < (T - δ) * W := by rw [hTδ]; nlinarith
    exact_mod_cast (show (birth W τ j : ℝ) < n by linarith)
  have hn : 1 ≤ n := by
    have : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn1
    exact_mod_cast this
  have hnT : (n : ℝ) ≤ T' * W := by
    have : (T + δ) * W ≤ T' * W := mul_le_mul_of_nonneg_right (by simp only [T']; linarith)
      hW0.le
    linarith
  have hn1T : ((n + 1 : ℕ) : ℝ) ≤ T' * W := by
    push_cast
    have : (T + δ) * W + 1 ≤ T' * W := by simp only [T']; nlinarith
    linarith
  have hint := ((hW₂ W hW2 n hn1T r i k s).integrable one_le_two)
  have hdf' : DeltaFresh b E W Cm Cf := fun X hX => hdf W hW1 E hEκ X hX
  have hμM := norm_massF_le m hm i k
  have hWn : (W : ℝ) / ((n : ℝ) + 1) ≤ 1 / (T - δ) := div_succ_le hTδ0 hn1
  have hWn0 : 0 ≤ (W : ℝ) / ((n : ℝ) + 1) := by positivity
  have hh4 : ∫⁻ x, ENNReal.ofReal (hFun b E W n x.1 ^ 4) ∂probedPathLaw W np b ≤
      ENNReal.ofReal H4b := by
    refine (hH4 W hWone n hnT np).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← div_pow]
    have := pow_le_pow_left₀ hWn0 hWn 4
    simp only [H4b]
    gcongr
  have hh8 : ∫⁻ x, ENNReal.ofReal (hFun b E W n x.1 ^ 8) ∂probedPathLaw W np b ≤
      ENNReal.ofReal H8b := by
    refine (hH8 W hWone n hnT np).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← div_pow]
    have := pow_le_pow_left₀ hWn0 hWn 8
    simp only [H8b]
    gcongr
  have hdr := drift_integral b E W n τ m i k hWone hCm hCf hμM (by positivity) hH4b
    (hW₃ W hW3 E hEκ n hn hnT np) (hW₄ W hW4 E hEκ n hn hnT np)
    (hF8 W hW6 E hEκ n (birth W τ i) (hβ i) hnT np i)
    (hF8 W hW6 E hEκ n (birth W τ k) (hβ k) hnT np k) hh4
  have hva := var_integral b E W n τ m i k hWone hCm hCf hμM hD4 hD8 (by positivity) hH8b
    (hW₄ W hW4 E hEκ n hn hnT np) (hW₅ W hW5 E hEκ n hn hnT np)
    (hF16 W hW7 E hEκ n (birth W τ i) (hβ i) hnT np i)
    (hF16 W hW7 E hEκ n (birth W τ k) (hβ k) hnT np k) hh8
  have hCd : Cd / W ≤ max Cd Cv / W := div_le_div_of_nonneg_right (le_max_left _ _) hW0.le
  have hCv : Cv / W ≤ max Cd Cv / W := div_le_div_of_nonneg_right (le_max_right _ _) hW0.le
  have hCd0 : 0 ≤ Cd := by
    have : 0 ≤ M := Finset.sum_nonneg fun j _ => hm j
    have : 0 ≤ sizeK b E := by unfold sizeK; positivity
    positivity
  exact window_step hb0 hb1 hE1 hE2 hWone τ m hm hn hβ hCm hCf hdf' r i k s hint
    (by have := le_max_left Cd Cv; positivity) (by have := le_max_left Cd Cv; positivity)
    (hdr.trans (ENNReal.ofReal_le_ofReal hCd)) (hva.trans (ENNReal.ofReal_le_ofReal hCv))

/-- `LayerIncrementBounds` from the same four hypotheses. -/
theorem layerIncrementBounds_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) : LayerIncrementBounds :=
  layerIncrementBounds_of (BlockBand.SourceProcess.RawTag.rawTagMoments_holds hGA hLp hSR hMT)
    (layerDriftBounds_holds hGA hLp hSR hMT)

/-- `LengthContinuity` from the same four hypotheses. -/
theorem lengthContinuity_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) : LengthContinuity :=
  lengthContinuity_of_drift (BlockBand.SourceProcess.RawTag.rawTagMoments_holds hGA hLp hSR hMT)
    (layerDriftBounds_holds hGA hLp hSR hMT)

/-- `ComplexSourceLimitSequenceContract` from the same four hypotheses. -/
theorem complexSourceLimitSequence_holds' (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) :
    ComplexSourceLimitSequenceContract :=
  complexSourceLimitSequence_of_drift
    (BlockBand.SourceProcess.RawTag.rawTagMoments_holds hGA hLp hSR hMT)
    (layerDriftBounds_holds hGA hLp hSR hMT)

end BlockBand.SourceProcess.LengthCont.OneLayer
