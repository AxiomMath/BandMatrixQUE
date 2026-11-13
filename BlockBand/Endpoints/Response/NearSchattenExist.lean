module

public import BlockBand.Endpoints.Response.NearSchattenExistClock

/-!
# Existence of critical clock limits from tightness, Prokhorov and Hausdorff

This file proves `NsCriticalClockLimitsExist` from the tightness clause of
`FullSourceGeneratorContract` (`nse_clock_tight`) and a Prokhorov realization of subsequential
limits (`NsProkhorovRealization`). The a.s. existence of the limiting clock measure is proved in
full (`nse_ae_isClockMeasure`, from the Hausdorff moment theorem `nse_hausdorff_exists`).

## Main results

* `nsCriticalClockLimitsExist_holds (hGen) (hReal) : NsCriticalClockLimitsExist`.
* `nse_prokhorovRealization_of_exists : NsCriticalClockLimitsExist → NsProkhorovRealization`
  (the hypothesis is implied by the conclusion).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-- C-tightness of the clock family's ordinary word values on `[s, T]`, `t₀ ≤ s < T`, in the
exact form of the `FullSourceGeneratorContract.tight` (tight at `s`, asymptotically small
sup-modulus on `[s, T]`), for the one-source family `(noTags, fun _ => q)`.
-/
def NsClockCTight (b E : ℝ) (q : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  ∀ w : ClockWord, IsOrdinaryWord w → ∀ s T : ℝ, t₀ ≤ s → s < T →
    (∀ θ : ℝ, 0 < θ → ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | M < ‖wordValue b E (noTags W) (fun _ => q) W ⌊(W : ℝ) * s⌋₊ ω w‖} ≤
        ENNReal.ofReal θ) ∧
    (∀ η θ : ℝ, 0 < η → 0 < θ → ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | ∃ t ∈ Set.Icc s T, ∃ t' ∈ Set.Icc s T, |t - t'| ≤ δ ∧
        η < ‖wordValue b E (noTags W) (fun _ => q) W ⌊(W : ℝ) * t⌋₊ ω w -
          wordValue b E (noTags W) (fun _ => q) W ⌊(W : ℝ) * t'⌋₊ ω w‖} ≤ ENNReal.ofReal θ)

/-- The `tight` clause at `t₀ = t₁ + R > 0` for a unit source (no tags). -/
theorem nse_clock_tight (hGen : FullSourceGeneratorContract) {b : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) {E : ℝ} (hE : -2 < E) (hE' : E < 2) {t₁ R : ℝ} {q : ℝ → ℝ}
    (hU : IsUnitSource t₁ R q) (hpos : 0 < t₁ + R) : NsClockCTight b E q (t₁ + R) :=
  fun w hw s T hs hsT =>
    hGen.tight b hb hb' E hE hE' (t₁ + R) hpos 0 1 (fun _ => q) (fun _ => ⟨t₁, hU.2.2.2.1⟩)
      noTags (Eventually.of_forall fun _ a => a.elim0) w hw s T hs hsT

/-- Prokhorov realization: for a tight one-source family, every strictly increasing sequence of
widths has a further subsequence along which the word values converge in finite-dimensional
distributions to a joint critical word limit. It is implied by `NsCriticalClockLimitsExist`
(`nse_prokhorovRealization_of_exists`); it omits the a.s. clock-measure clause, which is the
Hausdorff moment problem for the limiting moments (`nse_ae_isClockMeasure`). -/
def NsProkhorovRealization : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q → 0 < t₁ + R →
    NsClockCTight b E q (t₁ + R) →
    ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Z : ClockWord → ℝ → Ω → ℂ),
        IsWordLimit b E noTags (fun _ => q) (t₁ + R) P Z ∧
        NsFddAlong b E q (t₁ + R) P Z (ψ ∘ φ)

/-- **`NsCriticalClockLimitsExist`** from the `tight` clause, the Prokhorov realization
`NsProkhorovRealization` (proved as `nsProkhorovRealization_holds`), and the Hausdorff moment
theorem.
-/
theorem nsCriticalClockLimitsExist_holds (hGen : FullSourceGeneratorContract)
    (hReal : NsProkhorovRealization) : NsCriticalClockLimitsExist := by
  intro b hb hb' E hE hE' t₁ R q hU hpos ψ hψ
  obtain ⟨φ, hφ, Ω, _, P, Z, hW, hfdd⟩ :=
    hReal b hb hb' E hE hE' t₁ R q hU hpos (nse_clock_tight hGen hb hb' hE hE' hU hpos) ψ hψ
  have := hW.prob
  exact ⟨φ, hφ, Ω, inferInstance, P, Z, nseClockMeas Z, hW, hfdd, fun t ht =>
    nse_ae_isClockMeasure hU.2.2.2.1.1 hW.measurable hfdd ht⟩

/-- `NsProkhorovRealization` is implied by `NsCriticalClockLimitsExist`, so it is no stronger. -/
theorem nse_prokhorovRealization_of_exists (h : NsCriticalClockLimitsExist) :
    NsProkhorovRealization := by
  intro b hb hb' E hE hE' t₁ R q hU hpos _ ψ hψ
  obtain ⟨φ, hφ, Ω, inst, P, Z, -, hW, hfdd, -⟩ := h b hb hb' E hE hE' t₁ R q hU hpos ψ hψ
  exact ⟨φ, hφ, Ω, inst, P, Z, hW, hfdd⟩

end BlockBand.Endpoints
