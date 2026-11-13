module

public import BlockBand.SourceProcess.FullSourceGenerator.GenFinite

/-!
# The finite-`W` input of the limit passage: cylinder tests

`tendsto_tested_cyl`: the increments of `Φ - ∫𝒜Φ` between times `s ≤ t`, tested against bounded
continuous functions of finitely many word values before `s`, vanish as `W → ∞`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory MvPolynomial Finset Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

theorem measurable_wordValue_past (b E : ℝ) {W nT nI : ℕ} (k : Fin nT → ℕ)
    (q : Fin nI → ℝ → ℝ) {i j : ℕ} (h : i ≤ j) (w : TraceWord nT nI) :
    Measurable[growthSigma W j] fun ω : GrowthPath W => wordValue b E k q W i ω w := by
  have e : (fun ω : GrowthPath W => wordValue b E k q W i ω w) =
      fun ω => polyValue b E k q W i ω (X w) := by funext ω; simp [polyValue]
  rw [e]; exact measurable_polyValue_past b E k q h _

/-- **The cylinder-tested finite-`W` increments vanish.** -/
theorem tendsto_tested_cyl (hES : EarlySummed) (hFS : FullSourceStopsContract)
    (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ}
    (hE1 : -2 < E) (hE2 : E < 2) {t₀ : ℝ} (ht₀ : 0 < t₀) {nT nI : ℕ} {q : Fin nI → ℝ → ℝ}
    (hq : ∀ a, ∃ s : ℝ, IsSourceTest s t₀ (q a)) (k : ℕ → Fin nT → ℕ)
    (hk : ∀ᶠ W in atTop, ∀ a, ((k W a + 1 : ℕ) : ℝ) ≤ W * t₀) {Φ : TracePoly nT nI}
    (hΦ : IsOrdinaryPoly Φ) {s t : ℝ} (hs : t₀ ≤ s) (hst : s ≤ t) {m : ℕ}
    (ws : Fin m → TraceWord nT nI) (us : Fin m → ℝ) (hus : ∀ l, us l ≤ s)
    (φ : BoundedContinuousFunction (Fin m → ℂ) ℝ) :
    Tendsto (fun W : ℕ => ∫ ω, ((φ fun l => wordValue b E (k W) q W ⌊(W : ℝ) * us l⌋₊ ω (ws l) :
      ℝ) : ℂ) * (polyValue b E (k W) q W ⌊(W : ℝ) * t⌋₊ ω Φ -
        polyValue b E (k W) q W ⌊(W : ℝ) * s⌋₊ ω Φ - ∑ j ∈ Ico ⌊(W : ℝ) * s⌋₊ ⌊(W : ℝ) * t⌋₊,
          (W : ℂ)⁻¹ * polyValue b E (k W) q W j ω (wordGenerator b E q (t₀ + 1) Φ))
        ∂growthPathLaw W b) atTop (𝓝 0) := by
  have hqI : IsIntervalTests q := fun a => let ⟨s', hs'⟩ := hq a; ⟨s', t₀, hs'⟩
  have hq0 : ∀ a x, t₀ < x → q a x = 0 := fun a x hx => by
    obtain ⟨s', hs'⟩ := hq a
    exact hs'.2.1 x fun h => by linarith [h.2]
  have hs0 : 0 < s := lt_of_lt_of_le ht₀ hs
  set ξ : (W : ℕ) → GrowthPath W → ℂ := fun W ω =>
    ((φ fun l => wordValue b E (k W) q W ⌊(W : ℝ) * us l⌋₊ ω (ws l) : ℝ) : ℂ)
  have hξb : ∀ W ω, ‖ξ W ω‖ ≤ ‖φ‖ := fun W ω => by
    simp only [ξ, Complex.norm_real]; exact φ.norm_coe_le_norm _
  refine tendsto_tested hES hFS hMT hGA hLp hSR hb0 hb hE1 hE2 hqI hq0 hΦ (ε := t₀ / 2)
    (T := t + 1) (by positivity) (by linarith) k (fun W => ⌊(W : ℝ) * s⌋₊)
    (fun W => ⌊(W : ℝ) * t⌋₊) ?_ ξ ?_ (B := ‖φ‖ ^ 4) ?_ ?_
  · filter_upwards [hk, eventually_ge_atTop ⌈2 / t₀⌉₊] with W hkW hW
    have hW2 : 2 ≤ (W : ℝ) * t₀ := by
      have := (Nat.ceil_le.mp hW)
      rwa [div_le_iff₀ ht₀] at this
    have hWr : (0 : ℝ) ≤ W := Nat.cast_nonneg W
    have hfs := Nat.lt_floor_add_one ((W : ℝ) * s)
    have hWs : (W : ℝ) * t₀ ≤ W * s := mul_le_mul_of_nonneg_left hs hWr
    refine ⟨?_, ?_, Nat.floor_mono (mul_le_mul_of_nonneg_left hst hWr), ?_, fun a => ?_⟩
    · nlinarith
    · nlinarith
    · calc ((⌊(W : ℝ) * t⌋₊ : ℕ) : ℝ) ≤ W * t := Nat.floor_le (by nlinarith)
        _ ≤ (t + 1) * W := by nlinarith
    · have h1 : ((k W a + 1 : ℕ) : ℝ) ≤ W * s := (hkW a).trans hWs
      exact Nat.lt_of_succ_le (Nat.le_floor h1)
  · intro W
    have hv : Measurable[growthSigma W ⌊(W : ℝ) * s⌋₊] fun ω : GrowthPath W =>
        fun l => wordValue b E (k W) q W ⌊(W : ℝ) * us l⌋₊ ω (ws l) :=
      @Measurable.of_eval _ _ _ (growthSigma W ⌊(W : ℝ) * s⌋₊) _ _ fun l =>
        measurable_wordValue_past b E (k W) q
        (Nat.floor_mono (mul_le_mul_of_nonneg_left (hus l) (Nat.cast_nonneg W))) (ws l)
    have hf : Measurable[growthSigma W ⌊(W : ℝ) * s⌋₊] (ξ W) :=
      Complex.measurable_ofReal.comp (φ.continuous.measurable.comp hv)
    exact hf.stronglyMeasurable
  · refine Eventually.of_forall fun W => ?_
    calc ∫⁻ ω, ‖ξ W ω‖ₑ ^ 4 ∂growthPathLaw W b ≤ ∫⁻ _, ENNReal.ofReal (‖φ‖ ^ 4) ∂growthPathLaw W b :=
          lintegral_mono fun ω => by
            rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hξb W ω) 4)
      _ = ENNReal.ofReal (‖φ‖ ^ 4) := by simp
  · exact fun K => ⟨‖φ‖, norm_nonneg _, Eventually.of_forall fun W =>
      Eventually.of_forall fun ω _ => hξb W ω⟩

end BlockBand.SourceProcess.FullSourceGenerator
