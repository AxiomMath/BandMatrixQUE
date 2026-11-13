module

public import BlockBand.SourceProcess.SourceProcessLaw.Interface
public import BlockBand.SourceProcess.SourceProcessLaw.Analysis

/-!
# `PhysicalApproximation` in the "frequently in `h`" form

* `PhysicalApproximationFreq`: for `M > 0` and `ε > 0`, frequently as `h ↓ 0` and then
  frequently as `K → ∞`, every model value `v` at `(h, K, M)` is eventually (in `W`) within `ε`
  of the physical sampled transform. This allows one to avoid the at most countably many `h` at
  which the entrance law has an atom at `h²`.
* `physicalApproximationFreq_of`: `PhysicalApproximation` implies it.
* `tendsto_of_iterated_freq`: the frequently-form of `tendsto_of_iterated`.
* `PhysicalSamplingWeak`: positive source sampling with any error `e(M) → 0`;
  `physicalSamplingWeak_of`: `PhysicalSampling` (error `C/M`) implies it.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourcePins

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw

/-- **Closing and identification at fixed sample size, frequently in `h` and `K`.** -/
def PhysicalApproximationFreq : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
    ∀ M : ℕ, 0 < M → ∀ ε : ℝ, 0 < ε → ∃ᶠ h in 𝓝[>] (0 : ℝ), ∃ᶠ K in atTop, ∀ v : ℝ,
      FiniteSourceModelValue b E s T q h K M (entranceLaw P μ s) a v →
      ∀ᶠ W in atTop, |sampledPhysTransform b E T q a M W - v| ≤ ε

/-- **Positive source sampling with any vanishing error**: the
sampled transform with `M` tag locations differs from the source transform by `e(M)` for all large
`W`, with `e(M) → 0`. -/
def PhysicalSamplingWeak : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
      ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ M : ℕ, 0 < M → ∀ᶠ W in atTop,
        |sourceTransform b E T q a W - sampledPhysTransform b E T q a M W| ≤ e M

/-- `PhysicalSampling` (error `C/M`) implies the weak form. -/
theorem physicalSamplingWeak_of (h : PhysicalSampling) : PhysicalSamplingWeak := by
  intro b hb0 hb E hE1 hE2 s T hs hsT p q hq J a ha
  obtain ⟨C, hC⟩ := h b hb0 hb E hE1 hE2 s T hs hsT p q hq J a ha
  exact ⟨fun M => C / M, tendsto_const_div_atTop_nhds_zero_nat C, hC⟩

/-- `PhysicalApproximation` implies the frequently-form. -/
theorem physicalApproximationFreq_of (h : PhysicalApproximation) : PhysicalApproximationFreq := by
  intro b hb0 hb E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha M hM ε hε
  obtain ⟨h₀, hh₀, hK⟩ := h b hb0 hb E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha M hM ε hε
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x ∧ x < h₀ :=
    Eventually.and self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hh₀))
  refine (hev.mono fun x hx => ?_).frequently
  obtain ⟨K₀, hK₀⟩ := hK x hx.1 hx.2
  exact (eventually_atTop.2 ⟨K₀, hK₀⟩).frequently

/-- **Iterated limits, frequently-form.** `Φ(·, h) → Λ(h)` for `h > 0`, `Λ → Λ'` as `h ↓ 0`, and
for every `ε`, frequently in `h` then frequently in `K`, eventually `|y_W − Φ(K,h)| ≤ ε`: then
`y → Λ'`. -/
theorem tendsto_of_iterated_freq {y : ℕ → ℝ} {Φ : ℕ → ℝ → ℝ} {Λ : ℝ → ℝ} {Λ' : ℝ}
    (hK : ∀ h, 0 < h → Tendsto (fun K => Φ K h) atTop (𝓝 (Λ h)))
    (hh : Tendsto Λ (𝓝[>] 0) (𝓝 Λ'))
    (hE : ∀ ε : ℝ, 0 < ε → ∃ᶠ h in 𝓝[>] (0 : ℝ), ∃ᶠ K in atTop,
      ∀ᶠ W in atTop, |y W - Φ K h| ≤ ε) :
    Tendsto y atTop (𝓝 Λ') := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ |Λ h - Λ'| < ε / 4 :=
    Eventually.and self_mem_nhdsWithin
      (by simpa [Real.dist_eq] using (Metric.tendsto_nhds.1 hh) (ε / 4) (by linarith))
  obtain ⟨h, ⟨hpos, hΛ⟩, hfK⟩ := (hev.and_frequently (hE (ε / 4) (by linarith))).exists
  have hKev : ∀ᶠ K in atTop, |Φ K h - Λ h| < ε / 4 := by
    simpa [Real.dist_eq] using (Metric.tendsto_nhds.1 (hK h hpos)) (ε / 4) (by linarith)
  obtain ⟨K, hΦ, hW⟩ := (hKev.and_frequently hfK).exists
  filter_upwards [hW] with W hW
  rw [Real.dist_eq]
  have h1 := abs_sub_le (y W) (Φ K h) Λ'
  have h2 := abs_sub_le (Φ K h) (Λ h) Λ'
  linarith

end BlockBand.SourceProcess.SourcePins
