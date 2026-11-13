module

public import BlockBand.Transmission.Dual.GJDominate

/-!
# The collision bound: the hitting event is contained in the cylinder event

* `stop_mem_of_hit` (deterministic): if a continuous path started in an open `W'` leaves `W'` at
  some time `s ≤ t₀` while staying in `W` up to `s`, then the path stopped at its exit from `W'`
  is, at time `t₀`, in `W \ W'`.
* **`lemmaC_hit`**: for `W' = W \ A` an interior domain of `𝒞_q` containing `z` and a comparison
  solution `Y₂` in `W'` (continuous paths), if `H_q ≤ M` on `A ∩ closure W'` then
  `Q₂(∃ s ≤ t₀, s < τ_W(Y₂), Y₂(s) ∈ A) ≤ M / H_q(z)`. With `A = B_δ` and `W = int K_n` this is
  `P^{H_q}(S < ρ_n ∧ t₀) ≤ C δ / H_q(z)` (with `S ≤ t₀` in place of `S < t₀`), via `lemmaC_gap`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime
  stopTime_coe exitTimeFrom_attained mem_of_lt_exitTimeFrom)
open scoped NNReal

/-- **The deterministic inclusion of the collision bound.** -/
theorem stop_mem_of_hit {Ω : Type*} {d : ℕ} {W W' : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ}
    {ω : Ω} (hW' : IsOpen W') (hY : Continuous fun t => Y t ω) {s t₀ : ℝ≥0} (hst : s ≤ t₀)
    (hs : Y s ω ∉ W') (hin : ∀ r ≤ s, Y r ω ∈ W) :
    Y (stopTime (exitTimeFrom W' Y ω) t₀) ω ∈ W ∧ Y (stopTime (exitTimeFrom W' Y ω) t₀) ω ∉ W' := by
  have hle : exitTimeFrom W' Y ω ≤ s := iInf₂_le s hs
  rcases exitTimeFrom_attained hW' hY with h | ⟨s₀, h, hs₀⟩
  · rw [h] at hle; exact absurd hle (not_le.2 (WithTop.coe_lt_top s))
  · rw [h] at hle ⊢
    have hs₀s : s₀ ≤ s := WithTop.coe_le_coe.1 hle
    rw [stopTime_coe, min_eq_right (hs₀s.trans hst)]
    exact ⟨hin s₀ hs₀s, hs₀⟩

variable {q : ℕ} {D0 : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {Z : ℝ≥0 → Ω → Fin (q + q) → ℝ} {z : Fin (q + q) → ℝ} {W A : Set (Fin (q + q) → ℝ)}
  {Ω₂ : Type} [MeasurableSpace Ω₂] {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
  {𝓗 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)} {Y₂ : ℝ≥0 → Ω₂ → Fin (q + q) → ℝ}

/-- **The collision bound, hitting form**: `Q₂(∃ s ≤ t₀, s < τ_W(Y₂), Y₂(s) ∈ A) ≤ M / H_q(z)`
when `H_q ≤ M` on `A ∩ closure (W \ A)`. -/
theorem lemmaC_hit (hD0 : 0 < D0) (hZ : IsBaseSol D0 q P 𝓖 Z z)
    (hW : IsInteriorDomain (W \ A) (flatChamber q)) (hzW : z ∈ W \ A)
    (h₂ : IsMPSolutionOn Q₂ 𝓗 (flatDrift D0 q) (flatDiff D0 q) (W \ A) Y₂)
    (h₂0 : Q₂.map (Y₂ 0) = Measure.dirac z) (hc : ∀ ω, Continuous fun t => Y₂ t ω) (t₀ : ℝ≥0)
    (hA : MeasurableSet A) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ w ∈ A ∩ closure (W \ A), flatH q w ≤ M) :
    Q₂.real {ω | ∃ s ≤ t₀, (s : WithTop ℝ≥0) < exitTimeFrom W Y₂ ω ∧ Y₂ s ω ∈ A} ≤
      M / flatH q z := by
  refine (measureReal_mono fun ω hω => ?_).trans (lemmaC_bound hD0 hZ hW hzW h₂ h₂0 t₀ hA hM0 hM)
  obtain ⟨s, hst, hlt, hsA⟩ := hω
  have H := stop_mem_of_hit hW.1 (hc ω) hst (fun h => h.2 hsA) fun r hr =>
    mem_of_lt_exitTimeFrom (lt_of_le_of_lt (WithTop.coe_le_coe.2 hr) hlt)
  show Y₂ (stopTime (exitTimeFrom (W \ A) Y₂ ω) t₀) ω ∈ A
  by_contra hn
  exact H.2 ⟨H.1, hn⟩

end BlockBand.Transmission.Dual.G
