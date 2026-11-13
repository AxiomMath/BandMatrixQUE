module

public import BlockBand.Transmission.Dual.GDomB1

/-!
# Uniqueness of the law of a stop sequence

* `map_eq_of_stopSeq`: two stop sequences (for the same `W`, `t₀`) whose `n`-th stopped paths
  have the same law for every `n` have the same law on `ℕ → CPath d` (`map_le_of_stopSeq`
  both ways with one term and `c = 1`).
* **`map_eq_of_isMPSolutionOn`**: if, for every `n`, the `n`-th path of each sequence is the
  stopped, truncated path `(Y^{τ_{W_n}})^{t₀}` of *some* solution `Y` of the flat dual martingale
  problem of level `q` in `W n` from `z` (on its own space), then the two stop sequences have
  the same law (uniqueness for stopped martingale problems on each `W n`). So the law of
  `F.stopSeq W t₀ r` does not depend on the family, the radii, or the realization: it is the
  canonical law `P^{H_q}_z` on one path space. The same statement transfers pathwise results
  between realizations (e.g. the corner limit from the `p = 1` chart family `SolFamily` to
  `B1Family D₀ 1`) and is the form needed for random starts.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual BlockBand.SourceProcess.Stochastic.Uniqueness
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {d : ℕ} {W : ℕ → Set (Fin d → ℝ)} {t₀ : ℝ≥0}

/-- **Two stop sequences with the same `n`-th laws have the same law.** -/
theorem map_eq_of_stopSeq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsFiniteMeasure P] {Q : Measure Ω'} [IsFiniteMeasure Q]
    (hW : ∀ n, IsOpen (W n)) {Φ : Ω → ℕ → CPath d} {Ψ : Ω' → ℕ → CPath d}
    (hΦ : Measurable Φ) (hΨ : Measurable Ψ) (sΦ : IsStopSeq P W t₀ Φ) (sΨ : IsStopSeq Q W t₀ Ψ)
    (h : ∀ (n : ℕ) (B : Set (ℝ≥0 → Fin d → ℝ)), MeasurableSet B →
      P {x | (Φ x n).1 ∈ B} = Q {x | (Ψ x n).1 ∈ B}) : P.map Φ = Q.map Ψ := by
  refine le_antisymm ?_ ?_
  · have H := map_le_of_stopSeq (ι := Unit) hW hΦ (fun _ => hΨ) sΦ (fun _ => sΨ)
      (c := fun _ => 1) (fun _ => ENNReal.one_ne_top) fun n B hB => by simp [h n B hB]
    simpa using H
  · have H := map_le_of_stopSeq (ι := Unit) hW hΨ (fun _ => hΦ) sΨ (fun _ => sΦ)
      (c := fun _ => 1) (fun _ => ENNReal.one_ne_top) fun n B hB => by simp [h n B hB]
    simpa using H

/-- Truncation of a path at `t₀`. -/
def truncPath (t₀ : ℝ≥0) (w : ℝ≥0 → Fin d → ℝ) : ℝ≥0 → Fin d → ℝ := fun t => w (min t t₀)

theorem measurable_truncPath (t₀ : ℝ≥0) : Measurable (truncPath (d := d) t₀) :=
  measurable_pi_iff.2 fun t => measurable_pi_apply (min t t₀)

variable {q : ℕ} {D0 : ℝ}

/-- The `n`-th path of `Φ` is the stopped, truncated path of a level-`q` dual solution in
`W n` from `z`. -/
def IsDualStopAt {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) (D0 : ℝ)
    (W : ℕ → Set (Fin (q + q) → ℝ)) (t₀ : ℝ≥0) (z : Fin (q + q) → ℝ)
    (Φ : Ω → ℕ → CPath (q + q)) (n : ℕ) : Prop :=
  ∃ (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (Y : ℝ≥0 → Ω → Fin (q + q) → ℝ),
    IsMPSolutionOn Q 𝓖 (flatDrift D0 q) (flatDiff D0 q) (W n) Y ∧
    Q.map (Y 0) = Measure.dirac z ∧
    ∀ x, (Φ x n).1 = fun t => stoppedProcess Y (exitTimeFrom (W n) Y) (min t t₀) x

/-- **The law of a dual stop sequence is unique** (uniqueness for stopped martingale problems
on every `W n`). -/
theorem map_eq_of_isMPSolutionOn (hD0 : 0 < D0) {W : ℕ → Set (Fin (q + q) → ℝ)}
    (hW : ∀ n, IsInteriorDomain (W n) (flatChamber q)) {z : Fin (q + q) → ℝ}
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {Q₁ : Measure Ω₁}
    [IsProbabilityMeasure Q₁] {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
    {Φ : Ω₁ → ℕ → CPath (q + q)} {Ψ : Ω₂ → ℕ → CPath (q + q)}
    (hΦ : Measurable Φ) (hΨ : Measurable Ψ) (sΦ : IsStopSeq Q₁ W t₀ Φ)
    (sΨ : IsStopSeq Q₂ W t₀ Ψ) (hΦn : ∀ n, IsDualStopAt Q₁ D0 W t₀ z Φ n)
    (hΨn : ∀ n, IsDualStopAt Q₂ D0 W t₀ z Ψ n) : Q₁.map Φ = Q₂.map Ψ := by
  refine map_eq_of_stopSeq (fun n => (hW n).1) hΦ hΨ sΦ sΨ fun n B hB => ?_
  obtain ⟨𝓖₁, Y₁, h₁, h₁0, e₁⟩ := hΦn n
  obtain ⟨𝓖₂, Y₂, h₂, h₂0, e₂⟩ := hΨn n
  have hh := isHTransform_cauchyH (q := q) D0
  have hfull := stoppedMartingaleProblemUniquenessPosDef_holds (q + q) (flatDrift D0 q)
    (flatDiff D0 q) (flatChamber q) (W n) hh.isOpen hh.lip ((contDiffOn_flatDiff D0).mono hh.sub)
    (fun w hw => flatDiff_posDef hD0 (hh.sub hw)) (hW n) Ω₁ Q₁ 𝓖₁ Y₁ Ω₂ Q₂ 𝓖₂ Y₂ h₁ h₂
    (h₁0.trans h₂0.symm)
  have hBt : MeasurableSet (truncPath t₀ ⁻¹' B) := measurable_truncPath t₀ hB
  have hm₁ : {x | (Φ x n).1 ∈ B} =
      (fun ω t => stoppedProcess Y₁ (exitTimeFrom (W n) Y₁) t ω) ⁻¹' (truncPath t₀ ⁻¹' B) := by
    ext x; simp only [mem_ofPred_eq, mem_preimage, e₁ x]; rfl
  have hm₂ : {x | (Ψ x n).1 ∈ B} =
      (fun ω t => stoppedProcess Y₂ (exitTimeFrom (W n) Y₂) t ω) ⁻¹' (truncPath t₀ ⁻¹' B) := by
    ext x; simp only [mem_ofPred_eq, mem_preimage, e₂ x]; rfl
  rw [hm₁, hm₂, ← Measure.map_apply_of_aemeasurable _ hBt,
    ← Measure.map_apply_of_aemeasurable _ hBt, hfull]
  · exact aemeasurable_stopped (fun t => (h₂.adapted t).measurable) h₂.continuous (hW n).1
  · exact aemeasurable_stopped (fun t => (h₁.adapted t).measurable) h₁.continuous (hW n).1

/-- The stop sequence of a `B1Family` is a dual stop sequence (radii large enough). -/
theorem B1Family.isDualStopAt (hD0 : 0 < D0) {z : Fin (q + q) → ℝ} (F : B1Family D0 q z)
    (hz : z ∈ flatChamber q) {W : ℕ → Set (Fin (q + q) → ℝ)} {r : ℕ → ℕ}
    (hball : ∀ n, W n ⊆ chartQ q '' Metric.ball 0 (r n)) (n : ℕ) :
    IsDualStopAt (Pq q) D0 W t₀ z (F.stopSeq W t₀ r) n :=
  ⟨𝓖q q, F.Yf (r n), isMPSolutionOn_mono (F.isMPSolutionOn_Yf hD0 (r n)) (hball n),
    F.map_Yf_zero hz (r n), fun _ => rfl⟩

end BlockBand.Transmission.Dual.G
