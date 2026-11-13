module

public import BlockBand.SourceProcess.SourceProcessLaw.Entrance

/-!
# The finite-model value `Φ(K, h, M)` is well defined

`modelValue_exists`: under `ModelExists` and `ModelUnique`, the finite source model at
`(h, K, M)` has a transform value, determined by its unique Gram law.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessLaw

open MeasureTheory ProbabilityTheory Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal

theorem continuous_probeBlock {K p M : ℕ} :
    Continuous (fun G : GramState (SrcCol K (Fin p × Fin M)) => probeBlock G.1) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have h1 : Continuous fun A : Matrix (SrcCol K (Fin p × Fin M)) (SrcCol K (Fin p × Fin M)) ℂ =>
      A (Sum.inr i) (Sum.inr j) := by fun_prop
  exact h1.comp continuous_fst

section Meas

variable {c : Type} [Fintype c]

/-- Local Borel structure on Gram states (the product topology of matrices). -/
theorem gramState_borel : BorelSpace (GramState c) := by
  have : BorelSpace (Matrix c c ℂ) := inferInstanceAs (BorelSpace (c → c → ℂ))
  have : SecondCountableTopology (Matrix c c ℂ) :=
    inferInstanceAs (SecondCountableTopology (c → c → ℂ))
  exact Prod.borelSpace

theorem measurable_of_stronglyMeasurable_gram {Ω : Type} {m m₀ : MeasurableSpace Ω}
    (hle : m₀ ≤ m) {G : Ω → GramState c} (h : StronglyMeasurable[m₀] G) : Measurable[m] G := by
  have : BorelSpace (GramState c) := gramState_borel
  have : TopologicalSpace.PseudoMetrizableSpace (Matrix c c ℂ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (c → c → ℂ))
  exact (h.mono hle).measurable

end Meas

theorem measurable_sampledTransformValue {K p M J : ℕ} (a : Fin J → Fin p → ℝ) :
    Measurable (sampledTransformValue (K := K) (M := M) a) := by
  have : BorelSpace (GramState (SrcCol K (Fin p × Fin M))) := gramState_borel
  unfold sampledTransformValue
  refine Finset.measurable_prod _ fun j _ => ?_
  refine Complex.measurable_re.comp (Measurable.inv ?_)
  exact (Continuous.matrix_det (continuous_const.add (continuous_const.mul
    continuous_probeBlock))).measurable

/-- **`Φ(K, h, M)` exists**: the finite source model at `(h, K, M)` has a transform value. -/
theorem modelValue_exists (hB1 : ModelExists) (hB2 : ModelUnique) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {s T : ℝ} (hs : 0 < s) (hsT : s < T) {p : ℕ}
    {q : Fin p → ℝ → ℝ} (hq : ∀ i, IsSourceTest s T (q i))
    {entrance : Measure (Measure unitInterval)}
    (hent : ∃ ρ : Measure (ℕ → ℝ), IsProbabilityMeasure ρ ∧ (∀ᵐ t ∂ρ, IsTransmissionSequence t) ∧
      ρ.map seqTraceMeasure = entrance)
    {J : ℕ} (a : Fin J → Fin p → ℝ) {h : ℝ} (K : ℕ) {M : ℕ} (hh : 0 < h) (hM : 0 < M) :
    ∃ v : ℝ, FiniteSourceModelValue b E s T q h K M entrance a v := by
  obtain ⟨ρ, hρ, hρs, rfl⟩ := hent
  obtain ⟨Ω, m, 𝓖, Q, tseq, τ, G, hG⟩ :=
    hB1 b hb0 hb E hE1 hE2 s T hs hsT p q hq ρ hρ hρs h K M hh hM
  refine ⟨∫ ω, sampledTransformValue a (G (T - s).toNNReal ω) ∂Q,
    ⟨Ω, m, 𝓖, Q, tseq, τ, G, hG⟩, ?_⟩
  intro Ω' m' 𝓖' Q' tseq' τ' G' hG'
  have hlaw := hB2 b hb0 hb E hE1 hE2 s T hs hsT p q hq _ h K M hh hM Ω m 𝓖 Q tseq τ G hG
    Ω' m' 𝓖' Q' tseq' τ' G' hG' (T - s).toNNReal
  have hmeas :=
    measurable_of_stronglyMeasurable_gram (𝓖.le _) (hG.solution.adapted (T - s).toNNReal)
  have hmeas' :=
    measurable_of_stronglyMeasurable_gram (𝓖'.le _) (hG'.solution.adapted (T - s).toNNReal)
  have hf := measurable_sampledTransformValue (K := K) (M := M) a
  rw [← integral_map hmeas'.aemeasurable hf.aestronglyMeasurable, ← hlaw,
    integral_map hmeas.aemeasurable hf.aestronglyMeasurable]

end BlockBand.SourceProcess.SourceProcessLaw
