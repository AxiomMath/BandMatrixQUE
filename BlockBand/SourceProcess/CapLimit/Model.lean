module

public import BlockBand.SourceProcess.CapLimit.Cond

/-!
# `CapRestriction`: a cap-`K'` model restricts to a cap-`K` model on `{t_K ≤ h²}`

`capSet K h = {ν | seqExtract ν K ≤ h²}` is the entrance event `{t_K ≤ h²}` (by
`seqExtract_seqTraceMeasure`, on transmission sequences). For `K ≤ K'` and a cap-`K'` model with
`entrance (capSet K h) ≠ 0`, conditioning on `A = {seqTraceMeasure tseq ∈ capSet K h}` and
restricting the Gram state to the first `K` modes and the probes gives a cap-`K` model with
entrance `entrance[|capSet K h]` (`capRestrict`, and the Prop `CapRestriction` with
`capRestriction_holds`). On `A` the modes `k ≥ K` have `t_k ≤ h²` (antitone), so their initial
columns vanish; they stay zero (`ae_diag_eq_zero_on`); the restriction is then a born solution
(`isBornGramSolution_restrict`). `condModel` is the same-cap case without restriction.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapLimit

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

/-- The entrance event `{t_K ≤ h²}`. -/
def capSet (K : ℕ) (h : ℝ) : Set (Measure unitInterval) := {ν | seqExtract ν K ≤ h ^ 2}

theorem measurableSet_capSet (K : ℕ) (h : ℝ) : MeasurableSet (capSet K h) :=
  measurableSet_le ((measurable_pi_apply K).comp measurable_seqExtract) measurable_const

variable {b E s T : ℝ} {p : ℕ} {q : Fin p → ℝ → ℝ} {h : ℝ} {K K' M : ℕ}
  {entrance : Measure (Measure unitInterval)} {Ω : Type*} [MeasurableSpace Ω]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Q : Measure Ω}
  {tseq : Ω → ℕ → ℝ} {τ : Ω → Fin p × Fin M → ℝ}

/-- **Same cap**: conditioning a model on an entrance event gives a model. -/
theorem condModel {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin p × Fin M))}
    (hM : IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G)
    {S : Set (Measure unitInterval)} (hS : MeasurableSet S) (hS0 : entrance S ≠ 0) :
    IsFiniteSourceModel b E s T q h K M (entrance[|S]) 𝓖 (Q[|entEvent tseq S]) tseq τ G := by
  have := hM.prob
  refine model_cond_of hM hS hS0 hM.initial (isBornGramSolution_cond hM.solution
    (measurableSet_entEvent hM hS) ?_)
  rwa [measure_entEvent hM hS]

/-- On `A`, the modes `k ≥ K` of a cap-`K'` model stay zero at all times. -/
theorem ae_gsupp_capEmb (hK : K ≤ K') {G : ℝ≥0 → Ω → GramState (SrcCol K' (Fin p × Fin M))}
    (hM : IsFiniteSourceModel b E s T q h K' M entrance 𝓖 Q tseq τ G) :
    ∀ᵐ ω ∂Q, ω ∈ entEvent tseq (capSet K h) →
      ∀ t, GSupp (capEmb hK (Fin p × Fin M)) (G t ω) := by
  have := hM.prob
  have hA := measurableSet_entEvent hM (measurableSet_capSet K h)
  have hdiag : ∀ y : {y // y ∉ Set.range (capEmb hK (Fin p × Fin M))},
      ∀ᵐ ω ∂Q, ω ∈ entEvent tseq (capSet K h) → ∀ t, (G t ω).1 y y = 0 := by
    rintro ⟨y, hy⟩
    obtain ⟨k, σ, rfl, hk⟩ := notMem_range_capEmb hy
    refine ae_diag_eq_zero_on hM.solution (fun t ω => birthJump_inl_diag _ _ _ _)
      (fun ω => ⟨_, fun t => re_trace_birthJump_le _ _ _⟩) hA ?_
    filter_upwards [hM.initial, hM.entrance_sequence] with ω hi hseq hωA
    rw [hi]
    refine initialGram_diag_eq_zero k σ ((hseq.1 hk).trans ?_)
    have h1 : seqExtract (seqTraceMeasure (tseq ω)) K ≤ h ^ 2 := hωA
    rwa [seqExtract_seqTraceMeasure hseq] at h1
  filter_upwards [ae_all_iff.2 hdiag, hM.solution.feasible] with ω hω hf hωA t
  exact gsupp_of_feasible (hf t) fun y hy => by rw [hω ⟨y, hy⟩ hωA t, Complex.zero_re]

/-- **`CapRestriction`**: the cap-`K'` model, conditioned on `{t_K ≤ h²}` and restricted
to the first `K` modes, is a cap-`K` model with the conditioned entrance. -/
theorem capRestrict (hK : K ≤ K') {G : ℝ≥0 → Ω → GramState (SrcCol K' (Fin p × Fin M))}
    (hM : IsFiniteSourceModel b E s T q h K' M entrance 𝓖 Q tseq τ G)
    (hS0 : entrance (capSet K h) ≠ 0) :
    IsFiniteSourceModel b E s T q h K M (entrance[|capSet K h]) 𝓖
      (Q[|entEvent tseq (capSet K h)]) tseq τ (pRestrict (capEmb hK (Fin p × Fin M)) G) := by
  have := hM.prob
  have hS := measurableSet_capSet K h
  have hQA : Q (entEvent tseq (capSet K h)) ≠ 0 := by rwa [measure_entEvent hM hS]
  have hsol := isBornGramSolution_restrict (capEmb_injective hK _) sep_srcSignature hM.solution
    (measurableSet_entEvent hM hS) hQA (ae_gsupp_capEmb hK hM)
  rw [srcSignature_submatrix] at hsol
  have hJ : pRestrict (capEmb hK (Fin p × Fin M)) (fun (t : ℝ≥0) ω => birthJump (K := K')
      (fun i => τ ω i - s) (fun i => dStar b * sourceMass s T (q i.1) / M) (t : ℝ)) =
      fun (t : ℝ≥0) ω => birthJump (K := K) (fun i => τ ω i - s)
        (fun i => dStar b * sourceMass s T (q i.1) / M) (t : ℝ) := by
    funext t ω
    exact gRestrict_birthJump _ _ _
  rw [hJ] at hsol
  refine model_cond_of hM hS hS0 ?_ hsol
  filter_upwards [hM.initial] with ω hi
  simp only [pRestrict, hi, gRestrict_initialGram]

/-- **`CapRestriction`** as a Prop over all model data. -/
def CapRestriction : Prop :=
  ∀ (b E s T : ℝ) (p : ℕ) (q : Fin p → ℝ → ℝ) (h : ℝ) (K K' M : ℕ) (hK : K ≤ K')
    (entrance : Measure (Measure unitInterval)) (Ω : Type) (m : MeasurableSpace Ω)
    (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω) (tseq : Ω → ℕ → ℝ) (τ : Ω → Fin p × Fin M → ℝ)
    (G : ℝ≥0 → Ω → GramState (SrcCol K' (Fin p × Fin M))),
    IsFiniteSourceModel b E s T q h K' M entrance 𝓖 Q tseq τ G → entrance (capSet K h) ≠ 0 →
    IsFiniteSourceModel b E s T q h K M (entrance[|capSet K h]) 𝓖
      (Q[|entEvent tseq (capSet K h)]) tseq τ (pRestrict (capEmb hK (Fin p × Fin M)) G)

theorem capRestriction_holds : CapRestriction :=
  fun _ _ _ _ _ _ _ _ _ _ hK _ _ _ _ _ _ _ _ hM hS0 => capRestrict hK hM hS0

end BlockBand.SourceProcess.CapLimit
