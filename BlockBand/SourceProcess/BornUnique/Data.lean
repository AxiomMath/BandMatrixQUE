module

public import BlockBand.SourceProcess.BornUnique.Pin
public import BlockBand.SourceProcess.SourceProcessLaw.Extraction
public import BlockBand.SourceProcess.SourceProcessLaw.ModelValue

/-!
# The law of the data of a finite source model

The joint law of the birth times `tseq` and the initial data `τ` of every finite source model is
`modelDataLaw`, which depends only on the model parameters. Hence the joint law of the shifted
birth times and of the initial Gram state `G₀` is also fixed by the parameters.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornUnique

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

section Meas

variable {ι c : Type} [Fintype ι] [Fintype c]

omit [Fintype c] in
theorem continuous_gramPair (P : Matrix ι ι ℂ) :
    Continuous fun V : Matrix ι c ℂ => gramPair P V := by
  unfold gramPair BlockBand.SourceProcess.sourceGram BlockBand.SourceProcess.nearGram
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_id.matrix_conjTranspose).matrix_mul continuous_id
  · exact ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
      continuous_id

theorem measurable_gramPair (P : Matrix ι ι ℂ) :
    Measurable fun V : Matrix ι c ℂ => gramPair P V := by
  have : BorelSpace (Matrix ι c ℂ) := inferInstanceAs (BorelSpace (ι → c → ℂ))
  have : BorelSpace (GramState c) := gramState_borel
  exact (continuous_gramPair P).measurable

end Meas

theorem measurable_modeVector_apply (σ x : Fin 2) :
    Measurable fun r : ℝ => modeVector r σ x := by
  unfold modeVector
  split_ifs
  · fin_cases x <;> simp <;> fun_prop
  · fin_cases x <;> simp <;> fun_prop

theorem measurable_initialFrame (K : ℕ) (π : Type*) (h : ℝ) :
    Measurable fun t : ℕ → ℝ => initialFrame K π t h := by
  refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun col => ?_
  rcases col with ⟨k, σ⟩ | _
  · simp only [initialFrame]
    by_cases hx : x.1 = k
    · simp only [hx, true_and]
      refine Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply _)) ?_
        measurable_const
      exact (Complex.measurable_ofReal.comp ((measurable_pi_apply _).pow_const _)).mul
        ((measurable_modeVector_apply σ x.2).comp (measurable_pi_apply _))
    · simp [hx]
  · simp [initialFrame]

theorem measurable_initialGram (K : ℕ) (π : Type) [Fintype π] (h : ℝ) :
    Measurable fun t : ℕ → ℝ => initialGram K π t h :=
  (measurable_gramPair _).comp (measurable_initialFrame K π h)

variable {b E s T : ℝ} {p : ℕ} {q : Fin p → ℝ → ℝ} {h : ℝ} {K M : ℕ}
  {entrance : Measure (Measure unitInterval)} {Ω : Type} {m : MeasurableSpace Ω}
  {𝓖 : Filtration ℝ≥0 m} {Q : Measure Ω} {tseq : Ω → ℕ → ℝ} {τ : Ω → Fin p × Fin M → ℝ}
  {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin p × Fin M))}

/-- The law of `(tseq, τ)` of every finite source model. -/
def modelDataLaw (s T : ℝ) {p : ℕ} (q : Fin p → ℝ → ℝ) (M : ℕ)
    (entrance : Measure (Measure unitInterval)) : Measure ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) :=
  (entrance.map seqExtract).prod (Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1))

/-- The shifted birth times and the initial Gram state as a function of the data. -/
def initialData (s h : ℝ) (K : ℕ) (π : Type) [Fintype π] (x : (ℕ → ℝ) × (π → ℝ)) :
    (π → ℝ) × GramState (SrcCol K π) :=
  (fun i => x.2 i - s, initialGram K π x.1 h)

theorem measurable_initialData (s h : ℝ) (K : ℕ) (π : Type) [Fintype π] :
    Measurable (initialData s h K π) :=
  (measurable_pi_iff.2 fun i => ((measurable_pi_apply i).comp measurable_snd).sub_const s).prodMk
    ((measurable_initialGram K π h).comp measurable_fst)

theorem model_measurable_tseq
    (hM : IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G) : Measurable tseq :=
  hM.entrance_measurable.mono (𝓖.le 0) le_rfl

theorem model_measurable_τ
    (hM : IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G) : Measurable τ :=
  hM.births_measurable.mono (𝓖.le 0) le_rfl

/-- **The law of `tseq`** is `entrance.map seqExtract`. -/
theorem model_map_tseq
    (hM : IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G) :
    Q.map tseq = entrance.map seqExtract := by
  have ht := (model_measurable_tseq hM)
  have hae : tseq =ᵐ[Q] seqExtract ∘ (fun ω => seqTraceMeasure (tseq ω)) := by
    filter_upwards [hM.entrance_sequence] with ω hω
    exact (seqExtract_seqTraceMeasure hω).symm
  rw [Measure.map_congr hae, ← Measure.map_map (g := seqExtract)
    (f := fun ω => seqTraceMeasure (tseq ω)) measurable_seqExtract
    (measurable_seqTraceMeasure.comp ht), hM.entrance_law]

/-- **The joint law of `(tseq, τ)`** is `modelDataLaw`. -/
theorem model_map_data
    (hM : IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G) :
    Q.map (fun ω => (tseq ω, τ ω)) = modelDataLaw s T q M entrance := by
  have := hM.prob
  rw [(indepFun_iff_map_prod_eq_prod_map_map (model_measurable_tseq hM).aemeasurable
    (model_measurable_τ hM).aemeasurable).1 hM.independent, (model_map_tseq hM), hM.births_law]
  rfl

/-- **The joint law of the shifted birth times and `G₀`** is fixed by the parameters. -/
theorem model_map_initial
    (hM : IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G) :
    Q.map (fun ω => ((fun i => τ ω i - s), G 0 ω)) =
      (modelDataLaw s T q M entrance).map (initialData s h K (Fin p × Fin M)) := by
  have hae : (fun ω => ((fun i => τ ω i - s), G 0 ω)) =ᵐ[Q]
      initialData s h K (Fin p × Fin M) ∘ fun ω => (tseq ω, τ ω) := by
    filter_upwards [hM.initial] with ω hω
    simp only [Function.comp, initialData, hω]
  rw [Measure.map_congr hae, ← Measure.map_map (measurable_initialData s h K _)
    ((model_measurable_tseq hM).prodMk (model_measurable_τ hM)), (model_map_data hM)]

end BlockBand.SourceProcess.BornUnique
