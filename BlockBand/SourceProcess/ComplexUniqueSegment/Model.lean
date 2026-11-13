module

public import BlockBand.SourceProcess.ComplexUniqueSegment.Extract
public import BlockBand.SourceProcess.ComplexUniqueSegment.Laws

/-!
# The joint state of a complex finite model

* `model_measurable_joint`: `(G(t), 𝒦(t))` is measurable (from `adapted`);
* `model_continuous_joint`: `(G, 𝒦) - (J, J_𝒦)` has a.s. continuous paths (the two
  `continuous` fields);
* `model_map_zero` (time 0): the law of
  `(G(0), 𝒦(0))` is `entrance.map (ν ↦ (initialGram (extractSeq ν), 0))`, i.e. fixed by the
  entrance law (`initial`, `entrance_law`, `entrance_sequence`);
* `continuous_modelSourceData`: the final source data are continuous in the joint state.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUniqueSegment

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.ComplexSplit
open scoped NNReal

attribute [local instance] matrix_pseudoMetrizable matrix_secondCountable jointState_borel
  gramState_borel'

/-- The joint state `(G, 𝒦)` of a complex finite model with `np` probes and cap `K`. -/
abbrev JointState (K np : ℕ) := GramState (SrcCol K (Fin np)) × Matrix (Fin np) (Fin np) ℂ

/-- The deterministic joint birth jump `(J(t), J_𝒦(t))` of the complex finite model. -/
def jointJump (b E s : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (K : ℕ) (t : ℝ≥0) : JointState K np :=
  (birthJump (fun j => τ j - s) (fun j => dStar b * m j) (t : ℝ),
    kBirthJump E (fun j => τ j - s) m (t : ℝ))

theorem continuous_probeBlock' {K : ℕ} {π : Type} :
    Continuous (probeBlock : Matrix (SrcCol K π) (SrcCol K π) ℂ → Matrix π π ℂ) :=
  continuous_matrix fun i j => continuous_id.matrix_elem (Sum.inr i) (Sum.inr j)

theorem continuous_modelSourceData {K np : ℕ}
    (D : Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ) :
    Continuous fun y : JointState K np => modelSourceData D y.2 y.1 := by
  refine continuous_pi fun r => ?_
  fin_cases r
  · exact continuous_snd
  · exact continuous_probeBlock'.comp (continuous_fst.comp continuous_fst)
  · exact continuous_probeBlock'.comp (continuous_snd.comp continuous_fst)
  · exact continuous_probeBlock'.comp
      ((((continuous_fst.comp continuous_fst).matrix_mul continuous_const).matrix_mul
        (continuous_fst.comp continuous_fst)))

section Model

variable {b E s : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {hc : ℝ} {K : ℕ}
  {entrance : Measure (Measure unitInterval)} {Ω : Type} {mΩ : MeasurableSpace Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {Q : Measure Ω} {tseq : Ω → ℕ → ℝ}
  {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))} {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}

theorem model_measurable_joint
    (hM : IsFiniteComplexSourceModel b E s τ m hc K entrance 𝓖 Q tseq G Kc) (t : ℝ≥0) :
    Measurable fun ω => (G t ω, Kc t ω) := by
  have : TopologicalSpace.PseudoMetrizableSpace (GramState (SrcCol K (Fin np))) :=
    gramState_pseudoMetrizable
  exact (((hM.solution.adapted t).measurable).mono (𝓖.le t) le_rfl).prodMk
    (((hM.complex.adapted t).measurable).mono (𝓖.le t) le_rfl)

theorem model_continuous_joint
    (hM : IsFiniteComplexSourceModel b E s τ m hc K entrance 𝓖 Q tseq G Kc) :
    ∀ᵐ ω ∂Q, Continuous fun t => (G t ω, Kc t ω) - jointJump b E s τ m K t := by
  filter_upwards [hM.solution.continuous, hM.complex.continuous] with ω h1 h2
  simp only [jointJump, Prod.mk_sub_mk]
  exact h1.prodMk h2

/-- **Time 0.** The joint law of `(G(0), 𝒦(0))` is fixed by the entrance law. -/
theorem model_map_zero
    (hM : IsFiniteComplexSourceModel b E s τ m hc K entrance 𝓖 Q tseq G Kc) :
    Q.map (fun ω => (G 0 ω, Kc 0 ω)) =
      entrance.map (fun ν => (initialGram K (Fin np) (extractSeq ν) hc,
        (0 : Matrix (Fin np) (Fin np) ℂ))) := by
  have ht : Measurable tseq := hM.entrance_measurable.mono (𝓖.le 0) le_rfl
  have hF : Measurable fun ν : Measure unitInterval =>
      (initialGram K (Fin np) (extractSeq ν) hc, (0 : Matrix (Fin np) (Fin np) ℂ)) :=
    ((measurable_initialGram' K (Fin np) hc).comp measurable_extractSeq).prodMk measurable_const
  have hae : (fun ω => (G 0 ω, Kc 0 ω)) =ᵐ[Q]
      (fun ν : Measure unitInterval =>
        (initialGram K (Fin np) (extractSeq ν) hc, (0 : Matrix (Fin np) (Fin np) ℂ))) ∘
        (seqTraceMeasure ∘ tseq) := by
    filter_upwards [hM.initial, hM.entrance_sequence] with ω h1 h2
    simp only [Function.comp, extractSeq_seqTraceMeasure h2, h1.1, h1.2]
  rw [Measure.map_congr hae, ← Measure.map_map hF (measurable_seqTraceMeasure'.comp ht)]
  exact congrArg _ hM.entrance_law

end Model

end BlockBand.SourceProcess.ComplexUniqueSegment
