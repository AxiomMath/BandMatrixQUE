module

public import BlockBand.SourceProcess.PhysApprox.B3Pins
public import BlockBand.SourceProcess.PhysApprox.Pins
public import BlockBand.SourceProcess.ClosedLimit.PathInt
public import BlockBand.SourceProcess.ComplexCapLimit.Cond
public import BlockBand.SourceProcess.SourceProcessLaw.Entrance
public import BlockBand.SourceProcess.SourceProcessLaw.Extraction
public import BlockBand.SourceProcess.SourcePins.AtomLimit

/-!
# Reductions of `ComplexClosedLimitLaw` to `ComplexCapCondLimit`

* `complexClosedLimitIdentification_of_capCond`: `ComplexCapCondLimit` ⇒
  `ComplexClosedLimitIdentification`. The model off the cap event is the model with the full
  entrance `μ(s)` from `ComplexModelExists`; its capped value is identified by conditioning
  (`ComplexCapLimit.ccondModel`) and uniqueness.
* `complexClosedLimitLawStopped_of_identification`: `ComplexClosedLimitIdentification` ⇒
  `ComplexClosedLimitLawStopped`. With `TargetT8Stopped`, the two are equivalent.
* `complexClosedLimitLaw_of_identification`: `ComplexClosedLimitIdentification` and the
  model-level `ComplexTestedOfFinite` ⇒ `ComplexClosedLimitLaw`.
* Compositions `complexClosedLimitLawStopped_of_capCond`, `complexClosedLimitLaw_of_capCond`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.CapLimit BlockBand.SourceProcess.SourceProcessLaw
open scoped NNReal ENNReal ComplexConjugate

/-!
## The identification from the cap-event limit
-/

/-- **`ComplexClosedLimitIdentification` from the cap-event limit.** -/
theorem complexClosedLimitIdentification_of_capCond (hTL : TransmissionLawContract)
    (hEx : ComplexModelExists) (hU : ComplexFiniteUniqueness) (hC : ComplexCapCondLimit) :
    ComplexClosedLimitIdentification := by
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := id hD
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  refine ((hC b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ).and_eventually hpos).mono
    fun h ⟨hK, hh⟩ => hK.mono fun K hKL => ?_
  intro φ hφ L hφL
  obtain ⟨hz, hnz⟩ := hKL φ hφ L hφL
  obtain ⟨ρ, hρ, hρs, hρe⟩ := entrance_sequence (SourcePins.entranceAtomic_of hTL)
    seqExtraction_holds hb0 hb hE1 hE2 hlim hs
  obtain ⟨Ω₂, m₂, 𝓖₂, Q₂, tseq₂, G₂, K₂, hM₂⟩ := hEx b E np τ m T hD s hs hτ ρ hρ hρs h K hh
  rw [hρe] at hM₂
  refine ⟨Ω₂, m₂, 𝓖₂, Q₂, tseq₂, G₂, K₂, hM₂, ?_⟩
  have hS := measurableSet_capSet K h
  have hQA := ComplexCapLimit.cmeasure_entEvent hM₂ hS
  unfold restrictedModelExpectation
  by_cases h0 : entranceLaw P μ s (capSet K h) = 0
  · rw [setIntegral_measure_zero _ (hQA.trans h0), hz h0]
  obtain ⟨Ω₁, m₁, 𝓖₁, Q₁, tseq₁, G₁, K₁, hM₁, hval⟩ := hnz h0
  have hM₃ := ComplexCapLimit.ccondModel hM₂ hS h0
  have e1 := hU b E np τ m T hD s hs hτ h hh K _ Φ Ω₁ m₁ 𝓖₁ Q₁ tseq₁ G₁ K₁ hM₁ Ω₂ m₂ 𝓖₂ _
    tseq₂ G₂ K₂ hM₃
  unfold modelExpectation at e1 hval
  have hfin : entranceLaw P μ s (capSet K h) ≠ ∞ := by
    rw [← hQA]
    have := hM₂.prob
    exact measure_ne_top _ _
  rw [← hval, e1]
  simp only [ProbabilityTheory.cond, integral_smul_measure, hQA, smul_eq_mul]
  rw [← mul_assoc, ← ENNReal.toReal_mul, ENNReal.mul_inv_cancel h0 hfin, ENNReal.toReal_one,
    one_mul]

/-!
## Filtered models are stopped-tested models up to modification
-/

section Tested

variable {Ω : Type*} {I : Type*} [mΩ : MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 mΩ}
  {Q : Measure Ω}

/-- **Tested increments from a martingale.** A process that is, at every time, a.e. equal to a
`𝓖`-martingale has tested increments for every family of observables that is a.e. equal to a
`𝓖`-adapted family. -/
theorem isTestedMart_of_martingale [IsFiniteMeasure Q] {obs obs₀ : I → ℝ≥0 → Ω → ℂ}
    (hobs₀ : ∀ i u, StronglyMeasurable[𝓖 u] (obs₀ i u)) (hobs : ∀ i u, obs i u =ᵐ[Q] obs₀ i u)
    {N X : ℝ≥0 → Ω → ℂ} (hN : Martingale N 𝓖 Q) (hX : ∀ t, N t =ᵐ[Q] X t) :
    IsTestedMart Q obs X := by
  refine ⟨fun t => (hN.integrable t).congr (hX t), fun s t hst m i u hu φ => ?_⟩
  set f : Ω → ℝ := fun ω => φ (fun l => obs₀ (i l) (u l) ω) with hf_def
  have hcyl : Measurable[𝓖 s] (fun ω l => obs₀ (i l) (u l) ω) := by
    let : MeasurableSpace Ω := 𝓖 s
    exact Measurable.of_eval fun l => ((hobs₀ (i l) (u l)).mono (𝓖.mono (hu l))).measurable
  have hf : StronglyMeasurable[𝓖 s] f := by
    let : MeasurableSpace Ω := 𝓖 s
    exact (φ.continuous.measurable.comp hcyl).stronglyMeasurable
  have hg : Integrable (fun ω => N t ω - N s ω) Q := (hN.integrable t).sub (hN.integrable s)
  have hfg : Integrable (f • fun ω => N t ω - N s ω) Q :=
    hg.bdd_smul ‖φ‖ (hf.mono (𝓖.le s)).aestronglyMeasurable
      (Eventually.of_forall fun ω => φ.norm_coe_le_norm _)
  have hcongr : (fun ω => φ (fun l => obs (i l) (u l) ω) • (X t ω - X s ω)) =ᵐ[Q]
      (f • fun ω => N t ω - N s ω) := by
    have hall : ∀ᵐ ω ∂Q, ∀ l, obs (i l) (u l) ω = obs₀ (i l) (u l) ω :=
      ae_all_iff.2 fun l => hobs (i l) (u l)
    filter_upwards [hall, hX t, hX s] with ω h1 h2 h3
    simp only [Pi.smul_apply', hf_def, ← h2, ← h3]
    congr 2
    exact funext h1
  rw [integral_congr_ae hcongr, ← integral_condExp (𝓖.le s)]
  have h0 : Q[fun ω => N t ω - N s ω | 𝓖 s] =ᵐ[Q] 0 := by
    have hsub := condExp_sub (hN.integrable t) (hN.integrable s) (𝓖 s)
    have hs' : Q[N s | 𝓖 s] = N s :=
      condExp_of_stronglyMeasurable (𝓖.le s) (hN.1 s) (hN.integrable s)
    filter_upwards [hsub, hN.condExp_ae_eq hst] with ω h1 h2
    have h1' : Q[fun ω => N t ω - N s ω | 𝓖 s] ω = Q[N t | 𝓖 s] ω - Q[N s | 𝓖 s] ω := h1
    rw [h1', h2, hs', Pi.zero_apply, sub_self]
  have hpull := condExp_smul_of_aestronglyMeasurable_left hf.aestronglyMeasurable hfg hg
  have h1 : Q[f • fun ω => N t ω - N s ω | 𝓖 s] =ᵐ[Q] 0 := by
    filter_upwards [hpull, h0] with ω h1 h2
    simp only [h1, Pi.smul_apply', h2, Pi.zero_apply, smul_zero]
  rw [integral_congr_ae h1]
  simp

end Tested

section Modification

variable {b E s : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {h : ℝ} {K : ℕ}
  {entrance : Measure (Measure unitInterval)} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {𝓖 : Filtration ℝ≥0 mΩ} {Q : Measure Ω} {tseq : Ω → ℕ → ℝ}
  {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))} {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}

/-- The observables of a filtered complex model are adapted. -/
theorem stronglyMeasurable_complexObs
    (hM : IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖 Q tseq G Kc)
    (i : (Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) ⊕ ℕ ⊕ (Fin np × Fin np)) (u : ℝ≥0) :
    StronglyMeasurable[𝓖 u] (complexObs tseq G Kc i u) := by
  rcases i with e | k | ij
  · exact (continuous_gramEntry e).comp_stronglyMeasurable (hM.solution.adapted u)
  · have ht : Measurable[𝓖 u] tseq := hM.entrance_measurable.mono (𝓖.mono zero_le) le_rfl
    exact (Complex.measurable_ofReal.comp ((measurable_pi_apply k).comp ht)).stronglyMeasurable
  · exact ((continuous_apply ij.2).comp (continuous_apply ij.1)).comp_stronglyMeasurable
      (hM.complex.adapted u)

/-- **A filtered complex model is, up to a modification on a null set, a stopped-tested
model.** The modification replaces `(G, 𝒦)` by the birth jumps on a measurable null set
containing every `ω` at which `G − J` or `𝒦 − J_𝒦` is not continuous. -/
theorem exists_stoppedTested_of_finite
    (hM : IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖 Q tseq G Kc) :
    ∃ (G' : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
      (Kc' : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ),
      IsStoppedTestedComplexModel b E s τ m h K entrance Q tseq G' Kc' ∧
      ∀ t, G' t =ᵐ[Q] G t ∧ Kc' t =ᵐ[Q] Kc t := by
  classical
  have hP := hM.prob
  set B : Set Ω := {ω | ¬ (Continuous (fun u => G u ω - gramJ b s τ m u) ∧
    Continuous (fun u => Kc u ω - kJ E s τ m u))} with hB_def
  have hB0 : Q B = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hM.solution.continuous, hM.complex.continuous] with ω h1 h2
    exact fun hω => hω ⟨h1, h2⟩
  set Nul := toMeasurable Q B with hNul
  have hNm : MeasurableSet Nul := measurableSet_toMeasurable Q B
  have hN0 : Q Nul = 0 := by rw [hNul, measure_toMeasurable, hB0]
  have hgood : ∀ᵐ ω ∂Q, ω ∉ Nul := measure_eq_zero_iff_ae_notMem.1 hN0
  set G' : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)) :=
    fun u => Nul.piecewise (fun _ => gramJ b s τ m u) (G u) with hG'_def
  set Kc' : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ :=
    fun u => Nul.piecewise (fun _ => kJ E s τ m u) (Kc u) with hK'_def
  have hG : ∀ ω, ω ∉ Nul → ∀ u, G' u ω = G u ω := fun ω hω u => by
    simp only [hG'_def, Set.piecewise, hω, ↓reduceIte]
  have hK : ∀ ω, ω ∉ Nul → ∀ u, Kc' u ω = Kc u ω := fun ω hω u => by
    simp only [hK'_def, Set.piecewise, hω, ↓reduceIte]
  have hobs : ∀ i u, complexObs tseq G' Kc' i u =ᵐ[Q] complexObs tseq G Kc i u := by
    intro i u
    filter_upwards [hgood] with ω hω
    rcases i with e | k | ij
    · simp only [complexObs, hG ω hω]
    · rfl
    · simp only [complexObs, hK ω hω]
  have hobs₀ := stronglyMeasurable_complexObs hM
  refine ⟨G', Kc', ?_, fun t => ⟨?_, ?_⟩⟩
  rotate_left
  · filter_upwards [hgood] with ω hω using hG ω hω t
  · filter_upwards [hgood] with ω hω using hK ω hω t
  refine
    { prob := hP
      entrance_measurable := hM.entrance_measurable.mono (𝓖.le 0) le_rfl
      gram_measurable := fun u => StronglyMeasurable.piecewise hNm stronglyMeasurable_const
        ((hM.solution.adapted u).mono (𝓖.le u))
      k_measurable := fun u => StronglyMeasurable.piecewise hNm stronglyMeasurable_const
        ((hM.complex.adapted u).mono (𝓖.le u))
      entrance_sequence := hM.entrance_sequence
      entrance_law := hM.entrance_law
      initial := ?_
      continuous := ?_
      k_continuous := ?_
      feasible := ?_
      drift := ?_
      bracket := ?_
      martingale := ?_
      holomorphic := ?_
      antiholomorphic := ?_
      crossM := ?_
      crossB := ?_ }
  · filter_upwards [hM.initial, hgood] with ω h1 hω
    rw [hG ω hω, hK ω hω]
    exact h1
  · intro ω
    by_cases hω : ω ∈ Nul
    · simp only [hG'_def, Set.piecewise, hω, ↓reduceIte, sub_self]
      exact continuous_const
    · have hc : ω ∉ B := fun h' => hω (subset_toMeasurable Q B h')
      simp only [hB_def, Set.mem_ofPred_eq, not_not] at hc
      simp only [hG ω hω]
      exact hc.1
  · intro ω
    by_cases hω : ω ∈ Nul
    · simp only [hK'_def, Set.piecewise, hω, ↓reduceIte, sub_self]
      exact continuous_const
    · have hc : ω ∉ B := fun h' => hω (subset_toMeasurable Q B h')
      simp only [hB_def, Set.mem_ofPred_eq, not_not] at hc
      simp only [hK ω hω]
      exact hc.2
  · filter_upwards [hM.solution.feasible, hgood] with ω h1 hω t
    rw [hG ω hω]
    exact h1 t
  · intro L e
    obtain ⟨N, hN, hNe⟩ := hM.solution.drift L e
    refine isTestedMart_of_martingale hobs₀ hobs hN fun t => (hNe t).trans ?_
    filter_upwards [hgood] with ω hω
    simp only [stoppedProcess, gramTraceStop, bornCompensated, gramJ, hG ω hω]
  · intro L e e'
    obtain ⟨N, hN, hNe⟩ := hM.solution.bracket L e e'
    refine isTestedMart_of_martingale hobs₀ hobs hN fun t => (hNe t).trans ?_
    filter_upwards [hgood] with ω hω
    simp only [stoppedProcess, gramTraceStop, bornCompensated, gramJ, hG ω hω]
  · intro L i j
    obtain ⟨N, hN, hNe⟩ := hM.complex.martingale L i j
    refine isTestedMart_of_martingale hobs₀ hobs hN fun t => (hNe t).trans ?_
    filter_upwards [hgood] with ω hω
    simp only [stoppedProcess, gramTraceStop, kCompensated, kJ, hG ω hω, hK ω hω]
  · intro L i j k l
    obtain ⟨N, hN, hNe⟩ := hM.complex.holomorphic L i j k l
    refine isTestedMart_of_martingale hobs₀ hobs hN fun t => (hNe t).trans ?_
    filter_upwards [hgood] with ω hω
    simp only [stoppedProcess, gramTraceStop, kCompensated, kJ, hG ω hω, hK ω hω]
  · intro L i j k l
    obtain ⟨N, hN, hNe⟩ := hM.complex.antiholomorphic L i j k l
    refine isTestedMart_of_martingale hobs₀ hobs hN fun t => (hNe t).trans ?_
    filter_upwards [hgood] with ω hω
    simp only [stoppedProcess, gramTraceStop, kCompensated, kJ, hG ω hω, hK ω hω]
  · intro L i j k l
    obtain ⟨N, hN, hNe⟩ := hM.complex.crossM L i j k l
    refine isTestedMart_of_martingale hobs₀ hobs hN fun t => (hNe t).trans ?_
    filter_upwards [hgood] with ω hω
    simp only [stoppedProcess, gramTraceStop, kCompensated, kJ, bornCompensated, gramJ,
      hG ω hω, hK ω hω]
  · intro L i j k l
    obtain ⟨N, hN, hNe⟩ := hM.complex.crossB L i j k l
    refine isTestedMart_of_martingale hobs₀ hobs hN fun t => (hNe t).trans ?_
    filter_upwards [hgood] with ω hω
    simp only [stoppedProcess, gramTraceStop, kCompensated, kJ, bornCompensated, gramJ,
      hG ω hω, hK ω hω]

/-- The restricted model value is unchanged by a modification at the final time. -/
theorem restrictedModelExpectation_congr {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
    {tseq : Ω → ℕ → ℝ} {G G' : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))}
    {Kc Kc' : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ} (s T : ℝ)
    (hGK : ∀ t, G' t =ᵐ[Q] G t ∧ Kc' t =ᵐ[Q] Kc t)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) :
    restrictedModelExpectation K h s T Q tseq G' Kc' Φ =
      restrictedModelExpectation K h s T Q tseq G Kc Φ := by
  unfold restrictedModelExpectation
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [(hGK (T - s).toNNReal).1, (hGK (T - s).toNNReal).2] with ω h1 h2
  rw [h1, h2]

end Modification

/-!
## The stopped limit law from the identification
-/

/-- **`ComplexClosedLimitLawStopped` from `ComplexClosedLimitIdentification`** (the modification
at the limit model). -/
theorem complexClosedLimitLawStopped_of_identification (hI : ComplexClosedLimitIdentification) :
    ComplexClosedLimitLawStopped := by
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ
  refine (hI b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ).mono fun h hK => hK.mono fun K hKL => ?_
  intro φ hφ L hφL
  obtain ⟨Ω', m', 𝓖, Q, tseq, G, Kc, hM, hval⟩ := hKL φ hφ L hφL
  obtain ⟨G', Kc', hT, hGK⟩ := exists_stoppedTested_of_finite hM
  exact ⟨Ω', m', Q, tseq, G', Kc', hT, (restrictedModelExpectation_congr s T hGK Φ).trans hval⟩

/-- **`ComplexClosedLimitLaw` from `ComplexClosedLimitIdentification` and the model-level
`ComplexTestedOfFinite`.** -/
theorem complexClosedLimitLaw_of_identification (hI : ComplexClosedLimitIdentification)
    (hT : ComplexTestedOfFinite) : ComplexClosedLimitLaw := by
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  refine ((hI b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ).and_eventually hpos).mono
    fun h ⟨hK, hh⟩ => hK.mono fun K hKL => ?_
  intro φ hφ L hφL
  obtain ⟨Ω', m', 𝓖, Q, tseq, G, Kc, hM, hval⟩ := hKL φ hφ L hφL
  obtain ⟨G', Kc', hTM, hGK⟩ :=
    hT b E np τ m T hD s hs hτ h hh K _ Ω' m' 𝓖 Q tseq G Kc hM
  exact ⟨Ω', m', Q, tseq, G', Kc', hTM, (restrictedModelExpectation_congr s T hGK Φ).trans hval⟩

/-!
## Compositions
-/

/-- **`ComplexClosedLimitLawStopped` from the cap-event limit.** -/
theorem complexClosedLimitLawStopped_of_capCond (hTL : TransmissionLawContract)
    (hEx : ComplexModelExists) (hU : ComplexFiniteUniqueness) (hC : ComplexCapCondLimit) :
    ComplexClosedLimitLawStopped :=
  complexClosedLimitLawStopped_of_identification
    (complexClosedLimitIdentification_of_capCond hTL hEx hU hC)

/-- **`ComplexClosedLimitLaw` from the cap-event limit and the model-level
`ComplexTestedOfFinite`.** -/
theorem complexClosedLimitLaw_of_capCond (hTL : TransmissionLawContract)
    (hEx : ComplexModelExists) (hU : ComplexFiniteUniqueness) (hC : ComplexCapCondLimit)
    (hT : ComplexTestedOfFinite) : ComplexClosedLimitLaw :=
  complexClosedLimitLaw_of_identification
    (complexClosedLimitIdentification_of_capCond hTL hEx hU hC) hT

end BlockBand.SourceProcess.PhysApprox.B3
