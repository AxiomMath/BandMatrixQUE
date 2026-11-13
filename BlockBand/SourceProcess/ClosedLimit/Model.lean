module

public import BlockBand.SourceProcess.ClosedLimit.Born
public import BlockBand.SourceProcess.BornUnique.Reduce

/-!
# A finite source model from tested increments (limit-passage tool, part 2)

On a probability space carrying an entrance sequence `tseq`, birth locations `τ` and a Gram
process `G`, take as observables (`modelObs`) the Gram entries of `G`, the coordinates of `tseq`
and the coordinates of `τ`, with their raw natural filtration `𝓖 = pastFiltration`. If the data
have the laws of `IsFiniteSourceModel`, `G − J` is continuous for every `ω`, and the compensated
coordinates and products have tested martingale increments for these observables, then
`(𝓖, Q, tseq, τ, G)` is a finite source model (`isFiniteSourceModel_of_tested`).

This is the form in which a weak limit of the closed physical coordinates is identified with the
cap-`K` model: the limit is built on some probability space, and only tested
identities for bounded continuous cylinder tests pass to the limit.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedLimit

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess BlockBand.SourceProcess.BornUnique
open scoped NNReal ENNReal

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- The Gram state with prescribed coordinates. -/
def gramOfEntries (x : Fin 2 × c × c → ℂ) : GramState c :=
  (Matrix.of fun a b => x (0, a, b), Matrix.of fun a b => x (1, a, b))

omit [Fintype c] [DecidableEq c] in
theorem continuous_gramOfEntries : Continuous (gramOfEntries (c := c)) := by
  unfold gramOfEntries
  refine Continuous.prodMk ?_ ?_ <;>
    exact continuous_pi fun a => continuous_pi fun b => continuous_apply _

omit [Fintype c] [DecidableEq c] in
theorem gramOfEntries_gramEntry (G : GramState c) : gramOfEntries (fun e => gramEntry e G) = G := by
  ext a b <;> simp [gramOfEntries, gramEntry]

/-- Observables of a model: Gram entries, entrance coordinates, birth locations. -/
def modelObs {Ω π : Type*} (tseq : Ω → ℕ → ℝ) (τ : Ω → π → ℝ) (G : ℝ≥0 → Ω → GramState c) :
    (Fin 2 × c × c) ⊕ ℕ ⊕ π → ℝ≥0 → Ω → ℂ
  | Sum.inl e => fun u ω => gramEntry e (G u ω)
  | Sum.inr (Sum.inl k) => fun _ ω => (tseq ω k : ℂ)
  | Sum.inr (Sum.inr i) => fun _ ω => (τ ω i : ℂ)

variable {Ω π : Type*} [MeasurableSpace Ω] {tseq : Ω → ℕ → ℝ} {τ : Ω → π → ℝ}
  {G : ℝ≥0 → Ω → GramState c}

omit [Fintype c] [DecidableEq c] in
theorem measurable_modelObs (htm : Measurable tseq) (hτm : Measurable τ)
    (hG : ∀ u, StronglyMeasurable (G u)) : ∀ i u, Measurable (modelObs tseq τ G i u)
  | Sum.inl e, u => ((continuous_gramEntry e).comp_stronglyMeasurable (hG u)).measurable
  | Sum.inr (Sum.inl k), _ => Complex.measurable_ofReal.comp (measurable_pi_iff.1 htm k)
  | Sum.inr (Sum.inr i), _ => Complex.measurable_ofReal.comp (measurable_pi_iff.1 hτm i)

omit [Fintype c] [DecidableEq c] [MeasurableSpace Ω] in
theorem stronglyMeasurable_G_past [Fintype c] (u : ℝ≥0) :
    StronglyMeasurable[pastSigma (modelObs tseq τ G) u] (G u) := by
  set m := pastSigma (modelObs tseq τ G) u
  have hv : Measurable[m] fun ω => fun e : Fin 2 × c × c => gramEntry e (G u ω) := by
    let _ := m
    exact Measurable.of_eval fun e => measurable_obs_past (modelObs tseq τ G) (Sum.inl e) le_rfl
  have h := continuous_gramOfEntries.comp_stronglyMeasurable hv.stronglyMeasurable
  have e : (fun ω => gramOfEntries fun e : Fin 2 × c × c => gramEntry e (G u ω)) = G u :=
    funext fun ω => gramOfEntries_gramEntry _
  rwa [e] at h

omit [Fintype c] [DecidableEq c] [MeasurableSpace Ω] in
theorem measurable_tseq_past :
    Measurable[pastSigma (modelObs tseq τ G) 0] tseq := by
  let _ := pastSigma (modelObs tseq τ G) 0
  refine Measurable.of_eval fun k => ?_
  have e : (fun ω => tseq ω k) = fun ω => (modelObs tseq τ G (Sum.inr (Sum.inl k)) 0 ω).re :=
    funext fun ω => by simp [modelObs]
  rw [e]
  exact Complex.measurable_re.comp
    (measurable_obs_past (modelObs tseq τ G) (Sum.inr (Sum.inl k)) le_rfl)

omit [Fintype c] [DecidableEq c] [MeasurableSpace Ω] in
theorem measurable_τ_past :
    Measurable[pastSigma (modelObs tseq τ G) 0] τ := by
  let _ := pastSigma (modelObs tseq τ G) 0
  refine Measurable.of_eval fun i => ?_
  have e : (fun ω => τ ω i) = fun ω => (modelObs tseq τ G (Sum.inr (Sum.inr i)) 0 ω).re :=
    funext fun ω => by simp [modelObs]
  rw [e]
  exact Complex.measurable_re.comp
    (measurable_obs_past (modelObs tseq τ G) (Sum.inr (Sum.inr i)) le_rfl)

theorem re_trace_probeJump {K : ℕ} {π : Type*} [Fintype π] [DecidableEq π] (v : π → ℝ) (i : π) :
    (((probeJump (K := K) v i).1).trace).re = v i := by
  simp [probeJump]

/-- **A finite source model from tested increments.** The observables are the Gram entries, the
entrance coordinates and the birth locations; `𝓖` is their raw natural filtration. -/
theorem isFiniteSourceModel_of_tested {b E s T h : ℝ} {p K M : ℕ} {q : Fin p → ℝ → ℝ}
    {entrance : Measure (Measure unitInterval)} {Q : Measure Ω} [IsProbabilityMeasure Q]
    {tseq : Ω → ℕ → ℝ} {τ : Ω → Fin p × Fin M → ℝ}
    {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin p × Fin M))}
    (htm : Measurable tseq) (hτm : Measurable τ) (hG : ∀ u, StronglyMeasurable (G u))
    (hv : ∀ i : Fin p × Fin M, 0 ≤ dStar b * sourceMass s T (q i.1) / M)
    (hseq : ∀ᵐ ω ∂Q, IsTransmissionSequence (tseq ω))
    (hlaw : Q.map (fun ω => seqTraceMeasure (tseq ω)) = entrance)
    (hbl : Q.map τ = Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1))
    (hind : IndepFun tseq τ Q)
    (hinit : ∀ᵐ ω ∂Q, G 0 ω = initialGram K (Fin p × Fin M) (tseq ω) h)
    (hc : ∀ ω, Continuous fun u : ℝ≥0 => G u ω - birthJump (fun i => τ ω i - s)
      (fun i => dStar b * sourceMass s T (q i.1) / M) (u : ℝ))
    (hfeas : ∀ᵐ ω ∂Q, ∀ t, GramFeasible (srcSignature K (Fin p × Fin M)) (G t ω))
    (hdr : ∀ e, IsTestedMart Q (modelObs tseq τ G) (bornCompensated (transportD0 b E)
      (srcSignature K (Fin p × Fin M)) G (fun t ω => birthJump (fun i => τ ω i - s)
        (fun i => dStar b * sourceMass s T (q i.1) / M) (t : ℝ)) e))
    (hbr : ∀ e e', IsTestedMart Q (modelObs tseq τ G) (bornBracket (transportD0 b E)
      (srcSignature K (Fin p × Fin M)) G (fun t ω => birthJump (fun i => τ ω i - s)
        (fun i => dStar b * sourceMass s T (q i.1) / M) (t : ℝ)) e e')) :
    IsFiniteSourceModel b E s T q h K M entrance
      (pastFiltration (modelObs tseq τ G) (measurable_modelObs htm hτm hG)) Q tseq τ G := by
  have hβ : ∀ i, Measurable[pastSigma (modelObs tseq τ G) 0] fun ω => τ ω i - s := fun i => by
    let _ := pastSigma (modelObs tseq τ G) 0
    exact (measurable_pi_iff.1 measurable_τ_past i).sub_const s
  have hsol : IsBornGramSolution Q (pastFiltration (modelObs tseq τ G)
      (measurable_modelObs htm hτm hG)) (transportD0 b E) (srcSignature K (Fin p × Fin M))
      (bornJ (probeJump fun i => dStar b * sourceMass s T (q i.1) / M) (fun i ω => τ ω i - s))
      G :=
    isBornGramSolution_of_tested (obs := modelObs tseq τ G) (measurable_modelObs htm hτm hG)
      (fun i => by rw [re_trace_probeJump]; exact hv i) (fun u => stronglyMeasurable_G_past u) hβ
      hc hfeas hdr hbr
  exact ⟨inferInstance, measurable_tseq_past, hseq, hlaw, measurable_τ_past, hbl, hind, hinit,
    hsol⟩

end BlockBand.SourceProcess.ClosedLimit
