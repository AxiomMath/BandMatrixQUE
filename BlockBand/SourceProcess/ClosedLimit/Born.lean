module

public import BlockBand.SourceProcess.ClosedLimit.Tested
public import BlockBand.SourceProcess.ClosedLimit.StopC
public import BlockBand.SourceProcess.ClosedLimit.PathInt
public import BlockBand.SourceProcess.ModelExist.TransStop

/-!
# The born Gram martingale problem from tested increments (limit-passage tool, part 1)

Abstract: no random-band content beyond the Gram coefficients of the finite Gram law and the
births.

Setting: observables `obs : I → ℝ≥0 → Ω → ℂ` with raw natural filtration `𝓖 = pastFiltration obs`,
a Gram process `G` observed by `obs`, births `J_t = Σ_f 1{β_f ≤ t} j_f` with
`𝓖₀`-measurable times `β_f` and jumps of nonnegative trace, and `G − J` continuous **for every**
`ω`. If the unstopped compensated coordinates `bornCompensated e` and their compensated products
have tested martingale increments (`IsTestedMart`, the form produced by weak limits of
finite-`W` increments, as in `IsMartingaleIncrements`), then `G` is a born Gram
solution (`IsBornGramSolution`, the `solution` field of `IsFiniteSourceModel`) for `𝓖`:

* adaptedness of the compensated processes (`stronglyMeasurable_integral_past`: the time integral
  is `𝓖_t`-measurable, by `measurable_uncurry_split` with the past σ-algebra);
* path continuity (`continuous_integral_path`);
* martingales (`martingale_of_tested`);
* the trace stops: `ModelExist.exists_stop_ae_eq_traceStop` (a.e. a stopping time) and the
  complex optional stopping `exists_martingale_stopped_C`.

Main result: `isBornGramSolution_of_tested`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedLimit

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess BlockBand.SourceProcess.BornUnique BlockBand.SourceProcess.ModelExist
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {I : Type*} {obs : I → ℝ≥0 → Ω → ℂ}
  {c F : Type*} [Fintype c] [DecidableEq c] [Fintype F] [DecidableEq F]

/-- The birth process `J_t = Σ_f 1{β_f ≤ t} j_f` (`birthSum`). -/
def bornJ (j : F → GramState c) (β : F → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : GramState c :=
  birthSum j (fun f => β f ω) t

omit mΩ [Fintype c] [DecidableEq c] [DecidableEq F] in
theorem stronglyMeasurable_bornJ {m : MeasurableSpace Ω} (j : F → GramState c)
    {β : F → Ω → ℝ} (hβ : ∀ f, Measurable[m] (β f)) (t : ℝ≥0) :
    StronglyMeasurable[m] (bornJ j β t) := by
  unfold bornJ birthSum
  exact Finset.stronglyMeasurable_fun_sum _ fun f _ =>
    StronglyMeasurable.ite (measurableSet_le (hβ f) measurable_const) stronglyMeasurable_const
      stronglyMeasurable_const

omit mΩ [Fintype c] [DecidableEq c] in
/-- **The time integral of a born integrand is past-measurable.** -/
theorem stronglyMeasurable_integral_past {f : GramState c → ℂ} (hf : Continuous f)
    {G : ℝ≥0 → Ω → GramState c} {j : F → GramState c} {β : F → Ω → ℝ} (t : ℝ≥0)
    (hG : ∀ u, StronglyMeasurable[pastSigma obs u] (G u))
    (hβ : ∀ g, Measurable[pastSigma obs 0] (β g))
    (hc : ∀ ω, Continuous fun u => G u ω - bornJ j β u ω) :
    StronglyMeasurable[pastSigma obs t] fun ω => ∫ s in Ioc (0 : ℝ) t, f (G s.toNNReal ω) := by
  set m := pastSigma obs t
  have hβt : ∀ g, Measurable[m] (β g) := fun g => (hβ g).mono (pastSigma_mono obs zero_le) le_rfl
  set A : ℝ → Ω → GramState c := fun s ω => G (min s.toNNReal t) ω - bornJ j β (min s.toNNReal t) ω
  have hA : ∀ ω, Continuous fun s => A s ω := fun ω =>
    (hc ω).comp (continuous_real_toNNReal.min continuous_const)
  have hAm : ∀ (S : Finset F) s, Measurable[m] fun ω => f (A s ω + ∑ g ∈ S, j g) := fun S s => by
    have h1 : StronglyMeasurable[m] (G (min s.toNNReal t)) :=
      (hG _).mono (pastSigma_mono obs (min_le_right _ _))
    have h2 : StronglyMeasurable[m] (bornJ j β (min s.toNNReal t)) := stronglyMeasurable_bornJ j hβt _
    exact ((hf.comp (continuous_id.add continuous_const)).comp_stronglyMeasurable
      (h1.sub h2)).measurable
  have hτ : Measurable fun s : ℝ => ((min s.toNNReal t : ℝ≥0) : ℝ) :=
    (NNReal.continuous_coe.comp (continuous_real_toNNReal.min continuous_const)).measurable
  have hJ := measurable_uncurry_split (m := m) (f := f) j hA hf hAm hβt hτ
  have hint := (hJ.stronglyMeasurable.integral_prod_left (μ := volume.restrict (Ioc (0 : ℝ) t)))
  have e : (fun ω => ∫ s in Ioc (0 : ℝ) t, f (G s.toNNReal ω)) = fun ω =>
      ∫ s in Ioc (0 : ℝ) t, f (A s ω + birthSum j (fun g => β g ω) ((min s.toNNReal t : ℝ≥0) : ℝ)) :=
    funext fun ω => setIntegral_congr_fun measurableSet_Ioc fun s hs => by
      have hs' : s.toNNReal ≤ t := by
        rw [Real.toNNReal_le_iff_le_coe]; exact hs.2
      simp only [A, bornJ, min_eq_left hs', sub_add_cancel]
  rw [e]; exact hint

omit mΩ [Fintype c] [DecidableEq c] in
theorem continuous_integral_born {f : GramState c → ℂ} (hf : Continuous f)
    {G : ℝ≥0 → Ω → GramState c} {j : F → GramState c} {β : F → Ω → ℝ}
    (hc : ∀ ω, Continuous fun u => G u ω - bornJ j β u ω) (ω : Ω) :
    Continuous fun t : ℝ≥0 => ∫ s in Ioc (0 : ℝ) t, f (G s.toNNReal ω) :=
  continuous_integral_path hf j (G := fun u => G u ω) (fun g => β g ω) (hc ω)

/-- The compensated bracket process of `IsBornGramSolution.bracket`. -/
def bornBracket (D0 : ℝ) (D : Matrix c c ℂ) (G J : ℝ≥0 → Ω → GramState c)
    (e e' : Fin 2 × c × c) (t : ℝ≥0) (ω : Ω) : ℂ :=
  bornCompensated D0 D G J e t ω * bornCompensated D0 D G J e' t ω -
    ∫ s in Ioc (0 : ℝ) t, gramCovEntry D0 D e e' (G s.toNNReal ω)

variable {D0 : ℝ} {D : Matrix c c ℂ} {G : ℝ≥0 → Ω → GramState c} {j : F → GramState c}
  {β : F → Ω → ℝ}

omit mΩ in
theorem stronglyMeasurable_bornCompensated (hG : ∀ u, StronglyMeasurable[pastSigma obs u] (G u))
    (hβ : ∀ g, Measurable[pastSigma obs 0] (β g))
    (hc : ∀ ω, Continuous fun u => G u ω - bornJ j β u ω) (e : Fin 2 × c × c) (t : ℝ≥0) :
    StronglyMeasurable[pastSigma obs t] (bornCompensated D0 D G (bornJ j β) e t) := by
  have hJ : ∀ u, StronglyMeasurable[pastSigma obs t] (bornJ j β u) := fun u =>
    stronglyMeasurable_bornJ j (fun g => (hβ g).mono (pastSigma_mono obs zero_le) le_rfl) u
  have h1 := (continuous_gramEntry e).comp_stronglyMeasurable ((hG t).sub (hJ t))
  have h0 := (continuous_gramEntry e).comp_stronglyMeasurable
    (((hG 0).mono (pastSigma_mono obs zero_le)).sub (hJ 0))
  exact (h1.sub h0).sub (stronglyMeasurable_integral_past (continuous_gramDriftEntry D0 D e) t hG
    hβ hc)

omit mΩ in
theorem continuous_bornCompensated (hc : ∀ ω, Continuous fun u => G u ω - bornJ j β u ω)
    (e : Fin 2 × c × c) (ω : Ω) :
    Continuous fun t => bornCompensated D0 D G (bornJ j β) e t ω :=
  (((continuous_gramEntry e).comp (hc ω)).sub continuous_const).sub
    (continuous_integral_born (continuous_gramDriftEntry D0 D e) hc ω)

/-- **The born Gram martingale problem from tested increments.** -/
theorem isBornGramSolution_of_tested {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hobs : ∀ i u, Measurable (obs i u)) (hj : ∀ f, 0 ≤ ((j f).1.trace).re)
    (hG : ∀ u, StronglyMeasurable[pastSigma obs u] (G u))
    (hβ : ∀ g, Measurable[pastSigma obs 0] (β g))
    (hc : ∀ ω, Continuous fun u => G u ω - bornJ j β u ω)
    (hfeas : ∀ᵐ ω ∂Q, ∀ t, GramFeasible D (G t ω))
    (hdr : ∀ e, IsTestedMart Q obs (bornCompensated D0 D G (bornJ j β) e))
    (hbr : ∀ e e', IsTestedMart Q obs (bornBracket D0 D G (bornJ j β) e e')) :
    IsBornGramSolution Q (pastFiltration obs hobs) D0 D (bornJ j β) G := by
  set 𝓖 := pastFiltration obs hobs
  have hstop : ∀ K : ℝ, ∃ ρ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 ρ ∧
      ∀ᵐ ω ∂Q, ρ ω = gramTraceStop G K ω := fun K =>
    exists_stop_ae_eq_traceStop (𝓖 := 𝓖) (Q := Q) hG hj hβ (ae_of_all _ hc) K
  refine ⟨hG, fun t => stronglyMeasurable_bornJ j hβ t, ae_of_all _ hc, hfeas, ?_, ?_⟩
  · intro K e
    obtain ⟨ρ, hρ, hρe⟩ := hstop K
    have hM := martingale_of_tested hobs (hdr e) (stronglyMeasurable_bornCompensated hG hβ hc e)
    obtain ⟨M', hM', hM'e⟩ := exists_martingale_stopped_C hM (fun _ => EventuallyEq.rfl)
      (ae_of_all _ (continuous_bornCompensated hc e)) hρ
    exact ⟨M', hM', fun t => (hM'e t).trans (stoppedProcess_ae_eq _ hρe t)⟩
  · intro K e e'
    obtain ⟨ρ, hρ, hρe⟩ := hstop K
    have had : ∀ t, StronglyMeasurable[pastSigma obs t] (bornBracket D0 D G (bornJ j β) e e' t) :=
      fun t => ((stronglyMeasurable_bornCompensated hG hβ hc e t).mul
        (stronglyMeasurable_bornCompensated hG hβ hc e' t)).sub
        (stronglyMeasurable_integral_past (continuous_gramCovEntry D0 D e e') t hG hβ hc)
    have hM := martingale_of_tested hobs (hbr e e') had
    have hcont : ∀ ω, Continuous fun t => bornBracket D0 D G (bornJ j β) e e' t ω := fun ω =>
      ((continuous_bornCompensated hc e ω).mul (continuous_bornCompensated hc e' ω)).sub
        (continuous_integral_born (continuous_gramCovEntry D0 D e e') hc ω)
    obtain ⟨M', hM', hM'e⟩ := exists_martingale_stopped_C hM (fun _ => EventuallyEq.rfl)
      (ae_of_all _ hcont) hρ
    exact ⟨M', hM', fun t => (hM'e t).trans (stoppedProcess_ae_eq _ hρe t)⟩

end BlockBand.SourceProcess.ClosedLimit
