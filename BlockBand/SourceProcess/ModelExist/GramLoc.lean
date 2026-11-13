module

public import BlockBand.SourceProcess.ModelExist.CLoc
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GramRealPath
public import BlockBand.SourceProcess.Stochastic.Semimartingale.HittingTime
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AssemblyStratum

/-!
# Gram martingale-problem solutions as complex `LocMart`s

For a progressively measurable solution `G` of the Gram martingale problem
(`IsGramMartingaleSolution`) on any filtered probability space, the sibling module proves:
* `gramLoc_drift`: every compensated coordinate `N_e = gramCompensated D₀ 𝖣 G e` is a `CLocMart`
  with drift `0`;
* `gramLoc_bracket`: every product `N_e N_e'` is a `CLocMart` with drift `Γ_{ee'}(G_s)`
  (`gramCovEntry`).

This file provides the progressive measurability of `N_e` (`isStronglyProgressive_gramCompensated`)
and the localizing sequence `trHit G n`, the raw hitting time of `[n, ∞)` by `Re Tr M`: a stopping
time, a.s. equal to the trace stop `σ_n`, with `σ_n → ⊤` on continuous paths.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.RankFree
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  SourceSDE.frobBorelSpace SourceSDE.matrixPseudoMetrizable

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- Pathwise integrals of strongly progressive complex processes are strongly progressive. -/
theorem isStronglyProgressive_integral_C {g : ℝ≥0 → Ω → ℂ} (hg : IsStronglyProgressive 𝓖 g) :
    IsStronglyProgressive 𝓖 (fun t ω => ∫ r in Ioc (0 : ℝ) t, g r.toNNReal ω) := fun T => by
  let _ : MeasurableSpace (Set.Iic T × Ω) := Subtype.instMeasurableSpace.prod (𝓖 T)
  set c : ℝ → Set.Iic T := fun s => ⟨min s.toNNReal T, min_le_right _ _⟩
  have hc : Measurable c := (measurable_real_toNNReal.min measurable_const).subtype_mk
  set S : Set ((Set.Iic T × Ω) × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ ((q.1.1 : ℝ≥0) : ℝ)}
  have hS : MeasurableSet S := by
    refine (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd ?_)
    exact measurable_coe_nnreal_real.comp
      (measurable_subtype_coe.comp (measurable_fst.comp measurable_fst))
  have hG : StronglyMeasurable fun q : (Set.Iic T × Ω) × ℝ => g (c q.2) q.1.2 :=
    (hg T).comp_measurable ((hc.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst))
  have hI := StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) T))
    (hG.indicator hS)
  convert hI using 1
  funext p
  have hsub : Ioc (0 : ℝ) (p.1 : ℝ) ⊆ Ioc (0 : ℝ) T :=
    Ioc_subset_Ioc_right (by exact_mod_cast p.1.2)
  have e : (fun r => S.indicator (fun q => g (c q.2) q.1.2) (p, r)) =
      (Ioc (0 : ℝ) (p.1 : ℝ)).indicator fun r => g (c r) p.2 := by
    funext r; simp only [Set.indicator, S, Set.mem_ofPred_eq, mem_Ioc]
  rw [e, setIntegral_indicator measurableSet_Ioc, inter_eq_right.2 hsub]
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hrT : r.toNNReal ≤ T := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1.le]; exact (hsub hr).2
  simp only [c, min_eq_left hrT]

theorem IsStronglyProgressive.re' {g : ℝ≥0 → Ω → ℂ} (hg : IsStronglyProgressive 𝓖 g) :
    IsStronglyProgressive 𝓖 (fun t ω => (g t ω).re) := fun T =>
  Complex.continuous_re.comp_stronglyMeasurable (hg T)

theorem IsStronglyProgressive.im' {g : ℝ≥0 → Ω → ℂ} (hg : IsStronglyProgressive 𝓖 g) :
    IsStronglyProgressive 𝓖 (fun t ω => (g t ω).im) := fun T =>
  Complex.continuous_im.comp_stronglyMeasurable (hg T)

variable {c : Type*} [Fintype c] [DecidableEq c] {D0 : ℝ} {D : Matrix c c ℂ}
  {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}

omit [DecidableEq c] in
/-- The compensated Gram coordinates of a progressive process are progressive. -/
theorem isStronglyProgressive_gramCompensated (h0 : StronglyMeasurable[𝓖 0] (G 0))
    (hp : IsStronglyProgressive 𝓖 G) (e : Fin 2 × c × c) :
    IsStronglyProgressive 𝓖 (gramCompensated D0 D G e) := by
  have h1 : IsStronglyProgressive 𝓖 (fun t ω => gramEntry e (G t ω)) := fun T =>
    (continuous_gramEntry e).comp_stronglyMeasurable (hp T)
  have h2 : IsStronglyProgressive 𝓖 (fun _ ω => gramEntry e (G 0 ω)) := fun T =>
    (((continuous_gramEntry e).comp_stronglyMeasurable (h0.mono (𝓖.mono zero_le)))).comp_measurable
      measurable_snd
  have h3 : IsStronglyProgressive 𝓖 (fun t ω => gramDriftEntry D0 D e (G t ω)) := fun T =>
    (continuous_gramDriftEntry D0 D e).comp_stronglyMeasurable (hp T)
  have h4 := isStronglyProgressive_integral_C h3
  exact fun T => ((h1 T).sub (h2 T)).sub (h4 T)

omit [MeasurableSpace Ω] [DecidableEq c] in
theorem hitTime_trace (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) (K : ℝ) (ω : Ω) :
    hitTime (Ici K) (fun t ω => ((G t ω).1.trace).re) ω = gramTraceStop G K ω := by
  simp only [hitTime, gramTraceStop, mem_Ici]

omit [MeasurableSpace Ω] [DecidableEq c] in
/-- On a continuous path, the trace stops tend to `⊤`. -/
theorem tendsto_gramTraceStop {ω : Ω} (hc : Continuous fun t => G t ω) :
    Tendsto (fun n : ℕ => gramTraceStop G n ω) atTop (𝓝 ⊤) := by
  have hf : Continuous fun t => ((G t ω).1.trace).re :=
    Complex.continuous_re.comp ((continuous_fst.comp hc).matrix_trace)
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => absurd ha not_top_lt⟩
  lift a to ℝ≥0 using ha.ne_top
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := a + 1)).bddAbove_image hf.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_gt C
  filter_upwards [eventually_ge_atTop N] with n hn
  have hlt : (a : WithTop ℝ≥0) < ((a + 1 : ℝ≥0) : WithTop ℝ≥0) :=
    WithTop.coe_lt_coe.2 (lt_add_one a)
  refine hlt.trans_le (le_iInf₂ fun t ht => ?_)
  by_contra hlt'
  have htT : t ≤ a + 1 := (WithTop.coe_lt_coe.1 (not_le.1 hlt')).le
  have := hC ⟨t, ⟨zero_le, htT⟩, rfl⟩
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- The raw trace hitting times. -/
def trHit (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) (n : ℕ) : Ω → WithTop ℝ≥0 :=
  rawHit (Ici (n : ℝ)) (fun t ω => ((G t ω).1.trace).re)

section Sol
omit [DecidableEq c]
variable (hG : IsGramMartingaleSolution Q 𝓖 D0 D G)
include hG

theorem isStoppingTime_trHit (n : ℕ) : IsStoppingTime 𝓖 (trHit G n) := by
  have : SecondCountableTopology (Matrix c c ℂ) :=
    inferInstanceAs (SecondCountableTopology (c → c → ℂ))
  have : BorelSpace (Matrix c c ℂ × Matrix c c ℂ) := Prod.borelSpace
  exact isStoppingTime_rawHit fun t =>
    (Complex.continuous_re.comp (continuous_fst.matrix_trace)).measurable.comp
      (measurable_G0 hG t)

theorem trHit_ae (n : ℕ) : ∀ᵐ ω ∂Q, trHit G n ω = gramTraceStop G n ω := by
  filter_upwards [hG.continuous] with ω hc
  rw [trHit, rawHit_eq_hitTime (Y := fun t ω => ((G t ω).1.trace).re) isClosed_Ici
    (Complex.continuous_re.comp ((continuous_fst.comp hc).matrix_trace)), hitTime_trace]

theorem tendsto_trHit : ∀ᵐ ω ∂Q, Tendsto (fun n => trHit G n ω) atTop (𝓝 ⊤) := by
  have h := ae_all_iff.2 (trHit_ae hG)
  filter_upwards [hG.continuous, h] with ω hc h'
  simp only [h']
  exact tendsto_gramTraceStop hc

end Sol

end BlockBand.SourceProcess.ModelExist
