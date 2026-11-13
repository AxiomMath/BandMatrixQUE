module

public import BlockBand.SourceProcess.HorizonExt.Glue

/-!
# Gluing at `r`: the bracket clause

After `r` the stopped compensated product of the glued process is
`N^G_{ee'}(r) + ι [C_e N^Y_{e'} + C_{e'} N^Y_e + N^Y_{ee'}](t - r)` with `ι = 1{σ^G > r}` and
`C_e = N^G_e(r)`, an `𝓖_r`-measurable value. On `{ι = 1}` the path of `G` is feasible and below
the trace level on `[0, r]`, so `ι C_e` is bounded (`ae_bound_coef`, from `exists_pC_bound`) and
the cross terms are martingales (`BornRestart.martingale_const_mul`). **`glue_bracket`** then
follows as `glue_drift`, with `bracket_path` for the identification.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.HorizonExt

open MeasureTheory ProbabilityTheory Filter Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.BornStopped
open scoped NNReal

variable {c : Type} [Fintype c] [DecidableEq c]
variable {Ω W : Type} {m : MeasurableSpace Ω} [MeasurableSpace W] {Q : Measure Ω}
  {ν : Measure W} [IsProbabilityMeasure Q] [IsProbabilityMeasure ν]
variable {𝓖 : Filtration ℝ≥0 m} {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × W))}
  {D0 : ℝ} {D : Matrix c c ℂ} {r : ℝ≥0}
  {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} {Y : ℝ≥0 → Ω × W → Matrix c c ℂ × Matrix c c ℂ}

omit [IsProbabilityMeasure Q] in
/-- **The restart coefficient `ι C_e` is bounded.** -/
theorem ae_bound_coef (hG : IsGramHorizonSolution Q 𝓖 D0 D r G)
    (hY : IsGramMartingaleSolution (Q.prod ν) 𝓕 D0 D Y)
    (h0 : ∀ᵐ x ∂(Q.prod ν), Y 0 x = G r x.1) (K : ℝ) (e : Fin 2 × c × c)
    {NG : ℝ≥0 → Ω → ℂ} (hNGe : ∀ t, NG t =ᵐ[Q] stoppedProcess (gramCompensated D0 D G e)
      (fun ω => min (gramTraceStop G K ω) (r : WithTop ℝ≥0)) t) :
    ∃ C, ∀ᵐ x ∂(Q.prod ν), ‖ind G K r x * NG r x.1‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_pC_bound D0 D K r e
  have hq := (measurePreserving_fst (μ := Q) (ν := ν)).quasiMeasurePreserving
  refine ⟨max C 0, ?_⟩
  filter_upwards [ae_good hG hY h0, hq.ae_eq_comp (hNGe r)] with x hx h1
  simp only [Function.comp_apply] at h1
  rw [ind_eq hx.1, h1, stoppedProcess_eq_stopTime, noHitInd]
  split_ifs with hE
  · simp
  · have hno : ∀ s ≤ r, ¬ K ≤ ((G s x.1).1.trace).re := fun s hs hK =>
      hE ((pStop_le_iff hx.1).2 ⟨s, hs, hK⟩)
    have e1 : stopTime (min (gramTraceStop G K x.1) (r : WithTop ℝ≥0)) r = r :=
      le_pStop_of_noHit (g := fun s => G s x.1) hno
    rw [one_mul, e1]
    exact (hC (fun s => G s x.1) hx.2.1 hno).trans (le_max_left _ _)

omit [DecidableEq c] in
theorem gramBracket_zero {Ω' : Type*} (H : ℝ≥0 → Ω' → Matrix c c ℂ × Matrix c c ℂ)
    (e e' : Fin 2 × c × c) (ω : Ω') :
    gramCompensated D0 D H e 0 ω * gramCompensated D0 D H e' 0 ω -
      ∫ s in Ioc (0 : ℝ) (0 : ℝ≥0), gramCovEntry D0 D e e' (H s.toNNReal ω) = 0 := by
  simp [gramCompensated]

omit [IsProbabilityMeasure Q] in
theorem stronglyMeasurable_coef (h𝓕 : m.comap Prod.fst ≤ 𝓕 0)
    (hG : ∀ t, StronglyMeasurable[𝓖 t] (G t)) (K : ℝ) {NG : ℝ≥0 → Ω → ℂ}
    (hNG : Martingale NG 𝓖 Q) :
    StronglyMeasurable[𝓕 0] fun x : Ω × W => ind G K r x * NG r x.1 :=
  (stronglyMeasurable_ind h𝓕 hG K).mul (((hNG.1 r).comp_measurable
    (comap_measurable Prod.fst)).mono ((MeasurableSpace.comap_mono (𝓖.le r)).trans h𝓕))

/-- **The bracket clause of the glued process.** -/
theorem glue_bracket (h𝓕 : m.comap Prod.fst ≤ 𝓕 0) (hG : IsGramHorizonSolution Q 𝓖 D0 D r G)
    (hY : IsGramMartingaleSolution (Q.prod ν) 𝓕 D0 D Y)
    (h0 : ∀ᵐ x ∂(Q.prod ν), Y 0 x = G r x.1) (K : ℝ) (e e' : Fin 2 × c × c) :
    ∃ N : ℝ≥0 → Ω × W → ℂ, Martingale N (glueFil 𝓖 𝓕 h𝓕 r) (Q.prod ν) ∧ ∀ t,
      N t =ᵐ[Q.prod ν] stoppedProcess (fun t ω => gramCompensated D0 D (glueProc r G Y) e t ω *
          gramCompensated D0 D (glueProc r G Y) e' t ω -
          ∫ s in Ioc (0 : ℝ) t, gramCovEntry D0 D e e' (glueProc r G Y s.toNNReal ω))
        (gramTraceStop (glueProc r G Y) K) t := by
  obtain ⟨NB, hNB, hNBe⟩ := hG.bracket K e e'
  obtain ⟨N1, hN1, hN1e⟩ := hG.drift K e
  obtain ⟨N2, hN2, hN2e⟩ := hG.drift K e'
  obtain ⟨M1, hM1, hM1e⟩ := hY.drift K e
  obtain ⟨M2, hM2, hM2e⟩ := hY.drift K e'
  obtain ⟨MB, hMB, hMBe⟩ := hY.bracket K e e'
  obtain ⟨C1, hC1⟩ := ae_bound_coef hG hY h0 K e hN1e
  obtain ⟨C2, hC2⟩ := ae_bound_coef hG hY h0 K e' hN2e
  have hq := (measurePreserving_fst (μ := Q) (ν := ν)).quasiMeasurePreserving
  have hYm := ((BornRestart.martingale_const_mul hM2 (stronglyMeasurable_coef h𝓕 hG.adapted K hN1)
    hC1).add (BornRestart.martingale_const_mul hM1 (stronglyMeasurable_coef h𝓕 hG.adapted K hN2)
    hC2)).add (BornRestart.martingale_const_mul hMB (stronglyMeasurable_ind (r := r) h𝓕
    hG.adapted K) (ae_of_all _ (norm_ind_le K)))
  have hY0 : (fun x => ind G K r x * N1 r x.1 * M2 0 x + ind G K r x * N2 r x.1 * M1 0 x +
      ind G K r x * MB 0 x) =ᵐ[Q.prod ν] 0 := by
    filter_upwards [hM1e 0, hM2e 0, hMBe 0] with x h1 h2 h3
    rw [h1, h2, h3, stoppedProcess_zero _ (gramCompensated_zero Y e),
      stoppedProcess_zero _ (gramCompensated_zero Y e'),
      stoppedProcess_zero _ (gramBracket_zero Y e e')]
    simp
  refine ⟨_, (martingale_lift_min (h := h𝓕) hNB).add (martingale_shift (h := h𝓕) hYm hY0),
    fun t => ?_⟩
  filter_upwards [ae_good hG hY h0, hq.ae_eq_comp (hNBe (min t r)), hq.ae_eq_comp (hN1e r),
    hq.ae_eq_comp (hN2e r), hM1e (t - r), hM2e (t - r), hMBe (t - r)]
    with x hx hb h1 h2 k1 k2 kb
  obtain ⟨hgc, -, hyc, -, hy0⟩ := hx
  simp only [Pi.add_apply, Function.comp_apply] at hb h1 h2 ⊢
  rw [stoppedProcess_eq_stopTime]
  refine Eq.trans ?_ (bracket_path hgc hyc hy0 D0 D e e' t).symm
  rw [hb, stoppedProcess_eq_stopTime]
  congr 1
  split_ifs
  · show ind G K r x * N1 r x.1 * M2 (t - r) x + ind G K r x * N2 r x.1 * M1 (t - r) x +
      ind G K r x * MB (t - r) x = _
    rw [h1, h2, k1, k2, kb, ind_eq hgc, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime,
      stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime]
    rw [show ∀ i a b a' b' d : ℂ, i * (a * b + a' * b' + d) = i * a * b + i * a' * b' + i * d
      from fun _ _ _ _ _ _ => by ring]
    rfl
  · rfl

end BlockBand.SourceProcess.HorizonExt
