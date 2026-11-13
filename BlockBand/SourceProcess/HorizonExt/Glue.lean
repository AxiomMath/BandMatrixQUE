module

public import BlockBand.SourceProcess.HorizonExt.PathClause
public import BlockBand.SourceProcess.HorizonExt.CondLift
public import BlockBand.SourceProcess.BornStopped.Pin
public import BlockBand.SourceProcess.BornRestart.Lim

/-!
# Gluing a horizon solution with a global solution at `r`: setup and the drift clause

Data: a horizon solution `G` on `(Ω, 𝓖, Q)` (`IsGramHorizonSolution`), a global solution `Y` on
`(Ω × W, 𝓕, Q ⊗ ν)` with `fst⁻¹ m ≤ 𝓕₀`, and `Y₀ = G_r ∘ fst` a.s. The glued process
`glueProc r G Y` follows `G` on `[0, r]` and `Y(· - r)` after `r`; its filtration is
`glueFil 𝓖 𝓕 r`.
* `ae_good`: a.s. both paths are continuous, feasible (`G` on `[0, r]`) and match at `r`.
* `rawStop G K` (the `rawHit` of the trace level by `G`) is a `𝓖`-stopping time and equals
  `σ^G_K` on continuous paths, so `ind = 1{rawStop > r}` is `𝓕₀`-measurable (`ind_eq`).
* **`glue_drift`**: the drift clause. The martingale is
  `N^G(t ∧ r) ∘ fst + 1{r ≤ t} ind N^Y(t - r)` (`martingale_lift_min`, `martingale_shift`,
  `BornRestart.martingale_const_mul`), identified with the stopped compensated coordinate by
  `drift_path`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.HorizonExt

open MeasureTheory ProbabilityTheory Filter Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.BornStopped
open scoped NNReal

variable {c : Type} [Fintype c] [DecidableEq c]
variable {Ω W : Type} {m : MeasurableSpace Ω} [MeasurableSpace W] {Q : Measure Ω}
  {ν : Measure W} [IsProbabilityMeasure Q] [IsProbabilityMeasure ν]
variable {𝓖 : Filtration ℝ≥0 m} {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × W))}
  {D0 : ℝ} {D : Matrix c c ℂ} {r : ℝ≥0}
  {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} {Y : ℝ≥0 → Ω × W → Matrix c c ℂ × Matrix c c ℂ}

/-- The glued process. -/
def glueProc (r : ℝ≥0) (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ)
    (Y : ℝ≥0 → Ω × W → Matrix c c ℂ × Matrix c c ℂ) (t : ℝ≥0) (x : Ω × W) :
    Matrix c c ℂ × Matrix c c ℂ :=
  glue r (fun s => G s x.1) (fun s => Y s x) t

/-- The good sample points. -/
def GoodPt (D : Matrix c c ℂ) (r : ℝ≥0) (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ)
    (Y : ℝ≥0 → Ω × W → Matrix c c ℂ × Matrix c c ℂ) (x : Ω × W) : Prop :=
  Continuous (fun s => G s x.1) ∧ (∀ s ≤ r, GramFeasible D (G s x.1)) ∧
    Continuous (fun s => Y s x) ∧ (∀ s, GramFeasible D (Y s x)) ∧ Y 0 x = G r x.1

omit [IsProbabilityMeasure Q] in
theorem ae_good (hG : IsGramHorizonSolution Q 𝓖 D0 D r G)
    (hY : IsGramMartingaleSolution (Q.prod ν) 𝓕 D0 D Y)
    (h0 : ∀ᵐ x ∂(Q.prod ν), Y 0 x = G r x.1) : ∀ᵐ x ∂(Q.prod ν), GoodPt D r G Y x := by
  have hq := (measurePreserving_fst (μ := Q) (ν := ν)).quasiMeasurePreserving
  filter_upwards [hq.ae hG.continuous, hq.ae hG.feasible, hY.continuous, hY.feasible, h0]
    with x h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- The raw trace stop of `G`. -/
def rawStop (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) (K : ℝ) : Ω → WithTop ℝ≥0 :=
  rawHit (traceSuperLevel K) (fun t ω => toGramReal (G t ω))

theorem isStoppingTime_rawStop (hG : ∀ t, StronglyMeasurable[𝓖 t] (G t)) (K : ℝ) :
    IsStoppingTime 𝓖 (rawStop G K) :=
  have : BorelSpace (Matrix c c ℂ × Matrix c c ℂ) := SourceProcessLaw.gramState_borel
  isStoppingTime_rawHit fun t => continuous_toGramReal.measurable.comp
    (SourceProcessLaw.measurable_of_stronglyMeasurable_gram le_rfl (hG t))

/-- The indicator `1{rawStop G K > r}` on the product. -/
def ind (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) (K : ℝ) (r : ℝ≥0) (x : Ω × W) : ℂ :=
  if rawStop G K x.1 ≤ r then 0 else 1

omit [IsProbabilityMeasure Q] [IsProbabilityMeasure ν] in
theorem stronglyMeasurable_ind (h𝓕 : m.comap Prod.fst ≤ 𝓕 0)
    (hG : ∀ t, StronglyMeasurable[𝓖 t] (G t)) (K : ℝ) :
    StronglyMeasurable[𝓕 0] (ind (W := W) G K r) := by
  have hS : MeasurableSet[𝓕 0] {x : Ω × W | rawStop G K x.1 ≤ r} :=
    h𝓕 _ ⟨_, 𝓖.le r _ (isStoppingTime_rawStop hG K r), rfl⟩
  exact StronglyMeasurable.ite hS stronglyMeasurable_const stronglyMeasurable_const

omit [MeasurableSpace W] [IsProbabilityMeasure Q] [IsProbabilityMeasure ν] in
theorem norm_ind_le (K : ℝ) (x : Ω × W) : ‖ind G K r x‖ ≤ 1 := by
  unfold ind; split_ifs <;> simp

omit [IsProbabilityMeasure Q] [IsProbabilityMeasure ν] in
theorem rawStop_eq {ω : Ω} (hc : Continuous fun s => G s ω) (K : ℝ) :
    rawStop G K ω = pStop (fun s => G s ω) K := by
  rw [rawStop, rawHit_eq_hitTime (Y := fun t ω => toGramReal (G t ω))
    (isClosed_traceSuperLevel K) (continuous_toGramReal.comp hc),
    hitTime_traceSuperLevel]
  rfl

omit [MeasurableSpace W] [IsProbabilityMeasure Q] [IsProbabilityMeasure ν] in
theorem ind_eq {x : Ω × W} (hc : Continuous fun s => G s x.1) (K : ℝ) :
    ind G K r x = noHitInd (fun s => G s x.1) K r := by
  rw [ind, noHitInd, rawStop_eq hc]

omit [Fintype c] [DecidableEq c] in
theorem stoppedProcess_zero {Ω' : Type*} (X : ℝ≥0 → Ω' → ℂ) (h : ∀ ω, X 0 ω = 0)
    (τ : Ω' → WithTop ℝ≥0) (ω : Ω') : stoppedProcess X τ 0 ω = 0 := by
  rw [stoppedProcess_eq_stopTime, nonpos_iff_eq_zero.1 (stopTime_le _ 0), h]

omit [DecidableEq c] in
theorem gramCompensated_zero {Ω' : Type*} (H : ℝ≥0 → Ω' → Matrix c c ℂ × Matrix c c ℂ)
    (e : Fin 2 × c × c) (ω : Ω') : gramCompensated D0 D H e 0 ω = 0 := by
  simp [gramCompensated]

/-- **The drift clause of the glued process.** -/
theorem glue_drift (h𝓕 : m.comap Prod.fst ≤ 𝓕 0) (hG : IsGramHorizonSolution Q 𝓖 D0 D r G)
    (hY : IsGramMartingaleSolution (Q.prod ν) 𝓕 D0 D Y)
    (h0 : ∀ᵐ x ∂(Q.prod ν), Y 0 x = G r x.1) (K : ℝ) (e : Fin 2 × c × c) :
    ∃ N : ℝ≥0 → Ω × W → ℂ, Martingale N (glueFil 𝓖 𝓕 h𝓕 r) (Q.prod ν) ∧ ∀ t,
      N t =ᵐ[Q.prod ν] stoppedProcess (gramCompensated D0 D (glueProc r G Y) e)
        (gramTraceStop (glueProc r G Y) K) t := by
  obtain ⟨NG, hNG, hNGe⟩ := hG.drift K e
  obtain ⟨NY, hNY, hNYe⟩ := hY.drift K e
  have hq := (measurePreserving_fst (μ := Q) (ν := ν)).quasiMeasurePreserving
  have hYm := BornRestart.martingale_const_mul hNY (stronglyMeasurable_ind (r := r) h𝓕 hG.adapted K)
    (ae_of_all _ (norm_ind_le K))
  have hY0 : (fun x => ind G K r x * NY 0 x) =ᵐ[Q.prod ν] 0 := by
    filter_upwards [hNYe 0] with x hx
    rw [hx, stoppedProcess_zero _ (gramCompensated_zero Y e), mul_zero]
    rfl
  refine ⟨_, (martingale_lift_min (h := h𝓕) hNG).add (martingale_shift (h := h𝓕) hYm hY0),
    fun t => ?_⟩
  filter_upwards [ae_good hG hY h0, hq.ae_eq_comp (hNGe (min t r)), hNYe (t - r)]
    with x hx h1 h2
  obtain ⟨hgc, -, hyc, -, hy0⟩ := hx
  simp only [Pi.add_apply, Function.comp_apply] at h1 ⊢
  rw [stoppedProcess_eq_stopTime]
  refine Eq.trans ?_ (drift_path hgc hyc hy0 D0 D e t).symm
  rw [h1, stoppedProcess_eq_stopTime]
  congr 1
  split_ifs
  · show ind G K r x * NY (t - r) x = _
    rw [h2, ind_eq hgc, stoppedProcess_eq_stopTime]
    rfl
  · rfl

end BlockBand.SourceProcess.HorizonExt
