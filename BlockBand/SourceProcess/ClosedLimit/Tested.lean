module

public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Tested martingale increments and the natural filtration of observables

Abstract (no random-band content).
Observables `obs : I → ℝ≥0 → Ω → ℂ` generate the raw natural filtration
`pastFiltration obs` (`𝓖_s = σ(obs i u : u ≤ s)`). A process `X` has *tested martingale
increments* (`IsTestedMart`) if `X t` is integrable and `E[φ(obs(u₁..u_m)) (X_t − X_s)] = 0` for
every bounded continuous cylinder test `φ` at times `u_l ≤ s` (the form of
`IsMartingaleIncrements`, in which limit passages are stated).

* `setIntegral_eq_zero_of_tested`: then `∫_A (X_t − X_s) = 0` for every `A ∈ 𝓖_s` (closed
  cylinders by the outer approximations `IsClosed.apprSeq`, then Dynkin `induction_on_inter`
  on the π-system of closed cylinders, which generates `𝓖_s`).
* `martingale_of_tested`: an adapted process with tested increments is a `𝓖`-martingale.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedLimit

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {I : Type*}

/-- `σ(obs i u : u ≤ s)`. -/
@[reducible] def pastSigma (obs : I → ℝ≥0 → Ω → ℂ) (s : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ (i : I) (u : ℝ≥0) (_ : u ≤ s), MeasurableSpace.comap (obs i u) inferInstance

theorem pastSigma_mono (obs : I → ℝ≥0 → Ω → ℂ) {s t : ℝ≥0} (hst : s ≤ t) :
    pastSigma obs s ≤ pastSigma obs t :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_le fun hu =>
    le_iSup_of_le (hu.trans hst) le_rfl

theorem comap_le_pastSigma (obs : I → ℝ≥0 → Ω → ℂ) (i : I) {u s : ℝ≥0} (hu : u ≤ s) :
    MeasurableSpace.comap (obs i u) inferInstance ≤ pastSigma obs s :=
  le_iSup_of_le i (le_iSup_of_le u (le_iSup_of_le hu le_rfl))

theorem measurable_obs_past (obs : I → ℝ≥0 → Ω → ℂ) (i : I) {u s : ℝ≥0} (hu : u ≤ s) :
    Measurable[pastSigma obs s] (obs i u) :=
  Measurable.of_comap_le (comap_le_pastSigma obs i hu)

variable [mΩ : MeasurableSpace Ω]

/-- **The natural filtration of the observables.** -/
def pastFiltration (obs : I → ℝ≥0 → Ω → ℂ) (hobs : ∀ i u, Measurable (obs i u)) :
    Filtration ℝ≥0 mΩ where
  seq := pastSigma obs
  mono' := fun _ _ h => pastSigma_mono obs h
  le' := fun _ => iSup_le fun i => iSup_le fun u => iSup_le fun _ => (hobs i u).comap_le

/-- **Tested martingale increments.** -/
def IsTestedMart (Q : Measure Ω) (obs : I → ℝ≥0 → Ω → ℂ) (X : ℝ≥0 → Ω → ℂ) : Prop :=
  (∀ t, Integrable (X t) Q) ∧ ∀ s t : ℝ≥0, s ≤ t → ∀ (m : ℕ) (i : Fin m → I) (u : Fin m → ℝ≥0),
    (∀ l, u l ≤ s) → ∀ φ : BoundedContinuousFunction (Fin m → ℂ) ℝ,
      ∫ ω, φ (fun l => obs (i l) (u l) ω) • (X t ω - X s ω) ∂Q = 0

/-- Closed cylinder sets of the observables at times `≤ s`. -/
def closedCyl (obs : I → ℝ≥0 → Ω → ℂ) (s : ℝ≥0) : Set (Set Ω) :=
  {A | ∃ (m : ℕ) (i : Fin m → I) (u : Fin m → ℝ≥0) (F : Set (Fin m → ℂ)), (∀ l, u l ≤ s) ∧
    IsClosed F ∧ A = (fun ω l => obs (i l) (u l) ω) ⁻¹' F}

omit mΩ in
theorem isPiSystem_closedCyl (obs : I → ℝ≥0 → Ω → ℂ) (s : ℝ≥0) :
    IsPiSystem (closedCyl obs s) := by
  rintro _ ⟨m₁, i₁, u₁, F₁, hu₁, hF₁, rfl⟩ _ ⟨m₂, i₂, u₂, F₂, hu₂, hF₂, rfl⟩ -
  refine ⟨m₁ + m₂, Fin.append i₁ i₂, Fin.append u₁ u₂,
    {x | (fun l => x (Fin.castAdd m₂ l)) ∈ F₁ ∧ (fun l => x (Fin.natAdd m₁ l)) ∈ F₂},
    fun l => ?_, ?_, ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · rw [Fin.append_left]; exact hu₁ l
    · rw [Fin.append_right]; exact hu₂ l
  · exact (hF₁.preimage (continuous_pi fun l => continuous_apply _)).inter
      (hF₂.preimage (continuous_pi fun l => continuous_apply _))
  · ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, Fin.append_left, Fin.append_right]

omit mΩ in
theorem measurable_cyl (obs : I → ℝ≥0 → Ω → ℂ) {s : ℝ≥0} {m : ℕ} (i : Fin m → I)
    (u : Fin m → ℝ≥0) (hu : ∀ l, u l ≤ s) :
    Measurable[pastSigma obs s] (fun ω l => obs (i l) (u l) ω) :=
  letI := pastSigma obs s
  Measurable.of_eval fun l => measurable_obs_past obs (i l) (hu l)

omit mΩ in
theorem pastSigma_eq_generateFrom (obs : I → ℝ≥0 → Ω → ℂ) (s : ℝ≥0) :
    pastSigma obs s = MeasurableSpace.generateFrom (closedCyl obs s) := by
  refine le_antisymm (iSup_le fun i => iSup_le fun u => iSup_le fun hu => ?_) ?_
  · rw [MeasurableSpace.comap_le_iff_le_map, BorelSpace.measurable_eq (α := ℂ),
      borel_eq_generateFrom_isClosed]
    refine MeasurableSpace.generateFrom_le fun C hC => ?_
    exact MeasurableSpace.measurableSet_generateFrom ⟨1, fun _ => i, fun _ => u,
      {x | x 0 ∈ C}, fun _ => hu, (show IsClosed C from hC).preimage (continuous_apply 0), rfl⟩
  · refine MeasurableSpace.generateFrom_le fun A ⟨m, i, u, F, hu, hF, hA⟩ => ?_
    rw [hA]; exact measurable_cyl obs i u hu hF.measurableSet

variable {Q : Measure Ω} {obs : I → ℝ≥0 → Ω → ℂ} {X : ℝ≥0 → Ω → ℂ}

/-- A bounded continuous real version of an `ℝ≥0`-valued test with values in `[0,1]`. -/
def realBCF {X : Type*} [TopologicalSpace X] (f : BoundedContinuousFunction X ℝ≥0)
    (hf : ∀ x, f x ≤ 1) : BoundedContinuousFunction X ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => (f x : ℝ), NNReal.continuous_coe.comp f.continuous⟩
    1 fun x y => by
      simp only [ContinuousMap.coe_mk]
      have h1 : (f x : ℝ) ≤ 1 := by exact_mod_cast hf x
      have h2 : (f y : ℝ) ≤ 1 := by exact_mod_cast hf y
      rw [Real.dist_eq, abs_le]; constructor <;> linarith [NNReal.coe_nonneg (f x), NNReal.coe_nonneg (f y)]

theorem integral_cyl_eq_zero (hX : IsTestedMart Q obs X) {s t : ℝ≥0} (hst : s ≤ t) {m : ℕ}
    (i : Fin m → I) (u : Fin m → ℝ≥0) (hu : ∀ l, u l ≤ s) {F : Set (Fin m → ℂ)}
    (hF : IsClosed F) (hobs : ∀ i u, Measurable (obs i u)) :
    ∫ ω in (fun ω l => obs (i l) (u l) ω) ⁻¹' F, (X t ω - X s ω) ∂Q = 0 := by
  set Y : Ω → Fin m → ℂ := fun ω l => obs (i l) (u l) ω
  have hY : Measurable Y := Measurable.of_eval fun l => hobs (i l) (u l)
  have hint : Integrable (fun ω => X t ω - X s ω) Q := (hX.1 t).sub (hX.1 s)
  have hz : ∀ n, ∫ ω, realBCF (hF.apprSeq n) (HasOuterApproxClosed.apprSeq_apply_le_one hF n)
      (Y ω) • (X t ω - X s ω) ∂Q = 0 := fun n => hX.2 s t hst m i u hu _
  have hlim := tendsto_integral_of_dominated_convergence (fun ω => ‖X t ω - X s ω‖)
    (F := fun n ω => realBCF (hF.apprSeq n) (HasOuterApproxClosed.apprSeq_apply_le_one hF n)
      (Y ω) • (X t ω - X s ω))
    (f := fun ω => (F.indicator (fun _ => (1 : ℝ)) (Y ω)) • (X t ω - X s ω))
    (fun n => ((Continuous.measurable (realBCF _ _).continuous).comp hY).aestronglyMeasurable.smul
      hint.aestronglyMeasurable) hint.norm
    (fun n => Eventually.of_forall fun ω => by
      rw [norm_smul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      have h1 : (hF.apprSeq n (Y ω) : ℝ) ≤ 1 := by
        exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hF n (Y ω)
      show ‖((hF.apprSeq n (Y ω) : ℝ≥0) : ℝ)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]; exact h1)
    (Eventually.of_forall fun ω => by
      have h := (tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hF)) (Y ω)
      have h' := (NNReal.continuous_coe.tendsto _).comp h
      have e : ((F.indicator (fun _ => (1 : ℝ≥0)) (Y ω) : ℝ≥0) : ℝ) =
          F.indicator (fun _ => (1 : ℝ)) (Y ω) := by
        by_cases hy : Y ω ∈ F
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy]
      rw [e] at h'
      exact h'.smul_const _)
  have hval : ∫ ω, (F.indicator (fun _ => (1 : ℝ)) (Y ω)) • (X t ω - X s ω) ∂Q = 0 :=
    tendsto_nhds_unique hlim (by simp only [hz]; exact tendsto_const_nhds)
  refine (integral_indicator (hY hF.measurableSet)).symm.trans
    ((integral_congr_ae (Eventually.of_forall fun ω => ?_)).trans hval)
  by_cases hy : Y ω ∈ F
  · simp [Set.indicator_of_mem (show ω ∈ Y ⁻¹' F from hy), Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem (show ω ∉ Y ⁻¹' F from hy), Set.indicator_of_notMem hy]

/-- **Tested increments integrate to zero over every past event.** -/
theorem setIntegral_eq_zero_of_tested (hX : IsTestedMart Q obs X)
    (hobs : ∀ i u, Measurable (obs i u)) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω}
    (hA : MeasurableSet[pastSigma obs s] A) : ∫ ω in A, (X t ω - X s ω) ∂Q = 0 := by
  have hle : pastSigma obs s ≤ mΩ := (pastFiltration obs hobs).le s
  have hint : Integrable (fun ω => X t ω - X s ω) Q := (hX.1 t).sub (hX.1 s)
  have huniv : ∫ ω, (X t ω - X s ω) ∂Q = 0 := by
    have h := integral_cyl_eq_zero hX hst (m := 0) Fin.elim0 Fin.elim0 (fun l => l.elim0)
      isClosed_univ hobs
    rwa [preimage_univ, Measure.restrict_univ] at h
  refine MeasurableSpace.induction_on_inter (m := pastSigma obs s)
    (C := fun A _ => ∫ ω in A, (X t ω - X s ω) ∂Q = 0) (pastSigma_eq_generateFrom obs s)
    (isPiSystem_closedCyl obs s) (by simp) ?_ ?_ ?_ A hA
  · rintro _ ⟨m, i, u, F, hu, hF, rfl⟩
    exact integral_cyl_eq_zero hX hst i u hu hF hobs
  · intro B hB h
    rw [setIntegral_compl (hle B hB) hint, huniv, h, sub_zero]
  · intro f hd hfm h
    rw [integral_iUnion (fun n => hle _ (hfm n)) hd hint.integrableOn]
    simp [h]

/-- **A martingale from tested increments** (adapted to the natural filtration). -/
theorem martingale_of_tested [IsFiniteMeasure Q] (hobs : ∀ i u, Measurable (obs i u))
    (hX : IsTestedMart Q obs X)
    (had : ∀ t, StronglyMeasurable[pastSigma obs t] (X t)) :
    Martingale X (pastFiltration obs hobs) Q := by
  refine ⟨had, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((pastFiltration obs hobs).le s) (hX.1 t)
    (fun _ _ _ => (hX.1 s).integrableOn) (fun A hA _ => ?_)
    (had s).aestronglyMeasurable).symm
  have h := setIntegral_eq_zero_of_tested hX hobs hst hA
  rw [integral_sub (hX.1 t).integrableOn (hX.1 s).integrableOn, sub_eq_zero] at h
  exact h.symm

end BlockBand.SourceProcess.ClosedLimit
