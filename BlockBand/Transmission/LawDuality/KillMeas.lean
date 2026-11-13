module

public import BlockBand.Transmission.LawDuality.KillFullMart
public import BlockBand.Transmission.LawDuality.KillFTC
public import BlockBand.Transmission.Dual.GShift
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Adapted

/-!
# Measurability of the stopped ratio, the drift and the killing

* `measurable_levelFun_comp`: `ω ↦ f_{n(ω)}(dualCoordOf …)` is measurable for any family `f_k`
  continuous on the chambers, when the state is always in its chamber (piecewise extension);
* `isStronglyProgressive_pathRatio`, `isStronglyProgressive_pathGenInd`,
  `isStronglyProgressive_rateInd`: `F_{Z_t}(ν)`, `𝒟F(Z_t)1{t<τ}` and `k(t)R_t1{t<τ}` are
  progressive (adapted and right-continuous, `Dual.G.isStronglyProgressive_of_rightCont`);
* hence `F_{Z_{s∧τ}}(ν)` is `𝓖_s`-measurable (`stronglyMeasurable_ratioStop`), and so are the
  integrals `∫_{(0,s]} 𝒟F(Z)1{·<τ}` and `∫_{(0,s]} kR1{·<τ}`
  (`SemimartingaleIto.stronglyMeasurable_integral_of_progressive`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

theorem measurable_levelFun_comp {Ω : Type*} {mΩ : MeasurableSpace Ω} (f : ∀ k : ℕ, DualCoord k → ℝ)
    (hf : ∀ k, ContinuousOn (f k) (dualChamber k)) {n : Ω → ℕ} {a b : Ω → ℕ → ℝ}
    (hn : Measurable n) (ha : Measurable a) (hb : Measurable b)
    (hch : ∀ ω, dualCoordOf (n ω) (a ω) (b ω) ∈ dualChamber (n ω)) :
    Measurable fun ω => f (n ω) (dualCoordOf (n ω) (a ω) (b ω)) := by
  classical
  set F : Ω × ℕ → ℝ := fun z =>
    (dualChamber z.2).piecewise (f z.2) (fun _ => 0) (dualCoordOf z.2 (a z.1) (b z.1)) with hF
  have hFm : Measurable F := measurable_from_prod_countable_left fun k =>
    ((hf k).measurable_piecewise continuousOn_const
      (isOpen_dualChamber k).measurableSet).comp (measurable_dualCoordOf_comp ha hb k)
  have e : (fun ω => f (n ω) (dualCoordOf (n ω) (a ω) (b ω))) = F ∘ fun ω => (ω, n ω) := by
    funext ω
    simp only [hF, Function.comp_apply, piecewise_eq_of_mem _ _ _ (hch ω)]
  rw [e]
  exact hFm.comp (measurable_id.prodMk hn)

theorem continuousOn_ratioOn (ν : FiniteMeasure unitInterval) (k : ℕ) :
    ContinuousOn (ratioOn ν : DualCoord k → ℝ) (dualChamber k) := fun _ hz =>
  ((continuousAt_ratioOn hz ν).comp (f := fun w : DualCoord k => (w, ν))
    (continuous_id.prodMk continuous_const).continuousAt).continuousWithinAt

theorem continuousOn_dualGenerator_ratioOn (D0 : ℝ) (ν : FiniteMeasure unitInterval) (k : ℕ) :
    ContinuousOn (dualGenerator D0 (ratioOn ν : DualCoord k → ℝ)) (dualChamber k) := fun _ hz =>
  (continuousAt_dualGenerator_ratioOn_z D0 hz ν).continuousWithinAt

/-- `1{t < τ}`. -/
def stopInd {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : WithTop ℝ≥0) < τ ω then 1 else 0

theorem tendsto_stopInd_right {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (ω : Ω) (t : ℝ≥0) :
    Tendsto (fun s => stopInd τ s ω) (𝓝[≥] t) (𝓝 (stopInd τ t ω)) := by
  by_cases ht : (t : WithTop ℝ≥0) < τ ω
  · have hev : ∀ᶠ s : ℝ≥0 in 𝓝 t, (s : WithTop ℝ≥0) < τ ω := by
      cases hτ : τ ω with
      | top => exact Eventually.of_forall fun s => WithTop.coe_lt_top _
      | coe c =>
        rw [hτ] at ht
        filter_upwards [isOpen_Iio.mem_nhds (WithTop.coe_lt_coe.1 ht)] with s hs
        exact WithTop.coe_lt_coe.2 hs
    refine (tendsto_const_nhds.congr' ?_).mono_left nhdsWithin_le_nhds
    filter_upwards [hev] with s hs
    unfold stopInd
    split_ifs
    rfl
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have : ¬ (s : WithTop ℝ≥0) < τ ω := fun h =>
      ht (lt_of_le_of_lt (WithTop.coe_le_coe.2 hs) h)
    unfold stopInd
    split_ifs
    rfl

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ} {p : ℕ} {x y : Fin p → ℝ}
  {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

theorem measurable_stopInd {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (t : ℝ≥0) :
    Measurable[𝓖 t] (stopInd τ t) := by
  have hs : MeasurableSet[𝓖 t] {ω | (t : WithTop ℝ≥0) < τ ω} := by
    have := (hτ t).compl
    convert this using 1
    ext ω; simp only [mem_ofPred_eq, mem_compl_iff]; exact not_le.symm
  exact Measurable.ite hs measurable_const measurable_const

section Prog

variable (h : IsDualDeletionProcess P 𝓖 D0 x y N X Y)
  (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
include h hpath

theorem measurable_pathRatio (ν : FiniteMeasure unitInterval) (t : ℝ≥0) :
    Measurable[𝓖 t] (pathRatio ν N X Y t) :=
  measurable_levelFun_comp (mΩ := 𝓖 t) (fun k => (ratioOn ν : DualCoord k → ℝ))
    (continuousOn_ratioOn ν) (h.adapted t).1 (h.adapted t).2.1 (h.adapted t).2.2
    fun ω => (hpath ω).chamber t

theorem measurable_pathGen (ν : FiniteMeasure unitInterval) (t : ℝ≥0) :
    Measurable[𝓖 t] (pathGen D0 ν N X Y t) :=
  measurable_levelFun_comp (mΩ := 𝓖 t) (fun k => dualGenerator D0 (ratioOn ν : DualCoord k → ℝ))
    (continuousOn_dualGenerator_ratioOn D0 ν) (h.adapted t).1 (h.adapted t).2.1
    (h.adapted t).2.2 fun ω => (hpath ω).chamber t

theorem isStronglyProgressive_pathRatio (ν : FiniteMeasure unitInterval) :
    IsStronglyProgressive 𝓖 (pathRatio ν N X Y) :=
  G.isStronglyProgressive_of_rightCont (fun t => (measurable_pathRatio h hpath ν t).stronglyMeasurable)
    fun ω t => ((continuous_ratioPath (hpath ω) ν).tendsto t).mono_left nhdsWithin_le_nhds

omit h m in
theorem pathGen_eq_sum (hstart : ∀ ω, N 0 ω = p) (ν : FiniteMeasure unitInterval)
    (t : ℝ≥0) (ω : Ω) : pathGen D0 ν N X Y t ω = ∑ j ∈ Finset.range p,
      dualLift (dualGenerator D0 (ratioOn ν : DualCoord (j + 1) → ℝ)) (N t ω) (X t ω) (Y t ω) :=
  (sum_dualLift_eq (hstart ω ▸ (hpath ω).antitone zero_le)
    (fun k => dualGenerator D0 (ratioOn ν : DualCoord k → ℝ))
    (fun z => dualGenerator_zero D0 _ z) _ _).symm

omit h m in
theorem tendsto_pathGen_right (hstart : ∀ ω, N 0 ω = p) (ν : FiniteMeasure unitInterval)
    (ω : Ω) (t : ℝ≥0) :
    Tendsto (fun s => pathGen D0 ν N X Y s ω) (𝓝[≥] t) (𝓝 (pathGen D0 ν N X Y t ω)) := by
  simp_rw [pathGen_eq_sum hpath hstart ν _ ω]
  exact tendsto_finsetSum _ fun j _ => tendsto_lift_right_of_continuousAt (hpath ω)
    (fun _ hz => continuousAt_dualGenerator_ratioOn_z D0 hz ν) t

theorem isStronglyProgressive_pathGenInd (hstart : ∀ ω, N 0 ω = p)
    (ν : FiniteMeasure unitInterval) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) :
    IsStronglyProgressive 𝓖 (fun t ω => pathGen D0 ν N X Y t ω * stopInd τ t ω) :=
  G.isStronglyProgressive_of_rightCont
    (fun t => ((measurable_pathGen h hpath ν t).mul (measurable_stopInd hτ t)).stronglyMeasurable)
    fun ω t => (tendsto_pathGen_right hpath hstart ν ω t).mul (tendsto_stopInd_right τ ω t)

theorem isStronglyProgressive_rateInd {k : ℝ → ℝ} (hk : Continuous k)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) :
    IsStronglyProgressive 𝓖 (fun t ω => k t * dualTotal (N t ω) (X t ω) (Y t ω) * stopInd τ t ω) :=
  G.isStronglyProgressive_of_rightCont
    (fun t => ((measurable_const.mul (measurable_dualTotal_comp (mΩ := 𝓖 t) (h.adapted t).1
      (h.adapted t).2.1 (h.adapted t).2.2)).mul (measurable_stopInd hτ t)).stronglyMeasurable)
    fun ω t => ((((hk.comp NNReal.continuous_coe).tendsto t).mono_left nhdsWithin_le_nhds).mul
      (((continuous_total (hpath ω)).tendsto t).mono_left nhdsWithin_le_nhds)).mul
      (tendsto_stopInd_right τ ω t)

/-- **`F_{Z_{s∧τ}}(ν)` is `𝓖_s`-measurable.** -/
theorem stronglyMeasurable_ratioStop (ν : FiniteMeasure unitInterval) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) (s : ℝ≥0) :
    StronglyMeasurable[𝓖 s] fun ω => pathRatio ν N X Y (stopAt τ s ω) ω :=
  (isStronglyProgressive_pathRatio h hpath ν).stronglyAdapted_stoppedProcess hτ s

end Prog

end BlockBand.Transmission.LawDuality
