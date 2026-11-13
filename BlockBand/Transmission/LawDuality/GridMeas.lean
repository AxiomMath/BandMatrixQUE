module

public import BlockBand.Transmission.LawDuality.KillIdentity
public import BlockBand.Transmission.LawDuality.KillCap
public import BlockBand.Transmission.LawDuality.BorelGiry
public import BlockBand.Transmission.LawDuality.RatioForward

/-!
# Duality strip: joint measurability of the strip integrands

* `measurable_uncurry_rightCont`: a right-continuous process with measurable marginals is
  jointly measurable on `ℝ × Ω` (time read at `v⁺`; dyadic ceilings);
* Carathéodory in the measure variable `ν` (`FiniteMeasure [0,1]` is metrizable and second
  countable, `BorelGiry`): `ratioStop`, `genStop`, `pathGen·1{·<τ}`, `pathRatio` are jointly
  measurable in `(ν, (v, ω'))`; `killFac`, `killDer`, `R·1{·<τ}` in `(v, ω')`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- **Right-continuous processes are jointly measurable** (time `v ∈ ℝ` read at `v⁺`). -/
theorem measurable_uncurry_rightCont {Ω : Type*} [MeasurableSpace Ω] {u : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (u t)) (hrc : ∀ ω t, Tendsto (fun s => u s ω) (𝓝[≥] t) (𝓝 (u t ω))) :
    Measurable fun q : ℝ × Ω => u q.1.toNNReal q.2 := by
  refine measurable_of_tendsto_metrizable
    (f := fun (l : ℕ) (q : ℝ × Ω) => u (ceilDyad l q.1.toNNReal) q.2) (fun l => ?_)
    (tendsto_pi_nhds.2 fun q => (hrc q.2 _).comp (tendsto_ceilDyad _))
  have hF : Measurable fun z : Ω × ℕ => u ((z.2 : ℝ≥0) / 2 ^ l) z.1 :=
    measurable_from_prod_countable_left fun k => by
      show Measurable fun ω => u ((k : ℝ≥0) / 2 ^ l) ω
      exact hm _
  have hg : Measurable fun q : ℝ × Ω => (q.2, ⌈q.1.toNNReal * 2 ^ l⌉₊) :=
    measurable_snd.prodMk (Nat.measurable_ceil.comp
      ((measurable_real_toNNReal.comp measurable_fst).mul_const _))
  exact hF.comp hg

theorem killInd_eq_stopInd {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (v : ℝ) (ω : Ω) :
    killInd (τ ω) v = stopInd τ v.toNNReal ω := rfl

/-- The dual integrand `K_v G_v + Φ_v K'_v` of `integral_killed_dual`. -/
def dualInteg {Ω : Type*} (D0 : ℝ) (k : ℝ → ℝ) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ)
    (τ : Ω → WithTop ℝ≥0) (ν : FiniteMeasure unitInterval) (v : ℝ) (ω : Ω) : ℝ :=
  killFac k N X Y τ v ω * genStop D0 ν N X Y τ v ω + ratioStop ν N X Y τ v ω * killDer k N X Y τ v ω

/-- The forward drift at the dual point, on `{v < τ}`: `K_v(𝒟F 1{v<τ} − h(u)(R1{v<τ})F)`. -/
def fwdInteg {Ω : Type*} (D0 E : ℝ) (κ k : ℝ → ℝ) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ)
    (τ : Ω → WithTop ℝ≥0) (u : ℝ) (ν : FiniteMeasure unitInterval) (v : ℝ) (ω : Ω) : ℝ :=
  killFac k N X Y τ v ω * (pathGen D0 ν N X Y v.toNNReal ω * killInd (τ ω) v -
    absorptionRate E κ u * (dualTotal (N v.toNNReal ω) (X v.toNNReal ω) (Y v.toNNReal ω) *
      killInd (τ ω) v) * pathRatio ν N X Y v.toNNReal ω)

theorem ratioStop_of_lt {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    {τ : Ω → WithTop ℝ≥0} (ν : FiniteMeasure unitInterval) {v : ℝ} {ω : Ω}
    (hv : (v.toNNReal : WithTop ℝ≥0) < τ ω) :
    ratioStop ν N X Y τ v ω = pathRatio ν N X Y v.toNNReal ω := by
  unfold ratioStop stopAt
  rw [min_eq_left hv.le]; rfl

/-- **The two integrands differ by the killing mismatch** (`v > 0`). -/
theorem fwdInteg_sub_dualInteg {Ω : Type*} (D0 E : ℝ) (κ k : ℝ → ℝ) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) (τ : Ω → WithTop ℝ≥0) (u : ℝ) (ν : FiniteMeasure unitInterval)
    {v : ℝ} (hv : 0 < v) (ω : Ω) :
    fwdInteg D0 E κ k N X Y τ u ν v ω - dualInteg D0 k N X Y τ ν v ω =
      killFac k N X Y τ v ω * (dualTotal (N v.toNNReal ω) (X v.toNNReal ω) (Y v.toNNReal ω) *
        killInd (τ ω) v) * pathRatio ν N X Y v.toNNReal ω * (k v - absorptionRate E κ u) := by
  unfold fwdInteg dualInteg genStop killDer killRate
  by_cases h : (v.toNNReal : WithTop ℝ≥0) < τ ω
  · have h1 : killInd (τ ω) v = 1 := ite_eq_left_iff.2 fun h' => absurd h h'
    rw [ratioStop_of_lt ν h, h1]
    simp only [hv, ↓reduceIte]
    ring
  · have h1 : killInd (τ ω) v = 0 := ite_eq_right_iff.2 fun h' => absurd h' h
    rw [h1]; ring

section Joint

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ} {p : ℕ} {x y : Fin p → ℝ}
  {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

omit m in
theorem continuous_pathRatio_nu {ω : Ω}
    (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) (t : ℝ≥0) :
    Continuous fun ν => pathRatio ν N X Y t ω :=
  continuous_transmissionRatio_vec (IsRatioParameter.isRatioRange (hP.chamber t))

omit m in
theorem continuous_pathGen_nu {ω : Ω}
    (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) (D0 : ℝ) (t : ℝ≥0) :
    Continuous fun ν => pathGen D0 ν N X Y t ω :=
  continuous_iff_continuousAt.2 fun ν => (continuousAt_dualGenerator_ratioOn D0
    (hP.chamber t) ν).comp (f := fun ν => (dualCoordOf (N t ω) (X t ω) (Y t ω), ν))
    (continuous_const.prodMk continuous_id).continuousAt

variable (h : IsDualDeletionProcess P 𝓖 D0 x y N X Y)
  (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
  (hstart : ∀ ω, N 0 ω = p) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
include h hpath hstart hτ

omit hstart in
theorem measurable_ratioStop_joint :
    Measurable fun q : FiniteMeasure unitInterval × (ℝ × Ω) =>
      ratioStop q.1 N X Y τ q.2.1 q.2.2 := by
  refine measurable_uncurry_of_continuous_of_measurable
    (u := fun ν (q : ℝ × Ω) => ratioStop ν N X Y τ q.1 q.2)
    (fun q => continuous_pathRatio_nu (hpath q.2) _) fun ν => ?_
  exact measurable_uncurry_of_continuous_of_measurable
    (u := fun (r : ℝ) (ω : Ω) => ratioStop ν N X Y τ r ω)
    (fun ω => continuous_ratioStop (hpath ω) ν)
    fun r => ((stronglyMeasurable_ratioStop h hpath ν hτ r.toNNReal).mono (𝓖.le _)).measurable

theorem measurable_pathGenInd_joint :
    Measurable fun q : FiniteMeasure unitInterval × (ℝ × Ω) =>
      pathGen D0 q.1 N X Y q.2.1.toNNReal q.2.2 * killInd (τ q.2.2) q.2.1 := by
  refine measurable_uncurry_of_continuous_of_measurable
    (u := fun ν (q : ℝ × Ω) => pathGen D0 ν N X Y q.1.toNNReal q.2 * killInd (τ q.2) q.1)
    (fun q => (continuous_pathGen_nu (hpath q.2) D0 _).mul continuous_const) fun ν => ?_
  exact measurable_uncurry_rightCont (u := fun t ω => pathGen D0 ν N X Y t ω * stopInd τ t ω)
    (fun t => ((measurable_pathGen h hpath ν t).mono (𝓖.le _) le_rfl).mul
      ((measurable_stopInd hτ t).mono (𝓖.le _) le_rfl))
    fun ω t => (tendsto_pathGen_right hpath hstart ν ω t).mul (tendsto_stopInd_right τ ω t)

omit hstart hτ in
theorem measurable_pathRatio_joint :
    Measurable fun q : FiniteMeasure unitInterval × (ℝ × Ω) =>
      pathRatio q.1 N X Y q.2.1.toNNReal q.2.2 := by
  refine measurable_uncurry_of_continuous_of_measurable
    (u := fun ν (q : ℝ × Ω) => pathRatio ν N X Y q.1.toNNReal q.2)
    (fun q => continuous_pathRatio_nu (hpath q.2) _) fun ν => ?_
  exact measurable_uncurry_rightCont (u := fun t ω => pathRatio ν N X Y t ω)
    (fun t => (measurable_pathRatio h hpath ν t).mono (𝓖.le _) le_rfl)
    fun ω t => ((continuous_ratioPath (hpath ω) ν).tendsto t).mono_left nhdsWithin_le_nhds

theorem measurable_genStop_joint :
    Measurable fun q : FiniteMeasure unitInterval × (ℝ × Ω) =>
      genStop D0 q.1 N X Y τ q.2.1 q.2.2 :=
  (measurable_pathGenInd_joint h hpath hstart hτ).mul
    (Measurable.ite (measurableSet_Ioi.preimage (measurable_fst.comp measurable_snd))
      measurable_const measurable_const)

omit hstart in
theorem measurable_totalInd_joint :
    Measurable fun q : ℝ × Ω =>
      dualTotal (N q.1.toNNReal q.2) (X q.1.toNNReal q.2) (Y q.1.toNNReal q.2) * killInd (τ q.2) q.1 :=
  measurable_uncurry_rightCont (u := fun t ω => dualTotal (N t ω) (X t ω) (Y t ω) * stopInd τ t ω)
    (fun t => ((measurable_dualTotal_comp (h.adapted t).1 (h.adapted t).2.1
      (h.adapted t).2.2).mono (𝓖.le _) le_rfl).mul ((measurable_stopInd hτ t).mono (𝓖.le _) le_rfl))
    fun ω t => ((((continuous_total (hpath ω)).tendsto t).mono_left nhdsWithin_le_nhds)).mul
      (tendsto_stopInd_right τ ω t)

omit hstart in
theorem measurable_killFac_joint {k : ℝ → ℝ} (hk : Continuous k) :
    Measurable fun q : ℝ × Ω => killFac k N X Y τ q.1 q.2 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun r ω => killFac k N X Y τ r ω)
    (fun ω => continuous_killFac (hpath ω) hk)
    fun r => ((stronglyMeasurable_killFac h hpath hk hτ r).mono (𝓖.le _)).measurable

omit hstart in
theorem measurable_killDer_joint {k : ℝ → ℝ} (hk : Continuous k) :
    Measurable fun q : ℝ × Ω => killDer k N X Y τ q.1 q.2 := by
  have e : (fun q : ℝ × Ω => killDer k N X Y τ q.1 q.2) = fun q => -(k q.1 *
      (dualTotal (N q.1.toNNReal q.2) (X q.1.toNNReal q.2) (Y q.1.toNNReal q.2) *
        killInd (τ q.2) q.1)) * killFac k N X Y τ q.1 q.2 :=
    funext fun q => by simp only [killDer, killRate]; ring
  rw [e]
  exact ((hk.measurable.comp measurable_fst).mul (measurable_totalInd_joint h hpath hτ)).neg.mul
    (measurable_killFac_joint h hpath hτ hk)

theorem measurable_dualInteg_joint {k : ℝ → ℝ} (hk : Continuous k) :
    Measurable fun q : FiniteMeasure unitInterval × (ℝ × Ω) =>
      dualInteg D0 k N X Y τ q.1 q.2.1 q.2.2 :=
  (((measurable_killFac_joint h hpath hτ hk).comp measurable_snd).mul
      (measurable_genStop_joint h hpath hstart hτ)).add
    ((measurable_ratioStop_joint h hpath hτ).mul
      ((measurable_killDer_joint h hpath hτ hk).comp measurable_snd))

theorem measurable_fwdInteg_joint {E : ℝ} {κ k : ℝ → ℝ} (hκ : Continuous κ) (hk : Continuous k) :
    Measurable fun q : ℝ × (FiniteMeasure unitInterval × (ℝ × Ω)) =>
      fwdInteg D0 E κ k N X Y τ q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hh : Measurable fun u : ℝ => absorptionRate E κ u := by
    unfold absorptionRate; exact (hκ.measurable.const_mul _)
  exact ((measurable_killFac_joint h hpath hτ hk).comp (measurable_snd.comp measurable_snd)).mul
    (((measurable_pathGenInd_joint h hpath hstart hτ).comp measurable_snd).sub
      (((hh.comp measurable_fst).mul ((measurable_totalInd_joint h hpath hτ).comp
        (measurable_snd.comp measurable_snd))).mul
        ((measurable_pathRatio_joint h hpath).comp measurable_snd)))

end Joint

/-- **The forward process clamped at `a₀ > 0` is jointly measurable** (all paths continuous). -/
theorem measurable_muHat {Ω : Type*} [MeasurableSpace Ω] {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (hmeas : ∀ t, 0 < t → Measurable (μ t)) (hcont : ∀ ω, ContinuousOn (fun t => μ t ω) (Ioi 0))
    {a0 : ℝ} (ha0 : 0 < a0) : Measurable fun q : ℝ × Ω => μ (max q.1 a0) q.2 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun s ω => μ (max s a0) ω)
    (fun ω => (hcont ω).comp_continuous (continuous_id.max continuous_const)
      fun _ => lt_of_lt_of_le ha0 (le_max_right _ _))
    fun _ => hmeas _ (lt_of_lt_of_le ha0 (le_max_right _ _))

theorem measurable_mass : Measurable fun ν : FiniteMeasure unitInterval =>
    (ν : Measure unitInterval).real univ :=
  continuous_measureReal_univ.measurable

end BlockBand.Transmission.LawDuality
