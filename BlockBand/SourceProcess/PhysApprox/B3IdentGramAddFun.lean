module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Bounded additive functionals under fdd convergence

Abstract measure theory. Measures: arbitrary `μ n` on `Ω n` (eventually probability) and a
probability measure `Q` on `Ω'`. Times are `ℝ≥0`; time integrals are `∫ r in Ioc (0 : ℝ) t`
of `r.toNNReal`, the convention of `genA`/`genProc`.

* `FddConvOff B μ X Q Y`: the fdd of the observables `X n` under `μ n` converge to those of `Y`
  under `Q`, at every finite set of times outside `B`, against every bounded continuous real test
  (the format of `IsCapFddLimitAll`, with `condObsTestAll` written as a `condL` expectation).
* `addFun a j X t ω = ∫_{(0,t]} a(r, (X_{j c}(r, ω))_c) dr`; `augProc a j X`: the observables
  `X` together with the additive functionals `addFun (a k) j X` (index `I ⊕ A`).
* **`fddConvOff_augProc`**: for finite `B`, `μ n` eventually probability,
  jointly measurable observables, `a k` jointly measurable, bounded, continuous in the state at
  every time outside `B`, and, for every `r ∉ B`, `t ↦ a k t (Y(t))` a.s. continuous at `r`:
  `FddConvOff` passes to `augProc`. Joint continuity of `a` is not needed. The integral
  coordinates are tested at the same times `∉ B`. `AddFunFddStmt` (its universe-`0` instance,
  as a `Prop`) and `addFunFddStmt_holds`.
* For iteration: `measurable_uncurry_augProc`, `continuous_addFun` (every `ω`).

Proof: tags `(k + θ_N)/(N + 1)` off `B` (`exists_shift`); the Tonelli `L¹` bound for
the tagging error (`integral_norm_sub_tag_le`); its limit in `n`
by two-time fdd convergence and dominated convergence (`tendsto_tagErr_fdd`), and in `N` for the
limit by a.s. continuity (`tendsto_tagErr_zero`); the tagged vectors are continuous functions of
finitely many grid observations (`tendsto_tagVec`); bounded Lipschitz tests
(`abs_sub_le_lip`, `tendsto_of_approx`); extension to bounded continuous tests by Mathlib's
`MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto` for the image laws
(`tendsto_of_lipschitz`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.AddFun

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {I A : Type*} {κ : Type}

/-- **Fdd convergence off `B`**: for all finitely many coordinates `i l` and times `u l ∉ B`, and
every bounded continuous real test `ψ`, `E_{μ n} ψ(X n) → E_Q ψ(Y)`. -/
def FddConvOff (B : Set ℝ≥0) {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) (X : (n : ℕ) → I → ℝ≥0 → Ω n → ℂ) {Ω' : Type*}
    [MeasurableSpace Ω'] (Q : Measure Ω') (Y : I → ℝ≥0 → Ω' → ℂ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (i : ι → I) (u : ι → ℝ≥0), (∀ l, u l ∉ B) →
    ∀ ψ : BoundedContinuousFunction (ι → ℂ) ℝ,
      Tendsto (fun n => ∫ ω, ψ (fun l => X n (i l) (u l) ω) ∂μ n) atTop
        (𝓝 (∫ ω, ψ (fun l => Y (i l) (u l) ω) ∂Q))

/-- **The additive functional** `∫_{(0,t]} a(r, (X_{j c}(r))_c) dr`. -/
def addFun (a : ℝ≥0 → (κ → ℂ) → ℂ) (j : κ → I) {Ω : Type*} (X : I → ℝ≥0 → Ω → ℂ) (t : ℝ≥0)
    (ω : Ω) : ℂ :=
  ∫ r in Ioc (0 : ℝ) t, a r.toNNReal (fun c => X (j c) r.toNNReal ω)

/-- **The augmented process**: the observables and the additive functionals. -/
def augProc (a : A → ℝ≥0 → (κ → ℂ) → ℂ) (j : κ → I) {Ω : Type*} (X : I → ℝ≥0 → Ω → ℂ) :
    I ⊕ A → ℝ≥0 → Ω → ℂ
  | Sum.inl i => X i
  | Sum.inr k => addFun (a k) j X

/-!
## The shifted grid
-/

/-- The cell index `⌊(N + 1) r⌋₊`. -/
def tagIdx (N : ℕ) (r : ℝ) : ℕ := ⌊((N : ℝ) + 1) * r⌋₊

/-- The tag `(k + θ) / (N + 1)` of the cell `k`. -/
def tagPt (θ : ℝ) (N k : ℕ) : ℝ≥0 := (((k : ℝ) + θ) / ((N : ℝ) + 1)).toNNReal

/-- The tag of the cell containing `r`. -/
def tag (θ : ℝ) (N : ℕ) (r : ℝ) : ℝ≥0 := tagPt θ N (tagIdx N r)

theorem measurable_tagIdx (N : ℕ) : Measurable (tagIdx N) :=
  Measurable.nat_floor (measurable_id.const_mul _)

theorem measurable_tag (θ : ℝ) (N : ℕ) : Measurable (tag θ N) :=
  measurable_from_nat.comp (measurable_tagIdx N)

theorem tagIdx_mono (N : ℕ) {r r' : ℝ} (h : r ≤ r') : tagIdx N r ≤ tagIdx N r' :=
  Nat.floor_mono (mul_le_mul_of_nonneg_left h (by positivity))

theorem dist_tag_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    dist (tag θ N r) r.toNNReal ≤ 1 / ((N : ℝ) + 1) := by
  have hM : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hMr : 0 ≤ ((N : ℝ) + 1) * r := mul_nonneg hM.le hr
  have hk1 : ((tagIdx N r : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * r := Nat.floor_le hMr
  have hk2 : ((N : ℝ) + 1) * r < (tagIdx N r : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [NNReal.dist_eq, tag, tagPt, Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ hr]
  have e : ((tagIdx N r : ℝ) + θ) / ((N : ℝ) + 1) - r =
      ((tagIdx N r : ℝ) + θ - ((N : ℝ) + 1) * r) / ((N : ℝ) + 1) := by
    field_simp
  rw [e, abs_div, abs_of_pos hM, div_le_div_iff_of_pos_right hM, abs_le]
  constructor <;> linarith

theorem tendsto_tag {θ : ℕ → ℝ} (h0 : ∀ N, 0 ≤ θ N) (h1 : ∀ N, θ N ≤ 1) {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun N => tag (θ N) N r) atTop (𝓝 r.toNNReal) :=
  tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
    (fun N => dist_tag_le (h0 N) (h1 N) N hr) tendsto_one_div_add_atTop_nhds_zero_nat)

/-- **A shift avoiding `B`**: no tag `(k + θ)/(N + 1)` lies in the finite set `B`. -/
theorem exists_shift {B : Set ℝ≥0} (hB : B.Finite) (N : ℕ) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ k : ℕ, tagPt θ N k ∉ B := by
  obtain ⟨θ, ⟨h0, h1⟩, hθ⟩ := ((Set.Ioo_infinite (zero_lt_one' ℝ)).sdiff
    (hB.image fun b : ℝ≥0 => Int.fract (((N : ℝ) + 1) * b))).nonempty
  refine ⟨θ, h0, h1, fun k hk => hθ ⟨tagPt θ N k, hk, ?_⟩⟩
  have hM : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have e : ((N : ℝ) + 1) * (((k : ℝ) + θ) / ((N : ℝ) + 1)) = (k : ℝ) + θ := by
    field_simp
  simp only [tagPt]
  rw [Real.coe_toNNReal _ (by positivity), e, Int.fract_natCast_add,
    Int.fract_eq_self.2 ⟨h0.le, h1⟩]

/-- Almost every `r ∈ (0, t]` has `r.toNNReal ∉ B`. -/
theorem ae_off {B : Set ℝ≥0} (hB : B.Finite) (t : ℝ≥0) :
    ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) t)), r ∈ Ioc (0 : ℝ) t ∧ r.toNNReal ∉ B := by
  have h0 : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ ((↑) '' B : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 ((hB.image _).countable.measure_zero _)
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae h0] with r hr hrB
  exact ⟨hr, fun h => hrB ⟨_, h, Real.coe_toNNReal _ hr.1.le⟩⟩

instance isFiniteMeasure_Ioc (t : ℝ) : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
  isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne

/-!
## Measurability
-/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_state {a : ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I} {X : I → ℝ≥0 → Ω → ℂ}
    (ham : Measurable (Function.uncurry a)) (hX : ∀ i, Measurable (Function.uncurry (X i)))
    {α : Type*} [MeasurableSpace α] {g : α → ℝ≥0} (hg : Measurable g) :
    Measurable fun p : α × Ω => a (g p.1) (fun c => X (j c) (g p.1) p.2) :=
  ham.comp ((hg.comp measurable_fst).prodMk (Measurable.of_eval fun c =>
    (hX (j c)).comp ((hg.comp measurable_fst).prodMk measurable_snd)))

theorem measurable_addFun {a : ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I} {X : I → ℝ≥0 → Ω → ℂ}
    (ham : Measurable (Function.uncurry a)) (hX : ∀ i, Measurable (Function.uncurry (X i)))
    (t : ℝ≥0) : Measurable (addFun a j X t) :=
  (StronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc (0 : ℝ) t))
    (measurable_state ham hX measurable_real_toNNReal).stronglyMeasurable).measurable

/-- **Every-`ω` continuity of the additive functional in time.** -/
theorem continuous_addFun {a : ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I} {X : I → ℝ≥0 → Ω → ℂ}
    (ham : Measurable (Function.uncurry a)) (hX : ∀ i, Measurable (Function.uncurry (X i)))
    {L : ℝ} (hL : ∀ r x, ‖a r x‖ ≤ L) (ω : Ω) : Continuous fun t => addFun a j X t ω := by
  set h : ℝ → ℂ := fun r => a r.toNNReal (fun c => X (j c) r.toNNReal ω)
  have hm : Measurable h :=
    (measurable_state ham hX measurable_real_toNNReal).comp (measurable_id.prodMk measurable_const)
  have hii : ∀ x y : ℝ, IntervalIntegrable h volume x y := fun x y =>
    (intervalIntegrable_iff).2 (Measure.integrableOn_of_bounded (M := L)
      (lt_of_le_of_lt (measure_mono Set.uIoc_subset_uIcc) isCompact_uIcc.measure_lt_top).ne
      hm.aestronglyMeasurable (Eventually.of_forall fun r => hL _ _))
  refine ((intervalIntegral.continuous_primitive hii 0).comp NNReal.continuous_coe).congr
    fun t => ?_
  simp only [Function.comp]
  exact intervalIntegral.integral_of_le t.2

/-- **Joint measurability of the additive functional.** -/
theorem measurable_uncurry_addFun {a : ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I}
    {X : I → ℝ≥0 → Ω → ℂ} (ham : Measurable (Function.uncurry a))
    (hX : ∀ i, Measurable (Function.uncurry (X i))) {L : ℝ} (hL : ∀ r x, ‖a r x‖ ≤ L) :
    Measurable (Function.uncurry (addFun a j X)) :=
  measurable_uncurry_of_continuous_of_measurable (continuous_addFun ham hX hL)
    (measurable_addFun ham hX)

/-- **Joint measurability of the augmented process** (so that `fddConvOff_augProc` iterates). -/
theorem measurable_uncurry_augProc {a : A → ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I}
    {X : I → ℝ≥0 → Ω → ℂ} (ham : ∀ k, Measurable (Function.uncurry (a k)))
    (hab : ∀ k, ∃ L : ℝ, ∀ r x, ‖a k r x‖ ≤ L) (hX : ∀ i, Measurable (Function.uncurry (X i))) :
    ∀ q, Measurable (Function.uncurry (augProc a j X q))
  | Sum.inl i => hX i
  | Sum.inr k => measurable_uncurry_addFun (ham k) hX (hab k).choose_spec

end Meas

/-!
## Tagged approximations
-/

/-- The tagged functional `∫_{(0,t]} a(π(r), X(π(r))) dr`. -/
def tagFun (a : ℝ≥0 → (κ → ℂ) → ℂ) (j : κ → I) (θ : ℝ) (N : ℕ) {Ω : Type*}
    (X : I → ℝ≥0 → Ω → ℂ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  ∫ r in Ioc (0 : ℝ) t, a (tag θ N r) (fun c => X (j c) (tag θ N r) ω)

/-- Observables at `u` and additive functionals at `t`. -/
def splitVec (a : A → ℝ≥0 → (κ → ℂ) → ℂ) (j : κ → I) {Ω : Type*} (X : I → ℝ≥0 → Ω → ℂ)
    {ι ι₂ : Type} (i : ι → I) (u : ι → ℝ≥0) (k : ι₂ → A) (t : ι₂ → ℝ≥0) (ω : Ω) :
    ι ⊕ ι₂ → ℂ :=
  Sum.elim (fun l => X (i l) (u l) ω) (fun m => addFun (a (k m)) j X (t m) ω)

/-- Observables at `u` and tagged functionals at `t`. -/
def tagVec (a : A → ℝ≥0 → (κ → ℂ) → ℂ) (j : κ → I) (θ : ℝ) (N : ℕ) {Ω : Type*}
    (X : I → ℝ≥0 → Ω → ℂ) {ι ι₂ : Type} (i : ι → I) (u : ι → ℝ≥0) (k : ι₂ → A)
    (t : ι₂ → ℝ≥0) (ω : Ω) : ι ⊕ ι₂ → ℂ :=
  Sum.elim (fun l => X (i l) (u l) ω) (fun m => tagFun (a (k m)) j θ N X (t m) ω)

theorem measurable_splitVec [Fintype κ] {a : A → ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I} {Ω : Type*}
    [MeasurableSpace Ω] {Z : I → ℝ≥0 → Ω → ℂ} (ham : ∀ k, Measurable (Function.uncurry (a k)))
    (hZ : ∀ i, Measurable (Function.uncurry (Z i))) {ι ι₂ : Type} (i : ι → I) (u : ι → ℝ≥0)
    (k : ι₂ → A) (t : ι₂ → ℝ≥0) : Measurable (splitVec a j Z i u k t) := by
  refine Measurable.of_eval fun q => ?_
  rcases q with l | m
  · exact (hZ (i l)).comp measurable_prodMk_left
  · exact measurable_addFun (ham (k m)) hZ (t m)

theorem measurable_tagVec [Fintype κ] {a : A → ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I} {Ω : Type*}
    [MeasurableSpace Ω] {Z : I → ℝ≥0 → Ω → ℂ} (ham : ∀ k, Measurable (Function.uncurry (a k)))
    (hZ : ∀ i, Measurable (Function.uncurry (Z i))) (θ : ℝ) (N : ℕ) {ι ι₂ : Type} (i : ι → I)
    (u : ι → ℝ≥0) (k : ι₂ → A) (t : ι₂ → ℝ≥0) : Measurable (tagVec a j θ N Z i u k t) := by
  refine Measurable.of_eval fun q => ?_
  rcases q with l | m
  · exact (hZ (i l)).comp measurable_prodMk_left
  · exact (StronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc (0 : ℝ) (t m)))
      (measurable_state (ham (k m)) hZ (measurable_tag θ N)).stronglyMeasurable).measurable

/-- The tagging gap `‖addFun − tagFun‖`. -/
def tagGap (a : ℝ≥0 → (κ → ℂ) → ℂ) (j : κ → I) (θ : ℝ) (N : ℕ) {Ω : Type*}
    (X : I → ℝ≥0 → Ω → ℂ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ‖addFun a j X t ω - tagFun a j θ N X t ω‖

/-- The clamped cell index. -/
def clampIdx (K n : ℕ) : Fin (K + 1) := ⟨min n K, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- A tagged functional as a function of the observations at the grid. -/
def tagObsFun (a : ℝ≥0 → (κ → ℂ) → ℂ) (θ : ℝ) (N K : ℕ) (t : ℝ≥0)
    (x : Fin (K + 1) × κ → ℂ) : ℂ :=
  ∫ r in Ioc (0 : ℝ) t,
    a (tagPt θ N (clampIdx K (tagIdx N r))) (fun c => x (clampIdx K (tagIdx N r), c))

/-- The tagged vector as a function of the observations. -/
def tagPhi (a : A → ℝ≥0 → (κ → ℂ) → ℂ) (θ : ℝ) (N K : ℕ) {ι ι₂ : Type} (k : ι₂ → A)
    (t : ι₂ → ℝ≥0) (x : ι ⊕ (Fin (K + 1) × κ) → ℂ) : ι ⊕ ι₂ → ℂ :=
  Sum.elim (fun l => x (Sum.inl l))
    (fun m => tagObsFun (a (k m)) θ N K (t m) (fun p => x (Sum.inr p)))

theorem tagPhi_eq {a : A → ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I} {θ : ℝ} {N K : ℕ} {Ω : Type*}
    (Z : I → ℝ≥0 → Ω → ℂ) {ι ι₂ : Type} (i : ι → I) (u : ι → ℝ≥0) (k : ι₂ → A)
    (t : ι₂ → ℝ≥0) (ht : ∀ m, tagIdx N (t m) ≤ K) (ω : Ω) :
    tagPhi a θ N K k t (fun q => Z (Sum.elim i (fun p => j p.2) q)
      (Sum.elim u (fun p => tagPt θ N p.1) q) ω) = tagVec a j θ N Z i u k t ω := by
  funext q
  rcases q with l | m
  · rfl
  · simp only [tagPhi, tagVec, Sum.elim_inr, tagObsFun, tagFun]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have e : ((clampIdx K (tagIdx N r) : Fin (K + 1)) : ℕ) = tagIdx N r :=
      min_eq_left ((tagIdx_mono N hr.2).trans (ht m))
    simp only [e]
    rfl

theorem continuous_tagObsFun [Fintype κ] {a : ℝ≥0 → (κ → ℂ) → ℂ} {B : Set ℝ≥0}
    (hac : ∀ r, r ∉ B → Continuous (a r)) {L : ℝ} (hL : ∀ r x, ‖a r x‖ ≤ L) {θ : ℝ} {N : ℕ}
    (hθB : ∀ k, tagPt θ N k ∉ B) (K : ℕ) (t : ℝ≥0) : Continuous (tagObsFun a θ N K t) := by
  refine continuous_of_dominated (bound := fun _ => L) (fun x => ?_)
    (fun x => Eventually.of_forall fun r => hL _ _) (integrable_const _)
    (Eventually.of_forall fun r => ?_)
  · exact ((measurable_from_nat (f := fun n : ℕ => a (tagPt θ N (clampIdx K n))
      (fun c => x (clampIdx K n, c)))).comp (measurable_tagIdx N)).aestronglyMeasurable
  · exact (hac _ (hθB _)).comp
      (continuous_pi fun c => continuous_apply (clampIdx K (tagIdx N r), c))

/-!
## Abstract estimates
-/

section Est

variable {Ω : Type*} [MeasurableSpace Ω]

theorem norm_integral_norm_sub_le {ν : Measure Ω} [IsProbabilityMeasure ν] {F G : Ω → ℂ} {L : ℝ}
    (hF : ∀ ω, ‖F ω‖ ≤ L) (hG : ∀ ω, ‖G ω‖ ≤ L) : ‖∫ ω, ‖F ω - G ω‖ ∂ν‖ ≤ L + L := by
  have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun ω => ‖F ω - G ω‖) (C := L + L)
    (Eventually.of_forall fun ω => by
      rw [norm_norm]; exact (norm_sub_le _ _).trans (add_le_add (hF ω) (hG ω)))
  simpa using this

/-- **The tagging error** (Tonelli). -/
theorem integral_norm_sub_tag_le {ν : Measure Ω} [IsFiniteMeasure ν] {f : ℝ≥0 → Ω → ℂ}
    (hf : Measurable (Function.uncurry f)) {L : ℝ} (hL : ∀ r ω, ‖f r ω‖ ≤ L) {g : ℝ → ℝ≥0}
    (hg : Measurable g) (t : ℝ≥0) :
    ∫ ω, ‖(∫ r in Ioc (0 : ℝ) t, f r.toNNReal ω) - ∫ r in Ioc (0 : ℝ) t, f (g r) ω‖ ∂ν ≤
      ∫ r in Ioc (0 : ℝ) t, ∫ ω, ‖f r.toNNReal ω - f (g r) ω‖ ∂ν := by
  have hF : Measurable fun p : ℝ × Ω => f p.1.toNNReal p.2 :=
    hf.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hG : Measurable fun p : ℝ × Ω => f (g p.1) p.2 :=
    hf.comp ((hg.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable fun p : Ω × ℝ => ‖f p.2.toNNReal p.1 - f (g p.2) p.1‖ :=
    ((hF.comp measurable_swap).sub (hG.comp measurable_swap)).norm
  have hint : Integrable (Function.uncurry fun ω r => ‖f r.toNNReal ω - f (g r) ω‖)
      (ν.prod (volume.restrict (Ioc (0 : ℝ) t))) :=
    Integrable.of_bound hm.aestronglyMeasurable (L + L) (Eventually.of_forall fun p => by
      simp only [Function.uncurry, norm_norm]
      exact (norm_sub_le _ _).trans (add_le_add (hL _ _) (hL _ _)))
  rw [← integral_integral_swap hint]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    hint.integral_prod_left (Eventually.of_forall fun ω => ?_)
  dsimp only
  have hFi : Integrable (fun r => f r.toNNReal ω) (volume.restrict (Ioc (0 : ℝ) t)) :=
    Integrable.of_bound (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable L
      (Eventually.of_forall fun r => hL _ _)
  have hGi : Integrable (fun r => f (g r) ω) (volume.restrict (Ioc (0 : ℝ) t)) :=
    Integrable.of_bound (hG.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable L
      (Eventually.of_forall fun r => hL _ _)
  exact (le_of_eq (congrArg norm (integral_sub hFi hGi).symm)).trans
    (norm_integral_le_integral_norm _)

/-- **The tagging error of the limit vanishes with the mesh** (dominated convergence twice). -/
theorem tendsto_tagErr_zero {Q : Measure Ω} [IsProbabilityMeasure Q] {B : Set ℝ≥0}
    (hB : B.Finite) {θ : ℕ → ℝ} (h0 : ∀ N, 0 ≤ θ N) (h1 : ∀ N, θ N ≤ 1) {f : ℝ≥0 → Ω → ℂ}
    (hf : Measurable (Function.uncurry f)) {L : ℝ} (hL : ∀ r ω, ‖f r ω‖ ≤ L)
    (hc : ∀ r, r ∉ B → ∀ᵐ ω ∂Q, ContinuousAt (fun t => f t ω) r) (t : ℝ≥0) :
    Tendsto (fun N => ∫ r in Ioc (0 : ℝ) t, ∫ ω, ‖f r.toNNReal ω - f (tag (θ N) N r) ω‖ ∂Q)
      atTop (𝓝 0) := by
  have key := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc (0 : ℝ) t))
    (F := fun N r => ∫ ω, ‖f r.toNNReal ω - f (tag (θ N) N r) ω‖ ∂Q) (f := fun _ => (0 : ℝ))
    (fun _ => L + L) (fun N => ?_) (integrable_const _)
    (fun N => Eventually.of_forall fun r =>
      norm_integral_norm_sub_le (fun ω => hL _ ω) (fun ω => hL _ ω)) ?_
  · simpa only [integral_zero] using key
  · exact (StronglyMeasurable.integral_prod_right' (ν := Q)
      (f := fun p : ℝ × Ω => ‖f p.1.toNNReal p.2 - f (tag (θ N) N p.1) p.2‖)
      (((hf.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)).sub
        (hf.comp (((measurable_tag (θ N) N).comp measurable_fst).prodMk
          measurable_snd))).norm.stronglyMeasurable)).aestronglyMeasurable
  · filter_upwards [ae_off hB t] with r ⟨hr, hrB⟩
    have key2 := tendsto_integral_of_dominated_convergence (μ := Q)
      (F := fun N ω => ‖f r.toNNReal ω - f (tag (θ N) N r) ω‖) (f := fun _ => (0 : ℝ))
      (fun _ => L + L) (fun N => ?_) (integrable_const _)
      (fun N => Eventually.of_forall fun ω => by
        rw [norm_norm]; exact (norm_sub_le _ _).trans (add_le_add (hL _ _) (hL _ _))) ?_
    · simpa only [integral_zero] using key2
    · exact ((hf.comp (measurable_const.prodMk measurable_id)).sub
        (hf.comp (measurable_const.prodMk measurable_id))).norm.aestronglyMeasurable
    · filter_upwards [hc _ hrB] with ω hω
      have h2 := (hω.tendsto.comp (tendsto_tag h0 h1 hr.1.le))
      have h3 : Tendsto (fun N => f r.toNNReal ω - f (tag (θ N) N r) ω) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := f r.toNNReal ω)).sub h2
      simpa using h3.norm

/-- **Lipschitz tests**: the change of a Lipschitz test when the functionals are tagged. -/
theorem abs_sub_le_lip [Fintype κ] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {a : A → ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I} {Z : I → ℝ≥0 → Ω → ℂ}
    (hZ : ∀ i, Measurable (Function.uncurry (Z i)))
    (ham : ∀ k, Measurable (Function.uncurry (a k))) {Lk : A → ℝ}
    (hLk : ∀ k r x, ‖a k r x‖ ≤ Lk k) (θ : ℝ) (N : ℕ) {ι ι₂ : Type} [Fintype ι] [Fintype ι₂]
    (i : ι → I) (u : ι → ℝ≥0) (k : ι₂ → A) (t : ι₂ → ℝ≥0) {g : (ι ⊕ ι₂ → ℂ) → ℝ} {C : ℝ}
    (hC : ∀ x y, dist (g x) (g y) ≤ C) {Lg : ℝ≥0} (hLg : LipschitzWith Lg g) :
    |∫ ω, g (splitVec a j Z i u k t ω) ∂ν - ∫ ω, g (tagVec a j θ N Z i u k t ω) ∂ν| ≤
      Lg * ∑ m, ∫ r in Ioc (0 : ℝ) (t m), ∫ ω, ‖a (k m) r.toNNReal (fun c => Z (j c) r.toNNReal ω)
        - a (k m) (tag θ N r) (fun c => Z (j c) (tag θ N r) ω)‖ ∂ν := by
  have hS := measurable_splitVec (j := j) ham hZ i u k t
  have hT := measurable_tagVec (j := j) ham hZ θ N i u k t
  have hgi : ∀ {V : Ω → ι ⊕ ι₂ → ℂ}, Measurable V → Integrable (fun ω => g (V ω)) ν :=
    fun {V} hV => Integrable.of_bound (hLg.continuous.measurable.comp hV).aestronglyMeasurable
      (‖g 0‖ + C) (Eventually.of_forall fun ω => by
        have := hC (V ω) 0
        rw [Real.dist_eq] at this
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        linarith [abs_sub_abs_le_abs_sub (g (V ω)) (g 0)])
  have hd : ∀ m, Integrable (tagGap (a (k m)) j θ N Z (t m)) ν := fun m => by
    have hb : ∀ (F : ℝ → ℂ) (_ : ∀ r, ‖F r‖ ≤ Lk (k m)),
        ‖∫ r in Ioc (0 : ℝ) (t m), F r‖ ≤
          Lk (k m) * (volume.restrict (Ioc (0 : ℝ) (t m))).real univ :=
      fun F hF => norm_integral_le_of_norm_le_const (Eventually.of_forall hF)
    refine Integrable.of_bound (((measurable_pi_apply (Sum.inr m)).comp hS).sub
      ((measurable_pi_apply (Sum.inr m)).comp hT)).norm.aestronglyMeasurable
      (Lk (k m) * (volume.restrict (Ioc (0 : ℝ) (t m))).real univ +
        Lk (k m) * (volume.restrict (Ioc (0 : ℝ) (t m))).real univ)
      (Eventually.of_forall fun ω => ?_)
    rw [tagGap, norm_norm]
    exact (norm_sub_le _ _).trans (add_le_add (hb _ fun r => hLk _ _ _) (hb _ fun r => hLk _ _ _))
  have hdD : ∀ m, ∫ ω, tagGap (a (k m)) j θ N Z (t m) ω ∂ν ≤
      ∫ r in Ioc (0 : ℝ) (t m), ∫ ω, ‖a (k m) r.toNNReal
      (fun c => Z (j c) r.toNNReal ω) - a (k m) (tag θ N r) (fun c => Z (j c) (tag θ N r) ω)‖ ∂ν :=
    fun m => by
      unfold tagGap addFun tagFun
      exact integral_norm_sub_tag_le (ν := ν) (f := fun r ω => a (k m) r (fun c => Z (j c) r ω))
        (measurable_state (ham (k m)) hZ measurable_id) (fun r ω => hLk _ _ _)
        (measurable_tag θ N) (t m)
  rw [← integral_sub (hgi hS) (hgi hT), ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpt : ∀ ω, ‖g (splitVec a j Z i u k t ω) - g (tagVec a j θ N Z i u k t ω)‖ ≤
      Lg * ∑ m, tagGap (a (k m)) j θ N Z (t m) ω := fun ω => by
    rw [← dist_eq_norm]
    refine (hLg.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ Lg.2)
    refine (dist_pi_le_iff (Finset.sum_nonneg fun m _ => norm_nonneg _)).2 fun q => ?_
    rcases q with l | m
    · simp only [splitVec, tagVec, Sum.elim_inl, dist_self]
      exact Finset.sum_nonneg fun m _ => norm_nonneg _
    · simp only [splitVec, tagVec, Sum.elim_inr, dist_eq_norm]
      exact Finset.single_le_sum (f := fun m => tagGap (a (k m)) j θ N Z (t m) ω)
        (fun _ _ => norm_nonneg _)
        (Finset.mem_univ m)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    ((integrable_finsetSum _ fun m _ => hd m).const_mul _) (Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul, integral_finsetSum _ fun m _ => hd m]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => hdD m) Lg.2

/-- **An approximation criterion for real sequences.** -/
theorem tendsto_of_approx {x : ℕ → ℝ} {α : ℝ}
    (h : ∀ ε > 0, ∃ (y : ℕ → ℝ) (β : ℝ), Tendsto y atTop (𝓝 β) ∧ |β - α| ≤ ε ∧
      ∀ᶠ n in atTop, |x n - y n| ≤ ε) : Tendsto x atTop (𝓝 α) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨y, β, hy, hβ, hxy⟩ := h (ε / 4) (by positivity)
  filter_upwards [Metric.tendsto_nhds.1 hy (ε / 4) (by positivity), hxy] with n h1 h2
  rw [Real.dist_eq] at h1 ⊢
  calc |x n - α| ≤ |x n - y n| + |y n - β| + |β - α| := by
        have := abs_sub_le (x n) (y n) α
        have := abs_sub_le (y n) β α
        linarith
    _ < ε := by linarith

end Est

/-!
## Bounded Lipschitz tests determine the limit
-/

/-- **Bounded Lipschitz tests suffice** (Mathlib's `tendsto_iff_forall_lipschitz_integral_tendsto`
for the image laws). -/
theorem tendsto_of_lipschitz {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : (n : ℕ) → Measure (Ω n)} (hμ : ∀ n, IsProbabilityMeasure (μ n)) {Ω' : Type*}
    [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q] {Z : (n : ℕ) → Ω n → E}
    {Z' : Ω' → E} (hZ : ∀ n, Measurable (Z n)) (hZ' : Measurable Z')
    (h : ∀ g : E → ℝ, (∃ C, ∀ x y, dist (g x) (g y) ≤ C) → (∃ L, LipschitzWith L g) →
      Tendsto (fun n => ∫ ω, g (Z n ω) ∂μ n) atTop (𝓝 (∫ ω, g (Z' ω) ∂Q)))
    (ψ : BoundedContinuousFunction E ℝ) :
    Tendsto (fun n => ∫ ω, ψ (Z n ω) ∂μ n) atTop (𝓝 (∫ ω, ψ (Z' ω) ∂Q)) := by
  let ν : ℕ → ProbabilityMeasure E := fun n =>
    ⟨(μ n).map (Z n), by have := hμ n; infer_instance⟩
  let ν' : ProbabilityMeasure E := ⟨Q.map Z', inferInstance⟩
  have hc : Tendsto ν atTop (𝓝 ν') := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    intro g hg hL
    have hgc : Continuous g := hL.choose_spec.continuous
    have e : ∀ n, ∫ x, g x ∂(ν n : Measure E) = ∫ ω, g (Z n ω) ∂μ n := fun n =>
      integral_map (hZ n).aemeasurable hgc.aestronglyMeasurable
    have e' : ∫ x, g x ∂(ν' : Measure E) = ∫ ω, g (Z' ω) ∂Q :=
      integral_map hZ'.aemeasurable hgc.aestronglyMeasurable
    rw [e']
    exact (h g hg hL).congr fun n => (e n).symm
  have e : ∀ n, ∫ x, ψ x ∂(ν n : Measure E) = ∫ ω, ψ (Z n ω) ∂μ n := fun n =>
    integral_map (hZ n).aemeasurable ψ.continuous.aestronglyMeasurable
  have e' : ∫ x, ψ x ∂(ν' : Measure E) = ∫ ω, ψ (Z' ω) ∂Q :=
    integral_map hZ'.aemeasurable ψ.continuous.aestronglyMeasurable
  rw [← e']
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hc ψ).congr e

/-!
## The passage
-/

section Passage

variable {B : Set ℝ≥0} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  {μ : (n : ℕ) → Measure (Ω n)} {X : (n : ℕ) → I → ℝ≥0 → Ω n → ℂ} {Ω' : Type*}
  [MeasurableSpace Ω'] {Q : Measure Ω'} {Y : I → ℝ≥0 → Ω' → ℂ}

/-- **Two-time fdd convergence of the tagging error, integrated in time.** -/
theorem tendsto_tagErr_fdd [Fintype κ] (hB : B.Finite) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    [IsProbabilityMeasure Q] {a : ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I}
    (hX : ∀ n i, Measurable (Function.uncurry (X n i))) (ham : Measurable (Function.uncurry a))
    {L : ℝ} (hL : ∀ r x, ‖a r x‖ ≤ L) (hac : ∀ r, r ∉ B → Continuous (a r))
    (hF : FddConvOff B μ X Q Y) {θ : ℝ} {N : ℕ} (hθB : ∀ k, tagPt θ N k ∉ B) (t : ℝ≥0) :
    Tendsto (fun n => ∫ r in Ioc (0 : ℝ) t, ∫ ω, ‖a r.toNNReal (fun c => X n (j c) r.toNNReal ω)
        - a (tag θ N r) (fun c => X n (j c) (tag θ N r) ω)‖ ∂μ n) atTop
      (𝓝 (∫ r in Ioc (0 : ℝ) t, ∫ ω, ‖a r.toNNReal (fun c => Y (j c) r.toNNReal ω)
        - a (tag θ N r) (fun c => Y (j c) (tag θ N r) ω)‖ ∂Q)) := by
  have hT : ∀ r, tag θ N r ∉ B := fun r => hθB _
  refine tendsto_integral_of_dominated_convergence (fun _ => L + L) (fun n => ?_)
    (integrable_const _) (fun n => Eventually.of_forall fun r => ?_) ?_
  · exact (StronglyMeasurable.integral_prod_right' (ν := μ n)
      (f := fun p : ℝ × Ω n => ‖a p.1.toNNReal (fun c => X n (j c) p.1.toNNReal p.2)
        - a (tag θ N p.1) (fun c => X n (j c) (tag θ N p.1) p.2)‖)
      (((measurable_state ham (hX n) measurable_real_toNNReal).sub
        (measurable_state ham (hX n) (measurable_tag θ N))).norm.stronglyMeasurable)
      ).aestronglyMeasurable
  · have := hμ n
    exact norm_integral_norm_sub_le (fun ω => hL _ _) (fun ω => hL _ _)
  · filter_upwards [ae_off hB t] with r ⟨_, hrB⟩
    have hcont : Continuous fun x : κ ⊕ κ → ℂ =>
        ‖a r.toNNReal (fun c => x (Sum.inl c)) - a (tag θ N r) (fun c => x (Sum.inr c))‖ :=
      (((hac _ hrB).comp (continuous_pi fun c => continuous_apply (Sum.inl c))).sub
        ((hac _ (hT r)).comp (continuous_pi fun c => continuous_apply (Sum.inr c)))).norm
    have h := hF (κ ⊕ κ) (Sum.elim j j) (Sum.elim (fun _ => r.toNNReal) fun _ => tag θ N r)
      (by rintro (c | c); exacts [hrB, hT r])
      (BoundedContinuousFunction.ofNormedAddCommGroup _ hcont (L + L) fun x => by
        rw [norm_norm]; exact (norm_sub_le _ _).trans (add_le_add (hL _ _) (hL _ _)))
    exact h

/-- **Fdd convergence of the tagged vectors** (finitely many grid observations). -/
theorem tendsto_tagVec [Fintype κ] {a : A → ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I}
    (hac : ∀ k r, r ∉ B → Continuous (a k r)) {Lk : A → ℝ} (hLk : ∀ k r x, ‖a k r x‖ ≤ Lk k)
    (hF : FddConvOff B μ X Q Y) {θ : ℝ} {N : ℕ} (hθB : ∀ k, tagPt θ N k ∉ B) {ι ι₂ : Type}
    [Fintype ι] [Fintype ι₂] (i : ι → I) (u : ι → ℝ≥0) (hu : ∀ l, u l ∉ B) (k : ι₂ → A)
    (t : ι₂ → ℝ≥0) (ψ : BoundedContinuousFunction (ι ⊕ ι₂ → ℂ) ℝ) :
    Tendsto (fun n => ∫ ω, ψ (tagVec a j θ N (X n) i u k t ω) ∂μ n) atTop
      (𝓝 (∫ ω, ψ (tagVec a j θ N Y i u k t ω) ∂Q)) := by
  set K : ℕ := tagIdx N (Finset.univ.sup t : ℝ≥0)
  have ht : ∀ m, tagIdx N (t m) ≤ K := fun m =>
    tagIdx_mono N (NNReal.coe_le_coe.2 (Finset.le_sup (Finset.mem_univ m)))
  have hΦ : Continuous (tagPhi (ι := ι) a θ N K k t) := by
    refine continuous_pi fun q => ?_
    rcases q with l | m
    · exact continuous_apply (Sum.inl l)
    · exact (continuous_tagObsFun (hac (k m)) (hLk (k m)) hθB K (t m)).comp
        (continuous_pi fun p => continuous_apply (Sum.inr p) :
          Continuous fun x : ι ⊕ (Fin (K + 1) × κ) → ℂ => fun p => x (Sum.inr p))
  have hu' : ∀ q, Sum.elim u (fun p : Fin (K + 1) × κ => tagPt θ N p.1) q ∉ B := by
    rintro (l | p)
    exacts [hu l, hθB _]
  have key := hF _ (Sum.elim i fun p : Fin (K + 1) × κ => j p.2)
    (Sum.elim u fun p : Fin (K + 1) × κ => tagPt θ N p.1) hu' (ψ.compContinuous ⟨_, hΦ⟩)
  have e1 : ∀ n, ∫ ω, ψ (tagVec a j θ N (X n) i u k t ω) ∂μ n =
      ∫ ω, (ψ.compContinuous ⟨_, hΦ⟩) (fun q => X n (Sum.elim i (fun p => j p.2) q)
        (Sum.elim u (fun p => tagPt θ N p.1) q) ω) ∂μ n := fun n => by
    congr 1
    funext ω
    exact congrArg ψ (tagPhi_eq (X n) i u k t ht ω).symm
  have e2 : ∫ ω, ψ (tagVec a j θ N Y i u k t ω) ∂Q =
      ∫ ω, (ψ.compContinuous ⟨_, hΦ⟩) (fun q => Y (Sum.elim i (fun p => j p.2) q)
        (Sum.elim u (fun p => tagPt θ N p.1) q) ω) ∂Q := by
    congr 1
    funext ω
    exact congrArg ψ (tagPhi_eq Y i u k t ht ω).symm
  rw [e2]
  exact key.congr fun n => (e1 n).symm

/-- **The passage for observables and additive functionals** (probability measures). -/
theorem tendsto_splitVec_of_prob [Fintype κ] (hB : B.Finite) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    [IsProbabilityMeasure Q] {a : A → ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I}
    (hX : ∀ n i, Measurable (Function.uncurry (X n i)))
    (hY : ∀ i, Measurable (Function.uncurry (Y i)))
    (ham : ∀ k, Measurable (Function.uncurry (a k))) (hab : ∀ k, ∃ L : ℝ, ∀ r x, ‖a k r x‖ ≤ L)
    (hac : ∀ k r, r ∉ B → Continuous (a k r))
    (hYc : ∀ k r, r ∉ B → ∀ᵐ ω ∂Q, ContinuousAt (fun t => a k t (fun c => Y (j c) t ω)) r)
    (hF : FddConvOff B μ X Q Y) {ι ι₂ : Type} [Fintype ι] [Fintype ι₂] (i : ι → I)
    (u : ι → ℝ≥0) (hu : ∀ l, u l ∉ B) (k : ι₂ → A) (t : ι₂ → ℝ≥0)
    (ψ : BoundedContinuousFunction (ι ⊕ ι₂ → ℂ) ℝ) :
    Tendsto (fun n => ∫ ω, ψ (splitVec a j (X n) i u k t ω) ∂μ n) atTop
      (𝓝 (∫ ω, ψ (splitVec a j Y i u k t ω) ∂Q)) := by
  choose Lk hLk using hab
  choose θ hθ0 hθ1 hθB using exists_shift hB
  refine tendsto_of_lipschitz hμ (fun n => measurable_splitVec ham (hX n) i u k t)
    (measurable_splitVec ham hY i u k t) ?_ ψ
  rintro g ⟨C, hC⟩ ⟨Lg, hLg⟩
  set e : ℕ → ι₂ → ℝ := fun N m => ∫ r in Ioc (0 : ℝ) (t m), ∫ ω, ‖a (k m) r.toNNReal
    (fun c => Y (j c) r.toNNReal ω) - a (k m) (tag (θ N) N r)
      (fun c => Y (j c) (tag (θ N) N r) ω)‖ ∂Q
  have he : ∀ m, Tendsto (fun N => e N m) atTop (𝓝 0) := fun m =>
    tendsto_tagErr_zero (f := fun r ω => a (k m) r (fun c => Y (j c) r ω)) hB
      (fun N => (hθ0 N).le) (fun N => (hθ1 N).le) (measurable_state (ham (k m)) hY measurable_id)
      (fun r ω => hLk _ _ _) (hYc (k m)) (t m)
  have hsum : Tendsto (fun N => (Lg : ℝ) * ∑ m, e N m) atTop (𝓝 0) := by
    simpa using (tendsto_finsetSum Finset.univ fun m _ => he m).const_mul (Lg : ℝ)
  refine tendsto_of_approx fun ε hε => ?_
  obtain ⟨N, hN⟩ := (hsum.eventually_lt_const hε).exists
  have hD : ∀ m, Tendsto (fun n => ∫ r in Ioc (0 : ℝ) (t m), ∫ ω, ‖a (k m) r.toNNReal
      (fun c => X n (j c) r.toNNReal ω) - a (k m) (tag (θ N) N r)
        (fun c => X n (j c) (tag (θ N) N r) ω)‖ ∂μ n) atTop (𝓝 (e N m)) := fun m =>
    tendsto_tagErr_fdd hB hμ hX (ham (k m)) (hLk (k m)) (hac (k m)) hF (hθB N) (t m)
  have hDs := (tendsto_finsetSum Finset.univ fun m _ => hD m).const_mul (Lg : ℝ)
  refine ⟨fun n => ∫ ω, g (tagVec a j (θ N) N (X n) i u k t ω) ∂μ n,
    ∫ ω, g (tagVec a j (θ N) N Y i u k t ω) ∂Q,
    tendsto_tagVec hac hLk hF (hθB N) i u hu k t
      (BoundedContinuousFunction.mkOfBound ⟨g, hLg.continuous⟩ C hC), ?_, ?_⟩
  · rw [abs_sub_comm]
    exact (abs_sub_le_lip hY ham hLk (θ N) N i u k t hC hLg).trans hN.le
  · filter_upwards [hDs.eventually_lt_const hN] with n hn
    have := hμ n
    exact (abs_sub_le_lip (hX n) ham hLk (θ N) N i u k t hC hLg).trans hn.le

theorem augProc_of_isLeft {a : A → ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I} {Ω₀ : Type*}
    (Z : I → ℝ≥0 → Ω₀ → ℂ) (x : I ⊕ A) (h : x.isLeft) : augProc a j Z x = Z (x.getLeft h) := by
  cases x with
  | inl i => rfl
  | inr k => simp at h

theorem augProc_of_isRight {a : A → ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I} {Ω₀ : Type*}
    (Z : I → ℝ≥0 → Ω₀ → ℂ) (x : I ⊕ A) (h : x.isRight) :
    augProc a j Z x = addFun (a (x.getRight h)) j Z := by
  cases x with
  | inl i => simp at h
  | inr k => rfl

theorem augProc_eq_splitVec {a : A → ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I} {Ω₀ : Type*}
    (Z : I → ℝ≥0 → Ω₀ → ℂ) {ι : Type} (p : ι → I ⊕ A) (u : ι → ℝ≥0) (ω : Ω₀) :
    (fun l => augProc a j Z (p l) (u l) ω) = fun l =>
      splitVec a j Z (fun l : {l // (p l).isLeft = true} => (p l.1).getLeft l.2) (fun l => u l.1)
        (fun l : {l // ¬(p l).isLeft = true} => (p l.1).getRight (Sum.not_isLeft.1 l.2))
        (fun l => u l.1) ω ((Equiv.sumCompl fun l => (p l).isLeft = true).symm l) := by
  funext l
  by_cases h : (p l).isLeft = true
  · rw [Equiv.sumCompl_symm_apply_of_pos (p := fun l => (p l).isLeft = true) h]
    simp only [splitVec, Sum.elim_inl]
    rw [augProc_of_isLeft Z (p l) h]
  · rw [Equiv.sumCompl_symm_apply_of_neg (p := fun l => (p l).isLeft = true) h]
    simp only [splitVec, Sum.elim_inr]
    rw [augProc_of_isRight Z (p l) (Sum.not_isLeft.1 h)]

/-- **The passage of fdd convergence to the augmented process, for probability measures.** -/
theorem fddConvOff_augProc_of_prob [Fintype κ] (hB : B.Finite)
    (hμ : ∀ n, IsProbabilityMeasure (μ n))
    [IsProbabilityMeasure Q] {a : A → ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I}
    (hX : ∀ n i, Measurable (Function.uncurry (X n i)))
    (hY : ∀ i, Measurable (Function.uncurry (Y i)))
    (ham : ∀ k, Measurable (Function.uncurry (a k))) (hab : ∀ k, ∃ L : ℝ, ∀ r x, ‖a k r x‖ ≤ L)
    (hac : ∀ k r, r ∉ B → Continuous (a k r))
    (hYc : ∀ k r, r ∉ B → ∀ᵐ ω ∂Q, ContinuousAt (fun t => a k t (fun c => Y (j c) t ω)) r)
    (hF : FddConvOff B μ X Q Y) :
    FddConvOff B μ (fun n => augProc a j (X n)) Q (augProc a j Y) := by
  intro ι _ p u hu ψ
  let e := Equiv.sumCompl fun l => (p l).isLeft = true
  let R : ({l // (p l).isLeft = true} ⊕ {l // ¬(p l).isLeft = true} → ℂ) → (ι → ℂ) :=
    fun x l => x (e.symm l)
  have hR : Continuous R := continuous_pi fun l => continuous_apply _
  have key := tendsto_splitVec_of_prob hB hμ hX hY ham hab hac hYc hF
    (fun l : {l // (p l).isLeft = true} => (p l.1).getLeft l.2) (fun l => u l.1)
    (fun l => hu l.1)
    (fun l : {l // ¬(p l).isLeft = true} => (p l.1).getRight (Sum.not_isLeft.1 l.2))
    (fun l => u l.1) (ψ.compContinuous ⟨R, hR⟩)
  have e1 : ∀ n, ∫ ω, ψ (fun l => augProc a j (X n) (p l) (u l) ω) ∂μ n =
      ∫ ω, (ψ.compContinuous ⟨R, hR⟩) (splitVec a j (X n)
        (fun l : {l // (p l).isLeft = true} => (p l.1).getLeft l.2) (fun l => u l.1)
        (fun l : {l // ¬(p l).isLeft = true} => (p l.1).getRight (Sum.not_isLeft.1 l.2))
        (fun l => u l.1) ω) ∂μ n := fun n => by
    congr 1
    funext ω
    rw [augProc_eq_splitVec (X n) p u ω]
    rfl
  have e2 : ∫ ω, ψ (fun l => augProc a j Y (p l) (u l) ω) ∂Q =
      ∫ ω, (ψ.compContinuous ⟨R, hR⟩) (splitVec a j Y
        (fun l : {l // (p l).isLeft = true} => (p l.1).getLeft l.2) (fun l => u l.1)
        (fun l : {l // ¬(p l).isLeft = true} => (p l.1).getRight (Sum.not_isLeft.1 l.2))
        (fun l => u l.1) ω) ∂Q := by
    congr 1
    funext ω
    rw [augProc_eq_splitVec Y p u ω]
    rfl
  show Tendsto (fun n => ∫ ω, ψ (fun l => augProc a j (X n) (p l) (u l) ω) ∂μ n) atTop
    (𝓝 (∫ ω, ψ (fun l => augProc a j Y (p l) (u l) ω) ∂Q))
  rw [e2]
  exact key.congr fun n => (e1 n).symm

/-- **Bounded additive functionals adjoin to fdd convergence** off a finite set. -/
theorem fddConvOff_augProc [Fintype κ] (hB : B.Finite)
    (hμ : ∀ᶠ n in atTop, IsProbabilityMeasure (μ n))
    [IsProbabilityMeasure Q] {a : A → ℝ≥0 → (κ → ℂ) → ℂ} {j : κ → I}
    (hX : ∀ n i, Measurable (Function.uncurry (X n i)))
    (hY : ∀ i, Measurable (Function.uncurry (Y i)))
    (ham : ∀ k, Measurable (Function.uncurry (a k))) (hab : ∀ k, ∃ L : ℝ, ∀ r x, ‖a k r x‖ ≤ L)
    (hac : ∀ k r, r ∉ B → Continuous (a k r))
    (hYc : ∀ k r, r ∉ B → ∀ᵐ ω ∂Q, ContinuousAt (fun t => a k t (fun c => Y (j c) t ω)) r)
    (hF : FddConvOff B μ X Q Y) :
    FddConvOff B μ (fun n => augProc a j (X n)) Q (augProc a j Y) := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hμ
  have hF' : FddConvOff B (fun n => μ (n + N0)) (fun n => X (n + N0)) Q Y :=
    fun ι _ i u hu ψ => (tendsto_add_atTop_iff_nat
      (f := fun n => ∫ ω, ψ (fun l => X n (i l) (u l) ω) ∂μ n) N0).2 (hF ι i u hu ψ)
  have h := fddConvOff_augProc_of_prob (Ω := fun n => Ω (n + N0)) hB
    (fun n => hN0 _ (Nat.le_add_left _ _)) (fun n => hX _) hY ham hab hac hYc hF'
  intro ι _ i u hu ψ
  exact (tendsto_add_atTop_iff_nat
    (f := fun n => ∫ ω, ψ (fun l => augProc a j (X n) (i l) (u l) ω) ∂μ n) N0).1
    (h ι i u hu ψ)

/-- **The statement of `fddConvOff_augProc`** (its universe-`0` instance). -/
def AddFunFddStmt : Prop :=
  ∀ (I A : Type) (κ : Type) [Fintype κ] (B : Set ℝ≥0) (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) (X : (n : ℕ) → I → ℝ≥0 → Ω n → ℂ) (Ω' : Type)
    [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q] (Y : I → ℝ≥0 → Ω' → ℂ)
    (a : A → ℝ≥0 → (κ → ℂ) → ℂ) (j : κ → I),
    B.Finite → (∀ᶠ n in atTop, IsProbabilityMeasure (μ n)) →
    (∀ n i, Measurable (Function.uncurry (X n i))) → (∀ i, Measurable (Function.uncurry (Y i))) →
    (∀ k, Measurable (Function.uncurry (a k))) → (∀ k, ∃ L : ℝ, ∀ r x, ‖a k r x‖ ≤ L) →
    (∀ k r, r ∉ B → Continuous (a k r)) →
    (∀ k r, r ∉ B → ∀ᵐ ω ∂Q, ContinuousAt (fun t => a k t (fun c => Y (j c) t ω)) r) →
    FddConvOff B μ X Q Y →
    FddConvOff B μ (fun n => augProc a j (X n)) Q (augProc a j Y)

theorem addFunFddStmt_holds : AddFunFddStmt :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB hμ hX hY ham hab hac hYc hF =>
    fddConvOff_augProc hB hμ hX hY ham hab hac hYc hF

end Passage

end BlockBand.SourceProcess.PhysApprox.B3.AddFun
