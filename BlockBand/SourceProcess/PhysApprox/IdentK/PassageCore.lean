module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.Complex.Basic

/-!
# Generic fdd passage for generator processes

The drift-free form of the passage: the time integral is read off the observables at single
times, by Fubini and dominated convergence in time, so no separate fdd lemma for integrals is
needed.

Generic setting (Mathlib only). Measures: finite measures `P n` on `Ω n` (the prelimit laws,
possibly on varying spaces) and a finite measure `Q` on `Ω'` (the limit). Observables
`obsN n i t`, `obs i t : ℂ` indexed by `i : I` and time `t : ℝ≥0`, jointly measurable in
`(t, ω)`. `B : Set ℝ≥0` is a countable set of excluded times (the birth times), `0 ∉ B`.

* `IsFddOff B P obsN Q obs`: for every finite family of indices and times off `B` and every
  bounded continuous real test `ψ`, `∫ ψ(obsN n) dP n → ∫ ψ(obs) dQ` (the form of
  `IsCapFddLimitAll` after `condObsTestAll_eq`).
* `IsFddOff.tendsto_complex`: the same for bounded continuous complex tests.
* `xv c o t`: the coordinate vector `(o (c k) t)_{k : κ}` (`κ` finite).
* `mgen c f g o t = f_t(x_t, x_0) − ∫_{(0,t]} g_r(x_r, x_0) dr`.
* **`IsFddOff.tendsto_test_mgen`**: for `f_t, g_t` continuous and uniformly bounded, `g` jointly
  measurable, and times `s, t, u_l ∉ B`, the tested increments
  `∫ ψ(obs at u) • (mgen t − mgen s)` converge (fdd for the `f`-terms; Fubini and dominated
  convergence in `r`, off the null set `B`, for the integral terms).
* `integrable_mgen`: integrability at every time.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.Core

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

section Fdd

variable {I : Type*} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {Ω' : Type*}
  [MeasurableSpace Ω']

/-- Indexed fdd convergence off `B`. -/
def IsFddOff (B : Set ℝ≥0) (P : (n : ℕ) → Measure (Ω n)) (obsN : (n : ℕ) → I → ℝ≥0 → Ω n → ℂ)
    (Q : Measure Ω') (obs : I → ℝ≥0 → Ω' → ℂ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (i : ι → I) (u : ι → ℝ≥0), (∀ l, u l ∉ B) →
    ∀ ψ : BoundedContinuousFunction (ι → ℂ) ℝ,
      Tendsto (fun n => ∫ ω, ψ (fun l => obsN n (i l) (u l) ω) ∂P n) atTop
        (𝓝 (∫ ω, ψ (fun l => obs (i l) (u l) ω) ∂Q))

variable {B : Set ℝ≥0} {P : (n : ℕ) → Measure (Ω n)} {obsN : (n : ℕ) → I → ℝ≥0 → Ω n → ℂ}
  {Q : Measure Ω'} {obs : I → ℝ≥0 → Ω' → ℂ}

theorem IsFddOff.tendsto_mass (h : IsFddOff B P obsN Q obs) :
    Tendsto (fun n => (P n).real univ) atTop (𝓝 (Q.real univ)) := by
  have := h Empty (fun l => l.elim) (fun l => l.elim) (fun l => l.elim)
    (BoundedContinuousFunction.const _ 1)
  simpa using this

theorem IsFddOff.exists_mass_le (h : IsFddOff B P obsN Q obs) :
    ∃ M : ℝ, ∀ n, (P n).real univ ≤ M := by
  obtain ⟨M, hM⟩ := h.tendsto_mass.bddAbove_range
  exact ⟨M, fun n => hM ⟨n, rfl⟩⟩

theorem integrable_test {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {o : I → ℝ≥0 → α → ℂ} (ho : ∀ i u, Measurable (o i u)) {ι : Type*} [Countable ι] (i : ι → I)
    (u : ι → ℝ≥0) {g : (ι → ℂ) → ℂ} (hg : Continuous g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    Integrable (fun ω => g (fun l => o (i l) (u l) ω)) μ :=
  Integrable.of_bound
    (hg.measurable.comp (Measurable.of_eval fun l => ho (i l) (u l))).aestronglyMeasurable
    C (Eventually.of_forall fun _ => hC _)

/-- Complex-valued bounded continuous tests. -/
theorem IsFddOff.tendsto_complex [∀ n, IsFiniteMeasure (P n)] [IsFiniteMeasure Q]
    (h : IsFddOff B P obsN Q obs) (hmN : ∀ n i u, Measurable (obsN n i u))
    (hm : ∀ i u, Measurable (obs i u)) {ι : Type} [Fintype ι] (i : ι → I) (u : ι → ℝ≥0)
    (hu : ∀ l, u l ∉ B) (g : (ι → ℂ) → ℂ) (hg : Continuous g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    Tendsto (fun n => ∫ ω, g (fun l => obsN n (i l) (u l) ω) ∂P n) atTop
      (𝓝 (∫ ω, g (fun l => obs (i l) (u l) ω) ∂Q)) := by
  have hre := h ι i u hu (BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (g x).re) (Complex.continuous_re.comp hg) C
    (fun x => (Complex.abs_re_le_norm _).trans (hC x)))
  have him := h ι i u hu (BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (g x).im) (Complex.continuous_im.comp hg) C
    (fun x => (Complex.abs_im_le_norm _).trans (hC x)))
  simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroup] at hre him
  have key := ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const Complex.I)
  convert key using 2
  · exact (integral_re_add_im (integrable_test (P _) (hmN _) i u hg hC)).symm
  · exact (integral_re_add_im (integrable_test Q hm i u hg hC)).symm

/-! ## Generator processes of observables -/

variable {κ : Type}

/-- The coordinate vector `(o (c k) t)_k`. -/
def xv {α : Type*} (c : κ → I) (o : I → ℝ≥0 → α → ℂ) (t : ℝ≥0) (ω : α) : κ → ℂ :=
  fun k => o (c k) t ω

/-- `f_t(x_t, x_0) − ∫_0^t g_r(x_r, x_0) dr`. -/
def mgen {α : Type*} (c : κ → I) (f g : ℝ≥0 → (κ → ℂ) → (κ → ℂ) → ℂ)
    (o : I → ℝ≥0 → α → ℂ) (t : ℝ≥0) (ω : α) : ℂ :=
  f t (xv c o t ω) (xv c o 0 ω) -
    ∫ r in Ioc (0 : ℝ) t, g r.toNNReal (xv c o r.toNNReal ω) (xv c o 0 ω)

theorem measurable_xv {α : Type*} [MeasurableSpace α] {o : I → ℝ≥0 → α → ℂ}
    (ho : ∀ i, Measurable (Function.uncurry (o i))) (c : κ → I) :
    Measurable fun q : ℝ × α => xv c o q.1.toNNReal q.2 :=
  Measurable.of_eval fun k => (ho (c k)).comp
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)

theorem measurable_xv0 {α : Type*} [MeasurableSpace α] {o : I → ℝ≥0 → α → ℂ}
    (ho : ∀ i, Measurable (Function.uncurry (o i))) (c : κ → I) (t : ℝ≥0) :
    Measurable (xv c o t) :=
  Measurable.of_eval fun k => (ho (c k)).comp (measurable_const.prodMk measurable_id)

theorem measurable_integrand {α : Type*} [MeasurableSpace α] {o : I → ℝ≥0 → α → ℂ}
    (ho : ∀ i, Measurable (Function.uncurry (o i))) (c : κ → I)
    {g : ℝ≥0 → (κ → ℂ) → (κ → ℂ) → ℂ}
    (hgm : Measurable fun q : ℝ≥0 × (κ → ℂ) × (κ → ℂ) => g q.1 q.2.1 q.2.2) :
    Measurable fun q : ℝ × α => g q.1.toNNReal (xv c o q.1.toNNReal q.2) (xv c o 0 q.2) :=
  hgm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
    ((measurable_xv ho c).prodMk ((measurable_xv0 ho c 0).comp measurable_snd)))

theorem measurable_obsTest {α : Type*} [MeasurableSpace α] {o : I → ℝ≥0 → α → ℂ}
    (ho : ∀ i, Measurable (Function.uncurry (o i))) {m : ℕ} (i : Fin m → I) (u : Fin m → ℝ≥0)
    (ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ) :
    Measurable fun ω => ψ (fun l => o (i l) (u l) ω) :=
  ψ.continuous.measurable.comp (Measurable.of_eval fun l =>
    (ho (i l)).comp (measurable_const.prodMk measurable_id))

variable {c : κ → I} [Fintype κ]

/-- A test against a bounded continuous function of the state at one time `v ∉ B`. -/
theorem IsFddOff.tendsto_state [∀ n, IsFiniteMeasure (P n)] [IsFiniteMeasure Q]
    (h : IsFddOff B P obsN Q obs) (hmN : ∀ n i u, Measurable (obsN n i u))
    (hm : ∀ i u, Measurable (obs i u)) (h0 : (0 : ℝ≥0) ∉ B) {m : ℕ} (i : Fin m → I)
    (u : Fin m → ℝ≥0) (hu : ∀ l, u l ∉ B) (ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ)
    {v : ℝ≥0} (hv : v ∉ B) {k : (κ → ℂ) × (κ → ℂ) → ℂ} (hk : Continuous k) {C : ℝ}
    (hC : ∀ p, ‖k p‖ ≤ C) :
    Tendsto (fun n => ∫ ω, ψ (fun l => obsN n (i l) (u l) ω) •
        k (xv c (obsN n) v ω, xv c (obsN n) 0 ω) ∂P n) atTop
      (𝓝 (∫ ω, ψ (fun l => obs (i l) (u l) ω) • k (xv c obs v ω, xv c obs 0 ω) ∂Q)) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  let ii : Fin m ⊕ (κ ⊕ κ) → I := Sum.elim i (Sum.elim c c)
  let uu : Fin m ⊕ (κ ⊕ κ) → ℝ≥0 := Sum.elim u (Sum.elim (fun _ => v) (fun _ => 0))
  have huu : ∀ l, uu l ∉ B := by
    rintro (l | l | l)
    · exact hu l
    · exact hv
    · exact h0
  let g : (Fin m ⊕ (κ ⊕ κ) → ℂ) → ℂ := fun y =>
    (ψ (fun l => y (Sum.inl l)) : ℂ) *
      k (fun j => y (Sum.inr (Sum.inl j)), fun j => y (Sum.inr (Sum.inr j)))
  have hg : Continuous g := by
    refine (Complex.continuous_ofReal.comp (ψ.continuous.comp ?_)).mul (hk.comp ?_)
    · exact continuous_pi fun l => continuous_apply _
    · exact (continuous_pi fun j => continuous_apply _).prodMk
        (continuous_pi fun j => continuous_apply _)
  have hgC : ∀ y, ‖g y‖ ≤ ‖ψ‖ * C := fun y => by
    simp only [g, norm_mul, Complex.norm_real]
    exact mul_le_mul (ψ.norm_coe_le_norm _) (hC _) (norm_nonneg _) (norm_nonneg _)
  have := h.tendsto_complex hmN hm ii uu huu g hg hgC
  simp only [Complex.real_smul]
  exact this

omit [Fintype κ] in
/-- Fubini for the tested time integral. -/
theorem integral_test_integral_swap {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {o : I → ℝ≥0 → α → ℂ} (ho : ∀ i, Measurable (Function.uncurry (o i)))
    {m : ℕ} (i : Fin m → I) (u : Fin m → ℝ≥0) (ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ)
    {g : ℝ≥0 → (κ → ℂ) → (κ → ℂ) → ℂ} {C : ℝ} (hgC : ∀ t x y, ‖g t x y‖ ≤ C)
    (hgm : Measurable fun q : ℝ≥0 × (κ → ℂ) × (κ → ℂ) => g q.1 q.2.1 q.2.2) (t : ℝ≥0) :
    ∫ ω, ψ (fun l => o (i l) (u l) ω) •
        (∫ r in Ioc (0 : ℝ) t, g r.toNNReal (xv c o r.toNNReal ω) (xv c o 0 ω)) ∂μ =
      ∫ r in Ioc (0 : ℝ) t, ∫ ω, ψ (fun l => o (i l) (u l) ω) •
        g r.toNNReal (xv c o r.toNNReal ω) (xv c o 0 ω) ∂μ := by
  simp_rw [← integral_smul]
  refine integral_integral_swap (Integrable.of_bound ?_ (‖ψ‖ * C) ?_)
  · exact (((measurable_obsTest ho i u ψ).comp measurable_fst).smul
      ((measurable_integrand ho c hgm).comp measurable_swap)).aestronglyMeasurable
  · refine Eventually.of_forall fun q => ?_
    simp only [Function.uncurry, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (by simpa using ψ.norm_coe_le_norm _) (hgC _ _ _) (norm_nonneg _)
      (norm_nonneg _)

/-- The time-integral term converges. -/
theorem IsFddOff.tendsto_integral [∀ n, IsFiniteMeasure (P n)] [IsFiniteMeasure Q]
    (h : IsFddOff B P obsN Q obs) (hB : B.Countable)
    (hmN : ∀ n i, Measurable (Function.uncurry (obsN n i)))
    (hm : ∀ i, Measurable (Function.uncurry (obs i))) (h0 : (0 : ℝ≥0) ∉ B) {m : ℕ}
    (i : Fin m → I) (u : Fin m → ℝ≥0) (hu : ∀ l, u l ∉ B)
    (ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ) {g : ℝ≥0 → (κ → ℂ) → (κ → ℂ) → ℂ}
    (hg : ∀ t, Continuous fun p : (κ → ℂ) × (κ → ℂ) => g t p.1 p.2) {C : ℝ}
    (hgC : ∀ t x y, ‖g t x y‖ ≤ C)
    (hgm : Measurable fun q : ℝ≥0 × (κ → ℂ) × (κ → ℂ) => g q.1 q.2.1 q.2.2) (t : ℝ≥0) :
    Tendsto (fun n => ∫ ω, ψ (fun l => obsN n (i l) (u l) ω) •
        (∫ r in Ioc (0 : ℝ) t, g r.toNNReal (xv c (obsN n) r.toNNReal ω) (xv c (obsN n) 0 ω))
        ∂P n) atTop
      (𝓝 (∫ ω, ψ (fun l => obs (i l) (u l) ω) •
        (∫ r in Ioc (0 : ℝ) t, g r.toNNReal (xv c obs r.toNNReal ω) (xv c obs 0 ω)) ∂Q)) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hgC 0 0 0)
  have hmN' : ∀ n i u, Measurable (obsN n i u) := fun n i u =>
    (hmN n i).comp (measurable_const.prodMk measurable_id)
  have hm' : ∀ i u, Measurable (obs i u) := fun i u =>
    (hm i).comp (measurable_const.prodMk measurable_id)
  obtain ⟨M, hM⟩ := h.exists_mass_le
  simp_rw [integral_test_integral_swap (P _) (hmN _) i u ψ hgC hgm t,
    integral_test_integral_swap Q hm i u ψ hgC hgm t]
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖ψ‖ * C * M) (fun n => ?_)
    (integrable_const _) (fun n => Eventually.of_forall fun r => ?_) ?_
  · refine (StronglyMeasurable.integral_prod_right (f := fun (r : ℝ) (ω : Ω n) =>
      ψ (fun l => obsN n (i l) (u l) ω) •
        g r.toNNReal (xv c (obsN n) r.toNNReal ω) (xv c (obsN n) 0 ω)) ?_).aestronglyMeasurable
    exact (((measurable_obsTest (hmN n) i u ψ).comp measurable_snd).smul
      (measurable_integrand (hmN n) c hgm)).stronglyMeasurable
  · refine (norm_integral_le_of_norm_le_const (C := ‖ψ‖ * C)
      (Eventually.of_forall fun ω => ?_)).trans ?_
    · simp only [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (by simpa using ψ.norm_coe_le_norm _) (hgC _ _ _) (norm_nonneg _)
        (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hM n) (mul_nonneg (norm_nonneg _) hC0)
  · have hBR : ((fun x : ℝ≥0 => (x : ℝ)) '' B).Countable := hB.image _
    have hnull : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ (fun x : ℝ≥0 => (x : ℝ)) '' B :=
      measure_eq_zero_iff_ae_notMem.1 (hBR.measure_zero _)
    filter_upwards [ae_restrict_of_ae hnull, ae_restrict_mem measurableSet_Ioc] with r hr hrI
    have hrB : r.toNNReal ∉ B := fun hb => hr ⟨_, hb, Real.coe_toNNReal _ hrI.1.le⟩
    exact h.tendsto_state hmN' hm' h0 i u hu ψ hrB (hg r.toNNReal) (fun p => hgC r.toNNReal p.1 p.2)

theorem integrable_test_state {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {o : I → ℝ≥0 → α → ℂ} (ho : ∀ i, Measurable (Function.uncurry (o i)))
    {m : ℕ} (i : Fin m → I) (u : Fin m → ℝ≥0) (ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ)
    {k : (κ → ℂ) × (κ → ℂ) → ℂ} (hk : Continuous k) {C : ℝ} (hC : ∀ p, ‖k p‖ ≤ C) (v : ℝ≥0) :
    Integrable (fun ω => ψ (fun l => o (i l) (u l) ω) • k (xv c o v ω, xv c o 0 ω)) μ := by
  refine Integrable.of_bound ?_ (‖ψ‖ * C) (Eventually.of_forall fun ω => ?_)
  · exact ((measurable_obsTest ho i u ψ).smul (hk.measurable.comp
      ((measurable_xv0 ho c v).prodMk (measurable_xv0 ho c 0)))).aestronglyMeasurable
  · simp only [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (by simpa using ψ.norm_coe_le_norm _) (hC _) (norm_nonneg _)
      (norm_nonneg _)

omit [Fintype κ] in
theorem integrable_test_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {o : I → ℝ≥0 → α → ℂ} (ho : ∀ i, Measurable (Function.uncurry (o i)))
    {m : ℕ} (i : Fin m → I) (u : Fin m → ℝ≥0) (ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ)
    {g : ℝ≥0 → (κ → ℂ) → (κ → ℂ) → ℂ} {C : ℝ} (hgC : ∀ t x y, ‖g t x y‖ ≤ C)
    (hgm : Measurable fun q : ℝ≥0 × (κ → ℂ) × (κ → ℂ) => g q.1 q.2.1 q.2.2) (t : ℝ≥0) :
    Integrable (fun ω => ψ (fun l => o (i l) (u l) ω) •
      (∫ r in Ioc (0 : ℝ) t, g r.toNNReal (xv c o r.toNNReal ω) (xv c o 0 ω))) μ := by
  refine Integrable.of_bound ?_ (‖ψ‖ * (C * volume.real (Ioc (0 : ℝ) t)))
    (Eventually.of_forall fun ω => ?_)
  · refine ((measurable_obsTest ho i u ψ).aestronglyMeasurable.smul ?_)
    exact (StronglyMeasurable.integral_prod_left (μ := volume.restrict (Ioc (0 : ℝ) t))
      (f := fun (r : ℝ) (ω : α) => g r.toNNReal (xv c o r.toNNReal ω) (xv c o 0 ω))
      (measurable_integrand ho c hgm).stronglyMeasurable).aestronglyMeasurable
  · simp only [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (by simpa using ψ.norm_coe_le_norm _)
      (norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top fun r _ => hgC _ _ _)
      (norm_nonneg _) (norm_nonneg _)

theorem integral_test_mgen_sub {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {o : I → ℝ≥0 → α → ℂ} (ho : ∀ i, Measurable (Function.uncurry (o i)))
    {m : ℕ} (i : Fin m → I) (u : Fin m → ℝ≥0) (ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ)
    {f g : ℝ≥0 → (κ → ℂ) → (κ → ℂ) → ℂ}
    (hf : ∀ t, Continuous fun p : (κ → ℂ) × (κ → ℂ) => f t p.1 p.2) {C : ℝ}
    (hfC : ∀ t x y, ‖f t x y‖ ≤ C) (hgC : ∀ t x y, ‖g t x y‖ ≤ C)
    (hgm : Measurable fun q : ℝ≥0 × (κ → ℂ) × (κ → ℂ) => g q.1 q.2.1 q.2.2) (s t : ℝ≥0) :
    ∫ ω, ψ (fun l => o (i l) (u l) ω) • (mgen c f g o t ω - mgen c f g o s ω) ∂μ =
      ((∫ ω, ψ (fun l => o (i l) (u l) ω) • f t (xv c o t ω) (xv c o 0 ω) ∂μ) -
        ∫ ω, ψ (fun l => o (i l) (u l) ω) •
          (∫ r in Ioc (0 : ℝ) t, g r.toNNReal (xv c o r.toNNReal ω) (xv c o 0 ω)) ∂μ) -
      ((∫ ω, ψ (fun l => o (i l) (u l) ω) • f s (xv c o s ω) (xv c o 0 ω) ∂μ) -
        ∫ ω, ψ (fun l => o (i l) (u l) ω) •
          (∫ r in Ioc (0 : ℝ) s, g r.toNNReal (xv c o r.toNNReal ω) (xv c o 0 ω)) ∂μ) := by
  have hA : ∀ v : ℝ≥0, Integrable (fun ω => ψ (fun l => o (i l) (u l) ω) •
      f v (xv c o v ω) (xv c o 0 ω)) μ := fun v =>
    integrable_test_state (c := c) μ ho i u ψ (hf v) (fun p => hfC v p.1 p.2) v
  have hI := fun v : ℝ≥0 => integrable_test_integral (c := c) μ ho i u ψ hgC hgm v
  rw [← integral_sub (hA t) (hI t), ← integral_sub (hA s) (hI s)]
  have e := integral_sub ((hA t).sub (hI t)) ((hA s).sub (hI s))
  simp only [Pi.sub_apply] at e
  rw [← e]
  congr 1
  funext ω
  simp only [mgen, smul_sub]

/-- A generator process with bounded coefficients is integrable at every time. -/
theorem integrable_mgen {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {o : I → ℝ≥0 → α → ℂ} (ho : ∀ i, Measurable (Function.uncurry (o i)))
    {f g : ℝ≥0 → (κ → ℂ) → (κ → ℂ) → ℂ}
    (hf : ∀ t, Continuous fun p : (κ → ℂ) × (κ → ℂ) => f t p.1 p.2) {C : ℝ}
    (hfC : ∀ t x y, ‖f t x y‖ ≤ C) (hgC : ∀ t x y, ‖g t x y‖ ≤ C)
    (hgm : Measurable fun q : ℝ≥0 × (κ → ℂ) × (κ → ℂ) => g q.1 q.2.1 q.2.2) (t : ℝ≥0) :
    Integrable (mgen c f g o t) μ := by
  refine Integrable.of_bound ?_ (C + C * volume.real (Ioc (0 : ℝ) t))
    (Eventually.of_forall fun ω => ?_)
  · refine (((hf t).measurable.comp ((measurable_xv0 ho c t).prodMk
      (measurable_xv0 ho c 0))).aestronglyMeasurable).sub ?_
    exact (StronglyMeasurable.integral_prod_left (μ := volume.restrict (Ioc (0 : ℝ) t))
      (f := fun (r : ℝ) (ω : α) => g r.toNNReal (xv c o r.toNNReal ω) (xv c o 0 ω))
      (measurable_integrand ho c hgm).stronglyMeasurable).aestronglyMeasurable
  · exact (norm_sub_le _ _).trans (add_le_add (hfC _ _ _)
      (norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top fun r _ => hgC _ _ _))

/-- **Tested increments of a generator process converge.** -/
theorem IsFddOff.tendsto_test_mgen [∀ n, IsFiniteMeasure (P n)] [IsFiniteMeasure Q]
    (h : IsFddOff B P obsN Q obs) (hB : B.Countable)
    (hmN : ∀ n i, Measurable (Function.uncurry (obsN n i)))
    (hm : ∀ i, Measurable (Function.uncurry (obs i))) (h0 : (0 : ℝ≥0) ∉ B) {m : ℕ}
    (i : Fin m → I) (u : Fin m → ℝ≥0) (hu : ∀ l, u l ∉ B)
    (ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ) {f g : ℝ≥0 → (κ → ℂ) → (κ → ℂ) → ℂ}
    (hf : ∀ t, Continuous fun p : (κ → ℂ) × (κ → ℂ) => f t p.1 p.2)
    (hg : ∀ t, Continuous fun p : (κ → ℂ) × (κ → ℂ) => g t p.1 p.2) {C : ℝ}
    (hfC : ∀ t x y, ‖f t x y‖ ≤ C) (hgC : ∀ t x y, ‖g t x y‖ ≤ C)
    (hgm : Measurable fun q : ℝ≥0 × (κ → ℂ) × (κ → ℂ) => g q.1 q.2.1 q.2.2) {s t : ℝ≥0}
    (hs : s ∉ B) (ht : t ∉ B) :
    Tendsto (fun n => ∫ ω, ψ (fun l => obsN n (i l) (u l) ω) •
        (mgen c f g (obsN n) t ω - mgen c f g (obsN n) s ω) ∂P n) atTop
      (𝓝 (∫ ω, ψ (fun l => obs (i l) (u l) ω) • (mgen c f g obs t ω - mgen c f g obs s ω) ∂Q)) := by
  have hmN' : ∀ n i u, Measurable (obsN n i u) := fun n i u =>
    (hmN n i).comp (measurable_const.prodMk measurable_id)
  have hm' : ∀ i u, Measurable (obs i u) := fun i u =>
    (hm i).comp (measurable_const.prodMk measurable_id)
  simp_rw [integral_test_mgen_sub (P _) (hmN _) i u ψ hf hfC hgC hgm s t,
    integral_test_mgen_sub Q hm i u ψ hf hfC hgC hgm s t]
  have hAt := h.tendsto_state (c := c) hmN' hm' h0 i u hu ψ ht (hf t) (fun p => hfC t p.1 p.2)
  have hAs := h.tendsto_state (c := c) hmN' hm' h0 i u hu ψ hs (hf s) (fun p => hfC s p.1 p.2)
  have hIt := h.tendsto_integral (c := c) hB hmN hm h0 i u hu ψ hg hgC hgm t
  have hIs := h.tendsto_integral (c := c) hB hmN hm h0 i u hu ψ hg hgC hgm s
  exact (hAt.sub hIt).sub (hAs.sub hIs)

end Fdd

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.Core
