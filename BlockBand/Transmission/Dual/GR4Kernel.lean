module

public import BlockBand.Transmission.Dual.GPolish
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Martingale.Basic

/-!
# Martingales pass to the conditional kernel, core step

Setting: a filtered probability space `(Ω, 𝓖, P)`, a `𝓖₀`-measurable start `ξ : Ω → E` and a
random element `Φ : Ω → Ω₂` of a standard Borel space, with a filtration `𝓕 s = comap (tr s)` on
`Ω₂` (`tr s` = "the path up to `s`") such that `tr s ∘ Φ` is `𝓖 s`-measurable. Let
`κ = condKernel (law (ξ, Φ))`.

**`ae_martingale_condKernel`.** If `N` is an `𝓕`-adapted canonical process, right-continuous in
time at every point, bounded on bounded time intervals, and `N ∘ Φ` has a `𝓖`-martingale version
under `P`, then for `law(ξ)`-a.e. `z`, `N` is an `𝓕`-martingale under `κ z`.

Proof. For fixed `s ≤ t` the two finite kernels
`η_u z = ((κ z).withDensity (N_u + C)).map (tr s)` (`u = s, t`) have the same composition product
with `law(ξ)`: for a measurable `S ⊆ E × Ω₂`, `(law ξ ⊗ η_u)(S) = E_P[N_u(Φ) + C; (ξ, tr s Φ) ∈ S]`
and `{(ξ, tr s Φ) ∈ S} ∈ 𝓖 s` (`lintegral_section`). So `η_s = η_t` a.e.
(`Kernel.ae_eq_of_compProd_eq`; `Ω₂` is countably generated), which is the martingale identity
on all of `𝓕 s` at once. Countably many dense times, then right-continuity and dominated
convergence, give every `s ≤ t`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {E Ω₂ : Type*} [MeasurableSpace E] [MeasurableSpace Ω₂]
  [StandardBorelSpace Ω₂] [Nonempty Ω₂]

/-- The joint law of the start and the path. -/
def jlaw (P : Measure Ω) (ξ : Ω → E) (Φ : Ω → Ω₂) : Measure (E × Ω₂) :=
  P.map fun x => (ξ x, Φ x)

instance (P : Measure Ω) [IsFiniteMeasure P] (ξ : Ω → E) (Φ : Ω → Ω₂) :
    IsFiniteMeasure (jlaw P ξ Φ) := by
  unfold jlaw; infer_instance

/-- **Integrals against the conditional kernel, over a section of a set, are expectations.** -/
theorem lintegral_section {ξ : Ω → E} {Φ : Ω → Ω₂} (hξΦ : Measurable fun x => (ξ x, Φ x))
    {tr : Ω₂ → Ω₂} (htr : Measurable tr) {f : Ω₂ → ℝ≥0∞} (hf : Measurable f)
    {S : Set (E × Ω₂)} (hS : MeasurableSet S) :
    ∫⁻ z, ∫⁻ w in tr ⁻¹' (Prod.mk z ⁻¹' S), f w ∂(jlaw P ξ Φ).condKernel z ∂(jlaw P ξ Φ).fst =
      ∫⁻ x in {x | (ξ x, tr (Φ x)) ∈ S}, f (Φ x) ∂P := by
  have hg : Measurable fun p : E × Ω₂ => (p.1, tr p.2) := measurable_fst.prodMk (htr.comp measurable_snd)
  have hS' : MeasurableSet ((fun p : E × Ω₂ => (p.1, tr p.2)) ⁻¹' S) := hg hS
  have e1 : ∀ z, ∫⁻ w in tr ⁻¹' (Prod.mk z ⁻¹' S), f w ∂(jlaw P ξ Φ).condKernel z =
      ∫⁻ w, ((fun p : E × Ω₂ => (p.1, tr p.2)) ⁻¹' S).indicator (fun p => f p.2) (z, w)
        ∂(jlaw P ξ Φ).condKernel z := fun z => by
    rw [← lintegral_indicator (htr (measurable_prodMk_left hS))]
    rfl
  have hF : Measurable (((fun p : E × Ω₂ => (p.1, tr p.2)) ⁻¹' S).indicator
      (fun p : E × Ω₂ => f p.2)) := (hf.comp measurable_snd).indicator hS'
  simp_rw [e1]
  rw [← Measure.lintegral_compProd hF, Measure.disintegrate, jlaw, lintegral_map hF hξΦ,
    ← lintegral_indicator (show MeasurableSet {x | (ξ x, tr (Φ x)) ∈ S} from (hg.comp hξΦ) hS)]
  rfl

/-- The pushed weighted conditional kernel `z ↦ ((κ z).withDensity g).map tr`. -/
def wker (P : Measure Ω) [IsFiniteMeasure P] (ξ : Ω → E) (Φ : Ω → Ω₂) (g : Ω₂ → ℝ≥0)
    (tr : Ω₂ → Ω₂) : Kernel E Ω₂ :=
  ((jlaw P ξ Φ).condKernel.withDensity fun _ w => (g w : ℝ≥0∞)).map tr

instance (P : Measure Ω) [IsFiniteMeasure P] (ξ : Ω → E) (Φ : Ω → Ω₂) (g : Ω₂ → ℝ≥0)
    (tr : Ω₂ → Ω₂) : IsSFiniteKernel (wker P ξ Φ g tr) := by
  unfold wker; infer_instance

theorem wker_apply {ξ : Ω → E} {Φ : Ω → Ω₂} {g : Ω₂ → ℝ≥0} (hg : Measurable g) {tr : Ω₂ → Ω₂}
    (htr : Measurable tr) (z : E) {A : Set Ω₂} (hA : MeasurableSet A) :
    wker P ξ Φ g tr z A = ∫⁻ w in tr ⁻¹' A, (g w : ℝ≥0∞) ∂(jlaw P ξ Φ).condKernel z := by
  rw [wker, Kernel.map_apply' _ htr _ hA, Kernel.withDensity_apply'
    (f := fun (_ : E) w => (g w : ℝ≥0∞)) _ (show Measurable (Function.uncurry
      fun (_ : E) (w : Ω₂) => (g w : ℝ≥0∞)) from (measurable_coe_nnreal_ennreal.comp hg).comp
        measurable_snd)]

theorem compProd_wker_apply {ξ : Ω → E} {Φ : Ω → Ω₂} (hξΦ : Measurable fun x => (ξ x, Φ x))
    {g : Ω₂ → ℝ≥0} (hg : Measurable g) {tr : Ω₂ → Ω₂} (htr : Measurable tr)
    {S : Set (E × Ω₂)} (hS : MeasurableSet S) :
    ((jlaw P ξ Φ).fst ⊗ₘ wker P ξ Φ g tr) S =
      ∫⁻ x in {x | (ξ x, tr (Φ x)) ∈ S}, (g (Φ x) : ℝ≥0∞) ∂P := by
  rw [Measure.compProd_apply hS]
  simp_rw [wker_apply hg htr _ (measurable_prodMk_left hS)]
  exact lintegral_section hξΦ htr (measurable_coe_nnreal_ennreal.comp hg) hS

variable {tr : ℝ≥0 → Ω₂ → Ω₂} {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)}
  {ξ : Ω → E} {Φ : Ω → Ω₂} {N : ℝ≥0 → Ω₂ → ℝ} {M : ℝ≥0 → Ω → ℝ}

omit [StandardBorelSpace Ω₂] [Nonempty Ω₂] in
theorem integrable_of_abs_le {ν : Measure Ω₂} [IsFiniteMeasure ν] {f : Ω₂ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ w, |f w| ≤ C) : Integrable f ν :=
  (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ fun w => hC w)

omit [StandardBorelSpace Ω₂] [Nonempty Ω₂] in
theorem lintegral_ofReal_add {ν : Measure Ω₂} [IsFiniteMeasure ν] {f : Ω₂ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ w, |f w| ≤ C) (A : Set Ω₂) :
    ∫⁻ w in A, ENNReal.ofReal (f w + C) ∂ν = ENNReal.ofReal (∫ w in A, (f w + C) ∂ν) := by
  have hi : Integrable (fun w => f w + C) (ν.restrict A) :=
    ((integrable_of_abs_le hf hC).add (integrable_const C)).restrict
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun w => by have := (abs_le.1 (hC w)).1; show 0 ≤ f w + C; linarith)).symm

omit [StandardBorelSpace Ω₂] [Nonempty Ω₂] in
theorem integral_add_const' {ν : Measure Ω₂} [IsFiniteMeasure ν] {f : Ω₂ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ w, |f w| ≤ C) (A : Set Ω₂) :
    ∫ w in A, (f w + C) ∂ν = ∫ w in A, f w ∂ν + ν.real A * C := by
  rw [integral_add (integrable_of_abs_le hf hC).restrict (integrable_const C), setIntegral_const,
    smul_eq_mul]

omit [StandardBorelSpace Ω₂] [Nonempty Ω₂] in
theorem integral_add_const_nonneg {ν : Measure Ω₂} {f : Ω₂ → ℝ} {C : ℝ}
    (hC : ∀ w, |f w| ≤ C) (A : Set Ω₂) : 0 ≤ ∫ w in A, (f w + C) ∂ν :=
  integral_nonneg fun w => (by have := (abs_le.1 (hC w)).1; linarith : (0 : ℝ) ≤ f w + C)

/-- **Step A: the martingale identity on all of `𝓕 s`, for `law ξ`-a.e. kernel**, at fixed times. -/
theorem ae_setIntegral_eq (htr : ∀ s, Measurable (tr s))
    (h𝓕 : ∀ s, 𝓕 s = MeasurableSpace.comap (tr s) inferInstance)
    (hξ : Measurable[𝓖 0] ξ) (hΦ : Measurable Φ) (hΦa : ∀ s, Measurable[𝓖 s] fun x => tr s (Φ x))
    (hNm : ∀ t, Measurable[𝓕 t] (N t)) (hNb : ∀ T : ℝ≥0, ∃ C, ∀ t ≤ T, ∀ w, |N t w| ≤ C)
    (hM : Martingale M 𝓖 P) (hMN : ∀ t, M t =ᵐ[P] fun x => N t (Φ x)) {s t : ℝ≥0}
    (hst : s ≤ t) :
    ∀ᵐ z ∂(jlaw P ξ Φ).fst, ∀ A, MeasurableSet[𝓕 s] A →
      ∫ w in A, N t w ∂(jlaw P ξ Φ).condKernel z = ∫ w in A, N s w ∂(jlaw P ξ Φ).condKernel z := by
  obtain ⟨C, hC⟩ := hNb t
  have hNm' : ∀ u, Measurable (N u) := fun u => (hNm u).mono (𝓕.le u) le_rfl
  have hξ' : Measurable ξ := hξ.mono (𝓖.le 0) le_rfl
  have hξΦ : Measurable fun x => (ξ x, Φ x) := hξ'.prodMk hΦ
  set g : ℝ≥0 → Ω₂ → ℝ≥0 := fun u w => Real.toNNReal (N u w + C) with hgdef
  have hg : ∀ u, Measurable (g u) := fun u => ((hNm' u).add_const C).real_toNNReal
  have hgb : ∀ u ≤ t, ∀ w, (g u w : ℝ≥0∞) ≤ ENNReal.ofReal (2 * C) := fun u hu w =>
    ENNReal.ofReal_le_ofReal (by have := (abs_le.1 (hC u hu w)).2; linarith)
  have hfin : ∀ u ≤ t, IsFiniteKernel (wker P ξ Φ (g u) (tr s)) := fun u hu => by
    have := Kernel.isFiniteKernel_withDensity_of_bounded (jlaw P ξ Φ).condKernel
      (f := fun _ w => (g u w : ℝ≥0∞)) ENNReal.ofReal_ne_top fun _ w => hgb u hu w
    unfold wker; infer_instance
  have := hfin t le_rfl
  have := hfin s hst
  have heq : (jlaw P ξ Φ).fst ⊗ₘ wker P ξ Φ (g t) (tr s) =
      (jlaw P ξ Φ).fst ⊗ₘ wker P ξ Φ (g s) (tr s) := by
    ext S hS
    rw [compProd_wker_apply hξΦ (hg t) (htr s) hS, compProd_wker_apply hξΦ (hg s) (htr s) hS]
    set B := {x | (ξ x, tr s (Φ x)) ∈ S}
    have hB : MeasurableSet[𝓖 s] B := ((hξ.mono (𝓖.mono zero_le) le_rfl).prodMk (hΦa s)) hS
    have hI : ∀ u ≤ t, ∫⁻ x in B, g u (Φ x) ∂P =
        ENNReal.ofReal (∫ x in B, M u x ∂P + P.real B * C) := fun u hu => by
      have hm : Measurable fun x => N u (Φ x) := (hNm' u).comp hΦ
      have h := lintegral_ofReal_add (ν := P) hm (C := C) (fun x => hC u hu (Φ x)) B
      change ∫⁻ x in B, ENNReal.ofReal (N u (Φ x) + C) ∂P = _
      rw [h, integral_add_const' (ν := P) hm (C := C) (fun x => hC u hu (Φ x)) B,
        integral_congr_ae (ae_restrict_of_ae ((hMN u).mono fun x hx => hx.symm))]
    rw [hI t le_rfl, hI s hst, hM.setIntegral_eq hst hB]
  filter_upwards [Kernel.ae_eq_of_compProd_eq heq] with z hz
  intro A hA
  rw [h𝓕 s] at hA
  obtain ⟨A', hA', rfl⟩ := hA
  have h1 := congrArg (fun ν : Measure Ω₂ => ν A') hz
  rw [wker_apply (hg _) (htr s) z hA', wker_apply (hg _) (htr s) z hA'] at h1
  change ∫⁻ w in tr s ⁻¹' A', ENNReal.ofReal (N t w + C) ∂_ =
    ∫⁻ w in tr s ⁻¹' A', ENNReal.ofReal (N s w + C) ∂_ at h1
  rw [lintegral_ofReal_add (hNm' t) (fun w => hC t le_rfl w),
    lintegral_ofReal_add (hNm' s) (fun w => hC s hst w)] at h1
  have h2 := (ENNReal.ofReal_eq_ofReal_iff (integral_add_const_nonneg (fun w => hC t le_rfl w) _)
    (integral_add_const_nonneg (fun w => hC s hst w) _)).1 h1
  rw [integral_add_const' (hNm' t) (fun w => hC t le_rfl w),
    integral_add_const' (hNm' s) (fun w => hC s hst w)] at h2
  linarith

omit [StandardBorelSpace Ω₂] [Nonempty Ω₂] in
theorem exists_qtime_mem_Ioo {a b : ℝ≥0} (h : a < b) : ∃ i, a < qtime i ∧ qtime i < b := by
  obtain ⟨i, hi⟩ := denseRange_qtime.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 h)
  exact ⟨i, hi⟩

omit [StandardBorelSpace Ω₂] [Nonempty Ω₂] in
/-- Dense times strictly above `s`, converging to `s`, below a given `b > s`. -/
theorem exists_qtime_seq {s b : ℝ≥0} (h : s < b) : ∃ i : ℕ → ℕ,
    (∀ k, s < qtime (i k) ∧ qtime (i k) < b) ∧ Tendsto (fun k => qtime (i k)) atTop (𝓝[≥] s) := by
  have hk : ∀ k : ℕ, ∃ j, s < qtime j ∧ qtime j < min b (s + 1 / ((k : ℝ≥0) + 1)) := fun k =>
    exists_qtime_mem_Ioo (lt_min h (lt_add_of_pos_right s (by positivity)))
  choose i hi using hk
  refine ⟨i, fun k => ⟨(hi k).1, (hi k).2.trans_le (min_le_left _ _)⟩, ?_⟩
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => (hi k).1.le⟩
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun k => ha.trans (hi k).1, fun a ha => ?_⟩
  obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt (show (0 : ℝ) < (a - s : ℝ≥0) from by
    rw [NNReal.coe_pos]; exact tsub_pos_of_lt ha)
  filter_upwards [eventually_ge_atTop k₀] with k hk
  have h1 := (hi k).2.trans_le (min_le_right _ _)
  have h2 : (1 / ((k : ℝ≥0) + 1) : ℝ≥0) ≤ 1 / ((k₀ : ℝ≥0) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
  have h3 : ((1 / ((k₀ : ℝ≥0) + 1) : ℝ≥0) : ℝ) < (a - s : ℝ≥0) := by push_cast; exact hk₀
  have h4 : s + 1 / ((k₀ : ℝ≥0) + 1) < a := by
    rw [← NNReal.coe_lt_coe]; push_cast
    rw [NNReal.coe_sub ha.le] at h3; push_cast at h3; linarith
  exact h1.trans_le (add_le_add_right h2 s) |>.trans h4

/-- **Martingales of the path pass to the conditional kernel.** For `law ξ`-a.e. `z`, a
canonical process `N` whose composition with `Φ` has a `𝓖`-martingale version is an
`𝓕`-martingale under `condKernel (law (ξ, Φ)) z`. -/
theorem ae_martingale_condKernel (htr : ∀ s, Measurable (tr s))
    (h𝓕 : ∀ s, 𝓕 s = MeasurableSpace.comap (tr s) inferInstance)
    (hξ : Measurable[𝓖 0] ξ) (hΦ : Measurable Φ) (hΦa : ∀ s, Measurable[𝓖 s] fun x => tr s (Φ x))
    (hNm : ∀ t, Measurable[𝓕 t] (N t)) (hNr : ∀ w t, ContinuousWithinAt (fun u => N u w) (Ici t) t)
    (hNb : ∀ T : ℝ≥0, ∃ C, ∀ t ≤ T, ∀ w, |N t w| ≤ C)
    (hM : Martingale M 𝓖 P) (hMN : ∀ t, M t =ᵐ[P] fun x => N t (Φ x)) :
    ∀ᵐ z ∂(jlaw P ξ Φ).fst, Martingale N 𝓕 ((jlaw P ξ Φ).condKernel z) := by
  have hNm' : ∀ u, Measurable (N u) := fun u => (hNm u).mono (𝓕.le u) le_rfl
  have hA : ∀ᵐ z ∂(jlaw P ξ Φ).fst, ∀ i j : ℕ, qtime i ≤ qtime j → ∀ A,
      MeasurableSet[𝓕 (qtime i)] A → ∫ w in A, N (qtime j) w ∂(jlaw P ξ Φ).condKernel z =
        ∫ w in A, N (qtime i) w ∂(jlaw P ξ Φ).condKernel z := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    by_cases hij : qtime i ≤ qtime j
    · filter_upwards [ae_setIntegral_eq htr h𝓕 hξ hΦ hΦa hNm hNb hM hMN hij] with z hz
      exact fun _ => hz
    · exact Eventually.of_forall fun z h => absurd h hij
  filter_upwards [hA] with z hz
  set κz := (jlaw P ξ Φ).condKernel z
  have hint : ∀ t, Integrable (N t) κz := fun t => by
    obtain ⟨C, hC⟩ := hNb t
    exact integrable_of_abs_le (hNm' t) (hC t le_rfl)
  have hset : ∀ s t : ℝ≥0, s ≤ t → ∀ A, MeasurableSet[𝓕 s] A →
      ∫ w in A, N t w ∂κz = ∫ w in A, N s w ∂κz := by
    intro s t hst A hAm
    rcases hst.eq_or_lt with rfl | hlt
    · rfl
    obtain ⟨a, ha, hal⟩ := exists_qtime_seq hlt
    obtain ⟨b, hb, hbl⟩ := exists_qtime_seq (lt_add_one t)
    obtain ⟨C, hC⟩ := hNb (t + 1)
    have hDCT : ∀ (c : ℕ → ℕ) (u : ℝ≥0), u ≤ t → (∀ k, qtime (c k) < t + 1) →
        Tendsto (fun k => qtime (c k)) atTop (𝓝[≥] u) →
        Tendsto (fun k => ∫ w in A, N (qtime (c k)) w ∂κz) atTop (𝓝 (∫ w in A, N u w ∂κz)) :=
      fun c u hu hc hcl => tendsto_integral_of_dominated_convergence (fun _ => C)
        (fun k => (hNm' _).aestronglyMeasurable) (integrable_const C)
        (fun k => ae_of_all _ fun w => hC _ (hc k).le w)
        (ae_of_all _ fun w => (hNr w u).tendsto.comp hcl)
    have h1 := hDCT b t le_rfl (fun k => (hb k).2) hbl
    have h2 := hDCT a s hst (fun k => (ha k).2.trans (lt_add_one t)) hal
    refine tendsto_nhds_unique (h1.congr' ?_) h2
    filter_upwards [eventually_gt_atTop 0] with k _
    exact hz (a k) (b k) ((ha k).2.le.trans (hb k).1.le) A (𝓕.mono (ha k).1.le A hAm)
  exact ⟨fun t => (hNm t).stronglyMeasurable, fun i j hij =>
    (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le i) (hint j) (fun _ _ _ => (hint i).integrableOn)
      (fun s hs _ => (hset i j hij s hs).symm) (hNm i).stronglyMeasurable.aestronglyMeasurable).symm⟩

end BlockBand.Transmission.Dual.G
