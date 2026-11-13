module

public import BlockBand.Transmission.DualBoundary.PathOne
public import BlockBand.Transmission.Dual.Hitting

/-!
# Measurability of path functionals of the truncated state

Path space `DPath = ℝ≥0 → ℕ × (ℕ → ℝ) × (ℕ → ℝ)` with the product σ-algebra (the codomain of
`truncDualState`). The functionals `∫⁻_{[0,t]} R` and `∫_{(0,t]} h R` are not product-measurable
on all of `DPath`, but they are limits of measurable dyadic functionals (`R` sampled at
`⌈s 2^m⌉/2^m`, `Dual.ceilDyad`) along every path whose total `R` is continuous
(`tendsto_lintegral_dyad`, `tendsto_integral_dyad`), and every one-pair boundary path is such
(`continuous_dualTotal`). Hence their expectations, and `dualTransform`, depend only on the law
of `truncDualState`:
* **`lintegral_total_eq_of_map_eq`** (`E∫⁻_{[0,t]} R` for two realizations with one law);
* **`dualTransform_eq_of_map_eq`** (`dualTransform`, continuous weight, `t ≥ 0`).

Measures: any two probability spaces carrying one-pair boundary realizations
(`IsBoundaryDualProcess P 𝓖 D₀ ![x] ![y]`), with equal laws of `truncDualState`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- Path space of the truncated state. -/
abbrev DPath := ℝ≥0 → ℕ × (ℕ → ℝ) × (ℕ → ℝ)

/-- The total coordinate `R` along a path of `DPath`. -/
def pathTotal (γ : DPath) (s : ℝ≥0) : ℝ := dualTotal (γ s).1 (γ s).2.1 (γ s).2.2

theorem measurable_dualTotal_state :
    Measurable fun z : ℕ × (ℕ → ℝ) × (ℕ → ℝ) => dualTotal z.1 z.2.1 z.2.2 := by
  refine measurable_from_prod_countable_right (α := ℕ) (β := (ℕ → ℝ) × (ℕ → ℝ)) fun k => ?_
  unfold dualTotal
  refine Finset.measurable_fun_sum (Finset.range k) fun i _ => ?_
  exact (measurable_pi_apply i |>.comp measurable_fst).add
    (measurable_pi_apply i |>.comp measurable_snd)

theorem measurable_pathTotal (s : ℝ≥0) : Measurable fun γ : DPath => pathTotal γ s :=
  measurable_dualTotal_state.comp (measurable_pi_apply s)

/-- `R` at the dyadic time `⌈s 2^m⌉/2^m`, jointly in `(γ, s)`. -/
def dyTotal (m : ℕ) (q : DPath × ℝ) : ℝ := pathTotal q.1 (ceilDyad m q.2.toNNReal)

theorem measurable_dyTotal (m : ℕ) : Measurable (dyTotal m) := by
  have h1 : Measurable fun q : DPath × ℕ => pathTotal q.1 ((q.2 : ℝ≥0) / 2 ^ m) :=
    measurable_from_prod_countable_left fun k => measurable_pathTotal ((k : ℝ≥0) / 2 ^ m)
  have h2 : Measurable fun q : DPath × ℝ => (q.1, ⌈q.2.toNNReal * 2 ^ m⌉₊) :=
    measurable_fst.prodMk (Nat.measurable_ceil.comp
      ((measurable_real_toNNReal.comp measurable_snd).mul_const _))
  exact h1.comp h2

theorem ceilDyad_toNNReal_le {m : ℕ} {s t : ℝ} (hs : s ≤ t) :
    ceilDyad m s.toNNReal ≤ t.toNNReal + 1 := by
  refine (ceilDyad_lt m s.toNNReal).le.trans (add_le_add (Real.toNNReal_le_toNNReal hs) ?_)
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- A continuous `R` is bounded on the dyadic sampling window of `[0, t]`. -/
theorem exists_bound_pathTotal {γ : DPath} (hγ : Continuous (pathTotal γ)) (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ≥0, u ≤ t.toNNReal + 1 → |pathTotal γ u| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t.toNNReal + 1)).exists_bound_of_continuousOn
    hγ.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun u hu => ?_⟩
  have := hC u ⟨(zero_le : (0 : ℝ≥0) ≤ u), hu⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem tendsto_dyTotal {γ : DPath} (hγ : Continuous (pathTotal γ)) (s : ℝ) :
    Tendsto (fun m => dyTotal m (γ, s)) atTop (𝓝 (pathTotal γ s.toNNReal)) :=
  (hγ.continuousAt.mono_left nhdsWithin_le_nhds).comp (tendsto_ceilDyad s.toNNReal)

/-- The dyadic `∫⁻_{[0,t]} R` (measurable in the path). -/
def dyLInt (t : ℝ) (m : ℕ) (γ : DPath) : ℝ≥0∞ :=
  ∫⁻ s in Icc (0 : ℝ) t, ENNReal.ofReal (dyTotal m (γ, s))

theorem measurable_dyLInt (t : ℝ) (m : ℕ) : Measurable (dyLInt t m) :=
  (ENNReal.measurable_ofReal.comp (measurable_dyTotal m)).lintegral_prod_right'

theorem tendsto_lintegral_dyad {γ : DPath} (hγ : Continuous (pathTotal γ)) (t : ℝ) :
    Tendsto (fun m => dyLInt t m γ) atTop
      (𝓝 (∫⁻ s in Icc (0 : ℝ) t, ENNReal.ofReal (pathTotal γ s.toNNReal))) := by
  obtain ⟨C, -, hC⟩ := exists_bound_pathTotal hγ t
  refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal C)
    (fun m => ENNReal.measurable_ofReal.comp ((measurable_dyTotal m).comp
      (measurable_const.prodMk measurable_id))) (fun m => ?_) ?_ ?_
  · refine (ae_restrict_mem measurableSet_Icc).mono fun s hs => ?_
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC _ (ceilDyad_toNNReal_le hs.2)))
  · simp [lintegral_const, Real.volume_Icc, ENNReal.mul_eq_top]
  · exact ae_of_all _ fun s => (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_dyTotal hγ s)

/-- The dyadic `∫_{(0,t]} h(s) R_s ds` (measurable in the path). -/
def dyInt (h : ℝ → ℝ) (t : ℝ) (m : ℕ) (γ : DPath) : ℝ :=
  ∫ s in Ioc (0 : ℝ) t, h s * dyTotal m (γ, s)

theorem measurable_dyInt {h : ℝ → ℝ} (hh : Measurable h) (t : ℝ) (m : ℕ) :
    Measurable (dyInt h t m) :=
  (((hh.comp measurable_snd).mul (measurable_dyTotal m)).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) t))).measurable

theorem tendsto_integral_dyad {h : ℝ → ℝ} (hh : Continuous h) {γ : DPath}
    (hγ : Continuous (pathTotal γ)) (t : ℝ) :
    Tendsto (fun m => dyInt h t m γ) atTop
      (𝓝 (∫ s in Ioc (0 : ℝ) t, h s * pathTotal γ s.toNNReal)) := by
  obtain ⟨C, -, hC⟩ := exists_bound_pathTotal hγ t
  refine tendsto_integral_of_dominated_convergence (fun s => |h s| * C)
    (fun m => (hh.measurable.mul ((measurable_dyTotal m).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable) ?_ (fun m => ?_) ?_
  · exact ((hh.abs.mul continuous_const).integrableOn_Icc (a := 0) (b := t)).mono_set
      Ioc_subset_Icc_self
  · refine (ae_restrict_mem measurableSet_Ioc).mono fun s hs => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC _ (ceilDyad_toNNReal_le hs.2)) (abs_nonneg _)
  · exact ae_of_all _ fun s => (tendsto_dyTotal hγ s).const_mul (h s)

/-!
## Transfer through equal laws
-/

section Transfer

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
  {P₂ : Measure Ω₂} {Φ₁ : Ω₁ → DPath} {Φ₂ : Ω₂ → DPath}

theorem lintegral_eq_of_map_eq (hΦ₁ : Measurable Φ₁) (hΦ₂ : Measurable Φ₂)
    (hmap : P₁.map Φ₁ = P₂.map Φ₂) {G : DPath → ℝ≥0∞} (hG : Measurable G) {F₁ : Ω₁ → ℝ≥0∞}
    {F₂ : Ω₂ → ℝ≥0∞} (h₁ : F₁ =ᵐ[P₁] G ∘ Φ₁) (h₂ : F₂ =ᵐ[P₂] G ∘ Φ₂) :
    ∫⁻ ω, F₁ ω ∂P₁ = ∫⁻ ω, F₂ ω ∂P₂ := by
  rw [lintegral_congr_ae h₁, lintegral_congr_ae h₂]
  change ∫⁻ ω, G (Φ₁ ω) ∂P₁ = ∫⁻ ω, G (Φ₂ ω) ∂P₂
  rw [← lintegral_map hG hΦ₁, ← lintegral_map hG hΦ₂, hmap]

theorem integral_eq_of_map_eq (hΦ₁ : Measurable Φ₁) (hΦ₂ : Measurable Φ₂)
    (hmap : P₁.map Φ₁ = P₂.map Φ₂) {G : DPath → ℝ} (hG : Measurable G) {F₁ : Ω₁ → ℝ}
    {F₂ : Ω₂ → ℝ} (h₁ : F₁ =ᵐ[P₁] G ∘ Φ₁) (h₂ : F₂ =ᵐ[P₂] G ∘ Φ₂) :
    ∫ ω, F₁ ω ∂P₁ = ∫ ω, F₂ ω ∂P₂ := by
  rw [integral_congr_ae h₁, integral_congr_ae h₂]
  change ∫ ω, G (Φ₁ ω) ∂P₁ = ∫ ω, G (Φ₂ ω) ∂P₂
  rw [← integral_map hΦ₁.aemeasurable hG.aestronglyMeasurable,
    ← integral_map hΦ₂.aemeasurable hG.aestronglyMeasurable, hmap]

end Transfer

/-!
## The realizations
-/

section Real

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ}
  {x y : ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

theorem dualTotal_truncDualCoord (k : ℕ) (a b : ℕ → ℝ) :
    dualTotal k (truncDualCoord k a) (truncDualCoord k b) = dualTotal k a b := by
  unfold dualTotal
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < k := Finset.mem_range.1 hi
  simp [truncDualCoord, hi']

theorem pathTotal_truncDualState (ω : Ω) (s : ℝ≥0) :
    pathTotal (truncDualState N X Y ω) s = dualTotal (N s ω) (X s ω) (Y s ω) :=
  dualTotal_truncDualCoord _ _ _

theorem measurable_truncDualState (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) :
    Measurable (truncDualState N X Y) := by
  have tc : ∀ (k : Ω → ℕ) (a : Ω → ℕ → ℝ), Measurable k → Measurable a →
      Measurable fun ω => truncDualCoord (k ω) (a ω) := fun k a hk ha =>
    measurable_pi_iff.2 fun i => Measurable.ite (hk (measurableSet_Ioi (a := i)))
      ((measurable_pi_apply i).comp ha) measurable_const
  refine measurable_pi_iff.2 fun t => ?_
  have hN := (h.adapted t).1.mono (𝓖.le t) le_rfl
  exact hN.prodMk ((tc _ _ hN ((h.adapted t).2.1.mono (𝓖.le t) le_rfl)).prodMk
    (tc _ _ hN ((h.adapted t).2.2.mono (𝓖.le t) le_rfl)))

/-- Almost every path of a one-pair boundary realization starts at level one and is a boundary
deletion path. -/
theorem ae_path (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) :
    ∀ᵐ ω ∂P, N 0 ω = 1 ∧
      IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω) := by
  filter_upwards [h.start, h.paths] with ω h0 hp using ⟨h0.1, hp⟩

theorem ae_continuous_pathTotal (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) :
    ∀ᵐ ω ∂P, Continuous (pathTotal (truncDualState N X Y ω)) := by
  filter_upwards [ae_path h] with ω hω
  have e : pathTotal (truncDualState N X Y ω) = fun s => dualTotal (N s ω) (X s ω) (Y s ω) :=
    funext fun s => pathTotal_truncDualState ω s
  rw [e]
  exact continuous_dualTotal hω.2 hω.1

end Real

section TransferReal

variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂} {P₁ : Measure Ω₁}
  {P₂ : Measure Ω₂} {𝓖₁ : Filtration ℝ≥0 m₁} {𝓖₂ : Filtration ℝ≥0 m₂} {D0 D0' x y x' y' : ℝ}
  {N₁ : ℝ≥0 → Ω₁ → ℕ} {X₁ Y₁ : ℝ≥0 → Ω₁ → ℕ → ℝ} {N₂ : ℝ≥0 → Ω₂ → ℕ}
  {X₂ Y₂ : ℝ≥0 → Ω₂ → ℕ → ℝ}

/-- **`E∫⁻_{[0,t]} R` is a function of the law of `truncDualState`.** -/
theorem lintegral_total_eq_of_map_eq (h₁ : IsBoundaryDualProcess P₁ 𝓖₁ D0 ![x] ![y] N₁ X₁ Y₁)
    (h₂ : IsBoundaryDualProcess P₂ 𝓖₂ D0' ![x'] ![y'] N₂ X₂ Y₂)
    (hmap : P₁.map (truncDualState N₁ X₁ Y₁) = P₂.map (truncDualState N₂ X₂ Y₂)) (t : ℝ) :
    ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) t,
        ENNReal.ofReal (dualTotal (N₁ s.toNNReal ω) (X₁ s.toNNReal ω) (Y₁ s.toNNReal ω))) ∂P₁ =
      ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) t,
        ENNReal.ofReal (dualTotal (N₂ s.toNNReal ω) (X₂ s.toNNReal ω) (Y₂ s.toNNReal ω))) ∂P₂ := by
  refine lintegral_eq_of_map_eq (measurable_truncDualState h₁) (measurable_truncDualState h₂) hmap
    (G := fun γ => liminf (fun m => dyLInt t m γ) atTop)
    (Measurable.liminf fun m => measurable_dyLInt t m) ?_ ?_
  · filter_upwards [ae_continuous_pathTotal h₁] with ω hω
    simp only [Function.comp, ← pathTotal_truncDualState]
    exact ((tendsto_lintegral_dyad hω t).liminf_eq).symm
  · filter_upwards [ae_continuous_pathTotal h₂] with ω hω
    simp only [Function.comp, ← pathTotal_truncDualState]
    exact ((tendsto_lintegral_dyad hω t).liminf_eq).symm

/-- The integrand of the `dualTransform`, as a functional of the truncated path. -/
def transformG (h : ℝ → ℝ) (t : ℝ) (γ : DPath) : ℝ :=
  if (γ t.toNNReal).1 = 0 then Real.exp (-liminf (fun m => dyInt h t m γ) atTop) else 0

theorem measurable_transformG {h : ℝ → ℝ} (hh : Measurable h) (t : ℝ) :
    Measurable (transformG h t) := by
  refine Measurable.ite ?_ (Real.continuous_exp.measurable.comp
    (Measurable.liminf fun m => measurable_dyInt hh t m).neg) measurable_const
  exact (measurable_fst.comp (measurable_pi_apply _)) (measurableSet_singleton 0)

theorem transform_ae_eq (E : ℝ) {κ : ℝ → ℝ} (hκ : Continuous κ) {t : ℝ} (ht : 0 ≤ t)
    (h₁ : IsBoundaryDualProcess P₁ 𝓖₁ D0 ![x] ![y] N₁ X₁ Y₁) :
    (fun ω => if dualExtinction N₁ ω ≤ ENNReal.ofReal t then
      Real.exp (-∫ s in (0 : ℝ)..t,
        absorptionRate E κ (t - s) * dualTotal (N₁ s.toNNReal ω) (X₁ s.toNNReal ω) (Y₁ s.toNNReal ω))
      else 0) =ᵐ[P₁] transformG (fun s => absorptionRate E κ (t - s)) t ∘ truncDualState N₁ X₁ Y₁ := by
  have hc : Continuous fun s => absorptionRate E κ (t - s) :=
    continuous_const.mul (hκ.comp (continuous_const.sub continuous_id))
  filter_upwards [ae_path h₁, ae_continuous_pathTotal h₁] with ω hω hR
  have hiff := dualExtinction_le_iff hω.2 hω.1 t
  have h1 : (truncDualState N₁ X₁ Y₁ ω t.toNNReal).1 = N₁ t.toNNReal ω := rfl
  simp only [Function.comp, transformG]
  by_cases hz : N₁ t.toNNReal ω = 0
  · rw [ite_eq_left (hiff.2 hz), ite_eq_left (h1.trans hz), intervalIntegral.integral_of_le ht,
      ((tendsto_integral_dyad hc hR t).liminf_eq)]
    simp only [pathTotal_truncDualState]
  · rw [ite_eq_right (fun h => hz (hiff.1 h)), ite_eq_right (fun h => hz (h1 ▸ h))]

/-- **The `dualTransform` is a function of the law of `truncDualState`** (continuous
profile `κ`, `t ≥ 0`).
-/
theorem dualTransform_eq_of_map_eq (E : ℝ) {κ : ℝ → ℝ} (hκ : Continuous κ) {t : ℝ} (ht : 0 ≤ t)
    (h₁ : IsBoundaryDualProcess P₁ 𝓖₁ D0 ![x] ![y] N₁ X₁ Y₁)
    (h₂ : IsBoundaryDualProcess P₂ 𝓖₂ D0' ![x'] ![y'] N₂ X₂ Y₂)
    (hmap : P₁.map (truncDualState N₁ X₁ Y₁) = P₂.map (truncDualState N₂ X₂ Y₂)) :
    dualTransform E κ t P₁ N₁ X₁ Y₁ = dualTransform E κ t P₂ N₂ X₂ Y₂ := by
  have hc : Measurable fun s => absorptionRate E κ (t - s) :=
    (continuous_const.mul (hκ.comp (continuous_const.sub continuous_id))).measurable
  exact integral_eq_of_map_eq (measurable_truncDualState h₁) (measurable_truncDualState h₂) hmap
    (measurable_transformG hc t) (transform_ae_eq E hκ ht h₁) (transform_ae_eq E hκ ht h₂)

end TransferReal

end BlockBand.Transmission.DualBoundary
