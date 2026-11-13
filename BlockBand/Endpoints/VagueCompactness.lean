module

public import BlockBand.Model.Construction.MarkedStateTopologyConsequences
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Vague compactness of cutoff boxes

We prove that a vague limit of point measures is integer valued and deduce that the sets of point
measures with prescribed bounds on all cutoff coordinates are vaguely compact
(`isCompact_cutoffBox`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
open BlockBand.Model.Construction (stateCutoff stateCutoff_mem_unitInterval
  exists_stateCutoff_eq_one)

/-- A real number that is approximated to every positive precision `ε` by some natural
number is itself a natural number. -/
theorem exists_nat_eq_of_forall_approx {r : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, |(n : ℝ) - r| < ε) : ∃ n : ℕ, r = n := by
  obtain ⟨n, hn⟩ := h (1 / 2) (by norm_num)
  refine ⟨n, ?_⟩
  by_contra hne
  have hpos : 0 < |(n : ℝ) - r| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
  obtain ⟨m, hm⟩ := h (min (1 / 2) |(n : ℝ) - r|) (lt_min (by norm_num) hpos)
  have hm1 := hm.trans_le (min_le_left _ _)
  have hm2 := hm.trans_le (min_le_right _ _)
  have hmn : m = n := by
    rw [abs_lt] at hn hm1
    have h1 : (m : ℝ) < n + 1 := by linarith
    have h2 : (n : ℝ) < m + 1 := by linarith
    have h1' : m < n + 1 := by exact_mod_cast h1
    have h2' : n < m + 1 := by exact_mod_cast h2
    omega
  rw [hmn] at hm2
  exact lt_irrefl _ hm2

/-- Extended-real version: a finite `L : ℝ≥0∞` that is, for every real `ε > 0`, within
`ENNReal.ofReal ε` of some natural number on both sides is a natural number. -/
theorem exists_nat_eq_of_forall_approx_ennreal {L : ℝ≥0∞} (hL : L ≠ ∞)
    (h : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
      (n : ℝ≥0∞) < L + ENNReal.ofReal ε ∧ L < n + ENNReal.ofReal ε) :
    ∃ n : ℕ, L = n := by
  obtain ⟨n, hn⟩ := exists_nat_eq_of_forall_approx (r := L.toReal) (fun ε hε => by
    obtain ⟨n, h1, h2⟩ := h ε hε
    refine ⟨n, abs_lt.2 ⟨?_, ?_⟩⟩
    · have h3 := (ENNReal.toReal_lt_toReal hL (by finiteness)).2 h2
      rw [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hε.le, ENNReal.toReal_natCast] at h3
      linarith
    · have h3 := (ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top n) (by finiteness)).2 h1
      rw [ENNReal.toReal_add hL ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε.le,
        ENNReal.toReal_natCast] at h3
      linarith)
  refine ⟨n, ?_⟩
  rw [← ENNReal.ofReal_toReal hL, hn, ENNReal.ofReal_natCast]

/-- For any measure `ν` on `ℝ` finite on compact sets, a compactly supported continuous test
`g ≤ 1` whose topological support lies in a measurable set `V` with `ν V < ∞` satisfies
`∫ g dν ≤ ν.real V`. -/
theorem integral_le_measureReal_of_tsupport_subset {ν : Measure ℝ} [IsFiniteMeasureOnCompacts ν]
    (g : CompactlySupportedContinuousMap ℝ ℝ) (hg : ∀ x, g x ≤ 1) {V : Set ℝ}
    (hV : MeasurableSet V) (hνV : ν V ≠ ∞) (hgV : tsupport g ⊆ V) :
    ∫ x, g x ∂ν ≤ ν.real V := by
  have hle (x : ℝ) : g x ≤ V.indicator 1 x := by
    by_cases hx : x ∈ tsupport g
    · simp [hgV hx, hg x]
    · simp [image_eq_zero_of_notMem_tsupport hx, Set.indicator_nonneg]
  calc ∫ x, g x ∂ν ≤ ∫ x, V.indicator 1 x ∂ν :=
        integral_mono g.integrable
          (IntegrableOn.integrable_indicator (integrableOn_const hνV) hV) hle
    _ = ν.real V := integral_indicator_one hV

/-- For any measure `ν` on `ℝ` finite on compact sets, a nonnegative compactly supported
continuous test equal to `1` on a compact set `K` satisfies `ν.real K ≤ ∫ g dν`. -/
theorem measureReal_le_integral_of_eqOn_one {ν : Measure ℝ} [IsFiniteMeasureOnCompacts ν]
    (g : CompactlySupportedContinuousMap ℝ ℝ) (hg : ∀ x, 0 ≤ g x) {K : Set ℝ}
    (hK : IsCompact K) (hgK : ∀ x ∈ K, g x = 1) : ν.real K ≤ ∫ x, g x ∂ν := by
  have hle (x : ℝ) : K.indicator 1 x ≤ g x := by
    by_cases hx : x ∈ K
    · simp [hx, hgK x hx]
    · simp [hx, hg x]
  calc ν.real K = ∫ x, K.indicator 1 x ∂ν := (integral_indicator_one hK.measurableSet).symm
    _ ≤ ∫ x, g x ∂ν :=
        integral_mono ((continuousOn_const.integrableOn_compact hK).integrable_indicator
          hK.measurableSet) g.integrable hle

/-- Frontier-null open sets. Let `F` be a nontrivial filter on point measures on `ℝ`
and `μ` a regular Borel measure on `ℝ`, finite on compact sets, such that every vague
coordinate `ξ ↦ ∫ g dξ` (`g ∈ C_c(ℝ, ℝ)`) tends along `F` to `∫ g dμ`. Then every open
`V` with compact closure and `μ (closure V \ V) = 0` has natural-number mass `μ V`. -/
theorem exists_nat_measure_eq_of_tendsto_coordinate
    {F : Filter (VaguePointMeasure ℝ)} [F.NeBot] {μ : Measure ℝ} [μ.Regular]
    (hF : ∀ g : CompactlySupportedContinuousMap ℝ ℝ,
      Tendsto (fun ξ : VaguePointMeasure ℝ => ξ.coordinate g) F (𝓝 (∫ x, g x ∂μ)))
    {V : Set ℝ} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hfr : μ (closure V \ V) = 0) :
    ∃ n : ℕ, μ V = n := by
  have hμcl : μ (closure V) ≠ ∞ := hVc.measure_lt_top.ne
  have hμV : μ V ≠ ∞ := ne_top_of_le_ne_top hμcl (measure_mono subset_closure)
  have hclV : μ (closure V) = μ V :=
    le_antisymm (measure_mono_ae (ae_le_set.2 hfr)) (measure_mono subset_closure)
  obtain ⟨n, hn⟩ := exists_nat_eq_of_forall_approx (r := μ.real V) (fun ε hε => by
    have hε' : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.2 hε).ne'
    -- inner test function
    obtain ⟨K, hKV, hK, hlt⟩ := hV.measurableSet.exists_isCompact_lt_add hμV hε'
    obtain ⟨g0, hg1, hgc, hgV, hg01⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
    let g : CompactlySupportedContinuousMap ℝ ℝ := ⟨g0, hgc⟩
    have hKg : μ.real K ≤ ∫ x, g x ∂μ :=
      measureReal_le_integral_of_eqOn_one g (fun x => (hg01 x).1) hK (fun x hx => hg1 hx)
    have hKreal : μ.real V < μ.real K + ε := by
      have h3 := (ENNReal.toReal_lt_toReal hμV
        (ENNReal.add_ne_top.2 ⟨hK.measure_lt_top.ne, ENNReal.ofReal_ne_top⟩)).2 hlt
      rwa [ENNReal.toReal_add hK.measure_lt_top.ne ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hε.le] at h3
    -- outer test function
    obtain ⟨U, hVU, hU, hUlt⟩ := Set.exists_isOpen_lt_of_lt (closure V)
      (μ (closure V) + ENNReal.ofReal ε) (ENNReal.lt_add_right hμcl hε')
    obtain ⟨h0, hh1, hhc, hhU, hh01⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hVc hU hVU
    let h : CompactlySupportedContinuousMap ℝ ℝ := ⟨h0, hhc⟩
    have hUfin : μ U ≠ ∞ := ne_top_of_lt hUlt
    have hhU' : ∫ x, h x ∂μ ≤ μ.real U :=
      integral_le_measureReal_of_tsupport_subset h (fun x => (hh01 x).2) hU.measurableSet
        hUfin hhU
    have hUreal : μ.real U < μ.real V + ε := by
      have h3 := (ENNReal.toReal_lt_toReal hUfin (by finiteness)).2 hUlt
      rw [ENNReal.toReal_add hμcl ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε.le,
        hclV] at h3
      exact h3
    -- a point measure close to the limit on both tests
    have e1 : ∀ᶠ ξ in F, μ.real V - ε < ξ.coordinate g :=
      (hF g).eventually (lt_mem_nhds (by linarith))
    have e2 : ∀ᶠ ξ in F, ξ.coordinate h < μ.real V + ε :=
      (hF h).eventually (gt_mem_nhds (by linarith))
    obtain ⟨ξ, h1, h2⟩ := (e1.and e2).exists
    have hξcl : ξ.measure (closure V) ≠ ∞ := (ξ.finite_on_compact _ hVc).ne
    have hξV : ξ.measure V ≠ ∞ := ne_top_of_le_ne_top hξcl (measure_mono subset_closure)
    obtain ⟨m, hm⟩ := (ξ.integer_valued V hV.measurableSet).resolve_left hξV
    have hg' : ξ.coordinate g ≤ ξ.measure.real V :=
      integral_le_measureReal_of_tsupport_subset g (fun x => (hg01 x).2) hV.measurableSet
        hξV hgV
    have hh' : ξ.measure.real (closure V) ≤ ξ.coordinate h :=
      measureReal_le_integral_of_eqOn_one h (fun x => (hh01 x).1) hVc (fun x hx => hh1 hx)
    have hmono : ξ.measure.real V ≤ ξ.measure.real (closure V) :=
      measureReal_mono subset_closure hξcl
    have hmr : ξ.measure.real V = m := by rw [measureReal_def, hm, ENNReal.toReal_natCast]
    exact ⟨m, abs_lt.2 ⟨by linarith, by linarith⟩⟩)
  refine ⟨n, ?_⟩
  rw [← ENNReal.ofReal_toReal hμV, ← measureReal_def, hn, ENNReal.ofReal_natCast]

/-- Compact sets. Under the hypotheses of `exists_nat_measure_eq_of_tendsto_coordinate`
(nontrivial filter `F`, regular `μ` finite on compacts, vague convergence of all
`C_c(ℝ, ℝ)` coordinates along `F` to `μ`), every compact `K ⊆ ℝ` has natural-number
mass `μ K`. -/
theorem exists_nat_measure_eq_of_isCompact
    {F : Filter (VaguePointMeasure ℝ)} [F.NeBot] {μ : Measure ℝ} [μ.Regular]
    (hF : ∀ g : CompactlySupportedContinuousMap ℝ ℝ,
      Tendsto (fun ξ : VaguePointMeasure ℝ => ξ.coordinate g) F (𝓝 (∫ x, g x ∂μ)))
    {K : Set ℝ} (hK : IsCompact K) :
    ∃ n : ℕ, μ K = n := by
  have hKfin : μ K ≠ ∞ := hK.measure_lt_top.ne
  let S : ℝ≥0 → Set ℝ := fun t => cthickening (t : ℝ) K \ thickening (t : ℝ) K
  have hSm : ∀ t, MeasurableSet (S t) := fun _ =>
    isClosed_cthickening.measurableSet.diff isOpen_thickening.measurableSet
  have key : ∀ t s : ℝ≥0, t < s → Disjoint (S t) (S s) := by
    intro t s hts
    rw [Set.disjoint_left]
    rintro x ⟨hxt, -⟩ ⟨-, hxs⟩
    apply hxs
    rw [mem_thickening_iff_infEDist_lt]
    rw [mem_cthickening_iff] at hxt
    have hs0 : (0 : ℝ) < s := by exact_mod_cast (zero_le (a := t)).trans_lt hts
    exact hxt.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hs0).2 (by exact_mod_cast hts))
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro t s hts
    rcases lt_or_gt_of_ne hts with h | h
    · exact key t s h
    · exact (key s t h).symm
  have hC := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) hSm hdisj
  have hdense := (hC.image (fun t : ℝ≥0 => (t : ℝ))).dense_compl ℝ
  apply exists_nat_eq_of_forall_approx_ennreal hKfin
  intro ε hε
  have hε' : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.2 hε).ne'
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), μ (cthickening r K) < μ K + ENNReal.ofReal ε :=
    (tendsto_measure_cthickening_of_isCompact hK).eventually
      (gt_mem_nhds (ENNReal.lt_add_right hKfin hε'))
  obtain ⟨δ, hδ, hδr⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨t, htC, ht⟩ := hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 hδ)
  have ht0 : 0 < t := ht.1
  have hSt : μ (S ⟨t, ht0.le⟩) = 0 := by
    by_contra hne
    exact htC ⟨⟨t, ht0.le⟩, pos_iff_ne_zero.2 hne, rfl⟩
  have hcl : closure (thickening t K) ⊆ cthickening t K :=
    closure_thickening_subset_cthickening t K
  obtain ⟨n, hn⟩ := exists_nat_measure_eq_of_tendsto_coordinate hF (V := thickening t K)
    isOpen_thickening (hK.cthickening.of_isClosed_subset isClosed_closure hcl)
    (measure_mono_null (sdiff_subset_sdiff_left hcl) hSt)
  have hdist : dist t 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos ht0]; exact ht.2
  refine ⟨n, ?_, ?_⟩
  · rw [← hn]
    exact (measure_mono (thickening_subset_cthickening t K)).trans_lt (hδr hdist)
  · calc μ K ≤ μ (thickening t K) := measure_mono (self_subset_thickening ht0 K)
      _ = n := hn
      _ < n + ENNReal.ofReal ε := ENNReal.lt_add_right (ENNReal.natCast_ne_top n) hε'

/-- Measurable sets. Under the hypotheses of `exists_nat_measure_eq_of_tendsto_coordinate`,
the limit measure `μ` is integer valued: every Borel `A ⊆ ℝ` has `μ A = ∞` or
`μ A ∈ ℕ`. -/
theorem integerValued_of_tendsto_coordinate
    {F : Filter (VaguePointMeasure ℝ)} [F.NeBot] {μ : Measure ℝ} [μ.Regular]
    (hF : ∀ g : CompactlySupportedContinuousMap ℝ ℝ,
      Tendsto (fun ξ : VaguePointMeasure ℝ => ξ.coordinate g) F (𝓝 (∫ x, g x ∂μ)))
    (A : Set ℝ) (hA : MeasurableSet A) :
    μ A = ∞ ∨ ∃ n : ℕ, μ A = n := by
  by_cases hA' : μ A = ∞
  · exact Or.inl hA'
  right
  apply exists_nat_eq_of_forall_approx_ennreal hA'
  intro ε hε
  have hε' : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.2 hε).ne'
  obtain ⟨K, hKA, hK, hlt⟩ := hA.exists_isCompact_lt_add hA' hε'
  obtain ⟨n, hn⟩ := exists_nat_measure_eq_of_isCompact hF hK
  refine ⟨n, ?_, ?_⟩
  · rw [← hn]
    exact (measure_mono hKA).trans_lt (ENNReal.lt_add_right hA' hε')
  · rw [← hn]
    exact hlt

/-- Every compact test is dominated by a cutoff coordinate: for `g ∈ C_c(ℝ, ℝ)` there are
`n` and `B ≥ 0` with `|∫ g dξ| ≤ B · ∫ stateCutoff ℝ n dξ` for every point
measure `ξ`. -/
theorem exists_abs_coordinate_le (g : CompactlySupportedContinuousMap ℝ ℝ) :
    ∃ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ : VaguePointMeasure ℝ,
      |ξ.coordinate g| ≤ B * ξ.coordinate (stateCutoff ℝ n) := by
  obtain ⟨n, hn⟩ := exists_stateCutoff_eq_one ℝ g
  obtain ⟨C, hC⟩ := g.continuous.bounded_above_of_compact_support g.hasCompactSupport
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨n, C, hC0, fun ξ => ?_⟩
  have hpt : ∀ x, ‖g x‖ ≤ C * stateCutoff ℝ n x := by
    intro x
    by_cases hx : g x = 0
    · rw [hx, norm_zero]
      exact mul_nonneg hC0 (stateCutoff_mem_unitInterval ℝ n x).1
    · rw [hn x (subset_tsupport g hx), mul_one]
      exact hC x
  have hi : Integrable (stateCutoff ℝ n) ξ.measure :=
    (stateCutoff ℝ n).continuous.integrable_of_hasCompactSupport
      (stateCutoff ℝ n).hasCompactSupport
  have h := norm_integral_le_of_norm_le (hi.const_mul C) (ae_of_all _ hpt)
  simpa [Real.norm_eq_abs, integral_const_mul, VaguePointMeasure.coordinate] using h

/-- **Vague compactness of cutoff boxes.** For every threshold sequence `c : ℕ → ℝ`, the set
of point measures `ξ : VaguePointMeasure ℝ` with `∫ stateCutoff ℝ n dξ ≤ c n` for
all `n : ℕ` is compact in the vague topology. -/
theorem isCompact_cutoffBox (c : ℕ → ℝ) :
    IsCompact {ξ : VaguePointMeasure ℝ |
      ∀ n, ξ.coordinate (BlockBand.Model.Construction.stateCutoff ℝ n) ≤ c n} := by
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro 𝒰 h𝒰
  have hmem := le_principal_iff.1 h𝒰
  have hlim : ∀ g : CompactlySupportedContinuousMap ℝ ℝ, ∃ a : ℝ,
      Tendsto (fun ξ : VaguePointMeasure ℝ => ξ.coordinate g) (𝒰 : Filter _) (𝓝 a) := by
    intro g
    obtain ⟨n, B, hB, hb⟩ := exists_abs_coordinate_le g
    have hsub : {ξ : VaguePointMeasure ℝ | ∀ n, ξ.coordinate (stateCutoff ℝ n) ≤ c n} ⊆
        (fun ξ : VaguePointMeasure ℝ => ξ.coordinate g) ⁻¹' Icc (-(B * c n)) (B * c n) := by
      intro ξ hξ
      exact abs_le.1 ((hb ξ).trans (mul_le_mul_of_nonneg_left (hξ n) hB))
    obtain ⟨a, -, ha⟩ := isCompact_Icc.ultrafilter_le_nhds
      (𝒰.map fun ξ : VaguePointMeasure ℝ => ξ.coordinate g)
      (le_principal_iff.2 (Ultrafilter.mem_map.2 (Filter.mem_of_superset hmem hsub)))
    exact ⟨a, ha⟩
  choose Λ hΛ using hlim
  have hint (ξ : VaguePointMeasure ℝ) (g : CompactlySupportedContinuousMap ℝ ℝ) :
      Integrable g ξ.measure := g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have hadd (ξ : VaguePointMeasure ℝ) (g h : CompactlySupportedContinuousMap ℝ ℝ) :
      ξ.coordinate (g + h) = ξ.coordinate g + ξ.coordinate h := by
    simp only [VaguePointMeasure.coordinate, CompactlySupportedContinuousMap.coe_add,
      Pi.add_apply]
    exact integral_add (hint ξ g) (hint ξ h)
  have hsmul (ξ : VaguePointMeasure ℝ) (r : ℝ) (g : CompactlySupportedContinuousMap ℝ ℝ) :
      ξ.coordinate (r • g) = r * ξ.coordinate g := by
    simp only [VaguePointMeasure.coordinate, CompactlySupportedContinuousMap.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul r _
  have hmono (ξ : VaguePointMeasure ℝ) (g h : CompactlySupportedContinuousMap ℝ ℝ)
      (hgh : g ≤ h) : ξ.coordinate g ≤ ξ.coordinate h :=
    integral_mono (hint ξ g) (hint ξ h) hgh
  let Λp : CompactlySupportedContinuousMap ℝ ℝ →ₚ[ℝ] ℝ :=
    { toFun := Λ
      map_add' := fun g h =>
        tendsto_nhds_unique (by simpa only [hadd] using hΛ (g + h)) ((hΛ g).add (hΛ h))
      map_smul' := fun r g => by
        simp only [RingHom.id_apply, smul_eq_mul]
        exact tendsto_nhds_unique (by simpa only [hsmul] using hΛ (r • g))
          ((hΛ g).const_mul r)
      monotone' := fun g h hgh =>
        le_of_tendsto_of_tendsto' (hΛ g) (hΛ h) (fun ξ => hmono ξ g h hgh) }
  let μ : Measure ℝ := RealRMK.rieszMeasure Λp
  have hμ (g : CompactlySupportedContinuousMap ℝ ℝ) : ∫ x, g x ∂μ = Λ g :=
    RealRMK.integral_rieszMeasure Λp g
  have hF (g : CompactlySupportedContinuousMap ℝ ℝ) :
      Tendsto (fun ξ : VaguePointMeasure ℝ => ξ.coordinate g) (𝒰 : Filter _)
        (𝓝 (∫ x, g x ∂μ)) := by
    rw [hμ g]
    exact hΛ g
  have hiv := integerValued_of_tendsto_coordinate (F := (𝒰 : Filter _)) hF
  let ξ₀ : VaguePointMeasure ℝ :=
    { measure := μ
      finite_on_compact := fun _ hK => hK.measure_lt_top
      integer_valued := hiv
      count := fun A => ⌊(μ A.carrier).toReal⌋₊
      measure_eq_count := fun A => by
        have hA : μ A.carrier ≠ ∞ := ne_top_of_le_ne_top A.compact_closure.measure_lt_top.ne
          (measure_mono subset_closure)
        obtain ⟨n, hn⟩ := (hiv A.carrier A.measurable).resolve_left hA
        rw [hn, ENNReal.toReal_natCast, Nat.floor_natCast] }
  refine ⟨ξ₀, ?_, ?_⟩
  · intro n
    change ∫ x, stateCutoff ℝ n x ∂μ ≤ c n
    rw [hμ]
    exact le_of_tendsto (hΛ _) (Filter.mem_of_superset hmem (fun ξ hξ => hξ n))
  · have hind : Topology.IsInducing (fun ξ : VaguePointMeasure ℝ =>
        fun f : CompactlySupportedContinuousMap ℝ ℝ => ξ.coordinate f) := ⟨rfl⟩
    refine tendsto_id'.1 ?_
    rw [hind.tendsto_nhds_iff, tendsto_pi_nhds]
    intro f
    exact hF f

end BlockBand.Endpoints
