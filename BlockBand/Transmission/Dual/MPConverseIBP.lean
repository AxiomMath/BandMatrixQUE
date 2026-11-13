module

public import BlockBand.Internal.Contracts.Transmission
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Tools
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Riemann

/-!
# Integration by parts against a bounded drift

`hasMartingaleModification_ibp`: let `X` have a martingale modification, a.s. continuous paths
and `|X| ≤ C_T` on every horizon `[0, T]`; let `A_t = ∫_0^t β` with `|β| ≤ B`, `u ↦ β_u` a.s. measurable and `A_t`
`𝓖_t`-a.e. measurable. Then `G_t = A_t X_t − ∫_0^t β_u X_u du` has a martingale modification.

Proof (no stochastic integral, no Fubini): on the grids `t_k` of `[s, t]`,
`S_n = Σ_k A_{t_k}(X_{t_{k+1}} − X_{t_k})` has zero mean on `𝓖_s`-sets (martingale transform),
`S_n = A_t X_t − A_s X_s − Σ_k X_{t_{k+1}} ΔA_k` (summation by parts), and the Riemann sums
converge (`Semimartingale.tendsto_riemann`, `eventually_mesh_le`); `|S_n|` is bounded by a
constant, so dominated convergence gives `∫_E G_t = ∫_E G_s`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

section Pathwise

/-- Summation by parts. -/
theorem sum_abel (A X : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), A k * (X (k + 1) - X k) =
      A (n + 1) * X (n + 1) - A 0 * X 0 -
        ∑ k ∈ Finset.range (n + 1), X (k + 1) * (A (k + 1) - A k) := by
  have h := Finset.sum_range_sub (fun k => A k * X k) (n + 1)
  have e : ∀ k, A (k + 1) * X (k + 1) - A k * X k =
      A k * (X (k + 1) - X k) + X (k + 1) * (A (k + 1) - A k) := fun k => by ring
  simp only [e, Finset.sum_add_distrib] at h
  linarith

/-- The pathwise limit of the grid transforms. -/
theorem tendsto_gridIBP {x β : ℝ → ℝ} (hx : Continuous x) (hβ : Measurable β) {B : ℝ}
    (hβB : ∀ u, |β u| ≤ B) {s t : ℝ} (hst : s ≤ t) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
        x (rgrid s t n (k + 1)) * ∫ u in rgrid s t n k..rgrid s t n (k + 1), β u) atTop
      (𝓝 (∫ u in s..t, x u * β u)) := by
  have hint : ∀ a c : ℝ, IntervalIntegrable β volume a c := fun a c => by
    refine ⟨?_, ?_⟩ <;>
    · exact Measure.integrableOn_of_bounded (M := B) (by simp) hβ.aestronglyMeasurable
        (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hβB u)
  have hR := tendsto_riemann hst hx.continuousOn (hint s t) (fun u _ => hβB u)
  have hD : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
      (x (rgrid s t n (k + 1)) - x (rgrid s t n k)) *
        ∫ u in rgrid s t n k..rgrid s t n (k + 1), β u) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hβB 0)
    set δ := ε / (2 * (B * (t - s) + 1)) with hδ
    have hδpos : 0 < δ := div_pos hε (by nlinarith)
    obtain ⟨N, hN⟩ := (eventually_mesh_le hst hx.continuousOn hδpos).exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero]
    have hcell : ∀ k ∈ Finset.range (n + 1), |(x (rgrid s t n (k + 1)) - x (rgrid s t n k)) *
        ∫ u in rgrid s t n k..rgrid s t n (k + 1), β u| ≤
          δ * (B * (rgrid s t n (k + 1) - rgrid s t n k)) := by
      intro k hk
      have hk' := Finset.mem_range.1 hk
      have hmono := rgrid_mono hst n (Nat.le_succ k)
      rw [abs_mul]
      refine mul_le_mul ?_ ?_ (abs_nonneg _) hδpos.le
      · have := hN n hn k hk' _ ⟨hmono, le_rfl⟩
        rwa [Real.dist_eq] at this
      · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := rgrid s t n k)
          (b := rgrid s t n (k + 1)) (f := β) (C := B) fun u _ => by
            rw [Real.norm_eq_abs]; exact hβB u
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hmono)] at this
        linarith
    have hsum : ∑ k ∈ Finset.range (n + 1), δ * (B * (rgrid s t n (k + 1) - rgrid s t n k)) =
        δ * (B * (t - s)) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_sub (fun k => rgrid s t n k),
        rgrid_last, rgrid_zero]
    calc |∑ k ∈ Finset.range (n + 1), (x (rgrid s t n (k + 1)) - x (rgrid s t n k)) *
          ∫ u in rgrid s t n k..rgrid s t n (k + 1), β u|
        ≤ ∑ k ∈ Finset.range (n + 1), |(x (rgrid s t n (k + 1)) - x (rgrid s t n k)) *
          ∫ u in rgrid s t n k..rgrid s t n (k + 1), β u| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ δ * (B * (t - s)) := (Finset.sum_le_sum hcell).trans hsum.le
      _ < ε := by
        rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by nlinarith)]
        nlinarith [mul_nonneg hB0 (sub_nonneg.2 hst)]
  have := hR.add hD
  rw [add_zero] at this
  refine this.congr fun n => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

end Pathwise

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- The grid transform `Σ_k A_{t_k}(X_{t_{k+1}} − X_{t_k})` on `[s, t]`. -/
def gridIBP (A X : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), A (grid s t n k) ω * (X (grid s t n (k + 1)) ω - X (grid s t n k) ω)

theorem abs_setIntegral_Ioc_le {f : ℝ → ℝ} {B : ℝ} (hf : ∀ u, |f u| ≤ B) (r : ℝ≥0) :
    |∫ u in Ioc (0 : ℝ) r, f u| ≤ B * r := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) r) (f := f)
    measure_Ioc_lt_top (fun u _ => by rw [Real.norm_eq_abs]; exact hf u)
  rw [Real.norm_eq_abs] at h
  simpa [Measure.real, Real.volume_Ioc] using h

theorem intervalIntegrable_of_bound' {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ u, |f u| ≤ B) (a c : ℝ) : IntervalIntegrable f volume a c := by
  refine ⟨?_, ?_⟩ <;>
  · exact Measure.integrableOn_of_bounded (M := B) (by simp) hf.aestronglyMeasurable
      (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hB u)

theorem setIntegral_Ioc_sub {f : ℝ → ℝ} (hf : ∀ a c : ℝ, IntervalIntegrable f volume a c)
    {a c : ℝ≥0} (_hac : a ≤ c) :
    (∫ u in Ioc (0 : ℝ) c, f u) - ∫ u in Ioc (0 : ℝ) a, f u = ∫ u in (a : ℝ)..c, f u := by
  rw [← intervalIntegral.integral_of_le c.coe_nonneg, ← intervalIntegral.integral_of_le
    a.coe_nonneg]
  exact intervalIntegral.integral_interval_sub_left (hf 0 c) (hf 0 a)

omit [IsProbabilityMeasure Q] in
theorem aesm_indicator {m : MeasurableSpace Ω} {f : Ω → ℝ} (hf : AEStronglyMeasurable[m] f Q)
    {E : Set Ω} (hE : MeasurableSet[m] E) : AEStronglyMeasurable[m] (E.indicator f) Q := by
  obtain ⟨g, hg, hfg⟩ := hf
  exact ⟨E.indicator g, hg.indicator hE, hfg.indicator⟩

omit [IsProbabilityMeasure Q] in
theorem aesm_finset_sum {m : MeasurableSpace Ω} {ι : Type*} (s : Finset ι) {F : ι → Ω → ℝ}
    (hF : ∀ i ∈ s, AEStronglyMeasurable[m] (F i) Q) :
    AEStronglyMeasurable[m] (fun ω => ∑ i ∈ s, F i ω) Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (aestronglyMeasurable_const (m := m) (μ := Q) (b := (0 : ℝ)))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- **Integration by parts against a bounded drift.** -/
theorem hasMartingaleModification_ibp {X β A : ℝ≥0 → Ω → ℝ}
    (hX : HasMartingaleModification Q 𝓖 X) (hXc : ∀ᵐ ω ∂Q, Continuous fun t => X t ω)
    (hXb : ∀ T : ℝ≥0, ∃ C, ∀ᵐ ω ∂Q, ∀ t ≤ T, |X t ω| ≤ C) {B : ℝ} (hβb : ∀ t ω, |β t ω| ≤ B)
    (hβm : ∀ᵐ ω ∂Q, Measurable fun u : ℝ => β u.toNNReal ω)
    (hA : ∀ t ω, A t ω = ∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω)
    (hAm : ∀ t, AEStronglyMeasurable[𝓖 t] (A t) Q) :
    HasMartingaleModification Q 𝓖 (fun t ω => A t ω * X t ω -
      ∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω * X u.toNNReal ω) := by
  obtain ⟨M, hM, hMX⟩ := hX
  have hne : (univ : Set Ω).Nonempty :=
    nonempty_of_measure_ne_zero (μ := Q) (s := univ) (by simp)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hβb 0 hne.some)
  set G : ℝ≥0 → Ω → ℝ := fun t ω => A t ω * X t ω -
    ∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω * X u.toNNReal ω with hG
  -- pathwise convergence of the grid transforms
  have hlim : ∀ s t : ℝ≥0, s ≤ t → ∀ᵐ ω ∂Q,
      Tendsto (fun n => gridIBP A X s t n ω) atTop (𝓝 (G t ω - G s ω)) := by
    intro s t hst
    filter_upwards [hXc, hβm] with ω hc hm
    set x : ℝ → ℝ := fun u => X u.toNNReal ω
    set b : ℝ → ℝ := fun u => β u.toNNReal ω
    have hxc : Continuous x := hc.comp continuous_real_toNNReal
    have hbB : ∀ u, |b u| ≤ B := fun u => hβb _ _
    have hbi := intervalIntegrable_of_bound' hm hbB
    have hxbi : ∀ a c : ℝ, IntervalIntegrable (fun u => b u * x u) volume a c := fun a c =>
      (hbi a c).mul_continuousOn hxc.continuousOn
    have hst' : (s : ℝ) ≤ t := hst
    have hT := tendsto_gridIBP hxc hm hbB hst'
    have hgx : ∀ n k, X (grid s t n k) ω = x (rgrid s t n k) := fun n k => by
      simp only [x, ← coe_grid hst, Real.toNNReal_coe]
    have hgA : ∀ n k, A (grid s t n (k + 1)) ω - A (grid s t n k) ω =
        ∫ u in rgrid s t n k..rgrid s t n (k + 1), b u := fun n k => by
      rw [hA, hA, setIntegral_Ioc_sub hbi (grid_mono hst n (Nat.le_succ k)), coe_grid hst,
        coe_grid hst]
    have he : ∀ n, gridIBP A X s t n ω = A t ω * X t ω - A s ω * X s ω -
        ∑ k ∈ Finset.range (n + 1), x (rgrid s t n (k + 1)) *
          ∫ u in rgrid s t n k..rgrid s t n (k + 1), b u := fun n => by
      unfold gridIBP
      rw [sum_abel (fun k => A (grid s t n k) ω) (fun k => X (grid s t n k) ω) n]
      simp only [grid_last hst, grid_zero]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by rw [hgx, hgA]
    have hGd : G t ω - G s ω = A t ω * X t ω - A s ω * X s ω - ∫ u in (s : ℝ)..t, x u * b u := by
      simp only [hG]
      have := setIntegral_Ioc_sub hxbi hst
      have e : ∫ u in (s : ℝ)..t, x u * b u = ∫ u in (s : ℝ)..t, b u * x u := by
        congr 1; funext u; ring
      rw [e, ← this]
      ring
    rw [hGd]
    exact (tendsto_const_nhds.sub hT).congr fun n => (he n).symm
  -- uniform bound of the grid transforms
  have hAbd : ∀ t ω, |A t ω| ≤ B * t := fun t ω => by
    rw [hA]; exact abs_setIntegral_Ioc_le (fun u => hβb _ _) t
  have hbd : ∀ s t : ℝ≥0, s ≤ t → ∃ K, ∀ n, ∀ᵐ ω ∂Q, ‖gridIBP A X s t n ω‖ ≤ K := by
    intro s t hst
    obtain ⟨C, hC⟩ := hXb t
    have hC0 : 0 ≤ C := by
      obtain ⟨ω, hω⟩ := hC.exists
      exact (abs_nonneg _).trans (hω 0 zero_le)
    refine ⟨3 * (B * t * C), fun n => ?_⟩
    filter_upwards [hC, hβm] with ω hω hm
    have hbi := intervalIntegrable_of_bound' hm (fun u => hβb u.toNNReal ω)
    unfold gridIBP
    rw [sum_abel (fun k => A (grid s t n k) ω) (fun k => X (grid s t n k) ω) n]
    simp only [grid_last hst, grid_zero, Real.norm_eq_abs]
    have h1 : |A t ω * X t ω| ≤ B * t * C := by
      rw [abs_mul]; exact mul_le_mul (hAbd t ω) (hω t le_rfl) (abs_nonneg _) (by positivity)
    have h2 : |A s ω * X s ω| ≤ B * t * C := by
      rw [abs_mul]
      exact mul_le_mul ((hAbd s ω).trans (by gcongr)) (hω s hst) (abs_nonneg _) (by positivity)
    have hcell : ∀ k ∈ Finset.range (n + 1), |X (grid s t n (k + 1)) ω *
        (A (grid s t n (k + 1)) ω - A (grid s t n k) ω)| ≤
          C * (B * ((grid s t n (k + 1) : ℝ) - grid s t n k)) := by
      intro k hk
      have hkt : grid s t n (k + 1) ≤ t := by
        have := grid_mono hst n (Nat.succ_le_of_lt (Finset.mem_range.1 hk))
        rwa [grid_last hst] at this
      rw [abs_mul]
      refine mul_le_mul (hω _ hkt) ?_ (abs_nonneg _) hC0
      have hle := grid_mono hst n (Nat.le_succ k)
      rw [hA, hA, setIntegral_Ioc_sub hbi hle]
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (grid s t n k : ℝ)) (b := (grid s t n (k + 1) : ℝ))
        (f := fun u : ℝ => β u.toNNReal ω) (C := B) fun u _ => by
          rw [Real.norm_eq_abs]; exact hβb _ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hle))] at this
      linarith
    have hsum : ∑ k ∈ Finset.range (n + 1), C * (B * ((grid s t n (k + 1) : ℝ) - grid s t n k))
        = C * (B * ((t : ℝ) - s)) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_range_sub (fun k => (grid s t n k : ℝ)), grid_last hst, grid_zero]
    have h3 : |∑ k ∈ Finset.range (n + 1), X (grid s t n (k + 1)) ω *
        (A (grid s t n (k + 1)) ω - A (grid s t n k) ω)| ≤ B * t * C := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hcell).trans ?_)
      rw [hsum]
      have : (0 : ℝ) ≤ s := s.coe_nonneg
      nlinarith [mul_nonneg hB0 hC0]
    calc _ ≤ |A t ω * X t ω - A s ω * X s ω| + |∑ k ∈ Finset.range (n + 1),
          X (grid s t n (k + 1)) ω * (A (grid s t n (k + 1)) ω - A (grid s t n k) ω)| :=
          abs_sub _ _
      _ ≤ (|A t ω * X t ω| + |A s ω * X s ω|) + B * t * C := add_le_add (abs_sub _ _) h3
      _ ≤ 3 * (B * t * C) := by linarith
  -- measurability of the grid transforms
  have hmeasS : ∀ s t : ℝ≥0, s ≤ t → ∀ n, AEStronglyMeasurable[𝓖 t] (gridIBP A X s t n) Q := by
    intro s t hst n
    unfold gridIBP
    refine aesm_finset_sum _ fun k hk => ?_
    have hk := Finset.mem_range.1 hk
    have l0 : grid s t n k ≤ t := by
      have := grid_mono hst n hk.le; rwa [grid_last hst] at this
    have l1 : grid s t n (k + 1) ≤ t := by
      have := grid_mono hst n (Nat.succ_le_of_lt hk); rwa [grid_last hst] at this
    have hX' : ∀ j, grid s t n j ≤ t → AEStronglyMeasurable[𝓖 t] (X (grid s t n j)) Q :=
      fun j hj => (((hM.1 _).mono (𝓖.mono hj)).aestronglyMeasurable).congr (hMX _)
    exact ((hAm _).mono (𝓖.mono l0)).mul ((hX' _ l1).sub (hX' _ l0))
  -- zero mean on `𝓖_s`-sets
  have hzero : ∀ s t : ℝ≥0, s ≤ t → ∀ n, ∀ E, MeasurableSet[𝓖 s] E →
      ∫ ω in E, gridIBP A X s t n ω ∂Q = 0 := by
    intro s t hst n E hE
    have hEm : MeasurableSet E := 𝓖.le s E hE
    rw [← integral_indicator hEm]
    have he : E.indicator (gridIBP A X s t n) =ᵐ[Q] fun ω => ∑ k ∈ Finset.range (n + 1),
        E.indicator (A (grid s t n k)) ω * (M (grid s t n (k + 1)) ω - M (grid s t n k) ω) := by
      filter_upwards [ae_all_iff.2 fun j : ℕ => hMX (grid s t n j)] with ω hω
      by_cases hωE : ω ∈ E
      · simp only [Set.indicator_of_mem hωE, gridIBP, hω]
      · simp [Set.indicator_of_notMem hωE]
    have hgk : ∀ k ∈ Finset.range (n + 1), AEStronglyMeasurable[𝓖 (grid s t n k)]
        (E.indicator (A (grid s t n k))) Q ∧ ∀ᵐ ω ∂Q, ‖E.indicator (A (grid s t n k)) ω‖ ≤ B * t := by
      intro k hk
      have hk' := Finset.mem_range.1 hk
      have hsk : s ≤ grid s t n k := by
        have := grid_mono hst n (Nat.zero_le k); rwa [grid_zero] at this
      have hkt : grid s t n k ≤ t := by
        have := grid_mono hst n hk'.le; rwa [grid_last hst] at this
      refine ⟨aesm_indicator (hAm _) (𝓖.mono hsk E hE), Eventually.of_forall fun ω => ?_⟩
      rw [Real.norm_eq_abs]
      by_cases hωE : ω ∈ E
      · rw [Set.indicator_of_mem hωE]
        exact (hAbd _ ω).trans (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hkt) hB0)
      · rw [Set.indicator_of_notMem hωE, abs_zero]; positivity
    rw [integral_congr_ae he, integral_finsetSum]
    · refine Finset.sum_eq_zero fun k hk => ?_
      exact martingale_integral_mul_sub_eq_zero hM (grid_mono hst n (Nat.le_succ k))
        (hgk k hk).1 (hgk k hk).2
    · intro k hk
      exact ((hM.integrable _).sub (hM.integrable _)).bdd_mul
        ((hgk k hk).1.mono (𝓖.le _)) (hgk k hk).2
  -- measurability, bounds and integrability of `G`
  have hG0 : ∀ ω, G 0 ω = 0 := fun ω => by simp [hG, hA]
  have hGm : ∀ t, AEStronglyMeasurable[𝓖 t] (G t) Q := by
    intro t
    refine aestronglyMeasurable_of_tendsto_ae_sub (fun n => hmeasS 0 t zero_le n) ?_
    filter_upwards [hlim 0 t zero_le] with ω hω
    simpa [hG0] using hω
  have hGbd : ∀ t, ∃ K, ∀ᵐ ω ∂Q, ‖G t ω‖ ≤ K := by
    intro t
    obtain ⟨C, hC⟩ := hXb t
    have hC0 : 0 ≤ C := by
      obtain ⟨ω, hω⟩ := hC.exists
      exact (abs_nonneg _).trans (hω 0 zero_le)
    refine ⟨2 * (B * t * C), ?_⟩
    filter_upwards [hC] with ω hω
    have h1 : |A t ω * X t ω| ≤ B * t * C := by
      rw [abs_mul]; exact mul_le_mul (hAbd t ω) (hω t le_rfl) (abs_nonneg _) (by positivity)
    have h2 : |∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω * X u.toNNReal ω| ≤ B * C * t := by
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) t)
        (f := fun u => β u.toNNReal ω * X u.toNNReal ω) (C := B * C) measure_Ioc_lt_top
        (fun u hu => by
          have hut : u.toNNReal ≤ t := by
            rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le]; exact hu.2
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hβb _ _) (hω _ hut) (abs_nonneg _) hB0)
      rw [Real.norm_eq_abs] at h
      simpa [Measure.real, Real.volume_Ioc] using h
    rw [Real.norm_eq_abs]
    calc |G t ω| ≤ |A t ω * X t ω| + |∫ u in Ioc (0 : ℝ) t, β u.toNNReal ω * X u.toNNReal ω| :=
          abs_sub _ _
      _ ≤ 2 * (B * t * C) := by nlinarith
  have hGint : ∀ t, Integrable (G t) Q := fun t => by
    obtain ⟨K, hK⟩ := hGbd t
    exact Integrable.of_bound ((hGm t).mono (𝓖.le t)) K hK
  have hset : ∀ s t, s ≤ t → ∀ E, MeasurableSet[𝓖 s] E →
      ∫ ω in E, G t ω ∂Q = ∫ ω in E, G s ω ∂Q := by
    intro s t hst E hE
    obtain ⟨K, hK⟩ := hbd s t hst
    have hDCT := tendsto_integral_of_dominated_convergence (μ := Q.restrict E)
      (fun _ => K) (fun n => ((hmeasS s t hst n).mono (𝓖.le t)).restrict)
      (integrable_const _) (fun n => ae_restrict_of_ae (hK n))
      (ae_restrict_of_ae (hlim s t hst))
    have h0 : (fun n => ∫ ω in E, gridIBP A X s t n ω ∂Q) = fun _ => 0 :=
      funext fun n => hzero s t hst n E hE
    rw [h0] at hDCT
    have := tendsto_nhds_unique hDCT tendsto_const_nhds
    rw [integral_sub (hGint t).integrableOn (hGint s).integrableOn] at this
    linarith
  exact exists_martingale_modification hGint hGm hset

end BlockBand.Transmission.Dual
