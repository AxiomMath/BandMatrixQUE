module
public import BlockBand.SourceProcess.Stochastic.Representation.Assoc
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# A Brownian motion from a vector integral with identity bracket

Setting: `(Ω, m₀, Q)` a probability space, raw filtration `𝓖` (no usual conditions),
a vector integrator `h : IsL2IntegratorVec Q 𝓖 Z a` (finite index `ι`, symmetric `a`), and a
bounded raw-predictable integrand matrix `H : Fin m → ι → ℝ × Ω → ℝ` whose bracket density is
the identity: a.s., for every `r > 0`, `∑_{ij} H_{ki}(r) H_{lj}(r) a^{ij}_r = δ_{kl}`.

* `driverInt h hH T k = ∑_i ∫_0^· H_{ki} dZ^i` (horizon `T`, `h.vecCont`).
* `driverInt_horizon`: horizon consistency, a.s. for all `t ≤ T ≤ T'`.
* `driverInt_cross`: `X^k X^l - δ_{kl} (t ∧ T)` has a martingale modification.
* **`exists_brownian_of_driver`**: there is a `𝓖`-Brownian motion `B` (`IsFiltrationBrownian`,
  all times `t ∈ [0, ∞)`) with `B^k_t = X^k_t` a.s. for every horizon `T` and every `t ≤ T`.
-/

namespace BlockBand.SourceProcess.Stochastic.Representation
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Integral (leftPoint leftPoint_lt dyadicStep)
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] {Z : ι → ℝ≥0 → Ω → ℝ}
  {a : ι → ι → ℝ≥0 → Ω → ℝ} {m : ℕ}

/-- The horizon-`T` integrals `X^k = ∑_i ∫_0^· H_{ki} dZ^i`. -/
def driverInt [IsFiniteMeasure Q] (h : IsL2IntegratorVec Q 𝓖 Z a)
    {H : Fin m → ι → ℝ × Ω → ℝ} (hH : ∀ k i, IsBddPred 𝓖 (H k i)) (T : ℝ≥0) (k : Fin m) :
    ℝ≥0 → Ω → ℝ :=
  haveI := h.isFiniteMeasure_bar T
  h.vecCont T (fun i => bpL2 (barMeasure Q a T) (hH k i))

section Finite

variable [IsFiniteMeasure Q] (h : IsL2IntegratorVec Q 𝓖 Z a) {H : Fin m → ι → ℝ × Ω → ℝ}
  (hH : ∀ k i, IsBddPred 𝓖 (H k i))

theorem driverInt_continuous (T : ℝ≥0) (k : Fin m) :
    ∀ᵐ ω ∂Q, Continuous fun t => driverInt h hH T k t ω :=
  haveI := h.isFiniteMeasure_bar T
  (h.vecCont_spec T _).1

theorem driverInt_martingale (T : ℝ≥0) (k : Fin m) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y 𝓖 Q ∧ ∀ t, Y t =ᵐ[Q] driverInt h hH T k t :=
  haveI := h.isFiniteMeasure_bar T
  (h.vecCont_spec T _).2.2.1

theorem driverInt_zero (T : ℝ≥0) (k : Fin m) (ω : Ω) : driverInt h hH T k 0 ω = 0 := by
  simp only [driverInt, IsL2IntegratorVec.vecCont]
  exact Finset.sum_eq_zero fun i _ => by rw [(h.coord i).contIntegral_zero T]; rfl

/-- **Horizon consistency of the driver integrals.** -/
theorem driverInt_horizon {T T' : ℝ≥0} (hT : T ≤ T') (k : Fin m) :
    ∀ᵐ ω ∂Q, ∀ t ≤ T, driverInt h hH T' k t ω = driverInt h hH T k t ω := by
  have := h.isFiniteMeasure_bar T
  have := h.isFiniteMeasure_bar T'
  have hr (i : ι) : predRestrict 𝓖 (bracketMeasure_mono Q (a i i) hT)
      (h.restr T' i (bpL2 (barMeasure Q a T') (hH k i))) =
      h.restr T i (bpL2 (barMeasure Q a T) (hH k i)) := by
    refine predL2_ext 𝓖 ?_
    have hle1 := bracketMeasure_mono Q (a i i) hT
    have hle2 := h.coord_le_bar T' i
    have hle3 := h.coord_le_bar T i
    filter_upwards [predRestrict_coeFn 𝓖 hle1 (h.restr T' i (bpL2 (barMeasure Q a T') (hH k i))),
      (h.restr_coeFn T' i _).filter_mono (ae_mono hle1),
      ((bpL2_coeFn (μ := barMeasure Q a T') (hH k i)).filter_mono (ae_mono hle2)).filter_mono
        (ae_mono hle1),
      h.restr_coeFn T i _, (bpL2_coeFn (μ := barMeasure Q a T) (hH k i)).filter_mono
        (ae_mono hle3)] with p h1 h2 h3 h4 h5
    rw [h1, h2, h3, h4, h5]
  have hi (i : ι) := (h.coord i).contIntegral_horizon_all hT
    (h.restr T' i (bpL2 (barMeasure Q a T') (hH k i)))
  filter_upwards [ae_all_iff.2 hi] with ω hω t ht
  simp only [driverInt, IsL2IntegratorVec.vecCont]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hω i t ht, hr i]

omit [IsFiniteMeasure Q] in
include h in
/-- The pathwise cross term depends only on the `ν̄_T`-class of the integrands. -/
theorem crossTerm_congr_ae [SFinite Q] (hs : ∀ i j t ω, a i j t ω = a j i t ω) {T : ℝ≥0}
    (i j : ι) {f f' g g' : ℝ × Ω → ℝ} (hf : StronglyMeasurable f)
    (hf' : StronglyMeasurable f') (hg : StronglyMeasurable g) (hg' : StronglyMeasurable g')
    (hff : f =ᵐ[barMeasure Q a T] f') (hgg : g =ᵐ[barMeasure Q a T] g') :
    ∀ᵐ ω ∂Q, ∀ u ≤ T, crossTerm a i j f g u ω = crossTerm a i j f' g' u ω := by
  have hmd : Measurable fun p : ℝ × Ω => ENNReal.ofReal (traceA a p.1.toNNReal p.2) :=
    ENNReal.measurable_ofReal.comp h.measurable_trace
  have h1 : ∀ᵐ p ∂timeProbMeasure T Q, ENNReal.ofReal (traceA a p.1.toNNReal p.2) ≠ 0 →
      (f p = f' p ∧ g p = g' p) :=
    (ae_withDensity_iff hmd).1 (hff.and hgg)
  have h2 : ∀ᵐ p ∂timeProbMeasure T Q, f p * g p * a i j p.1.toNNReal p.2 =
      f' p * g' p * a i j p.1.toNNReal p.2 := by
    filter_upwards [h1] with p hp
    by_cases ha : a i j p.1.toNNReal p.2 = 0
    · rw [ha, mul_zero, mul_zero]
    · have htr : 0 < traceA a p.1.toNNReal p.2 :=
        (abs_pos.2 ha).trans_le (h.abs_le_trace hs i j _ _)
      obtain ⟨e1, e2⟩ := hp (ENNReal.ofReal_pos.2 htr).ne'
      rw [e1, e2]
  have hmeas : MeasurableSet {p : ℝ × Ω | f p * g p * a i j p.1.toNNReal p.2 =
      f' p * g' p * a i j p.1.toNNReal p.2} :=
    measurableSet_eq_fun ((hf.measurable.mul hg.measurable).mul (h.measurable i j))
      ((hf'.measurable.mul hg'.measurable).mul (h.measurable i j))
  rw [timeProbMeasure, Measure.ae_prod_iff_ae_ae hmeas, Measure.ae_ae_comm hmeas] at h2
  filter_upwards [h2] with ω hω u hu
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hω] with r hr hru
  exact hr ⟨hru.1, hru.2.trans (NNReal.coe_le_coe.2 hu)⟩

omit [IsFiniteMeasure Q] in
include hH in
/-- With identity bracket density, the summed cross terms are `δ_{kl} u`. -/
theorem sum_crossTerm_eq {ω : Ω}
    (hint : ∀ i j, ∀ t : ℝ≥0, IntegrableOn (fun r : ℝ => a i j r.toNNReal ω) (Ioc 0 t))
    (hω : ∀ r : ℝ, 0 < r → ∀ k l, ∑ i, ∑ j, H k i (r, ω) * H l j (r, ω) * a i j r.toNNReal ω =
      if k = l then 1 else 0) (k l : Fin m) (u : ℝ≥0) :
    ∑ i, ∑ j, crossTerm a i j (H k i) (H l j) u ω = if k = l then (u : ℝ) else 0 := by
  have hI (i j : ι) : IntegrableOn (fun r => H k i (r, ω) * H l j (r, ω) *
      a i j r.toNNReal ω) (Ioc (0 : ℝ) u) := by
    obtain ⟨C, -, hC⟩ := (hH k i).bdd
    obtain ⟨D, -, hD⟩ := (hH l j).bdd
    have hm (i' : ι) (k' : Fin m) : Measurable fun r : ℝ => H k' i' (r, ω) :=
      ((hH k' i').sm.mono (predictableSpace_le _)).measurable.comp
        (measurable_id.prodMk measurable_const)
    refine Integrable.bdd_mul (c := C * D) (hint i j u) ((hm i k).mul (hm j l)).aestronglyMeasurable
      (Eventually.of_forall fun r => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hC _) (hD _) (abs_nonneg _) ((abs_nonneg _).trans (hC (r, ω)))
  simp only [crossTerm]
  have e1 : ∀ i, ∑ j, ∫ r in Ioc (0 : ℝ) u, H k i (r, ω) * H l j (r, ω) * a i j r.toNNReal ω =
      ∫ r in Ioc (0 : ℝ) u, ∑ j, H k i (r, ω) * H l j (r, ω) * a i j r.toNNReal ω :=
    fun i => (integral_finsetSum _ fun j _ => hI i j).symm
  rw [Finset.sum_congr rfl fun i _ => e1 i,
    ← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun r hr => hω r hr.1 k l)]
  split_ifs <;> simp

/-- **The cross bracket of the driver integrals.** -/
theorem driverInt_cross (hs : ∀ i j t ω, a i j t ω = a j i t ω)
    (hHaH : ∀ᵐ ω ∂Q, ∀ r : ℝ, 0 < r → ∀ k l,
      ∑ i, ∑ j, H k i (r, ω) * H l j (r, ω) * a i j r.toNNReal ω = if k = l then 1 else 0)
    (T : ℝ≥0) (k l : Fin m) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y 𝓖 Q ∧ ∀ t, Y t =ᵐ[Q] fun ω =>
      driverInt h hH T k t ω * driverInt h hH T l t ω -
        if k = l then ((min t T : ℝ≥0) : ℝ) else 0 := by
  have := h.isFiniteMeasure_bar T
  set μ := barMeasure Q a T
  choose Y hY hYe using fun p : ι × ι => h.cross_martingale T hs p.1 p.2
    (bpL2 μ (hH k p.1)) (bpL2 μ (hH l p.2))
  refine ⟨fun t ω => ∑ i, ∑ j, Y (i, j) t ω, martingale_finset_sum _ fun i =>
    martingale_finset_sum _ fun j => hY (i, j), fun t => ?_⟩
  have hcg (p : ι × ι) := crossTerm_congr_ae h hs (T := T) p.1 p.2
    (Lp.stronglyMeasurable _) ((hH k p.1).sm.mono (predictableSpace_le _))
    (Lp.stronglyMeasurable _) ((hH l p.2).sm.mono (predictableSpace_le _))
    (bpL2_coeFn (μ := μ) (hH k p.1)) (bpL2_coeFn (μ := μ) (hH l p.2))
  filter_upwards [ae_all_iff.2 fun p : ι × ι => hYe p t, ae_all_iff.2 hcg, hHaH,
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => h.integrable i j] with ω h1 h2 h3 h4
  simp only [h1, Finset.sum_sub_distrib]
  have e : ∑ i, ∑ j, crossTerm a i j ((bpL2 μ (hH k i) : Lp ℝ 2 μ) : ℝ × Ω → ℝ)
      ((bpL2 μ (hH l j) : Lp ℝ 2 μ) : ℝ × Ω → ℝ) (min t T) ω =
      if k = l then ((min t T : ℝ≥0) : ℝ) else 0 := by
    rw [← sum_crossTerm_eq hH h4 h3 k l (min t T)]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      h2 (i, j) _ (min_le_right t T)
  rw [e]
  congr 1
  simp only [driverInt, IsL2IntegratorVec.vecCont, Finset.sum_mul_sum]
  rfl

end Finite

section Brownian

variable [IsProbabilityMeasure Q] (h : IsL2IntegratorVec Q 𝓖 Z a) {H : Fin m → ι → ℝ × Ω → ℝ}
  (hH : ∀ k i, IsBddPred 𝓖 (H k i))

/-- **A Brownian motion from a vector integral with identity bracket density** (all times
`t ∈ [0, ∞)`). -/
theorem exists_brownian_of_driver (hs : ∀ i j t ω, a i j t ω = a j i t ω)
    (hHaH : ∀ᵐ ω ∂Q, ∀ r : ℝ, 0 < r → ∀ k l,
      ∑ i, ∑ j, H k i (r, ω) * H l j (r, ω) * a i j r.toNNReal ω = if k = l then 1 else 0) :
    ∃ B : ℝ≥0 → Ω → Fin m → ℝ, IsFiltrationBrownian Q 𝓖 B ∧
      ∀ T : ℝ≥0, ∀ k, ∀ t ≤ T, (fun ω => B t ω k) =ᵐ[Q] driverInt h hH T k t := by
  choose M hM hMe using fun (n : ℕ) (k : Fin m) => driverInt_martingale h hH n k
  have consX : ∀ n n' : ℕ, n ≤ n' → ∀ k, ∀ᵐ ω ∂Q, ∀ t ≤ (n : ℝ≥0), driverInt h hH (n' : ℝ≥0) k t ω = driverInt h hH (n : ℝ≥0) k t ω :=
    fun n n' hn k => driverInt_horizon h hH (Nat.cast_le.2 hn) k
  have consM : ∀ k, ∀ n n' : ℕ, n ≤ n' → ∀ t : ℝ≥0, t ≤ n → M n' k t =ᵐ[Q] M n k t := by
    intro k n n' hn t ht
    filter_upwards [hMe n' k t, hMe n k t, consX n n' hn k] with ω h1 h2 h3
    rw [h1, h2, h3 t ht]
  set V : ℝ≥0 → Ω → Fin m → ℝ := fun t ω k => M ⌈t⌉₊ k t ω with hVdef
  have hV : ∀ t, StronglyMeasurable[𝓖 t] (V t) := fun t =>
    (@measurable_pi_iff Ω (Fin m) (fun _ => ℝ) (𝓖 t) _ _ |>.2
      fun k => ((hM ⌈t⌉₊ k).1 t).measurable).stronglyMeasurable
  set B : ℝ≥0 → Ω → Fin m → ℝ := fun t ω => predVersion V ((t : ℝ), ω) with hBdef
  -- the good set
  have hgood : ∀ᵐ ω ∂Q, (∀ (n : ℕ) k, Continuous fun t => driverInt h hH (n : ℝ≥0) k t ω) ∧
      ∀ N j n : ℕ, ((j : ℝ≥0) * dyadicStep N ≤ n) →
        V ((j : ℝ≥0) * dyadicStep N) ω = fun k => driverInt h hH (n : ℝ≥0) k ((j : ℝ≥0) * dyadicStep N) ω := by
    have hc : ∀ᵐ ω ∂Q, ∀ (n : ℕ) k, Continuous fun t => driverInt h hH (n : ℝ≥0) k t ω :=
      ae_all_iff.2 fun n => ae_all_iff.2 fun k => driverInt_continuous h hH n k
    have hd : ∀ᵐ ω ∂Q, ∀ N j n : ℕ, ∀ k, ((j : ℝ≥0) * dyadicStep N ≤ n) →
        V ((j : ℝ≥0) * dyadicStep N) ω k = driverInt h hH (n : ℝ≥0) k ((j : ℝ≥0) * dyadicStep N) ω := by
      refine ae_all_iff.2 fun N => ae_all_iff.2 fun j => ae_all_iff.2 fun n =>
        ae_all_iff.2 fun k => ?_
      set q : ℝ≥0 := (j : ℝ≥0) * dyadicStep N
      by_cases hq : q ≤ n
      · filter_upwards [hMe ⌈q⌉₊ k q, consX ⌈q⌉₊ n (Nat.ceil_le.2 hq) k] with ω h1 h2 _
        simp only [hVdef]
        rw [h1, ← h2 q (Nat.le_ceil q)]
      · exact ae_of_all _ fun ω h => absurd h hq
    filter_upwards [hc, hd] with ω h1 h2
    exact ⟨h1, fun N j n hq => funext fun k => h2 N j n k hq⟩
  have hpath : ∀ᵐ ω ∂Q, ∀ n : ℕ, ∀ t : ℝ≥0, t ≤ n → B t ω = fun k => driverInt h hH (n : ℝ≥0) k t ω := by
    filter_upwards [hgood] with ω ⟨hc, hd⟩ n t ht
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | hpos
    · subst h0
      simp only [hBdef, NNReal.coe_zero, predVersion_zero]
      funext k
      exact (driverInt_zero h hH n k ω).symm
    · have hpos' : (0 : ℝ) < t := NNReal.coe_pos.2 hpos
      have hcong : predVersion V ((t : ℝ), ω) =
          predVersion (fun s ω' k => driverInt h hH (n : ℝ≥0) k s ω') ((t : ℝ), ω) := by
        refine predVersion_congr fun N => ?_
        have hlt := leftPoint_lt N hpos'
        exact hd N _ n ((NNReal.coe_le_coe.1 (hlt.le.trans (NNReal.coe_le_coe.2 ht))))
      simp only [hBdef, hcong]
      rw [predVersion_eq (continuous_pi fun k => hc n k) hpos', Real.toNNReal_coe]
  -- Lévy
  have hcont : ∀ᵐ ω ∂Q, Continuous fun t => B t ω := by
    filter_upwards [hgood, hpath] with ω ⟨hc, _⟩ hp
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt t₀
    have hev : (fun t => fun k => driverInt h hH (n : ℝ≥0) k t ω) =ᶠ[𝓝 t₀] fun t => B t ω := by
      filter_upwards [Iio_mem_nhds hn] with t ht
      exact (hp n t (le_of_lt ht)).symm
    exact (continuous_pi fun k => hc n k).continuousAt.congr hev
  have hBX : ∀ k, ∀ t, (fun ω => B t ω k) =ᵐ[Q] driverInt h hH (⌈t⌉₊ : ℝ≥0) k t := fun k t => by
    filter_upwards [hpath] with ω hω
    rw [hω ⌈t⌉₊ t (Nat.le_ceil t)]
  have hmart : ∀ k, HasMartingaleModification Q 𝓖 fun t ω => B t ω k := by
    intro k
    refine ⟨fun t => M ⌈t⌉₊ k t, martingale_glue (fun n => hM n k) (consM k), fun t => ?_⟩
    exact (hMe ⌈t⌉₊ k t).trans (hBX k t).symm
  have hbr : ∀ k l, HasMartingaleModification Q 𝓖 fun t ω =>
      B t ω k * B t ω l - if k = l then (t : ℝ) else 0 := by
    intro k l
    choose K hK hKe using fun n : ℕ => driverInt_cross h hH hs hHaH n k l
    have hKe' : ∀ n : ℕ, ∀ t : ℝ≥0, t ≤ n → K n t =ᵐ[Q] fun ω =>
        driverInt h hH (n : ℝ≥0) k t ω * driverInt h hH (n : ℝ≥0) l t ω - if k = l then (t : ℝ) else 0 := by
      intro n t ht
      filter_upwards [hKe n t] with ω hω
      rw [hω, min_eq_left ht]
    have consK : ∀ n n' : ℕ, n ≤ n' → ∀ t : ℝ≥0, t ≤ n → K n' t =ᵐ[Q] K n t := by
      intro n n' hn t ht
      filter_upwards [hKe' n' t (ht.trans (Nat.cast_le.2 hn)), hKe' n t ht,
        consX n n' hn k, consX n n' hn l] with ω h1 h2 h3 h4
      rw [h1, h2, h3 t ht, h4 t ht]
    refine ⟨fun t => K ⌈t⌉₊ t, martingale_glue hK consK, fun t => ?_⟩
    filter_upwards [hKe' ⌈t⌉₊ t (Nat.le_ceil t), hBX k t, hBX l t] with ω h1 h2 h3
    rw [h1, ← h2, ← h3]
  have hlevy : IsLevyMartingale Q 𝓖 B :=
    ⟨isStronglyProgressive_predVersion 𝓖 hV, hcont,
      ae_of_all _ (fun ω => by simp only [hBdef, NNReal.coe_zero, predVersion_zero]), hmart,
      hbr⟩
  refine ⟨B, hlevy.isFiltrationBrownian, fun T k t ht => ?_⟩
  filter_upwards [hpath, driverInt_horizon h hH (Nat.le_ceil T) k] with ω h1 h2
  rw [h1 ⌈T⌉₊ t (ht.trans (Nat.le_ceil T))]
  exact h2 t ht

end Brownian

end BlockBand.SourceProcess.Stochastic.Representation
