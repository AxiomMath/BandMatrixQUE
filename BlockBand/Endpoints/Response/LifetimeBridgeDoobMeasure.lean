module

public import BlockBand.Endpoints.Response.LifetimeBridgeDoobRect

/-!
# The joint law of the path and the lifetime as a measure, from inputs 1 and 2

A step of the proof of the lifetime bridge lemma.

For a one-pair boundary dual realization from `z = (x, y)` and `0 < t₁ < ⋯ < t_k` (`T = t_k`):
* `lbkJointLaw`: `μ = (P|_{T < σ₀ < ∞}).map (Z_{t₁..t_k}, σ₀)` on `(ℝ²)^k × ℝ` (with the
  measurable lifetime `lbkExtinctionRat N`); `lbk_jointLaw_lintegral` integrates against it;
* `lbkJointDensity`: `ν = ((Leb ⊗ Leb|_{(0,∞)}).withDensity((D₀/2)(x+y) Π(zs) p_s(z_k, 0))).map
  ((zs, s) ↦ (zs, T + s))`; `lbk_jointDensity_lintegral` integrates against it;
* `lbk_jointLaw_eq_density`: `μ = ν`, given inputs 1 and 2 (rectangles `A ×ˢ Iic r` by
  `lbk_killed_rect_of_doob`, then `lbk_measure_ext_Iic_rect`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-- The killed joint law `(P|_{T < σ₀ < ∞}).map (Z_{t₁..t_k}, σ₀)` (measurable lifetime). -/
def lbkJointLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) {k : ℕ} (ts : Fin k → ℝ) : Measure ((Fin k → ℝ × ℝ) × ℝ) :=
  (P.restrict {ω | ENNReal.ofReal (lbkLastTime ts) < lbkExtinctionRat N ω ∧
      lbkExtinctionRat N ω < ⊤}).map
    fun ω => ((fun i => dualPoint X Y (ts i) ω), (lbkExtinctionRat N ω).toReal)

/-- The density `(D₀/2)(x+y) Π(zs) p_s(z_k, 0)` of the joint law in `(zs, s = σ₀ - T)`. -/
def lbkJointDens (D0 x y : ℝ) {k : ℕ} (ts : Fin k → ℝ) (q : (Fin k → ℝ × ℝ) × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (D0 / 2 * (x + y)) * lbkFddProd (lbkKernel D0) (x, y) ts q.1 *
    ENNReal.ofReal (lbkKernel D0 q.2 (lbkLastPoint (x, y) q.1) (0, 0))

/-- The explicit joint law: the density measure in `(zs, s)` pushed forward by
`(zs, s) ↦ (zs, T + s)`. -/
def lbkJointDensity (D0 x y : ℝ) {k : ℕ} (ts : Fin k → ℝ) : Measure ((Fin k → ℝ × ℝ) × ℝ) :=
  (((volume : Measure (Fin k → ℝ × ℝ)).prod (volume.restrict (Ioi (0 : ℝ)))).withDensity
    (lbkJointDens D0 x y ts)).map fun q => (q.1, lbkLastTime ts + q.2)

theorem lbk_jointDens_measurable {D0 : ℝ} (hD0 : 0 < D0) (x y : ℝ) {k : ℕ} (ts : Fin k → ℝ) :
    Measurable (lbkJointDens D0 x y ts) := by
  have hk := lbk_kernel_measurable hD0
  unfold lbkJointDens
  exact (measurable_const.mul ((lbk_fddProd_measurable hk (x, y) ts).comp measurable_fst)).mul
    (hk.comp (f := fun q : (Fin k → ℝ × ℝ) × ℝ =>
      (q.2, lbkLastPoint (x, y) q.1, ((0, 0) : ℝ × ℝ)))
      (measurable_snd.prodMk (((lbk_measurable_cons (x, y) (Fin.last k)).comp
        measurable_fst).prodMk measurable_const))).ennreal_ofReal

theorem lbk_jointDensity_lintegral {D0 : ℝ} (hD0 : 0 < D0) (x y : ℝ) {k : ℕ} (ts : Fin k → ℝ)
    {G : (Fin k → ℝ × ℝ) × ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ q, G q ∂lbkJointDensity D0 x y ts =
      ∫⁻ zs, ∫⁻ s in Ioi 0, lbkJointDens D0 x y ts (zs, s) * G (zs, lbkLastTime ts + s) := by
  have hdm := lbk_jointDens_measurable hD0 x y ts
  have hshift : Measurable fun q : (Fin k → ℝ × ℝ) × ℝ => (q.1, lbkLastTime ts + q.2) :=
    measurable_fst.prodMk (measurable_const.add measurable_snd)
  have hGs : Measurable fun q : (Fin k → ℝ × ℝ) × ℝ => G (q.1, lbkLastTime ts + q.2) :=
    hG.comp hshift
  rw [lbkJointDensity, lintegral_map hG hshift, lintegral_withDensity_eq_lintegral_mul _ hdm hGs,
    lintegral_prod _ (hdm.mul hGs).aemeasurable]
  simp only [Pi.mul_apply]

theorem lbk_jointDensity_rect {D0 : ℝ} (hD0 : 0 < D0) (x y : ℝ) {k : ℕ} (ts : Fin k → ℝ)
    {A : Set (Fin k → ℝ × ℝ)} (hA : MeasurableSet A) (r : ℝ) :
    lbkJointDensity D0 x y ts (A ×ˢ Iic r) =
      ENNReal.ofReal (D0 / 2 * (x + y)) * ∫⁻ zs, A.indicator 1 zs *
        lbkFddProd (lbkKernel D0) (x, y) ts zs *
          ∫⁻ s in Ioc 0 (r - lbkLastTime ts),
            ENNReal.ofReal (lbkKernel D0 s (lbkLastPoint (x, y) zs) (0, 0)) := by
  have hk := lbk_kernel_measurable hD0
  have hAr : MeasurableSet (A ×ˢ Iic r) := hA.prod measurableSet_Iic
  rw [← lintegral_indicator_one hAr, lbk_jointDensity_lintegral hD0 x y ts
    (measurable_one.indicator hAr), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun zs => ?_
  set T := lbkLastTime ts with hT
  set f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (lbkKernel D0 s (lbkLastPoint (x, y) zs) (0, 0))
    with hf
  have hfm : Measurable f :=
    (hk.comp (f := fun s : ℝ => (s, lbkLastPoint (x, y) zs, ((0, 0) : ℝ × ℝ)))
      (measurable_id.prodMk measurable_const)).ennreal_ofReal
  have hpt : ∀ s, lbkJointDens D0 x y ts (zs, s) * (A ×ˢ Iic r).indicator 1 (zs, T + s) =
      (ENNReal.ofReal (D0 / 2 * (x + y)) * (A.indicator 1 zs *
        lbkFddProd (lbkKernel D0) (x, y) ts zs)) * (Iic (r - T)).indicator f s := by
    intro s
    have hiff : T + s ≤ r ↔ s ≤ r - T := le_sub_iff_add_le'.symm
    by_cases hzA : zs ∈ A
    · by_cases hsr : s ≤ r - T
      · rw [indicator_of_mem (mem_prod.2 ⟨hzA, hiff.2 hsr⟩), indicator_of_mem hzA,
          indicator_of_mem (show s ∈ Iic (r - T) from hsr)]
        simp only [lbkJointDens, Pi.one_apply, hf]
        ring
      · rw [indicator_of_notMem (fun h => hsr (hiff.1 (mem_prod.1 h).2)),
          indicator_of_notMem (show s ∉ Iic (r - T) from hsr), mul_zero, mul_zero]
    · rw [indicator_of_notMem (fun h => hzA (mem_prod.1 h).1), indicator_of_notMem hzA,
        mul_zero, zero_mul, mul_zero, zero_mul]
  simp_rw [hpt]
  rw [lintegral_const_mul _ (hfm.indicator measurableSet_Iic), lintegral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioi]
  ring

theorem lbk_jointLaw_lintegral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {x y : ℝ}
    {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (hP : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) {k : ℕ} (ts : Fin k → ℝ)
    {G : (Fin k → ℝ × ℝ) × ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ q, G q ∂lbkJointLaw P N X Y ts =
      ∫⁻ ω, {ω | ENNReal.ofReal (lbkLastTime ts) < lbkExtinctionRat N ω ∧
        lbkExtinctionRat N ω < ⊤}.indicator
          (fun ω => G ((fun i => dualPoint X Y (ts i) ω), (lbkExtinctionRat N ω).toReal)) ω ∂P := by
  obtain ⟨hτm, -⟩ := lbk_extinction_ae_eq hP
  have hSm : MeasurableSet {ω | ENNReal.ofReal (lbkLastTime ts) < lbkExtinctionRat N ω ∧
      lbkExtinctionRat N ω < ⊤} :=
    (measurableSet_lt measurable_const hτm).inter (measurableSet_lt hτm measurable_const)
  rw [lbkJointLaw, lintegral_map hG ((lbk_dualPath_measurable hP ts).prodMk hτm.ennreal_toReal),
    lintegral_indicator hSm]

theorem lbk_jointLaw_rect {D0 : ℝ} (hD0 : 0 < D0) (h1 : LbkCornerHeatIdentity D0)
    (h2 : LbkDoobKilledLaw D0) {x y : ℝ}
    (hxy : IsDualStart ![x] ![y]) {Ω : Type} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m}
    {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (hP : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) {k : ℕ} {ts : Fin k → ℝ}
    (hts : StrictMono ts) (htp : ∀ i, 0 < ts i) {A : Set (Fin k → ℝ × ℝ)}
    (hA : MeasurableSet A) (r : ℝ) :
    lbkJointLaw P N X Y ts (A ×ˢ Iic r) = lbkJointDensity D0 x y ts (A ×ˢ Iic r) := by
  obtain ⟨hτm, -⟩ := lbk_extinction_ae_eq hP
  have hT0 : 0 ≤ lbkLastTime ts := lbk_lastTime_nonneg htp
  have hAr : MeasurableSet (A ×ˢ Iic r) := hA.prod measurableSet_Iic
  have hΦm := (lbk_dualPath_measurable hP ts).prodMk hτm.ennreal_toReal
  rw [lbk_jointDensity_rect hD0 x y ts hA r, lbkJointLaw, Measure.map_apply hΦm hAr,
    Measure.restrict_apply (hΦm hAr)]
  rcases le_or_gt r (lbkLastTime ts) with hr | hr
  · have hJ : ∀ zs : Fin k → ℝ × ℝ, ∫⁻ s in Ioc 0 (r - lbkLastTime ts),
        ENNReal.ofReal (lbkKernel D0 s (lbkLastPoint (x, y) zs) (0, 0)) = 0 := fun zs => by
      rw [Ioc_eq_empty (not_lt.2 (sub_nonpos.2 hr)), Measure.restrict_empty,
        lintegral_zero_measure]
    simp only [hJ, mul_zero, lintegral_zero]
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_Iic, mem_ofPred_eq] at hω
    have hlt := (ENNReal.ofReal_lt_iff_lt_toReal hT0 hω.2.2.ne).1 hω.2.1
    exact absurd (hω.1.2.trans hr) (not_le.2 hlt)
  · rw [← lbk_killed_rect_of_doob hD0 h1 h2 hxy hP hts htp hA hr]
    congr 1
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_Iic, mem_ofPred_eq]
    have hr0 : 0 ≤ r := hT0.trans hr.le
    constructor
    · rintro ⟨⟨hA', hle⟩, hT', hfin⟩
      exact ⟨hA', hT', (ENNReal.le_ofReal_iff_toReal_le hfin.ne hr0).2 hle⟩
    · rintro ⟨hA', hT', hle⟩
      have hne : lbkExtinctionRat N ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
      exact ⟨⟨hA', (ENNReal.le_ofReal_iff_toReal_le hne hr0).1 hle⟩, hT', lt_top_iff_ne_top.2 hne⟩

/-- **The joint law of the path and the lifetime is the explicit density measure**, from inputs 1
and 2. -/
theorem lbk_jointLaw_eq_density {D0 : ℝ} (hD0 : 0 < D0) (h1 : LbkCornerHeatIdentity D0)
    (h2 : LbkDoobKilledLaw D0) {x y : ℝ}
    (hxy : IsDualStart ![x] ![y]) {Ω : Type} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m}
    {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (hP : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) {k : ℕ} {ts : Fin k → ℝ}
    (hts : StrictMono ts) (htp : ∀ i, 0 < ts i) :
    lbkJointLaw P N X Y ts = lbkJointDensity D0 x y ts := by
  have := hP.prob
  have : IsFiniteMeasure (lbkJointLaw P N X Y ts) := by
    unfold lbkJointLaw
    infer_instance
  exact lbk_measure_ext_Iic_rect fun A hA r => lbk_jointLaw_rect hD0 h1 h2 hxy hP hts htp hA r

end BlockBand.Endpoints
