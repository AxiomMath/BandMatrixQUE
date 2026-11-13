module

public import BlockBand.Endpoints.Response.LifetimeBridgeDoobAux

/-!
# The joint law of the path and the lifetime on rectangles, from inputs 1 and 2

A step of the proof of the lifetime bridge lemma (the appended-time argument).

**Proved here** (`lbk_killed_rect_of_doob`): for every one-pair boundary dual realization from
`z = (x, y)`, `0 < t₁ < ⋯ < t_k` (`T = t_k`, `t₀ = 0`), measurable `A ⊆ (ℝ²)^k` and `r > T`,
`P(Z_{t₁..t_k} ∈ A, T < σ₀ ≤ r) =
  (D₀/2)(x+y) ∫_A p_{t₁}(z,z₁)⋯p_{t_k-t_{k-1}}(z_{k-1},z_k) ∫_{(0, r-T]} p_s(z_k, 0) ds dzs`,
with `σ₀` replaced by its measurable version `lbkExtinctionRat N` (a.s. equal).

Proof: input 2 at the `k` times with `F = 1_A` gives `P(Z ∈ A, T < σ₀) = (x+y)∫_A Π·H(z_k)`;
input 2 at the `k + 1` times `(t₁, …, t_k, r)` with `F = 1_A ∘ init`, split along
`(ℝ²)^{k+1} ≅ ℝ² × (ℝ²)^k` (`MeasurableEquiv.piFinSuccAbove` at the last index), gives
`P(Z ∈ A, r < σ₀) = (x+y)∫_A Π·P_{r-T}H(z_k)`; input 1 at `z_k` (off the null corner, and on
`{Π ≠ 0}`, where `z_k` lies in the strip) gives `H(z_k) = P_{r-T}H(z_k) + (D₀/2)∫_{(0,r-T]}
p_s(z_k,0) ds`; subtract (all terms finite, as probabilities). No Markov input is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

theorem lbk_harm_measurable : Measurable lbkHarm := by
  unfold lbkHarm
  exact (measurable_fst.add measurable_snd).inv

theorem lbk_dualPath_measurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {p : ℕ}
    {x y : Fin p → ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (hP : IsBoundaryDualProcess P 𝓖 D0 x y N X Y) {k : ℕ} (ts : Fin k → ℝ) :
    Measurable fun ω => (fun i => dualPoint X Y (ts i) ω : Fin k → ℝ × ℝ) := by
  refine Measurable.of_eval fun i => ?_
  exact ((measurable_pi_apply 0).comp ((hP.adapted _).2.1.mono (𝓖.le _) le_rfl)).prodMk
    ((measurable_pi_apply 0).comp ((hP.adapted _).2.2.mono (𝓖.le _) le_rfl))

/-- Input 2 with `F = 1_A`, as the probability of an event (with the measurable lifetime). -/
theorem lbk_doob_indicator {D0 : ℝ} (h2 : LbkDoobKilledLaw D0) {x y : ℝ}
    (hxy : IsDualStart ![x] ![y]) {Ω : Type} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m}
    {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (hP : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) {k : ℕ} {ts : Fin k → ℝ}
    (hts : StrictMono ts) (htp : ∀ i, 0 < ts i) {A : Set (Fin k → ℝ × ℝ)}
    (hA : MeasurableSet A) :
    P {ω | (fun i => dualPoint X Y (ts i) ω) ∈ A ∧
        ENNReal.ofReal (lbkLastTime ts) < lbkExtinctionRat N ω} =
      ∫⁻ zs, A.indicator 1 zs * lbkFddProd (lbkKernel D0) (x, y) ts zs *
        ENNReal.ofReal ((x + y) * lbkHarm (lbkLastPoint (x, y) zs)) := by
  classical
  obtain ⟨hτm, hτ⟩ := lbk_extinction_ae_eq hP
  have hS : MeasurableSet {ω | (fun i => dualPoint X Y (ts i) ω) ∈ A ∧
      ENNReal.ofReal (lbkLastTime ts) < lbkExtinctionRat N ω} :=
    (lbk_dualPath_measurable hP ts hA).inter (measurableSet_lt measurable_const hτm)
  rw [← lbk_lintegral_ite_one hS,
    ← h2 x y hxy Ω m 𝓖 P N X Y hP k ts hts htp (A.indicator 1) (measurable_one.indicator hA)]
  refine lintegral_congr_ae ?_
  filter_upwards [hτ] with ω hω
  rw [hω]
  by_cases h1 : (fun i => dualPoint X Y (ts i) ω) ∈ A <;>
    by_cases h3 : ENNReal.ofReal (lbkLastTime ts) < lbkExtinctionRat N ω <;> simp [h1, h3]

/-- **The appended-time step**: input 2 at `(t₁, …, t_k, r)` with `F = 1_A ∘ init` is
`P(Z ∈ A, r < σ₀) = ∫_A Π · (x + y) P_{r - T}H(z_k)`. -/
theorem lbk_doob_snoc {D0 : ℝ} (hD0 : 0 < D0) (h2 : LbkDoobKilledLaw D0) {x y : ℝ}
    (hxy : IsDualStart ![x] ![y]) {Ω : Type} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m}
    {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (hP : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) {k : ℕ} {ts : Fin k → ℝ}
    (hts : StrictMono ts) (htp : ∀ i, 0 < ts i) {A : Set (Fin k → ℝ × ℝ)}
    (hA : MeasurableSet A) {r : ℝ} (hr : lbkLastTime ts < r) :
    P {ω | (fun i => dualPoint X Y (ts i) ω) ∈ A ∧ ENNReal.ofReal r < lbkExtinctionRat N ω} =
      ∫⁻ zs, A.indicator 1 zs * lbkFddProd (lbkKernel D0) (x, y) ts zs *
        ENNReal.ofReal (x + y) *
          ∫⁻ w, ENNReal.ofReal (lbkKernel D0 (r - lbkLastTime ts) (lbkLastPoint (x, y) zs) w) *
            ENNReal.ofReal (lbkHarm w) := by
  classical
  obtain ⟨-, -, hs⟩ := lbk_isDualStart_strip hxy
  have hr0 : 0 < r := (lbk_lastTime_nonneg htp).trans_lt hr
  have hinitm : Measurable fun zs' : Fin (k + 1) → ℝ × ℝ => Fin.init zs' :=
    Measurable.of_eval fun i => measurable_pi_apply _
  have hA' : MeasurableSet ((fun zs' : Fin (k + 1) → ℝ × ℝ => Fin.init zs') ⁻¹' A) := hinitm hA
  have hb := lbk_doob_indicator h2 hxy hP (lbk_strictMono_snoc hts hr0 hr)
    (lbk_snoc_pos htp hr0) hA'
  have hpath : ∀ ω, Fin.init (fun i => dualPoint X Y ((Fin.snoc ts r : Fin (k + 1) → ℝ) i) ω) =
      fun i => dualPoint X Y (ts i) ω := fun ω => by
    funext i
    simp only [Fin.init, Fin.snoc_castSucc]
  simp only [mem_preimage, hpath, lbk_lastTime_snoc] at hb
  rw [hb]
  -- split `(ℝ²)^{k+1} ≅ ℝ² × (ℝ²)^k` at the last index
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ × ℝ) (Fin.last k)).symm
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have hind : ∀ zs' : Fin (k + 1) → ℝ × ℝ,
      ((fun zs' : Fin (k + 1) → ℝ × ℝ => Fin.init zs') ⁻¹' A).indicator
          (1 : (Fin (k + 1) → ℝ × ℝ) → ℝ≥0∞) zs' =
        A.indicator (1 : (Fin k → ℝ × ℝ) → ℝ≥0∞) (Fin.init zs') := fun zs' => by
    by_cases h : Fin.init zs' ∈ A <;> simp [h]
  simp only [hind, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_last', Fin.init_snoc, lbk_fddProd_snoc, lbk_lastPoint_snoc]
  have hk := lbk_kernel_measurable hD0
  have hjoint : Measurable fun q : (ℝ × ℝ) × (Fin k → ℝ × ℝ) =>
      A.indicator 1 q.2 * (lbkFddProd (lbkKernel D0) (x, y) ts q.2 *
        ENNReal.ofReal (lbkKernel D0 (r - lbkLastTime ts) (lbkLastPoint (x, y) q.2) q.1)) *
        ENNReal.ofReal ((x + y) * lbkHarm q.1) :=
    (((measurable_one.indicator hA).comp measurable_snd).mul
      (((lbk_fddProd_measurable hk (x, y) ts).comp measurable_snd).mul
        (hk.comp (measurable_const.prodMk (((lbk_measurable_cons (x, y) (Fin.last k)).comp
          measurable_snd).prodMk measurable_fst))).ennreal_ofReal)).mul
      (measurable_const.mul (lbk_harm_measurable.comp measurable_fst)).ennreal_ofReal
  rw [Measure.volume_eq_prod, lintegral_prod_symm' _ hjoint]
  refine lintegral_congr fun zs => ?_
  have hwm : Measurable fun w : ℝ × ℝ =>
      ENNReal.ofReal (lbkKernel D0 (r - lbkLastTime ts) (lbkLastPoint (x, y) zs) w) *
        ENNReal.ofReal (lbkHarm w) :=
    (hk.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).ennreal_ofReal.mul
      lbk_harm_measurable.ennreal_ofReal
  rw [← lintegral_const_mul _ hwm]
  refine lintegral_congr fun w => ?_
  simp only [lbkLastPoint, ENNReal.ofReal_mul hs.le]
  ring

/-- **The joint law of the path and the lifetime on rectangles** `A × (T, r]` from inputs 1 and 2:
`P(Z ∈ A, T < σ₀ ≤ r) = (D₀/2)(x+y) ∫_A Π ∫_{(0, r - T]} p_s(z_k, 0) ds`. -/
theorem lbk_killed_rect_of_doob {D0 : ℝ} (hD0 : 0 < D0) (h1 : LbkCornerHeatIdentity D0)
    (h2 : LbkDoobKilledLaw D0) {x y : ℝ}
    (hxy : IsDualStart ![x] ![y]) {Ω : Type} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m}
    {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (hP : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) {k : ℕ} {ts : Fin k → ℝ}
    (hts : StrictMono ts) (htp : ∀ i, 0 < ts i) {A : Set (Fin k → ℝ × ℝ)}
    (hA : MeasurableSet A) {r : ℝ} (hr : lbkLastTime ts < r) :
    P {ω | (fun i => dualPoint X Y (ts i) ω) ∈ A ∧
        ENNReal.ofReal (lbkLastTime ts) < lbkExtinctionRat N ω ∧
        lbkExtinctionRat N ω ≤ ENNReal.ofReal r} =
      ENNReal.ofReal (D0 / 2 * (x + y)) *
        ∫⁻ zs, A.indicator 1 zs * lbkFddProd (lbkKernel D0) (x, y) ts zs *
          ∫⁻ s in Ioc 0 (r - lbkLastTime ts),
            ENNReal.ofReal (lbkKernel D0 s (lbkLastPoint (x, y) zs) (0, 0)) := by
  classical
  have := hP.prob
  obtain ⟨hz, hz0, hs⟩ := lbk_isDualStart_strip hxy
  obtain ⟨hτm, -⟩ := lbk_extinction_ae_eq hP
  have hk := lbk_kernel_measurable hD0
  have hZm := lbk_dualPath_measurable hP ts
  set T := lbkLastTime ts with hT
  set Z : Ω → (Fin k → ℝ × ℝ) := fun ω i => dualPoint X Y (ts i) ω with hZ
  set τ := lbkExtinctionRat N with hτ
  -- the three events
  have hdecomp : {ω | Z ω ∈ A ∧ ENNReal.ofReal T < τ ω} =
      {ω | Z ω ∈ A ∧ ENNReal.ofReal r < τ ω} ∪
        {ω | Z ω ∈ A ∧ ENNReal.ofReal T < τ ω ∧ τ ω ≤ ENNReal.ofReal r} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union]
    constructor
    · rintro ⟨hA, hT'⟩
      rcases lt_or_ge (ENNReal.ofReal r) (τ ω) with h | h
      · exact Or.inl ⟨hA, h⟩
      · exact Or.inr ⟨hA, hT', h⟩
    · rintro (⟨hA, h⟩ | ⟨hA, h, -⟩)
      · exact ⟨hA, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hr.le) h⟩
      · exact ⟨hA, h⟩
  have hdisj : Disjoint {ω | Z ω ∈ A ∧ ENNReal.ofReal r < τ ω}
      {ω | Z ω ∈ A ∧ ENNReal.ofReal T < τ ω ∧ τ ω ≤ ENNReal.ofReal r} :=
    disjoint_left.2 fun ω h h' => absurd h'.2.2 (not_le.2 h.2)
  have hRm : MeasurableSet {ω | Z ω ∈ A ∧ ENNReal.ofReal T < τ ω ∧ τ ω ≤ ENNReal.ofReal r} :=
    (hZm hA).inter ((measurableSet_lt measurable_const hτm).inter
      (measurableSet_le hτm measurable_const))
  have hsum := measure_union (μ := P) hdisj hRm
  rw [← hdecomp, lbk_doob_indicator h2 hxy hP hts htp hA, lbk_doob_snoc hD0 h2 hxy hP hts htp hA hr]
    at hsum
  -- input 1 at `z_k`
  set Q : (Fin k → ℝ × ℝ) → ℝ≥0∞ := fun zs =>
    ∫⁻ w, ENNReal.ofReal (lbkKernel D0 (r - T) (lbkLastPoint (x, y) zs) w) *
      ENNReal.ofReal (lbkHarm w) with hQ
  set J : (Fin k → ℝ × ℝ) → ℝ≥0∞ := fun zs =>
    ∫⁻ s in Ioc 0 (r - T), ENNReal.ofReal (lbkKernel D0 s (lbkLastPoint (x, y) zs) (0, 0))
    with hJ
  have hpt : ∀ᵐ zs ∂(volume : Measure (Fin k → ℝ × ℝ)),
      A.indicator 1 zs * lbkFddProd (lbkKernel D0) (x, y) ts zs *
          ENNReal.ofReal ((x + y) * lbkHarm (lbkLastPoint (x, y) zs)) =
        A.indicator 1 zs * lbkFddProd (lbkKernel D0) (x, y) ts zs * ENNReal.ofReal (x + y) * Q zs +
          ENNReal.ofReal (D0 / 2 * (x + y)) *
            (A.indicator 1 zs * lbkFddProd (lbkKernel D0) (x, y) ts zs * J zs) := by
    filter_upwards [lbk_ae_lastPoint_ne (k := k) hz0] with zs hzs
    by_cases hPi : lbkFddProd (lbkKernel D0) (x, y) ts zs = 0
    · simp [hPi]
    have hw := lbk_lastPoint_mem_of_fddProd_ne_zero hz hPi
    have hheat := h1 _ hw hzs (r - T) (sub_pos.2 hr)
    rw [ENNReal.ofReal_mul hs.le, ← hheat, ENNReal.ofReal_mul (by positivity : 0 ≤ D0 / 2)]
    simp only [hQ, hJ]
    ring
  have hQm : Measurable Q := by
    refine Measurable.lintegral_prod_right' (f := fun q : (Fin k → ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (lbkKernel D0 (r - T) (lbkLastPoint (x, y) q.1) q.2) *
        ENNReal.ofReal (lbkHarm q.2)) ?_
    exact (hk.comp (measurable_const.prodMk (((lbk_measurable_cons (x, y) (Fin.last k)).comp
      measurable_fst).prodMk measurable_snd))).ennreal_ofReal.mul
      (lbk_harm_measurable.comp measurable_snd).ennreal_ofReal
  have hfirst : Measurable fun zs : Fin k → ℝ × ℝ =>
      A.indicator 1 zs * lbkFddProd (lbkKernel D0) (x, y) ts zs * ENNReal.ofReal (x + y) * Q zs :=
    (((measurable_one.indicator hA).mul (lbk_fddProd_measurable hk (x, y) ts)).mul
      measurable_const).mul hQm
  rw [lintegral_congr_ae hpt, lintegral_add_left hfirst,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hsum
  have hfin : ∫⁻ zs, A.indicator 1 zs * lbkFddProd (lbkKernel D0) (x, y) ts zs *
      ENNReal.ofReal (x + y) * Q zs ≠ ⊤ := by
    rw [← lbk_doob_snoc hD0 h2 hxy hP hts htp hA hr]
    exact measure_ne_top P _
  exact ((ENNReal.add_right_inj hfin).1 hsum).symm
