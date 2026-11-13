module

public import BlockBand.Transmission.Dual.GNegMom
public import BlockBand.Transmission.Dual.GSeqA3
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Left continuity of `E[h(Z_u)]`: atomlessness and the boundary classification at every level

For the level-one base solution `Z = pairPath z X` on `(Ω₁, P₁, 𝓖₁)` (`isBaseSol_pair`) and
`h = flatH 1 = 1/(x+y)`:
* `measure_flatH_gt_le`: `P₁(h(Z_s) > M) ≤ 4e M⁻² / (1 − e^{−D₀ s})²` (from
  `measure_gapG_lt_le`, since `g ≤ x + y`);
* `lintegral_tail_le` (uniform integrability): for `s ≥ T₁ > 0` and `M > 0`,
  `E[(h(Z_s) − M)⁺] ≤ C(T₁)/M` (layer cake and `∫_0^∞ C/(M+t)² dt = C/M`);
* **`hLeftCont_holds`**: `HLeftCont D₀` for `D₀ > 0` — `u ↦ E[h(Z_u)]` is left-continuous on
  `(0, ∞)` (truncation at `M`: dominated convergence for `min(h, M)` along the continuous
  paths, plus the uniform tail bound; this is Vitali's theorem in the form needed);
* **`gSeq_all_holds`**: the boundary classification `GSeq D₀ (q+1)` holds on the sequence space
  for every `q` (`gSeq_all_of_hLeftCont`), and **`a3Seq_holds`**: the level-one lifetime is
  atomless (`A3Seq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

variable {D0 : ℝ} {z : Fin 2 → ℝ} {X : ℝ≥0 → Ω₁ → Fin 2 → ℝ}

theorem flatH_one_eq (w : Fin (1 + 1) → ℝ) : flatH 1 w = (w 0 + w 1)⁻¹ := by
  rw [flatH, cauchyH_one]; rfl

theorem measurable_flatH_one : Measurable (flatH 1) := by
  rw [show flatH 1 = fun w : Fin (1 + 1) → ℝ => (w 0 + w 1)⁻¹ from funext flatH_one_eq]
  fun_prop

theorem continuousAt_flatH_one {w : Fin (1 + 1) → ℝ} (h : w 0 + w 1 ≠ 0) :
    ContinuousAt (flatH 1) w := by
  rw [show flatH 1 = fun w : Fin (1 + 1) → ℝ => (w 0 + w 1)⁻¹ from funext flatH_one_eq]
  exact ((continuous_apply 0).add (continuous_apply 1)).continuousAt.inv₀ h

theorem ae_pairPath_eq
    (hX : IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X) :
    ∀ᵐ ω ∂P₁, ∀ t, pairPath z X t ω = toFlat (X t ω) := by
  have : ∀ᵐ ω ∂P₁, ω ∈ pairGood z X := ae_iff.2 (measure_pairGood_compl hX)
  filter_upwards [this] with ω hω t
  simp only [pairPath, hω, ite_true]

/-- The constant of the small-ball bound at times `≥ T₁`. -/
def tailC (D0 T₁ : ℝ) : ℝ := 4 * exp 1 / (1 - exp (-(D0 * T₁))) ^ 2

theorem one_sub_exp_pos (hD0 : 0 < D0) {T : ℝ} (hT : 0 < T) : 0 < 1 - exp (-(D0 * T)) := by
  have : exp (-(D0 * T)) < 1 := by
    calc exp (-(D0 * T)) < exp 0 := exp_lt_exp.2 (by nlinarith)
      _ = 1 := exp_zero
  linarith

theorem tailC_nonneg (hD0 : 0 < D0) {T₁ : ℝ} (hT₁ : 0 < T₁) : 0 ≤ tailC D0 T₁ :=
  div_nonneg (by positivity) (pow_pos (one_sub_exp_pos hD0 hT₁) 2).le

/-- **Small-ball bound for `h`** at times `s ≥ T₁ > 0`. -/
theorem measure_flatH_gt_le (hD0 : 0 < D0)
    (hX : IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X) {T₁ : ℝ}
    (hT₁ : 0 < T₁) {s : ℝ≥0} (hs : T₁ ≤ s) {M : ℝ} (hM : 0 < M) :
    P₁ {ω | M < flatH 1 (pairPath z X s ω)} ≤ ENNReal.ofReal (tailC D0 T₁ / M ^ 2) := by
  have hs0 : 0 < s := by have : (0 : ℝ) < s := by linarith
                         exact_mod_cast this
  have h1 : P₁ {ω | M < flatH 1 (pairPath z X s ω)} ≤ P₁ {ω | gapG (toFlat (X s ω)) < M⁻¹} := by
    refine measure_mono_ae ?_
    filter_upwards [ae_pairPath_eq hX] with ω hω hmem
    have hmem' : M < flatH 1 (pairPath z X s ω) := hmem
    rw [hω s, flatH_one_eq] at hmem'
    show gapG (toFlat (X s ω)) < M⁻¹
    have hx := toFlat_mem_posU (X s ω)
    have hy : 0 < toFlat (X s ω) 1 := by rw [toFlat_one]; exact lgt_pos _
    have hpos : 0 < toFlat (X s ω) 0 + toFlat (X s ω) 1 := by
      have : 0 < toFlat (X s ω) 0 := hx
      linarith
    have : toFlat (X s ω) 0 + toFlat (X s ω) 1 < M⁻¹ := by
      rw [lt_inv_comm₀ hpos hM]; exact hmem'
    exact (gapG_le hx).trans_lt this
  refine h1.trans ((measure_gapG_lt_le hD0 hX hs0 (inv_pos.2 hM)).trans
    (ENNReal.ofReal_le_ofReal ?_))
  have hb1 := one_sub_exp_pos hD0 hT₁
  have hb2 : 1 - exp (-(D0 * T₁)) ≤ 1 - exp (-(D0 * s)) := by
    have : exp (-(D0 * s)) ≤ exp (-(D0 * T₁)) := exp_le_exp.2 (by nlinarith)
    linarith
  have hsq : (1 - exp (-(D0 * T₁))) ^ 2 ≤ (1 - exp (-(D0 * s))) ^ 2 :=
    pow_le_pow_left₀ hb1.le hb2 2
  have hM2 : 0 < M ^ 2 := by positivity
  have hbs : 0 < (1 - exp (-(D0 * s))) ^ 2 := lt_of_lt_of_le (pow_pos hb1 2) hsq
  rw [tailC, div_div, inv_pow, div_le_div_iff₀ hbs (mul_pos (pow_pos hb1 2) hM2)]
  have e : 4 * exp 1 * (M ^ 2)⁻¹ * ((1 - exp (-(D0 * T₁))) ^ 2 * M ^ 2) =
      4 * exp 1 * (1 - exp (-(D0 * T₁))) ^ 2 := by field_simp
  rw [e]
  nlinarith [exp_pos 1]

/-- `∫_0^∞ C/(M+t)² dt = C/M`. -/
theorem lintegral_inv_sq {C M : ℝ} (hC : 0 ≤ C) (hM : 0 < M) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (C / (M + t) ^ 2) = ENNReal.ofReal (C / M) := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun t => -(C / (M + t))) (C / (M + x) ^ 2) x := by
    intro x hx
    have hx' : M + x ≠ 0 := by have : (0 : ℝ) ≤ x := hx; linarith
    have := (((hasDerivAt_id' x).const_add M).fun_inv hx').const_mul C |>.neg
    refine (this.congr_deriv (by field_simp)).congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun t => by simp [div_eq_mul_inv]
  have hlim : Tendsto (fun t : ℝ => -(C / (M + t))) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := C)).div_atTop (tendsto_atTop_add_const_left atTop M
      tendsto_id)
    simpa using this.neg
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv (fun x hx => by positivity) hlim
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity),
    hval]
  simp

/-- **Uniform integrability of `h(Z_s)`** at times `s ≥ T₁ > 0`. -/
theorem lintegral_tail_le (hD0 : 0 < D0)
    (hX : IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X) {T₁ : ℝ}
    (hT₁ : 0 < T₁) {s : ℝ≥0} (hs : T₁ ≤ s) {M : ℝ} (hM : 0 < M) :
    ∫⁻ ω, ENNReal.ofReal (max (flatH 1 (pairPath z X s ω) - M) 0) ∂P₁ ≤
      ENNReal.ofReal (tailC D0 T₁ / M) := by
  have hm : Measurable fun ω => flatH 1 (pairPath z X s ω) :=
    measurable_flatH_one.comp ((stronglyMeasurable_pairPath hX s).mono (𝓖₁.le s)).measurable
  rw [lintegral_eq_lintegral_meas_lt P₁ (f := fun ω => max (flatH 1 (pairPath z X s ω) - M) 0)
    (Eventually.of_forall fun ω => le_max_right _ _)
    ((hm.sub_const M).max measurable_const).aemeasurable]
  refine (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_).trans
    (lintegral_inv_sq (tailC_nonneg hD0 hT₁) hM).le
  have ht' : (0 : ℝ) < t := ht
  have e : {ω | t < max (flatH 1 (pairPath z X s ω) - M) 0} =
      {ω | M + t < flatH 1 (pairPath z X s ω)} := by
    ext ω
    simp only [mem_ofPred_eq, lt_max_iff]
    constructor
    · rintro (h | h)
      · linarith
      · linarith
    · intro h; left; linarith
  rw [e]
  exact measure_flatH_gt_le hD0 hX hT₁ hs (by linarith)

theorem measurable_h_pairPath
    (hX : IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X) (s : ℝ≥0) :
    Measurable fun ω => flatH 1 (pairPath z X s ω) :=
  measurable_flatH_one.comp ((stronglyMeasurable_pairPath hX s).mono (𝓖₁.le s)).measurable

/-- **The truncations `E[min(h(Z_s), M)]` are continuous** (dominated convergence). -/
theorem tendsto_trunc (hD0 : 0 < D0) (hz : z ∈ flatO 1)
    (hX : IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X) (M : ℝ)
    (u : ℝ≥0) :
    Tendsto (fun s => ∫⁻ ω, ENNReal.ofReal (min (flatH 1 (pairPath z X s ω)) M) ∂P₁) (𝓝 u)
      (𝓝 (∫⁻ ω, ENNReal.ofReal (min (flatH 1 (pairPath z X u ω)) M) ∂P₁)) := by
  have hB := isBaseSol_pair hD0 hz hX
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => ENNReal.ofReal M)
    (Eventually.of_forall fun s => ((measurable_h_pairPath hX s).min measurable_const).ennreal_ofReal)
    (Eventually.of_forall fun s => Eventually.of_forall fun ω =>
      ENNReal.ofReal_le_ofReal (min_le_right _ _)) (by simp) (Eventually.of_forall fun ω => ?_)
  have hm := mem_flatChamber_one (flatO_one_subset (hB.mem u ω))
  have hc : ContinuousAt (fun s => flatH 1 (pairPath z X s ω)) u :=
    (continuousAt_flatH_one (by linarith [hm.1, hm.2.1])).comp (hB.cont ω).continuousAt
  exact ENNReal.continuous_ofReal.continuousAt.comp (hc.min continuousAt_const)

/-- **`HLeftCont`** (the analytic input of the atomlessness of the lifetime), for `D₀ > 0`. -/
theorem hLeftCont_holds (hD0 : 0 < D0) : HLeftCont D0 := by
  intro z hz
  have hzO := flatChamber_subset_flatO 1 hz
  obtain ⟨X, hX⟩ := exists_pairBase_sde hD0 z
  refine ⟨Ω₁, inferInstance, P₁, inferInstance, 𝓖₁, pairPath z X, isBaseSol_pair hD0 hzO hX,
    fun u hu => ?_⟩
  have hB := isBaseSol_pair hD0 hzO hX
  set φ : ℝ≥0 → ℝ≥0∞ := fun s => ∫⁻ ω, ENNReal.ofReal (flatH 1 (pairPath z X s ω)) ∂P₁
  set G : ℝ → ℝ≥0 → ℝ≥0∞ := fun M s =>
    ∫⁻ ω, ENNReal.ofReal (min (flatH 1 (pairPath z X s ω)) M) ∂P₁
  have hpos : ∀ s ω, 0 < flatH 1 (pairPath z X s ω) := fun s ω => by
    have hm := mem_flatChamber_one (flatO_one_subset (hB.mem s ω))
    rw [flatH_one_eq]; exact inv_pos.2 (by linarith [hm.1, hm.2.1])
  have hGle : ∀ M s, G M s ≤ φ s := fun M s =>
    lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hT₁ : (0 : ℝ) < (u : ℝ) / 2 := by have : (0 : ℝ) < u := hu; linarith
  have hφle : ∀ M : ℝ, 0 < M → ∀ s : ℝ≥0, (u : ℝ) / 2 ≤ s →
      φ s ≤ G M s + ENNReal.ofReal (tailC D0 ((u : ℝ) / 2) / M) := by
    intro M hM s hs
    calc φ s ≤ ∫⁻ ω, (ENNReal.ofReal (min (flatH 1 (pairPath z X s ω)) M) +
          ENNReal.ofReal (max (flatH 1 (pairPath z X s ω) - M) 0)) ∂P₁ :=
          lintegral_mono fun ω => by
            rw [← ENNReal.ofReal_add (le_min (hpos s ω).le hM.le) (le_max_right _ _)]
            refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
            rcases le_total (flatH 1 (pairPath z X s ω)) M with h1 | h1
            · rw [min_eq_left h1, max_eq_right (by linarith)]; ring
            · rw [min_eq_right h1, max_eq_left (by linarith)]; ring
      _ = G M s + ∫⁻ ω, ENNReal.ofReal (max (flatH 1 (pairPath z X s ω) - M) 0) ∂P₁ :=
          lintegral_add_left ((measurable_h_pairPath hX s).min measurable_const).ennreal_ofReal _
      _ ≤ _ := add_le_add le_rfl (lintegral_tail_le hD0 hX hT₁ hs hM)
  have hlim : Tendsto (fun n : ℕ => G n u) atTop (𝓝 (φ u)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n =>
      ((measurable_h_pairPath hX u).min measurable_const).ennreal_ofReal.aemeasurable)
      (Eventually.of_forall fun ω m n hmn => ENNReal.ofReal_le_ofReal
        (min_le_min_left _ (by exact_mod_cast hmn))) (Eventually.of_forall fun ω => ?_)
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈flatH 1 (pairPath z X u ω)⌉₊)
      fun n hn => ?_
    rw [min_eq_left ((Nat.le_ceil _).trans (by exact_mod_cast hn))]
  have hev2 : ∀ᶠ s : ℝ≥0 in 𝓝 u, (u : ℝ) / 2 ≤ (s : ℝ) := by
    filter_upwards [Ioi_mem_nhds (half_lt_self hu)] with s hs
    have : ((u / 2 : ℝ≥0) : ℝ) < s := NNReal.coe_lt_coe.2 hs
    push_cast at this
    exact this.le
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds ha)).exists
    have := (tendsto_trunc hD0 hzO hX n u).eventually (lt_mem_nhds hn)
    exact (this.filter_mono nhdsWithin_le_nhds).mono fun s hs => hs.trans_le (hGle n s)
  · obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hb
    set C := tailC D0 ((u : ℝ) / 2)
    have hC := tailC_nonneg hD0 hT₁
    have hr' : (0 : ℝ) < r := hr0
    set M : ℝ := 2 * C / r + 1
    have hM : 0 < M := by positivity
    have hCM : ENNReal.ofReal (C / M) ≤ ((r / 2 : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ hM]
      push_cast
      have : (r : ℝ) / 2 * M = C + r / 2 := by simp only [M]; field_simp
      rw [this]; linarith
    have hGu : G M u ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ENNReal.ofReal M) ENNReal.ofReal_ne_top ?_
      calc G M u ≤ ∫⁻ _, ENNReal.ofReal M ∂P₁ :=
            lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (min_le_right _ _)
        _ = _ := by simp
    have hr2 : ((r / 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
      simpa using hr0.ne'
    have h2 : G M u < G M u + ((r / 2 : ℝ≥0) : ℝ≥0∞) := ENNReal.lt_add_right hGu hr2
    have hev := (tendsto_trunc hD0 hzO hX M u).eventually (gt_mem_nhds h2)
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds, hev2.filter_mono nhdsWithin_le_nhds]
      with s hs hs2
    calc φ s ≤ G M s + ENNReal.ofReal (C / M) := hφle M hM s hs2
      _ ≤ G M s + ((r / 2 : ℝ≥0) : ℝ≥0∞) := add_le_add le_rfl hCM
      _ < G M u + ((r / 2 : ℝ≥0) : ℝ≥0∞) + ((r / 2 : ℝ≥0) : ℝ≥0∞) :=
          ENNReal.add_lt_add_right ENNReal.coe_ne_top hs
      _ ≤ φ u + r := by
          rw [add_assoc, ← ENNReal.coe_add, add_halves]
          exact add_le_add (hGle M u) le_rfl
      _ < b := hr

/-- **The level-one lifetime is atomless on the sequence space** (`D₀ > 0`). -/
theorem a3Seq_holds (hD0 : 0 < D0) : A3Seq D0 := a3Seq_of_hLeftCont hD0 (hLeftCont_holds hD0)

/-- **The boundary classification at every level on the sequence space** (`D₀ > 0`). -/
theorem gSeq_all_holds (hD0 : 0 < D0) : ∀ q, GSeq D0 q :=
  gSeq_all_of_hLeftCont hD0 (hLeftCont_holds hD0)

end BlockBand.Transmission.Dual.G
