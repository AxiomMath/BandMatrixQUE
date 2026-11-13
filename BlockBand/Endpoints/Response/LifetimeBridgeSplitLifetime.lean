module

public import BlockBand.Endpoints.Response.LifetimeBridgeSplitDefs

/-!
# The corner lifetime law from the heat identity and the Doob killed law

This file derives the law of the lifetime `σ₀` of the `H` transform from `LbkCornerHeatIdentity`
and `LbkDoobKilledLaw` alone, without the Markov property.

## Main results

* `lbk_extinction_pos_ae`: `σ₀ > 0` a.s. (the killed law at `k = 0`);
* `lbk_survival_of_doob`: `P(t < σ₀) = (x + y) P_tH(z)` (the killed law at `k = 1`, `F = 1`);
* `lbk_lifetime_cdf_of_split`: `P(σ₀ ≤ t) = (D₀/2)(x + y)∫_{(0,t]} p_s(z,0) ds` (complement and
  the corner heat identity);
* `lbk_lifetime_law_of_split`: the corner lifetime law
  `E[h(σ₀); σ₀ < ∞] = ∫_{(0,∞)} h(s) (D₀/2)(x+y) p_s(z,(0,0)) ds` for all measurable `h ≥ 0`
  (the distribution function determines the finite measure, `Measure.ext_of_Iic`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-!
### Measurability of the lifetime
-/

/-- The lifetime computed over rational times: `inf {q ∈ ℚ : N_{q⁺} = 0}` (with `q⁺ = max q 0`). -/
def lbkExtinctionRat {Ω : Type*} (N : ℝ≥0 → Ω → ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (q : ℚ) (_ : N (q : ℝ).toNNReal ω = 0), (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞)

theorem lbk_extinctionRat_measurable {Ω : Type*} [MeasurableSpace Ω] {N : ℝ≥0 → Ω → ℕ}
    (hN : ∀ t, Measurable (N t)) : Measurable (lbkExtinctionRat N) := by
  classical
  refine Measurable.iInf fun q => ?_
  have hset : MeasurableSet {ω | N (q : ℝ).toNNReal ω = 0} :=
    hN _ (measurableSet_singleton 0)
  have : (fun ω => ⨅ (_ : N (q : ℝ).toNNReal ω = 0), (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞)) =
      fun ω => if N (q : ℝ).toNNReal ω = 0 then (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) else ⊤ := by
    funext ω
    exact iInf_eq_if _
  rw [this]
  exact Measurable.ite hset measurable_const measurable_const

/-- On an antitone level path the lifetime equals its rational version. -/
theorem lbk_extinction_eq_rat {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {ω : Ω}
    (hanti : Antitone fun t => N t ω) : dualExtinction N ω = lbkExtinctionRat N ω := by
  refine le_antisymm ?_ ?_
  · exact le_iInf₂ fun q hq => iInf₂_le (f := fun (t : ℝ≥0) (_ : N t ω = 0) => (t : ℝ≥0∞)) _ hq
  · refine le_iInf₂ fun t ht => le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    obtain ⟨q, -, htq, hqc⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hc
    have htq' : t ≤ (q : ℝ).toNNReal := (ENNReal.coe_lt_coe.1 htq).le
    have hq : N (q : ℝ).toNNReal ω = 0 := Nat.eq_zero_of_le_zero (ht ▸ hanti htq')
    exact (iInf₂_le (f := fun (q : ℚ) (_ : N (q : ℝ).toNNReal ω = 0) =>
      (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞)) q hq).trans hqc.le

/-- The lifetime of a boundary dual realization is a.e. measurable: it is a.e. equal to the
measurable `lbkExtinctionRat N`. -/
theorem lbk_extinction_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {p : ℕ}
    {x y : Fin p → ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (hP : IsBoundaryDualProcess P 𝓖 D0 x y N X Y) :
    Measurable (lbkExtinctionRat N) ∧ ∀ᵐ ω ∂P, dualExtinction N ω = lbkExtinctionRat N ω := by
  refine ⟨lbk_extinctionRat_measurable fun t => (hP.adapted t).1.mono (𝓖.le t) le_rfl, ?_⟩
  filter_upwards [hP.paths] with ω hω
  exact lbk_extinction_eq_rat hω.antitone

/-!
### Elementary facts about one-pair starts
-/

theorem lbk_isDualStart_strip {x y : ℝ} (h : IsDualStart ![x] ![y]) :
    (x, y) ∈ baseStrip ∧ (x, y) ≠ (0, 0) ∧ 0 < x + y := by
  obtain ⟨hx, hy, hs⟩ := lbk_isDualStart_one h
  refine ⟨⟨hx, hy⟩, fun h0 => ?_, hs⟩
  simp only [Prod.mk.injEq] at h0
  rw [h0.1, h0.2] at hs
  simp at hs

theorem lbk_lintegral_ite_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {S : Set Ω}
    (hS : MeasurableSet S) [DecidablePred (· ∈ S)] :
    ∫⁻ ω, (if ω ∈ S then (1 : ℝ≥0∞) else 0) ∂P = P S := by
  rw [← lintegral_indicator_one hS]
  refine lintegral_congr fun ω => ?_
  by_cases h : ω ∈ S <;> simp [h]

/-!
### The Doob killed law at `k = 0` and `k = 1`
-/

/-- `σ₀ > 0` a.s. (the Doob killed law at `k = 0`). -/
theorem lbk_extinction_pos_ae {D0 : ℝ} (h2 : LbkDoobKilledLaw D0) {x y : ℝ}
    (hxy : IsDualStart ![x] ![y]) {Ω : Type} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m}
    {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (hP : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) :
    ∀ᵐ ω ∂P, 0 < dualExtinction N ω := by
  classical
  have := hP.prob
  obtain ⟨-, -, hs⟩ := lbk_isDualStart_strip hxy
  obtain ⟨hτm, hτ⟩ := lbk_extinction_ae_eq hP
  have h0 := h2 x y hxy Ω m 𝓖 P N X Y hP 0 (fun i => i.elim0) (fun a _ _ => a.elim0)
    (fun i => i.elim0) (fun _ => 1) measurable_const
  have hlast : lbkLastTime (fun i : Fin 0 => i.elim0 : Fin 0 → ℝ) = 0 := by simp [lbkLastTime]
  have hR : ∀ zs : Fin 0 → ℝ × ℝ,
      (1 : ℝ≥0∞) * lbkFddProd (lbkKernel D0) (x, y) (fun i : Fin 0 => i.elim0) zs *
        ENNReal.ofReal ((x + y) * lbkHarm (lbkLastPoint (x, y) zs)) = 1 := fun zs => by
    simp only [lbkFddProd, Finset.univ_eq_empty, Finset.prod_empty, one_mul, lbkLastPoint,
      Fin.last_zero, Fin.cons_zero, lbkHarm]
    rw [mul_inv_cancel₀ hs.ne', ENNReal.ofReal_one]
  simp_rw [hR, hlast, ENNReal.ofReal_zero] at h0
  have hvol : ∫⁻ _ : Fin 0 → ℝ × ℝ, (1 : ℝ≥0∞) = 1 := by simp [MeasureTheory.volume_pi]
  rw [hvol] at h0
  have hS : MeasurableSet {ω | 0 < lbkExtinctionRat N ω} := measurableSet_lt measurable_const hτm
  have h1 : P {ω | 0 < lbkExtinctionRat N ω} = 1 := by
    rw [← lbk_lintegral_ite_one hS]
    refine (lintegral_congr_ae ?_).trans h0
    filter_upwards [hτ] with ω hω
    simp only [hω]
  have hc : P {ω | 0 < lbkExtinctionRat N ω}ᶜ = 0 := by
    rw [prob_compl_eq_one_sub hS, h1, tsub_self]
  have hae : ∀ᵐ ω ∂P, 0 < lbkExtinctionRat N ω := by
    rw [ae_iff]
    exact hc
  filter_upwards [hae, hτ] with ω h1 h2
  rw [h2]
  exact h1

/-- The survival probability `P(t < σ₀) = (x + y) P_tH(z)`, i.e. `P_t⁰H(z)/H(z)` (the Doob killed
law at `k = 1`, `F = 1`). -/
theorem lbk_survival_of_doob {D0 : ℝ} (h2 : LbkDoobKilledLaw D0) {x y : ℝ}
    (hxy : IsDualStart ![x] ![y]) {Ω : Type} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m}
    {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (hP : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) {t : ℝ} (ht : 0 < t) :
    P {ω | ENNReal.ofReal t < lbkExtinctionRat N ω} =
      ENNReal.ofReal (x + y) *
        ∫⁻ w', ENNReal.ofReal (lbkKernel D0 t (x, y) w') * ENNReal.ofReal (lbkHarm w') := by
  classical
  obtain ⟨-, -, hs⟩ := lbk_isDualStart_strip hxy
  obtain ⟨hτm, hτ⟩ := lbk_extinction_ae_eq hP
  have h1 := h2 x y hxy Ω m 𝓖 P N X Y hP 1 ![t] (Subsingleton.strictMono _)
    (fun i => by simpa [Fin.fin_one_eq_zero i] using ht) (fun _ => 1) measurable_const
  have hlast : lbkLastTime ![t] = t := by simp [lbkLastTime]
  have hR : ∀ zs : Fin 1 → ℝ × ℝ,
      (1 : ℝ≥0∞) * lbkFddProd (lbkKernel D0) (x, y) ![t] zs *
        ENNReal.ofReal ((x + y) * lbkHarm (lbkLastPoint (x, y) zs)) =
      ENNReal.ofReal (x + y) *
        (ENNReal.ofReal (lbkKernel D0 t (x, y) (zs default)) *
          ENNReal.ofReal (lbkHarm (zs default))) := fun zs => by
    simp only [lbkFddProd, Fin.prod_univ_one, one_mul, lbkLastPoint, Fin.castSucc_zero,
      Fin.cons_zero, Matrix.cons_val_fin_one, sub_zero, ENNReal.ofReal_mul hs.le]
    have : (Fin.cons (x, y) zs : Fin 2 → ℝ × ℝ) (Fin.last 1) = zs 0 := by simp
    rw [this]
    simp only [Fin.default_eq_zero]
    ring
  simp_rw [hR, hlast] at h1
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h1
  have hU := (volume_preserving_funUnique (Fin 1) (ℝ × ℝ)).lintegral_comp_emb
    (MeasurableEquiv.funUnique (Fin 1) (ℝ × ℝ)).measurableEmbedding
    (fun w' => ENNReal.ofReal (lbkKernel D0 t (x, y) w') * ENNReal.ofReal (lbkHarm w'))
  simp only [MeasurableEquiv.funUnique_apply] at hU
  replace h1 := h1.trans (congrArg (ENNReal.ofReal (x + y) * ·) hU)
  have hS : MeasurableSet {ω | ENNReal.ofReal t < lbkExtinctionRat N ω} :=
    measurableSet_lt measurable_const hτm
  rw [← lbk_lintegral_ite_one hS]
  refine (lintegral_congr_ae ?_).trans h1
  filter_upwards [hτ] with ω hω
  simp only [hω]

/-!
### The survival-to-density step
-/

/-- The distribution function of the lifetime:
`P(σ₀ ≤ t) = (D₀/2)(x + y) ∫_{(0,t]} p_s(z, (0,0)) ds` for `t > 0`, from the survival probability
and the corner heat identity. -/
theorem lbk_lifetime_cdf_of_split {D0 : ℝ} (h1 : LbkCornerHeatIdentity D0)
    (h2 : LbkDoobKilledLaw D0) {x y : ℝ}
    (hxy : IsDualStart ![x] ![y]) {Ω : Type} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m}
    {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (hP : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) {t : ℝ} (ht : 0 < t) :
    P {ω | lbkExtinctionRat N ω ≤ ENNReal.ofReal t} =
      ENNReal.ofReal (D0 / 2 * (x + y)) *
        ∫⁻ s in Ioc 0 t, ENNReal.ofReal (lbkKernel D0 s (x, y) (0, 0)) := by
  have := hP.prob
  obtain ⟨hz, hz0, hs⟩ := lbk_isDualStart_strip hxy
  obtain ⟨hτm, -⟩ := lbk_extinction_ae_eq hP
  set A := ∫⁻ w', ENNReal.ofReal (lbkKernel D0 t (x, y) w') * ENNReal.ofReal (lbkHarm w')
  set B := ∫⁻ s in Ioc 0 t, ENNReal.ofReal (lbkKernel D0 s (x, y) (0, 0))
  have hheat := h1 (x, y) hz hz0 t ht
  have hsurv := lbk_survival_of_doob h2 hxy hP ht
  have hS : MeasurableSet {ω | lbkExtinctionRat N ω ≤ ENNReal.ofReal t} :=
    measurableSet_le hτm measurable_const
  have hcompl : {ω | lbkExtinctionRat N ω ≤ ENNReal.ofReal t}ᶜ =
      {ω | ENNReal.ofReal t < lbkExtinctionRat N ω} := by
    ext ω
    simp
  have hsum := measure_add_measure_compl (μ := P) hS
  rw [hcompl, hsurv, measure_univ] at hsum
  have hone : ENNReal.ofReal (x + y) * ENNReal.ofReal (lbkHarm (x, y)) = 1 := by
    rw [← ENNReal.ofReal_mul hs.le, lbkHarm, mul_inv_cancel₀ hs.ne', ENNReal.ofReal_one]
  have hheat' : ENNReal.ofReal (x + y) * A + ENNReal.ofReal (D0 / 2 * (x + y)) * B = 1 := by
    have e : ENNReal.ofReal (D0 / 2 * (x + y)) =
        ENNReal.ofReal (x + y) * ENNReal.ofReal (D0 / 2) := by
      rw [mul_comm, ENNReal.ofReal_mul hs.le]
    rw [e, ← hone, ← hheat]
    ring
  have hfin : ENNReal.ofReal (x + y) * A ≠ ⊤ := by
    rw [← hsurv]
    exact measure_ne_top P _
  rw [← hheat', add_comm (ENNReal.ofReal (x + y) * A)] at hsum
  exact (ENNReal.add_left_inj hfin).1 hsum

/-- The corner lifetime law from the corner heat identity and the Doob killed law only (no Markov
property): for every boundary dual realization from `z = (x, y)` and measurable `h ≥ 0`,
`E[h(σ₀); σ₀ < ∞] = ∫_{(0,∞)} h(s) (D₀/2)(x + y) p_s(z, (0,0)) ds`. -/
theorem lbk_lifetime_law_of_split {D0 : ℝ} (hD0 : 0 < D0) (h1 : LbkCornerHeatIdentity D0)
    (h2 : LbkDoobKilledLaw D0) {x y : ℝ}
    (hxy : IsDualStart ![x] ![y]) {Ω : Type} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m}
    {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (hP : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ ω, (if dualExtinction N ω < ⊤ then h (dualExtinction N ω).toReal else 0) ∂P =
      ∫⁻ s in Ioi 0, h s * ENNReal.ofReal (D0 / 2 * (x + y) * lbkKernel D0 s (x, y) (0, 0)) := by
  classical
  have := hP.prob
  obtain ⟨-, -, hs⟩ := lbk_isDualStart_strip hxy
  obtain ⟨hτm, hτ⟩ := lbk_extinction_ae_eq hP
  have hpos := lbk_extinction_pos_ae h2 hxy hP
  have hpos' : ∀ᵐ ω ∂P, 0 < lbkExtinctionRat N ω := by
    filter_upwards [hpos, hτ] with ω h1 h2
    exact h2 ▸ h1
  have hc : 0 ≤ D0 / 2 * (x + y) := by positivity
  set τ := lbkExtinctionRat N
  set f : Ω → ℝ := fun ω => (τ ω).toReal with hf
  have hfm : Measurable f := hτm.ennreal_toReal
  set S : Set Ω := {ω | τ ω < ⊤} with hSdef
  have hS : MeasurableSet S := measurableSet_lt hτm measurable_const
  set dens : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (D0 / 2 * (x + y) * lbkKernel D0 s (x, y) (0, 0))
    with hdens
  have hkm : Measurable fun s : ℝ => lbkKernel D0 s (x, y) (0, 0) :=
    (lbk_kernel_measurable hD0).comp (f := fun s : ℝ => (s, (x, y), ((0, 0) : ℝ × ℝ)))
      (measurable_id.prodMk measurable_const)
  have hdm : Measurable dens := (measurable_const.mul hkm).ennreal_ofReal
  set μ : Measure ℝ := (P.restrict S).map f with hμ
  set ν : Measure ℝ := (volume.restrict (Ioi (0 : ℝ))).withDensity dens with hν
  have hμν : μ = ν := by
    refine Measure.ext_of_Iic μ ν fun r => ?_
    rw [hμ, hν, Measure.map_apply hfm measurableSet_Iic,
      Measure.restrict_apply (hfm measurableSet_Iic),
      withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Ioi]
    rcases le_or_gt r 0 with hr | hr
    · rw [Ioc_eq_empty (not_lt.2 hr), Measure.restrict_empty, lintegral_zero_measure]
      rw [ae_iff] at hpos'
      refine measure_mono_null (fun ω hω => ?_) hpos'
      simp only [mem_inter_iff, mem_preimage, mem_Iic, hSdef, mem_ofPred_eq, hf] at hω
      simp only [mem_ofPred_eq, not_lt, nonpos_iff_eq_zero]
      have h0 : (τ ω).toReal = 0 := le_antisymm (hω.1.trans hr) ENNReal.toReal_nonneg
      rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h | h
      · exact h
      · exact absurd h hω.2.ne
    · have hset : f ⁻¹' Iic r ∩ S = {ω | τ ω ≤ ENNReal.ofReal r} := by
        ext ω
        simp only [mem_inter_iff, mem_preimage, mem_Iic, hSdef, mem_ofPred_eq, hf]
        constructor
        · rintro ⟨h1, h2⟩
          exact (ENNReal.le_ofReal_iff_toReal_le h2.ne hr.le).2 h1
        · intro h1
          have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
          exact ⟨(ENNReal.le_ofReal_iff_toReal_le hne hr.le).1 h1, lt_top_iff_ne_top.2 hne⟩
      rw [hset, lbk_lifetime_cdf_of_split h1 h2 hxy hP hr, hdens,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun s => ?_
      rw [ENNReal.ofReal_mul hc]
  have hL : ∫⁻ ω, (if dualExtinction N ω < ⊤ then h (dualExtinction N ω).toReal else 0) ∂P =
      ∫⁻ r, h r ∂μ := by
    rw [hμ, lintegral_map hh hfm, ← lintegral_indicator hS]
    refine lintegral_congr_ae ?_
    filter_upwards [hτ] with ω hω
    simp only [indicator, hSdef, mem_ofPred_eq, hω, hf]
  rw [hL, hμν, hν, lintegral_withDensity_eq_lintegral_mul _ hdm hh]
  refine lintegral_congr fun s => ?_
  simp only [Pi.mul_apply, hdens]
  ring

end BlockBand.Endpoints
