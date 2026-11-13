module

public import BlockBand.Transmission.LawDuality.DualityKill
public import BlockBand.Transmission.LawDuality.DualAtom

/-!
# The duality at the endpoint: the limit `a₀ ↓ 0`

With `W(a₀) = E'[(E F_{Z_{t−a₀}}(μ_{a₀})) K_{t−a₀}]` (`stripV` with `τ ≡ ⊤`, `K` the unstopped
killing), **`tendsto_stripV_top`**: as `a₀ ↓ 0`, `W(a₀) → E'[1{ζ < t} K_t]` whenever
`P'(ζ = t) = 0`. Pathwise in `ω'`:
* on `{ζ < t}` the dual is empty near `t` and `F = 1` at level `0`;
* on `{ζ > t}` some pair stays `≥ (a, b) > 0` near `t` (`exists_pair_left`: survivors are
  continuous across a deletion at `t`), so `0 ≤ E F_{Z_{t−a₀}}(μ_{a₀}) ≤ E F_{a,b}(μ_{a₀}) → 0`
  (`transmissionRatio_le_pair` and the one-pair entrance `HasRatioEntrance`).
Bounded convergence (`0 ≤ FK ≤ 1`) concludes.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- An antitone level is constant on a left neighbourhood of `t > 0`. -/
theorem exists_const_left {n : ℝ≥0 → ℕ} (hn : Antitone n) {t : ℝ≥0} (ht : 0 < t) :
    ∃ r0 < t, ∀ u, r0 ≤ u → u < t → n u = n r0 := by
  have hne : (n '' Iio t).Nonempty := ⟨n 0, 0, ht, rfl⟩
  obtain ⟨r0, hr0, hq⟩ := Nat.sInf_mem hne
  refine ⟨r0, hr0, fun u hu1 hu2 => le_antisymm (hn hu1) ?_⟩
  rw [hq]; exact Nat.sInf_le ⟨u, hu2, rfl⟩

/-- **A surviving pair stays away from the corner near `t`.** -/
theorem exists_pair_left {n : ℝ≥0 → ℕ} {x y : ℝ≥0 → ℕ → ℝ} (hP : IsDeletionPath n x y)
    {t : ℝ≥0} (ht : 0 < t) (hn : n t ≠ 0) :
    ∃ (a b : ℝ) (i0 : ℕ), 0 < a ∧ 0 < b ∧ b < 1 ∧
      ∀ᶠ u in 𝓝[<] t, i0 < n u ∧ a ≤ x u i0 ∧ b ≤ y u i0 := by
  obtain ⟨r0, hr0, hc⟩ := exists_const_left hP.antitone ht
  have hpos : 0 < n t := Nat.pos_of_ne_zero hn
  have hch := hP.chamber t
  have hx0 : 0 < x t 0 := hch.2.2.1 ⟨0, hpos⟩
  have hy0 : 0 < y t 0 := (hch.2.2.2 ⟨0, hpos⟩).1
  have hy1 : y t 0 < 1 := (hch.2.2.2 ⟨0, hpos⟩).2
  have hev : ∀ᶠ u in 𝓝[<] t, n u = n r0 := by
    filter_upwards [Ioo_mem_nhdsLT hr0] with u hu using hc u hu.1.le hu.2
  have hmem : Icc r0 t ∈ 𝓝[<] t := mem_of_superset (Ioo_mem_nhdsLT hr0) Ioo_subset_Icc_self
  refine ⟨x t 0 / 2, y t 0 / 2, ?_⟩
  by_cases hq : n r0 = n t
  · have hcont := hP.cont r0 t hr0.le hq.symm 0 (hq ▸ hpos)
    have hX : Tendsto (fun u => x u 0) (𝓝[<] t) (𝓝 (x t 0)) :=
      ((hcont.1 t ⟨hr0.le, le_rfl⟩).tendsto).mono_left (nhdsWithin_le_of_mem hmem)
    have hY : Tendsto (fun u => y u 0) (𝓝[<] t) (𝓝 (y t 0)) :=
      ((hcont.2 t ⟨hr0.le, le_rfl⟩).tendsto).mono_left (nhdsWithin_le_of_mem hmem)
    refine ⟨0, half_pos hx0, half_pos hy0, by linarith, ?_⟩
    filter_upwards [hev, hX.eventually (lt_mem_nhds (half_lt_self hx0)),
      hY.eventually (lt_mem_nhds (half_lt_self hy0))] with u hu h1 h2
    exact ⟨by rw [hu, hq]; exact hpos, h1.le, h2.le⟩
  · have hr1 : 1 ≤ n r0 := le_trans hpos (hP.antitone hr0.le)
    obtain ⟨q', hq'⟩ : ∃ q', n r0 = q' + 1 := ⟨n r0 - 1, by omega⟩
    have hev' : ∀ᶠ u in 𝓝[<] t, n u = q' + 1 := hev.mono fun u hu => hu.trans hq'
    obtain ⟨hnt, -, -, hsurv⟩ := hP.deletion t ht q' hev' (fun h' => hq (hq'.trans h'.symm))
    obtain ⟨hX, hY⟩ := hsurv 0 (hnt ▸ hpos)
    refine ⟨1, half_pos hx0, half_pos hy0, by linarith, ?_⟩
    filter_upwards [hev', hX.eventually (lt_mem_nhds (half_lt_self hx0)),
      hY.eventually (lt_mem_nhds (half_lt_self hy0))] with u hu h1 h2
    refine ⟨?_, h1.le, h2.le⟩
    rw [hu]; have : 1 ≤ q' := hnt ▸ hpos; omega

theorem tendsto_toNNReal_sub {t : ℝ} (ht : 0 < t) :
    Tendsto (fun a0 : ℝ => (t - a0).toNNReal) (𝓝[>] 0) (𝓝[<] t.toNNReal) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : Continuous fun a0 : ℝ => (t - a0).toNNReal :=
      continuous_real_toNNReal.comp (continuous_const.sub continuous_id)
    have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with a0 ha0
    exact (Real.toNNReal_lt_toNNReal_iff ht).2 (by linarith [mem_Ioi.1 ha0])

theorem ratioOn_dualCoordOf_zero (ν : FiniteMeasure unitInterval) {n : ℕ} (hn : n = 0)
    (a b : ℕ → ℝ) : ratioOn ν (dualCoordOf n a b) = 1 := by
  subst hn; exact ratioOn_level_zero ν _

theorem isRatioParameter_pair {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hb1 : b < 1) :
    IsRatioParameter ![a] ![b] :=
  ⟨Subsingleton.strictMono _, Subsingleton.strictMono _, Fin.forall_fin_one.2 (by simpa using ha),
    Fin.forall_fin_one.2 (by simpa using ⟨hb, hb1⟩)⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : ℝ → Ω → FiniteMeasure unitInterval}
  {Ω' : Type*} [m' : MeasurableSpace Ω'] {P' : Measure Ω'} {𝓖 : Filtration ℝ≥0 m'} {D0 : ℝ}
  {p : ℕ} {x y : Fin p → ℝ} {N : ℝ≥0 → Ω' → ℕ} {X Y : ℝ≥0 → Ω' → ℕ → ℝ}
  (h : IsDualDeletionProcess P' 𝓖 D0 x y N X Y)
  (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
  {k : ℝ → ℝ} (hk : Continuous k) (hk0 : ∀ v, 0 ≤ k v)
  (hmeas : ∀ t, 0 < t → Measurable (μ t))

omit m' in
include hpath hmeas in
/-- **On `{ζ > t}` the forward average at the dual point tends to `0`** (one-pair entrance). -/
theorem tendsto_inner_zero (hent : HasRatioEntrance P μ) {t : ℝ} (ht : 0 < t) {ω' : Ω'}
    (hn : N t.toNNReal ω' ≠ 0) :
    Tendsto (fun a0 => ∫ ω, pathRatio (μ a0 ω) N X Y (t - a0).toNNReal ω' ∂P) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨a, b, i0, ha, hb, hb1, hev⟩ := exists_pair_left (hpath ω') (Real.toNNReal_pos.2 ht) hn
  have hev' := (tendsto_toNNReal_sub ht).eventually hev
  have hz := isRatioParameter_pair ha hb hb1
  have hent' := hent 1 le_rfl (![a], ![b]) hz
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hent' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with a0 _
    exact integral_nonneg fun ω => (pathRatio_mem (hpath ω') _ _).1.le
  · filter_upwards [hev', self_mem_nhdsWithin] with a0 hu ha0
    obtain ⟨hi, hax, hby⟩ := hu
    have hm := hmeas a0 ha0
    refine integral_mono (Integrable.of_bound ((continuous_pathRatio_nu (hpath ω')
      _).measurable.comp hm).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact abs_pathRatio_le (hpath ω') _ _))
      (integrable_ratio_comp (IsRatioParameter.isRatioRange hz) hm) fun ω => ?_
    exact transmissionRatio_le_pair (IsRatioParameter.isRatioRange ((hpath ω').chamber _))
      ⟨i0, hi⟩ ha.le hb.le hax hby _

include h hpath hk hk0 hmeas in
/-- **`W(a₀) → E'[1{ζ < t} K_t]` as `a₀ ↓ 0`.** -/
theorem tendsto_stripV_top (hent : HasRatioEntrance P μ) {t : ℝ} (ht : 0 < t)
    (hζ : ∀ᵐ ω' ∂P', dualExtinction N ω' ≠ ENNReal.ofReal t) :
    Tendsto (fun a0 => stripV P μ a0 t P' k N X Y (fun _ => ⊤) a0 (t - a0)) (𝓝[>] 0)
      (𝓝 (∫ ω', (if dualExtinction N ω' < ENNReal.ofReal t then
        killFac k N X Y (fun _ => ⊤) t ω' else 0) ∂P')) := by
  have := h.prob
  have hτ := isStoppingTime_top (Ω := Ω') 𝓖
  have hev_le : ∀ᶠ a0 in 𝓝[>] (0 : ℝ), 0 < a0 ∧ a0 ≤ t := by
    filter_upwards [Ioo_mem_nhdsGT ht] with a0 h2 using ⟨h2.1, h2.2.le⟩
  have hF : ∀ a0, 0 < a0 → a0 ≤ t → stripV P μ a0 t P' k N X Y (fun _ => ⊤) a0 (t - a0) =
      ∫ ω', (∫ ω, pathRatio (μ a0 ω) N X Y (t - a0).toNNReal ω' ∂P) *
        killFac k N X Y (fun _ => ⊤) (t - a0) ω' ∂P' := fun a0 _ hat => by
    unfold stripV
    rw [clampT_of_mem ⟨le_rfl, hat⟩]
    refine integral_congr_ae (ae_of_all _ fun ω' => ?_)
    congr 1
  refine (tendsto_congr' (hev_le.mono fun a0 h => (hF a0 h.1 h.2))).2 ?_
  have hb : ∀ a0 ω', ‖(∫ ω, pathRatio (μ a0 ω) N X Y (t - a0).toNNReal ω' ∂P) *
      killFac k N X Y (fun _ => ⊤) (t - a0) ω'‖ ≤ 1 := fun a0 ω' => by
    have hK := killFac_mem (τ := fun _ => ⊤) (hpath ω') hk0 (t - a0)
    have hI : |∫ ω, pathRatio (μ a0 ω) N X Y (t - a0).toNNReal ω' ∂P| ≤ 1 := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le_const (C := 1) (ae_of_all _ fun ω => ?_)).trans (by simp)
      rw [Real.norm_eq_abs]; exact abs_pathRatio_le (hpath ω') _ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hK.1]
    exact (mul_le_mul hI hK.2 hK.1.le zero_le_one).trans (le_of_eq (one_mul 1))
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_
    (Eventually.of_forall fun a0 => ae_of_all _ (hb a0)) (integrable_const 1) ?_
  · filter_upwards [hev_le] with a0 ha0
    have hm : Measurable fun z : Ω × Ω' => pathRatio (μ a0 z.1) N X Y (t - a0).toNNReal z.2 :=
      (measurable_pathRatio_joint h hpath).comp
        (f := fun z : Ω × Ω' => (μ a0 z.1, (t - a0, z.2)))
        (((hmeas a0 ha0.1).comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
    exact ((hm.stronglyMeasurable.integral_prod_left' (μ := P)).measurable.mul
      ((measurable_killFac_joint h hpath hτ hk).comp (f := fun ω' => (t - a0, ω'))
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · filter_upwards [hζ] with ω' hω'
    have hK : Tendsto (fun a0 => killFac k N X Y (fun _ => ⊤) (t - a0) ω') (𝓝[>] 0)
        (𝓝 (killFac k N X Y (fun _ => ⊤) t ω')) := by
      have hc : Continuous fun a0 : ℝ => killFac k N X Y (fun _ => ⊤) (t - a0) ω' :=
        (continuous_killFac (τ := fun _ => ⊤) (hpath ω') hk).comp
          (continuous_const.sub continuous_id)
      have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    by_cases hlt : dualExtinction N ω' < ENNReal.ofReal t
    · simp only [hlt, ↓reduceIte]
      obtain ⟨s, hs⟩ := iInf_lt_iff.1 hlt
      obtain ⟨hs0, hst⟩ := iInf_lt_iff.1 hs
      have hst' : (s : ℝ) < t := by
        have : s < t.toNNReal := ENNReal.coe_lt_coe.1 hst
        exact (Real.lt_toNNReal_iff_coe_lt).1 this
      have hone : ∀ᶠ a0 in 𝓝[>] (0 : ℝ),
          ∫ ω, pathRatio (μ a0 ω) N X Y (t - a0).toNNReal ω' ∂P = 1 := by
        filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hst')] with a0 ha0
        have hle : s ≤ (t - a0).toNNReal :=
          (Real.le_toNNReal_iff_coe_le (by linarith [ha0.2, s.coe_nonneg])).2 (by linarith [ha0.2])
        have h0 : N (t - a0).toNNReal ω' = 0 :=
          Nat.eq_zero_of_le_zero (hs0 ▸ (hpath ω').antitone hle)
        have : ∀ ω, pathRatio (μ a0 ω) N X Y (t - a0).toNNReal ω' = 1 := fun ω =>
          ratioOn_dualCoordOf_zero _ h0 _ _
        simp [this]
      have := (tendsto_const_nhds (x := (1 : ℝ)).congr' (hone.mono fun _ h => h.symm)).mul hK
      simpa using this
    · simp only [hlt, ↓reduceIte]
      have hn : N t.toNNReal ω' ≠ 0 := fun h0 => hlt (lt_of_le_of_ne
        (iInf₂_le (f := fun (s : ℝ≥0) (_ : N s ω' = 0) => (s : ℝ≥0∞)) t.toNNReal h0) hω')
      have := (tendsto_inner_zero (P := P) hpath hmeas hent ht hn).mul hK
      simpa using this

end BlockBand.Transmission.LawDuality
