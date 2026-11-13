module

public import BlockBand.SourceProcess.Stochastic.Dyson.Spectrum

/-!
# Dyson Brownian motion: gap stops)

* `iInf_coe_le_iff_of_isClosed`: for a closed `S ⊆ ℝ≥0`, `⨅ v ∈ S, v ≤ u ↔ ∃ v ∈ S, v ≤ u`.
* `measurableSet_exists_le_of_continuous`: for a process with continuous real paths whose time-`v`
  values are measurable for `v ≤ u`, `{ω | ∃ v ≤ u, f v ω ≤ c}` is measurable (countable dense
  subset of `[0,u]` plus attainment of the minimum on the compact `[0,u]`).
* `isStoppingTime_gapStop`: for every everywhere-continuous adapted matrix process the gap stops
  are stopping times of the shifted filtration (no completion needed).
* `gapStop_tendsto_top`: on every sample where `H_t` has simple spectrum for all `t > 0`, the gap
  stops from `s > 0` tend to `⊤`.
* `dysonBM_b4_of_b1`: clause (b4) of the contract, its first half unconditionally and its second
  half from the non-collision statement (b1).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal Matrix
open BlockBand.Internal.Contracts.Transmission

attribute [local instance] secondCountableTopology_matrix

/-- First-hitting infimum of a closed time set: `⨅ v ∈ S, v ≤ u ↔ ∃ v ∈ S, v ≤ u`. -/
theorem iInf_coe_le_iff_of_isClosed {S : Set ℝ≥0} (hS : IsClosed S) (u : ℝ≥0) :
    (⨅ v ∈ S, (v : WithTop ℝ≥0)) ≤ u ↔ ∃ v ∈ S, v ≤ u := by
  constructor
  · intro h
    rcases S.eq_empty_or_nonempty with hE | hne
    · subst hE
      have e : (⨅ v ∈ (∅ : Set ℝ≥0), (v : WithTop ℝ≥0)) = ⊤ := by
        simp only [iInf_eq_top]; intro v hv; exact absurd hv (Set.notMem_empty v)
      rw [e, top_le_iff] at h
      exact absurd h WithTop.coe_ne_top
    · have hmem := hS.csInf_mem hne (OrderBot.bddBelow S)
      have e : (⨅ v ∈ S, (v : WithTop ℝ≥0)) = ↑(sInf S) := by
        rw [WithTop.coe_sInf' hne (OrderBot.bddBelow S), sInf_image]
      rw [e, WithTop.coe_le_coe] at h
      exact ⟨_, hmem, h⟩
  · rintro ⟨v, hv, hvu⟩
    exact (iInf₂_le v hv).trans (WithTop.coe_le_coe.mpr hvu)

/-- Measurability of "the continuous path `f · ω` is `≤ c` somewhere on `[0,u]`". -/
theorem measurableSet_exists_le_of_continuous {Ω : Type*} {m : MeasurableSpace Ω}
    (f : ℝ≥0 → Ω → ℝ) (hf : ∀ ω, Continuous fun v => f v ω) (u : ℝ≥0)
    (hmeas : ∀ v, v ≤ u → Measurable (f v)) (c : ℝ) :
    MeasurableSet {ω | ∃ v, v ≤ u ∧ f v ω ≤ c} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Icc (0 : ℝ≥0) u)
  have key : {ω | ∃ v, v ≤ u ∧ f v ω ≤ c} =
      ⋂ k : ℕ, ⋃ d ∈ D, {ω | f (d : ℝ≥0) ω < c + 1 / ((k : ℝ) + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨v, hvu, hv⟩ k
      have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hopen : IsOpen {x : Icc (0 : ℝ≥0) u | f (x : ℝ≥0) ω < c + 1 / ((k : ℝ) + 1)} :=
        isOpen_lt ((hf ω).comp continuous_subtype_val) continuous_const
      obtain ⟨d, hdD, hdU⟩ := hDd.exists_mem_open hopen
        ⟨⟨v, zero_le, hvu⟩, show f v ω < _ by linarith⟩
      exact ⟨d, hdD, hdU⟩
    · intro h
      obtain ⟨w, hw, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := u)).exists_isMinOn
        ⟨0, le_rfl, zero_le⟩ (hf ω).continuousOn
      refine ⟨w, hw.2, ?_⟩
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨d, -, hd⟩ := h k
      have := hmin d.2
      simp only [mem_ofPred_eq] at this
      linarith
  rw [key]
  refine MeasurableSet.iInter fun k => MeasurableSet.biUnion hDc fun d _ => ?_
  exact measurableSet_lt (hmeas d d.2.2) measurable_const

/-- The time set where some gap of `H_{s+v}` is at most `1/n`. -/
def gapSet {Ω : Type*} (N : ℕ) (H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (n : ℕ)
    (ω : Ω) : Set ℝ≥0 :=
  {v | ∃ i j : Fin N, i ≠ j ∧
    |dysonEigenvalue N (H (s + v) ω) i - dysonEigenvalue N (H (s + v) ω) j| ≤ 1 / (n : ℝ)}

theorem gapStop_eq {Ω : Type*} (N : ℕ) (H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0)
    (n : ℕ) (ω : Ω) : gapStop N H s n ω = ⨅ v ∈ gapSet N H s n ω, (v : WithTop ℝ≥0) := rfl

/-- Continuity of a gap along a continuous matrix path. -/
theorem continuous_gap {N : ℕ} {p : ℝ≥0 → Matrix (Fin N) (Fin N) ℂ} (hp : Continuous p)
    (i j : Fin N) : Continuous fun v => |dysonEigenvalue N (p v) i - dysonEigenvalue N (p v) j| :=
  (((continuous_dysonEigenvalue i).comp hp).sub ((continuous_dysonEigenvalue j).comp hp)).abs

theorem isClosed_gapSet {Ω : Type*} {N : ℕ} {H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}
    (hH : ∀ ω, Continuous fun t => H t ω) (s : ℝ≥0) (n : ℕ) (ω : Ω) :
    IsClosed (gapSet N H s n ω) := by
  have hp : Continuous fun v => H (s + v) ω := (hH ω).comp (continuous_const.add continuous_id)
  have : gapSet N H s n ω = ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j),
      {v | |dysonEigenvalue N (H (s + v) ω) i - dysonEigenvalue N (H (s + v) ω) j| ≤ 1 / (n : ℝ)} := by
    ext v; simp [gapSet]
  rw [this]
  exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => isClosed_le (continuous_gap hp i j) continuous_const

theorem gapStop_le_iff {Ω : Type*} {N : ℕ} {H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}
    (hH : ∀ ω, Continuous fun t => H t ω) (s : ℝ≥0) (n : ℕ) (ω : Ω) (u : ℝ≥0) :
    gapStop N H s n ω ≤ u ↔ ∃ v ∈ gapSet N H s n ω, v ≤ u :=
  iInf_coe_le_iff_of_isClosed (isClosed_gapSet hH s n ω) u

/-- **(b4), first half.** For an everywhere-continuous adapted matrix process the gap stops
from any start `s` are stopping times of `u ↦ 𝓖_{s+u}` (for every `n`, including `n = 0`). -/
theorem isStoppingTime_gapStop {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} (hH : ∀ ω, Continuous fun t => H t ω)
    (hadapt : ∀ t, Measurable[𝓖 t] (H t)) (s : ℝ≥0) (n : ℕ) :
    IsStoppingTime (shiftFiltration 𝓖 s) (gapStop N H s n) := by
  intro u
  have e : {ω | gapStop N H s n ω ≤ u} =
      ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j), {ω | ∃ v, v ≤ u ∧
        |dysonEigenvalue N (H (s + v) ω) i - dysonEigenvalue N (H (s + v) ω) j| ≤ 1 / (n : ℝ)} := by
    ext ω
    simp only [mem_ofPred_eq, gapStop_le_iff hH, gapSet, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨v, ⟨i, j, hij, hv⟩, hvu⟩; exact ⟨i, j, hij, v, hvu, hv⟩
    · rintro ⟨i, j, hij, v, hvu, hv⟩; exact ⟨v, ⟨i, j, hij, hv⟩, hvu⟩
  rw [e]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => ?_
  refine measurableSet_exists_le_of_continuous (m := shiftFiltration 𝓖 s u)
    (fun v ω => |dysonEigenvalue N (H (s + v) ω) i - dysonEigenvalue N (H (s + v) ω) j|)
    (fun ω => continuous_gap ((hH ω).comp (continuous_const.add continuous_id)) i j) u
    (fun v hv => ?_) _
  have hm : Measurable[shiftFiltration 𝓖 s u] (H (s + v)) :=
    (hadapt (s + v)).mono (𝓖.mono ((add_le_add_iff_left s).mpr hv)) le_rfl
  exact continuous_abs.measurable.comp (((continuous_dysonEigenvalue i).measurable.comp hm).sub
    ((continuous_dysonEigenvalue j).measurable.comp hm))

/-- **(b4), second half, pathwise.** If `H_t` has simple spectrum for all `t > 0` along a
continuous path, the gap stops from `s > 0` tend to `⊤`. -/
theorem gapStop_tendsto_top {Ω : Type*} {N : ℕ} {H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}
    (hH : ∀ ω, Continuous fun t => H t ω) {s : ℝ≥0} (hs : 0 < s) {ω : Ω}
    (hsimple : ∀ t : ℝ≥0, 0 < t → HasSimpleSpectrum N (H t ω)) :
    Tendsto (fun n => gapStop N H s n ω) atTop (𝓝 ⊤) := by
  have hp : Continuous fun v => H (s + v) ω := (hH ω).comp (continuous_const.add continuous_id)
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => absurd ha not_top_lt⟩
  lift a to ℝ≥0 using ha.ne
  -- minimal gap over `[0, a]` for every pair, attained on the compact interval
  have hpos : ∀ i j : Fin N, i ≠ j → ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ Icc (0 : ℝ≥0) a,
      δ ≤ |dysonEigenvalue N (H (s + v) ω) i - dysonEigenvalue N (H (s + v) ω) j| := by
    intro i j hij
    obtain ⟨w, -, hw⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := a)).exists_isMinOn
      ⟨0, le_rfl, zero_le⟩ (continuous_gap hp i j).continuousOn
    refine ⟨_, ?_, fun v hv => hw hv⟩
    exact abs_pos.mpr (sub_ne_zero.mpr
      (HasSimpleSpectrum.ne (hsimple _ (add_pos_of_pos_of_nonneg hs zero_le)) hij))
  have hev : ∀ᶠ n : ℕ in atTop, ∀ i j : Fin N, i ≠ j → ∀ v ∈ Icc (0 : ℝ≥0) a,
      1 / (n : ℝ) < |dysonEigenvalue N (H (s + v) ω) i - dysonEigenvalue N (H (s + v) ω) j| := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    obtain ⟨δ, hδ, hδle⟩ := hpos i j hij
    obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hδ
    filter_upwards [eventually_ge_atTop (n₀ + 1)] with n hn _ v hv
    have hn' : ((n₀ : ℝ) + 1) ≤ n := by exact_mod_cast hn
    have : 1 / (n : ℝ) ≤ 1 / ((n₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hn'
    linarith [hδle v hv]
  filter_upwards [hev] with n hn
  by_contra hle
  rw [not_lt, gapStop_le_iff hH] at hle
  obtain ⟨v, ⟨i, j, hij, hv⟩, hva⟩ := hle
  exact absurd hv (not_le.mpr (hn i j hij v ⟨zero_le, hva⟩))

/-- Continuity of `t ↦ F + G_t` for every sample. -/
theorem continuous_hermBM_add {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {N : ℕ}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} (hG : IsHermitianBrownian Q 𝓖 N G)
    (F : Ω → Matrix (Fin N) (Fin N) ℂ) (ω : Ω) : Continuous fun t => F ω + G t ω :=
  continuous_const.add (hG.continuous ω)

/-- Adaptedness of `t ↦ F + G_t` for `𝓖_0`-measurable `F`. -/
theorem measurable_hermBM_add {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {N : ℕ}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} (hG : IsHermitianBrownian Q 𝓖 N G)
    {F : Ω → Matrix (Fin N) (Fin N) ℂ} (hF : Measurable[𝓖 0] F) (t : ℝ≥0) :
    Measurable[𝓖 t] fun ω => F ω + G t ω :=
  (hF.mono (𝓖.mono zero_le) le_rfl).add (hG.adapted t)

/-- **Clause (b4) of `DysonBrownianMotion`**, with its first half (stopping times) proved
unconditionally and its second half (`σ_n → ⊤` a.s.) derived from clause (b1). -/
theorem dysonBM_b4_of_b1 {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {N : ℕ}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}
    (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F)
    (hb1 : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t → HasSimpleSpectrum N (F ω + G t ω)) :
    ∀ (s : ℝ≥0), 0 < s →
      (∀ n : ℕ, 0 < n →
        IsStoppingTime (shiftFiltration 𝓖 s) (gapStop N (fun t ω => F ω + G t ω) s n)) ∧
      ∀ᵐ ω ∂Q, Tendsto (fun n => gapStop N (fun t ω => F ω + G t ω) s n ω) atTop (𝓝 ⊤) := by
  intro s hs
  refine ⟨fun n _ => isStoppingTime_gapStop (continuous_hermBM_add hG F) (measurable_hermBM_add hG hF) s n, ?_⟩
  filter_upwards [hb1] with ω hω
  exact gapStop_tendsto_top (continuous_hermBM_add hG F) hs hω

end BlockBand.SourceProcess.Stochastic.Dyson
