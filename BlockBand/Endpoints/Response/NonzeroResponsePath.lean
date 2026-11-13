module

public import BlockBand.Endpoints.Response.PassDerivativeLimitResponse

/-!
# Pathwise and measurability facts for the one-pair boundary dual

For a `p = 1` boundary deletion path (`IsBoundaryDeletionPath`, level `1` at time `0`):
* `nzr_level_zero_iff`, `nzr_level_one_iff`: `N_t = 0 ↔ σ₀ ≤ t` and `N_t = 1 ↔ t < σ₀`
  (`σ₀ = dualExtinction N`);
* `nzr_total_continuous`: `s ↦ R_s` (`dualTotal`, real time through `toNNReal`) is continuous on
  `ℝ` (continuous before `σ₀`, tending to `0` at `σ₀`, zero afterwards).
For a realization:
* `nzr_total_measurable`: each `R_s` is measurable;
* `nzr_caratheodory`: a process measurable at each time with a.s. continuous paths agrees a.s.
  (for all times simultaneously) with a jointly measurable process.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

section Path

variable {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {ω : Ω}

/-- `N_t = 0` iff the extinction time is `≤ t` (antitone, right-continuous level). -/
theorem nzr_level_zero_iff
    (hp : IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) (t : ℝ≥0) :
    N t ω = 0 ↔ dualExtinction N ω ≤ t := by
  constructor
  · intro h
    exact iInf₂_le t h
  · intro hle
    by_contra hne
    have hev := hp.rightCont t
    obtain ⟨t', ht', hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    have : (t' : ℝ≥0∞) ≤ dualExtinction N ω := by
      refine le_iInf₂ fun u hu => ?_
      by_contra hlt
      push Not at hlt
      have hlt' : u < t' := by exact_mod_cast hlt
      rcases le_or_gt u t with hut | hut
      · have := hp.antitone hut
        rw [hu] at this
        omega
      · have : N u ω = N t ω := hsub ⟨hut, hlt'⟩
        rw [hu] at this
        exact hne this.symm
    have : (t' : ℝ≥0∞) ≤ t := this.trans hle
    have : t' ≤ t := by exact_mod_cast this
    exact absurd ht' (not_lt.2 this)

theorem nzr_level_one_iff
    (hp : IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (h0 : N 0 ω = 1) (t : ℝ≥0) : N t ω = 1 ↔ (t : ℝ≥0∞) < dualExtinction N ω := by
  rw [← not_le, ← nzr_level_zero_iff hp t]
  rcases boundaryPath_level (n := fun t => N t ω) hp h0 t with h | h
  · simp [h]
  · simp [h]

theorem nzr_extinction_pos
    (hp : IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (h0 : N 0 ω = 1) : 0 < dualExtinction N ω := by
  have := (nzr_level_one_iff hp h0 0).1 h0
  simpa using this

/-- **Continuity of `s ↦ R_s`** along a `p = 1` boundary path, on all of `ℝ≥0`. -/
theorem nzr_total_continuous_nnreal
    (hp : IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (h0 : N 0 ω = 1) : Continuous (fun u : ℝ≥0 => dualTotal (N u ω) (X u ω) (Y u ω)) := by
  set g : ℝ≥0 → ℝ := fun u => dualTotal (N u ω) (X u ω) (Y u ω)
  set h : ℝ≥0 → ℝ := fun u => X u ω 0 + Y u ω 0
  have hgh : ∀ u : ℝ≥0, (u : ℝ≥0∞) < dualExtinction N ω → g u = h u := by
    intro u hu
    simp only [g, h, (nzr_level_one_iff hp h0 u).2 hu, dualTotal_one]
  have hg0 : ∀ u : ℝ≥0, dualExtinction N ω ≤ u → g u = 0 := by
    intro u hu
    simp only [g, (nzr_level_zero_iff hp u).2 hu, dualTotal_zero]
  -- continuity of `h` on `[0, T]` while the level is `1`
  have hcont : ∀ T : ℝ≥0, (T : ℝ≥0∞) < dualExtinction N ω → ContinuousOn h (Icc 0 T) := by
    intro T hT
    have hT1 := (nzr_level_one_iff hp h0 T).2 hT
    obtain ⟨hcx, hcy⟩ := hp.cont 0 T (zero_le : (0 : ℝ≥0) ≤ T) (by rw [hT1, h0]) 0
      (by rw [h0]; omega)
    exact hcx.add hcy
  refine continuous_iff_continuousAt.2 fun u => ?_
  rcases lt_trichotomy (u : ℝ≥0∞) (dualExtinction N ω) with hu | hu | hu
  · obtain ⟨T, huT, hT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hu
    have huT' : u < T := by exact_mod_cast huT
    have hgc : ContinuousOn g (Icc 0 T) :=
      (hcont T hT).congr fun v hv => hgh v (lt_of_le_of_lt (by exact_mod_cast hv.2) hT)
    exact hgc.continuousAt (mem_of_superset (Iio_mem_nhds huT') fun v hv => ⟨(zero_le : (0 : ℝ≥0) ≤ v), hv.le⟩)
  · -- `u = σ₀`
    have hgu : g u = 0 := hg0 u hu.ge
    have hupos : 0 < u := by
      have := nzr_extinction_pos hp h0
      rw [← hu] at this
      exact_mod_cast this
    rw [continuousAt_iff_continuous_left'_right']
    constructor
    · have hbefore : ∀ v, v < u → N v ω = 1 := fun v hv =>
        (nzr_level_one_iff hp h0 v).2 (hu ▸ by exact_mod_cast hv)
      have hdel := hp.deletion u hupos 0
        (eventually_nhdsWithin_of_forall fun v hv => by simp only [zero_add]; exact hbefore v hv)
        (by simp only [zero_add]; rw [(nzr_level_zero_iff hp u).2 hu.ge]; omega)
      obtain ⟨-, hx, hy, -⟩ := hdel
      have hlim : Tendsto h (𝓝[<] u) (𝓝 0) := by
        have := hx.add hy
        simpa [h] using this
      rw [ContinuousWithinAt, hgu]
      exact hlim.congr' (eventually_nhdsWithin_of_forall fun v hv =>
        (hgh v (hu ▸ by exact_mod_cast hv)).symm)
    · rw [ContinuousWithinAt, hgu]
      exact tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun v hv =>
        (hg0 v (hu ▸ by exact_mod_cast (le_of_lt hv))).symm)
  · -- after extinction
    have hfin : dualExtinction N ω ≠ ⊤ := ne_top_of_lt hu
    set σ : ℝ≥0 := (dualExtinction N ω).toNNReal
    have hσ : (σ : ℝ≥0∞) = dualExtinction N ω := ENNReal.coe_toNNReal hfin
    have hσu : σ < u := by rw [← hσ] at hu; exact_mod_cast hu
    have hev : g =ᶠ[𝓝 u] fun _ => 0 :=
      eventually_of_mem (Ioi_mem_nhds hσu) fun v hv => hg0 v (by rw [← hσ]; exact_mod_cast le_of_lt hv)
    exact (continuousAt_const.congr hev.symm)

/-- **Continuity of `s ↦ R_s` in real time** (`s ↦ R_{s⁺}`) along a `p = 1` boundary path. -/
theorem nzr_total_continuous
    (hp : IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (h0 : N 0 ω = 1) :
    Continuous (fun s : ℝ => dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω)) :=
  (nzr_total_continuous_nnreal hp h0).comp continuous_real_toNNReal

end Path

section Meas

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `ω ↦ dualTotal (N ω) (X ω) (Y ω)` is measurable for measurable `N, X, Y`. -/
theorem nzr_dualTotal_measurable {N : Ω → ℕ} {X Y : Ω → ℕ → ℝ} (hN : Measurable N)
    (hX : Measurable X) (hY : Measurable Y) :
    Measurable fun ω => dualTotal (N ω) (X ω) (Y ω) := by
  have hF : Measurable fun w : ((ℕ → ℝ) × (ℕ → ℝ)) × ℕ => dualTotal w.2 w.1.1 w.1.2 := by
    refine measurable_from_prod_countable_left fun n => ?_
    simp only [dualTotal]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp measurable_fst).add ((measurable_pi_apply i).comp measurable_snd)
  exact hF.comp ((hX.prodMk hY).prodMk hN)

/-- Each `R_s` of a realization is measurable. -/
theorem nzr_total_measurable {P : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {p : ℕ}
    {x y : Fin p → ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (hR : IsBoundaryDualProcess P 𝓖 D0 x y N X Y) (s : ℝ) :
    Measurable fun ω => dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω) := by
  obtain ⟨hN, hX, hY⟩ := hR.adapted s.toNNReal
  exact nzr_dualTotal_measurable (hN.mono (𝓖.le _) le_rfl) (hX.mono (𝓖.le _) le_rfl)
    (hY.mono (𝓖.le _) le_rfl)

/-- **Carathéodory modification.** A real process measurable at each time with a.s. continuous
paths agrees a.s., simultaneously for all times, with a jointly measurable process that is
measurable at each time. -/
theorem nzr_caratheodory {P : Measure Ω} (u : ℝ → Ω → ℝ) (hmeas : ∀ s, Measurable (u s))
    (hcont : ∀ᵐ ω ∂P, Continuous fun s => u s ω) :
    ∃ u' : ℝ → Ω → ℝ, Measurable (Function.uncurry u') ∧ (∀ s, Measurable (u' s)) ∧
      ∀ᵐ ω ∂P, ∀ s, u' s ω = u s ω := by
  set B : Set Ω := {ω | ¬Continuous fun s => u s ω}
  set G : Set Ω := (toMeasurable P B)ᶜ
  have hG : MeasurableSet G := (measurableSet_toMeasurable P B).compl
  have hGc : ∀ ω ∈ G, Continuous fun s => u s ω := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable P B h)
  have hBnull : P B = 0 := by
    exact ae_iff.1 hcont
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    simp only [G, mem_compl_iff, not_not, ofPred_mem_eq, measure_toMeasurable, hBnull]
  refine ⟨fun s => G.indicator (u s), ?_, fun s => (hmeas s).indicator hG, ?_⟩
  · refine measurable_uncurry_of_continuous_of_measurable (fun ω => ?_)
      (fun s => (hmeas s).indicator hG)
    by_cases hω : ω ∈ G
    · simpa [indicator_of_mem hω] using hGc ω hω
    · simpa [indicator_of_notMem hω] using continuous_const
  · filter_upwards [hGae] with ω hω s
    exact indicator_of_mem hω _

end Meas

end BlockBand.Endpoints
