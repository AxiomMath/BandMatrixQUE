module

public import BlockBand.Transmission.Dual.LevelPath

/-!
# Level gaps of a continuous path functional

For a deletion path and any continuous path functional `G`, the localized increments of `G` across
the level gaps converge (`tendsto_level_gap_of_continuous`), extending `Dual.tendsto_level_gap`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {n : ℝ≥0 → ℕ} {x y : ℝ≥0 → ℕ → ℝ} {q : ℕ}

/-- **Convergence of the localized increments, for any continuous path functional `G`**
(`Dual.tendsto_level_gap` is the case `G = R`). -/
theorem tendsto_level_gap_of_continuous (hP : IsDeletionPath n x y) {G : ℝ≥0 → ℝ}
    (hR : Continuous G) (hq : 1 ≤ q) (hq0 : q ≤ n 0)
    (rho : ℝ≥0) (θ : ℕ → WithTop ℝ≥0)
    (hb : ∀ e : ℝ≥0, entryTime n (q - 1) = e → ∀ k, θ k ≤ e)
    (hc : ∀ t : ℝ≥0, entryTime n q ≤ t → (t : WithTop ℝ≥0) < entryTime n (q - 1) →
      ∀ᶠ k in atTop, (t : WithTop ℝ≥0) < θ k) :
    Tendsto (fun k => if entryTime n q ≤ ((min (rho : WithTop ℝ≥0) (θ k)).untopA : WithTop ℝ≥0)
        ∧ entryTime n q < θ k then
          G (min (rho : WithTop ℝ≥0) (θ k)).untopA -
            G (entryTime n q).untopA else 0) atTop
      (𝓝 (G (min (rho : WithTop ℝ≥0) (entryTime n (q - 1))).untopA -
        G (min (rho : WithTop ℝ≥0) (entryTime n q)).untopA)) := by
  have hmin_ne : ∀ a : WithTop ℝ≥0, min (rho : WithTop ℝ≥0) a ≠ ⊤ := fun a =>
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  by_cases hE : entryTime n q ≤ rho
  · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hE)
    have hs' : entryTime n q = s := hs.symm
    have hsρ : s ≤ rho := WithTop.coe_le_coe.1 (hs' ▸ hE)
    have hsE' := entryTime_lt_pred hP hq hq0 hs'
    have hθs := hc s hs'.le hsE'
    have hmE : min (rho : WithTop ℝ≥0) (entryTime n q) = s := by
      rw [hs']; exact min_eq_right (WithTop.coe_le_coe.2 hsρ)
    rw [hmE, untopA_coe', hs', untopA_coe']
    by_cases hrE' : (rho : WithTop ℝ≥0) < entryTime n (q - 1)
    · have hθρ := hc rho hE hrE'
      rw [min_eq_left hrE'.le, untopA_coe']
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hθρ] with k hk
      rw [min_eq_left hk.le, untopA_coe']
      have hc1 : (s : WithTop ℝ≥0) ≤ rho := WithTop.coe_le_coe.2 hsρ
      have hc2 : (s : WithTop ℝ≥0) < θ k := lt_of_le_of_lt hc1 hk
      simp only [hc1, hc2, and_self, ↓reduceIte]
    · obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.1
        (ne_top_of_le_ne_top WithTop.coe_ne_top (not_lt.1 hrE'))
      have he' : entryTime n (q - 1) = e := he.symm
      have heρ : e ≤ rho := WithTop.coe_le_coe.1 (he' ▸ not_lt.1 hrE')
      have hse : s < e := WithTop.coe_lt_coe.1 (he' ▸ hsE')
      rw [he', min_eq_right (WithTop.coe_le_coe.2 heρ), untopA_coe']
      have hθe : ∀ k, θ k ≤ e := hb e he'
      have hmin : ∀ k, min (rho : WithTop ℝ≥0) (θ k) = θ k := fun k =>
        min_eq_right ((hθe k).trans (WithTop.coe_le_coe.2 heρ))
      have hfin : ∀ k, θ k ≠ ⊤ := fun k => ne_top_of_le_ne_top WithTop.coe_ne_top (hθe k)
      have hlim : Tendsto (fun k => (θ k).untopA) atTop (𝓝 e) := by
        refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
        · have h1 : (max a s : WithTop ℝ≥0) < entryTime n (q - 1) := by
            rw [he']; exact WithTop.coe_lt_coe.2 (max_lt ha hse)
          filter_upwards [hc (max a s) (hs'.trans_le (WithTop.coe_le_coe.2 (le_max_right a s)))
            h1] with k hk
          rw [← coe_untopA_of_ne_top (hfin k)] at hk
          exact lt_of_le_of_lt (le_max_left a s) (WithTop.coe_lt_coe.1 hk)
        · refine Eventually.of_forall fun k => lt_of_le_of_lt ?_ ha
          rw [← WithTop.coe_le_coe, coe_untopA_of_ne_top (hfin k)]
          exact hθe k
      refine ((hR.tendsto e).comp hlim |>.sub tendsto_const_nhds).congr' ?_
      filter_upwards [hθs] with k hk
      rw [hmin k]
      have h1 : (s : WithTop ℝ≥0) ≤ ((θ k).untopA : WithTop ℝ≥0) := by
        rw [coe_untopA_of_ne_top (hfin k)]; exact hk.le
      simp only [h1, hk, and_self, ↓reduceIte, Function.comp_apply]
  · have hE' : ¬ entryTime n (q - 1) ≤ rho := fun h => hE ((entryTime_mono_pred q).trans h)
    rw [min_eq_left (not_le.1 hE').le, min_eq_left (not_le.1 hE).le, sub_self]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun k => ?_)
    have : ¬ entryTime n q ≤ ((min (rho : WithTop ℝ≥0) (θ k)).untopA : WithTop ℝ≥0) := by
      rw [coe_untopA_of_ne_top (hmin_ne _)]
      exact fun h => hE (h.trans (min_le_left _ _))
    simp only [this, false_and, ↓reduceIte]

end BlockBand.Transmission.LawDuality
