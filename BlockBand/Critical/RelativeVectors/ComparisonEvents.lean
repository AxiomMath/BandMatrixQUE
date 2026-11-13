module

public import BlockBand.Critical.RelativeVectors.CompareDuhamel
public import BlockBand.Critical.RelativeVectors.Disintegration

/-!
# The good events and the good eigenvalue paths

`exists_rmv_sets`: given four (outer-measure) bad sets of probability `≤ N^{-D'}` each, outside
of which (and of the null sets of non-Hermitian `G_a` and of collisions) every sample is good
(`RmvGood`), and outside the spectral one of which the long-gap bound holds on `[a,c]`, there are
* a measurable event `𝒜 ⊆ {RmvGood}` with `P(𝒜ᶜ) ≤ 4N^{-D'}` (`toMeasurable` of the bad set),
* `𝓛`-measurable good paths `𝒢 ⊆ simplePathSet ∩ longGapPathSet` (`step1_goodPaths`)
  with `P(𝒢ᶜ) ≤ N^{-D₁} + N^{-D'}` and `P(B ∩ 𝒜ᶜ) ≤ N^{-D₁}P(B)` for `𝓛`-measurable `B ⊆ 𝒢`,
provided `4N^{-D'} ≤ N^{-2D₁}`. The eigenvalue-path part of the long-gap event `𝓡` that the
Duhamel identity needs (clause 1) is the `𝓛`-measurable `longGapPathSet` (countable reduction by
continuity); the remaining clauses and the localization event enter through `𝒜`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Finset Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.MomentFlow

variable {N r : ℕ}

theorem exists_rmv_sets (hDBM : DysonBrownianMotion N) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    {E r₀ : ℝ} {V : Matrix (Fin N) (Fin r) ℂ} {t : ℝ} {ℓ w : ℕ}
    {c₁ Csp b₀ Ccomp Cd Mint Cw Dsp D₁ D' : ℝ}
    (Bc Bi Bs Bsp : Set (FlowSample N))
    (hBc : flowLaw N a Bc ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')))
    (hBi : flowLaw N a Bi ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')))
    (hBs : flowLaw N a Bs ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')))
    (hBsp : flowLaw N a Bsp ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')))
    (hgood : ∀ ω : FlowSample N, ω.1.IsHermitian →
      (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) → ω ∉ Bc → ω ∉ Bi → ω ∉ Bs →
        ω ∉ Bsp → RmvGood F c E r₀ V a t ℓ w c₁ Csp b₀ Ccomp Cd Mint Cw Dsp ω)
    (hlong : ∀ ω : FlowSample N, ω.1.IsHermitian → ω ∉ Bs → ∀ σ ∈ Icc a c,
      ∀ i j : Fin N, ℓ ≤ labelDist i j →
        c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|)
    (hD' : 4 * (N : ℝ) ^ (-D') ≤ (N : ℝ) ^ (-(2 * D₁))) :
    ∃ 𝒜 𝒢 : Set (FlowSample N), MeasurableSet 𝒜 ∧
      (∀ ω ∈ 𝒜, RmvGood F c E r₀ V a t ℓ w c₁ Csp b₀ Ccomp Cd Mint Cw Dsp ω) ∧
      MeasurableSet[pathSigma F a a c] 𝒢 ∧
      flowLaw N a 𝒢ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁) + (N : ℝ) ^ (-D')) ∧
      𝒢 ⊆ simplePathSet F a c ∩ longGapPathSet F a c ℓ c₁ ∧
      ∀ B : Set (FlowSample N), MeasurableSet[pathSigma F a a c] B → B ⊆ 𝒢 →
        (flowLaw N a).real (B ∩ 𝒜ᶜ) ≤ (N : ℝ) ^ (-D₁) * (flowLaw N a).real B := by
  classical
  set μ := flowLaw N a with hμ
  set Nh : Set (FlowSample N) := {ω | ¬ ω.1.IsHermitian} with hNh
  set Ns : Set (FlowSample N) := (simplePathSet F a c)ᶜ with hNs
  have hNh0 : μ Nh = 0 := by
    have h := BlockBand.Palm.RelativeLocalization.ae_fst_isHermitian (N := N) a
    rw [ae_iff] at h
    exact h
  have hNs0 : μ Ns = 0 := flowLaw_compl_simplePathSet hDBM F hF ha hN hac
  set Bad : Set (FlowSample N) :=
    {ω | ¬ RmvGood F c E r₀ V a t ℓ w c₁ Csp b₀ Ccomp Cd Mint Cw Dsp ω} with hBad
  have hsub : Bad ⊆ Bc ∪ Bi ∪ Bs ∪ Bsp ∪ Nh ∪ Ns := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
    have hh : ω.1.IsHermitian := by simpa [hNh] using h5
    have hs : ω ∈ simplePathSet F a c := by simpa [hNs] using h6
    exact hω (hgood ω hh ((mem_simplePathSet_iff hF hac hh).mp hs) h1 h2 h3 h4)
  have hBadμ : μ Bad ≤ ENNReal.ofReal (4 * (N : ℝ) ^ (-D')) := by
    refine (measure_mono hsub).trans ?_
    refine (measure_union_le _ _).trans ?_
    rw [hNs0, add_zero]
    refine (measure_union_le _ _).trans ?_
    rw [hNh0, add_zero]
    have h4 : μ (Bc ∪ Bi ∪ Bs ∪ Bsp) ≤ μ Bc + μ Bi + μ Bs + μ Bsp :=
      (measure_union_le _ _).trans (add_le_add_left ((measure_union_le _ _).trans
        (add_le_add_left (measure_union_le _ _) _)) _)
    refine h4.trans ((add_le_add (add_le_add (add_le_add hBc hBi) hBs) hBsp).trans (le_of_eq ?_))
    have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg N) _
    rw [← ENNReal.ofReal_add hp hp, ← ENNReal.ofReal_add (by positivity) hp,
      ← ENNReal.ofReal_add (by positivity) hp]
    congr 1; ring
  set 𝒜 : Set (FlowSample N) := (toMeasurable μ Bad)ᶜ with h𝒜
  have h𝒜m : MeasurableSet 𝒜 := (measurableSet_toMeasurable μ Bad).compl
  have h𝒜good : ∀ ω ∈ 𝒜, RmvGood F c E r₀ V a t ℓ w c₁ Csp b₀ Ccomp Cd Mint Cw Dsp ω := by
    intro ω hω
    by_contra hc
    exact hω (subset_toMeasurable μ Bad hc)
  have h𝒜c : μ.real 𝒜ᶜ ≤ (N : ℝ) ^ (-(2 * D₁)) := by
    rw [h𝒜, compl_compl, measureReal_def, measure_toMeasurable]
    have hfin : μ Bad ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hBadμ
    refine le_trans ?_ hD'
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_toReal hfin]
    exact hBadμ
  obtain ⟨𝒢₀, h𝒢₀m, h𝒢₀c, h𝒢₀B⟩ := step1_goodPaths hN F a c D₁ h𝒜m h𝒜c
  refine ⟨𝒜, 𝒢₀ ∩ (simplePathSet F a c ∩ longGapPathSet F a c ℓ c₁), h𝒜m, h𝒜good,
    h𝒢₀m.inter ((measurableSet_simplePathSet F a c).inter
      (measurableSet_longGapPathSet F a c ℓ c₁)), ?_, Set.inter_subset_right, ?_⟩
  · -- complement
    have hlg : (longGapPathSet F a c ℓ c₁)ᶜ ⊆ Bs ∪ Nh := by
      intro ω hω
      by_contra hc
      simp only [Set.mem_union, not_or] at hc
      have hh : ω.1.IsHermitian := by simpa [hNh] using hc.2
      exact hω ((mem_longGapPathSet_iff hF hac hh).mpr (hlong ω hh hc.1))
    have h1 : μ 𝒢₀ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁)) := by
      have hfin : μ 𝒢₀ᶜ ≠ ⊤ := measure_ne_top μ _
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal h𝒢₀c
    have h2 : μ (longGapPathSet F a c ℓ c₁)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
      refine (measure_mono hlg).trans ((measure_union_le _ _).trans ?_)
      rw [hNh0, add_zero]; exact hBs
    rw [Set.compl_inter, Set.compl_inter]
    refine (measure_union_le _ _).trans ?_
    have h3 : μ ((simplePathSet F a c)ᶜ ∪ (longGapPathSet F a c ℓ c₁)ᶜ) ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
      refine (measure_union_le _ _).trans ?_
      rw [show μ (simplePathSet F a c)ᶜ = 0 from hNs0, zero_add]
      exact h2
    refine (add_le_add h1 h3).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
  · intro B hB hBG
    exact h𝒢₀B B hB (hBG.trans Set.inter_subset_left)

end BlockBand.Critical.RelativeVectors
