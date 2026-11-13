module

public import BlockBand.Palm.MomentFlow.CanonFlows
public import BlockBand.Palm.MomentFlow.LongGenScales
public import BlockBand.Palm.MomentFlow.ExcessCore
public import BlockBand.Palm.MomentFlow.MultiAux

/-!
# The continuous long-versus-short excess over centres and window configurations

* `windowPairs N r W`: pairs `(k₀, ζ)` with `ζ` in the `r`-sector and `rampDist k₀ ζ ≤ W`
  (at most `N^{r+1}`, `card_windowPairs_le`).
* `nearBulk F a c E κ ρ k₀`: every label within `ρ` of `k₀` stays within `κ` of `E` on `[a,c]`
  (`𝓛`-measurable, `measurableSet_nearBulk`).
* **`longShortExcess`** `Y n v ω = Σ_{(k₀,ζ)} 1_{nearBulk k₀}(ω) (|fullC - shortC|(v,ζ) - main)_+`:
  `𝓛`-measurable at each time, continuous in time on every sample, `≥ 0`, bounded on `gapSet n`
  by `#pairs · 2 overlapBound^r`, independent of `n` on `gapSet n`, which are the hypotheses of
  `excess_core`; every term is `≤ Y` (`term_le_longShortExcess`).
* Pathwise generator bounds for the canonical full flow: `fullC_localGen` (the long-jump row
  bound and the local moment bound `M_loc` on bulk configurations, through a regular version
  equal to `fullC`), `fullC_globalGen`.
* `bulk_of_nearBulk`, `rampDist_le_of_mem_occBall`: configurations near the centre are in the bulk.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-!
## Centres, windows and bulk sets
-/

/-- Pairs `(k₀, ζ)` with `rampDist k₀ ζ ≤ W`. -/
def windowPairs (N r : ℕ) (W : ℝ) : Finset (Fin N × Occ N) := by
  classical
  exact ((Finset.univ : Finset (Fin N)) ×ˢ sector N r).filter fun p => (rampDist (p.1 : ℕ) p.2 : ℝ) ≤ W

theorem mem_windowPairs {r : ℕ} {W : ℝ} {k₀ : Fin N} {ζ : Occ N} :
    (k₀, ζ) ∈ windowPairs N r W ↔ ζ ∈ sector N r ∧ (rampDist (k₀ : ℕ) ζ : ℝ) ≤ W := by
  classical
  unfold windowPairs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]

theorem card_windowPairs_le (r : ℕ) (W : ℝ) : ((windowPairs N r W).card : ℝ) ≤ (N : ℝ) ^ (r + 1) := by
  classical
  have h1 : (windowPairs N r W).card ≤ ((Finset.univ : Finset (Fin N)) ×ˢ sector N r).card := by
    unfold windowPairs; exact Finset.card_filter_le _ _
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ((windowPairs N r W).card : ℝ) ≤ (N : ℝ) * (sector N r).card := by exact_mod_cast h1
  calc ((windowPairs N r W).card : ℝ) ≤ (N : ℝ) * (sector N r).card := h2
    _ ≤ (N : ℝ) * (N : ℝ) ^ r := mul_le_mul_of_nonneg_left
        (by exact_mod_cast card_sector_le (N := N) r) (Nat.cast_nonneg N)
    _ = (N : ℝ) ^ (r + 1) := by ring

/-- The configuration occupying (once) every label within `ρ` of `k₀`. -/
def nearCfg (k₀ : Fin N) (ρ : ℝ) : Occ N := by
  classical
  exact fun k => if (labelDist k₀ k : ℝ) ≤ ρ then 1 else 0

theorem nearCfg_pos {k₀ k : Fin N} {ρ : ℝ} : 0 < nearCfg k₀ ρ k ↔ (labelDist k₀ k : ℝ) ≤ ρ := by
  classical
  unfold nearCfg
  split_ifs with h <;> simp [h]

/-- Every label within `ρ` of `k₀` stays within `κ` of `E` on `[a,c]`. -/
def nearBulk (F : Matrix (Fin N) (Fin N) ℂ) (a c E κ ρ : ℝ) (k₀ : Fin N) : Set (FlowSample N) :=
  {ω | ∀ v ∈ Icc a c, ∀ k : Fin N, 0 < nearCfg k₀ ρ k → |flowEigenvalue F a ω v k - E| ≤ κ}

theorem measurableSet_nearBulk {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (a c E κ ρ : ℝ) (k₀ : Fin N) : MeasurableSet[pathSigma F a a c] (nearBulk F a c E κ ρ k₀) :=
  measurableSet_bulk F hF le_rfl le_rfl (nearCfg k₀ ρ) E κ

theorem bulk_of_nearBulk {F : Matrix (Fin N) (Fin N) ℂ} {a c E κ ρ : ℝ} {k₀ : Fin N}
    {ω : FlowSample N} (hω : ω ∈ nearBulk F a c E κ ρ k₀) {η : Occ N}
    (hη : (rampDist (k₀ : ℕ) η : ℝ) ≤ ρ) :
    ∀ k : Fin N, 0 < η k → ∀ σ ∈ Icc a c, |flowEigenvalue F a ω σ k - E| ≤ κ := by
  intro k hk σ hσ
  have h1 : labelDist k k₀ ≤ rampDist (k₀ : ℕ) η := (rampDist_le_iff k₀ η _).1 le_rfl k hk
  have h2 : (labelDist k₀ k : ℝ) ≤ ρ := by
    rw [labelDist_comm]; exact (Nat.cast_le.2 h1).trans hη
  exact hω σ hσ k (nearCfg_pos.2 h2)

theorem rampDist_le_of_mem_occBall {r : ℕ} {R : ℝ} {ζ η : Occ N} (hζ : ζ ∈ sector N r)
    (hη : η ∈ occBall r R ζ) (k₀ : ℕ) :
    (rampDist k₀ η : ℝ) ≤ rampDist k₀ ζ + r * R := by
  classical
  have hη' : η ∈ sector N r ∧ ¬ ((r : ℝ) * R < (occDist ζ η : ℝ)) := by
    unfold occBall at hη; exact Finset.mem_filter.1 hη
  have h := rampDist_sub_le_occDist hζ hη'.1 k₀
  have h2 := not_lt.1 hη'.2
  have := neg_abs_le ((rampDist k₀ ζ : ℝ) - rampDist k₀ η)
  linarith

/-!
## The excess
-/

/-- **The excess** `Σ_{(k₀,ζ)} 1_{nearBulk k₀} (|fullC - shortC|(v,ζ) - main)_+`. -/
def longShortExcess (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (q : Fin N → ℂ) (ℓ r n : ℕ)
    (E κ ρ W main : ℝ) (v : ℝ) (ω : FlowSample N) : ℝ :=
  ∑ p ∈ windowPairs N r W, (nearBulk F a c E κ ρ p.1).indicator
    (fun ω => max (|fullC F a c q r n v ω p.2 - shortC F a c q ℓ r n v ω p.2| - main) 0) ω

theorem measurable_longShortExcess {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) (ℓ r n : ℕ) (E κ ρ W main v : ℝ) :
    Measurable[pathSigma F a a c] (longShortExcess F a c q ℓ r n E κ ρ W main v) := by
  refine Finset.measurable_sum _ fun p _ => ?_
  have h1 := measurable_fullC hF hN hac q r n v p.2
  have h2 := measurable_shortC hF hN hac q ℓ r n v p.2
  have h3 : Measurable[pathSigma F a a c] fun ω =>
      max (|fullC F a c q r n v ω p.2 - shortC F a c q ℓ r n v ω p.2| - main) 0 :=
    ((continuous_abs.measurable.comp (h1.sub h2)).sub_const main).max measurable_const
  exact h3.indicator (measurableSet_nearBulk hF a c E κ ρ p.1)

theorem continuous_longShortExcess {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    (a c : ℝ) (q : Fin N → ℂ) (ℓ r n : ℕ) (E κ ρ W main : ℝ) (ω : FlowSample N) :
    Continuous fun v => longShortExcess F a c q ℓ r n E κ ρ W main v ω := by
  refine continuous_finsetSum _ fun p _ => ?_
  by_cases hω : ω ∈ nearBulk F a c E κ ρ p.1
  · simp only [Set.indicator_of_mem hω]
    exact ((((continuous_fullC hF hN a c q r n ω p.2).sub
      (continuous_shortC hF hN a c q ℓ r n ω p.2)).abs).sub continuous_const).max
      continuous_const
  · simp only [Set.indicator_of_notMem hω]
    exact continuous_const

theorem longShortExcess_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (q : Fin N → ℂ) (ℓ r n : ℕ)
    (E κ ρ W main v : ℝ) (ω : FlowSample N) : 0 ≤ longShortExcess F a c q ℓ r n E κ ρ W main v ω :=
  Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => le_max_right _ _) _

theorem term_le_longShortExcess {F : Matrix (Fin N) (Fin N) ℂ} {a c : ℝ} {q : Fin N → ℂ} {ℓ r n : ℕ}
    {E κ ρ W main v : ℝ} {ω : FlowSample N} {k₀ : Fin N} {ζ : Occ N}
    (hp : (k₀, ζ) ∈ windowPairs N r W) (hω : ω ∈ nearBulk F a c E κ ρ k₀) :
    max (|fullC F a c q r n v ω ζ - shortC F a c q ℓ r n v ω ζ| - main) 0 ≤
      longShortExcess F a c q ℓ r n E κ ρ W main v ω := by
  have h := Finset.single_le_sum (f := fun p : Fin N × Occ N => (nearBulk F a c E κ ρ p.1).indicator
    (fun ω => max (|fullC F a c q r n v ω p.2 - shortC F a c q ℓ r n v ω p.2| - main) 0) ω)
    (fun _ _ => Set.indicator_nonneg (fun _ _ => le_max_right _ _) _) hp
  simp only [Set.indicator_of_mem hω] at h
  exact h

theorem longShortExcess_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N) {a c : ℝ}
    (hac : a ≤ c) (q : Fin N → ℂ) (ℓ r n : ℕ) (E κ ρ W : ℝ) {main : ℝ} (hmain : 0 ≤ main)
    {ω : FlowSample N} (hω : ω ∈ gapSet F a c n) {v : ℝ} (hv : v ∈ Icc a c) :
    longShortExcess F a c q ℓ r n E κ ρ W main v ω ≤
      (windowPairs N r W).card * (2 * overlapBound N q ^ r) := by
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
  have hζ : p.2 ∈ sector N r := (mem_windowPairs.1 (show (p.1, p.2) ∈ windowPairs N r W from hp)).1
  have h1 := abs_fullC_le hF hN hac q r n hω v hv p.2 hζ
  have h2 := abs_shortC_le hF hN hac q ℓ r n hω v hv p.2 hζ
  have h3 : max (|fullC F a c q r n v ω p.2 - shortC F a c q ℓ r n v ω p.2| - main) 0 ≤
      2 * overlapBound N q ^ r := by
    refine max_le ?_ (by have := (abs_nonneg _).trans h1; linarith)
    have := abs_sub (fullC F a c q r n v ω p.2) (shortC F a c q ℓ r n v ω p.2)
    linarith
  by_cases hm : ω ∈ nearBulk F a c E κ ρ p.1
  · simp only [Set.indicator_of_mem hm]; exact h3
  · simp only [Set.indicator_of_notMem hm]; exact (le_max_right _ _).trans h3

theorem longShortExcess_succ {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N) {a c : ℝ}
    (hac : a ≤ c) (q : Fin N → ℂ) (ℓ r n : ℕ) (E κ ρ W main : ℝ) {ω : FlowSample N}
    (hω : ω ∈ gapSet F a c n) {v : ℝ} (hv : v ∈ Icc a c) :
    longShortExcess F a c q ℓ r (n + 1) E κ ρ W main v ω = longShortExcess F a c q ℓ r n E κ ρ W main v ω := by
  refine Finset.sum_congr rfl fun p hp => ?_
  have hζ : p.2 ∈ sector N r := (mem_windowPairs.1 (show (p.1, p.2) ∈ windowPairs N r W from hp)).1
  by_cases hm : ω ∈ nearBulk F a c E κ ρ p.1
  · simp only [Set.indicator_of_mem hm]
    rw [fullC_succ hF hN hac q r n hω v hv p.2 hζ, shortC_succ hF hN hac q ℓ r n hω v hv p.2 hζ]
  · simp only [Set.indicator_of_notMem hm]

/-!
## Pathwise generator bounds for the canonical full flow
-/

/-- **Local bound** (the long-jump row bound and `M_loc`, through a version `Φ` equal to `fullC`
on the sample). -/
theorem fullC_localGen {F : Matrix (Fin N) (Fin N) ℂ} {a c : ℝ} {q : Fin N → ℂ} {ℓ r n : ℕ}
    {ω : FlowSample N} {Φ : ℝ → Occ N → FlowSample N → ℝ}
    (hΦeq : ∀ σ ∈ Icc a c, ∀ ζ ∈ sector N r, Φ σ ζ ω = fullC F a c q r n σ ω ζ)
    {E κ d b L : ℝ} (hpos : ∀ ξ ∈ sector N r, ∀ σ ∈ Icc a c, 0 ≤ Φ σ ξ ω)
    (hb : ∀ ξ ∈ sector N r, ∀ σ ∈ Icc a c,
      (∀ k : Fin N, 0 < ξ k → ∀ σ' ∈ Icc a c, |flowEigenvalue F a ω σ' k - E| ≤ κ) →
      Φ σ ξ ω ≤ b)
    (hd : ∀ ξ ∈ sector N r, ∀ i : Fin N, 0 < ξ i →
      (∀ k : Fin N, 0 < ξ k → ∀ σ' ∈ Icc a c, |flowEigenvalue F a ω σ' k - E| ≤ κ) →
      ∀ σ ∈ Icc a c, ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
        flowRate F a ω σ i j * ((ξ j : ℝ) + 1) * Φ σ (move ξ i j) ω ≤ d)
    (hL : ∀ σ ∈ Icc a c, ∀ i : Fin N, longCoupling F a ω ℓ σ i ≤ L) :
    ∀ σ ∈ Icc a c, ∀ η ∈ sector N r,
      (∀ k : Fin N, 0 < η k → ∀ σ' ∈ Icc a c, |flowEigenvalue F a ω σ' k - E| ≤ κ) →
      |momentGenerator (flowRate F a ω σ) (fullC F a c q r n σ ω) η -
          momentGenerator (shortFlowRate F a ω ℓ σ) (fullC F a c q r n σ ω) η| ≤
        r * d + (r + 1) * b * (r * L) := by
  intro σ hσ η hη hbulk
  refine longGen_local_bound hη (fun ζ hζ => by rw [← hΦeq σ hσ ζ hζ]; exact hpos ζ hζ σ hσ)
    (fun i hi => ?_) (by rw [← hΦeq σ hσ η hη]; exact hb η hη σ hσ hbulk) (hL σ hσ)
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_)) (hd η hη i hi hbulk σ hσ)
  by_cases hij : i = j
  · subst hij; rw [flowRate_self]; ring
  · rw [hΦeq σ hσ _ (move_mem_sector hη hij hi)]

/-- **Global bound** `2 overlapBound^r (r+1) r L` on the whole sector. -/
theorem fullC_globalGen {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) (ℓ r n : ℕ) {ω : FlowSample N}
    (hω : ω ∈ gapSet F a c n) {L : ℝ}
    (hL : ∀ σ ∈ Icc a c, ∀ i : Fin N, longCoupling F a ω ℓ σ i ≤ L) :
    ∀ σ ∈ Icc a c, ∀ η ∈ sector N r,
      |momentGenerator (flowRate F a ω σ) (fullC F a c q r n σ ω) η -
          momentGenerator (shortFlowRate F a ω ℓ σ) (fullC F a c q r n σ ω) η| ≤
        2 * overlapBound N q ^ r * (r + 1) * r * L := fun σ hσ _η hη =>
  longGen_global_bound hη (abs_fullC_le hF hN hac q r n hω σ hσ) (hL σ hσ)

end BlockBand.Palm.MomentFlow
