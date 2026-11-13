module

public import BlockBand.Transmission.Generator.ProdTools
public import BlockBand.Internal.Contracts.TransmissionLaws

/-!
# Grid sums of source tests

For `g` continuous on `[s,T]` (`0 < s`) and zero outside, the grid sums
`Σ_{k<⌊WT⌋} g((k+1)/W)/W` tend to `∫_{[s,T]} g` (`tendsto_gridSum`). A source test may jump at
`s` and at `T` (`IsSourceTest` asks continuity only on `[s,T]`): the grid points `(k+1)/W` lie to
the right of `⌊Wu⌋/W`, so the cell values converge to `g(u)` for `u ∈ [s,T)` and to `0` at `u = T`,
and `riemann_tendsto` applies to `1_{[s,T)} g`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapCond

open MeasureTheory Filter Topology

/-- The grid point to the right of `u`. -/
theorem gridPoint_bounds {W : ℕ} (hW : 0 < W) {u : ℝ} (hu : 0 ≤ u) :
    u < (((⌊(W : ℝ) * u⌋₊ + 1 : ℕ) : ℝ)) / W ∧
      (((⌊(W : ℝ) * u⌋₊ + 1 : ℕ) : ℝ)) / W ≤ u + 1 / W := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 := Nat.lt_floor_add_one ((W : ℝ) * u)
  have h2 := Nat.floor_le (mul_nonneg hWr.le hu)
  push_cast
  constructor
  · rw [lt_div_iff₀ hWr]; linarith
  · rw [div_le_iff₀ hWr, add_mul, one_div, inv_mul_cancel₀ hWr.ne']; linarith

theorem tendsto_gridPoint {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun W : ℕ => (((⌊(W : ℝ) * u⌋₊ + 1 : ℕ) : ℝ)) / W) atTop (𝓝[>] u) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, (eventually_ge_atTop 1).mono fun W hW =>
    (gridPoint_bounds hW hu).1⟩
  have hup : Tendsto (fun W : ℕ => u + 1 / (W : ℝ)) atTop (𝓝 u) := by
    have := (tendsto_const_nhds (x := u)).add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · exact (eventually_ge_atTop 1).mono fun W hW => (gridPoint_bounds hW hu).1.le
  · exact (eventually_ge_atTop 1).mono fun W hW => (gridPoint_bounds hW hu).2

variable {s T : ℝ} {g : ℝ → ℝ}

/-- The cell values converge to `1_{[s,T)} g`. -/
theorem tendsto_cell (hg : ContinuousOn g (Set.Icc s T))
    (hg0 : ∀ x, x ∉ Set.Icc s T → g x = 0) {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun W : ℕ => g ((((⌊(W : ℝ) * u⌋₊ + 1 : ℕ) : ℝ)) / W)) atTop
      (𝓝 ((Set.Ico s T).indicator g u)) := by
  have hx := tendsto_gridPoint hu
  rcases lt_or_ge u s with hus | hsu
  · rw [Set.indicator_of_notMem (fun h => absurd h.1 (not_le.2 hus))]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hx (Ioo_mem_nhdsGT hus)] with W hW
    exact (hg0 _ fun h => absurd h.1 (not_le.2 hW.2)).symm
  rcases lt_or_ge u T with huT | hTu
  · rw [Set.indicator_of_mem (show u ∈ Set.Ico s T from ⟨hsu, huT⟩)]
    have hc : Tendsto g (𝓝[Set.Icc s T] u) (𝓝 (g u)) :=
      hg u (show u ∈ Set.Icc s T from ⟨hsu, huT.le⟩)
    refine hc.comp (tendsto_nhdsWithin_iff.2 ⟨tendsto_nhdsWithin_iff.1 hx |>.1, ?_⟩)
    filter_upwards [hx (Ioo_mem_nhdsGT huT)] with W hW
    exact ⟨hsu.trans hW.1.le, hW.2.le⟩
  · rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.2 hTu))]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [tendsto_nhdsWithin_iff.1 hx |>.2] with W hW
    exact (hg0 _ fun h => absurd (hTu.trans_lt hW) (not_lt.2 h.2)).symm

/-- **Grid sums converge** to `∫_{[s,T]} g`. -/
theorem tendsto_gridSum (hs : 0 < s) (hsT : s ≤ T) (hg : ContinuousOn g (Set.Icc s T))
    (hg0 : ∀ x, x ∉ Set.Icc s T → g x = 0) :
    Tendsto (fun W : ℕ => ∑ k ∈ Finset.range ⌊(W : ℝ) * T⌋₊, g (((k + 1 : ℕ) : ℝ) / W) / W)
      atTop (𝓝 (∫ x in Set.Icc s T, g x)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hbd : ∀ x, |g x| ≤ C := by
    intro x
    by_cases hx : x ∈ Set.Icc s T
    · simpa [Real.norm_eq_abs] using hC x hx
    · rw [hg0 x hx, abs_zero]
      exact (norm_nonneg _).trans (hC s ⟨le_rfl, hsT⟩)
  have hT0 : 0 ≤ T := hs.le.trans hsT
  have h := Transmission.Generator.riemann_tendsto (σ := id) tendsto_id
    (c := fun W r => g (((r + 1 : ℕ) : ℝ) / W)) (g := (Set.Ico s T).indicator g) (K := C)
    (s := 0) (t := T) le_rfl hT0 (Eventually.of_forall fun W u _ => hbd _)
    (fun u (hu : u ∈ Set.Icc 0 T) => tendsto_cell hg hg0 hu.1)
  have e : ∫ u in (0 : ℝ)..T, (Set.Ico s T).indicator g u = ∫ x in Set.Icc s T, g x := by
    rw [intervalIntegral.integral_of_le hT0, integral_indicator measurableSet_Ico,
      Measure.restrict_restrict measurableSet_Ico,
      Set.inter_eq_left.2 fun x (hx : x ∈ Set.Ico s T) =>
        (show x ∈ Set.Ioc 0 T from ⟨hs.trans_le hx.1, hx.2.le⟩)]
    exact setIntegral_congr_set Ico_ae_eq_Icc
  rw [e] at h
  refine h.congr fun W => ?_
  rw [mul_zero, Nat.floor_zero, ← Finset.range_eq_Ico]
  rfl

end BlockBand.SourceProcess.CapCond
