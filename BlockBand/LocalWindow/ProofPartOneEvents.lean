module

public import BlockBand.LocalWindow.ProofPartOnePoint

/-!
# The energy grid and the rank-location event

A finite grid of the bulk interval, Markov's inequality at a real order, and rank location under
the split law, for part (i) of the physical local-window lemma.

## Main results

* `exists_bulk_grid`: a grid of spacing `h` of `bulkInterval κ` with at most `4/h + 1` points.
* `meas_ge_le_of_eLpNorm`: Markov at order `q` from an `L^q` bound (outer measure).
* `splitLaw_rankLocation_le`: rank location under the split law.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartOne
open BlockBand.Internal.Contracts.Layers

/-- **Grid of the bulk interval**: for `0 ≤ κ ≤ 2` and spacing `h > 0` there is a
finite grid `Es ⊆ bulkInterval κ` with `|Es| ≤ 4/h + 1` and every `E ∈ bulkInterval κ` within
`h` of a grid point. -/
theorem exists_bulk_grid {κ h : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 2) (hh : 0 < h) :
    ∃ Es : Finset ℝ, (∀ e ∈ Es, e ∈ bulkInterval κ) ∧ (Es.card : ℝ) ≤ 4 / h + 1 ∧
      ∀ E ∈ bulkInterval κ, ∃ e ∈ Es, |E - e| ≤ h := by
  set K : ℕ := ⌊(4 - 2 * κ) / h⌋₊
  have hK : (K : ℝ) * h ≤ 4 - 2 * κ := by
    have := Nat.floor_le (div_nonneg (by linarith : (0 : ℝ) ≤ 4 - 2 * κ) hh.le)
    rwa [le_div_iff₀ hh] at this
  refine ⟨(Finset.range (K + 1)).image fun k : ℕ => -2 + κ + k * h, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
    have hk' : (k : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have : (k : ℝ) * h ≤ K * h := mul_le_mul_of_nonneg_right hk' hh.le
    have : 0 ≤ (k : ℝ) * h := by positivity
    constructor <;> linarith
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Finset.card_range, Nat.cast_add, Nat.cast_one]
    have := Nat.floor_le (div_nonneg (by linarith : (0 : ℝ) ≤ 4 - 2 * κ) hh.le)
    have : (4 - 2 * κ) / h ≤ 4 / h := div_le_div_of_nonneg_right (by linarith) hh.le
    linarith
  · intro E hE
    obtain ⟨h1, h2⟩ := hE
    set k : ℕ := ⌊(E - (-2 + κ)) / h⌋₊
    have hx : 0 ≤ (E - (-2 + κ)) / h := div_nonneg (by linarith) hh.le
    have hk1 : (k : ℝ) * h ≤ E - (-2 + κ) := by
      have := Nat.floor_le hx; rwa [le_div_iff₀ hh] at this
    have hk2 : E - (-2 + κ) < (k + 1) * h := by
      have := Nat.lt_floor_add_one ((E - (-2 + κ)) / h); rwa [div_lt_iff₀ hh] at this
    have hkK : k ≤ K := Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hh.le)
    refine ⟨-2 + κ + k * h, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
    rw [abs_le]; constructor <;> nlinarith

end BlockBand.LocalWindow.ProofPartOne

namespace BlockBand.LocalWindow.ProofPartOne
open MeasureTheory BlockBand.Internal.Contracts.CoareaPalm BlockBand.Model.Construction
open scoped ENNReal

/-- Markov at order `q` for a real function with an `L^q` bound (no measurability needed). -/
theorem meas_ge_le_of_eLpNorm {X : Type*} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ}
    {q κ B : ℝ} (hq : 1 ≤ q) (hκ : 0 < κ) (hB : 0 ≤ B)
    (hf : eLpNorm f (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B) :
    μ {x | κ ≤ |f x|} ≤ ENNReal.ofReal ((B / κ) ^ q) := by
  have hq0 : ENNReal.ofReal q ≠ 0 := by simp; linarith
  have hqt : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal (by linarith)
  have h := mul_meas_ge_le_pow_eLpNorm' μ hq0 ENNReal.ofReal_ne_top (f := f) (ENNReal.ofReal κ)
  rw [hqt] at h
  have hset : {x | κ ≤ |f x|} = {x | ENNReal.ofReal κ ≤ ‖f x‖ₑ} := by
    ext x
    simp only [Set.mem_ofPred_eq, Real.enorm_eq_ofReal_abs]
    exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).symm
  rw [hset]
  have hpow : eLpNorm f (ENNReal.ofReal q) μ ^ q ≤ ENNReal.ofReal B ^ q :=
    ENNReal.rpow_le_rpow hf (by linarith)
  have hκq : ENNReal.ofReal κ ^ q ≠ 0 := by
    rw [ENNReal.ofReal_rpow_of_nonneg hκ.le (by linarith)]
    simp [Real.rpow_pos_of_pos hκ q]
  rw [ENNReal.ofReal_rpow_of_nonneg hκ.le (by linarith),
    ENNReal.ofReal_rpow_of_nonneg hB (by linarith)] at *
  rw [Real.div_rpow hB hκ.le, ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hκ q),
    ENNReal.le_div_iff_mul_le (Or.inl hκq) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact h.trans hpow

open BlockBand.Internal.Contracts.Layers in
/-- **Rank location under the split law** (the rank-location theorem, `RankLocationContract.location`,
Markov at order `q`, union over the `N = nW` ranks). -/
theorem splitLaw_rankLocation_le (hRL : RankLocationContract) (b T ϑ : ℝ) (hb : 0 < b)
    (hb' : b < 1 / 2) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * p.W →
      ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
        IsPairSplitting p i model (splitS p) Pω → ∀ κ : ℝ, 0 < κ →
          BlockBand.LocalWindow.splitLaw p i Pω {x | ∃ α : Fin p.N, IsBulkRank p ϑ α ∧
              κ ≤ |physicalOrderedEigenvalue p (assemble p i x.1 x.2) α - classicalLocation p α|} ≤
            ENNReal.ofReal (p.N * ((C / (p.n * Real.sqrt p.W)) / κ) ^ q) := by
  obtain ⟨C, hC⟩ := hRL.location b hb hb' T ϑ hϑ hϑ' q hq
  refine ⟨max C 0, le_max_right _ _, fun p hpb hn model i Pω hPω κ hκ => ?_⟩
  set B : ℝ := max C 0 / (p.n * Real.sqrt p.W)
  have hB : 0 ≤ B := div_nonneg (le_max_right _ _) (by positivity)
  set f := fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2
  have hf : Measurable f := BlockBand.Angular.PairCoareaBridge.measurable_assemble p i
  have hone : ∀ α : Fin p.N, BlockBand.LocalWindow.splitLaw p i Pω
      (f ⁻¹' {H | IsBulkRank p ϑ α ∧
        κ ≤ |physicalOrderedEigenvalue p H α - classicalLocation p α|}) ≤
      ENNReal.ofReal ((B / κ) ^ q) := by
    intro α
    refine (Measure.le_map_apply hf.aemeasurable _).trans ?_
    unfold BlockBand.LocalWindow.splitLaw
    rw [hPω]
    by_cases hα : IsBulkRank p ϑ α
    · have hL := hC p hpb hn model .physical α hα
      have hL' : eLpNorm (fun H => physicalOrderedEigenvalue p H α - classicalLocation p α)
          (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) ≤ ENNReal.ofReal B :=
        hL.trans (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)))
      exact (measure_mono fun H hH => hH.2).trans (meas_ge_le_of_eLpNorm _ hq hκ hB hL')
    · have : {H : p.SiteMatrix | IsBulkRank p ϑ α ∧
          κ ≤ |physicalOrderedEigenvalue p H α - classicalLocation p α|} = ∅ := by
        ext H; simp [hα]
      rw [this, measure_empty]; exact bot_le
  have hsub : {x : SplitState p i × PairMatrix p i | ∃ α : Fin p.N, IsBulkRank p ϑ α ∧
      κ ≤ |physicalOrderedEigenvalue p (assemble p i x.1 x.2) α - classicalLocation p α|} ⊆
      ⋃ α : Fin p.N, f ⁻¹' {H | IsBulkRank p ϑ α ∧
        κ ≤ |physicalOrderedEigenvalue p H α - classicalLocation p α|} := by
    rintro x ⟨α, hα, h⟩
    exact Set.mem_iUnion.mpr ⟨α, hα, h⟩
  calc _ ≤ ∑ α : Fin p.N, BlockBand.LocalWindow.splitLaw p i Pω (f ⁻¹' {H | IsBulkRank p ϑ α ∧
        κ ≤ |physicalOrderedEigenvalue p H α - classicalLocation p α|}) :=
        (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _α : Fin p.N, ENNReal.ofReal ((B / κ) ^ q) := Finset.sum_le_sum fun α _ => hone α
    _ = ENNReal.ofReal (p.N * (B / κ) ^ q) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end BlockBand.LocalWindow.ProofPartOne
