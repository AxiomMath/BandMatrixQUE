module

public import BlockBand.LocalWindow.Statements
public import BlockBand.LocalWindow.ProofTruncation
public import BlockBand.Angular.PairCoareaBridge

/-!
# Exterior crowding

With high probability no two exterior eigenvalues lie within `ε₀` of a common energy in
`[-L, L]`; this is the crowding estimate of the physical local-window lemma.

## Main results

* `spectralSum_reindex`, `eigenCount_Icc_eq_spectralSum`: counts as spectral sums.
* `exteriorBlock_assemble`: `H_R(assemble ω G) = ω.1`.
* `exteriorCount_two_le` (the exterior crowding bound and Markov): for every splitting law,
  `P{N_{ω.1}([a, b]) ≥ 2} ≤ (C/√c · nW · (b - a))² / 2`.
* `exteriorCrowding_le` (the cover): for `ε₀ > 0`, `L ≥ 0`,
  `P{∃ E ∈ [-L, L], N_{ω.1}([E - ε₀, E + ε₀]) ≥ 2} ≤ (L/ε₀ + 1) (C/√c · nW · 4ε₀)² / 2`.
* `nearSet_card_le_one_of_not_mem`: off that event, `#{j : |λ_j(H_R) - E| ≤ ε₀} ≤ 1` for every
  `|E| ≤ L` (the hypothesis `hnear` of `isPerturbation_actual`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofCrowding

open MeasureTheory ProbabilityTheory Matrix Finset
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open scoped ENNReal

/-!
## Counts as spectral sums
-/

/-- Interval indicator used for counts. -/
def iccInd (a b : ℝ) : ℝ → ℝ := fun l => if a ≤ l ∧ l ≤ b then 1 else 0

/-- `spectralSum` is invariant under reindexing. -/
theorem spectralSum_reindex {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι ℂ) (f : ℝ → ℝ) :
    spectralSum (Matrix.reindex e e A) f = spectralSum A f := by
  unfold spectralSum
  rw [Matrix.charpoly_reindex]

/-- The interval count is monotone in the interval. -/
theorem spectralSum_iccInd_mono {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    spectralSum A (iccInd a b) ≤ spectralSum A (iccInd a' b') := by
  unfold spectralSum
  apply Multiset.sum_map_le_sum_map
  intro z _
  unfold iccInd
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd ⟨ha.trans h1.1, h1.2.trans hb⟩ h2
  · norm_num
  · exact le_rfl

/-- The PSSS eigenvalue count on `[a, b]` is the spectral sum of the indicator. -/
theorem eigenCount_Icc_eq_spectralSum {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : BlockBand.External.PSSS.HermitianMatrix ι) (a b : ℝ) :
    (BlockBand.External.PSSS.eigenCount A (Set.Icc a b) : ℝ) = spectralSum A.1 (iccInd a b) := by
  classical
  have h := BlockBand.LocalWindow.ProofCount.spectralSum_Icc A.2 a b
  unfold iccInd
  rw [h]
  unfold BlockBand.External.PSSS.eigenCount
  norm_cast
  refine Finset.card_bij (fun r _ => BlockBand.Foundations.Spectral.increasingIndex r) ?_ ?_ ?_
  · intro r hr
    simp only [mem_filter, mem_univ, true_and, Set.mem_Icc] at hr ⊢
    rw [BlockBand.Foundations.Spectral.eigenvalue_increasingIndex]
    exact hr
  · intro r _ r' _ h
    exact BlockBand.Foundations.Spectral.increasingIndex.injective h
  · intro j hj
    refine ⟨BlockBand.Foundations.Spectral.increasingIndex.symm j, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and, Set.mem_Icc] at hj ⊢
    have := BlockBand.Foundations.Spectral.eigenvalue_increasingIndex A.2
      (BlockBand.Foundations.Spectral.increasingIndex.symm j)
    rw [Equiv.apply_symm_apply] at this
    rw [← this]
    exact hj

/-!
## The exterior block of the reassembled matrix
-/

section Exterior

variable (p : Parameters) (i : ZMod p.n)

/-- `H_R(assemble ω G) = ω.1`. -/
theorem exteriorBlock_assemble (om : SplitState p i) (G : PairMatrix p i) :
    exteriorBlock p i (assemble p i om G) = om.1 := by
  ext x y
  simp [exteriorBlock, assemble, x.2, y.2]

/-- The exterior blocks `R = {i, i+1}ᶜ`. -/
def exteriorBlocks : Finset (ZMod p.n) := univ.filter fun k => ¬ (k = i ∨ k = i + 1)

/-- Sites of the blocks in `R` are the exterior sites. -/
def exteriorSiteEquiv : BlockSites p (exteriorBlocks p i) ≃ ExteriorSite p i :=
  Equiv.subtypeEquivRight fun x => by simp [exteriorBlocks]

theorem exteriorBlocks_card_le : (exteriorBlocks p i).card ≤ p.n := by
  calc (exteriorBlocks p i).card ≤ (univ : Finset (ZMod p.n)).card := card_filter_le _ _
    _ = p.n := by rw [card_univ, ZMod.card]

/-- `H_R` is the reindexed block-submatrix of `R`. -/
theorem exteriorBlock_eq_reindex (H : p.SiteMatrix) :
    exteriorBlock p i H = Matrix.reindex (exteriorSiteEquiv p i) (exteriorSiteEquiv p i)
      (H.submatrix (Subtype.val : BlockSites p (exteriorBlocks p i) → p.Site) Subtype.val) := by
  ext x y
  rfl

/-- The zero deformation of the conditioning data. -/
def zeroDeformation : p.SiteMatrix →
    BlockBand.External.PSSS.HermitianMatrix (BlockSites p (exteriorBlocks p i)) :=
  fun _ => ⟨0, Matrix.isHermitian_zero⟩

/-- At a Hermitian matrix, the PSSS subsystem count with `R = {i,i+1}ᶜ`, `Φ = 0` is the count of
the exterior block. -/
theorem subsystemCount_eq (H : p.SiteMatrix) (hH : H.IsHermitian) (a b : ℝ) :
    (subsystemCount p (exteriorBlocks p i) (zeroDeformation p i) (Set.Icc a b) H : ℝ) =
      spectralSum (exteriorBlock p i H) (iccInd a b) := by
  unfold subsystemCount
  rw [eigenCount_Icc_eq_spectralSum]
  have hv : (p.physicalHermitianVersion H).1 = H :=
    p.gaussianReconstruction_gaussianExtraction H hH
  simp only [zeroDeformation, add_zero, hv]
  rw [exteriorBlock_eq_reindex, spectralSum_reindex]

end Exterior

/-!
## Exterior crowding and Markov on the split space
-/

section Crowding

/-- The scale `(C/√c · nW · ℓ)² / 2` of the two-point bound for an interval of length `ℓ`. -/
def crowdingBound (p : Parameters) (C ℓ : ℝ) : ℝ :=
  (C / Real.sqrt p.c * ((p.n : ℝ) * p.W) * ℓ) ^ 2 / 2

/-- **Exterior crowding and Markov**, from
`Inputs.PhysicalBlockConditionalCount` (`R = {i,i+1}ᶜ`, `Φ = 0`, `r = 2`). One constant `C > 0`
first; for every admissible `p`, model, adjacent pair, pair splitting law `Pω` at `s = splitS p` and `a ≤ b`, under the original split law,
`P{N_{H_R}([a, b]) ≥ 2} ≤ (C/√c · nW · (b - a))² / 2` (outer measure). -/
theorem exteriorCount_two_le (hPBC : PhysicalBlockConditionalCount) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n)
      (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
      ∀ a b : ℝ, a ≤ b →
        splitLaw p i Pω {x | 2 ≤ spectralSum x.1.1 (iccInd a b)} ≤
          ENNReal.ofReal (crowdingBound p C (b - a)) := by
  obtain ⟨C, hC, hcount⟩ := hPBC
  refine ⟨C, hC, fun p model i Pω hsplit a b hab => ?_⟩
  set μ : Measure p.SiteMatrix := (model.law : Measure p.SiteMatrix) with hμ
  set R := exteriorBlocks p i
  set cnt := subsystemCount p R (zeroDeformation p i) (Set.Icc a b)
  have hf : Measurable (fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) :=
    BlockBand.Angular.PairCoareaBridge.measurable_assemble p i
  have hmap : (splitLaw p i Pω).map (fun x => assemble p i x.1 x.2) = μ := hsplit
  obtain ⟨hint, hle⟩ := hcount p model R (zeroDeformation p i) measurable_const a b hab 2 (by norm_num)
  set g := BlockBand.External.PSSS.factorialCount cnt 2
  set S : Set p.SiteMatrix := {H | (2 : ℝ) ≤ g H}
  set T : Set p.SiteMatrix := {H | ¬ H.IsHermitian}
  have hT : μ T = 0 := by
    have := model.isPhysical.1
    rw [ae_iff] at this
    exact this
  have hsub : {x : SplitState p i × PairMatrix p i | 2 ≤ spectralSum x.1.1 (iccInd a b)} ⊆
      (fun x => assemble p i x.1 x.2) ⁻¹' S ∪ (fun x => assemble p i x.1 x.2) ⁻¹' T := by
    intro x hx
    by_cases hH : (assemble p i x.1 x.2).IsHermitian
    · left
      have hc := subsystemCount_eq p i _ hH a b
      rw [exteriorBlock_assemble] at hc
      have h2 : (2 : ℝ) ≤ cnt (assemble p i x.1 x.2) := by
        simp only [Set.mem_ofPred_eq] at hx
        rw [hc]; exact hx
      have h2' : 2 ≤ cnt (assemble p i x.1 x.2) := by exact_mod_cast h2
      show (2 : ℝ) ≤ (Nat.descFactorial (cnt (assemble p i x.1 x.2)) 2 : ℝ)
      have : 2 ≤ Nat.descFactorial (cnt (assemble p i x.1 x.2)) 2 := by
        rw [Nat.descFactorial_eq_div (by omega)]
        obtain ⟨m, hm⟩ : ∃ m, cnt (assemble p i x.1 x.2) = m + 2 := ⟨_, (Nat.sub_add_cancel h2').symm⟩
        rw [hm, show m + 2 - 2 = m by omega]
        rw [show (m + 2).factorial = (m + 2) * (m + 1) * m.factorial by
          rw [Nat.factorial_succ, Nat.factorial_succ]; ring]
        rw [Nat.mul_div_cancel _ (Nat.factorial_pos m)]
        nlinarith
      exact_mod_cast this
    · right
      exact hH
  have hS : μ S ≤ ENNReal.ofReal (crowdingBound p C (b - a)) := by
    have hg0 : 0 ≤ᵐ[μ] g := Filter.Eventually.of_forall fun H => by
      simp only [g, BlockBand.External.PSSS.factorialCount, Pi.zero_apply]; positivity
    have hM := mul_meas_ge_le_integral_of_nonneg hg0 hint 2
    have hbound : (C / Real.sqrt p.c * ((R.card * p.W : ℕ) : ℝ) * (b - a)) ^ 2 ≤
        (C / Real.sqrt p.c * ((p.n : ℝ) * p.W) * (b - a)) ^ 2 := by
      have hc0 : 0 ≤ C / Real.sqrt p.c := div_nonneg hC.le (Real.sqrt_nonneg _)
      have hba : 0 ≤ b - a := sub_nonneg.mpr hab
      apply pow_le_pow_left₀ (mul_nonneg (mul_nonneg hc0 (by positivity)) hba)
      apply mul_le_mul_of_nonneg_right _ hba
      apply mul_le_mul_of_nonneg_left _ hc0
      push_cast
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast exteriorBlocks_card_le p i)
        (by positivity)
    have hreal : μ.real S ≤ crowdingBound p C (b - a) := by
      unfold crowdingBound
      have := hM.trans (hle.trans hbound)
      linarith
    rw [← ofReal_measureReal (measure_ne_top μ S)]
    exact ENNReal.ofReal_le_ofReal hreal
  calc splitLaw p i Pω {x | 2 ≤ spectralSum x.1.1 (iccInd a b)}
      ≤ splitLaw p i Pω ((fun x => assemble p i x.1 x.2) ⁻¹' S) +
          splitLaw p i Pω ((fun x => assemble p i x.1 x.2) ⁻¹' T) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ μ S + μ T := by
        gcongr
        · rw [← hmap]; exact Measure.le_map_apply hf.aemeasurable S
        · rw [← hmap]; exact Measure.le_map_apply hf.aemeasurable T
    _ ≤ ENNReal.ofReal (crowdingBound p C (b - a)) := by rw [hT, add_zero]; exact hS

/-- The crowding event `{∃ E ∈ [-L, L], N_{H_R}([E - ε₀, E + ε₀]) ≥ 2}` of the split space. -/
def crowdingEvent (p : Parameters) (i : ZMod p.n) (ε₀ L : ℝ) :
    Set (SplitState p i × PairMatrix p i) :=
  {x | ∃ E : ℝ, |E| ≤ L ∧ 2 ≤ spectralSum x.1.1 (iccInd (E - ε₀) (E + ε₀))}

/-- **The cover estimate**: with the constant `C` of
`exteriorCount_two_le`, for every splitting law, `ε₀ > 0` and `L ≥ 0`,
`P{∃ E ∈ [-L, L], N_{H_R}([E - ε₀, E + ε₀]) ≥ 2} ≤ (L/ε₀ + 1) (C/√c · nW · 4ε₀)² / 2`,
by a cover of `[-L, L]` by `⌊L/ε₀⌋ + 1` intervals of length `4ε₀`. -/
theorem exteriorCrowding_le (hPBC : PhysicalBlockConditionalCount) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n)
      (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
      ∀ ε₀ : ℝ, 0 < ε₀ → ∀ L : ℝ, 0 ≤ L →
        splitLaw p i Pω (crowdingEvent p i ε₀ L) ≤
          ENNReal.ofReal ((L / ε₀ + 1) * crowdingBound p C (4 * ε₀)) := by
  obtain ⟨C, hC, h2⟩ := exteriorCount_two_le hPBC
  refine ⟨C, hC, fun p model i Pω hsplit ε₀ hε₀ L hL => ?_⟩
  set K := ⌊L / ε₀⌋₊
  let a : ℕ → ℝ := fun k => -L - ε₀ + 2 * k * ε₀
  have hsub : crowdingEvent p i ε₀ L ⊆ ⋃ k ∈ range (K + 1),
      {x : SplitState p i × PairMatrix p i |
        2 ≤ spectralSum x.1.1 (iccInd (a k) (a k + 4 * ε₀))} := by
    rintro x ⟨E, hE, hx⟩
    rw [abs_le] at hE
    set k := ⌊(E + L) / (2 * ε₀)⌋₊
    have hq0 : 0 ≤ (E + L) / (2 * ε₀) := div_nonneg (by linarith) (by positivity)
    have hk1 : (k : ℝ) ≤ (E + L) / (2 * ε₀) := Nat.floor_le hq0
    have hk2 : (E + L) / (2 * ε₀) < k + 1 := Nat.lt_floor_add_one _
    have hk1' : 2 * k * ε₀ ≤ E + L := by
      rw [le_div_iff₀ (by positivity)] at hk1; linarith
    have hk2' : E + L < 2 * (k + 1) * ε₀ := by
      rw [div_lt_iff₀ (by positivity)] at hk2; linarith
    simp only [Set.mem_iUnion, mem_range]
    refine ⟨k, ?_, ?_⟩
    · have : k ≤ K := Nat.floor_mono (by
        rw [div_le_div_iff₀ (by positivity) hε₀]; nlinarith)
      omega
    · show 2 ≤ spectralSum x.1.1 (iccInd (a k) (a k + 4 * ε₀))
      refine hx.trans (spectralSum_iccInd_mono _ ?_ ?_)
      · simp only [a]; linarith
      · simp only [a]; linarith
  have hB0 : 0 ≤ crowdingBound p C (4 * ε₀) := by unfold crowdingBound; positivity
  calc splitLaw p i Pω (crowdingEvent p i ε₀ L)
      ≤ ∑ k ∈ range (K + 1), splitLaw p i Pω {x : SplitState p i × PairMatrix p i |
          2 ≤ spectralSum x.1.1 (iccInd (a k) (a k + 4 * ε₀))} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _k ∈ range (K + 1), ENNReal.ofReal (crowdingBound p C (4 * ε₀)) := by
        gcongr with k
        have := h2 p model i Pω hsplit (a k) (a k + 4 * ε₀) (by linarith)
        rwa [show a k + 4 * ε₀ - a k = 4 * ε₀ by ring] at this
    _ = ENNReal.ofReal ((K + 1 : ℕ) * crowdingBound p C (4 * ε₀)) := by
        rw [sum_const, card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((L / ε₀ + 1) * crowdingBound p C (4 * ε₀)) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ hB0
        push_cast
        have := Nat.floor_le (div_nonneg hL hε₀.le)
        linarith

/-- Off the crowding event, at every `|E| ≤ L` the exterior has at most one eigenvalue within
`ε₀` of `E` (the hypothesis `hnear` of `isPerturbation_actual`). -/
theorem nearSet_card_le_one_of_not_mem {p : Parameters} {i : ZMod p.n} {ε₀ L : ℝ}
    {x : SplitState p i × PairMatrix p i} (hx : x ∉ crowdingEvent p i ε₀ L)
    (hH : x.1.1.IsHermitian) {E : ℝ} (hE : |E| ≤ L) :
    (BlockBand.LocalWindow.ProofCount.nearSet ε₀ hH E).card ≤ 1 := by
  by_contra hc
  push Not at hc
  apply hx
  refine ⟨E, hE, ?_⟩
  have := BlockBand.LocalWindow.ProofCount.nearSet_card_eq hH ε₀ E
  unfold iccInd
  rw [← this]
  exact_mod_cast hc

end Crowding

end BlockBand.LocalWindow.ProofCrowding
