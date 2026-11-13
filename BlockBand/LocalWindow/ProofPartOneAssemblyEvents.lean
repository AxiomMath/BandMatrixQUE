module

public import BlockBand.LocalWindow.ProofCrowding
public import BlockBand.LocalWindow.ProofPartOneEvents
public import BlockBand.Angular.FiberAngular

/-!
# The null, crowding and rank-exit events of part (i)

Each exceptional event of part (i) of the physical local-window lemma has small probability under
the split law: the null event (non-Hermitian blocks or a pole at a selected energy) has
probability zero, and the crowding and rank-exit events are `O(W^{-D})`.

## Main results

* `splitLaw_assemble_preimage_le`: `P(assemble⁻¹ S) ≤ P_phys(S)` for every set `S`.
* `splitLaw_partOneNull_eq_zero`: the null event `partOneNullEvent` is a null set.
* `splitLaw_crowding_rpow_le`: the crowding event at radius `W^{-(D+4)}` on `[-2, 2]` has
  probability `≤ C W^{-D}`.
* `splitLaw_partOneRank_le`: the rank-exit event `partOneRankEvent` has probability
  `≤ C W^{-D}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartOne

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open scoped ENNReal

variable {p : Parameters} {i : ZMod p.n}

/-- `P(assemble⁻¹ S) ≤ P_phys(S)` for every set `S` of site matrices (outer measure). -/
theorem splitLaw_assemble_preimage_le {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hsplit : IsPairSplitting p i model (splitS p) Pω)
    (S : Set p.SiteMatrix) :
    splitLaw p i Pω ((fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) ⁻¹' S) ≤
      (model.law : Measure p.SiteMatrix) S := by
  have hf : Measurable (fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) :=
    BlockBand.Angular.PairCoareaBridge.measurable_assemble p i
  have hmap : (splitLaw p i Pω).map (fun x => assemble p i x.1 x.2) =
      (model.law : Measure p.SiteMatrix) := hsplit
  rw [← hmap]
  exact Measure.le_map_apply hf.aemeasurable S

/-- The null event of part (i): `H_R`, `V` or `G` not Hermitian, or some selected energy `λ_α`
an eigenvalue of `H_R`. -/
def partOneNullEvent (p : Parameters) (i : ZMod p.n) : Set (SplitState p i × PairMatrix p i) :=
  {x | ¬ (x.1.1.IsHermitian ∧ x.1.2.2.IsHermitian ∧ x.2.IsHermitian) ∨
    ∃ α : Fin p.N, (x.1.1 - ((physicalOrderedEigenvalue p (assemble p i x.1 x.2) α : ℝ) : ℂ) •
      (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det = 0}

/-- **The null event of part (i) has split-law probability zero**, from `CoareaContract`
(`regular_ae`), the splitting `IsPairSplitting` and the almost-sure Hermitianity of the GUE block. -/
theorem splitLaw_partOneNull_eq_zero (hCo : CoareaContract) {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hsplit : IsPairSplitting p i model (splitS p) Pω) :
    splitLaw p i Pω (partOneNullEvent p i) = 0 := by
  set N1 : Set (SplitState p i) := {om | ¬ (om.1.IsHermitian ∧ om.2.2.IsHermitian)}
  have hN1 : Pω N1 = 0 := by
    have := BlockBand.Angular.FiberAngular.ae_hermitian_of_isPairSplitting p i hsplit
    rw [ae_iff] at this
    exact this
  set N2 : Set (PairMatrix p i) := {G | ¬ G.IsHermitian}
  have hN2 : gueMeasure (PairSite p i) (pairTime p (splitS p)) N2 = 0 := by
    have := BlockBand.Angular.PairCoareaBridge.ae_gueMeasure_isHermitian (PairSite p i)
      (pairTime p (splitS p))
    rwa [ae_iff] at this
  set S : Set p.SiteMatrix := {H | ¬ (H.IsHermitian ∧ H.charpoly.Separable ∧
    ∀ (α : Fin p.N) (j : ZMod p.n),
      (exteriorBlock p j H - ((physicalOrderedEigenvalue p H α : ℝ) : ℂ) • 1).det ≠ 0)}
  have hS : (model.law : Measure p.SiteMatrix) S = 0 := by
    have := hCo.regular_ae p model
    rw [ae_iff] at this
    exact this
  have hsub : partOneNullEvent p i ⊆ (N1 ×ˢ Set.univ ∪ Set.univ ×ˢ N2) ∪
      (fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) ⁻¹' S := by
    rintro x (hx | ⟨α, hα⟩)
    · by_cases h1 : x.1.1.IsHermitian ∧ x.1.2.2.IsHermitian
      · refine Or.inl (Or.inr ⟨trivial, ?_⟩)
        intro hG
        exact hx ⟨h1.1, h1.2, hG⟩
      · exact Or.inl (Or.inl ⟨h1, trivial⟩)
    · right
      intro h
      apply h.2.2 α i
      rw [ProofCrowding.exteriorBlock_assemble]
      exact hα
  refine le_antisymm ((measure_mono hsub).trans ((measure_union_le _ _).trans ?_)) bot_le
  have h1 : splitLaw p i Pω (N1 ×ˢ Set.univ ∪ Set.univ ×ˢ N2) = 0 := by
    refine le_antisymm ((measure_union_le _ _).trans ?_) bot_le
    unfold splitLaw
    rw [Measure.prod_prod, Measure.prod_prod, hN1, hN2, zero_mul, mul_zero, add_zero]
  have h2 := splitLaw_assemble_preimage_le hsplit S
  rw [hS] at h2
  rw [h1, zero_add]
  exact h2

/-- **Crowding at radius `W^{-(D+4)}`**: for fixed `b < 1/2`, `T` and `D ≥ 0` there is `C ≥ 0` such
that for every `p` with `n ≤ TW` and under every splitting law,
`P{∃ |E| ≤ 2, N_{H_R}([E - ε₀, E + ε₀]) ≥ 2} ≤ C W^{-D}`, `ε₀ = W^{-(D+4)}`. Hypothesis:
`PhysicalBlockConditionalCount` (through `ProofCrowding.exteriorCrowding_le`). -/
theorem splitLaw_crowding_rpow_le (hPBC : PhysicalBlockConditionalCount) (b T D : ℝ)
    (hb' : b < 1 / 2) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * p.W →
      ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
        IsPairSplitting p i model (splitS p) Pω →
          splitLaw p i Pω (ProofCrowding.crowdingEvent p i ((p.W : ℝ) ^ (-(D + 4))) 2) ≤
            ENNReal.ofReal (C * (p.W : ℝ) ^ (-D)) := by
  obtain ⟨C, hC, hcr⟩ := ProofCrowding.exteriorCrowding_le hPBC
  have hc : 0 < 1 - 2 * b := by linarith
  refine ⟨24 * (C ^ 2 / (1 - 2 * b)) * T ^ 2, by positivity, fun p hpb hn model i Pω hsplit => ?_⟩
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < p.W := by linarith
  have hn0 : (0 : ℝ) ≤ p.n := by positivity
  set ε₀ := (p.W : ℝ) ^ (-(D + 4)) with hε₀
  have hε₀0 : 0 < ε₀ := Real.rpow_pos_of_pos hW0 _
  have hε₀1 : ε₀ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  refine (hcr p model i Pω hsplit ε₀ hε₀0 2 (by norm_num)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hpc : p.c = 1 - 2 * b := by unfold Parameters.c; rw [hpb]
  unfold ProofCrowding.crowdingBound
  rw [hpc]
  have hsq : Real.sqrt (1 - 2 * b) ^ 2 = 1 - 2 * b := Real.sq_sqrt hc.le
  have hsqpos : 0 < Real.sqrt (1 - 2 * b) := Real.sqrt_pos.mpr hc
  have hnW : ((p.n : ℝ) * p.W) ^ 2 ≤ T ^ 2 * (p.W : ℝ) ^ (4 : ℝ) := by
    have hT : 0 ≤ T * p.W := hn0.trans hn
    have : (p.n : ℝ) * p.W ≤ T * p.W * p.W := mul_le_mul_of_nonneg_right hn hW0.le
    have h2 := pow_le_pow_left₀ (by positivity) this 2
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have hpow : (p.W : ℝ) ^ (4 : ℝ) * ε₀ = (p.W : ℝ) ^ (-D) := by
    rw [hε₀, ← Real.rpow_add hW0]; ring_nf
  have h3 : 2 / ε₀ + 1 ≤ 3 / ε₀ := by
    rw [div_add_one hε₀0.ne', div_le_div_iff_of_pos_right hε₀0]; linarith
  calc (2 / ε₀ + 1) * ((C / Real.sqrt (1 - 2 * b) * ((p.n : ℝ) * p.W) * (4 * ε₀)) ^ 2 / 2)
      ≤ 3 / ε₀ * ((C / Real.sqrt (1 - 2 * b) * ((p.n : ℝ) * p.W) * (4 * ε₀)) ^ 2 / 2) := by
        gcongr
    _ = 24 * (C / Real.sqrt (1 - 2 * b)) ^ 2 * ((p.n : ℝ) * p.W) ^ 2 * ε₀ := by
        field_simp; ring
    _ = 24 * (C ^ 2 / (1 - 2 * b)) * ((p.n : ℝ) * p.W) ^ 2 * ε₀ := by
        rw [div_pow, hsq]
    _ ≤ 24 * (C ^ 2 / (1 - 2 * b)) * (T ^ 2 * (p.W : ℝ) ^ (4 : ℝ)) * ε₀ := by gcongr
    _ = 24 * (C ^ 2 / (1 - 2 * b)) * T ^ 2 * ((p.W : ℝ) ^ (4 : ℝ) * ε₀) := by ring
    _ = _ := by rw [hpow]

/-- `IsBulkRank` is antitone in the margin. -/
theorem isBulkRank_antitone {p : Parameters} {ϑ ϑ' : ℝ} (h : ϑ' ≤ ϑ) {α : Fin p.N}
    (hα : IsBulkRank p ϑ α) : IsBulkRank p ϑ' α :=
  ⟨h.trans hα.1, hα.2.trans (by linarith)⟩

/-- The rank-exit event `{∃ ϑ-bulk α, κ ≤ |λ_α - e_α|}`. -/
def partOneRankEvent (p : Parameters) (i : ZMod p.n) (ϑ κ : ℝ) :
    Set (SplitState p i × PairMatrix p i) :=
  {x | ∃ α : Fin p.N, IsBulkRank p ϑ α ∧
    κ ≤ |physicalOrderedEigenvalue p (assemble p i x.1 x.2) α - classicalLocation p α|}

/-- **Rank location pays the bulk exit**: for fixed `0 < b < 1/2`, `T`, `0 < ϑ < 1/2`, `κ > 0` and
`D ≥ 0` there is `C ≥ 0` such that for every `p` with `n ≤ TW` and under every splitting law,
`P{∃ ϑ-bulk α, |λ_α - e_α| ≥ κ} ≤ C W^{-D}`. Hypothesis: `RankLocationContract`
(through `splitLaw_rankLocation_le` at order `q = 2D + 4`). -/
theorem splitLaw_partOneRank_le (hRL : RankLocationContract) (b T ϑ κ D : ℝ) (hb : 0 < b)
    (hb' : b < 1 / 2) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) (hκ : 0 < κ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * p.W →
      ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
        IsPairSplitting p i model (splitS p) Pω →
          splitLaw p i Pω (partOneRankEvent p i ϑ κ) ≤
            ENNReal.ofReal (C * (p.W : ℝ) ^ (-D)) := by
  set q : ℝ := 2 * D + 4 with hq
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  obtain ⟨Cm, hCm0, hloc⟩ := splitLaw_rankLocation_le hRL b T ϑ hb hb' hϑ hϑ' q hq1
  refine ⟨|T| * (Cm / κ) ^ q, by positivity, fun p hpb hn model i Pω hsplit => ?_⟩
  refine (hloc p hpb hn model i Pω hsplit κ hκ).trans (ENNReal.ofReal_le_ofReal ?_)
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < p.W := by linarith
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
  set K : ℝ := Cm / ((p.n : ℝ) * Real.sqrt p.W) with hK
  have hsW : Real.sqrt p.W = (p.W : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hKle : K / κ ≤ Cm / κ * (p.W : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hK, Real.rpow_neg hW0.le, ← hsW]
    have hs1 : 1 ≤ Real.sqrt p.W := by rw [Real.one_le_sqrt]; exact hW1
    have hsp : 0 < Real.sqrt p.W := by linarith
    rw [div_div, div_le_iff₀ (by positivity)]
    calc Cm = Cm / κ * (Real.sqrt p.W)⁻¹ * (κ * Real.sqrt p.W) := by field_simp
      _ ≤ Cm / κ * (Real.sqrt p.W)⁻¹ * ((p.n : ℝ) * Real.sqrt p.W * κ) := by
          have : κ * Real.sqrt p.W ≤ (p.n : ℝ) * Real.sqrt p.W * κ := by
            nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hn1) hsp.le) hκ.le]
          exact mul_le_mul_of_nonneg_left this (by positivity)
  have hpowq : (K / κ) ^ q ≤ (Cm / κ) ^ q * (p.W : ℝ) ^ (-(D + 2)) := by
    calc (K / κ) ^ q ≤ (Cm / κ * (p.W : ℝ) ^ (-(1 / 2 : ℝ))) ^ q :=
          Real.rpow_le_rpow (by positivity) hKle hq0.le
      _ = (Cm / κ) ^ q * ((p.W : ℝ) ^ (-(1 / 2 : ℝ))) ^ q :=
          Real.mul_rpow (by positivity) (by positivity)
      _ = (Cm / κ) ^ q * (p.W : ℝ) ^ (-(D + 2)) := by
          rw [← Real.rpow_mul hW0.le]; congr 2; rw [hq]; ring
  have hN : ((p.N : ℕ) : ℝ) ≤ |T| * (p.W : ℝ) ^ (2 : ℝ) := by
    have : ((p.N : ℕ) : ℝ) = (p.n : ℝ) * p.W := by simp [Parameters.N]
    rw [this, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have := le_abs_self T
    nlinarith
  have hWD : (p.W : ℝ) ^ (2 : ℝ) * (p.W : ℝ) ^ (-(D + 2)) = (p.W : ℝ) ^ (-D) := by
    rw [← Real.rpow_add hW0]; ring_nf
  calc ((p.N : ℕ) : ℝ) * (K / κ) ^ q
      ≤ (|T| * (p.W : ℝ) ^ (2 : ℝ)) * ((Cm / κ) ^ q * (p.W : ℝ) ^ (-(D + 2))) :=
        mul_le_mul hN hpowq (by positivity) (by positivity)
    _ = |T| * (Cm / κ) ^ q * ((p.W : ℝ) ^ (2 : ℝ) * (p.W : ℝ) ^ (-(D + 2))) := by ring
    _ = _ := by rw [hWD]

end BlockBand.LocalWindow.ProofPartOne
