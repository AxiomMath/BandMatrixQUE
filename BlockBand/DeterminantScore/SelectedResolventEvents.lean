module

public import BlockBand.DeterminantScore.SelectedResolventTransfer
public import BlockBand.LocalWindow.ProofNormEvent
public import BlockBand.LocalWindow.ProofCrowding
public import BlockBand.Window.Count.RefinedCountLocationTools

/-!
# Exceptional events for the selected-energy certificate

Probability bounds under the pair splitting law for the events excluded at the selected energies:
the null event (non-Hermitian blocks or a selected energy in the spectrum of `H_R`), eigenvalue
crowding at radius `W^{-(D+4)}`, and the exit of a bulk eigenvalue from its classical location.

* `measure_abs_lt_le_of_eLpNorm_le`: Markov for `|f|` without measurability.
* `splitLaw_null_le`, `splitLaw_crowding_le`, `splitLaw_rank_le`: the three event bounds.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedResolvent

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.LocalWindow BlockBand.LocalWindow.ProofCertificate
open scoped ENNReal

/-- **Markov for `|f|`** at a real moment `q > 0`: `‖f‖_q ≤ K` gives `μ{|f| > u} ≤ (K/u)^q`
(outer measure; no measurability). -/
theorem measure_abs_lt_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) {q u K : ℝ} (hq : 0 < q) (hu : 0 < u) (hK : 0 ≤ K)
    (h : eLpNorm f (ENNReal.ofReal q) μ ≤ ENNReal.ofReal K) :
    μ {x | u < |f x|} ≤ ENNReal.ofReal ((K / u) ^ q) := by
  have hq0 : ENNReal.ofReal q ≠ 0 := by simp [hq]
  have hM := mul_meas_ge_le_pow_eLpNorm' μ hq0 ENNReal.ofReal_ne_top (f := f)
    (ENNReal.ofReal u)
  rw [ENNReal.toReal_ofReal hq.le] at hM
  have hsub : {x | u < |f x|} ⊆ {x | ENNReal.ofReal u ≤ ‖f x‖ₑ} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal hx.le
  have h2 : ENNReal.ofReal u ^ q * μ {x | u < |f x|} ≤ ENNReal.ofReal K ^ q :=
    (mul_le_mul_right (measure_mono hsub) _).trans
      (hM.trans (ENNReal.rpow_le_rpow h hq.le))
  rw [ENNReal.ofReal_rpow_of_nonneg hu.le hq.le, ENNReal.ofReal_rpow_of_nonneg hK hq.le] at h2
  have hup : 0 < u ^ q := Real.rpow_pos_of_pos hu q
  rw [Real.div_rpow hK hu.le, ENNReal.ofReal_div_of_pos hup]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [hup])) (Or.inl ENNReal.ofReal_ne_top),
    mul_comm]
  exact h2

variable {p : Parameters} {i : ZMod p.n}

/-- `P(f⁻¹ S) ≤ P_phys(S)` for the assembled matrix, for every set `S`. -/
theorem splitLaw_preimage_le {model : p.GaussianRingModel} {Pω : Measure (SplitState p i)}
    (hsplit : IsPairSplitting p i model (splitS p) Pω) (S : Set p.SiteMatrix) :
    splitLaw p i Pω ((fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) ⁻¹' S) ≤
      (model.law : Measure p.SiteMatrix) S := by
  have hf : Measurable (fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) :=
    BlockBand.Angular.PairCoareaBridge.measurable_assemble p i
  have hmap : (splitLaw p i Pω).map (fun x => assemble p i x.1 x.2) =
      (model.law : Measure p.SiteMatrix) := hsplit
  rw [← hmap]
  exact Measure.le_map_apply hf.aemeasurable S

/-- The null event: `H_R` or `V` not Hermitian, or some `λ_α` an eigenvalue of `H_R`. -/
def nullEvent (p : Parameters) (i : ZMod p.n) : Set (SplitState p i × PairMatrix p i) :=
  {x | ¬ (x.1.1.IsHermitian ∧ x.1.2.2.IsHermitian) ∨
    ∃ α : Fin p.N, (x.1.1 - ((physicalOrderedEigenvalue p (assemble p i x.1 x.2) α : ℝ) : ℂ) •
      (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det = 0}

/-- **The null event has probability zero** (`CoareaContract.regular_ae`). -/
theorem splitLaw_null_le (hCo : CoareaContract) {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hsplit : IsPairSplitting p i model (splitS p) Pω) :
    splitLaw p i Pω (nullEvent p i) = 0 := by
  set N1 : Set (SplitState p i) := {om | ¬ (om.1.IsHermitian ∧ om.2.2.IsHermitian)}
  have hN1 : Pω N1 = 0 := by
    have := BlockBand.Angular.FiberAngular.ae_hermitian_of_isPairSplitting p i hsplit
    rw [ae_iff] at this
    exact this
  set S : Set p.SiteMatrix := {H | ¬ (H.IsHermitian ∧ H.charpoly.Separable ∧
    ∀ (α : Fin p.N) (j : ZMod p.n),
      (exteriorBlock p j H - ((physicalOrderedEigenvalue p H α : ℝ) : ℂ) • 1).det ≠ 0)}
  have hS : (model.law : Measure p.SiteMatrix) S = 0 := by
    have := hCo.regular_ae p model
    rw [ae_iff] at this
    exact this
  have hsub : nullEvent p i ⊆ N1 ×ˢ Set.univ ∪
      (fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) ⁻¹' S := by
    rintro x (hx | ⟨α, hα⟩)
    · exact Or.inl ⟨hx, trivial⟩
    · right
      intro h
      apply h.2.2 α i
      rw [ProofCrowding.exteriorBlock_assemble]
      exact hα
  have hprob := PhysicalColumn.isProbabilityMeasure_gue (PairSite p i) (pairTime p (splitS p))
  refine le_antisymm ((measure_mono hsub).trans ((measure_union_le _ _).trans ?_)) bot_le
  have h1 : splitLaw p i Pω (N1 ×ˢ Set.univ) = 0 := by
    unfold splitLaw; rw [Measure.prod_prod, hN1, zero_mul]
  have h2 := splitLaw_preimage_le hsplit S
  rw [hS] at h2
  rw [h1, zero_add]
  exact h2

/-- **Crowding at radius `W^{-(D+4)}`**: fixed `b, T, D ≥ 0`; then `C ≥ 0`;
under every splitting law, `P{∃ |E| ≤ 2, N_{H_R}([E - ε₀, E + ε₀]) ≥ 2} ≤ C W^{-D}`,
`ε₀ = W^{-(D+4)}`. -/
theorem splitLaw_crowding_le (hPBC : PhysicalBlockConditionalCount) (b T D : ℝ) (hb : 0 < b)
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
theorem isBulkRank_mono {p : Parameters} {ϑ ϑ' : ℝ} (h : ϑ' ≤ ϑ) {α : Fin p.N}
    (hα : IsBulkRank p ϑ α) : IsBulkRank p ϑ' α :=
  ⟨h.trans hα.1, hα.2.trans (by linarith)⟩

/-- The rank-exit event `{∃ ϑ-bulk α, κ < |λ_α - e_α|}`. -/
def rankEvent (p : Parameters) (i : ZMod p.n) (ϑ κ : ℝ) : Set (SplitState p i × PairMatrix p i) :=
  {x | ∃ α : Fin p.N, IsBulkRank p ϑ α ∧
    κ < |physicalOrderedEigenvalue p (assemble p i x.1 x.2) α - classicalLocation p α|}

/-- **Rank location pays the bulk exit** (the rank location theorem): fixed
`0 < b < 1/2`, `T`, `0 < ϑ < 1/2`, `κ > 0`, `D ≥ 0`; then `C ≥ 0`; under every splitting law,
`P{∃ ϑ-bulk α, |λ_α - e_α| > κ} ≤ C W^{-D}`. -/
theorem splitLaw_rank_le (hRank : RankLocationContract) (b T ϑ κ D : ℝ) (hb : 0 < b)
    (hb' : b < 1 / 2) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) (hκ : 0 < κ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * p.W →
      ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
        IsPairSplitting p i model (splitS p) Pω →
          splitLaw p i Pω (rankEvent p i ϑ κ) ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D)) := by
  set q : ℝ := 2 * D + 4 with hq
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  obtain ⟨Cr, hCr⟩ := hRank.location b hb hb' T ϑ hϑ hϑ' q hq1
  set Cm := max Cr 0 with hCm
  have hCm0 : 0 ≤ Cm := le_max_right _ _
  refine ⟨|T| * (Cm / κ) ^ q, by positivity, fun p hpb hn model i Pω hsplit => ?_⟩
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < p.W := by linarith
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
  set S : Set p.SiteMatrix := {H | ∃ α : Fin p.N, IsBulkRank p ϑ α ∧
    κ < |physicalOrderedEigenvalue p H α - classicalLocation p α|}
  have hpre : rankEvent p i ϑ κ = (fun x : SplitState p i × PairMatrix p i =>
      assemble p i x.1 x.2) ⁻¹' S := rfl
  rw [hpre]
  refine (splitLaw_preimage_le hsplit S).trans ?_
  set K : ℝ := Cm / ((p.n : ℝ) * Real.sqrt p.W) with hK
  have hK0 : 0 ≤ K := by positivity
  have hα : ∀ α : Fin p.N, (model.law : Measure p.SiteMatrix) {H | IsBulkRank p ϑ α ∧
      κ < |physicalOrderedEigenvalue p H α - classicalLocation p α|} ≤
      ENNReal.ofReal ((K / κ) ^ q) := by
    intro α
    by_cases hb : IsBulkRank p ϑ α
    · have h := hCr p hpb hn model MassLaw.physical α hb
      have h' : eLpNorm (fun H => physicalOrderedEigenvalue p H α - classicalLocation p α)
          (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) ≤ ENNReal.ofReal K :=
        h.trans (ENNReal.ofReal_le_ofReal (by rw [hK]; gcongr; exact le_max_left _ _))
      refine (measure_mono fun H hH => hH.2).trans ?_
      exact measure_abs_lt_le_of_eLpNorm_le _ _ hq0 hκ hK0 h'
    · calc _ ≤ (model.law : Measure p.SiteMatrix) ∅ := measure_mono fun H hH => absurd hH.1 hb
        _ = 0 := measure_empty
        _ ≤ _ := bot_le
  have hsub : S ⊆ ⋃ α : Fin p.N, {H | IsBulkRank p ϑ α ∧
      κ < |physicalOrderedEigenvalue p H α - classicalLocation p α|} := by
    rintro H ⟨α, hα⟩; exact Set.mem_iUnion.mpr ⟨α, hα⟩
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun α _ => hα α).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  -- arithmetic
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

end BlockBand.DeterminantScore.SelectedResolvent
