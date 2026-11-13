module

public import BlockBand.LocalWindow.ProofETH
public import BlockBand.LocalWindow.ProofPairLaw
public import BlockBand.Angular.PairCoareaBridge

/-!
# Part (ii) of the physical local window: reduction to the exterior-conditional form

The proof of (ii) works conditionally on the exterior `ω = (H_R, C, V)`: outside an exterior
event `Ω_ext` (crowding, norm, certificate, rank location; `Pω`-small), the fresh block `G` has a
`GUE`-small bad set. `PartTwoConditionalStatement` records exactly that form: an exterior event
`Ω_ext` (any set) and a measurable bad set `S` of the split space whose sections at
`ω ∉ Ω_ext` are `GUE_d(s/d)`-small, outside of which the conclusion of (ii) holds; same
quantifiers, observables and constants as `PhysicalLocalWindowPartTwoStatement`.

## Main results

* `physicalLocalWindow_partTwo_of_conditional`: `PartTwoConditionalStatement →
  PhysicalLocalWindowPartTwoStatement` (Fubini for `splitLaw = Pω ⊗ GUE_d(t)`, the conditional
  statement at failure exponent `D + 1`, then `splitPairLaw_le_of` for every pair law).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal

/-- The conclusion of part (ii) at one point `x = (ω, G)` of the split space:
at every `ϑ`-bulk selected energy `E = λ_α`, for `|λ| ≤ δ` and every unit `u` with
`A(E) u = λ u`, `|u*B u - j_B(E, λ)| ≤ C W^{-1/2+ε}`. -/
def PartTwoGood (p : Parameters) (i : ZMod p.n) (ϑ δ C ε : ℝ)
    (B : SplitState p i → ℝ → PairMatrix p i) (x : SplitState p i × PairMatrix p i) : Prop :=
  ∀ α : Fin p.N, IsBulkRank p ϑ α →
    let E := physicalOrderedEigenvalue p (assemble p i x.1 x.2) α
    let A := schurA p i x.1 x.2 E
    ∀ lam : ℝ, |lam| ≤ δ → ∀ u : PairSite p i → ℂ, l2Norm u = 1 →
      A *ᵥ u = (lam : ℂ) • u →
      |(star u ⬝ᵥ (B x.1 E *ᵥ u)).re -
          windowCenter p i (B x.1 E) (schurK0 p i x.1 E) (splitS p) lam| ≤
        C * (p.W : ℝ) ^ (-(1 / 2 : ℝ) + ε)

theorem partTwoGood_mono {p : Parameters} {i : ZMod p.n} {ϑ δ C C' ε : ℝ}
    {B : SplitState p i → ℝ → PairMatrix p i} {x : SplitState p i × PairMatrix p i}
    (hC : C ≤ C') (h : PartTwoGood p i ϑ δ C ε B x) : PartTwoGood p i ϑ δ C' ε B x := by
  intro α hα
  have hα' := h α hα
  dsimp only at hα' ⊢
  intro lam hlam u hu hAu
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  exact (hα' lam hlam u hu hAu).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hW.le _))

/-- **Part (ii) of the physical local window, conditional on the exterior.** Same
quantifiers as `PhysicalLocalWindowPartTwoStatement`; the event is given as an exterior event
`Ω_ext` with `Pω(Ω_ext) ≤ C W^{-D}` and a measurable set `S` of the split space with
`GUE_d(s/d)(S_ω) ≤ C W^{-D}` for every `ω ∉ Ω_ext`; outside both, `PartTwoGood` holds. -/
def PartTwoConditionalStatement : Prop :=
  ∀ b T ϑ : ℝ, 0 < ϑ →
    ∃ (δ : ℝ) (k : ℕ), 0 < δ ∧ δ < 1 ∧
      ∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 < D → ∀ K₀ : ℝ,
        ∃ C : ℝ, ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
          ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
            IsPairSplitting p i model (splitS p) Pω →
            ∀ B : SplitState p i → ℝ → PairMatrix p i, IsWindowObservable p i k K₀ B →
              ∃ (Ωext : Set (SplitState p i)) (S : Set (SplitState p i × PairMatrix p i)),
                MeasurableSet S ∧ Pω Ωext ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D)) ∧
                (∀ om ∉ Ωext, gueMeasure (PairSite p i) (pairTime p (splitS p))
                    (Prod.mk om ⁻¹' S) ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D))) ∧
                ∀ x : SplitState p i × PairMatrix p i, x.1 ∉ Ωext → x ∉ S →
                  PartTwoGood p i ϑ δ C ε B x

section Fubini

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Conditional Fubini: if `S` is measurable and `ν(S_x) ≤ a` for `x ∉ Ω`, then
`(μ ⊗ ν)(S ∩ {x ∉ Ω}) ≤ a μ(X)` (`Ω` arbitrary). -/
theorem prod_section_le (μ : Measure X) (ν : Measure Y) [SFinite ν] {S : Set (X × Y)}
    (hS : MeasurableSet S) {Ω : Set X} {a : ℝ≥0∞}
    (h : ∀ x ∉ Ω, ν (Prod.mk x ⁻¹' S) ≤ a) :
    μ.prod ν {z | z ∈ S ∧ z.1 ∉ Ω} ≤ a * μ Set.univ := by
  set f : X → ℝ≥0∞ := fun x => ν (Prod.mk x ⁻¹' S)
  have hf : Measurable f := measurable_measure_prodMk_left hS
  set G' : Set X := {x | f x ≤ a}
  have hG' : MeasurableSet G' := measurableSet_le hf measurable_const
  have hS' : MeasurableSet (S ∩ Prod.fst ⁻¹' G') := hS.inter (measurable_fst hG')
  calc μ.prod ν {z | z ∈ S ∧ z.1 ∉ Ω} ≤ μ.prod ν (S ∩ Prod.fst ⁻¹' G') :=
        measure_mono fun z hz => ⟨hz.1, h _ hz.2⟩
    _ = ∫⁻ x, ν (Prod.mk x ⁻¹' (S ∩ Prod.fst ⁻¹' G')) ∂μ := Measure.prod_apply hS'
    _ ≤ ∫⁻ _, a ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ G'
        · exact (measure_mono Set.inter_subset_left).trans hx
        · have : Prod.mk x ⁻¹' (S ∩ Prod.fst ⁻¹' G') = ∅ := by
            ext y; simp [hx]
          rw [this, measure_empty]; exact bot_le
    _ = a * μ Set.univ := lintegral_const a

end Fubini

variable {p : Parameters} {i : ZMod p.n}

theorem isProbabilityMeasure_gueMeasure_pair (s : ℝ) :
    IsProbabilityMeasure (gueMeasure (PairSite p i) (pairTime p s)) := by
  unfold gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
  infer_instance

/-- Under an exact pair splitting, `Pω` has total mass one. -/
theorem measure_univ_of_isPairSplitting' {model : p.GaussianRingModel} {s : ℝ}
    {Pω : Measure (SplitState p i)} (h : IsPairSplitting p i model s Pω) : Pω Set.univ = 1 := by
  have hprob := isProbabilityMeasure_gueMeasure_pair (p := p) (i := i) s
  have h1 := congrArg (fun μ : Measure p.SiteMatrix => μ Set.univ) h
  rw [Measure.map_apply (BlockBand.Angular.PairCoareaBridge.measurable_assemble p i)
    MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ, Measure.prod_prod] at h1
  simpa using h1

/-- The split law of `Ω_ext × M ∪ (S ∖ Ω_ext × M)` is at most `2a` (`a = ofReal (C W^{-D'})`). -/
theorem splitLaw_union_le {model : p.GaussianRingModel} {Pω : Measure (SplitState p i)}
    (hPω : IsPairSplitting p i model (splitS p) Pω) {Ωext : Set (SplitState p i)}
    {S : Set (SplitState p i × PairMatrix p i)} (hS : MeasurableSet S) {a : ℝ≥0∞}
    (hext : Pω Ωext ≤ a)
    (hsec : ∀ om ∉ Ωext, gueMeasure (PairSite p i) (pairTime p (splitS p)) (Prod.mk om ⁻¹' S) ≤ a) :
    splitLaw p i Pω (Prod.fst ⁻¹' Ωext ∪ {x | x ∈ S ∧ x.1 ∉ Ωext}) ≤ 2 * a := by
  have hprob := isProbabilityMeasure_gueMeasure_pair (p := p) (i := i) (splitS p)
  have hone := measure_univ_of_isPairSplitting' hPω
  refine (measure_union_le _ _).trans ?_
  have h1 : splitLaw p i Pω (Prod.fst ⁻¹' Ωext) ≤ a := by
    unfold splitLaw
    rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]
    exact hext
  have h2 : splitLaw p i Pω {x | x ∈ S ∧ x.1 ∉ Ωext} ≤ a := by
    unfold splitLaw
    refine (prod_section_le Pω _ hS hsec).trans ?_
    rw [hone, mul_one]
  calc _ ≤ a + a := add_le_add h1 h2
    _ = 2 * a := (two_mul a).symm

/-- **Reduction of part (ii) of the physical local window to its form conditional on the
exterior.** Run the conditional statement at failure exponent `D + 1`
with constant `C`; the event `Ω = Ω_ext × M ∪ (S ∖ Ω_ext × M)` has
`splitLaw(Ω) ≤ 2 max(C,0) W^{-(D+1)} ≤ 2 max(C,0) W^{-D}` (Fubini) and
`splitPairLaw_α(Ω) ≤ T max(C,0) W^{-D}` (`splitPairLaw_le_of`); the conclusion holds off `Ω`. -/
theorem physicalLocalWindow_partTwo_of_conditional (h : PartTwoConditionalStatement) :
    PhysicalLocalWindowPartTwoStatement := by
  intro b T ϑ hϑ
  obtain ⟨δ, k, hδ, hδ1, hcond⟩ := h b T ϑ hϑ
  refine ⟨δ, k, hδ, hδ1, fun ε hε D hD K₀ => ?_⟩
  obtain ⟨C, hC⟩ := hcond ε hε (D + 1) (by linarith) K₀
  set C₀ := max C 0 with hC₀
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  refine ⟨max C (max (2 * C₀) (T * (2 * C₀) / 2)), fun p hpb hn model i Pω hPω B hB => ?_⟩
  obtain ⟨Ωext, S, hS, hext, hsec, hgood⟩ := hC p hpb hn model i Pω hPω B hB
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  set a := ENNReal.ofReal (C₀ * (p.W : ℝ) ^ (-(D + 1)))
  have hext' : Pω Ωext ≤ a :=
    hext.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hW.le _)))
  have hsec' : ∀ om ∉ Ωext, gueMeasure (PairSite p i) (pairTime p (splitS p))
      (Prod.mk om ⁻¹' S) ≤ a := fun om hom =>
    (hsec om hom).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hW.le _)))
  set Ω := Prod.fst ⁻¹' Ωext ∪ {x : SplitState p i × PairMatrix p i | x ∈ S ∧ x.1 ∉ Ωext}
  have hΩ : splitLaw p i Pω Ω ≤ ENNReal.ofReal (2 * C₀ * (p.W : ℝ) ^ (-(D + 1))) := by
    refine (splitLaw_union_le hPω hS hext' hsec').trans (le_of_eq ?_)
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
      mul_assoc]
  have hpow : (p.W : ℝ) ^ (-(D + 1)) ≤ (p.W : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  refine ⟨Ω, ?_, fun α => ?_, fun x hx => ?_⟩
  · refine hΩ.trans (ENNReal.ofReal_le_ofReal ?_)
    calc 2 * C₀ * (p.W : ℝ) ^ (-(D + 1)) ≤ 2 * C₀ * (p.W : ℝ) ^ (-D) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
          ((le_max_left _ _).trans (le_max_right _ _)) (Real.rpow_nonneg hW.le _)
  · refine (splitPairLaw_le_of hPω α (by positivity) hn hΩ).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _))
      (Real.rpow_nonneg hW.le _)
  · have hx1 : x.1 ∉ Ωext := fun h' => hx (Or.inl h')
    have hx2 : x ∉ S := fun h' => hx (Or.inr ⟨h', hx1⟩)
    intro α hα
    exact partTwoGood_mono (le_max_left _ _) (hgood x hx1 hx2) α hα

end BlockBand.LocalWindow.ProofPartTwo
