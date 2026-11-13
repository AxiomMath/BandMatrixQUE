module

public import BlockBand.Angular.AssemblyBounds

/-!
# Excluded events under the pair law

* `extendedPairMeasure_preimage_le`: an event of `H` has the same pair-law probability on any
  extension as under `physicalPairMeasure` (inequality form, no measurability of the event).
* `physicalPairWeight_le`: `dP♯/dP = (n/2)(p_i + p_{i+1}) ≤ n/2` almost surely.
* `extendedPairMeasure_gaussian_le`: for the splitting Gaussian `G_e`,
  `P♯(G_e ∈ B) ≤ (n/2) GUE_{2W}(s/2W)(B)`.
* `exteriorBlock_sub_embedPair`, `couplingBlock_sub_embedPair`, `pairBlock_sub_embedPair`:
  removing `G_e` changes only the pair block.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Assembly

open MeasureTheory ProbabilityTheory BlockBand.Model.Construction
open BlockBand.Internal.Contracts.QUE BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.QUE.Fourier
open scoped ENNReal NNReal

variable (p : Parameters) (i : ZMod p.n)

theorem self_ne_add_one' : i ≠ i + 1 := by
  intro h
  have h1 : ((1 : ℕ) : ZMod p.n) = 0 := by
    rw [Nat.cast_one]
    have := congrArg (fun x => x - i) h
    simpa using this.symm
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_one] at h1
  have := p.n_ge_four
  omega

theorem exteriorBlock_sub_embedPair (H : p.SiteMatrix) (G : PairMatrix p i) :
    exteriorBlock p i (H - embedPair p i G) = exteriorBlock p i H := by
  ext x y
  have hx := x.2
  simp [exteriorBlock, embedPair, hx]

theorem couplingBlock_sub_embedPair (H : p.SiteMatrix) (G : PairMatrix p i) :
    couplingBlock p i (H - embedPair p i G) = couplingBlock p i H := by
  ext x y
  have hx := x.2
  simp [couplingBlock, embedPair, hx]

theorem pairBlock_sub_embedPair (H : p.SiteMatrix) (G : PairMatrix p i) :
    pairBlock p i (H - embedPair p i G) = pairBlock p i H - G := by
  ext x y
  simp [pairBlock, embedPair, x.2, y.2]

variable {p i}

/-- Events of `H` have the same pair-law probability on every extension. -/
theorem extendedPairMeasure_preimage_le {model : p.GaussianRingModel} (α : Fin p.N)
    (X : PairExtension p model) (S : Set p.SiteMatrix) :
    extendedPairMeasure p α i X.P X.Hm (X.Hm ⁻¹' S) ≤ physicalPairMeasure p model α i S := by
  set T := toMeasurable (physicalPairMeasure p model α i) S
  have hT : MeasurableSet T := measurableSet_toMeasurable _ S
  calc extendedPairMeasure p α i X.P X.Hm (X.Hm ⁻¹' S)
      ≤ extendedPairMeasure p α i X.P X.Hm (X.Hm ⁻¹' T) :=
        measure_mono (Set.preimage_mono (subset_toMeasurable _ S))
    _ = physicalPairMeasure p model α i T := by
        unfold extendedPairMeasure physicalPairMeasure
        rw [withDensity_apply _ (X.measurable_Hm hT), withDensity_apply _ hT, ← X.map_eq,
          Measure.restrict_map X.measurable_Hm hT,
          lintegral_map (measurable_physicalPairWeight p α i).coe_nnreal_ennreal X.measurable_Hm]
    _ = physicalPairMeasure p model α i S := measure_toMeasurable S

/-- `(n/2)(p_i + p_{i+1}) ≤ n/2` whenever the eigenvector has unit mass. -/
theorem physicalPairWeight_le (α : Fin p.N) (H : p.SiteMatrix)
    (hH : (∑ x, ‖physicalOrderedEigenvector p H α x‖ ^ 2) = 1) :
    (physicalPairWeight p α i H : ℝ) ≤ (p.n : ℝ) / 2 := by
  change (p.n : ℝ) / 2 * (physicalOrderedBlockMass p H α i +
    physicalOrderedBlockMass p H α (i + 1)) ≤ (p.n : ℝ) / 2
  have hsum : (∑ k : ZMod p.n, physicalOrderedBlockMass p H α k) = 1 := by
    unfold physicalOrderedBlockMass
    rw [BlockBand.QUE.PhysicalAngularReduction.sum_blocks p (fun x => ‖physicalOrderedEigenvector p H α x‖ ^ 2)]
    exact hH
  have hpair : physicalOrderedBlockMass p H α i + physicalOrderedBlockMass p H α (i + 1) ≤
      ∑ k : ZMod p.n, physicalOrderedBlockMass p H α k := by
    rw [← Finset.sum_pair (self_ne_add_one' p i)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun k _ _ => physicalOrderedBlockMass_nonneg p H α k
  have hn : (0 : ℝ) ≤ (p.n : ℝ) / 2 := by positivity
  nlinarith

open BlockBand.QUE.PhysicalAngularReduction in
/-- **`dP♯ ≤ (n/2) dP` for the splitting Gaussian**: `P♯(G_e ∈ B) ≤ (n/2) GUE(B)`. -/
theorem extendedPairMeasure_gaussian_le {model : p.GaussianRingModel} (α : Fin p.N)
    (X : PairExtension p model) (G : X.Ω → PairMatrix p i) (hG : IsCenterSplitting X G)
    {B : Set (PairMatrix p i)} (hB : MeasurableSet B) :
    extendedPairMeasure p α i X.P X.Hm (G ⁻¹' B) ≤
      ENNReal.ofReal ((p.n : ℝ) / 2) * gueMeasure (PairSite p i) (pairTime p (splitS p)) B := by
  obtain ⟨hGm, hlaw, -⟩ := hG
  have hA : MeasurableSet (G ⁻¹' B) := hGm hB
  have hmass : ∀ᵐ ω ∂X.P, (∑ x, ‖physicalOrderedEigenvector p (X.Hm ω) α x‖ ^ 2) = 1 := by
    have h := physicalOrderedEigenvector_totalMass_ae p model
    rw [← X.map_eq] at h
    filter_upwards [ae_of_ae_map X.measurable_Hm.aemeasurable h] with ω hω
    exact hω α
  unfold extendedPairMeasure
  rw [withDensity_apply _ hA, ← hlaw.map_eq, Measure.map_apply hGm hB, ← setLIntegral_const]
  refine setLIntegral_mono_ae measurable_const.aemeasurable ?_
  filter_upwards [hmass] with ω hω _
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (physicalPairWeight_le α (X.Hm ω) hω)

end BlockBand.Angular.Assembly
