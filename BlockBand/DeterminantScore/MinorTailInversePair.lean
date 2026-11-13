module

public import BlockBand.DeterminantScore.MinorTail
public import BlockBand.LocalWindow.Statements

/-!
# Calculus of the pair-law expectation `pairExpect`

Elementary rules for the nested coarea integral `pairExpect` (`E♯_{α,S}` in coarea coordinates),
used to combine the good-event, bad-event and local-window estimates of the physical minor tail.
The only hypothesis is `CoareaContract`.

* `pairExpect_const_mul`: finite constants factor out (no measurability needed);
* `pairExpect_mono_ae`: monotonicity on the support of the pair law (Hermitian blocks, unit `v`,
  nonpole energy, almost every `G'`, nonzero sector weight);
* `pairExpect_add_le`: a summand with a fixed-`θ` bound `B · Σ_{ℓ=α-1}^{α+1} 𝔷_ℓ(θ)` costs `3B`
  (through `PhysicalColumn.outerInt_sector_le_one`); the other summand only needs to be measurable
  in `G'` at fixed `θ`;
* `pairExpect_add_le_of_measurable`: subadditivity when one summand is jointly measurable;
* `pairExpect_one_le`: the pair law has mass at most one (`CoareaContract.pairLaw_measure`);
* `pairExpect_indicator_eq`: for a measurable event `Ω` of the split space `(ω, G)`, the pair-law
  expectation of `1_Ω(ω, G)` with `G = reconstructedGaussian` is `splitPairLaw Ω`
  (`CoareaContract.pairLaw_formula`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.MinorTailInverse

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Angular.FiberAngular
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.DeterminantScore.PhysicalColumn BlockBand.DeterminantScore.MinorTail
open scoped NNReal ENNReal

variable {p : Parameters} {i : ZMod p.n}

theorem measurable_sectorWeight (α : Fin p.N) {U : FrameMap p i} (hU : Measurable U) :
    Measurable fun z : OuterData p i × FrameMatrix p => ENNReal.ofReal (sectorWeight α U z.1 z.2) :=
  measurable_secInt hU α.val

theorem measurable_sectorWeight_G (α : Fin p.N) {U : FrameMap p i} (hU : Measurable U)
    (θ : OuterData p i) :
    Measurable fun G' : FrameMatrix p => ENNReal.ofReal (sectorWeight α U θ G') := by
  have h : Measurable ((fun z : OuterData p i × FrameMatrix p =>
      ENNReal.ofReal (sectorWeight α U z.1 z.2)) ∘ Prod.mk θ) :=
    (measurable_sectorWeight α hU).comp measurable_prodMk_left
  exact h

theorem l2Norm_of_normSqSum {v : PairSite p i → ℂ}
    (hv : BlockBand.Angular.ProjectiveStein.normSqSum v = 1) : l2Norm v = 1 := by
  unfold l2Norm
  rw [show (∑ k, ‖v k‖ ^ 2) = BlockBand.Angular.ProjectiveStein.normSqSum v from rfl, hv,
    Real.sqrt_one]

/-- Finite constants factor out of `pairExpect`. -/
theorem pairExpect_const_mul (α : Fin p.N) (s : ℝ) (U : FrameMap p i)
    (Pω : Measure (SplitState p i)) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (Ψ : OuterData p i → FrameMatrix p → ℝ≥0∞) :
    pairExpect α s U Pω (fun θ G' => c * Ψ θ G') = c * pairExpect α s U Pω Ψ := by
  unfold pairExpect
  rw [← lintegral_const_mul' _ _ hc]; refine lintegral_congr fun om => ?_
  rw [← lintegral_const_mul' _ _ hc]; refine lintegral_congr fun E => ?_
  rw [← lintegral_const_mul' _ _ hc]; refine lintegral_congr fun v => ?_
  rw [← lintegral_const_mul' _ _ hc]; refine lintegral_congr fun G' => ?_
  ring

/-- **Monotonicity on the support of the pair law.** -/
theorem pairExpect_mono_ae {model : p.GaussianRingModel} {s : ℝ} {Pω : Measure (SplitState p i)}
    (hPω : IsPairSplitting p i model s Pω) (α : Fin p.N) (U : FrameMap p i)
    {Ψ Φ : OuterData p i → FrameMatrix p → ℝ≥0∞}
    (h : ∀ θ : OuterData p i, θ.1.1.IsHermitian → θ.1.2.2.IsHermitian → l2Norm θ.2.2 = 1 →
      (θ.1.1 - (θ.2.1 : ℂ) • 1).det ≠ 0 →
      ∀ᵐ G' ∂gueMeasure (FrameIndex p) (pairTime p s),
        sectorWeight α U θ G' ≠ 0 → Ψ θ G' ≤ Φ θ G') :
    pairExpect α s U Pω Ψ ≤ pairExpect α s U Pω Φ := by
  unfold pairExpect
  refine lintegral_mono_ae ?_
  filter_upwards [ae_hermitian_of_isPairSplitting p i hPω] with om hom
  refine lintegral_mono_ae ?_
  filter_upwards [ae_det_sub_smul_ne_zero om.1] with E hE
  refine lintegral_mono_ae ?_
  filter_upwards [BlockBand.Angular.ProjectiveStein.ae_projectiveHaar_unit
    (ι := PairSite p i)] with v hv
  refine lintegral_mono_ae ?_
  filter_upwards [h (om, E, v) hom.1 hom.2 (l2Norm_of_normSqSum hv) hE] with G' hG'
  by_cases hsw : sectorWeight α U (om, E, v) G' = 0
  · simp [hsw]
  · gcongr
    exact hG' hsw

/-- The outer integral of `B` times the three neighbouring restored sector terms is at most
`3B` (each restored pair law has mass at most one). -/
theorem outerInt_three_le (hC : CoareaContract) {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hPω : IsPairSplitting p i model (splitS p) Pω)
    {U : FrameMap p i} (hU : IsPairFrame p i U) (α : Fin p.N) (B : ℝ≥0∞) :
    outerInt Pω (fun θ => B * (sectorTerm (splitS p) U (α.val - 1) θ +
      sectorTerm (splitS p) U α.val θ + sectorTerm (splitS p) U (α.val + 1) θ)) ≤ 3 * B := by
  set s := splitS p
  have hm := fun ℓ => measurable_sectorTerm s hU.1 ℓ
  have h1 := outerInt_sector_le_one hC hPω hU (α.val - 1)
  have h2 := outerInt_sector_le_one hC hPω hU α.val
  have h3 := outerInt_sector_le_one hC hPω hU (α.val + 1)
  calc _ = B * (outerInt Pω (sectorTerm s U (α.val - 1)) + outerInt Pω (sectorTerm s U α.val) +
          outerInt Pω (sectorTerm s U (α.val + 1))) := by
        rw [outerInt_const_mul Pω B (f := fun θ => sectorTerm s U (α.val - 1) θ +
            sectorTerm s U α.val θ + sectorTerm s U (α.val + 1) θ) (((hm _).add (hm _)).add (hm _)),
          outerInt_add Pω (sectorTerm s U (α.val + 1)) (f := fun θ => sectorTerm s U (α.val - 1) θ +
            sectorTerm s U α.val θ) ((hm _).add (hm _)),
          outerInt_add Pω (sectorTerm s U α.val) (hm _)]
    _ ≤ B * (1 + 1 + 1) := by gcongr
    _ = 3 * B := by rw [mul_comm]; norm_num

/-- **Fixed-`θ` bound for one summand.** If `Ψ₁` has the fixed-`θ` bound of
`PhysicalColumn.pairExpect_le` and `Ψ₂` is measurable in `G'` at every `θ`, then
`E♯[Ψ₁ + Ψ₂] ≤ 3B + E♯[Ψ₂]`. -/
theorem pairExpect_add_le (hC : CoareaContract) {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hPω : IsPairSplitting p i model (splitS p) Pω)
    {U : FrameMap p i} (hU : IsPairFrame p i U) (α : Fin p.N)
    (Ψ₁ Ψ₂ : OuterData p i → FrameMatrix p → ℝ≥0∞) (B : ℝ≥0∞)
    (hΨ₂ : ∀ θ, Measurable (Ψ₂ θ))
    (h : ∀ θ : OuterData p i, θ.1.1.IsHermitian → θ.1.2.2.IsHermitian → l2Norm θ.2.2 = 1 →
      (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') * Ψ₁ θ G'
          ∂gueMeasure (FrameIndex p) (pairTime p (splitS p))) ≤
        B * (zNat (splitS p) U (α.val - 1) θ + zNat (splitS p) U α.val θ +
          zNat (splitS p) U (α.val + 1) θ)) :
    pairExpect α (splitS p) U Pω (fun θ G' => Ψ₁ θ G' + Ψ₂ θ G') ≤
      3 * B + pairExpect α (splitS p) U Pω Ψ₂ := by
  set s := splitS p
  have hm := fun ℓ => measurable_sectorTerm s hU.1 ℓ
  set f : OuterData p i → ℝ≥0∞ := fun θ => B * (sectorTerm s U (α.val - 1) θ +
    sectorTerm s U α.val θ + sectorTerm s U (α.val + 1) θ) with hfdef
  have hf : Measurable f := (((hm _).add (hm _)).add (hm _)).const_mul B
  set g : OuterData p i → ℝ≥0∞ := fun θ => ∫⁻ G',
    ENNReal.ofReal (angularWeight p i s θ.1 θ.2.1 θ.2.2) * ENNReal.ofReal (sectorWeight α U θ G') *
      Ψ₂ θ G' ∂gueMeasure (FrameIndex p) (pairTime p s) with hgdef
  have step : pairExpect α s U Pω (fun θ G' => Ψ₁ θ G' + Ψ₂ θ G') ≤
      outerInt Pω (fun θ => f θ + g θ) := by
    unfold pairExpect outerInt
    refine lintegral_mono_ae ?_
    filter_upwards [ae_hermitian_of_isPairSplitting p i hPω] with om hom
    refine lintegral_mono fun E => ?_
    refine lintegral_mono_ae ?_
    filter_upwards [BlockBand.Angular.ProjectiveStein.ae_projectiveHaar_unit
      (ι := PairSite p i)] with v hv
    have hl2 := l2Norm_of_normSqSum hv
    have hmeas : Measurable fun G' : FrameMatrix p =>
        ENNReal.ofReal (angularWeight p i s om E v) *
          ENNReal.ofReal (sectorWeight α U (om, E, v) G') * Ψ₂ (om, E, v) G' :=
      (measurable_const.mul (measurable_sectorWeight_G α hU.1 _)).mul (hΨ₂ _)
    calc (∫⁻ G', ENNReal.ofReal (angularWeight p i s om E v) *
          ENNReal.ofReal (sectorWeight α U (om, E, v) G') *
            (Ψ₁ (om, E, v) G' + Ψ₂ (om, E, v) G') ∂gueMeasure (FrameIndex p) (pairTime p s))
        = ∫⁻ G', (ENNReal.ofReal (angularWeight p i s om E v) *
            (ENNReal.ofReal (sectorWeight α U (om, E, v) G') * Ψ₁ (om, E, v) G') +
          ENNReal.ofReal (angularWeight p i s om E v) *
            ENNReal.ofReal (sectorWeight α U (om, E, v) G') * Ψ₂ (om, E, v) G')
            ∂gueMeasure (FrameIndex p) (pairTime p s) :=
          lintegral_congr fun G' => by ring
      _ = ENNReal.ofReal (angularWeight p i s om E v) *
            (∫⁻ G', ENNReal.ofReal (sectorWeight α U (om, E, v) G') * Ψ₁ (om, E, v) G'
              ∂gueMeasure (FrameIndex p) (pairTime p s)) + g (om, E, v) := by
          rw [lintegral_add_right _ hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (angularWeight p i s om E v) *
            (B * (zNat s U (α.val - 1) (om, E, v) + zNat s U α.val (om, E, v) +
              zNat s U (α.val + 1) (om, E, v))) + g (om, E, v) := by
          gcongr
          exact h (om, E, v) hom.1 hom.2 hl2
      _ = f (om, E, v) + g (om, E, v) := by
          simp only [hfdef, sectorTerm]; ring
  calc _ ≤ _ := step
    _ = outerInt Pω f + outerInt Pω g := outerInt_add Pω g hf
    _ ≤ 3 * B + pairExpect α s U Pω Ψ₂ := by
        gcongr
        · exact outerInt_three_le hC hPω hU α B
        · exact le_of_eq rfl

/-- **Subadditivity** when the second summand is jointly measurable. -/
theorem pairExpect_add_le_of_measurable (α : Fin p.N) (s : ℝ) {U : FrameMap p i}
    (hU : Measurable U) (Pω : Measure (SplitState p i))
    (Ψa Ψb : OuterData p i → FrameMatrix p → ℝ≥0∞)
    (hb : Measurable fun z : OuterData p i × FrameMatrix p => Ψb z.1 z.2) :
    pairExpect α s U Pω (fun θ G' => Ψa θ G' + Ψb θ G') ≤
      pairExpect α s U Pω Ψa + pairExpect α s U Pω Ψb := by
  have := isProbabilityMeasure_gue (FrameIndex p) (pairTime p s)
  have hj : Measurable fun z : OuterData p i × FrameMatrix p =>
      ENNReal.ofReal (angularWeight p i s z.1.1 z.1.2.1 z.1.2.2) *
        ENNReal.ofReal (sectorWeight α U z.1 z.2) * Ψb z.1 z.2 :=
    ((ENNReal.measurable_ofReal.comp ((measurable_angularWeight s).comp measurable_fst)).mul
      (measurable_sectorWeight α hU)).mul hb
  set gb : OuterData p i → ℝ≥0∞ := fun θ => ∫⁻ G',
    ENNReal.ofReal (angularWeight p i s θ.1 θ.2.1 θ.2.2) * ENNReal.ofReal (sectorWeight α U θ G') *
      Ψb θ G' ∂gueMeasure (FrameIndex p) (pairTime p s) with hgb
  set ga : OuterData p i → ℝ≥0∞ := fun θ => ∫⁻ G',
    ENNReal.ofReal (angularWeight p i s θ.1 θ.2.1 θ.2.2) * ENNReal.ofReal (sectorWeight α U θ G') *
      Ψa θ G' ∂gueMeasure (FrameIndex p) (pairTime p s) with hga
  have hmb : Measurable gb := hj.lintegral_prod_right'
  have e : pairExpect α s U Pω (fun θ G' => Ψa θ G' + Ψb θ G') =
      outerInt Pω (fun θ => gb θ + ga θ) := by
    unfold pairExpect outerInt
    refine lintegral_congr fun om => lintegral_congr fun E => lintegral_congr fun v => ?_
    have hjG : Measurable ((fun z : OuterData p i × FrameMatrix p =>
        ENNReal.ofReal (angularWeight p i s z.1.1 z.1.2.1 z.1.2.2) *
          ENNReal.ofReal (sectorWeight α U z.1 z.2) * Ψb z.1 z.2) ∘ Prod.mk (om, E, v)) :=
      hj.comp measurable_prodMk_left
    have hjG' : Measurable fun G' : FrameMatrix p =>
        ENNReal.ofReal (angularWeight p i s om E v) *
          ENNReal.ofReal (sectorWeight α U (om, E, v) G') * Ψb (om, E, v) G' := hjG
    rw [hgb, hga]
    simp only
    rw [← lintegral_add_left hjG']
    exact lintegral_congr fun G' => by ring
  rw [e, outerInt_add Pω ga hmb, add_comm]
  exact le_rfl

/-- The pair law has mass at most one. -/
theorem pairExpect_one_le (hC : CoareaContract) {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hPω : IsPairSplitting p i model (splitS p) Pω)
    {U : FrameMap p i} (hU : IsPairFrame p i U) (α : Fin p.N) :
    pairExpect α (splitS p) U Pω (fun _ _ => 1) ≤ 1 := by
  have h2 := hC.pairLaw_measure p model α i (splitS p)
    (BlockBand.Angular.PairCoareaBridge.splitS_pos p) le_rfl Pω hPω U hU (fun _ => 1)
    measurable_const
  have hprob := hC.pairLaw_probability p model α i
  rw [pairExpect_one_eq, ← h2, lintegral_const, measure_univ, one_mul]

/-- Observables of the split state through the reconstructed Gaussian: `pairExpect` is the
coarea right side with crossing factor `n/2`. -/
theorem pairExpect_reconstructed (α : Fin p.N) (s : ℝ) (U : FrameMap p i)
    (Pω : Measure (SplitState p i)) (Φ : SplitState p i → PairMatrix p i → ℝ≥0∞) :
    pairExpect α s U Pω (fun θ G' => Φ θ.1 (reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G')) =
      coareaRHS p α i s Pω U (fun _ _ _ => (p.n : ℝ) / 2) Φ := by
  unfold pairExpect coareaRHS coareaFiber
  refine lintegral_congr fun om => lintegral_congr fun E => lintegral_congr fun v =>
    lintegral_congr fun G' => ?_
  have ha := angularWeight_nonneg p i s om E v
  by_cases h : negativeCount (frameM p i U om E v G') + negativeCount (om.1 - (E : ℂ) • 1) = α.val
  · have h' : negativeCount (outerM U (om, E, v) G') +
        negativeCount ((om, E, v).1.1 - ((om, E, v).2.1 : ℂ) • 1) = α.val := h
    have hsw : sectorWeight α U (om, E, v) G' = Complex.normSq (frameM p i U om E v G').det := by
      simp only [sectorWeight, h', ↓reduceIte, mul_one]; rfl
    rw [hsw, ← ENNReal.ofReal_mul ha]
    simp only [h, ↓reduceIte, mul_one]
    rfl
  · have h' : ¬ negativeCount (outerM U (om, E, v) G') +
        negativeCount ((om, E, v).1.1 - ((om, E, v).2.1 : ℂ) • 1) = α.val := h
    have hsw : sectorWeight α U (om, E, v) G' = 0 := by
      simp only [sectorWeight, h', ↓reduceIte, mul_zero]
    simp only [hsw, h, ↓reduceIte, ENNReal.ofReal_zero, mul_zero, zero_mul]

/-- **Transfer of a split-space event.** For a measurable event `Ω` of `(ω, G)`, the pair-law
expectation of `1_Ω(ω, G)`, `G` the reconstructed Gaussian, is its `splitPairLaw` measure. -/
theorem pairExpect_indicator_eq (hC : CoareaContract) {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hPω : IsPairSplitting p i model (splitS p) Pω)
    {U : FrameMap p i} (hU : IsPairFrame p i U) (α : Fin p.N)
    {Ω : Set (SplitState p i × PairMatrix p i)} (hΩ : MeasurableSet Ω) :
    pairExpect α (splitS p) U Pω (fun θ G' =>
        Ω.indicator 1 (θ.1, reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G')) =
      BlockBand.LocalWindow.splitPairLaw p i α Pω Ω := by
  have hmeas : Measurable (Function.uncurry fun (om : SplitState p i) (G : PairMatrix p i) =>
      Ω.indicator (1 : SplitState p i × PairMatrix p i → ℝ≥0∞) (om, G)) :=
    measurable_one.indicator hΩ
  rw [pairExpect_reconstructed α (splitS p) U Pω (fun om G => Ω.indicator 1 (om, G)),
    ← hC.pairLaw_formula p model α i (splitS p) (BlockBand.Angular.PairCoareaBridge.splitS_pos p)
      le_rfl Pω hPω U hU _ hmeas]
  unfold BlockBand.LocalWindow.splitPairLaw BlockBand.LocalWindow.splitLaw
  rw [withDensity_apply _ hΩ, ← lintegral_indicator hΩ]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ Ω <;> simp [hx]

end BlockBand.DeterminantScore.MinorTailInverse
