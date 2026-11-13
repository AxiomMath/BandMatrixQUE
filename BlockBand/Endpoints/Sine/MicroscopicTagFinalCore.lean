module

public import BlockBand.Endpoints.Sine.MicroscopicTagPortAssembly
public import BlockBand.Endpoints.Sine.MicroscopicTagComparison

/-!
# Steps 1–4 of the microscopic tag comparison for a window and a nonnegative Lipschitz test

The comparison is proved in four steps: (1) cyclic invariance reduces to block `0` in Palm form;
(2) the one-block Palm reduction on the regular event; (3) the multi-tag covariance change, after
truncating the number of tags at `K`; (4) the common-port comparison under the prior.

* `mts_prior_gauss_lead`: under the prior, the Gaussian field `Γ₀` tag test is within
  `2 Lip(Φ) · (Gaussian three-tag test) + ε` of the matched-lead side `leadTagSide` (Step 3
  identification through `LeadFieldIdentificationContract`, the deletion identity, and Step 4,
  `mts_commonPort_step`, integrated over `u`).
* `mts_core`: the conclusion of `MicroscopicTagLeadComparison` for a window `w` (`IsWindow`) and a
  nonnegative bounded Lipschitz `Φ`. The order of the constants is `ε → δ = ε/(20(L+1)) → K`
  (the K trick) `→` the widths of the window/prior transfer (`OneBlockNormalizerContract.tv`), of
  the Palm–Gaussian comparison and of the common-port step, then eventually in `j` (the width
  `W_j → ∞`, `n_j ≤ (τ+1)W_j`, and `VanishingBlockAtom` for the block-`0` atom).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.RingSymmetry
open scoped ENNReal NNReal ComplexOrder BoundedContinuousFunction

theorem mts_abs_mainClockTest_le (p : Parameters) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    (x : ZMod p.n → ℝ) : |mts_mainClockTest p Φ x| ≤ ‖Φ‖ := by
  unfold mts_mainClockTest
  have hn' : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  rw [abs_mul, abs_of_pos (inv_pos.2 hn')]
  have h2 : ∑ j : ZMod p.n, |Φ (Set.projIci 0 ((p.n : ℝ) * x j / ∑ i, x i))| ≤
      ∑ _j : ZMod p.n, ‖Φ‖ := Finset.sum_le_sum fun _ _ => by
    rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at h2
  calc (p.n : ℝ)⁻¹ * |_| ≤ (p.n : ℝ)⁻¹ * (p.n * ‖Φ‖) :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans h2)
          (inv_nonneg.2 hn'.le)
    _ = ‖Φ‖ := by field_simp

theorem mts_tent_le (y : Set.Ici (0 : ℝ)) : mts_tent y ≤ 3 / 2 := by
  rw [mts_tent_apply]
  refine max_le (by norm_num) ?_
  rcases le_total (y : ℝ) (3 / 2) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

theorem mts_abs_atomClockTest_le (p : Parameters) (k : ZMod p.n) (x : ZMod p.n → ℝ) :
    |mts_atomClockTest p k x| ≤ 2 := by
  unfold mts_atomClockTest
  have h0 : ∀ y, 0 ≤ mts_tent y := mts_tent_nonneg
  rw [abs_of_nonneg (mul_nonneg (by norm_num) (add_nonneg (add_nonneg (h0 _) (h0 _)) (h0 _)))]
  have := mts_tent_le (Set.projIci 0 (3 * (1 / 2 * x k) / ∑ i, x i))
  have := mts_tent_le (Set.projIci 0 (3 * (∑ i, x i - x k) / ∑ i, x i))
  linarith

theorem mts_isProbabilityMeasure_portLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (mts_portLaw W b) := by
  have := passDeriv_isProbabilityMeasure_growthPathLaw W b
  have := mts_isProbabilityMeasure_commonPortProbeLaw W b
  unfold mts_portLaw; infer_instance

/-- **Gaussian field `Γ₀` → matched-lead side, under the prior.** Hypotheses:
`LeadFieldIdentificationContract`, `UniformClockTagsCommonPortContract` and
`MatchedTracesContract`. Fixed first `b`, bulk `E`, `T`, a window `w`, a bounded Lipschitz `Φ`
and `ε > 0`; then for `W ≥ W₀` and `n ≤ TW`, every model, one-block splitting law of block `0`
and reindexing: `|∫ E_g test_main(M₀g) d𝔭_W - leadTagSide| ≤ 2 Lip(Φ) ∫ E_g test_atom(M₀g) d𝔭_W + ε`. -/
theorem mts_prior_gauss_lead (hL : LeadFieldIdentificationContract)
    (hCP : UniformClockTagsCommonPortContract) (hMT : MatchedTracesContract) {b : ℝ}
    (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) (T : ℝ) {w : ℝ → ℝ}
    (hw : IsWindow w) {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ} {L : NNReal} (hLip : LipschitzWith L Φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (Pω : Measure (BlockState p 0)),
      IsBlockSplitting p 0 model Pω → ∀ (σ : BlockSite p 0 ≃ Fin (Fintype.card (BlockSite p 0))),
      |(∫ x, mts_gaussTag p 0 σ p.n (mts_mainTags p 0 σ) Φ (mts_priorPoint p 0 E x)
            ∂priorWindowMeasure Pω w) - leadTagSide p E w Φ| ≤
        2 * L * (∫ x, mts_gaussTag p 0 σ 3 (mts_atomTags p 0 σ) mts_tent (mts_priorPoint p 0 E x)
            ∂priorWindowMeasure Pω w) + ε := by
  obtain ⟨hκ, hκE⟩ := mts_bulk_margin hE1 hE2
  set κ := (2 - |E|) / 2
  have hρ := mts_semicircleDensity_pos hE1 hE2
  obtain ⟨R, hR⟩ := mts_exists_support_radius hw.2.1
  obtain ⟨W₁, hW₁⟩ := mts_commonPort_step hCP hMT hb hb' hκ T Φ hε
  refine ⟨max W₁ ⌈R / (κ * Parameters.semicircleDensity E)⌉₊, ?_⟩
  intro p hpb hW hn model Pω hs σ
  subst hpb
  have hP := mts_isProbabilityMeasure_of_blockSplitting hs
  have hPr := mts_isProbabilityMeasure_prior (Pω := Pω) hw
  have hPp := mts_isProbabilityMeasure_portLaw p.W p.b
  have hPc := isProbabilityMeasure_probedClockLaw p.W p.b
  have hW1 : W₁ ≤ p.W := (le_max_left _ _).trans hW
  have hWR : R / (κ * Parameters.semicircleDensity E) ≤ p.W := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans hW)
  have hbulk : ∀ u, w u ≠ 0 → microEnergy p E u ∈ bulkInterval κ := fun u hu =>
    mts_mem_bulk_of_window p hρ hκE hκ hWR (by rw [mts_microCoord_microEnergy p hρ]; exact hR u hu)
  have hwi : Integrable w := hw.1.integrable_of_hasCompactSupport hw.2.1
  -- the Gaussian tag tests along the prior
  set Fm := fun x => mts_gaussTag p 0 σ p.n (mts_mainTags p 0 σ) Φ (mts_priorPoint p 0 E x)
    with hFmdef
  set Fa := fun x => mts_gaussTag p 0 σ 3 (mts_atomTags p 0 σ) mts_tent (mts_priorPoint p 0 E x)
    with hFadef
  have hFmm : Measurable Fm := (mts_measurable_gaussTag σ p.n (mts_measurable_mainTags p 0 σ)
    Φ).comp (mts_measurable_priorPoint p 0 E)
  have hFam : Measurable Fa := (mts_measurable_gaussTag σ 3 (mts_measurable_atomTags p 0 σ)
    mts_tent).comp (mts_measurable_priorPoint p 0 E)
  have hFmi : Integrable Fm (priorWindowMeasure Pω w) := Integrable.of_bound
    hFmm.aestronglyMeasurable ‖Φ‖ (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact mts_abs_gaussTag_le σ _ _ Φ _)
  have hFai : Integrable Fa (priorWindowMeasure Pω w) := Integrable.of_bound
    hFam.aestronglyMeasurable ‖mts_tent‖ (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact mts_abs_gaussTag_le σ _ _ mts_tent _)
  rw [mts_integral_prior hw hFmi, mts_integral_prior hw hFai]
  set Mn := fun u => ∫ ω, Fm (u, ω) ∂Pω with hMndef
  set At := fun u => ∫ ω, Fa (u, ω) ∂Pω with hAtdef
  set I := fun u => ∫ x, leadAveragedTest p.b (microEnergy p E u) p.n p.W Φ x
    ∂probedClockLaw p.W p.b with hIdef
  have hMnm : Measurable Mn := hFmm.stronglyMeasurable.integral_prod_right'.measurable
  have hAtm : Measurable At := hFam.stronglyMeasurable.integral_prod_right'.measurable
  have hIm : Measurable I := (measurable_leadAveragedTest_of p.b p.n p.W Φ
    ((mts_measurable_microEnergy p E).comp measurable_fst)
    measurable_snd).stronglyMeasurable.integral_prod_right'.measurable
  have hMnb : ∀ u, ‖Mn u‖ ≤ ‖Φ‖ := fun u => by
    have h := norm_integral_le_of_norm_le_const (μ := Pω) (C := ‖Φ‖) (f := fun ω => Fm (u, ω))
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact mts_abs_gaussTag_le σ _ _ Φ _)
    simpa [probReal_univ] using h
  have hAtb : ∀ u, ‖At u‖ ≤ ‖mts_tent‖ := fun u => by
    have h := norm_integral_le_of_norm_le_const (μ := Pω) (C := ‖mts_tent‖)
      (f := fun ω => Fa (u, ω))
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact mts_abs_gaussTag_le σ _ _ mts_tent _)
    simpa [probReal_univ] using h
  have hIb : ∀ u, ‖I u‖ ≤ ‖Φ‖ := fun u => by
    have h := norm_integral_le_of_norm_le_const (μ := probedClockLaw p.W p.b) (C := ‖Φ‖)
      (f := fun x => leadAveragedTest p.b (microEnergy p E u) p.n p.W Φ x)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; exact abs_leadAveragedTest_le _ _ p.n_ge_four _ Φ _)
    simpa [probReal_univ] using h
  have hwMn : Integrable (fun u => w u * Mn u) := hwi.mul_bdd hMnm.aestronglyMeasurable
    (ae_of_all _ hMnb)
  have hwAt : Integrable (fun u => w u * At u) := hwi.mul_bdd hAtm.aestronglyMeasurable
    (ae_of_all _ hAtb)
  have hwI : Integrable (fun u => w u * I u) := hwi.mul_bdd hIm.aestronglyMeasurable
    (ae_of_all _ hIb)
  -- the pointwise comparison at a bulk energy
  have hpt : ∀ u, w u ≠ 0 → |Mn u - I u| ≤ 2 * L * At u + ε := by
    intro u hu
    have hbu := hbulk u hu
    have he1 : -2 < microEnergy p E u := by have := hbu.1; linarith
    have he2 : microEnergy p E u < 2 := by have := hbu.2; linarith
    set e := microEnergy p E u with hedef
    have hMn : Mn u = ∫ y, mts_mainClockTest p Φ (fun j => mts_portBlockClock p.b e p.n p.W y j)
        ∂mts_portLaw p.W p.b :=
      mts_gauss_eq_port hL p hs σ he1 he2 p.n (mts_mainTags p 0 σ) Φ
        (mts_measurable_mainClockTest p Φ) ⟨‖Φ‖, mts_abs_mainClockTest_le p Φ⟩
        (fun ω v => mts_tagTest_mainTags p 0 σ e ω Φ v)
        (fun x => mts_mainClockTest_smul p Φ p.c_pos.ne' x)
    have hAt : At u = ∫ y, mts_atomClockTest p 0
        (fun j => mts_portBlockClock p.b e p.n p.W y j) ∂mts_portLaw p.W p.b :=
      mts_gauss_eq_port hL p hs σ he1 he2 3 (mts_atomTags p 0 σ) mts_tent
        (mts_measurable_atomClockTest p 0) ⟨2, mts_abs_atomClockTest_le p 0⟩
        (fun ω v => mts_tagTest_atomTags p 0 σ e ω v)
        (fun x => mts_atomClockTest_smul p 0 p.c_pos.ne' x)
    have hcp := hW₁ p.W hW1 p.n p.n_ge_four hn e hbu
    have hclk : Measurable fun y : GrowthPath p.W × (LayerSample p.W .common ×
        (Fin 1 × Fin p.W → ℂ)) => fun j => mts_portBlockClock p.b e p.n p.W y j :=
      measurable_pi_iff.2 fun j => mts_measurable_portBlockClock p.b e p.n p.W j
    have i1 : Integrable (fun y => mts_mainClockTest p Φ
        (fun j => mts_portBlockClock p.b e p.n p.W y j)) (mts_portLaw p.W p.b) :=
      Integrable.of_bound ((mts_measurable_mainClockTest p Φ).comp hclk).aestronglyMeasurable ‖Φ‖
        (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact mts_abs_mainClockTest_le p Φ _)
    have i2 : Integrable (fun y : GrowthPath p.W × (LayerSample p.W .common ×
        (Fin 1 × Fin p.W → ℂ)) => leadAveragedTest p.b e p.n p.W Φ
          (y.1, commonPortProbe p.b e (leadSchur e p.W (p.n - 3) y.1) y.2))
        (mts_portLaw p.W p.b) :=
      Integrable.of_bound (measurable_leadAveragedTest_of p.b p.n p.W Φ measurable_const
        (mts_measurable_portProbe p.b e p.W (p.n - 3))).aestronglyMeasurable ‖Φ‖
        (ae_of_all _ fun y => by
          rw [Real.norm_eq_abs]; exact abs_leadAveragedTest_le _ _ p.n_ge_four _ Φ _)
    have i3 : Integrable (fun y => mts_atomClockTest p 0
        (fun j => mts_portBlockClock p.b e p.n p.W y j)) (mts_portLaw p.W p.b) :=
      Integrable.of_bound ((mts_measurable_atomClockTest p 0).comp hclk).aestronglyMeasurable 2
        (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact mts_abs_atomClockTest_le p 0 _)
    have hdel : |Mn u - ∫ y, leadAveragedTest p.b e p.n p.W Φ
        (y.1, commonPortProbe p.b e (leadSchur e p.W (p.n - 3) y.1) y.2)
          ∂mts_portLaw p.W p.b| ≤ 2 * L * At u := by
      rw [hMn, hAt, ← integral_sub i1 i2, ← integral_const_mul]
      exact abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
        (ae_of_all _ fun _ => abs_nonneg _) (i3.const_mul _)
        (ae_of_all _ fun y => mts_port_deletion p p.b e hLip y))
    calc |Mn u - I u| ≤ |Mn u - ∫ y, leadAveragedTest p.b e p.n p.W Φ
          (y.1, commonPortProbe p.b e (leadSchur e p.W (p.n - 3) y.1) y.2)
            ∂mts_portLaw p.W p.b| + |(∫ y, leadAveragedTest p.b e p.n p.W Φ
          (y.1, commonPortProbe p.b e (leadSchur e p.W (p.n - 3) y.1) y.2)
            ∂mts_portLaw p.W p.b) - I u| := abs_sub_le _ _ _
      _ ≤ 2 * L * At u + ε := add_le_add hdel hcp
  -- integrate over `u`
  have hlead : leadTagSide p E w Φ = ∫ u, w u * I u := rfl
  rw [hlead, ← integral_sub hwMn hwI]
  have hint : Integrable (fun u => 2 * L * (w u * At u) + ε * w u) :=
    (hwAt.const_mul _).add (hwi.const_mul _)
  calc |∫ u, (w u * Mn u - w u * I u)| ≤ ∫ u, |w u * Mn u - w u * I u| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u, (2 * L * (w u * At u) + ε * w u) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hint (ae_of_all _ fun u => by
          show |w u * Mn u - w u * I u| ≤ 2 * L * (w u * At u) + ε * w u
          rw [← mul_sub, abs_mul, abs_of_nonneg (hw.2.2.1 u)]
          by_cases hu : w u = 0
          · rw [hu]; simp
          · have h := mul_le_mul_of_nonneg_left (hpt u hu) (hw.2.2.1 u)
            linarith)
    _ = 2 * L * (∫ u, w u * At u) + ε := by
        rw [integral_add (hwAt.const_mul _) (hwi.const_mul _), integral_const_mul,
          integral_const_mul, hw.2.2.2, mul_one]

theorem mts_integrable_blockAtom (p : Parameters) (model : p.GaussianRingModel) (E : ℝ)
    {w : ℝ → ℝ} (hwc : Continuous w) (hws : HasCompactSupport w) :
    Integrable (blockAtomFunctional p E w) (model.law : Measure p.SiteMatrix) := by
  obtain ⟨C, hC⟩ := hwc.bounded_above_of_compact_support hws
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hm : Measurable (blockAtomFunctional p E w) := by
    unfold blockAtomFunctional
    exact Finset.measurable_sum _ fun α _ => (continuous_abs.measurable.comp (hwc.measurable.comp
      ((mts_measurable_microCoord p E).comp (mts_measurable_physicalOrderedEigenvalue p α)))).mul
      (Finset.measurable_sum _ fun k _ => (measurable_physicalOrderedBlockMass p α k).pow_const 2)
  refine Integrable.of_bound hm.aestronglyMeasurable (p.N * (C * p.n)) ?_
  filter_upwards [physicalOrderedBlockMass_sum_ae p model] with H hH
  have hnn : 0 ≤ blockAtomFunctional p E w H := Finset.sum_nonneg fun α _ =>
    mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun k _ => sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  unfold blockAtomFunctional
  have hle : ∀ α : Fin p.N, |w (microCoord p E (physicalOrderedEigenvalue p H α))| *
      ∑ k : ZMod p.n, physicalOrderedBlockMass p H α k ^ 2 ≤ C * p.n := by
    intro α
    have hp1 : ∀ k, physicalOrderedBlockMass p H α k ≤ 1 := fun k => by
      rw [← hH α]
      exact Finset.single_le_sum (f := fun k => physicalOrderedBlockMass p H α k)
        (fun k _ => physicalOrderedBlockMass_nonneg p H α k) (Finset.mem_univ k)
    have hs : ∑ k : ZMod p.n, physicalOrderedBlockMass p H α k ^ 2 ≤ p.n := by
      calc ∑ k : ZMod p.n, physicalOrderedBlockMass p H α k ^ 2 ≤ ∑ _k : ZMod p.n, (1 : ℝ) :=
            Finset.sum_le_sum fun k _ =>
              pow_le_one₀ (physicalOrderedBlockMass_nonneg p H α k) (hp1 k)
        _ = p.n := by simp
    exact mul_le_mul (by rw [← Real.norm_eq_abs]; exact hC _) hs
      (Finset.sum_nonneg fun k _ => sq_nonneg _) hC0
  calc _ ≤ ∑ _α : Fin p.N, C * p.n := Finset.sum_le_sum fun α _ => hle α
    _ = p.N * (C * p.n) := by simp

/-- **Steps 1–4 for a window and a nonnegative Lipschitz test.** Hypotheses:
`RingRotationInvariance`, `VanishingBlockAtom`, `FreshEigenpairDensityContract`,
`OneBlockPalmContract`, `OneBlockNormalizerContract`, `UniformClockTagsPalmContract`,
`ClockCovarianceStabilityContract`, `BlockRegularEventContract`,
`LeadFieldIdentificationContract`, `UniformClockTagsCommonPortContract` and
`MatchedTracesContract`. -/
theorem mts_core (hRot : RingRotationInvariance) (hAtom : VanishingBlockAtom)
    (hPalm : OneBlockPalmContract) (hNorm : OneBlockNormalizerContract)
    (hFED : FreshEigenpairDensityContract) (hUCT : UniformClockTagsPalmContract)
    (hCS : ClockCovarianceStabilityContract) (hReg : BlockRegularEventContract)
    (hL : LeadFieldIdentificationContract) (hCP : UniformClockTagsCommonPortContract)
    (hMT : MatchedTracesContract) (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ)
    (hE1 : -2 < E) (hE2 : E < 2) {w : ℝ → ℝ} (hw : IsWindow w) {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ}
    (hΦ : ∀ x, 0 ≤ Φ x) {L : NNReal} (hLip : LipschitzWith L Φ) (τ : ℝ) (hτ : 0 < τ)
    (s : CriticalSequence τ) (R : ∀ j, (s.parameters b hb hb' j).GaussianRingModel)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ k : ZMod (s.parameters b hb hb' j).n,
      |physicalTagSide (s.parameters b hb hb' j) (R j) E w Φ k -
          leadTagSide (s.parameters b hb hb' j) E w Φ| ≤ ε := by
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  set δ := ε / (20 * ((L : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hεδ : ε = 20 * ((L : ℝ) + 1) * δ := by rw [hδdef]; field_simp
  set K := (2 * (‖Φ‖ + ‖mts_tent‖) + 1) / δ with hKdef
  have hK : 0 < K := by positivity
  have hδK : δ * K = 2 * (‖Φ‖ + ‖mts_tent‖) + 1 := by rw [hKdef]; field_simp
  have hKΦ : 2 * ‖Φ‖ / K ≤ δ := by
    rw [div_le_iff₀ hK, hδK]; nlinarith [norm_nonneg mts_tent]
  have hKt : 2 * ‖mts_tent‖ / K ≤ δ := by
    rw [div_le_iff₀ hK, hδK]; nlinarith [norm_nonneg Φ]
  set T := τ + 1 with hTdef
  obtain ⟨W₁, hW₁⟩ := mts_window_to_prior hNorm hb hb' hE1 hE2 T hw hΦ hδ
  obtain ⟨W₂, hW₂⟩ := mts_window_to_prior hNorm hb hb' hE1 hE2 T hw mts_tent_nonneg hδ
  obtain ⟨W₃, hW₃⟩ := mts_prior_palm_gauss hUCT hCS hReg hb hb' hE1 hE2 T hw Φ hδ hK
  obtain ⟨W₄, hW₄⟩ := mts_prior_palm_gauss hUCT hCS hReg hb hb' hE1 hE2 T hw mts_tent hδ hK
  obtain ⟨W₅, hW₅⟩ := mts_prior_gauss_lead hL hCP hMT hb hb' hE1 hE2 T hw hLip hδ
  set W₀ := max (max (max W₁ W₂) (max W₃ W₄)) W₅ with hW₀def
  have hev1 : ∀ᶠ j in atTop, W₀ ≤ s.W j := s.width_tendsto.eventually_ge_atTop W₀
  have hev2 : ∀ᶠ j in atTop, (s.n j : ℝ) / s.W j < T :=
    s.ratio_tendsto.eventually (gt_mem_nhds (by rw [hTdef]; linarith))
  have hev3 : ∀ᶠ j in atTop, ∫ H, blockAtomFunctional (s.parameters b hb hb' j) E w H
      ∂((R j).law : Measure (s.parameters b hb hb' j).SiteMatrix) < δ :=
    (hAtom b hb hb' E hE1 hE2 w hw.1 hw.2.1 τ hτ s R).eventually (gt_mem_nhds hδ)
  filter_upwards [hev1, hev2, hev3] with j hWj hnj hatj
  set p := s.parameters b hb hb' j with hpdef
  intro k
  have hpb : p.b = b := rfl
  have hWp : W₀ ≤ p.W := hWj
  have hnp : (p.n : ℝ) ≤ T * p.W := by
    have hWpos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
    exact ((div_lt_iff₀ hWpos).1 hnj).le
  have h1 : W₁ ≤ p.W := (le_max_left _ _).trans ((le_max_left _ _).trans
    ((le_max_left _ _).trans hWp))
  have h2 : W₂ ≤ p.W := (le_max_right _ _).trans ((le_max_left _ _).trans
    ((le_max_left _ _).trans hWp))
  have h3 : W₃ ≤ p.W := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_left _ _).trans hWp))
  have h4 : W₄ ≤ p.W := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_left _ _).trans hWp))
  have h5 : W₅ ≤ p.W := (le_max_right _ _).trans hWp
  obtain ⟨Pω, hs⟩ := hPalm.splitting_exists p (R j) 0
  obtain ⟨U, hU⟩ := hPalm.frame_exists p 0
  set σ := Fintype.equivFin (BlockSite p 0)
  have hw0 := hw.2.2.1
  have hwm := hw.1.measurable
  -- the main chain
  have e1 : physicalTagSide p (R j) E w Φ k = (∫⁻ x, ENNReal.ofReal
      (mts_palmTag p 0 σ p.n (mts_mainTags p 0 σ) Φ x) ∂blockWindowMeasure p 0 U Pω E w).toReal :=
    mts_physical_main p hRot hPalm hFED hs U hU σ E hwm hw0 hΦ k
  have e2 := hW₁ p hpb h1 hnp (R j) 0 Pω hs U hU σ p.n (mts_mainTags p 0 σ)
    (mts_measurable_mainTags p 0 σ)
  have e3 := hW₃ p hpb h3 hnp (R j) 0 Pω hs σ p.n p.n_pos (mts_mainTags p 0 σ)
    (mts_measurable_mainTags p 0 σ) (fun x j => mts_mainTags_posSemidef p 0 σ x j)
    (mts_mainTags_sum_sub_one p 0 σ)
  have e4 := hW₅ p hpb h5 hnp (R j) Pω hs σ
  -- the block-`0` atom
  have a1 := mts_physical_atom p hRot hPalm hFED hs U hU σ E hwm hw0
  have a2 := hW₂ p hpb h2 hnp (R j) 0 Pω hs U hU σ 3 (mts_atomTags p 0 σ)
    (mts_measurable_atomTags p 0 σ)
  have a3 := hW₄ p hpb h4 hnp (R j) 0 Pω hs σ 3 (by norm_num) (mts_atomTags p 0 σ)
    (mts_measurable_atomTags p 0 σ) (fun x j => mts_atomTags_posSemidef p 0 σ x j)
    (mts_atomTags_sum_sub_one p 0 σ)
  have hai := mts_integrable_blockAtom p (R j) E hw.1 hw.2.1
  have hann : ∀ H, 0 ≤ blockAtomFunctional p E w H := fun H => Finset.sum_nonneg fun α _ =>
    mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hat0 : 0 ≤ ∫ H, blockAtomFunctional p E w H ∂((R j).law : Measure p.SiteMatrix) :=
    integral_nonneg hann
  have a1' : (∫⁻ x, ENNReal.ofReal (mts_palmTag p 0 σ 3 (mts_atomTags p 0 σ) mts_tent x)
      ∂blockWindowMeasure p 0 U Pω E w).toReal ≤ 2 * δ := by
    have h := a1
    rw [← ofReal_integral_eq_lintegral_ofReal hai (ae_of_all _ hann), ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num)] at h
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity) h).trans (by linarith)
  -- assemble
  rw [e1]
  obtain ⟨e2l, e2r⟩ := abs_le.1 e2
  obtain ⟨e3l, e3r⟩ := abs_le.1 e3
  obtain ⟨e4l, e4r⟩ := abs_le.1 e4
  obtain ⟨a2l, a2r⟩ := abs_le.1 a2
  obtain ⟨a3l, a3r⟩ := abs_le.1 a3
  set Ga := ∫ x, mts_gaussTag p 0 σ 3 (mts_atomTags p 0 σ) mts_tent (mts_priorPoint p 0 E x)
    ∂priorWindowMeasure Pω w with hGadef
  have hGa : Ga ≤ 7 * δ := by
    have := (ENNReal.toReal_nonneg : (0 : ℝ) ≤ (∫⁻ x, ENNReal.ofReal
      (mts_palmTag p 0 σ 3 (mts_atomTags p 0 σ) mts_tent x) ∂blockWindowMeasure p 0 U Pω E w).toReal)
    linarith
  have hLG : 2 * (L : ℝ) * Ga ≤ 2 * L * (7 * δ) := mul_le_mul_of_nonneg_left hGa (by positivity)
  have hLδ : 0 ≤ (L : ℝ) * δ := mul_nonneg hL0 hδ.le
  refine abs_le.2 ⟨?_, ?_⟩
  · rw [hεδ]; linarith
  · rw [hεδ]; linarith

end BlockBand.Endpoints
