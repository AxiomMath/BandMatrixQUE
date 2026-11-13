module

public import BlockBand.Angular.AssemblyGoodFiber
public import BlockBand.Window.Count.RefinedCountLocationTools
public import BlockBand.Angular.AssemblyEigen

/-!
# The good part of the physical angular estimate

Per parameter set, with `ρ ∈ {Re, Im}` and `g = obsG`:
* the pair-law integrand is `ρ⁻¹`-recombined from `g(splitOf(H - G_e), λ_α, ψ_α)`
  (`obsG_pair`);
* `E♯[g^±]` is the nested angular integral (`lintegral_transfer`);
* on each good fiber the comparison gives `|∫g⁺ - ∫g⁻| ≤ K(zT + r + sT)`
  (`fiber_bound`, the first moment by `center_angular_first_moment_goodDomain`
  with `K = 1`: the remainder `(n/2)C_K N^{-K}` is `O(T C_1)` for `n ≤ TW`, so no large `K`
  is needed for an `O((M+L)/W)` bound; `j_*(J) = j_e` by `CenterDomainContract.regular`);
  off the good set `g = 0`;
* outer integration (`abs_integral_obsOn_le`): `∫∫zT ≤ 1` (`outerInt_sector_le_one`),
  `∫∫1_I r ≤ 4r` (`I = bulkInterval (πθ/4) ⊇` good energies, `classicalLocation_mem_bulk`),
  `∫∫1_I sT ≤ C_s` (`DeterminantScoreStatement.moments`, exponent `1`);
* `r = (n/2)C_1(2W)^{-1}`, so `4r ≤ T C_1`; the constant is
  `C = |compConst|(1 + |T|C_1 + |C_s|)`, chosen before `n, W`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.AssemblyGood

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.FiberAngular
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.QUE
open BlockBand.Angular.Assembly BlockBand.Angular.ProjectiveStein BlockBand.Angular.PairCoareaBridge
open BlockBand.DeterminantScore BlockBand.DeterminantScore.PhysicalColumn BlockBand.Coarea
open BlockBand.Model.Construction BlockBand.QUE.PhysicalAngularReduction
open BlockBand.Angular.Ratio BlockBand.Angular.Stein BlockBand.Angular.Stein.AngularData
open BlockBand.Angular.StepTwoGlue BlockBand.Angular.DetFactor BlockBand.Angular.FirstMoment
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
## Outer integrals
-/

section Outer

variable {p : BlockBand.Parameters} {i : ZMod p.n}

theorem detFactor_eq_zNat' (α : Fin p.N) (s : ℝ) (U : FrameMap p i) (ω : SplitState p i) (E : ℝ)
    (v : PairSite p i → ℂ) : detFactor p i α s U ω E v = zNat s U α.val (ω, E, v) :=
  BlockBand.DeterminantScore.MinorTail.detFactor_eq_zNat α s U (ω, E, v)

theorem measurable_zT (α : Fin p.N) {U : FrameMap p i} (hU : IsPairFrame p i U) :
    Measurable (Function.uncurry (zT α U)) := by
  have := isProbabilityMeasure_projectiveHaar (ι := PairSite p i)
  have h : Measurable fun θ : OuterData p i =>
      ENNReal.ofReal (angularWeight p i (splitS p) θ.1 θ.2.1 θ.2.2) *
        detFactor p i α (splitS p) U θ.1 θ.2.1 θ.2.2 :=
    (ENNReal.measurable_ofReal.comp (measurable_angularWeight (splitS p))).mul
      (measurable_detFactor α (splitS p) hU)
  have h2 := (h.comp (measurable_fst.fst.prodMk
    (measurable_fst.snd.prodMk measurable_snd))).lintegral_prod_right'
    (ν := projectiveHaar (PairSite p i))
  exact h2

theorem outer_zT_le (hC : CoareaContract) {model : p.GaussianRingModel} (α : Fin p.N)
    {X : PairExtension p model} {G : X.Ω → PairMatrix p i} (hG : IsCenterSplitting X G)
    {U : FrameMap p i} (hU : IsPairFrame p i U) :
    (∫⁻ ω', ∫⁻ E, zT α U ω' E
      ∂volume ∂(X.P.map (fun ω => splitOf p i (X.Hm ω - embedPair p i (G ω))))) ≤ 1 := by
  have hPω := isPairSplitting_of_centerSplitting p i X G hG
  refine le_trans (le_of_eq ?_) (outerInt_sector_le_one hC hPω hU α.val)
  unfold outerInt sectorTerm zT
  refine lintegral_congr fun om => lintegral_congr fun E => lintegral_congr fun v => ?_
  rw [detFactor_eq_zNat']

theorem prob_univ_le {model : p.GaussianRingModel} (X : PairExtension p model)
    {G : X.Ω → PairMatrix p i} (hG : IsCenterSplitting X G) :
    (X.P.map (fun ω => splitOf p i (X.Hm ω - embedPair p i (G ω)))) Set.univ ≤ 1 := by
  have hm : Measurable fun ω => splitOf p i (X.Hm ω - embedPair p i (G ω)) :=
    (measurable_splitOf p i).comp (X.measurable_Hm.sub ((measurable_embedPair p i).comp hG.1))
  rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ]
  have h1 : X.P Set.univ = (X.P.map X.Hm) Set.univ := by
    rw [Measure.map_apply X.measurable_Hm MeasurableSet.univ, Set.preimage_univ]
  rw [h1, X.map_eq]
  exact prob_le_one

theorem outer_r_le {model : p.GaussianRingModel} (X : PairExtension p model)
    {G : X.Ω → PairMatrix p i} (hG : IsCenterSplitting X G) {κ : ℝ} (hκ : 0 ≤ κ) (r : ℝ) (hr : 0 ≤ r) :
    (∫⁻ _ω, ∫⁻ E, (bulkInterval κ).indicator 1 E * ENNReal.ofReal r
      ∂volume ∂(X.P.map (fun ω => splitOf p i (X.Hm ω - embedPair p i (G ω))))) ≤
      ENNReal.ofReal (4 * r) := by
  have hE : (∫⁻ E, (bulkInterval κ).indicator 1 E * ENNReal.ofReal r) ≤ ENNReal.ofReal (4 * r) := by
    have e : (fun E => (bulkInterval κ).indicator (1 : ℝ → ℝ≥0∞) E * ENNReal.ofReal r) =
        fun E => (bulkInterval κ).indicator (fun _ => ENNReal.ofReal r) E := by
      funext E; by_cases h : E ∈ bulkInterval κ <;> simp [h]
    have hmeas : MeasurableSet (bulkInterval κ) := by unfold bulkInterval; exact measurableSet_Icc
    rw [e, lintegral_indicator_const hmeas]
    unfold bulkInterval
    rw [Real.volume_Icc]
    rw [← ENNReal.ofReal_mul hr]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith
  calc _ ≤ ∫⁻ ω', ENNReal.ofReal (4 * r)
        ∂(X.P.map (fun ω => splitOf p i (X.Hm ω - embedPair p i (G ω)))) :=
        lintegral_mono fun _ => hE
    _ = ENNReal.ofReal (4 * r) *
        (X.P.map (fun ω => splitOf p i (X.Hm ω - embedPair p i (G ω)))) Set.univ := lintegral_const _
    _ ≤ ENNReal.ofReal (4 * r) := by
        calc _ ≤ ENNReal.ofReal (4 * r) * 1 := by gcongr; exact prob_univ_le X hG
          _ = _ := mul_one _

theorem outer_sT_le {α : Fin p.N} {U : FrameMap p i} (κ : ℝ) (Pω : Measure (SplitState p i)) :
    (∫⁻ ω', ∫⁻ E, (bulkInterval κ).indicator 1 E * sT α U ω' E ∂volume ∂Pω) ≤
      pairExpect α (splitS p) U Pω (fun θ _ =>
        (bulkInterval κ).indicator 1 θ.2.1 *
          ENNReal.ofReal (‖condInverse α (splitS p) U θ‖ ^ (1 : ℝ) +
            l2Norm (score α (splitS p) U θ) ^ (1 : ℝ))) := by
  unfold pairExpect sT
  refine lintegral_mono fun om => lintegral_mono fun E => ?_
  have hind : (bulkInterval κ).indicator (1 : ℝ → ℝ≥0∞) E ≠ ∞ := by
    unfold Set.indicator; split_ifs <;> simp
  rw [← lintegral_const_mul' _ _ hind]
  refine lintegral_mono fun v => ?_
  set Ψ := (bulkInterval κ).indicator (1 : ℝ → ℝ≥0∞) E *
    ENNReal.ofReal (‖condInverse α (splitS p) U (om, E, v)‖ ^ (1 : ℝ) +
      l2Norm (score α (splitS p) U (om, E, v)) ^ (1 : ℝ))
  have hΨ : Ψ ≠ ∞ := ENNReal.mul_ne_top hind ENNReal.ofReal_ne_top
  have e : (∫⁻ G', ENNReal.ofReal (angularWeight p i (splitS p) om E v) *
      ENNReal.ofReal (sectorWeight α U (om, E, v) G') * Ψ
      ∂gueMeasure (FrameIndex p) (pairTime p (splitS p))) =
      ENNReal.ofReal (angularWeight p i (splitS p) om E v) *
        detFactor p i α (splitS p) U om E v * Ψ := by
    rw [lintegral_mul_const' _ _ hΨ, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      detFactor_eq_zNat']
    rfl
  rw [e]
  have hs : ENNReal.ofReal (l2Norm (score α (splitS p) U (om, E, v))) ≤
      ENNReal.ofReal (‖condInverse α (splitS p) U (om, E, v)‖ ^ (1 : ℝ) +
        l2Norm (score α (splitS p) U (om, E, v)) ^ (1 : ℝ)) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.rpow_one, Real.rpow_one]
    linarith [norm_nonneg (condInverse α (splitS p) U (om, E, v))]
  calc (bulkInterval κ).indicator 1 E * (ENNReal.ofReal (angularWeight p i (splitS p) om E v) *
        detFactor p i α (splitS p) U om E v *
          ENNReal.ofReal (l2Norm (score α (splitS p) U (om, E, v))))
      = ENNReal.ofReal (angularWeight p i (splitS p) om E v) * detFactor p i α (splitS p) U om E v *
          ((bulkInterval κ).indicator 1 E *
            ENNReal.ofReal (l2Norm (score α (splitS p) U (om, E, v)))) := by ring
    _ ≤ _ := by unfold Ψ; gcongr

end Outer

/-!
## The bound on one real part
-/

section RealPart

variable {p : BlockBand.Parameters} {i : ZMod p.n}

/-- The observable on the extension. -/
def obsOn {model : p.GaussianRingModel} (cst : CenterDomainConstants) (α : Fin p.N) (M₀ R₀ : ℝ)
    (φ : (p.Site → ℂ) → ℂ) (ρ : ℂ → ℝ) (X : PairExtension p model) (G : X.Ω → PairMatrix p i)
    (ω : X.Ω) : ℝ :=
  obsG p i cst α M₀ R₀ φ ρ (splitOf p i (residual p i X G ω),
    physicalOrderedEigenvalue p (X.Hm ω) α) (physicalOrderedEigenvector p (X.Hm ω) α)

theorem measurable_obsOn {model : p.GaussianRingModel} {cst : CenterDomainConstants}
    (hcd : CenterDomainContract cst) (α : Fin p.N) (M₀ R₀ : ℝ) {φ : (p.Site → ℂ) → ℂ} {M L : ℝ}
    (hφ : IsAngularTest φ M L) {ρ : ℂ → ℝ} (hρ : IsRealPart ρ) (X : PairExtension p model)
    {G : X.Ω → PairMatrix p i} (hG : IsCenterSplitting X G) :
    Measurable (obsOn cst α M₀ R₀ φ ρ X G) := by
  have hres : Measurable fun ω => residual p i X G ω :=
    X.measurable_Hm.sub ((measurable_embedPair p i).comp hG.1)
  have hψ : Measurable fun ω => physicalOrderedEigenvector p (X.Hm ω) α :=
    measurable_pi_iff.2 fun x => (measurable_physicalOrderedEigenvector p α x).comp X.measurable_Hm
  have hx := (((measurable_splitOf p i).comp hres).prodMk
    ((measurable_physicalOrderedEigenvalue p α).comp X.measurable_Hm)).prodMk hψ
  have h2 := (measurable_obsG hcd α M₀ R₀ hφ hρ).comp hx
  exact h2

/-- **The good part for one real part `ρ`.** -/
theorem abs_integral_obsOn_le (hC : CoareaContract)
    {model : p.GaussianRingModel} {cst : CenterDomainConstants} (hcd : CenterDomainContract cst)
    (α : Fin p.N) (M₀ R₀ : ℝ) {φ : (p.Site → ℂ) → ℂ} {M L : ℝ} (hφ : IsAngularTest φ M L)
    {ρ : ℂ → ℝ} (hρ : IsRealPart ρ) (X : PairExtension p model) {G : X.Ω → PairMatrix p i}
    (hG : IsCenterSplitting X G) {U : FrameMap p i} (hU : IsPairFrame p i U) {κ K r Cs : ℝ}
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hκ0 : 0 ≤ κ)
    (hκ : ∀ x ∈ goodSet p i cst α M₀, x.2 ∈ bulkInterval κ)
    (hfib : ∀ ω : SplitState p i, ω.1.IsHermitian → ω.2.2.IsHermitian → ∀ E : ℝ,
      (ω, E) ∈ goodSet p i cst α M₀ →
        angInt α U (obsG p i cst α M₀ R₀ φ ρ) 1 ω E ≠ ∞ ∧
        angInt α U (obsG p i cst α M₀ R₀ φ ρ) (-1) ω E ≠ ∞ ∧
        ENNReal.ofReal |(angInt α U (obsG p i cst α M₀ R₀ φ ρ) 1 ω E).toReal -
            (angInt α U (obsG p i cst α M₀ R₀ φ ρ) (-1) ω E).toReal| ≤
          ENNReal.ofReal K * (zT α U ω E + ENNReal.ofReal r + sT α U ω E))
    (hmom : pairExpect α (splitS p) U (X.P.map (fun ω => splitOf p i (X.Hm ω - embedPair p i (G ω))))
      (fun θ _ => (bulkInterval κ).indicator 1 θ.2.1 *
        ENNReal.ofReal (‖condInverse α (splitS p) U θ‖ ^ (1 : ℝ) +
          l2Norm (score α (splitS p) U θ) ^ (1 : ℝ))) ≤ ENNReal.ofReal Cs) :
    |∫ ω, obsOn cst α M₀ R₀ φ ρ X G ω ∂extendedPairMeasure p α i X.P X.Hm| ≤
      K * (1 + 4 * r + |Cs|) := by
  have hprob := BlockBand.QUE.PairResidual.extendedPairMeasure_isProbability p model α i X
  set μ := extendedPairMeasure p α i X.P X.Hm
  set Pω := X.P.map (fun ω => splitOf p i (X.Hm ω - embedPair p i (G ω)))
  set g := obsG p i cst α M₀ R₀ φ ρ
  have hgm : Measurable (Function.uncurry g) := measurable_obsG hcd α M₀ R₀ hφ hρ
  have hgl : IsLineInvariant g := isLineInvariant_obsG cst α M₀ R₀ hφ ρ
  have hfm := measurable_obsOn hcd α M₀ R₀ hφ hρ X hG
  have hfB : ∀ ω, |obsOn cst α M₀ R₀ φ ρ X G ω| ≤ 2 * M := fun ω =>
    abs_obsG_le hφ hρ (splitOf p i (residual p i X G ω), physicalOrderedEigenvalue p (X.Hm ω) α)
      (physicalOrderedEigenvector p (X.Hm ω) α)
  have hfi : Integrable (obsOn cst α M₀ R₀ φ ρ X G) μ :=
    Integrable.of_bound hfm.aestronglyMeasurable (2 * M)
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfB ω)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi]
  have hT1 := lintegral_transfer hC α X G hG hU hgm hgl 1
  have hT2 := lintegral_transfer hC α X G hG hU hgm hgl (-1)
  simp only [one_mul, neg_one_mul] at hT1 hT2
  have hT1' : (∫⁻ ω, ENNReal.ofReal (obsOn cst α M₀ R₀ φ ρ X G ω) ∂μ) =
      ∫⁻ ω', ∫⁻ E, angInt α U g 1 ω' E ∂volume ∂Pω := hT1
  have hT2' : (∫⁻ ω, ENNReal.ofReal (-obsOn cst α M₀ R₀ φ ρ X G ω) ∂μ) =
      ∫⁻ ω', ∫⁻ E, angInt α U g (-1) ω' E ∂volume ∂Pω := hT2
  rw [hT1', hT2']
  -- finiteness
  have hfin : ∀ sgn : ℝ, (∫⁻ ω, ENNReal.ofReal (sgn * obsOn cst α M₀ R₀ φ ρ X G ω) ∂μ) ≠ ∞ ∧
      (|sgn| ≤ 1 → (∫⁻ ω, ENNReal.ofReal (sgn * obsOn cst α M₀ R₀ φ ρ X G ω) ∂μ) ≤
        ENNReal.ofReal (2 * M)) := by
    intro sgn
    have hb : |sgn| ≤ 1 → ∀ ω, sgn * obsOn cst α M₀ R₀ φ ρ X G ω ≤ 2 * M := fun hs ω => by
      have := hfB ω
      calc sgn * _ ≤ |sgn * obsOn cst α M₀ R₀ φ ρ X G ω| := le_abs_self _
        _ = |sgn| * |obsOn cst α M₀ R₀ φ ρ X G ω| := abs_mul _ _
        _ ≤ 1 * (2 * M) := mul_le_mul hs this (abs_nonneg _) zero_le_one
        _ = 2 * M := one_mul _
    refine ⟨?_, fun hs => ?_⟩
    · exact (Integrable.lintegral_lt_top (hfi.const_mul sgn)).ne
    · calc _ ≤ ∫⁻ _, ENNReal.ofReal (2 * M) ∂μ := lintegral_mono fun ω =>
            ENNReal.ofReal_le_ofReal (hb hs ω)
        _ = ENNReal.ofReal (2 * M) := by rw [lintegral_const, measure_univ, mul_one]
  have hf1 : (∫⁻ ω', ∫⁻ E, angInt α U g 1 ω' E ∂volume ∂Pω) ≠ ∞ := by
    rw [← hT1']; simpa using (hfin 1).1
  have hf2 : (∫⁻ ω', ∫⁻ E, angInt α U g (-1) ω' E ∂volume ∂Pω) ≠ ∞ := by
    rw [← hT2']; simpa using (hfin (-1)).1
  -- the dominating function
  set cfun : SplitState p i → ℝ → ℝ≥0∞ := fun ω' E => ENNReal.ofReal K *
    ((zT α U ω' E + (bulkInterval κ).indicator 1 E * ENNReal.ofReal r) +
      (bulkInterval κ).indicator 1 E * sT α U ω' E) with hcdef
  have hzero : ∀ ω' E, (ω', E) ∉ goodSet p i cst α M₀ → ∀ sgn, angInt α U g sgn ω' E = 0 := by
    intro ω' E hx sgn
    unfold angInt
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun v => ?_)
    have : g (ω', E) (schurLift p i ω'.1 ω'.2.1 E v) = 0 := by
      show obsG p i cst α M₀ R₀ φ ρ (ω', E) _ = 0
      unfold obsG; rw [Set.indicator_of_notMem hx]; simp
    simp [this]
  have hgood : ∀ ω' : SplitState p i, ω'.1.IsHermitian → ω'.2.2.IsHermitian → ∀ E,
      angInt α U g 1 ω' E ≤ angInt α U g (-1) ω' E + cfun ω' E ∧
        angInt α U g (-1) ω' E ≤ angInt α U g 1 ω' E + cfun ω' E := by
    intro ω' hR hV E
    by_cases hx : (ω', E) ∈ goodSet p i cst α M₀
    · obtain ⟨h1, h2, h3⟩ := hfib ω' hR hV E hx
      have hI : (bulkInterval κ).indicator (1 : ℝ → ℝ≥0∞) E = 1 := by
        rw [Set.indicator_of_mem (hκ _ hx)]; rfl
      have hc : ENNReal.ofReal K * (zT α U ω' E + ENNReal.ofReal r + sT α U ω' E) = cfun ω' E := by
        rw [hcdef]; simp only [hI, one_mul]
      rw [hc] at h3
      refine ⟨le_add_of_ofReal_abs_sub_le h1 h2 h3, le_add_of_ofReal_abs_sub_le h2 h1 ?_⟩
      rwa [abs_sub_comm]
    · rw [hzero ω' E hx 1, hzero ω' E hx (-1)]
      exact ⟨zero_le, zero_le⟩
  have hae := ae_hermitian_of_isPairSplitting p i (isPairSplitting_of_centerSplitting p i X G hG)
  have hmain := ofReal_abs_sub_le_nested (μ := Pω) (ν := volume) (c := cfun)
    (measurable_angInt α hU hgm 1) (measurable_angInt α hU hgm (-1)) hf1 hf2
    (by filter_upwards [hae] with ω' hω' E using (hgood ω' hω'.1 hω'.2 E).1)
    (by filter_upwards [hae] with ω' hω' E using (hgood ω' hω'.1 hω'.2 E).2)
  -- the outer integral of `cfun`
  have hmI : Measurable ((bulkInterval κ).indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_const.indicator (by unfold bulkInterval; exact measurableSet_Icc)
  have hmP : Measurable (Function.uncurry fun ω' E =>
      zT α U ω' E + (bulkInterval κ).indicator (1 : ℝ → ℝ≥0∞) E * ENNReal.ofReal r) := by
    have h := (measurable_zT α hU).add ((hmI.comp measurable_snd).mul
      (measurable_const (a := ENNReal.ofReal r)))
    exact h
  have hcint : (∫⁻ ω', ∫⁻ E, cfun ω' E ∂volume ∂Pω) ≤ ENNReal.ofReal (K * (1 + 4 * r + |Cs|)) := by
    have hsplit : (∫⁻ ω', ∫⁻ E, cfun ω' E ∂volume ∂Pω) = ENNReal.ofReal K *
        ((∫⁻ ω', ∫⁻ E, zT α U ω' E ∂volume ∂Pω) +
          (∫⁻ ω', ∫⁻ E, (bulkInterval κ).indicator 1 E * ENNReal.ofReal r ∂volume ∂Pω) +
          ∫⁻ ω', ∫⁻ E, (bulkInterval κ).indicator 1 E * sT α U ω' E ∂volume ∂Pω) := by
      rw [hcdef]
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      have hin : ∀ ω', Measurable fun E =>
          zT α U ω' E + (bulkInterval κ).indicator (1 : ℝ → ℝ≥0∞) E * ENNReal.ofReal r :=
        fun ω' => by have h := hmP.comp (measurable_prodMk_left (x := ω')); exact h
      have hout : Measurable fun ω' => ∫⁻ E, (zT α U ω' E +
          (bulkInterval κ).indicator (1 : ℝ → ℝ≥0∞) E * ENNReal.ofReal r) := by
        have h := hmP.lintegral_prod_right' (ν := volume); exact h
      simp_rw [lintegral_add_left (hin _)]
      rw [lintegral_add_left hout]
      congr 1
      have hz : ∀ ω', Measurable fun E => zT α U ω' E :=
        fun ω' => by have h := (measurable_zT α hU).comp (measurable_prodMk_left (x := ω')); exact h
      simp_rw [lintegral_add_left (hz _)]
      have h := (measurable_zT α hU).lintegral_prod_right' (ν := volume)
      exact lintegral_add_left h _
    rw [hsplit, ENNReal.ofReal_mul hK]
    gcongr
    have e1 := outer_zT_le hC α hG hU
    have e2 := outer_r_le X hG hκ0 r hr
    have e3 := (outer_sT_le (α := α) (U := U) κ Pω).trans hmom
    calc _ ≤ 1 + ENNReal.ofReal (4 * r) + ENNReal.ofReal Cs := by gcongr
      _ ≤ ENNReal.ofReal (1 + 4 * r + |Cs|) := by
        rw [ENNReal.ofReal_add (by positivity) (abs_nonneg _),
          ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
        gcongr
        exact le_abs_self _
  have hfinal := hmain.trans hcint
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfinal

end RealPart

/-!
## The good part
-/

section Main

theorem mem_bulk_of_goodSet {p : BlockBand.Parameters} {i : ZMod p.n}
    {cst : CenterDomainConstants} {α : Fin p.N} {M₀ θ : ℝ} (hθ : 0 < θ) (hα : IsBulkRank p θ α)
    {x : SplitState p i × ℝ} (hx : x ∈ goodSet p i cst α M₀) :
    x.2 ∈ bulkInterval (Real.pi * θ / 4) := by
  have hE : x.2 ∈ bulkInterval (rankMargin p α) := hx.2.1.1
  have he := BlockBand.Window.Count.classicalLocation_mem_bulk p hθ hα
  unfold bulkInterval at hE he ⊢
  have habs : |classicalLocation p α| ≤ 2 - Real.pi * θ / 2 :=
    abs_le.2 ⟨by linarith [he.1], he.2⟩
  have hm : Real.pi * θ / 4 ≤ rankMargin p α := by unfold rankMargin; linarith
  exact ⟨by linarith [hE.1], by linarith [hE.2]⟩

/-- **Steps 1, 2, 4, 5 of the physical angular estimate**: `GoodPartStatement` for
`0 < θ < 1/2`, from `CoareaContract`, `FreshPalmContract`, `FreshEigenpairDensityContract`
and `DeterminantScoreStatement`. -/
theorem goodPart_of (hC : CoareaContract) (hP : FreshPalmContract)
    (hD : FreshEigenpairDensityContract) (hScore : DeterminantScoreStatement) {b θ T : ℝ}
    (hb : 0 < b) (hb' : b < 1 / 2) (hθ : 0 < θ) (hθ' : θ < 1 / 2) :
    GoodPartStatement b θ T hb hb' := by
  intro cst hcd R₀ M₀ _hR₀ hM₀
  obtain ⟨y₀, Cζ, hy₀, C₀, hC₀, hK⟩ :=
    center_angular_first_moment_goodDomain hP hD cst hcd hb hb' hθ hθ' hM₀
  obtain ⟨CK, hCK, hFM⟩ := hK 1 one_pos
  obtain ⟨r₀, s₀, v₀, y₁, Cr, -, -, hreg⟩ := hcd.regular b hb hb' θ hθ hθ'
  have hκ0 : 0 < Real.pi * θ / 4 := by positivity
  obtain ⟨Cs, hCs⟩ := hScore.moments b T θ (Real.pi * θ / 4) 1 hθ hκ0 one_pos (by norm_num)
  set s0 : ℝ := min (1 - 2 * b) b with hs0
  set σ : ℝ := max s0 s0⁻¹ with hσ
  set Kc : ℝ := compConst σ y₀⁻¹ Cζ C₀ (stepSixCutoff R₀) with hKc
  refine ⟨|Kc| * (1 + |T| * CK + |Cs|), by positivity, ?_⟩
  intro n W hn hW hnW
  obtain ⟨p, hp⟩ : ∃ p : BlockBand.Parameters, p = ⟨n, W, b, hn, hW, hb, hb'⟩ := ⟨_, rfl⟩
  rw [← hp]
  have hpb : p.b = b := by rw [hp]
  have hps : splitS p = s0 := by rw [hp]; rfl
  have hpn : (p.n : ℝ) ≤ T * p.W := by rw [hp]; exact hnW
  intro model α hα i X G hG φ M L hφ
  obtain ⟨U, hU⟩ := hC.frame_exists p i
  have hprob := BlockBand.QUE.PairResidual.extendedPairMeasure_isProbability p model α i X
  have hWpos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * p.W := by
    rw [card_pairSite]; push_cast; ring
  set r : ℝ := (p.n : ℝ) / 2 * CK * (Fintype.card (PairSite p i) : ℝ) ^ (-1 : ℝ) with hrdef
  have hr : 0 ≤ r := by positivity
  set K : ℝ := |Kc * (M + L) / Fintype.card (PairSite p i)| with hKdef
  set μ := extendedPairMeasure p α i X.P X.Hm
  have hpart : ∀ ρ : ℂ → ℝ, IsRealPart ρ →
      |∫ ω, obsOn cst α M₀ R₀ φ ρ X G ω ∂μ| ≤ K * (1 + 4 * r + |Cs|) := by
    intro ρ hρ
    refine abs_integral_obsOn_le hC hcd α M₀ R₀ hφ hρ X hG hU (abs_nonneg _) hr hκ0.le
      (fun x hx => mem_bulk_of_goodSet hθ hα hx) ?_
      (hCs p hpb hpn model α hα i _ (isPairSplitting_of_centerSplitting p i X G hG) U hU)
    intro ω' hR hV E hx
    have hH : (asm p i ω').IsHermitian := hx.1
    obtain ⟨hICD, h2, h3⟩ := hx.2
    have hRe := exteriorBlock_isHermitian p i hH
    have hdist : ∀ k, (p.W : ℝ) ^ (-M₀) ≤ |hRe.eigenvalues k - E| := fun k => by
      rw [abs_sub_comm]; exact h2 _ (det_sub_eigenvalue_eq_zero hRe k)
    obtain ⟨D, hDK, hDs, hDζ, hy, hζC, hFMD⟩ := hFM p hpb α hα i (asm p i ω') hH E hICD hdist
      ‖pairBlock p i (asm p i ω')‖ ‖couplingBlock p i (asm p i ω')‖ (norm_nonneg _)
      (norm_nonneg _) h3 (fun x => l2Norm_mulVec_le_opNorm _ x)
      (fun x => l2Norm_mulVec_le_opNorm _ x)
    have hdet : (exteriorBlock p i (asm p i ω') - (E : ℂ) • 1).det ≠ 0 := by
      intro h0
      have := h2 E h0
      rw [sub_self, abs_zero] at this
      linarith [Real.rpow_pos_of_pos hWpos (-M₀)]
    obtain ⟨-, -, -, -, -, -, -, hform⟩ := hreg p hpb α hα i (asm p i ω') hH E hdet hICD
    have hj : D.jStar (pairContrast p i) = dCH p i cst α (ω', E) := by
      rw [jStar_pairContrast_eq p i D cst α hDK hDs (by rw [hDζ]; exact hform)]
      unfold dCH
      rw [Set.indicator_of_mem (show (asm p i ω', E) ∈
        {y : p.SiteMatrix × ℝ | y.1.IsHermitian} from hH)]
    have hs1 : D.s ≤ σ := by rw [hDs, hps]; exact le_max_left _ _
    have hs2 : D.s⁻¹ ≤ σ := by rw [hDs, hps]; exact le_max_right _ _
    have hY : D.ζ.im⁻¹ ≤ y₀⁻¹ := inv_anti₀ hy₀ hy
    have hFMD' : ∀ w : PairSite p i → ℂ,
        ∫ v, Real.exp (D.expo v) * stepOneDensity p i α (splitS p) ω' E v * ‖star w ⬝ᵥ v‖ ^ 2
            ∂projectiveHaar (PairSite p i) ≤
          C₀ * ((∫ v, Real.exp (D.expo v) * stepOneDensity p i α (splitS p) ω' E v
              ∂projectiveHaar (PairSite p i)) + r) / Fintype.card (PairSite p i) *
            (star w ⬝ᵥ (D.Γ *ᵥ w)).re := fun w => by
      have h := hFMD U hU w
      rw [splitOf_asm] at h
      exact h
    exact fiber_bound hScore α hU hφ hρ (measurable_obsG hcd α M₀ R₀ hφ hρ) hR hV hx D hDK hDs hj
      hs1 hs2 hY hζC (by linarith) hr hFMD'
  -- the complex integrand
  set F : X.Ω → ℂ := fun ω => stepWeight p i cst α M₀ R₀ X G ω *
    angularIntegrand p i α X (centerOn p i cst α X G) φ ω with hFdef
  have hae : ∀ ρ : ℂ → ℝ, IsRealPart ρ → ∀ᵐ ω ∂μ, ρ (F ω) = obsOn cst α M₀ R₀ φ ρ X G ω :=
    fun ρ hρ => by
      filter_upwards [ae_residual_eigen α X G hG, ae_l2Norm_eigenvector p model α i X]
        with ω h1 h2
      exact obsG_pair cst α M₀ R₀ X G φ hρ ω h1.1 h2
  have hint : ∀ ρ : ℂ → ℝ, IsRealPart ρ → Integrable (obsOn cst α M₀ R₀ φ ρ X G) μ :=
    fun ρ hρ => Integrable.of_bound (measurable_obsOn hcd α M₀ R₀ hφ hρ X hG).aestronglyMeasurable
      (2 * M) (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_obsG_le hφ hρ (splitOf p i (residual p i X G ω),
          physicalOrderedEigenvalue p (X.Hm ω) α) (physicalOrderedEigenvector p (X.Hm ω) α))
  have hre : Integrable (fun ω => (F ω).re) μ :=
    (hint _ isRealPart_re).congr ((hae _ isRealPart_re).mono fun ω h => h.symm)
  have him : Integrable (fun ω => (F ω).im) μ :=
    (hint _ isRealPart_im).congr ((hae _ isRealPart_im).mono fun ω h => h.symm)
  have hFeq : F = fun ω => ((F ω).re : ℂ) + ((F ω).im : ℂ) * Complex.I :=
    funext fun ω => (Complex.re_add_im (F ω)).symm
  have hFi : Integrable F μ := by
    rw [hFeq]; exact hre.ofReal.add (him.ofReal.mul_const _)
  refine ⟨hFi, ?_⟩
  have hI : ∫ ω, F ω ∂μ = ((∫ ω, (F ω).re ∂μ : ℝ) : ℂ) + ((∫ ω, (F ω).im ∂μ : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [hFeq]
    rw [integral_add hre.ofReal (him.ofReal.mul_const _), integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal]
  have e1 : ∫ ω, (F ω).re ∂μ = ∫ ω, obsOn cst α M₀ R₀ φ Complex.re X G ω ∂μ :=
    integral_congr_ae (hae _ isRealPart_re)
  have e2 : ∫ ω, (F ω).im ∂μ = ∫ ω, obsOn cst α M₀ R₀ φ Complex.im X G ω ∂μ :=
    integral_congr_ae (hae _ isRealPart_im)
  have hM := IsAngularTest.bound_nonneg hφ
  have hL := IsAngularTest.lip_nonneg hφ
  have hK' : K = |Kc| * (M + L) / (2 * p.W) := by
    rw [hKdef, hcard, abs_div, abs_mul, abs_of_nonneg (by linarith : 0 ≤ M + L),
      abs_of_pos (by positivity : (0 : ℝ) < 2 * p.W)]
  have h4r : 4 * r ≤ |T| * CK := by
    rw [hrdef, hcard, Real.rpow_neg_one]
    have hT : (p.n : ℝ) ≤ |T| * p.W :=
      hpn.trans (mul_le_mul_of_nonneg_right (le_abs_self T) hWpos.le)
    rw [show 4 * ((p.n : ℝ) / 2 * CK * (2 * (p.W : ℝ))⁻¹) = (p.n : ℝ) * CK / p.W by
      field_simp; ring]
    rw [div_le_iff₀ hWpos]
    nlinarith
  calc ‖∫ ω, F ω ∂μ‖
      ≤ |∫ ω, (F ω).re ∂μ| + |∫ ω, (F ω).im ∂μ| := by
        rw [hI]
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ K * (1 + 4 * r + |Cs|) + K * (1 + 4 * r + |Cs|) := by
        rw [e1, e2]
        exact add_le_add (hpart _ isRealPart_re) (hpart _ isRealPart_im)
    _ = |Kc| * (1 + 4 * r + |Cs|) * (M + L) / p.W := by
        rw [hK']; field_simp; ring
    _ ≤ |Kc| * (1 + |T| * CK + |Cs|) * (M + L) / p.W := by
        gcongr

/-- The good part at `min θ (1/4)`, the form consumed by `Assembly.physicalAngularLabel_of`. -/
theorem goodPart_min_of (hC : CoareaContract) (hP : FreshPalmContract)
    (hD : FreshEigenpairDensityContract) (hScore : DeterminantScoreStatement) {b θ T : ℝ}
    (hb : 0 < b) (hb' : b < 1 / 2) (hθ : 0 < θ) :
    GoodPartStatement b (min θ (1 / 4)) T hb hb' :=
  goodPart_of hC hP hD hScore hb hb' (lt_min hθ (by norm_num))
    ((min_le_right θ (1 / 4)).trans_lt (by norm_num))

/-- **The physical angular estimate** `PhysicalAngularLabel` for `0 < θ`: the good part is
proved from `CoareaContract`, `FreshPalmContract`, `FreshEigenpairDensityContract` and
`DeterminantScoreStatement`; the other hypotheses are `PairPoleExclusionContract` and the
two Gaussian tails `GUENormTailStatement` and `PairRowNormTailStatement` (proved as
`gueNormTail_holds` and `pairRowNormTail_holds`). -/
theorem physicalAngularLabel_of_contracts (hC : CoareaContract) (hP : FreshPalmContract)
    (hD : FreshEigenpairDensityContract) (hScore : DeterminantScoreStatement) {b θ T : ℝ}
    (hb : 0 < b) (hb' : b < 1 / 2) (hθ : 0 < θ)
    (hTail : BlockBand.DeterminantScore.GUENormTail.GUENormTailStatement)
    (hRow : PairRowNormTailStatement) (hPole : PairPoleExclusionContract) :
    PhysicalAngularLabel b θ T hb hb' :=
  physicalAngularLabel_of hb hb' hθ (goodPart_min_of hC hP hD hScore hb hb' hθ) hTail hRow hPole

end Main

end BlockBand.Angular.AssemblyGood
