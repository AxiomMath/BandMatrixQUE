module

public import BlockBand.DeterminantScore.PhysicalColumnInner

/-!
# The physical column: restoring the three pair laws

In the complete coarea formula the regression, energy, vector and pair weight `n/2` are fixed on
the row; integrating the unchanged base restores three pair laws, each of mass at most one. The
only hypothesis is `CoareaContract`.

* Joint measurability of the pair-law integrand (`measurable_angularWeight`,
  `measurable_outerM`, `measurable_secInt`), so that the nested `E`, `v`, `ω` integrals of
  `outerInt` are additive (`outerInt_add`, `outerInt_const_mul`).
* `outerInt_sector_le_one`: the base `c_{d,t}𝓡(n/2)` integrated against a sector weight
  `det² 1{N_-(M) + N_-(H_R - E) = ℓ}` has mass `≤ 1`: for `ℓ < N` it is the pair-law total mass
  (`pairExpect_one_eq`, `CoareaContract.pairLaw_measure` with `Φ₀ = 1`, `pairLaw_probability`);
  for `ℓ ≥ N` the sector is empty (`N_-(M) + N_-(H_R - E) ≤ (2W-1) + (N-2W) < N`).
* `pairExpect_le`: a fixed-`θ` bound by `B` times the three neighbouring sector masses (for
  Hermitian blocks and unit `v`, which is almost sure) gives `E♯[Ψ] ≤ 3B`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.PhysicalColumn

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Angular.FiberAngular BlockBand.DeterminantScore.Sector
open scoped ENNReal NNReal

variable {p : Parameters} {i : ZMod p.n}

/-!
## Measurability
-/

section MatrixMeasurable

variable {X : Type*} [MeasurableSpace X] {m n o : Type} [Fintype m] [Fintype n] [Fintype o]

theorem measurable_entry {A : X → Matrix m n ℂ} (hA : Measurable A) (a : m) (b : n) :
    Measurable fun x => A x a b :=
  (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hA)

theorem measurable_of_entry {A : X → Matrix m n ℂ} (h : ∀ a b, Measurable fun x => A x a b) :
    Measurable A :=
  measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => h a b

theorem measurable_matMul {A : X → Matrix m n ℂ} {B : X → Matrix n o ℂ} (hA : Measurable A)
    (hB : Measurable B) : Measurable fun x => A x * B x :=
  measurable_of_entry fun a c => by
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun k _ => (measurable_entry hA a k).mul (measurable_entry hB k c)

theorem measurable_matConjT {A : X → Matrix m n ℂ} (hA : Measurable A) :
    Measurable fun x => (A x)ᴴ :=
  measurable_of_entry fun a b => by
    simp only [conjTranspose_apply]
    exact continuous_star.measurable.comp (measurable_entry hA b a)

theorem measurable_matAdd {A B : X → Matrix m n ℂ} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => A x + B x :=
  measurable_of_entry fun a b => by
    simp only [Matrix.add_apply]
    exact (measurable_entry hA a b).add (measurable_entry hB a b)

theorem measurable_matSub {A B : X → Matrix m n ℂ} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => A x - B x :=
  measurable_of_entry fun a b => by
    simp only [Matrix.sub_apply]
    exact (measurable_entry hA a b).sub (measurable_entry hB a b)

theorem measurable_smul_one [DecidableEq m] {E : X → ℝ} (hE : Measurable E) :
    Measurable fun x => ((E x : ℂ)) • (1 : Matrix m m ℂ) :=
  measurable_of_entry fun a b => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact (Complex.measurable_ofReal.comp hE).mul_const _

theorem measurable_mulVec' {A : X → Matrix m n ℂ} {v : X → n → ℂ} (hA : Measurable A)
    (hv : Measurable v) : Measurable fun x => A x *ᵥ v x :=
  measurable_pi_iff.mpr fun a => by
    simp only [mulVec, dotProduct]
    exact Finset.measurable_sum _ fun b _ =>
      (measurable_entry hA a b).mul ((measurable_pi_apply b).comp hv)

theorem measurable_regressionFactor [DecidableEq m] (t : ℝ) {E : X → ℝ} {v : X → m → ℂ}
    {F : X → Matrix m m ℂ} (hE : Measurable E) (hv : Measurable v) (hF : Measurable F) :
    Measurable fun x => regressionFactor t (E x) (v x) (F x) := by
  unfold regressionFactor
  have hmv := measurable_mulVec' hF hv
  have ha : Measurable fun x => star (v x) ⬝ᵥ (F x *ᵥ v x) := by
    simp only [dotProduct, Pi.star_apply]
    exact Finset.measurable_sum _ fun k _ =>
      (continuous_star.measurable.comp ((measurable_pi_apply k).comp hv)).mul
        ((measurable_pi_apply k).comp hmv)
  have hw : Measurable fun x => F x *ᵥ v x - (star (v x) ⬝ᵥ (F x *ᵥ v x)) • v x :=
    measurable_pi_iff.mpr fun k => by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact ((measurable_pi_apply k).comp hmv).sub (ha.mul ((measurable_pi_apply k).comp hv))
  exact Real.measurable_exp.comp ((((hE.sub (Complex.measurable_re.comp ha)).pow_const 2).add
    (measurable_const.mul ((BlockBand.Angular.ConeDivergence.measurable_l2Norm.comp
      hw).pow_const 2))).neg.div_const _)

end MatrixMeasurable

theorem measurable_physF :
    Measurable fun z : SplitState p i × ℝ => physicalCoareaF z.1.1 z.1.2.1 z.1.2.2 z.2 := by
  unfold physicalCoareaF physicalCoareaResolvent
  have hres : Measurable fun z : SplitState p i × ℝ =>
      (z.1.1 - (z.2 : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ))⁻¹ :=
    measurable_inv_matrix.comp (measurable_matSub measurable_fst.fst
      (measurable_smul_one measurable_snd))
  exact measurable_matSub measurable_fst.snd.snd (measurable_matMul (measurable_matMul
    (measurable_matConjT measurable_fst.snd.fst) hres) measurable_fst.snd.fst)

theorem measurable_angularWeight (s : ℝ) :
    Measurable fun θ : OuterData p i => angularWeight p i s θ.1 θ.2.1 θ.2.2 := by
  unfold angularWeight
  have hF : Measurable fun θ : OuterData p i => physicalCoareaF θ.1.1 θ.1.2.1 θ.1.2.2 θ.2.1 :=
    measurable_physF.comp (measurable_fst.prodMk measurable_snd.fst)
  have h := measurable_regressionFactor (pairTime p s : ℝ) measurable_snd.fst measurable_snd.snd hF
  exact (measurable_const.mul h).mul measurable_const

theorem measurable_outerM {U : FrameMap p i} (hU : Measurable U) :
    Measurable fun z : OuterData p i × FrameMatrix p => outerM U z.1 z.2 := by
  unfold outerM frameM
  have hUv : Measurable fun z : OuterData p i × FrameMatrix p => U z.1.2.2 :=
    hU.comp measurable_fst.snd.snd
  have hF : Measurable fun z : OuterData p i × FrameMatrix p =>
      physicalCoareaF z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2.1 :=
    measurable_physF.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)
  exact measurable_matSub (measurable_matAdd (measurable_matMul (measurable_matMul
    (measurable_matConjT hUv) hF) hUv) measurable_snd) (measurable_smul_one measurable_fst.snd.fst)

theorem measurable_nR : Measurable fun θ : OuterData p i => nR θ :=
  BlockBand.Angular.DetFactor.measurable_negativeCount_nat.comp
    (measurable_matSub measurable_fst.fst (measurable_smul_one measurable_snd.fst))

theorem measurable_secInt {U : FrameMap p i} (hU : Measurable U) (ℓ : ℕ) :
    Measurable fun z : OuterData p i × FrameMatrix p =>
      ENNReal.ofReal (secW (nR z.1) ℓ (outerM U z.1 z.2)) := by
  have hM := measurable_outerM hU
  have hN : Measurable fun z : OuterData p i × FrameMatrix p =>
      negativeCount (outerM U z.1 z.2) + nR z.1 :=
    (measurable_of_countable (fun x : ℕ × ℕ => x.1 + x.2)).comp
      ((BlockBand.Angular.DetFactor.measurable_negativeCount_nat.comp hM).prodMk
        (measurable_nR.comp measurable_fst))
  refine ENNReal.measurable_ofReal.comp ?_
  unfold secW
  exact ((Complex.continuous_normSq.comp continuous_id.matrix_det).measurable.comp hM).mul
    (Measurable.ite ((measurableSet_singleton ℓ).preimage hN) measurable_const measurable_const)

/-- The base weight times a sector mass, `c_{d,t}𝓡(n/2) · E_{G'}[det² 1{sector ℓ}]`. -/
def sectorTerm (s : ℝ) (U : FrameMap p i) (ℓ : ℕ) (θ : OuterData p i) : ℝ≥0∞ :=
  ENNReal.ofReal (angularWeight p i s θ.1 θ.2.1 θ.2.2) * zNat s U ℓ θ

theorem measurable_sectorTerm (s : ℝ) {U : FrameMap p i} (hU : Measurable U) (ℓ : ℕ) :
    Measurable (sectorTerm s U ℓ) := by
  have := isProbabilityMeasure_gue (FrameIndex p) (pairTime p s)
  exact (ENNReal.measurable_ofReal.comp (measurable_angularWeight s)).mul
    (measurable_secInt hU ℓ).lintegral_prod_right'

/-!
## The nested outer integral
-/

/-- `∫dPω ∫dE ∫ν(dv) f(ω, E, v)`. -/
def outerInt (Pω : Measure (SplitState p i)) (f : OuterData p i → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ om, ∫⁻ E, ∫⁻ v, f (om, E, v) ∂projectiveHaar (PairSite p i) ∂volume ∂Pω

theorem measurable_outer_v {f : OuterData p i → ℝ≥0∞} (hf : Measurable f) (om : SplitState p i)
    (E : ℝ) : Measurable fun v => f (om, E, v) :=
  hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))

theorem measurable_outer_E {f : OuterData p i → ℝ≥0∞} (hf : Measurable f) (om : SplitState p i) :
    Measurable fun E => ∫⁻ v, f (om, E, v) ∂projectiveHaar (PairSite p i) := by
  have := BlockBand.Angular.ProjectiveStein.isProbabilityMeasure_projectiveHaar (ι := PairSite p i)
  exact (hf.comp (measurable_const.prodMk measurable_id)).lintegral_prod_right'

theorem measurable_outer_om {f : OuterData p i → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun om => ∫⁻ E, ∫⁻ v, f (om, E, v) ∂projectiveHaar (PairSite p i) ∂volume := by
  have := BlockBand.Angular.ProjectiveStein.isProbabilityMeasure_projectiveHaar (ι := PairSite p i)
  have h1 : Measurable fun z : SplitState p i × ℝ =>
      ∫⁻ v, f (z.1, z.2, v) ∂projectiveHaar (PairSite p i) :=
    (hf.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).lintegral_prod_right'
  exact h1.lintegral_prod_right'

theorem outerInt_add (Pω : Measure (SplitState p i)) {f : OuterData p i → ℝ≥0∞}
    (g : OuterData p i → ℝ≥0∞) (hf : Measurable f) :
    outerInt Pω (fun θ => f θ + g θ) = outerInt Pω f + outerInt Pω g := by
  unfold outerInt
  rw [← lintegral_add_left (measurable_outer_om hf)]
  refine lintegral_congr fun om => ?_
  rw [← lintegral_add_left (measurable_outer_E hf om)]
  refine lintegral_congr fun E => ?_
  exact lintegral_add_left (measurable_outer_v hf om E) _

theorem outerInt_const_mul (Pω : Measure (SplitState p i)) (c : ℝ≥0∞) {f : OuterData p i → ℝ≥0∞}
    (hf : Measurable f) : outerInt Pω (fun θ => c * f θ) = c * outerInt Pω f := by
  unfold outerInt
  rw [← lintegral_const_mul c (measurable_outer_om hf)]
  refine lintegral_congr fun om => ?_
  rw [← lintegral_const_mul c (measurable_outer_E hf om)]
  refine lintegral_congr fun E => ?_
  exact lintegral_const_mul c (measurable_outer_v hf om E)

/-!
## Sector masses
-/

theorem negativeCount_le_card {κ : Type} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℂ) :
    negativeCount M ≤ Fintype.card κ := by
  unfold negativeCount
  split_ifs
  · exact (Finset.card_filter_le _ _).trans (by simp)
  · exact Nat.zero_le _

theorem card_exteriorSite : Fintype.card (ExteriorSite p i) = p.N - 2 * p.W := by
  rw [Fintype.card_subtype_compl, card_pairSite]
  simp [Parameters.N, Parameters.Site, ZMod.card]

theorem negativeCount_add_nR_lt (U : FrameMap p i) (θ : OuterData p i) (G' : FrameMatrix p) :
    negativeCount (outerM U θ G') + nR θ < p.N := by
  have h1 := negativeCount_le_card (outerM U θ G')
  have h2 := negativeCount_le_card (θ.1.1 - (θ.2.1 : ℂ) • 1)
  rw [Fintype.card_fin] at h1
  rw [card_exteriorSite] at h2
  have hW := p.W_pos
  have hN : 2 * p.W ≤ p.N := by
    unfold Parameters.N; have := p.n_ge_four; nlinarith
  unfold nR
  omega

/-- The pair-law integral of `1` is the coarea right side with crossing factor `n/2`. -/
theorem pairExpect_one_eq (α : Fin p.N) (s : ℝ) (U : FrameMap p i)
    (Pω : Measure (SplitState p i)) :
    pairExpect α s U Pω (fun _ _ => 1) =
      coareaRHS p α i s Pω U (fun _ _ _ => (p.n : ℝ) / 2) (fun _ _ => 1) := by
  unfold pairExpect coareaRHS coareaFiber
  refine lintegral_congr fun om => lintegral_congr fun E => lintegral_congr fun v =>
    lintegral_congr fun G' => ?_
  have ha := angularWeight_nonneg p i s om E v
  simp only [mul_one]
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
    simp only [hsw, h, ↓reduceIte, ENNReal.ofReal_zero, mul_zero]

/-- **Each restored pair law has mass at most one.** -/
theorem outerInt_sector_le_one (hC : CoareaContract) {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hPω : IsPairSplitting p i model (splitS p) Pω)
    {U : FrameMap p i} (hU : IsPairFrame p i U) (ℓ : ℕ) :
    outerInt Pω (sectorTerm (splitS p) U ℓ) ≤ 1 := by
  by_cases hℓ : ℓ < p.N
  · have h1 : outerInt Pω (sectorTerm (splitS p) U ℓ) =
        pairExpect ⟨ℓ, hℓ⟩ (splitS p) U Pω (fun _ _ => 1) := by
      unfold outerInt pairExpect
      refine lintegral_congr fun om => lintegral_congr fun E => lintegral_congr fun v => ?_
      unfold sectorTerm zNat
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun G' => ?_
      rw [sectorWeight_eq, mul_one]
    have h2 := hC.pairLaw_measure p model ⟨ℓ, hℓ⟩ i (splitS p)
      (BlockBand.Angular.PairCoareaBridge.splitS_pos p) le_rfl Pω hPω U hU (fun _ => 1)
      measurable_const
    have hprob := hC.pairLaw_probability p model ⟨ℓ, hℓ⟩ i
    rw [h1, pairExpect_one_eq, ← h2, lintegral_const, measure_univ, one_mul]
  · refine le_trans (le_of_eq ?_) zero_le_one
    unfold outerInt
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun om => ?_)
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun E => ?_)
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun v => ?_)
    unfold sectorTerm zNat
    have h0 : (∫⁻ G', ENNReal.ofReal (secW (nR (om, E, v)) ℓ (outerM U (om, E, v) G'))
        ∂gueMeasure (FrameIndex p) (pairTime p (splitS p))) = 0 := by
      refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun G' => ?_)
      have hlt := negativeCount_add_nR_lt U (om, E, v) G'
      have hne : ¬ negativeCount (outerM U (om, E, v) G') + nR (om, E, v) = ℓ := by omega
      simp [secW, hne]
    simp [h0]

/-!
## The outer assembly
-/

/-- **Restoring the three pair laws.** A fixed-`θ` bound by `B` times the three neighbouring
sector masses, for Hermitian blocks and unit `v`, gives `E♯_{α,S}[Ψ] ≤ 3B`. -/
theorem pairExpect_le (hC : CoareaContract) {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hPω : IsPairSplitting p i model (splitS p) Pω)
    {U : FrameMap p i} (hU : IsPairFrame p i U) (α : Fin p.N)
    (Ψ : OuterData p i → FrameMatrix p → ℝ≥0∞) (B : ℝ≥0∞)
    (h : ∀ θ : OuterData p i, θ.1.1.IsHermitian → θ.1.2.2.IsHermitian → l2Norm θ.2.2 = 1 →
      (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') * Ψ θ G'
          ∂gueMeasure (FrameIndex p) (pairTime p (splitS p))) ≤
        B * (zNat (splitS p) U (α.val - 1) θ + zNat (splitS p) U α.val θ +
          zNat (splitS p) U (α.val + 1) θ)) :
    pairExpect α (splitS p) U Pω Ψ ≤ 3 * B := by
  set s := splitS p
  have hm := fun ℓ => measurable_sectorTerm s hU.1 ℓ
  have step : pairExpect α s U Pω Ψ ≤ outerInt Pω (fun θ => B *
      (sectorTerm s U (α.val - 1) θ + sectorTerm s U α.val θ + sectorTerm s U (α.val + 1) θ)) := by
    unfold pairExpect outerInt
    refine lintegral_mono_ae ?_
    filter_upwards [ae_hermitian_of_isPairSplitting p i hPω] with om hom
    refine lintegral_mono fun E => ?_
    refine lintegral_mono_ae ?_
    filter_upwards [BlockBand.Angular.ProjectiveStein.ae_projectiveHaar_unit
      (ι := PairSite p i)] with v hv
    have hl2 : l2Norm v = 1 := by
      unfold l2Norm
      rw [show (∑ k, ‖v k‖ ^ 2) = BlockBand.Angular.ProjectiveStein.normSqSum v from rfl, hv,
        Real.sqrt_one]
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (angularWeight p i s om E v) * ∫⁻ G',
          ENNReal.ofReal (sectorWeight α U (om, E, v) G') * Ψ (om, E, v) G'
          ∂gueMeasure (FrameIndex p) (pairTime p s)
        ≤ ENNReal.ofReal (angularWeight p i s om E v) *
          (B * (zNat s U (α.val - 1) (om, E, v) + zNat s U α.val (om, E, v) +
            zNat s U (α.val + 1) (om, E, v))) :=
          mul_le_mul_right (h (om, E, v) hom.1 hom.2 hl2) _
      _ = _ := by unfold sectorTerm; ring
  have h1 := outerInt_sector_le_one hC hPω hU (α.val - 1)
  have h2 := outerInt_sector_le_one hC hPω hU α.val
  have h3 := outerInt_sector_le_one hC hPω hU (α.val + 1)
  calc pairExpect α s U Pω Ψ ≤ _ := step
    _ = B * (outerInt Pω (sectorTerm s U (α.val - 1)) + outerInt Pω (sectorTerm s U α.val) +
          outerInt Pω (sectorTerm s U (α.val + 1))) := by
        rw [outerInt_const_mul Pω B (f := fun θ => sectorTerm s U (α.val - 1) θ +
            sectorTerm s U α.val θ + sectorTerm s U (α.val + 1) θ) (((hm _).add (hm _)).add (hm _)),
          outerInt_add Pω (sectorTerm s U (α.val + 1)) (f := fun θ => sectorTerm s U (α.val - 1) θ +
            sectorTerm s U α.val θ) ((hm _).add (hm _)),
          outerInt_add Pω (sectorTerm s U α.val) (hm _)]
    _ ≤ B * (1 + 1 + 1) := mul_le_mul_right (add_le_add (add_le_add h1 h2) h3) _
    _ = 3 * B := by rw [mul_comm]; norm_num

end BlockBand.DeterminantScore.PhysicalColumn
