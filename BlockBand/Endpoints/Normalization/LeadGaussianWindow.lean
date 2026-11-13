module

public import BlockBand.Endpoints.Normalization.LeadGaussianEnergy
public import BlockBand.Endpoints.Normalization.LeadProfileAssemblyAtom

/-!
# The physical lead-profile theorem: the removed-block mass under the windowed Palm law

Under the block-`0` Palm law the removed-block expectation is `n E Σ_α |w(u_α)| p_{α0}²`, equal by
cyclic symmetry to the vanishing block-atom statistic; the normalizer and Gaussian-ratios theorems
transfer the same bounded mass ratio to the Gaussian field.

**Main results.**
* `window_massObs_comparison` (from `OneBlockPalmContract` (`massReal`, `upper`) and
  `OneBlockNormalizerContract` (`tv`)): the window comparison of
  `physicalOneMark_window_comparison` for an arbitrary bounded measurable mass-vector observable
  `g`: with `A` representing `Σ_ℓ 𝒜⁰_ℓ[g(p)] = Z₀ A`,
  `|n E Σ_α p_{α0} w(u_α) g(p_α) - ∫ A(e(u), ω) d𝔭_W| ≤ M ε`.
* `nsmul_blockZero_sq_eq` (cyclic invariance): for bounded measurable `w`,
  `n E Σ_α w(u_α) p_{α0}² = E Σ_α w(u_α) Σ_k p_{αk}²`.
* `exists_smooth_dominating`: a continuous compactly supported `w ≥ 0` is dominated by a smooth
  compactly supported `w̃ ≥ 0`.
* `blockZero_mass_le_blockAtom`: `n E Σ_α p_{α0} w(u_α) min(1, max(0, p_{α0})) ≤
  blockAtomStatistic R E w̃` for `0 ≤ w ≤ w̃`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

namespace LeadGaussian

open MeasureTheory Matrix Filter Topology
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal BoundedContinuousFunction

section Window

variable (p : Parameters)

theorem isBoundedCompactEnergy_massObs {E : ℝ} (h1 : -2 < E) (h2 : E < 2) {w : ℝ → ℝ}
    (hc : Continuous w) (hs : HasCompactSupport w) (g : (ZMod p.n → ℝ) → ℝ) (Mg : ℝ)
    (hMg : ∀ q, |g q| ≤ Mg) :
    IsBoundedCompactEnergy (fun e q => w (microCoord p E e) * g q) := by
  obtain ⟨M, R, hM0, hM, hR⟩ := exists_bound_support_of_compact hc hs
  have hρ := semicircleDensity_pos h1 h2
  have hN : (0 : ℝ) < p.N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p.N)
  have hκ : 0 < (p.N : ℝ) * Parameters.semicircleDensity E := mul_pos hN hρ
  refine ⟨⟨M * Mg, fun e q => ?_⟩, ⟨|E| + |R| / ((p.N : ℝ) * Parameters.semicircleDensity E),
    fun e q he => ?_⟩⟩
  · rw [abs_mul]
    exact mul_le_mul (hM _) (hMg _) (abs_nonneg _) hM0
  · simp only
    rw [hR, zero_mul]
    unfold microCoord
    rw [abs_mul, abs_of_pos hκ]
    have hd : |R| / ((p.N : ℝ) * Parameters.semicircleDensity E) < |e - E| := by
      have := abs_sub_abs_le_abs_sub e E
      linarith
    have := (div_lt_iff₀' hκ).mp hd
    linarith [le_abs_self R]

/-- **The window comparison for a general mass-vector observable**, from `OneBlockPalmContract`
(`massReal`, `upper`) and `OneBlockNormalizerContract` (`tv`). -/
theorem window_massObs_comparison (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ)
    (h1 : -2 < E) (h2 : E < 2) (T : ℝ) (w : ℝ → ℝ) (hw : IsWindow w) (M : ℝ) (hM : 0 < M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
      ∀ (R : FiniteRealization p) (Pω : Measure (BlockState p 0)),
      IsBlockSplitting p 0 R.model Pω →
      ∀ (U : (BlockSite p 0 → ℂ) → Matrix (BlockSite p 0) (BlockFrameIndex p) ℂ),
      IsBlockFrame p 0 U →
      ∀ (g : (ZMod p.n → ℝ) → ℝ), Measurable g → ∀ Mg : ℝ, (∀ q, |g q| ≤ Mg) →
      ∀ A : ℝ → BlockState p 0 → ℝ, Measurable (Function.uncurry A) → (∀ e ω, |A e ω| ≤ M) →
      (∀ᵐ ω ∂Pω, ∀ e, ∑ ℓ ∈ Finset.range p.W,
          blockSectorFiberReal p 0 U ω e ℓ (fun v => g (blockReconMass p 0 ω e v)) =
        (blockNormalizer p 0 U ω e).toReal * A e ω) →
        |(p.n : ℝ) * (∫ H, ∑ α : Fin p.N, physicalOrderedBlockMass p H α 0 *
              (w (microCoord p E (physicalOrderedEigenvalue p H α)) *
                g (blockMassVector p H α)) ∂(R.model.law : Measure p.SiteMatrix)) -
            ∫ x, A (microEnergy p E x.1) x.2 ∂priorWindowMeasure Pω w| ≤ M * ε := by
  obtain ⟨W₀, hW₀⟩ := hNorm.tv b hb hb' E h1 h2 T w hw ε hε
  obtain ⟨C, hC⟩ := hPalm.upper b hb hb'
  refine ⟨W₀, fun p hpb hW hn R Pω hsplit U hU g hg Mg hMg A hAm hAb hAeq => ?_⟩
  have hprob := isProbabilityMeasure_blockSplitting p R.model 0 hsplit
  have hZB : ∀ᵐ ω ∂Pω, ∀ e, blockNormalizer p 0 U ω e ≤ ENNReal.ofReal (C * p.W) := by
    filter_upwards [ae_blockSplit_isHermitian p R.model 0 hsplit] with ω hω
    exact hC p hpb 0 U hU ω hω
  have hw0 : ∀ u, 0 ≤ w u := hw.2.2.1
  set dens : ℝ × BlockState p 0 → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((p.n : ℝ) * w (microCoord p E x.1)) * blockNormalizer p 0 U x.2 x.1
  have hdens_meas : Measurable dens :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul
      (hw.1.measurable.comp ((measurable_microCoord (p := p) E).comp measurable_fst)))).mul
      (measurable_blockNormalizer_joint p 0 U hU.1)
  have hZBprod : ∀ᵐ x ∂(volume.prod Pω), ∀ e,
      blockNormalizer p 0 U x.2 e ≤ ENNReal.ofReal (C * p.W) :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := Pω)).ae
      (p := fun ω => ∀ e, blockNormalizer p 0 U ω e ≤ ENNReal.ofReal (C * p.W)) hZB
  have hdens_fin : ∀ᵐ x ∂(volume.prod Pω), dens x < ∞ := by
    filter_upwards [hZBprod] with x hx
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt (hx x.1) ENNReal.ofReal_lt_top)
  have hdens_toReal : ∀ x, (dens x).toReal =
      (p.n : ℝ) * w (microCoord p E x.1) * (blockNormalizer p 0 U x.2 x.1).toReal := by
    intro x
    simp only [dens, ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity) (hw0 _))]
  -- the one-block Palm formula
  have hf_meas : Measurable (Function.uncurry fun e q => w (microCoord p E e) * g q) :=
    (hw.1.measurable.comp ((measurable_microCoord (p := p) E).comp measurable_fst)).mul
      (hg.comp measurable_snd)
  have h1a := hPalm.massReal p R.model 0 Pω hsplit U hU (fun e q => w (microCoord p E e) * g q)
    hf_meas (isBoundedCompactEnergy_massObs p h1 h2 hw.1 hw.2.1 g Mg hMg)
  have hrep : (p.n : ℝ) * (∫ H, ∑ α : Fin p.N, physicalOrderedBlockMass p H α 0 *
        (w (microCoord p E (physicalOrderedEigenvalue p H α)) * g (blockMassVector p H α))
        ∂(R.model.law : Measure p.SiteMatrix)) =
      ∫ ω, ∫ e : ℝ, (dens (e, ω)).toReal * A e ω ∂volume ∂Pω := by
    rw [h1a, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hAeq] with ω hω
    rw [← integral_const_mul]
    congr 1
    funext e
    have hpull : ∑ ℓ ∈ Finset.range p.W, blockSectorFiberReal p 0 U ω e ℓ
        (fun v => w (microCoord p E e) * g (blockReconMass p 0 ω e v)) =
        w (microCoord p E e) * ∑ ℓ ∈ Finset.range p.W,
          blockSectorFiberReal p 0 U ω e ℓ (fun v => g (blockReconMass p 0 ω e v)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      exact blockSectorFiberReal_const_mul p 0 U ω e ℓ _ _
    rw [hpull, hω e, hdens_toReal]
    ring
  have hint : Integrable (fun x : ℝ × BlockState p 0 => (dens x).toReal * A x.1 x.2)
      (volume.prod Pω) := by
    have hg' : Integrable (fun x : ℝ × BlockState p 0 =>
        (p.n : ℝ) * (max C 0 * p.W) * M * w (microCoord p E x.1)) (volume.prod Pω) :=
      ((integrable_window_microCoord p h1 h2 hw).const_mul _).comp_fst Pω
    refine hg'.mono' ((ENNReal.measurable_toReal.comp hdens_meas).mul hAm).aestronglyMeasurable ?_
    filter_upwards [hZBprod] with x hx
    rw [Real.norm_eq_abs, abs_mul, hdens_toReal, abs_of_nonneg (by
      have := hw0 (microCoord p E x.1); positivity)]
    have hZ : (blockNormalizer p 0 U x.2 x.1).toReal ≤ max C 0 * p.W := by
      have hWp : (0 : ℝ) ≤ p.W := by positivity
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ((hx x.1).trans
        (ENNReal.ofReal_le_ofReal ?_))
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hWp
    have hwx := hw0 (microCoord p E x.1)
    have hAx := hAb x.1 x.2
    calc (p.n : ℝ) * w (microCoord p E x.1) * (blockNormalizer p 0 U x.2 x.1).toReal *
          |A x.1 x.2| ≤ (p.n : ℝ) * w (microCoord p E x.1) * (max C 0 * p.W) * M := by
          gcongr
      _ = _ := by ring
  have hwin : ∫ x, A x.1 x.2 ∂blockWindowMeasure p 0 U Pω E w =
      (p.n : ℝ) * (∫ H, ∑ α : Fin p.N, physicalOrderedBlockMass p H α 0 *
        (w (microCoord p E (physicalOrderedEigenvalue p H α)) * g (blockMassVector p H α))
        ∂(R.model.law : Measure p.SiteMatrix)) := by
    rw [hrep]
    unfold blockWindowMeasure
    rw [integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_fin]
    simp only [smul_eq_mul]
    exact integral_prod_symm _ hint
  have hF : Measurable (fun x : ℝ × BlockState p 0 => A (microEnergy p E x.1) x.2 / M) := by
    have : Measurable (fun x : ℝ × BlockState p 0 => (microEnergy p E x.1, x.2)) := by
      refine Measurable.prodMk ?_ measurable_snd
      unfold microEnergy
      exact measurable_const.add (measurable_fst.div_const _)
    exact (hAm.comp this).div_const M
  have hF1 : ∀ x : ℝ × BlockState p 0, |A (microEnergy p E x.1) x.2 / M| ≤ 1 := by
    intro x
    rw [abs_div, abs_of_pos hM, div_le_one hM]
    exact hAb _ _
  have htv := hW₀ p hpb hW hn R.model 0 Pω hsplit U hU _ hF hF1
  simp only [microEnergy_microCoord p h1 h2] at htv
  rw [integral_div, integral_div, hwin, ← sub_div, abs_div, abs_of_pos hM,
    div_le_iff₀ hM] at htv
  linarith

end Window

section Cyclic

variable {p : Parameters}

theorem integrable_weight_blockMass_sq (model : p.GaussianRingModel) (E : ℝ) {w : ℝ → ℝ}
    (hw : Measurable w) (Mw : ℝ) (hMw : ∀ x, |w x| ≤ Mw) (k : ZMod p.n) :
    Integrable (fun H => ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
      physicalOrderedBlockMass p H α k ^ 2) (model.law : Measure p.SiteMatrix) := by
  refine integrable_finsetSum _ fun α _ => ?_
  have hm : Measurable fun H => w (microCoord p E (physicalOrderedEigenvalue p H α)) *
      physicalOrderedBlockMass p H α k ^ 2 :=
    (hw.comp ((measurable_microCoord (p := p) E).comp
      (measurable_physicalOrderedEigenvalue p α))).mul
      ((measurable_physicalOrderedBlockMass p α k).pow_const 2)
  refine (integrable_const Mw).mono' hm.aestronglyMeasurable ?_
  filter_upwards [BlockBand.QUE.Fourier.physical_mass_le_one_ae p model α] with H hH
  rw [Real.norm_eq_abs, abs_mul]
  have h0 := physicalOrderedBlockMass_nonneg p H α k
  have h1 := hH k
  have : |physicalOrderedBlockMass p H α k ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  calc |w (microCoord p E (physicalOrderedEigenvalue p H α))| *
        |physicalOrderedBlockMass p H α k ^ 2| ≤ Mw * 1 := by
        gcongr
        · exact (abs_nonneg _).trans (hMw 0)
        · exact hMw _
    _ = Mw := mul_one _

/-- **Cyclic symmetry of the block atom**: for bounded measurable `w`,
`n E Σ_α w(u_α) p_{α0}² = E Σ_α w(u_α) Σ_k p_{αk}²`. Unconditional. -/
theorem nsmul_blockZero_sq_eq (R : FiniteRealization p) (E : ℝ) {w : ℝ → ℝ}
    (hw : Measurable w) (Mw : ℝ) (hMw : ∀ x, |w x| ≤ Mw) :
    (p.n : ℝ) * ∫ H, ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
        physicalOrderedBlockMass p H α 0 ^ 2 ∂(R.model.law : Measure p.SiteMatrix) =
      ∫ H, ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
        ∑ k : ZMod p.n, physicalOrderedBlockMass p H α k ^ 2
        ∂(R.model.law : Measure p.SiteMatrix) := by
  set μ := (R.model.law : Measure p.SiteMatrix)
  set f : ZMod p.n → p.SiteMatrix → ℝ := fun k H => ∑ α : Fin p.N,
    w (microCoord p E (physicalOrderedEigenvalue p H α)) * physicalOrderedBlockMass p H α k ^ 2
  have hk : ∀ k, ∫ H, f k H ∂μ = ∫ H, f 0 H ∂μ := by
    intro k
    rw [← integral_comp_cyclic R.model k (f 0)]
    apply integral_congr_ae
    filter_upwards [R.model.isPhysical.1, R.model.ae_charpoly_separable] with H hH hsep
    simp only [f]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [BlockBand.QUE.Fourier.physical_blockMass_cyclic p H hH hsep α k 0, zero_add,
      BlockBand.QUE.Fourier.physical_eigenvalue_cyclic p H hH α k]
  have hsum : ∫ H, ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
      ∑ k : ZMod p.n, physicalOrderedBlockMass p H α k ^ 2 ∂μ = ∑ k : ZMod p.n, ∫ H, f k H ∂μ := by
    rw [← integral_finsetSum _ fun k _ =>
      integrable_weight_blockMass_sq R.model E hw Mw hMw k]
    congr 1; funext H
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hsum]
  simp_rw [hk]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

/-- The block-`0` mass functional is dominated by the block atom: for `0 ≤ w ≤ w̃` (bounded
measurable), `n E Σ_α p_{α0} w(u_α) min(1, max(0, p_{α0})) ≤ blockAtomStatistic R E w̃`. -/
theorem blockZero_mass_le_blockAtom (R : FiniteRealization p) (E : ℝ) {w wt : ℝ → ℝ}
    (hw : Measurable w) (hwt : Measurable wt) (Mw : ℝ) (hMw : ∀ x, |wt x| ≤ Mw)
    (h0 : ∀ x, 0 ≤ w x) (hle : ∀ x, w x ≤ wt x) :
    (p.n : ℝ) * (∫ H, ∑ α : Fin p.N, physicalOrderedBlockMass p H α 0 *
        (w (microCoord p E (physicalOrderedEigenvalue p H α)) *
          max 0 (min 1 (blockMassVector p H α 0))) ∂(R.model.law : Measure p.SiteMatrix)) ≤
      blockAtomStatistic R E wt := by
  have hMw' : ∀ x, |w x| ≤ Mw := fun x => by
    rw [abs_of_nonneg (h0 x)]; exact (hle x).trans ((le_abs_self _).trans (hMw x))
  have hwt0 : ∀ x, 0 ≤ wt x := fun x => (h0 x).trans (hle x)
  unfold blockAtomStatistic
  simp_rw [abs_of_nonneg (hwt0 _)]
  rw [← nsmul_blockZero_sq_eq R E hwt Mw hMw]
  have hn : (0 : ℝ) ≤ p.n := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hn
  have hm : Measurable fun H => ∑ α : Fin p.N, physicalOrderedBlockMass p H α 0 *
      (w (microCoord p E (physicalOrderedEigenvalue p H α)) *
        max 0 (min 1 (blockMassVector p H α 0))) := by
    refine Finset.measurable_sum _ fun α _ => ?_
    refine (measurable_physicalOrderedBlockMass p α 0).mul
      ((hw.comp ((measurable_microCoord (p := p) E).comp
        (measurable_physicalOrderedEigenvalue p α))).mul ?_)
    exact measurable_const.max (measurable_const.min (measurable_physicalOrderedBlockMass p α 0))
  have hint2 := integrable_weight_blockMass_sq R.model E hwt Mw hMw 0
  refine integral_mono_of_nonneg ?_ hint2 ?_
  · refine Filter.Eventually.of_forall fun H => Finset.sum_nonneg fun α _ => ?_
    exact mul_nonneg (physicalOrderedBlockMass_nonneg p H α 0)
      (mul_nonneg (h0 _) (le_max_left _ _))
  · refine Filter.Eventually.of_forall fun H => Finset.sum_le_sum fun α _ => ?_
    have hp0 := physicalOrderedBlockMass_nonneg p H α 0
    have hcl : max 0 (min 1 (blockMassVector p H α 0)) ≤ physicalOrderedBlockMass p H α 0 :=
      max_le hp0 (min_le_right _ _)
    have hw1 := h0 (microCoord p E (physicalOrderedEigenvalue p H α))
    have hw2 := hle (microCoord p E (physicalOrderedEigenvalue p H α))
    calc physicalOrderedBlockMass p H α 0 * (w (microCoord p E (physicalOrderedEigenvalue p H α)) *
          max 0 (min 1 (blockMassVector p H α 0)))
        ≤ physicalOrderedBlockMass p H α 0 *
          (wt (microCoord p E (physicalOrderedEigenvalue p H α)) *
            physicalOrderedBlockMass p H α 0) := by
          gcongr
          · exact hwt0 _
      _ = wt (microCoord p E (physicalOrderedEigenvalue p H α)) *
          physicalOrderedBlockMass p H α 0 ^ 2 := by ring

end Cyclic

section Smooth

/-- **Smooth domination**: a continuous compactly supported `w` is dominated
by `w̃ = M · bump`, smooth, compactly supported, `0 ≤ w̃ ≤ M`.
-/
theorem exists_smooth_dominating {w : ℝ → ℝ} (hc : Continuous w) (hs : HasCompactSupport w) :
    ∃ wt : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) wt ∧ HasCompactSupport wt ∧
      (∀ x, w x ≤ wt x) ∧ ∃ M : ℝ, ∀ x, |wt x| ≤ M := by
  obtain ⟨M, R, hM0, hM, hR⟩ := exists_bound_support_of_compact hc hs
  let f : ContDiffBump (0 : ℝ) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  refine ⟨fun x => M * f x, ?_, ?_, ?_, ⟨M, fun x => ?_⟩⟩
  · exact contDiff_const.mul f.contDiff
  · exact f.hasCompactSupport.mul_left
  · intro x
    by_cases hx : R < |x|
    · rw [hR x hx]; exact mul_nonneg hM0 f.nonneg
    · push Not at hx
      have h1 : f x = 1 := by
        apply f.one_of_mem_closedBall
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
        show |x| ≤ |R| + 1
        linarith [le_abs_self R]
      show w x ≤ M * f x
      rw [h1, mul_one]
      exact (le_abs_self _).trans (hM x)
  · rw [abs_mul, abs_of_nonneg hM0, abs_of_nonneg f.nonneg]
    exact mul_le_of_le_one_right hM0 f.le_one

end Smooth

end LeadGaussian

end BlockBand.Endpoints.Normalization
