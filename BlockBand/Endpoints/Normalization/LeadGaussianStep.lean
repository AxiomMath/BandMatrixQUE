module

public import BlockBand.Endpoints.Normalization.LeadGaussianWindow

/-!
# The physical lead-profile theorem: the assembly `LeadGaussianStep`

We combine the Gaussian ratios for the one-block law, the covariance change to `c|z₀-Σ|^{-2}`, the
identification of the field with `√c(Hg, ULg)` and the removal of block `0`.

**Main results.**
* `energy_lead_comparison` (energy-wise): fixed first `b`, the bulk range `bulkInterval κ`, `T`,
  `Φ`, `ε₁ > 0`, the deletion constant `C` of `energy_deletion` and `ε₂ > 0`; for `W ≥ W₀`,
  `n ≤ TW`, every model, `Pω`, frame, `e ∈ bulkInterval κ`:
  `|E_ω A(e, ω) - gaussianLeadSide p Φ e| ≤ (5 + 4‖Φ‖)ε₁ + C (E_ω A₀(e, ω) + 6ε₂)`, where
  `A₀(e, ω) = Σ_ℓ 𝒜⁰_{ℓ,e}[p_0(v,e)] / Z₀(e)` is the normalized Palm average of the block-`0`
  mass.
* `integral_priorWindowMeasure`: `∫ F d𝔭_W = ∫ w(u) E_ω F(u, ω) du` (bounded measurable `F`).
* `leadGaussianStep_of`: `LeadGaussianStep` from `FreshEigenpairDensityContract`,
  `GaussianRatiosContract`, `BlockRegularEventContract`, `OneBlockPalmContract`,
  `OneBlockNormalizerContract`, `LeadAngularRegularity` and `VanishingBlockAtom` (applied to a
  smooth compactly supported `w̃ ≥ w`). Proof: `|∫A d𝔭_W - ∫ w gaussianLeadSide| ≤ ∫ w |E_ω A - gLS|`
  (energy-wise bound on the support of `w`, where `e(u)` is in the bulk for large `W`), then
  `∫ A₀ d𝔭_W ≤ ε₂ + n E Σ_α p_{α0} w(u_α) min(1,p_{α0}) ≤ ε₂ + blockAtomStatistic R E w̃`
  (`window_massObs_comparison`, `blockZero_mass_le_blockAtom`), and `VanishingBlockAtom`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

namespace LeadGaussian

open MeasureTheory Matrix Filter Topology
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile
open scoped ENNReal NNReal BoundedContinuousFunction

/-- The clamped block-`0` mass observable `q ↦ min(1, max(0, q_0))`. -/
def blockZeroObs (p : Parameters) (q : ZMod p.n → ℝ) : ℝ := max 0 (min 1 (q 0))

theorem measurable_blockZeroObs (p : Parameters) : Measurable (blockZeroObs p) :=
  measurable_const.max (measurable_const.min (measurable_pi_apply 0))

theorem abs_blockZeroObs_le (p : Parameters) (q : ZMod p.n → ℝ) : |blockZeroObs p q| ≤ 1 := by
  unfold blockZeroObs
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le zero_le_one (min_le_left _ _)

theorem blockZeroObs_recon (p : Parameters) (ω : BlockState p 0) (e : ℝ)
    (v : BlockSite p 0 → ℂ) : blockZeroObs p (blockReconMass p 0 ω e v) =
      blockReconMass p 0 ω e v 0 := by
  obtain ⟨h0, h1⟩ := blockReconMass_self_le_one p 0 ω e v
  unfold blockZeroObs
  rw [min_eq_right h1, max_eq_right h0]

/-- The coordinate test on the one-cube. -/
def cubeCoord : C(Fin 1 → Set.Icc (-1 : ℝ) 1, ℝ) :=
  ⟨fun x => (x 0 : ℝ), continuous_subtype_val.comp (continuous_apply 0)⟩

/-- **Energy-wise comparison**, from `FreshEigenpairDensityContract`, `GaussianRatiosContract` and
`BlockRegularEventContract`. -/
theorem energy_lead_comparison (hD : FreshEigenpairDensityContract)
    (hGR : GaussianRatiosContract) (hReg : BlockRegularEventContract) (b : ℝ) (hb : 0 < b)
    (hb' : b < 1 / 2) (κ T : ℝ) (hκ : 0 < κ) (Φ : MassProfile →ᵇ ℝ) (ε₁ : ℝ) (hε₁ : 0 < ε₁)
    (C : ℝ) (hC : 0 ≤ C)
    (hdel : ∀ (p : Parameters) (model : p.GaussianRingModel)
      (Pω : Measure (BlockState p 0)), IsBlockSplitting p 0 model Pω → ∀ e : ℝ, |e| < 2 →
      |(∫ ω, ∫ g', leadReconObservable p Φ 0 ω e (blockFieldFactor p 0 ω e *ᵥ g')
          ∂circularVectorLaw (BlockSite p 0) ∂Pω) - gaussianLeadSide p Φ e| ≤
        ε₁ + C * ∫ ω, ∫ g', blockReconMass p 0 ω e (blockFieldFactor p 0 ω e *ᵥ g') 0
          ∂circularVectorLaw (BlockSite p 0) ∂Pω)
    (ε₂ : ℝ) (hε₂ : 0 < ε₂) :
    ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (Pω : Measure (BlockState p 0)),
      IsBlockSplitting p 0 model Pω →
    ∀ (U : (BlockSite p 0 → ℂ) → Matrix (BlockSite p 0) (BlockFrameIndex p) ℂ),
      IsBlockFrame p 0 U → ∀ e ∈ bulkInterval κ,
      |(∫ ω, leadAngularAverage p U Φ ω e ∂Pω) - gaussianLeadSide p Φ e| ≤
        (5 + 4 * ‖Φ‖) * ε₁ + C * ((∫ ω, (∑ ℓ ∈ Finset.range p.W,
            blockSectorFiberReal p 0 U ω e ℓ (fun v => blockZeroObs p (blockReconMass p 0 ω e v))) /
            (blockNormalizer p 0 U ω e).toReal ∂Pω) + 6 * ε₂) := by
  obtain ⟨m, φ, ψ, hφ, happrox⟩ := exists_cylinder_approx Φ ε₁ hε₁
  obtain ⟨W₁, hW₁⟩ := energy_palm_field_comparison hD hGR hReg b hb hb' κ T hκ m ψ ε₁ hε₁
  obtain ⟨W₂, hW₂⟩ := energy_palm_field_comparison hD hGR hReg b hb hb' κ T hκ 1 cubeCoord ε₂ hε₂
  refine ⟨max W₁ W₂, ?_⟩
  intro p hpb hW hnT model Pω hsplit U hU e he
  obtain ⟨he1, he2, -⟩ := mem_bulkInterval_bounds hκ he
  have he' : |e| < 2 := abs_lt.mpr ⟨he1, he2⟩
  -- the Φ-observable
  set G₁ : (ZMod p.n → ℝ) → ℝ := fun q => leadProfileRotationAverage p Φ (massVectorProfile p q)
  have hG₁ : Measurable G₁ :=
    (measurable_leadProfileRotationAverage p Φ).comp (measurable_massVectorProfile p)
  have hG₁b : ∀ q, |G₁ q| ≤ ‖Φ‖ := fun q => abs_leadProfileRotationAverage_le p Φ _
  have hn : (0 : ℝ) < p.n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p.n)
  have hcyl : ∀ (ω : BlockState p 0) (v : BlockSite p 0 → ℂ),
      |G₁ (blockReconMass p 0 ω e v) - (Fintype.card (ZMod p.n) : ℝ)⁻¹ * ∑ s : ZMod p.n,
        ψ (ratioCube (fun i => liftForm p 0 ω e
            (fun y => φ i (physicalProfileGrid p s + physicalProfileGrid p y.1)))
          (clockForm p 0 ω e) (fun _ i => φ i (physicalProfileGrid p s)) v)| ≤ ε₁ := by
    intro ω v
    simp only [G₁, leadProfileRotationAverage, ZMod.card]
    simp_rw [← cylinderVec_rotation_eq_ratioCube]
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.mpr hn)]
    calc (p.n : ℝ)⁻¹ * |∑ s : ZMod p.n, (Φ (massProfileRotation (physicalProfileGrid p s)
            (massVectorProfile p (blockReconMass p 0 ω e v))) -
          ψ (cylinderVec φ (massProfileRotation (physicalProfileGrid p s)
            (massVectorProfile p (blockReconMass p 0 ω e v)))))|
        ≤ (p.n : ℝ)⁻¹ * ∑ _s : ZMod p.n, ε₁ := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => happrox _)
      _ = ε₁ := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; field_simp
  have e1 := hW₁ p hpb ((le_max_left _ _).trans hW) hnT model Pω hsplit U hU e he
    (fun ω (s : ZMod p.n) i => liftForm p 0 ω e
      (fun y => φ i (physicalProfileGrid p s + physicalProfileGrid p y.1)))
    (fun ω s j => liftForm_isSandwiched p 0 ω e _ fun y => hφ j _)
    (fun _ s _ i => φ i (physicalProfileGrid p s)) (fun _ _ => measurable_const)
    G₁ hG₁ ‖Φ‖ hG₁b ε₁ hcyl
  -- the block-0 observable
  have hzero : ∀ (ω : BlockState p 0) (v : BlockSite p 0 → ℂ),
      |blockZeroObs p (blockReconMass p 0 ω e v) - (Fintype.card Unit : ℝ)⁻¹ * ∑ _s : Unit,
        cubeCoord (ratioCube (fun _ : Fin 1 => blockForm p 0 ω e 0) (clockForm p 0 ω e)
          (fun _ _ => 0) v)| ≤ 0 := by
    intro ω v
    rw [blockZeroObs_recon, blockReconMass_self_eq_ratioCube]
    simp [cubeCoord]
  have e2 := hW₂ p hpb ((le_max_right _ _).trans hW) hnT model Pω hsplit U hU e he
    (S := Unit) (fun ω _ _ => blockForm p 0 ω e 0)
    (fun ω _ _ => liftForm_isSandwiched p 0 ω e _ fun y => by split_ifs <;> norm_num)
    (fun _ _ _ _ => 0) (fun _ _ => measurable_const)
    (blockZeroObs p) (measurable_blockZeroObs p) 1 (abs_blockZeroObs_le p) 0 hzero
  have e3 := hdel p model Pω hsplit e he'
  have hG0 : ∀ ω : BlockState p 0, (∫ g', blockZeroObs p (blockReconMass p 0 ω e
      (blockFieldFactor p 0 ω e *ᵥ g')) ∂circularVectorLaw (BlockSite p 0)) =
      ∫ g', blockReconMass p 0 ω e (blockFieldFactor p 0 ω e *ᵥ g') 0
        ∂circularVectorLaw (BlockSite p 0) := fun ω => by
    simp_rw [blockZeroObs_recon]
  simp_rw [hG0] at e2
  have hA : (fun ω => leadAngularAverage p U Φ ω e) = fun ω => (∑ ℓ ∈ Finset.range p.W,
      blockSectorFiberReal p 0 U ω e ℓ (fun v => G₁ (blockReconMass p 0 ω e v))) /
      (blockNormalizer p 0 U ω e).toReal := rfl
  have hF : (fun ω => ∫ g', leadReconObservable p Φ 0 ω e (blockFieldFactor p 0 ω e *ᵥ g')
      ∂circularVectorLaw (BlockSite p 0)) = fun ω => ∫ g', G₁ (blockReconMass p 0 ω e
        (blockFieldFactor p 0 ω e *ᵥ g')) ∂circularVectorLaw (BlockSite p 0) := rfl
  rw [hA]
  rw [hF] at e3
  have := abs_sub_le (∫ ω, (∑ ℓ ∈ Finset.range p.W,
      blockSectorFiberReal p 0 U ω e ℓ (fun v => G₁ (blockReconMass p 0 ω e v))) /
      (blockNormalizer p 0 U ω e).toReal ∂Pω)
    (∫ ω, ∫ g', G₁ (blockReconMass p 0 ω e (blockFieldFactor p 0 ω e *ᵥ g'))
        ∂circularVectorLaw (BlockSite p 0) ∂Pω) (gaussianLeadSide p Φ e)
  have h2' := (abs_le.mp e2).1
  have hCε := mul_le_mul_of_nonneg_left (show (∫ ω, ∫ g', blockReconMass p 0 ω e
      (blockFieldFactor p 0 ω e *ᵥ g') 0 ∂circularVectorLaw (BlockSite p 0) ∂Pω) ≤
      (∫ ω, (∑ ℓ ∈ Finset.range p.W, blockSectorFiberReal p 0 U ω e ℓ
        (fun v => blockZeroObs p (blockReconMass p 0 ω e v))) /
        (blockNormalizer p 0 U ω e).toReal ∂Pω) + 6 * ε₂ by linarith) hC
  nlinarith [norm_nonneg Φ]

/-- `∫ F d𝔭_W = ∫ w(u) E_ω F(u, ω) du` for a window `w` and bounded measurable `F`. -/
theorem integral_priorWindowMeasure {Ω : Type*} [MeasurableSpace Ω] (Pω : Measure Ω)
    [IsProbabilityMeasure Pω] {w : ℝ → ℝ} (hw : IsWindow w) (F : ℝ × Ω → ℝ)
    (hF : Measurable F) (M : ℝ) (hM : ∀ x, |F x| ≤ M) :
    ∫ x, F x ∂priorWindowMeasure Pω w = ∫ u, w u * ∫ ω, F (u, ω) ∂Pω := by
  have hwi : Integrable w volume := hw.1.integrable_of_hasCompactSupport hw.2.1
  have hfin : IsFiniteMeasure (volume.withDensity fun u => ENNReal.ofReal (w u)) :=
    isFiniteMeasure_withDensity_ofReal hwi.2
  have hFi : Integrable F (priorWindowMeasure Pω w) := by
    unfold priorWindowMeasure
    exact (integrable_const M).mono' hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)
  unfold priorWindowMeasure at hFi ⊢
  have hdm : Measurable fun u => ENNReal.ofReal (w u) :=
    ENNReal.measurable_ofReal.comp hw.1.measurable
  rw [integral_prod F hFi, integral_withDensity_eq_integral_toReal_smul hdm
    (Filter.Eventually.of_forall fun u => ENNReal.ofReal_lt_top)]
  congr 1
  funext u
  rw [ENNReal.toReal_ofReal (hw.2.2.1 u), smul_eq_mul]

/-- **The window bound at a fixed parameter set** (finite-`W` form). -/
theorem lead_window_bound (hD : FreshEigenpairDensityContract) (hGR : GaussianRatiosContract)
    (hReg : BlockRegularEventContract) (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hAR : LeadAngularRegularity) (b : ℝ) (hb : 0 < b)
    (hb' : b < 1 / 2) (E : ℝ) (h1 : -2 < E) (h2 : E < 2) (w : ℝ → ℝ) (hw : IsWindow w)
    (Φ : MassProfile →ᵇ ℝ) (κ T : ℝ) (hκ : 0 < κ) (ε₁ : ℝ) (hε₁ : 0 < ε₁) (C : ℝ) (hC : 0 ≤ C)
    (hdel : ∀ (p : Parameters) (model : p.GaussianRingModel)
      (Pω : Measure (BlockState p 0)), IsBlockSplitting p 0 model Pω → ∀ e : ℝ, |e| < 2 →
      |(∫ ω, ∫ g', leadReconObservable p Φ 0 ω e (blockFieldFactor p 0 ω e *ᵥ g')
          ∂circularVectorLaw (BlockSite p 0) ∂Pω) - gaussianLeadSide p Φ e| ≤
        ε₁ + C * ∫ ω, ∫ g', blockReconMass p 0 ω e (blockFieldFactor p 0 ω e *ᵥ g') 0
          ∂circularVectorLaw (BlockSite p 0) ∂Pω)
    (ε₂ : ℝ) (hε₂ : 0 < ε₂) (wt : ℝ → ℝ) (hwt : Measurable wt) (Mt : ℝ) (hMt : ∀ x, |wt x| ≤ Mt)
    (hle : ∀ x, w x ≤ wt x) :
    ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
    ∀ (R : FiniteRealization p) (Pω : Measure (BlockState p 0)),
      IsBlockSplitting p 0 R.model Pω →
    ∀ (U : (BlockSite p 0 → ℂ) → Matrix (BlockSite p 0) (BlockFrameIndex p) ℂ),
      IsBlockFrame p 0 U →
      (∀ u, w u ≠ 0 → microEnergy p E u ∈ bulkInterval κ) →
      blockAtomStatistic R E wt ≤ ε₂ →
      |(∫ x, leadAngularAverage p U Φ x.2 (microEnergy p E x.1) ∂priorWindowMeasure Pω w) -
          ∫ u, w u * gaussianLeadSide p Φ (microEnergy p E u)| ≤
        (5 + 4 * ‖Φ‖) * ε₁ + 8 * C * ε₂ := by
  obtain ⟨W₁, hW₁⟩ := energy_lead_comparison hD hGR hReg b hb hb' κ T hκ Φ ε₁ hε₁ C hC hdel ε₂ hε₂
  obtain ⟨W₃, hW₃⟩ := window_massObs_comparison hPalm hNorm b hb hb' E h1 h2 T w hw 1 one_pos
    ε₂ hε₂
  refine ⟨max W₁ W₃, ?_⟩
  intro p hpb hW hnT R Pω hsplit U hU hbulk hatom
  have hprob := isProbabilityMeasure_blockSplitting p R.model 0 hsplit
  have hw0 : ∀ u, 0 ≤ w u := hw.2.2.1
  have hwi : Integrable w volume := hw.1.integrable_of_hasCompactSupport hw.2.1
  obtain ⟨hAm, hAb, -⟩ := hAR p U hU Φ
  have hHerm := ae_blockSplit_isHermitian p R.model 0 hsplit
  -- the block-0 Palm average and its clamp
  set A0raw : ℝ → BlockState p 0 → ℝ := fun e ω => (∑ ℓ ∈ Finset.range p.W,
    blockSectorFiberReal p 0 U ω e ℓ (fun v => blockZeroObs p (blockReconMass p 0 ω e v))) /
    (blockNormalizer p 0 U ω e).toReal
  set A0 : ℝ → BlockState p 0 → ℝ := fun e ω => max (-1) (min 1 (A0raw e ω))
  have hA0rm : Measurable (Function.uncurry A0raw) :=
    measurable_blockSectorAverage p 0 U hU.1 (blockZeroObs p) (measurable_blockZeroObs p)
  have hA0m : Measurable (Function.uncurry A0) :=
    measurable_const.max (measurable_const.min hA0rm)
  have hA0b : ∀ e ω, |A0 e ω| ≤ 1 := fun e ω => by
    simp only [A0]
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hA0eq : ∀ e ω, ω.1.IsHermitian → A0 e ω = A0raw e ω := fun e ω hω => by
    have h := abs_le.mp (abs_blockSectorAverage_le p 0 hD U hU ω hω e (blockZeroObs p)
      (measurable_blockZeroObs p) 1 (abs_blockZeroObs_le p))
    simp only [A0]
    rw [min_eq_right h.2, max_eq_right h.1]
  have hrep0 : ∀ᵐ ω ∂Pω, ∀ e, ∑ ℓ ∈ Finset.range p.W,
      blockSectorFiberReal p 0 U ω e ℓ (fun v => blockZeroObs p (blockReconMass p 0 ω e v)) =
      (blockNormalizer p 0 U ω e).toReal * A0 e ω := by
    filter_upwards [hHerm] with ω hω e
    rw [hA0eq e ω hω]
    exact sum_blockSectorFiberReal_eq_mul p 0 hD U hU ω hω e (blockZeroObs p)
      (measurable_blockZeroObs p) 1 (abs_blockZeroObs_le p)
  -- the windowed block-0 mass is small
  have hS5 := hW₃ p hpb ((le_max_right _ _).trans hW) hnT R Pω hsplit U hU (blockZeroObs p)
    (measurable_blockZeroObs p) 1 (abs_blockZeroObs_le p) A0 hA0m hA0b hrep0
  have hS6 := blockZero_mass_le_blockAtom R E hw.1.measurable hwt Mt hMt hw0 hle
  have hA0win : ∫ x, A0 (microEnergy p E x.1) x.2 ∂priorWindowMeasure Pω w ≤ 2 * ε₂ := by
    have := (abs_le.mp hS5).1
    have h6 : (p.n : ℝ) * (∫ H, ∑ α : Fin p.N, physicalOrderedBlockMass p H α 0 *
        (w (microCoord p E (physicalOrderedEigenvalue p H α)) *
          blockZeroObs p (blockMassVector p H α)) ∂(R.model.law : Measure p.SiteMatrix)) ≤ ε₂ :=
      hS6.trans hatom
    linarith
  -- measurability in `u`
  have hme : Measurable fun x : ℝ × BlockState p 0 => (microEnergy p E x.1, x.2) :=
    ((measurable_microEnergy p E).comp measurable_fst).prodMk measurable_snd
  have hFA : Measurable fun x : ℝ × BlockState p 0 =>
      leadAngularAverage p U Φ x.2 (microEnergy p E x.1) := by
    have h := hAm.comp hme
    exact h
  have hFA0 : Measurable fun x : ℝ × BlockState p 0 => A0 (microEnergy p E x.1) x.2 := by
    have h := hA0m.comp hme
    exact h
  have hS1 := integral_priorWindowMeasure Pω hw _ hFA ‖Φ‖ (fun x => hAb _ _)
  have hS4 := integral_priorWindowMeasure Pω hw _ hFA0 1 (fun x => hA0b _ _)
  set a : ℝ → ℝ := fun u => ∫ ω, leadAngularAverage p U Φ ω (microEnergy p E u) ∂Pω
  set c : ℝ → ℝ := fun u => ∫ ω, A0 (microEnergy p E u) ω ∂Pω
  set gs : ℝ → ℝ := fun u => gaussianLeadSide p Φ (microEnergy p E u)
  have ham : Measurable a := (hFA.stronglyMeasurable.integral_prod_right' (ν := Pω)).measurable
  have hcm : Measurable c := (hFA0.stronglyMeasurable.integral_prod_right' (ν := Pω)).measurable
  have hgsm : Measurable gs :=
    (measurable_gaussianLeadSide p Φ).comp (measurable_microEnergy p E)
  have hab : ∀ u, |a u| ≤ ‖Φ‖ := fun u => by
    have := norm_integral_le_of_norm_le_const (μ := Pω) (C := ‖Φ‖)
      (f := fun ω => leadAngularAverage p U Φ ω (microEnergy p E u))
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hAb _ _)
    simpa [Real.norm_eq_abs] using this
  have hcb : ∀ u, |c u| ≤ 1 := fun u => by
    have := norm_integral_le_of_norm_le_const (μ := Pω) (C := 1)
      (f := fun ω => A0 (microEnergy p E u) ω)
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hA0b _ _)
    simpa [Real.norm_eq_abs] using this
  have hgsb : ∀ u, |gs u| ≤ ‖Φ‖ := fun u => abs_gaussianLeadSide_le p Φ _
  have hint : ∀ f : ℝ → ℝ, Measurable f → ∀ M, (∀ u, |f u| ≤ M) →
      Integrable (fun u => w u * f u) volume := fun f hf M hM => by
    have := hwi.bdd_mul (f := f) (c := M) hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hM u)
    simpa only [mul_comm] using this
  -- the energy-wise bound on the support of `w`
  have hS2 : ∀ u, w u ≠ 0 → |a u - gs u| ≤ (5 + 4 * ‖Φ‖) * ε₁ + C * (c u + 6 * ε₂) := by
    intro u hu
    have hb := hW₁ p hpb ((le_max_left _ _).trans hW) hnT R.model Pω hsplit U hU
      (microEnergy p E u) (hbulk u hu)
    have hc' : (∫ ω, A0raw (microEnergy p E u) ω ∂Pω) = c u := by
      refine integral_congr_ae ?_
      filter_upwards [hHerm] with ω hω
      exact (hA0eq _ ω hω).symm
    rw [hc'] at hb
    exact hb
  -- integrate
  have hpt : ∀ u, ‖w u * a u - w u * gs u‖ ≤
      w u * ((5 + 4 * ‖Φ‖) * ε₁ + 6 * C * ε₂) + C * (w u * c u) := by
    intro u
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (hw0 u)]
    by_cases hu : w u = 0
    · rw [hu]; simp
    · have := mul_le_mul_of_nonneg_left (hS2 u hu) (hw0 u)
      nlinarith
  have hdiff := norm_integral_le_of_norm_le
    (g := fun u => w u * ((5 + 4 * ‖Φ‖) * ε₁ + 6 * C * ε₂) + C * (w u * c u))
    (((hwi.mul_const _)).add ((hint c hcm 1 hcb).const_mul C)) (Filter.Eventually.of_forall hpt)
  have heq : ∫ u, (w u * ((5 + 4 * ‖Φ‖) * ε₁ + 6 * C * ε₂) + C * (w u * c u)) =
      ((5 + 4 * ‖Φ‖) * ε₁ + 6 * C * ε₂) + C * ∫ u, w u * c u := by
    rw [integral_add (hwi.mul_const _) ((hint c hcm 1 hcb).const_mul C), integral_mul_const,
      hw.2.2.2, one_mul, integral_const_mul]
  rw [heq] at hdiff
  rw [hS1, ← integral_sub (hint a ham ‖Φ‖ hab) (hint gs hgsm ‖Φ‖ hgsb)]
  rw [← Real.norm_eq_abs]
  have hc2 : ∫ u, w u * c u ≤ 2 * ε₂ := by rw [← hS4]; exact hA0win
  have := mul_le_mul_of_nonneg_left hc2 hC
  linarith

end LeadGaussian

open LeadGaussian
open MeasureTheory Matrix Filter Topology
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile

/-- **`LeadGaussianStep`** (steps 2–4 of the physical lead-profile theorem), from
`FreshEigenpairDensityContract`, `GaussianRatiosContract`, `BlockRegularEventContract`,
`OneBlockPalmContract`, `OneBlockNormalizerContract`, `LeadAngularRegularity` and
`VanishingBlockAtom`. -/
theorem leadGaussianStep_of (hD : FreshEigenpairDensityContract) (hGR : GaussianRatiosContract)
    (hReg : BlockRegularEventContract) (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hAR : LeadAngularRegularity)
    (hVBA : VanishingBlockAtom) : LeadGaussianStep := by
  intro b hb hb' E h1 h2 w hw Φ τ hτ s R Pω hPω U hU
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K : ℝ := 14 + 4 * ‖Φ‖ with hK
  have hK0 : 0 < K := by positivity
  set ε₁ : ℝ := ε / (2 * K) with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  obtain ⟨C, hC, hdel⟩ := energy_deletion Φ ε₁ hε₁
  set ε₂ : ℝ := ε₁ / (C + 1) with hε₂def
  have hε₂ : 0 < ε₂ := by positivity
  have hCε : C * ε₂ ≤ ε₁ := by
    rw [hε₂def, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  set κ : ℝ := (2 - |E|) / 2 with hκ
  have hκ0 : 0 < κ := by
    have : |E| < 2 := abs_lt.mpr ⟨h1, h2⟩
    rw [hκ]; linarith
  obtain ⟨wt, hwts, hwtc, hle, Mt, hMt⟩ := exists_smooth_dominating hw.1 hw.2.1
  obtain ⟨W₀, hW₀⟩ := lead_window_bound hD hGR hReg hPalm hNorm hAR b hb hb' E h1 h2 w hw Φ κ
    (τ + 1) hκ0 ε₁ hε₁ C hC hdel ε₂ hε₂ wt hwts.continuous.measurable Mt hMt hle
  have hatom := hVBA b hb hb' E h1 h2 wt hwts hwtc τ hτ s R
  obtain ⟨Mw, Rw, -, -, hRw⟩ := exists_bound_support_of_compact hw.1 hw.2.1
  have hρ := semicircleDensity_pos h1 h2
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hatom ε₂ hε₂
  have hratio := s.ratio_tendsto
  have hev1 : ∀ᶠ j in atTop, (s.n j : ℝ) / s.W j < τ + 1 :=
    hratio.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ j in atTop,
      max W₀ (⌈|Rw| / (κ * Parameters.semicircleDensity E)⌉₊) ≤ s.W j :=
    s.width_tendsto.eventually_ge_atTop _
  obtain ⟨N₂, hN₂⟩ := (hev1.and hev2).exists_forall_of_atTop
  refine ⟨max N₁ N₂, fun j hj => ?_⟩
  obtain ⟨hr2, hWj⟩ := hN₂ j (le_of_max_le_right hj)
  have hWpos : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
  have hW0 : W₀ ≤ (s.parameters b hb hb' j).W := (le_max_left _ _).trans hWj
  have hnT : ((s.parameters b hb hb' j).n : ℝ) ≤ (τ + 1) * (s.parameters b hb hb' j).W :=
    ((div_lt_iff₀ hWpos).mp hr2).le
  have hbulk : ∀ u, w u ≠ 0 → microEnergy (s.parameters b hb hb' j) E u ∈ bulkInterval κ := by
    intro u hu
    have hu' : |u| ≤ Rw := by
      by_contra h
      push Not at h
      exact hu (hRw u h)
    apply bulk_of_near hκ
    have hN : ((s.parameters b hb hb' j).W : ℝ) ≤ (s.parameters b hb hb' j).N := by
      change ((s.W j : ℕ) : ℝ) ≤ ((s.n j * s.W j : ℕ) : ℝ)
      have : 1 ≤ s.n j := by have := s.n_ge_four j; omega
      exact_mod_cast Nat.le_mul_of_pos_left _ this
    have hNpos : (0 : ℝ) < (s.parameters b hb hb' j).N := lt_of_lt_of_le hWpos hN
    have hceil : |Rw| / (κ * Parameters.semicircleDensity E) ≤ (s.parameters b hb hb' j).W := by
      have := Nat.le_ceil (|Rw| / (κ * Parameters.semicircleDensity E))
      have h' : ((⌈|Rw| / (κ * Parameters.semicircleDensity E)⌉₊ : ℕ) : ℝ) ≤ s.W j := by
        exact_mod_cast (le_max_right _ _).trans hWj
      change _ ≤ ((s.W j : ℕ) : ℝ)
      linarith
    unfold microEnergy
    rw [add_sub_cancel_left, abs_div, abs_of_pos (mul_pos hNpos hρ)]
    rw [div_le_iff₀ (mul_pos hNpos hρ)]
    have hk : |Rw| ≤ κ * Parameters.semicircleDensity E * (s.parameters b hb hb' j).W := by
      rw [div_le_iff₀ (mul_pos hκ0 hρ)] at hceil; linarith
    calc |u| ≤ |Rw| := hu'.trans (le_abs_self _)
      _ ≤ κ * Parameters.semicircleDensity E * (s.parameters b hb hb' j).W := hk
      _ ≤ κ * ((s.parameters b hb hb' j).N * Parameters.semicircleDensity E) := by
          have := mul_le_mul_of_nonneg_left hN (mul_pos hκ0 hρ).le
          nlinarith
  have hat : blockAtomStatistic (R j) E wt ≤ ε₂ := by
    have := hN₁ j (le_of_max_le_left hj)
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  have hbd := hW₀ (s.parameters b hb hb' j) rfl hW0 hnT (R j) (Pω j) (hPω j) (U j) (hU j) hbulk
    hat
  rw [Real.dist_eq, sub_zero]
  have hKε : (5 + 4 * ‖Φ‖) * ε₁ + 8 * C * ε₂ < ε := by
    have h8 : 8 * C * ε₂ ≤ 8 * ε₁ := by nlinarith
    have : (13 + 4 * ‖Φ‖) * ε₁ < ε := by
      rw [hε₁def]
      have : (13 + 4 * ‖Φ‖) * (ε / (2 * K)) = ε * ((13 + 4 * ‖Φ‖) / (2 * K)) := by ring
      rw [this]
      have hlt : (13 + 4 * ‖Φ‖) / (2 * K) < 1 := by
        rw [div_lt_one (by positivity), hK]; nlinarith [norm_nonneg Φ]
      nlinarith
    nlinarith
  exact lt_of_le_of_lt hbd hKε

end BlockBand.Endpoints.Normalization
