module

public import BlockBand.Endpoints.Normalization.OneBlockPalmRank

/-!
# One-block Palm identity: clauses `mass` and `index`

**Statements.** For every admissible `p`, model, block `k`, one-block splitting law `Pω`
(`IsBlockSplitting`, fresh block `GUE_W(c/W)`), measurable block frame `U` and measurable
`f ≥ 0` of `(e, p)`:
* `oneBlockPalm_mass`: `E Σ_α p_{αk} f(λ_α, p_α) = E_ext ∫ Σ_{ℓ<W} 𝒜⁰_{ℓ,e}[f(e, p(v,e))] de`;
* `oneBlockPalm_index`: for every rank `α`,
  `E f(λ_α, p_α) = E_ext ∫ Σ_{ℓ<W} 1{ℓ + N_-(H_R - e) = α} 𝒜⁰_{ℓ,e}[(v*Dv) f(e, p(v,e))] de`.
Measures: the exact physical law on the left; `Pω`, Lebesgue `de`, `projectiveHaar` and
`GUE_{W-1}(c/W)` on the right. Exact identities in `[0,∞]`.

**Proof** (as in the pair case `exactPalm_mass_of_coarea`). The left side is transported to
`Pω ⊗ GUE_W(c/W)` by `IsBlockSplitting`, then the fixed-exterior one-block coarea formula
`oneBlockPalm_formula_fixed` is applied for `Pω`-a.e. `ω`. On the
support (`det M ≠ 0`, rank condition) `oneBlockPalm_reconstruction` gives `λ_α = e`,
`p_α = p(v,e)` and `p_{αk} = 1/(v*Dv)`. The inertia indicator is split
into sectors `ℓ < W` (`N_-(M) ≤ W - 1`, `sector_lintegral`). For `mass` the speed cancels and
`Σ_α 1{ℓ + N_-(H_R - e) = α} = 1` (`N_-(H_R - e) ≤ N - W`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
  BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate

section Lemmas

variable (p : Parameters) (k : ZMod p.n)

/-- `det(H_R - E) ≠ 0` for Lebesgue-a.e. real `E`. -/
theorem oneBlockPalm_ae_det_shift_ne_zero
    (H_R : Matrix (OffBlockSite p k) (OffBlockSite p k) ℂ) :
    ∀ᵐ E : ℝ, (H_R - (E : ℂ) • 1).det ≠ 0 := by
  have hfin : {E : ℝ | (H_R - (E : ℂ) • 1).det = 0}.Finite := by
    refine (Polynomial.finite_setOfPred_isRoot (H_R.charpoly_monic.ne_zero)).preimage
      (Complex.ofReal_injective.injOn) |>.subset ?_
    intro E hE
    simp only [Set.mem_ofPred_eq] at hE ⊢
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Polynomial.IsRoot, Matrix.eval_charpoly]
    have : Matrix.scalar (OffBlockSite p k) (E : ℂ) - H_R = -(H_R - (E : ℂ) • 1) := by
      rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [this, Matrix.det_neg, hE, mul_zero]
  exact measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero volume)

theorem oneBlockPalm_nonempty_blockSite : Nonempty (BlockSite p k) :=
  ⟨⟨(k, ⟨0, p.W_pos⟩), rfl⟩⟩

theorem oneBlockPalm_negativeCount_frame_lt
    (M : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ) : negativeCount M < p.W := by
  have h := negativeCount_le_card M
  rw [Fintype.card_fin] at h
  have := p.W_pos
  omega

/-- `Pω`-a.e. the off-block `H_R` is Hermitian. -/
theorem oneBlockPalm_ae_isHermitian {model : p.GaussianRingModel}
    {Pω : Measure (BlockState p k)} (hP : IsBlockSplitting p k model Pω) :
    ∀ᵐ ω ∂Pω, ω.1.IsHermitian :=
  regularEvent_ae_blockState_isHermitian hP

end Lemmas

/-!
## The integrands on the support
-/

section Integrands

variable (p : Parameters) (k : ZMod p.n)

/-- Index integrand: the coarea density with speed `v*Dv` and observable `f(λ_α, p_α)` of the
reassembled matrix equals the angular density times `(v*Dv) f(E, p(v,E))`. -/
theorem oneBlockPalm_index_integrand (α : Fin p.N)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (h1 : ω.1.IsHermitian) (E : ℝ)
    (hD : (ω.1 - (E : ℂ) • 1).det ≠ 0) (v : BlockSite p k → ℂ) (hv : l2Norm v = 1)
    (G' : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ) (hG' : G'.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a) (f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞) :
    ENNReal.ofReal (a * blockClockSpeed p k ω E v *
          Complex.normSq (blockFrameM p k U ω E v G').det) *
        (if negativeCount (blockFrameM p k U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) =
          α.val then 1 else 0) *
        f (physicalOrderedEigenvalue p
            (assembleBlock p k ω (oneBlockPalmRecon p k U ω E v G')) α)
          (blockMassVector p (assembleBlock p k ω (oneBlockPalmRecon p k U ω E v G')) α) =
      ENNReal.ofReal (a * Complex.normSq (blockFrameM p k U ω E v G').det) *
        (if negativeCount (blockFrameM p k U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) =
          α.val then 1 else 0) *
        (ENNReal.ofReal (blockClockSpeed p k ω E v) * f E (blockReconMass p k ω E v)) := by
  by_cases hM : (blockFrameM p k U ω E v G').det = 0
  · simp [hM]
  by_cases hc : negativeCount (blockFrameM p k U ω E v G') +
      negativeCount (ω.1 - (E : ℂ) • 1) = α.val
  · obtain ⟨hlam, hbm, -⟩ :=
      oneBlockPalm_reconstruction p k α U hU ω h1 E v G' hG' hv hD hM hc
    rw [hlam, hbm, ite_eq_left hc, mul_one, mul_one,
      show a * blockClockSpeed p k ω E v * Complex.normSq (blockFrameM p k U ω E v G').det =
        (a * Complex.normSq (blockFrameM p k U ω E v G').det) * blockClockSpeed p k ω E v by
          ring,
      ENNReal.ofReal_mul (mul_nonneg ha (Complex.normSq_nonneg _)), mul_assoc]
  · rw [ite_eq_right hc]; simp

/-- Mass integrand: with the block weight `p_{αk}` in the observable, the speed cancels. -/
theorem oneBlockPalm_mass_integrand (α : Fin p.N)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (h1 : ω.1.IsHermitian) (E : ℝ)
    (hD : (ω.1 - (E : ℂ) • 1).det ≠ 0) (v : BlockSite p k → ℂ) (hv : l2Norm v = 1)
    (G' : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ) (hG' : G'.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a) (f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞) :
    ENNReal.ofReal (a * blockClockSpeed p k ω E v *
          Complex.normSq (blockFrameM p k U ω E v G').det) *
        (if negativeCount (blockFrameM p k U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) =
          α.val then 1 else 0) *
        (ENNReal.ofReal (physicalOrderedBlockMass p
            (assembleBlock p k ω (oneBlockPalmRecon p k U ω E v G')) α k) *
          f (physicalOrderedEigenvalue p
              (assembleBlock p k ω (oneBlockPalmRecon p k U ω E v G')) α)
            (blockMassVector p (assembleBlock p k ω (oneBlockPalmRecon p k U ω E v G')) α)) =
      ENNReal.ofReal (a * Complex.normSq (blockFrameM p k U ω E v G').det) *
        (if negativeCount (blockFrameM p k U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) =
          α.val then 1 else 0) *
        f E (blockReconMass p k ω E v) := by
  by_cases hM : (blockFrameM p k U ω E v G').det = 0
  · simp [hM]
  by_cases hc : negativeCount (blockFrameM p k U ω E v G') +
      negativeCount (ω.1 - (E : ℂ) • 1) = α.val
  · obtain ⟨hlam, hbm, hsm⟩ :=
      oneBlockPalm_reconstruction p k α U hU ω h1 E v G' hG' hv hD hM hc
    rw [hlam, hbm, ite_eq_left hc, mul_one, mul_one, ← mul_assoc,
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg ha
        (oneBlockPalm_clockSpeed_nonneg p k ω E v)) (Complex.normSq_nonneg _))]
    congr 2
    linear_combination (a * Complex.normSq (blockFrameM p k U ω E v G').det) * hsm
  · rw [ite_eq_right hc]; simp

end Integrands

/-!
## The fixed-exterior fiber in sector form
-/

section Fiber

variable (p : Parameters) (k : ZMod p.n)

/-- Fixed-exterior one-block coarea fiber in the sector form
`∫ de Σ_ℓ 1{ℓ + N_-(H_R - e) = α} 𝒜⁰_{ℓ,e}[g_e]`, whenever the integrands agree for every
pole-free `E`, unit `v` and Hermitian `G'`. -/
theorem oneBlockPalm_coareaFiber_eq_sector (α : Fin p.N)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (Φ : Matrix (BlockSite p k) (BlockSite p k) ℂ → ℝ≥0∞)
    (g : ℝ → (BlockSite p k → ℂ) → ℝ≥0∞)
    (hpt : ∀ E : ℝ, (ω.1 - (E : ℂ) • 1).det ≠ 0 → ∀ v : BlockSite p k → ℂ, l2Norm v = 1 →
      ∀ G' : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ, G'.IsHermitian →
      ENNReal.ofReal (coareaConstant p.W (blockTime p) *
          regressionFactor (blockTime p) E v (blockF p k ω E) *
          blockClockSpeed p k ω E v * Complex.normSq (blockFrameM p k U ω E v G').det) *
        (if negativeCount (blockFrameM p k U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) =
          α.val then 1 else 0) * Φ (oneBlockPalmRecon p k U ω E v G') =
      ENNReal.ofReal (coareaConstant p.W (blockTime p) *
          regressionFactor (blockTime p) E v (blockF p k ω E) *
          Complex.normSq (blockFrameM p k U ω E v G').det) *
        (if negativeCount (blockFrameM p k U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) =
          α.val then 1 else 0) * g E v) :
    oneBlockPalmCoareaFiber p k α U ω Φ =
      ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range p.W,
          (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          blockSectorFiber p k U ω e ℓ (g e) := by
  have := oneBlockPalm_nonempty_blockSite p k
  unfold oneBlockPalmCoareaFiber
  refine lintegral_congr_ae ?_
  filter_upwards [oneBlockPalm_ae_det_shift_ne_zero p k ω.1] with E hE
  refine Eq.trans ?_ (Eq.trans (sector_lintegral (projectiveHaar (BlockSite p k))
    (gueMeasure (BlockFrameIndex p) (blockTime p)) p.W
    (fun v G' => negativeCount (blockFrameM p k U ω E v G'))
    (fun v G' => oneBlockPalm_negativeCount_frame_lt p _)
    (negativeCount (ω.1 - (E : ℂ) • 1)) α.val
    (fun v G' => ENNReal.ofReal (coareaConstant p.W (blockTime p) *
        regressionFactor (blockTime p) E v (blockF p k ω E) *
        Complex.normSq (blockFrameM p k U ω E v G').det))
    (fun v _ => g E v)) ?_)
  swap
  · rfl
  refine lintegral_congr_ae ?_
  filter_upwards [ProjectiveHaar.ae_l2Norm_projectiveHaar (BlockSite p k)] with v hv
  refine lintegral_congr_ae ?_
  filter_upwards [GUELaw.ae_isHermitian_gueMeasure (ι := BlockFrameIndex p)
    (blockTime p)] with G' hG'
  exact hpt E hE v hv G' hG'

theorem oneBlockPalm_coareaConstant_mul_regression_nonneg (t : ℝ≥0) (E : ℝ)
    (v : BlockSite p k → ℂ) (F : Matrix (BlockSite p k) (BlockSite p k) ℂ) :
    0 ≤ coareaConstant p.W t * regressionFactor t E v F :=
  mul_nonneg (by unfold coareaConstant; positivity) (Real.exp_pos _).le

end Fiber

/-!
## Measurability of the one-block angular fiber in the energy
-/

section Measurability

variable (p : Parameters) (k : ZMod p.n)

theorem oneBlockPalm_measurable_shift (H_R : Matrix (OffBlockSite p k) (OffBlockSite p k) ℂ) :
    Measurable fun E : ℝ =>
      H_R - (E : ℂ) • (1 : Matrix (OffBlockSite p k) (OffBlockSite p k) ℂ) := by
  apply Measurable.of_eval_matrix
  intro a b
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  fun_prop

theorem oneBlockPalm_measurable_resolvent
    (H_R : Matrix (OffBlockSite p k) (OffBlockSite p k) ℂ) :
    Measurable fun E : ℝ => physicalCoareaResolvent H_R E :=
  CoareaNative.BlockBand.Measurable.matrixNonsingInv (oneBlockPalm_measurable_shift p k H_R)

theorem oneBlockPalm_measurable_coareaT (ω : BlockState p k) :
    Measurable fun E : ℝ => physicalCoareaT ω.1 ω.2 E :=
  CoareaNative.BlockBand.measurable_matrix_mul_rect (oneBlockPalm_measurable_resolvent p k ω.1)
    measurable_const

theorem oneBlockPalm_measurable_blockF (ω : BlockState p k) :
    Measurable fun E : ℝ => blockF p k ω E := by
  unfold blockF physicalCoareaF
  exact FixedOmega.measurable_matrix_sub measurable_const
    (CoareaNative.BlockBand.measurable_matrix_mul_rect
      (CoareaNative.BlockBand.measurable_matrix_mul_rect measurable_const
        (oneBlockPalm_measurable_resolvent p k ω.1)) measurable_const)

theorem oneBlockPalm_measurable_coareaD (ω : BlockState p k) :
    Measurable fun E : ℝ => physicalCoareaD ω.1 ω.2 E := by
  unfold physicalCoareaD schurClock
  have hT := oneBlockPalm_measurable_coareaT p k ω
  exact FixedOmega.measurable_matrix_add measurable_const
    (CoareaNative.BlockBand.measurable_matrix_mul_rect
      (CoareaNative.BlockBand.Measurable.matrix_conjTranspose hT) hT)

/-- `(E, v) ↦ v*D(E)v` is measurable. -/
theorem oneBlockPalm_measurable_clockSpeed_joint (ω : BlockState p k) :
    Measurable fun x : ℝ × (BlockSite p k → ℂ) => blockClockSpeed p k ω x.1 x.2 := by
  unfold blockClockSpeed
  exact Complex.measurable_re.comp (measurable_star_dotProduct' measurable_snd
    (measurable_mulVec' ((oneBlockPalm_measurable_coareaD p k ω).comp measurable_fst)
      measurable_snd))

/-- `(E, v) ↦ L_E v` is measurable. -/
theorem oneBlockPalm_measurable_blockLift_joint (ω : BlockState p k) :
    Measurable fun x : ℝ × (BlockSite p k → ℂ) => blockLift p k ω x.1 x.2 := by
  have hTv : Measurable fun x : ℝ × (BlockSite p k → ℂ) => physicalCoareaT ω.1 ω.2 x.1 *ᵥ x.2 :=
    measurable_mulVec' ((oneBlockPalm_measurable_coareaT p k ω).comp measurable_fst)
      measurable_snd
  refine Measurable.of_eval fun y => ?_
  unfold blockLift
  by_cases hy : y.1 = k
  · simp only [hy, dite_true]
    exact (measurable_pi_apply _).comp measurable_snd
  · simp only [hy, dite_false]
    exact ((measurable_pi_apply _).comp hTv).neg

/-- `(E, v) ↦ p(v, E)` (`blockReconMass`) is measurable. -/
theorem oneBlockPalm_measurable_reconMass_joint (ω : BlockState p k) :
    Measurable fun x : ℝ × (BlockSite p k → ℂ) => blockReconMass p k ω x.1 x.2 := by
  refine Measurable.of_eval fun j => ?_
  unfold blockReconMass
  refine Measurable.div (Finset.measurable_sum _ fun a _ => ?_)
    (oneBlockPalm_measurable_clockSpeed_joint p k ω)
  exact (((measurable_pi_apply _).comp
    (oneBlockPalm_measurable_blockLift_joint p k ω)).norm).pow_const 2

/-- `((E, v), G') ↦ M` is measurable. -/
theorem oneBlockPalm_measurable_frameM_joint
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (ω : BlockState p k) :
    Measurable fun q : (ℝ × (BlockSite p k → ℂ)) ×
        Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ =>
      blockFrameM p k U ω q.1.1 q.1.2 q.2 := by
  have hU1 : Measurable fun q : (ℝ × (BlockSite p k → ℂ)) ×
      Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ => U q.1.2 :=
    hU.comp (measurable_snd.comp measurable_fst)
  have hF : Measurable fun q : (ℝ × (BlockSite p k → ℂ)) ×
      Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ => blockF p k ω q.1.1 :=
    (oneBlockPalm_measurable_blockF p k ω).comp (measurable_fst.comp measurable_fst)
  have hE : Measurable fun q : (ℝ × (BlockSite p k → ℂ)) ×
      Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ =>
      ((q.1.1 : ℝ) : ℂ) • (1 : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ) := by
    apply Measurable.of_eval_matrix
    intro a b
    simp only [Matrix.smul_apply]
    exact (Complex.measurable_ofReal.comp (measurable_fst.comp measurable_fst)).smul
      measurable_const
  unfold blockFrameM
  exact FixedOmega.measurable_matrix_sub (FixedOmega.measurable_matrix_add
    (CoareaNative.BlockBand.measurable_matrix_mul_rect
      (CoareaNative.BlockBand.measurable_matrix_mul_rect
        (CoareaNative.BlockBand.Measurable.matrix_conjTranspose hU1) hF) hU1) measurable_snd) hE

/-- `(E, v) ↦ 𝓡(E, v, F(E))` is measurable. -/
theorem oneBlockPalm_measurable_regression_joint (ω : BlockState p k) (t : ℝ) :
    Measurable fun x : ℝ × (BlockSite p k → ℂ) =>
      regressionFactor t x.1 x.2 (blockF p k ω x.1) := by
  have hg : Measurable fun x : ℝ × (BlockSite p k → ℂ) => (x.1, x.2, blockF p k ω x.1) :=
    measurable_fst.prodMk (measurable_snd.prodMk
      ((oneBlockPalm_measurable_blockF p k ω).comp measurable_fst))
  have h1 := measurable_regressionFactor_joint (ι := BlockSite p k) t
  have h2 := h1.comp hg
  exact h2

/-- The integrand of `𝒜⁰_{ℓ,e}` is jointly measurable in `((e, v), G')`. -/
theorem oneBlockPalm_measurable_sectorIntegrand
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (ω : BlockState p k) (ℓ : ℕ)
    (g : ℝ → (BlockSite p k → ℂ) → ℝ≥0∞) (hg : Measurable (Function.uncurry g)) :
    Measurable fun q : (ℝ × (BlockSite p k → ℂ)) ×
        Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ =>
      ENNReal.ofReal (coareaConstant p.W (blockTime p) *
          regressionFactor (blockTime p) q.1.1 q.1.2 (blockF p k ω q.1.1) *
          Complex.normSq (blockFrameM p k U ω q.1.1 q.1.2 q.2).det) *
        (if negativeCount (blockFrameM p k U ω q.1.1 q.1.2 q.2) = ℓ then 1 else 0) *
        g q.1.1 q.1.2 := by
  have hM := oneBlockPalm_measurable_frameM_joint p k U hU ω
  have hR : Measurable fun q : (ℝ × (BlockSite p k → ℂ)) ×
      Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ =>
      regressionFactor (blockTime p) q.1.1 q.1.2 (blockF p k ω q.1.1) :=
    (oneBlockPalm_measurable_regression_joint p k ω (blockTime p)).comp measurable_fst
  have hdet : Measurable fun q : (ℝ × (BlockSite p k → ℂ)) ×
      Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ =>
      Complex.normSq (blockFrameM p k U ω q.1.1 q.1.2 q.2).det :=
    Complex.continuous_normSq.measurable.comp ((continuous_id.matrix_det).measurable.comp hM)
  have hind : Measurable fun q : (ℝ × (BlockSite p k → ℂ)) ×
      Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ =>
      (if negativeCount (blockFrameM p k U ω q.1.1 q.1.2 q.2) = ℓ then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_eq_fun ((FixedOmega.measurable_negativeCount _).comp hM)
      measurable_const) measurable_const measurable_const
  have hgq : Measurable fun q : (ℝ × (BlockSite p k → ℂ)) ×
      Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ => g q.1.1 q.1.2 := hg.comp measurable_fst
  exact ((ENNReal.measurable_ofReal.comp ((measurable_const.mul hR).mul hdet)).mul hind).mul hgq

/-- `e ↦ 𝒜⁰_{ℓ,e}[g(e, ·)]` is measurable in the energy. -/
theorem oneBlockPalm_measurable_blockSectorFiber
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (ω : BlockState p k) (ℓ : ℕ)
    (g : ℝ → (BlockSite p k → ℂ) → ℝ≥0∞) (hg : Measurable (Function.uncurry g)) :
    Measurable fun e : ℝ => blockSectorFiber p k U ω e ℓ (g e) := by
  have h2 := (oneBlockPalm_measurable_sectorIntegrand p k U hU ω ℓ g hg).lintegral_prod_right'
    (ν := gueMeasure (BlockFrameIndex p) (blockTime p))
  have h3 := h2.lintegral_prod_right' (ν := projectiveHaar (BlockSite p k))
  unfold blockSectorFiber
  exact h3

theorem oneBlockPalm_measurable_offShiftCount (ω : BlockState p k) :
    Measurable fun e : ℝ => negativeCount (ω.1 - (e : ℂ) • 1) :=
  (FixedOmega.measurable_negativeCount _).comp (oneBlockPalm_measurable_shift p k ω.1)

end Measurability

/-!
## The rank indicator sums to one
-/

theorem oneBlockPalm_card_offBlockSite_add (p : Parameters) (k : ZMod p.n) :
    Fintype.card (OffBlockSite p k) + p.W = p.N := by
  classical
  have h1 := Fintype.card_subtype_compl (fun x : p.Site => x.1 = k)
  have h2 := regularEvent_card_blockSite p k
  have h3 : Fintype.card p.Site = p.N := by
    simp [Parameters.N, Fintype.card_prod, ZMod.card]
  have h4 := Fintype.card_subtype_le (fun x : p.Site => x.1 = k)
  have h5 : Fintype.card (OffBlockSite p k) = Fintype.card {x : p.Site // ¬ x.1 = k} := rfl
  have h6 : Fintype.card (BlockSite p k) = Fintype.card {x : p.Site // x.1 = k} := rfl
  omega

/-- `Σ_α 1{ℓ + N_-(H_R - e) = α} = 1` for every attainable sector `ℓ < W`. -/
theorem oneBlockPalm_sum_rank_indicator (p : Parameters) (k : ZMod p.n)
    (M : Matrix (OffBlockSite p k) (OffBlockSite p k) ℂ) (ℓ : ℕ) (hℓ : ℓ < p.W) :
    (∑ α : Fin p.N, (if ℓ + negativeCount M = α.val then (1 : ℝ≥0∞) else 0)) = 1 := by
  have hc := negativeCount_le_card M
  have hN := oneBlockPalm_card_offBlockSite_add p k
  have hlt : ℓ + negativeCount M < p.N := by omega
  rw [Finset.sum_eq_single_of_mem (⟨ℓ + negativeCount M, hlt⟩ : Fin p.N) (Finset.mem_univ _)]
  · simp
  · intro β _ hβ
    rw [ite_eq_right]
    intro h
    exact hβ (Fin.ext h.symm)

/-!
## The fixed-exterior fibers
-/

section FixedExterior

/-- Fixed-exterior form of the one-block `mass` identity: for `Pω`-a.e. `ω`,
`∫ dGUE_W(c/W)(G) Σ_α p_{αk} f(λ_α, p_α)(assembleBlock ω G) = ∫ Σ_ℓ 𝒜⁰_{ℓ,e}[f(e,p(v,e))] de`. -/
theorem oneBlockPalm_massFiber_ae (p : Parameters) (model : p.GaussianRingModel)
    (k : ZMod p.n) (Pω : Measure (BlockState p k)) (hP : IsBlockSplitting p k model Pω)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) :
    ∀ᵐ ω ∂Pω, (∫⁻ G, ∑ α : Fin p.N,
        ENNReal.ofReal (physicalOrderedBlockMass p (assembleBlock p k ω G) α k) *
        f (physicalOrderedEigenvalue p (assembleBlock p k ω G) α)
          (blockMassVector p (assembleBlock p k ω G) α)
        ∂(gueMeasure (BlockSite p k) (blockTime p))) =
      ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range p.W,
          blockSectorFiber p k U ω e ℓ (fun v => f e (blockReconMass p k ω e v)) := by
  have hA := regularEvent_measurable_assembleBlock p k
  have hobsα : ∀ α : Fin p.N, Measurable fun H : p.SiteMatrix =>
      ENNReal.ofReal (physicalOrderedBlockMass p H α k) *
        f (physicalOrderedEigenvalue p H α) (blockMassVector p H α) := fun α =>
    (ENNReal.measurable_ofReal.comp (measurable_physicalOrderedBlockMass p α k)).mul
      (hf.comp ((measurable_physicalOrderedEigenvalue p α).prodMk
        (Measurable.of_eval fun j => measurable_physicalOrderedBlockMass p α j)))
  filter_upwards [oneBlockPalm_ae_isHermitian p k hP,
    ae_all_iff.2 fun α : Fin p.N => oneBlockPalm_formula_fixed p model α k Pω hP U hU]
    with ω hω hfix
  have hAω : Measurable fun G : Matrix (BlockSite p k) (BlockSite p k) ℂ =>
      assembleBlock p k ω G := hA.comp measurable_prodMk_left
  rw [lintegral_finsetSum Finset.univ (f := fun (α : Fin p.N)
      (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) =>
      ENNReal.ofReal (physicalOrderedBlockMass p (assembleBlock p k ω G) α k) *
        f (physicalOrderedEigenvalue p (assembleBlock p k ω G) α)
          (blockMassVector p (assembleBlock p k ω G) α)) fun α _ => (hobsα α).comp hAω]
  have hfib : ∀ α : Fin p.N,
      (∫⁻ G, ENNReal.ofReal (physicalOrderedBlockMass p (assembleBlock p k ω G) α k) *
        f (physicalOrderedEigenvalue p (assembleBlock p k ω G) α)
          (blockMassVector p (assembleBlock p k ω G) α)
        ∂(gueMeasure (BlockSite p k) (blockTime p))) =
      ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range p.W,
          (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          blockSectorFiber p k U ω e ℓ (fun v => f e (blockReconMass p k ω e v)) := by
    intro α
    refine (hfix α _ ((hobsα α).comp hAω)).trans ?_
    refine oneBlockPalm_coareaFiber_eq_sector p k α U ω _
      (fun e v => f e (blockReconMass p k ω e v)) fun E hE v hv G' hG' => ?_
    exact oneBlockPalm_mass_integrand p k α U hU ω hω E hE v hv G' hG' _
      (oneBlockPalm_coareaConstant_mul_regression_nonneg p k _ E v _) f
  rw [Finset.sum_congr rfl fun α _ => hfib α]
  have hgm : Measurable (Function.uncurry fun (e : ℝ) (v : BlockSite p k → ℂ) =>
      f e (blockReconMass p k ω e v)) :=
    hf.comp (measurable_fst.prodMk (oneBlockPalm_measurable_reconMass_joint p k ω))
  have hfibm : ∀ ℓ, Measurable fun e : ℝ =>
      blockSectorFiber p k U ω e ℓ (fun v => f e (blockReconMass p k ω e v)) := fun ℓ =>
    oneBlockPalm_measurable_blockSectorFiber p k U hU.1 ω ℓ
      (fun e v => f e (blockReconMass p k ω e v)) hgm
  have hNR := oneBlockPalm_measurable_offShiftCount p k ω
  rw [← lintegral_finsetSum Finset.univ (f := fun (α : Fin p.N) (e : ℝ) =>
      ∑ ℓ ∈ Finset.range p.W,
        (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          blockSectorFiber p k U ω e ℓ (fun v => f e (blockReconMass p k ω e v)))
    fun α _ => Finset.measurable_sum _ fun ℓ _ =>
      (Measurable.ite (measurableSet_eq_fun (hNR.const_add ℓ) measurable_const)
        measurable_const measurable_const).mul (hfibm ℓ)]
  refine lintegral_congr fun e => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [← Finset.sum_mul, oneBlockPalm_sum_rank_indicator p k _ ℓ (Finset.mem_range.1 hℓ),
    one_mul]

/-- Fixed-exterior form of the one-block `index` identity. -/
theorem oneBlockPalm_indexFiber_ae (p : Parameters) (model : p.GaussianRingModel)
    (k : ZMod p.n) (Pω : Measure (BlockState p k)) (hP : IsBlockSplitting p k model Pω)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (α : Fin p.N) (f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) :
    ∀ᵐ ω ∂Pω, (∫⁻ G, f (physicalOrderedEigenvalue p (assembleBlock p k ω G) α)
          (blockMassVector p (assembleBlock p k ω G) α)
        ∂(gueMeasure (BlockSite p k) (blockTime p))) =
      ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range p.W,
          (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          blockSectorFiber p k U ω e ℓ
            (fun v => ENNReal.ofReal (blockClockSpeed p k ω e v) *
              f e (blockReconMass p k ω e v)) := by
  have hA := regularEvent_measurable_assembleBlock p k
  have hobs : Measurable fun H : p.SiteMatrix =>
      f (physicalOrderedEigenvalue p H α) (blockMassVector p H α) :=
    hf.comp ((measurable_physicalOrderedEigenvalue p α).prodMk
      (Measurable.of_eval fun j => measurable_physicalOrderedBlockMass p α j))
  filter_upwards [oneBlockPalm_ae_isHermitian p k hP,
      oneBlockPalm_formula_fixed p model α k Pω hP U hU] with ω hω hfix
  rw [hfix (fun G => f (physicalOrderedEigenvalue p (assembleBlock p k ω G) α)
      (blockMassVector p (assembleBlock p k ω G) α)) (hobs.comp (hA.comp measurable_prodMk_left))]
  refine oneBlockPalm_coareaFiber_eq_sector p k α U ω _ _ fun E hE v hv G' hG' => ?_
  exact oneBlockPalm_index_integrand p k α U hU ω hω E hE v hv G' hG' _
    (oneBlockPalm_coareaConstant_mul_regression_nonneg p k _ E v _) f

end FixedExterior

/-!
## `mass` and `index`
-/

/-- **`OneBlockPalmContract.mass`** (the one-block corollary of the mass Palm identity): for
measurable `f ≥ 0`, `E Σ_α p_{αk} f(λ_α, p_α) = E_ext ∫ Σ_ℓ 𝒜⁰_{ℓ,e}[f(e, p(v,e))] de`.
Measures: the exact physical law on the left; `Pω`, Lebesgue `de`, `projectiveHaar` and
`GUE_{W-1}(c/W)` on the right. Exact identity in `[0,∞]`; no contract is used. -/
theorem oneBlockPalm_mass : ∀ (p : Parameters) (model : p.GaussianRingModel) (k : ZMod p.n)
    (Pω : Measure (BlockState p k)), IsBlockSplitting p k model Pω →
    ∀ U, IsBlockFrame p k U → ∀ f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞, Measurable (Function.uncurry f) →
      (∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (physicalOrderedBlockMass p H α k) *
          f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫⁻ ω, ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range p.W,
          blockSectorFiber p k U ω e ℓ (fun v => f e (blockReconMass p k ω e v)) ∂volume ∂Pω := by
  intro p model k Pω hP U hU f hf
  have hA := regularEvent_measurable_assembleBlock p k
  have hobs : Measurable fun H : p.SiteMatrix => ∑ α : Fin p.N,
      ENNReal.ofReal (physicalOrderedBlockMass p H α k) *
        f (physicalOrderedEigenvalue p H α) (blockMassVector p H α) :=
    Finset.measurable_sum _ fun α _ =>
      (ENNReal.measurable_ofReal.comp (measurable_physicalOrderedBlockMass p α k)).mul
        (hf.comp ((measurable_physicalOrderedEigenvalue p α).prodMk
          (Measurable.of_eval fun j => measurable_physicalOrderedBlockMass p α j)))
  have hg : Measurable fun z : BlockState p k × Matrix (BlockSite p k) (BlockSite p k) ℂ =>
      ∑ α : Fin p.N, ENNReal.ofReal (physicalOrderedBlockMass p (assembleBlock p k z.1 z.2) α k) *
        f (physicalOrderedEigenvalue p (assembleBlock p k z.1 z.2) α)
          (blockMassVector p (assembleBlock p k z.1 z.2) α) := hobs.comp hA
  rw [← hP, lintegral_map hobs hA, lintegral_prod _ hg.aemeasurable]
  exact lintegral_congr_ae (oneBlockPalm_massFiber_ae p model k Pω hP U hU f hf)

/-- **`OneBlockPalmContract.index`** (the one-block corollary of the index Palm identity): for
measurable `f ≥ 0` and every rank `α`,
`E f(λ_α, p_α) = E_ext ∫ Σ_ℓ 1{ℓ + N_-(H_R - e) = α} 𝒜⁰_{ℓ,e}[(v*Dv) f(e, p(v,e))] de`.
Measures as in `oneBlockPalm_mass`. Exact identity in `[0,∞]`; no contract is used. -/
theorem oneBlockPalm_index : ∀ (p : Parameters) (model : p.GaussianRingModel) (k : ZMod p.n)
    (Pω : Measure (BlockState p k)), IsBlockSplitting p k model Pω →
    ∀ U, IsBlockFrame p k U → ∀ (α : Fin p.N) (f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞),
      Measurable (Function.uncurry f) →
      (∫⁻ H, f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫⁻ ω, ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range p.W,
          (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          blockSectorFiber p k U ω e ℓ
            (fun v => ENNReal.ofReal (blockClockSpeed p k ω e v) *
              f e (blockReconMass p k ω e v))
        ∂volume ∂Pω := by
  intro p model k Pω hP U hU α f hf
  have hA := regularEvent_measurable_assembleBlock p k
  have hobs : Measurable fun H : p.SiteMatrix =>
      f (physicalOrderedEigenvalue p H α) (blockMassVector p H α) :=
    hf.comp ((measurable_physicalOrderedEigenvalue p α).prodMk
      (Measurable.of_eval fun j => measurable_physicalOrderedBlockMass p α j))
  have hg : Measurable fun z : BlockState p k × Matrix (BlockSite p k) (BlockSite p k) ℂ =>
      f (physicalOrderedEigenvalue p (assembleBlock p k z.1 z.2) α)
        (blockMassVector p (assembleBlock p k z.1 z.2) α) := hobs.comp hA
  rw [← hP, lintegral_map hobs hA, lintegral_prod _ hg.aemeasurable]
  exact lintegral_congr_ae (oneBlockPalm_indexFiber_ae p model k Pω hP U hU α f hf)

end BlockBand.Endpoints.Normalization
