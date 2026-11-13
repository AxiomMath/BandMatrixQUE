module

public import BlockBand.Layers.CompensatedPhase

/-!
# The compensated ring phase `Ξ_{n-1}` (proof of the rank-location theorem)

The ring form of the compensated phase (`RingCompensatedPhaseContract`): delete block `k`, grow the
middle `n - 3` blocks with separate ports, and append the two end blocks with their bonds
to block `k` as one common-port layer.

* `cph_ring_identity`: by Schur inertia (`negativeCount_fromBlocks_schur22`, with
  `rng_HR_submatrix`) and the deterministic Schur composition `rng_oneBlockComplement`,
  `Ξ_{n-1}(H) = Ψ_{n-3}(π) + N_-(A - E - X_{n-3}) + Θ_{z₀}(Σ) - Θ_{z_∂}(X_{n-3})` for
  `(ℓ, π) = rngSplit k ω`, `H = rngAssemble ω`, almost surely.
* `ringCompensatedPhase_of_inputs`: `RingCompensatedPhaseContract` from the matched traces, the
  conditional mean increments (both shapes), and the inputs `CphIncrementFluctuation`, `CphCore`
  of `BlockBand.Layers.CompensatedPhase` (through the compensated-phase lemma at `r = n - 3`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm (negativeCount)
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
## 1. The ring phase and its Borel version
-/

section RingPhase

variable {p : Parameters}

/-- Borel version of `Ξ_{n-1}`. -/
def cphXiM (p : Parameters) (k : ZMod p.n) (E : ℝ) (H : p.SiteMatrix) : ℝ :=
  cphRawSum cphNegInd (rngHR k H - (E : ℂ) • 1) +
    cphPhase (commonZ p.b E) (oneBlockComplement p k H E)

theorem cph_measurable_rngHR (k : ZMod p.n) :
    Measurable (fun H : p.SiteMatrix => rngHR k H) :=
  measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y =>
    (measurable_pi_apply y.1).comp (measurable_pi_apply x.1)

theorem cph_measurable_oneBlockComplement (k : ZMod p.n) (E : ℝ) :
    Measurable (fun H : p.SiteMatrix => oneBlockComplement p k H E) := by
  have hC : Measurable (fun H : p.SiteMatrix => rngC k H) :=
    measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y =>
      (measurable_pi_apply y.1).comp (measurable_pi_apply x.1)
  simp_rw [rng_oneBlockComplement_eq]
  exact srec_measurable_mul (srec_measurable_mul (srec_measurable_conjTranspose hC)
    (measurable_matrix_inv.comp ((cph_measurable_rngHR k).sub measurable_const))) hC

theorem cph_measurable_xiM (k : ZMod p.n) (E : ℝ) : Measurable (cphXiM p k E) :=
  ((cph_measurable_rawSum cph_measurable_negInd).comp
    ((cph_measurable_rngHR k).sub measurable_const)).add
    ((cph_measurable_phase _).comp (cph_measurable_oneBlockComplement k E))

theorem cph_rngHR_isHermitian {k : ZMod p.n} {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) :
    (rngHR k H - (E : ℂ) • 1).IsHermitian :=
  cph_isHermitian_sub (hH.submatrix (fun x : OffBlockSite p k => x.1)) E

theorem cph_xi_eq {k : ZMod p.n} {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) :
    ringCompensatedPhase p k H E = cphXiM p k E H := by
  have hS : (oneBlockComplement p k H E).IsHermitian := by
    rw [rng_oneBlockComplement_eq]
    exact isHermitian_conjTranspose_mul_mul _ (cph_rngHR_isHermitian hH E).inv
  change (negativeCount (rngHR k H - (E : ℂ) • 1) : ℝ) +
    phaseCount (commonZ p.b E) (oneBlockComplement p k H E) = _
  unfold cphXiM
  rw [cph_negativeCount_eq_rawSum, cph_phaseCount_eq hS]

theorem cph_ring_ae_herm (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), H.IsHermitian := by
  rw [rng_law_eq_map model]
  refine (ae_map_iff rng_measurable_assemble.aemeasurable
    BlockBand.Model.Construction.measurableSet_isHermitian).mpr ?_
  filter_upwards [rng_ae_blocks_isHermitian] with ω hω
  exact rngAssemble_isHermitian ω hω

theorem cph_xi_ae_eq (model : p.GaussianRingModel) (k : ZMod p.n) (E : ℝ) :
    (fun H => ringCompensatedPhase p k H E) =ᵐ[(model.law : Measure p.SiteMatrix)] cphXiM p k E := by
  filter_upwards [cph_ring_ae_herm model] with H hH
  exact cph_xi_eq hH E

theorem cph_abs_xiM_le {k : ZMod p.n} {E : ℝ} (hz0 : 0 ≤ (commonZ p.b E).im) (H : p.SiteMatrix) :
    |cphXiM p k E H| ≤ 2 * (p.n * p.W) := by
  have hcard1 : (Fintype.card (OffBlockSite p k) : ℝ) ≤ p.n * p.W := by
    have := Fintype.card_subtype_le (fun x : p.Site => x.1 ≠ k)
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fin] at this
    exact_mod_cast this
  have hcard2 : (Fintype.card (BlockSite p k) : ℝ) ≤ p.n * p.W := by
    have := Fintype.card_subtype_le (fun x : p.Site => x.1 = k)
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fin] at this
    exact_mod_cast this
  have h0 := cph_rawNeg_nonneg (rngHR k H - (E : ℂ) • 1)
  have h1 := cph_rawNeg_le (rngHR k H - (E : ℂ) • 1)
  have h2 := cph_phase_nonneg hz0 (oneBlockComplement p k H E)
  have h3 := cph_phase_le (commonZ p.b E) (oneBlockComplement p k H E)
  unfold cphXiM
  rw [abs_le]
  constructor <;> linarith

/-- **The ring identity** (Schur inertia and the deterministic common-port composition). -/
theorem cph_ring_identity (ω : RngSample p) (k : ZMod p.n) (E : ℝ)
    (hA : ∀ j, (ω.1 j).IsHermitian)
    (hH : IsUnit (pathMatrix (rngSplit k ω).2 - (E : ℂ) • 1).det)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag (rngSplit k ω).1.1 - (E : ℂ) • 1 -
      pathSchur E (rngSplit k ω).2).det) :
    ringCompensatedPhase p k (rngAssemble p ω) E =
      compensatedPhase p.b E (rngSplit k ω).2 +
        cphComIncrement p.b E (pathSchur E (rngSplit k ω).2) (rngSplit k ω).1 := by
  have hHh := rngAssemble_isHermitian ω hA
  have hHR := cph_rngHR_isHermitian (k := k) hHh E
  have hsub := hHR.submatrix (rngSiteEquiv k)
  rw [rng_HR_submatrix] at hsub
  have hM : (Matrix.fromBlocks (Internal.Contracts.Layers.blockDiag (rngSplit k ω).1.1 -
      (E : ℂ) • 1) (pathPortCoupling (rngSplit k ω).2)ᴴ (pathPortCoupling (rngSplit k ω).2)ᴴᴴ
      (pathMatrix (rngSplit k ω).2 - (E : ℂ) • 1)).IsHermitian := by
    rw [conjTranspose_conjTranspose]; exact hsub
  have key := negativeCount_fromBlocks_schur22 hM hH.ne_zero
  rw [conjTranspose_conjTranspose] at key
  have hN : negativeCount (rngHR k (rngAssemble p ω) - (E : ℂ) • 1) =
      pathCount E (rngSplit k ω).2 + negativeCount (Internal.Contracts.Layers.blockDiag
        (rngSplit k ω).1.1 - (E : ℂ) • 1 - pathSchur E (rngSplit k ω).2) := by
    rw [← cph_negativeCount_submatrix (rngSiteEquiv k) hHR, rng_HR_submatrix, key]
    rfl
  have hP : phaseCount (commonZ p.b E) (oneBlockComplement p k (rngAssemble p ω) E) =
      phaseCount (commonZ p.b E) (layerSchur .common E (pathSchur E (rngSplit k ω).2)
        (rngSplit k ω).1) := by
    rw [← cph_phaseCount_submatrix (commonZ p.b E) (rngPortEquiv k),
      rng_oneBlockComplement ω k E hH hS]
  change (negativeCount (rngHR k (rngAssemble p ω) - (E : ℂ) • 1) : ℝ) +
    phaseCount (commonZ p.b E) (oneBlockComplement p k (rngAssemble p ω) E) = _
  unfold compensatedPhase cphComIncrement
  rw [hN, hP]
  push_cast
  ring

/-- The Borel ring identity, almost surely under the ring sample law. -/
theorem cph_ae_ring (k : ZMod p.n) (E : ℝ) :
    ∀ᵐ ω ∂rngLaw p, cphXiM p k E (rngAssemble p ω) =
      cphPsiM p.b E (rngSplit k ω).2 +
        cphComIncrementM p.b E (pathSchur E (rngSplit k ω).2) (rngSplit k ω).1 := by
  filter_upwards [rng_ae_blocks_isHermitian,
    (rng_mp_split k).quasiMeasurePreserving.ae (rng_ae_invertible p.b_lt_half E)]
    with ω hA hinv
  have hpath : ∀ j, ((rngSplit k ω).2.1 j).IsHermitian := fun j => hA _
  have hlay : ∀ j, ((rngSplit k ω).1.1 j).IsHermitian := fun j => hA _
  rw [← cph_xi_eq (rngAssemble_isHermitian ω hA) E, cph_ring_identity ω k E hA hinv.1 hinv.2,
    cph_psi_eq hpath, cph_comIncrement_eq p.b E (srec_pathSchur_isHermitian E _ hpath) hlay]

end RingPhase

/-!
## 2. Transfer to the layer-path product
-/

section Transfer

variable {p : Parameters}

/-- The Borel common-port conditional mean. -/
def cphComMean (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  ∫ ℓ, cphComIncrementM b E X ℓ ∂layerLaw W b .common

theorem cph_measurable_comMean (b E : ℝ) (W : ℕ) :
    Measurable (fun X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => cphComMean b E X) := by
  have hF : Measurable (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      LayerSample W .common => cphComIncrementM b E q.1 q.2) :=
    cph_measurable_comIncrementM b E measurable_fst measurable_snd
  exact (hF.stronglyMeasurable.integral_prod_right').measurable

theorem cph_abs_comMean_le {b E : ℝ} (hz : 0 ≤ (boundaryZ b E).im) (hz0 : 0 ≤ (commonZ b E).im)
    {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : |cphComMean b E X| ≤ 6 * W :=
  cph_abs_integral_le fun ℓ => cph_abs_comIncrementM_le hz hz0 X ℓ

theorem cph_comIncrement_ae_eq (b E : ℝ) {W : ℕ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) :
    (cphComIncrement b E X) =ᵐ[layerLaw W b .common] cphComIncrementM b E X := by
  filter_upwards [lct_ae_blocks_isHermitian W b .common] with ℓ hℓ
  exact cph_comIncrement_eq b E hX hℓ

theorem cph_comMean_eq {b κ E : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ)
    {W : ℕ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    cphComMean b E X = (∫ ω, ((negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
        phaseCount (commonZ b E) (layerSchur .common E X ω)) ∂layerLaw W b .common) -
      phaseCount (boundaryZ b E) X := by
  have hz0 := cph_commonZ_im_nonneg hb hκ hE
  unfold cphComMean
  rw [← integral_congr_ae (cph_comIncrement_ae_eq b E hX)]
  unfold cphComIncrement
  have hmeas : AEStronglyMeasurable (fun ω : LayerSample W .common =>
      (negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
        phaseCount (commonZ b E) (layerSchur .common E X ω)) (layerLaw W b .common) := by
    have hm : Measurable (fun ω : LayerSample W .common =>
        cphRawSum cphNegInd (blockDiag ω.1 - (E : ℂ) • 1 - X) +
          cphPhase (commonZ b E) (layerSchur .common E X ω)) :=
      ((cph_measurable_rawSum cph_measurable_negInd).comp
        (cph_measurable_top E measurable_const measurable_fst)).add
        ((cph_measurable_phase _).comp
          (cph_measurable_layerSchur_common E measurable_const measurable_id))
    refine hm.aestronglyMeasurable.congr ?_
    filter_upwards [lct_ae_blocks_isHermitian W b .common] with ℓ hℓ
    rw [cph_negativeCount_eq_rawSum,
      cph_phaseCount_eq (rng_layerSchur_common_isHermitian E hX ℓ hℓ)]
  have hint : Integrable (fun ω : LayerSample W .common =>
      (negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
        phaseCount (commonZ b E) (layerSchur .common E X ω)) (layerLaw W b .common) := by
    refine cph_integrable_of_bound hmeas (B := 2 * W + 2 * W) fun ω => ?_
    have h1 := cph_negativeCount_le_two (blockDiag ω.1 - (E : ℂ) • 1 - X)
    have h2 := cph_abs_phaseCount_le hz0 (layerSchur .common E X ω)
    simp only [Fintype.card_prod, Fintype.card_fin] at h2
    push_cast at h2
    have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg _
    have h0 := Nat.cast_nonneg (α := ℝ) (negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X))
    rw [abs_le] at h2 ⊢
    constructor <;> linarith
  rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]

theorem cph_comMean_bound (hinc : CompensatedIncrementContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      X.IsHermitian → ∀ E ∈ bulkInterval κ,
        |cphComMean b E X - W * (phaseEll E + phaseH E)| ≤
          C * (W * matchedDistance b E X ^ 2 + (W : ℝ)⁻¹) := by
  obtain ⟨C, hC⟩ := hinc.common b hb0 hb1 κ hκ
  refine ⟨max C 0, le_max_right _ _, fun W hW X hX E hE => ?_⟩
  rw [cph_comMean_eq hb1 hκ hE hX]
  refine (hC W hW X hX E hE).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  positivity

theorem cph_comDev_bound (hfl : CphIncrementFluctuation) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) {q : ℝ} (hq : 1 ≤ q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      X.IsHermitian → ∀ E ∈ bulkInterval κ,
        eLpNorm (fun ℓ => cphComIncrementM b E X ℓ - cphComMean b E X) (ENNReal.ofReal q)
          (layerLaw W b .common) ≤ ENNReal.ofReal K := by
  obtain ⟨K, hK⟩ := hfl.common b hb0 hb1 κ hκ q hq
  refine ⟨max K 0, le_max_right _ _, fun W hW X hX E hE => ?_⟩
  have hae := cph_comIncrement_ae_eq b E hX (W := W)
  have hI : ∫ ℓ', cphComIncrement b E X ℓ' ∂layerLaw W b .common = cphComMean b E X :=
    integral_congr_ae hae
  have h := hK W hW X hX E hE
  rw [hI] at h
  refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) (h.trans (ENNReal.ofReal_le_ofReal
    (le_max_left _ _)))
  filter_upwards [hae] with ℓ hℓ
  rw [hℓ]

/-- The ring observable on the layer-path product. -/
def cphG (b E : ℝ) {W r : ℕ} (x : LayerSample W .common × PathSample W r) : ℝ :=
  cphPsiM b E x.2 + cphComIncrementM b E (pathSchur E x.2) x.1

theorem cph_measurable_G (b E : ℝ) (W r : ℕ) :
    Measurable (cphG b E (W := W) (r := r)) :=
  ((cph_measurable_psiM b E W r).comp measurable_snd).add
    (cph_measurable_comIncrementM b E ((measurable_pathSchur W r E).comp measurable_snd)
      measurable_fst)

theorem cph_integral_xi (model : p.GaussianRingModel) (k : ZMod p.n) (E : ℝ) :
    ∫ H, cphXiM p k E H ∂(model.law : Measure p.SiteMatrix) =
      ∫ x, cphG p.b E x ∂((layerLaw p.W p.b .common).prod (pathLaw p.W (p.n - 3) p.b)) := by
  rw [rng_law_eq_map model, integral_map rng_measurable_assemble.aemeasurable
    (cph_measurable_xiM k E).aestronglyMeasurable, integral_congr_ae (cph_ae_ring k E),
    ← (rng_mp_split k).map_eq, integral_map (rng_mp_split k).measurable.aemeasurable
    (cph_measurable_G p.b E _ _).aestronglyMeasurable]
  rfl

theorem cph_eLpNorm_xi (model : p.GaussianRingModel) (k : ZMod p.n) (E c : ℝ) (q : ℝ≥0∞) :
    eLpNorm (fun H => cphXiM p k E H - c) q (model.law : Measure p.SiteMatrix) =
      eLpNorm (fun x => cphG p.b E x - c) q
        ((layerLaw p.W p.b .common).prod (pathLaw p.W (p.n - 3) p.b)) := by
  rw [rng_law_eq_map model, eLpNorm_map_measure
    ((cph_measurable_xiM k E).sub_const c).aestronglyMeasurable
    rng_measurable_assemble.aemeasurable,
    ← eLpNorm_comp_measurePreserving ((cph_measurable_G p.b E _ _).sub_const c).aestronglyMeasurable
      (rng_mp_split k)]
  refine eLpNorm_congr_ae ?_
  filter_upwards [cph_ae_ring k E] with ω hω
  simp only [Function.comp_apply, cphG, hω]

theorem cph_integral_G {W r : ℕ} {b E : ℝ} (hz : 0 ≤ (boundaryZ b E).im)
    (hz0 : 0 ≤ (commonZ b E).im) :
    ∫ x, cphG b E x ∂((layerLaw W b .common).prod (pathLaw W r b)) =
      ∫ ω, cphPsiM b E ω ∂pathLaw W r b + ∫ ω, cphComMean b E (pathSchur E ω) ∂pathLaw W r b := by
  have hi1 : Integrable (fun x : LayerSample W .common × PathSample W r => cphPsiM b E x.2)
      ((layerLaw W b .common).prod (pathLaw W r b)) :=
    cph_integrable_of_bound ((cph_measurable_psiM b E W r).comp measurable_snd).aestronglyMeasurable
      fun x => cph_abs_psiM_le hz x.2
  have hi2 : Integrable (fun x : LayerSample W .common × PathSample W r =>
      cphComIncrementM b E (pathSchur E x.2) x.1) ((layerLaw W b .common).prod (pathLaw W r b)) :=
    cph_integrable_of_bound (cph_measurable_comIncrementM b E
      ((measurable_pathSchur W r E).comp measurable_snd) measurable_fst).aestronglyMeasurable
      fun x => cph_abs_comIncrementM_le hz hz0 _ _
  unfold cphG
  rw [integral_add hi1 hi2, cph_integral_comp_snd (cph_measurable_psiM b E W r),
    integral_prod_symm _ hi2]
  rfl

end Transfer

/-!
## 3. `RingCompensatedPhaseContract`
-/

section RingAssembly

theorem cph_n_sub_three (p : Parameters) : ((p.n - 3 : ℕ) : ℝ) = p.n - 3 := by
  have := p.n_ge_four
  rw [Nat.cast_sub (by omega)]; norm_num

/-- **The ring compensated phase, fluctuation clause.** -/
theorem cph_ring_fluctuation (hmt : MatchedTracesContract) (hinc : CompensatedIncrementContract)
    (hfl : CphIncrementFluctuation) (hcore : CphCore) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ q : ℝ, 1 ≤ q →
    ∃ Cq : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (k : ZMod p.n) (E : ℝ), E ∈ bulkInterval κ →
      eLpNorm (fun H => ringCompensatedPhase p k H E -
          ∫ H', ringCompensatedPhase p k H' E ∂(model.law : Measure p.SiteMatrix))
          (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) ≤
        ENNReal.ofReal (Cq * Real.sqrt p.n) := by
  intro b hb0 hb1 κ T hκ q hq
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈q / 2⌉₊ := ⟨_, rfl⟩
  have hm : 1 ≤ m := by
    rw [hmdef]; exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
  have hqm : q ≤ 2 * (m : ℝ) := by
    have := Nat.le_ceil (q / 2); rw [← hmdef] at this; linarith
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨Cf, hCf⟩ := cph_fluctuation hmt hinc hfl hcore b hb0 hb1 κ T hκ q hq
  obtain ⟨ε₀, Cm, hε₀, hCm, hd⟩ := cph_path_d hmt hb0 hb1 T hκ
  obtain ⟨C, hC0, hC⟩ := cph_comMean_bound hinc hb0 hb1 hκ
  obtain ⟨K, hK0, hK⟩ := cph_comDev_bound hfl hb0 hb1 hκ hq
  set T' := max T 0
  set W₁ : ℝ := 4 * m / ε₀
  set A := C * (4 * m * Cm ^ 2 + 1) + C * (2 * Cm ^ 2 + 1)
  set Cf' := max Cf 0
  have hT' : 0 ≤ T' := le_max_right _ _
  have hW₁ : 0 ≤ W₁ := by positivity
  have hA : 0 ≤ A := by positivity
  have hCf' : 0 ≤ Cf' := le_max_right _ _
  refine ⟨4 * (T' * W₁) * W₁ + (Cf' + A + K), fun p hpb hnT model k E hE => ?_⟩
  subst hpb
  have hz := cph_boundaryZ_im_nonneg (b := p.b) (by linarith) hκ hE
  have hz0 := cph_commonZ_im_nonneg hb1 hκ hE
  have hWr : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hn4 : (4 : ℝ) ≤ p.n := by exact_mod_cast p.n_ge_four
  have hsq : 1 ≤ Real.sqrt p.n := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ p.n by linarith); rwa [Real.sqrt_one] at this
  have hnT' : (p.n : ℝ) ≤ T' * p.W := hnT.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hWr.le)
  have hq0 : (0 : ℝ) < q := by linarith
  -- the Borel version
  have hae := cph_xi_ae_eq model k E
  rw [integral_congr_ae hae]
  rw [eLpNorm_congr_ae (g := fun H => cphXiM p k E H -
    ∫ H', cphXiM p k E H' ∂(model.law : Measure p.SiteMatrix)) (by
      filter_upwards [hae] with H hH; simp only [hH])]
  by_cases hWs : (p.W : ℝ) < W₁
  · have hcr := eLpNorm_le_of_ae_bound (p := ENNReal.ofReal q) (μ := (model.law : Measure p.SiteMatrix))
      ((cph_measurable_xiM k E).sub_const
        (∫ H', cphXiM p k E H' ∂(model.law : Measure p.SiteMatrix))).aestronglyMeasurable
      (C := 4 * (p.n * p.W)) (ae_of_all _ fun H => by
        rw [Real.norm_eq_abs]
        have h1 := cph_abs_xiM_le (k := k) hz0 H
        have h2 : |∫ H', cphXiM p k E H' ∂(model.law : Measure p.SiteMatrix)| ≤ 2 * (p.n * p.W) :=
          cph_abs_integral_le fun H' => cph_abs_xiM_le hz0 H'
        exact (abs_sub _ _).trans (by linarith))
    rw [measure_univ, ENNReal.one_rpow, one_mul] at hcr
    refine hcr.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : (p.n : ℝ) * p.W ≤ (T' * W₁) * W₁ := by
      have : (p.n : ℝ) ≤ T' * W₁ := hnT'.trans (mul_le_mul_of_nonneg_left hWs.le hT')
      exact mul_le_mul this hWs.le hWr.le (by positivity)
    calc 4 * ((p.n : ℝ) * p.W) ≤ 4 * (T' * W₁) * W₁ := by linarith
      _ ≤ 4 * (T' * W₁) * W₁ + (Cf' + A + K) := by linarith [hCf', hA, hK0]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hsq
  · have hW4 : 4 * (m : ℝ) ≤ ε₀ * p.W := by
      have : W₁ ≤ p.W := le_of_not_gt hWs
      rw [div_le_iff₀ hε₀] at this; linarith
    rw [cph_integral_xi model k E, cph_eLpNorm_xi model k E]
    set P := (layerLaw p.W p.b .common).prod (pathLaw p.W (p.n - 3) p.b)
    set μ := pathLaw p.W (p.n - 3) p.b
    set Ec : PathSample p.W (p.n - 3) → ℝ := fun ω =>
      cphComMean p.b E (pathSchur E ω) - ∫ ω', cphComMean p.b E (pathSchur E ω') ∂μ
    set Dc : LayerSample p.W .common × PathSample p.W (p.n - 3) → ℝ := fun x =>
      cphComIncrementM p.b E (pathSchur E x.2) x.1 - cphComMean p.b E (pathSchur E x.2)
    have hEcm : Measurable Ec :=
      ((cph_measurable_comMean p.b E p.W).comp (measurable_pathSchur _ _ E)).sub_const _
    have hDcm : Measurable Dc :=
      (cph_measurable_comIncrementM p.b E ((measurable_pathSchur _ _ E).comp measurable_snd)
        measurable_fst).sub ((cph_measurable_comMean p.b E p.W).comp
          ((measurable_pathSchur _ _ E).comp measurable_snd))
    obtain ⟨F1, hF1def⟩ : ∃ F1 : LayerSample p.W .common × PathSample p.W (p.n - 3) → ℝ,
        F1 = fun x => cphS p.b E p.W (p.n - 3) x.2 := ⟨_, rfl⟩
    obtain ⟨F2, hF2def⟩ : ∃ F2 : LayerSample p.W .common × PathSample p.W (p.n - 3) → ℝ,
        F2 = fun x => Ec x.2 := ⟨_, rfl⟩
    have hIG : ∫ x', cphG p.b E x' ∂P = ∫ ω, cphPsiM p.b E ω ∂pathLaw p.W (p.n - 3) p.b +
        ∫ ω, cphComMean p.b E (pathSchur E ω) ∂pathLaw p.W (p.n - 3) p.b := cph_integral_G hz hz0
    have hGeq : (fun x => cphG p.b E x - ∫ x', cphG p.b E x' ∂P) = F1 + F2 + Dc := by
      rw [hIG, hF1def, hF2def]
      funext x
      simp only [Pi.add_apply, cphG, cphS, Ec, Dc]
      ring
    rw [hGeq]
    have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
    -- the path part
    have hn3 : 1 ≤ p.n - 3 := by have := p.n_ge_four; omega
    have hn3T : ((p.n - 3 : ℕ) : ℝ) ≤ T * p.W := by
      rw [cph_n_sub_three]; linarith
    have hS : eLpNorm (cphS p.b E p.W (p.n - 3)) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (Cf' * Real.sqrt p.n) := by
      have h := hCf p.W p.W_pos (p.n - 3) hn3 hn3T E hE
      have hae' := cph_psi_ae_eq p.b E p.W (p.n - 3)
      rw [integral_congr_ae hae'] at h
      refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) (h.trans (ENNReal.ofReal_le_ofReal ?_))
      · filter_upwards [hae'] with ω hω; simp only [cphS, hω]
      · have hs : Real.sqrt (((p.n - 3 : ℕ) : ℝ) + 1) ≤ Real.sqrt p.n :=
          Real.sqrt_le_sqrt (by rw [cph_n_sub_three]; linarith)
        calc Cf * Real.sqrt (((p.n - 3 : ℕ) : ℝ) + 1) ≤ Cf' * Real.sqrt (((p.n - 3 : ℕ) : ℝ) + 1) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
          _ ≤ Cf' * Real.sqrt p.n := mul_le_mul_of_nonneg_left hs hCf'
    -- the predictable part
    have hEc : eLpNorm Ec (ENNReal.ofReal q) μ ≤ ENNReal.ofReal A := by
      have h2 := hd p.W p.W_pos 2 le_rfl (by linarith) (p.n - 3) hn3 hn3T E hE
      have h4 := hd p.W p.W_pos (2 * ((2 * m : ℕ) : ℝ)) (by push_cast; linarith)
        (by push_cast; linarith) (p.n - 3) hn3 hn3T E hE
      have herr := (cph_errors_gen hm hb1 hκ hE p.W_pos hC0 (by positivity) (by positivity)
        (cph_measurable_comMean p.b E p.W) (fun X => cph_abs_comMean_le hz hz0 X)
        (t := p.W * (phaseEll E + phaseH E)) (fun X hX => hC p.W p.W_pos X hX E hE) h2 h4).2
      refine (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hqm)).trans
        (herr.trans (ENNReal.ofReal_le_ofReal ?_))
      have hs4 : Real.sqrt (2 * ((2 * m : ℕ) : ℝ)) ^ 2 = 4 * m := by
        rw [Real.sq_sqrt (by positivity)]; push_cast; ring
      have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
      rw [div_pow, mul_pow, hs4, div_pow, mul_pow, hs2]
      have e1 : C * (p.W * (Cm ^ 2 * (4 * m) / p.W ^ 2) + (p.W : ℝ)⁻¹) =
          C * (4 * m * Cm ^ 2 + 1) / p.W := by field_simp
      have e2 : C * (p.W * (Cm ^ 2 * 2 / p.W ^ 2) + (p.W : ℝ)⁻¹) =
          C * (2 * Cm ^ 2 + 1) / p.W := by field_simp
      rw [e1, e2, ← add_div]
      exact div_le_self hA hW1
    -- the fresh part
    have hDc : eLpNorm Dc (ENNReal.ofReal q) P ≤ ENNReal.ofReal K := by
      refine srec_eLpNorm_prod_le hDcm hq0 ?_
      filter_upwards [srec_ae_pathSchur_isHermitian p.W (p.n - 3) p.b E] with ω hω
      have e : (fun ℓ => Dc (ℓ, ω)) = fun ℓ =>
          cphComIncrementM p.b E (pathSchur E ω) ℓ - cphComMean p.b E (pathSchur E ω) := rfl
      rw [e]
      exact hK p.W p.W_pos _ hω E hE
    have hF1 : eLpNorm F1 (ENNReal.ofReal q) P =
        eLpNorm (cphS p.b E p.W (p.n - 3)) (ENNReal.ofReal q) μ := by
      rw [hF1def]; exact cph_eLpNorm_comp_snd (cph_measurable_S _ _ _ _) _
    have hF2 : eLpNorm F2 (ENNReal.ofReal q) P = eLpNorm Ec (ENNReal.ofReal q) μ := by
      rw [hF2def]; exact cph_eLpNorm_comp_snd hEcm _
    have hsum1 : eLpNorm (F1 + F2 + Dc) (ENNReal.ofReal q) P ≤
        eLpNorm (F1 + F2) (ENNReal.ofReal q) P + eLpNorm Dc (ENNReal.ofReal q) P :=
      eLpNorm_add_le hq1
    have hsum2 : eLpNorm (F1 + F2) (ENNReal.ofReal q) P ≤
        eLpNorm F1 (ENNReal.ofReal q) P + eLpNorm F2 (ENNReal.ofReal q) P :=
      eLpNorm_add_le hq1
    rw [hF1, hF2] at hsum2
    refine hsum1.trans ((add_le_add (hsum2.trans (add_le_add hS hEc)) hDc).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) hA, ← ENNReal.ofReal_add (by positivity) hK0]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : A ≤ A * Real.sqrt p.n := le_mul_of_one_le_right hA hsq
    have h2 : K ≤ K * Real.sqrt p.n := le_mul_of_one_le_right hK0 hsq
    have h3 : 0 ≤ 4 * (T' * W₁) * W₁ * Real.sqrt p.n := by positivity
    nlinarith

/-- **The ring compensated phase, mean clause.** -/
theorem cph_ring_mean (hmt : MatchedTracesContract) (hinc : CompensatedIncrementContract)
    (hcore : CphCore) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ C : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (k : ZMod p.n) (E : ℝ), E ∈ bulkInterval κ →
      |(∫ H, ringCompensatedPhase p k H E ∂(model.law : Measure p.SiteMatrix)) -
          ((p.n : ℝ) - 1) * p.W * semicircleCDF E - p.W * (phaseEll E + b * phaseH E)| ≤
        C * p.n / p.W := by
  intro b hb0 hb1 κ T hκ
  obtain ⟨Cpm, hCpm⟩ := cph_mean hmt hinc hcore b hb0 hb1 κ T hκ
  obtain ⟨ε₀, Cm, hε₀, hCm, hd⟩ := cph_path_d hmt hb0 hb1 T hκ
  obtain ⟨C, hC0, hC⟩ := cph_comMean_bound hinc hb0 hb1 hκ
  set W₂ : ℝ := max (4 / ε₀) 1
  set Cpm' := max Cpm 0
  have hW₂ : 1 ≤ W₂ := le_max_right _ _
  have hCpm' : 0 ≤ Cpm' := le_max_right _ _
  have hCC : 0 ≤ C * (2 * Cm ^ 2 + 1) := by positivity
  refine ⟨4 * W₂ ^ 2 + (Cpm' + C * (2 * Cm ^ 2 + 1)), fun p hpb hnT model k E hE => ?_⟩
  subst hpb
  have hz := cph_boundaryZ_im_nonneg (b := p.b) (by linarith) hκ hE
  have hz0 := cph_commonZ_im_nonneg hb1 hκ hE
  have hE2 : |E| ≤ 2 := (abs_le_of_mem_bulkInterval hE).trans (by linarith)
  have hEI : E ∈ Set.Icc (-2 : ℝ) 2 := abs_le.mp hE2
  have hWr : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hn4 : (4 : ℝ) ≤ p.n := by exact_mod_cast p.n_ge_four
  have hF := BlockBand.RankLocation.semicircleCDF_nonneg E
  have hF1 := BlockBand.RankLocation.semicircleCDF_le_one E
  have hl := cph_abs_phaseEll_le E
  have hh := cph_abs_phaseH_le hE2
  rw [integral_congr_ae (cph_xi_ae_eq model k E), le_div_iff₀ hWr]
  have hpos : 0 ≤ 4 * W₂ ^ 2 := by positivity
  by_cases hWs : (p.W : ℝ) < 4 / ε₀
  · have hI : |∫ H, cphXiM p k E H ∂(model.law : Measure p.SiteMatrix)| ≤ 2 * (p.n * p.W) :=
      cph_abs_integral_le fun H => cph_abs_xiM_le hz0 H
    have hWW : (p.W : ℝ) ≤ W₂ := hWs.le.trans (le_max_left _ _)
    have h3 : |(p.W : ℝ) * (phaseEll E + p.b * phaseH E)| ≤ p.n * p.W := by
      rw [abs_mul, abs_of_pos hWr]
      have : |phaseEll E + p.b * phaseH E| ≤ 2 := by
        have := abs_add_le (phaseEll E) (p.b * phaseH E)
        rw [abs_mul, abs_of_pos hb0] at this
        nlinarith
      nlinarith
    have h4 : |((p.n : ℝ) - 1) * p.W * semicircleCDF E| ≤ p.n * p.W := by
      have h0 : (0 : ℝ) ≤ ((p.n : ℝ) - 1) * p.W := mul_nonneg (by linarith) hWr.le
      rw [abs_of_nonneg (mul_nonneg h0 hF)]
      have := mul_le_of_le_one_right h0 hF1
      nlinarith
    have hcrude : |(∫ H, cphXiM p k E H ∂(model.law : Measure p.SiteMatrix)) -
        ((p.n : ℝ) - 1) * p.W * semicircleCDF E - p.W * (phaseEll E + p.b * phaseH E)| ≤
        4 * (p.n * p.W) := by
      rw [abs_le] at hI h3 h4 ⊢
      constructor <;> linarith
    have hWsq : (p.W : ℝ) * p.W ≤ W₂ ^ 2 := by nlinarith
    calc _ ≤ (4 : ℝ) * ((p.n : ℝ) * p.W) * p.W := mul_le_mul_of_nonneg_right hcrude hWr.le
      _ = (4 : ℝ) * p.n * ((p.W : ℝ) * p.W) := by ring
      _ ≤ (4 : ℝ) * p.n * W₂ ^ 2 := mul_le_mul_of_nonneg_left hWsq (by positivity)
      _ ≤ (4 * W₂ ^ 2 + (Cpm' + C * (2 * Cm ^ 2 + 1))) * p.n := by nlinarith
  · have hW4 : 4 ≤ ε₀ * p.W := by
      have : 4 / ε₀ ≤ p.W := le_of_not_gt hWs
      rw [div_le_iff₀ hε₀] at this; linarith
    rw [cph_integral_xi model k E, cph_integral_G hz hz0]
    have hn3 : 1 ≤ p.n - 3 := by have := p.n_ge_four; omega
    have hn3T : ((p.n - 3 : ℕ) : ℝ) ≤ T * p.W := by rw [cph_n_sub_three]; linarith
    have hpm := hCpm p.W p.W_pos (p.n - 3) hn3 hn3T E hE
    rw [integral_congr_ae (cph_psi_ae_eq p.b E p.W (p.n - 3)), cph_n_sub_three] at hpm
    have h2 := hd p.W p.W_pos 2 le_rfl (by linarith) (p.n - 3) hn3 hn3T E hE
    have h4 := hd p.W p.W_pos (2 * ((2 * 1 : ℕ) : ℝ)) (by norm_num) (by norm_num; linarith)
      (p.n - 3) hn3 hn3T E hE
    have herr := (cph_errors_gen (m := 1) le_rfl hb1 hκ hE p.W_pos hC0 (by positivity)
      (by positivity) (cph_measurable_comMean p.b E p.W) (fun X => cph_abs_comMean_le hz hz0 X)
      (t := p.W * (phaseEll E + phaseH E)) (fun X hX => hC p.W p.W_pos X hX E hE) h2 h4).1
    have hcm : |(∫ ω, cphComMean p.b E (pathSchur E ω) ∂pathLaw p.W (p.n - 3) p.b) -
        p.W * (phaseEll E + phaseH E)| * p.W ≤ C * (2 * Cm ^ 2 + 1) := by
      have e : C * (p.W * (Cm * Real.sqrt 2 / p.W) ^ 2 + (p.W : ℝ)⁻¹) =
          C * (2 * Cm ^ 2 + 1) / p.W := by
        rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; field_simp
      rw [e] at herr
      rwa [le_div_iff₀ hWr] at herr
    have hpm' : |(∫ ω, cphPsiM p.b E ω ∂pathLaw p.W (p.n - 3) p.b) -
        ((p.n : ℝ) - 3) * p.W * semicircleCDF E - p.W * (2 * phaseEll E + p.b * phaseH E)| * p.W
        ≤ Cpm' * (p.n - 2) := by
      have := (mul_le_mul_of_nonneg_right hpm hWr.le)
      rw [div_mul_cancel₀ _ hWr.ne'] at this
      refine this.trans ?_
      have : (p.n : ℝ) - 3 + 1 = p.n - 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    have hFsc := BlockBand.RankLocation.semicircleCDF_eq_phase hEI
    have hsplit : |(∫ ω, cphPsiM p.b E ω ∂pathLaw p.W (p.n - 3) p.b) +
        (∫ ω, cphComMean p.b E (pathSchur E ω) ∂pathLaw p.W (p.n - 3) p.b) -
        ((p.n : ℝ) - 1) * p.W * semicircleCDF E - p.W * (phaseEll E + p.b * phaseH E)| ≤
        |(∫ ω, cphPsiM p.b E ω ∂pathLaw p.W (p.n - 3) p.b) -
          ((p.n : ℝ) - 3) * p.W * semicircleCDF E - p.W * (2 * phaseEll E + p.b * phaseH E)| +
        |(∫ ω, cphComMean p.b E (pathSchur E ω) ∂pathLaw p.W (p.n - 3) p.b) -
          p.W * (phaseEll E + phaseH E)| := by
      refine le_of_eq_of_le ?_ (abs_add_le _ _)
      congr 1
      rw [hFsc]
      ring
    calc _ ≤ (|(∫ ω, cphPsiM p.b E ω ∂pathLaw p.W (p.n - 3) p.b) -
          ((p.n : ℝ) - 3) * p.W * semicircleCDF E - p.W * (2 * phaseEll E + p.b * phaseH E)| +
        |(∫ ω, cphComMean p.b E (pathSchur E ω) ∂pathLaw p.W (p.n - 3) p.b) -
          p.W * (phaseEll E + phaseH E)|) * p.W := mul_le_mul_of_nonneg_right hsplit hWr.le
      _ ≤ Cpm' * (p.n - 2) + C * (2 * Cm ^ 2 + 1) := by rw [add_mul]; exact add_le_add hpm' hcm
      _ ≤ (Cpm' + C * (2 * Cm ^ 2 + 1)) * p.n := by
          have := mul_le_mul_of_nonneg_left (show (p.n : ℝ) - 2 ≤ p.n by linarith) hCpm'
          have := le_mul_of_one_le_right hCC (show (1 : ℝ) ≤ p.n by linarith)
          linarith
      _ ≤ (4 * W₂ ^ 2 + (Cpm' + C * (2 * Cm ^ 2 + 1))) * p.n :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)

/-- **The ring compensated phase** (`RingCompensatedPhaseContract`) from the matched traces,
the conditional mean increments, and the isolated inputs `CphIncrementFluctuation`, `CphCore`. -/
theorem ringCompensatedPhase_of_inputs (hmt : MatchedTracesContract)
    (hinc : CompensatedIncrementContract) (hfl : CphIncrementFluctuation) (hcore : CphCore) :
    RingCompensatedPhaseContract where
  fluctuation := cph_ring_fluctuation hmt hinc hfl hcore
  mean := cph_ring_mean hmt hinc hcore

/-- `ringCompensatedPhase_of_inputs` with the matched traces from `matchedTraces_holds`. -/
theorem ringCompensatedPhase_holds_of
    (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) (hinc : CompensatedIncrementContract)
    (hfl : CphIncrementFluctuation) (hcore : CphCore) : RingCompensatedPhaseContract :=
  ringCompensatedPhase_of_inputs (matchedTraces_holds hcount hgrad) hinc hfl hcore

end RingAssembly

end BlockBand.Layers
