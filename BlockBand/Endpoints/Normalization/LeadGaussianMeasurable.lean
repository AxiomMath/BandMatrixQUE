module

public import BlockBand.Endpoints.Normalization.LeadGaussianDeletion
public import BlockBand.Endpoints.Normalization.OneBlockPalmMass

/-!
# The physical lead-profile theorem: measurability and the representation of averages

**Main results.**
* `measurable_blockReconMass_joint'`: `((e, ω), v) ↦ p(v, e)` is jointly measurable;
* `measurable_blockFieldFactor`: `ω ↦ M(ω, e) = √c(z₀ - Σ)⁻¹` is measurable;
* `measurable_fieldObs`: `(ω, g) ↦ G(p(M(ω,e) g, e))` is jointly measurable for measurable `G`;
* `measurable_blockSectorFiberReal_joint'`: `(e, ω) ↦ 𝒜⁰_{ℓ,e}[G(e, ω, ·)]` is jointly measurable
  (the argument used for the angular regularity of the lead profile);
* `sum_blockSectorFiberReal_eq_mul` (from `FreshEigenpairDensityContract`): at a Hermitian
  exterior, for bounded measurable mass-vector observables `G`,
  `Σ_ℓ 𝒜⁰_{ℓ,e}[G(p)] = Z₀(e) · (Σ_ℓ 𝒜⁰_{ℓ,e}[G(p)] / Z₀(e))` (the sector sum vanishes where
  `Z₀(e) = 0`, since then the Palm weights vanish a.e.).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

namespace LeadGaussian

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile
open scoped ENNReal NNReal ComplexConjugate ComplexOrder BoundedContinuousFunction

section Measurable

variable (p : Parameters) (k : ZMod p.n)

theorem measurable_shift_joint' {X : Type*} [MeasurableSpace X] {α : Type*} [Fintype α]
    [DecidableEq α] {H : X → Matrix α α ℂ} {e : X → ℝ} (hH : Measurable H) (he : Measurable e) :
    Measurable fun x => H x - ((e x : ℝ) : ℂ) • (1 : Matrix α α ℂ) := by
  refine FixedOmega.measurable_matrix_sub hH ?_
  refine Measurable.of_eval_matrix _ fun a b => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (Complex.measurable_ofReal.comp he).mul measurable_const

theorem measurable_coareaT_joint' {X : Type*} [MeasurableSpace X] {α β : Type*} [Fintype α]
    [DecidableEq α] {H : X → Matrix α α ℂ} {C : X → Matrix α β ℂ} {e : X → ℝ}
    (hH : Measurable H) (hC : Measurable C) (he : Measurable e) :
    Measurable fun x => physicalCoareaT (H x) (C x) (e x) := by
  unfold physicalCoareaT physicalCoareaResolvent
  exact CoareaNative.BlockBand.measurable_matrix_mul_rect
    (CoareaNative.BlockBand.Measurable.matrixNonsingInv (measurable_shift_joint' hH he)) hC

theorem measurable_coareaD_joint' {X : Type*} [MeasurableSpace X] {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] {H : X → Matrix α α ℂ} {C : X → Matrix α β ℂ}
    {e : X → ℝ} (hH : Measurable H) (hC : Measurable C) (he : Measurable e) :
    Measurable fun x => physicalCoareaD (H x) (C x) (e x) := by
  unfold physicalCoareaD schurClock
  have hT := measurable_coareaT_joint' hH hC he
  exact FixedOmega.measurable_matrix_add measurable_const
    (CoareaNative.BlockBand.measurable_matrix_mul_rect
      (CoareaNative.BlockBand.Measurable.matrix_conjTranspose hT) hT)

/-- `((e, ω), v) ↦ p(v, e)` is jointly measurable. -/
theorem measurable_blockReconMass_joint' :
    Measurable fun x : (ℝ × BlockState p k) × (BlockSite p k → ℂ) =>
      blockReconMass p k x.1.2 x.1.1 x.2 := by
  have hH : Measurable fun x : (ℝ × BlockState p k) × (BlockSite p k → ℂ) => x.1.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hC : Measurable fun x : (ℝ × BlockState p k) × (BlockSite p k → ℂ) => x.1.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have he : Measurable fun x : (ℝ × BlockState p k) × (BlockSite p k → ℂ) => x.1.1 :=
    measurable_fst.comp measurable_fst
  have hT := measurable_coareaT_joint' hH hC he
  have hD := measurable_coareaD_joint' hH hC he
  have hTv : Measurable fun x : (ℝ × BlockState p k) × (BlockSite p k → ℂ) =>
      physicalCoareaT x.1.2.1 x.1.2.2 x.1.1 *ᵥ x.2 := measurable_mulVec' hT measurable_snd
  have hL : Measurable fun x : (ℝ × BlockState p k) × (BlockSite p k → ℂ) =>
      blockLift p k x.1.2 x.1.1 x.2 := by
    refine Measurable.of_eval fun y => ?_
    unfold blockLift
    by_cases hy : y.1 = k
    · simp only [hy, dite_true]
      exact (measurable_pi_apply _).comp measurable_snd
    · simp only [hy, dite_false]
      exact ((measurable_pi_apply _).comp hTv).neg
  have hS : Measurable fun x : (ℝ × BlockState p k) × (BlockSite p k → ℂ) =>
      blockClockSpeed p k x.1.2 x.1.1 x.2 := by
    unfold blockClockSpeed
    exact Complex.measurable_re.comp (measurable_star_dotProduct' measurable_snd
      (measurable_mulVec' hD measurable_snd))
  refine Measurable.of_eval fun j => ?_
  unfold blockReconMass
  refine Measurable.div (Finset.measurable_sum _ fun a _ => ?_) hS
  exact (((measurable_pi_apply _).comp hL).norm).pow_const 2

theorem measurable_blockF_fixed (e : ℝ) : Measurable fun ω : BlockState p k => blockF p k ω e :=
  measurable_physicalCoareaF_joint (H := fun ω : BlockState p k => ω.1) (C := fun ω => ω.2)
    (V := fun _ => (0 : Matrix (BlockSite p k) (BlockSite p k) ℂ)) (e := fun _ => e)
    measurable_fst measurable_snd measurable_const measurable_const

theorem measurable_blockFieldFactor (e : ℝ) :
    Measurable fun ω : BlockState p k => blockFieldFactor p k ω e := by
  unfold blockFieldFactor blockShifted
  have h1 : Measurable fun ω : BlockState p k =>
      commonZ p.b e • (1 : Matrix (BlockSite p k) (BlockSite p k) ℂ) + blockF p k ω e :=
    FixedOmega.measurable_matrix_add measurable_const (measurable_blockF_fixed p k e)
  have h2 := CoareaNative.BlockBand.Measurable.matrixNonsingInv h1
  refine Measurable.of_eval_matrix _ fun a b => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact measurable_const.mul ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp h2))

/-- `(ω, g) ↦ G(p(M(ω,e) g, e))` is jointly measurable. -/
theorem measurable_fieldObs (e : ℝ) (G : (ZMod p.n → ℝ) → ℝ) (hG : Measurable G) :
    Measurable fun x : BlockState p k × (BlockSite p k → ℂ) =>
      G (blockReconMass p k x.1 e (blockFieldFactor p k x.1 e *ᵥ x.2)) := by
  have hM : Measurable fun x : BlockState p k × (BlockSite p k → ℂ) =>
      blockFieldFactor p k x.1 e := (measurable_blockFieldFactor p k e).comp measurable_fst
  have hv : Measurable fun x : BlockState p k × (BlockSite p k → ℂ) =>
      blockFieldFactor p k x.1 e *ᵥ x.2 := measurable_mulVec' hM measurable_snd
  have hemb : Measurable fun x : BlockState p k × (BlockSite p k → ℂ) =>
      ((e, x.1), blockFieldFactor p k x.1 e *ᵥ x.2) :=
    (measurable_const.prodMk measurable_fst).prodMk hv
  have h := (measurable_blockReconMass_joint' p k).comp hemb
  exact hG.comp h

/-- The Gaussian-field average `ω ↦ E_g G(p(M(ω,e) g, e))` is measurable. -/
theorem measurable_fieldAverage (e : ℝ) (G : (ZMod p.n → ℝ) → ℝ) (hG : Measurable G) :
    Measurable fun ω : BlockState p k =>
      ∫ g, G (blockReconMass p k ω e (blockFieldFactor p k ω e *ᵥ g))
        ∂circularVectorLaw (BlockSite p k) :=
  ((measurable_fieldObs p k e G hG).stronglyMeasurable.integral_prod_right'
    (ν := circularVectorLaw (BlockSite p k))).measurable

/-!
### The one-block sector integrand
-/

/-- The integration variables `((e, ω), v), G'`. -/
abbrev SectorVar := ((ℝ × BlockState p k) × (BlockSite p k → ℂ)) ×
  Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ

theorem measurable_blockF_sector :
    Measurable fun q : SectorVar p k => blockF p k q.1.1.2 q.1.1.1 :=
  measurable_physicalCoareaF_joint
    (H := fun q : SectorVar p k => q.1.1.2.1) (C := fun q : SectorVar p k => q.1.1.2.2)
    (V := fun _ : SectorVar p k => (0 : Matrix (BlockSite p k) (BlockSite p k) ℂ))
    (e := fun q : SectorVar p k => q.1.1.1)
    (measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))
    (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))
    measurable_const (measurable_fst.comp (measurable_fst.comp measurable_fst))

theorem measurable_blockFrameM_sector
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) :
    Measurable fun q : SectorVar p k => blockFrameM p k U q.1.1.2 q.1.1.1 q.1.2 q.2 := by
  have hU1 : Measurable fun q : SectorVar p k => U q.1.2 :=
    hU.comp (measurable_snd.comp measurable_fst)
  have hF := measurable_blockF_sector p k
  have hE : Measurable fun q : SectorVar p k =>
      ((q.1.1.1 : ℝ) : ℂ) • (1 : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ) := by
    apply Measurable.of_eval_matrix
    intro a b
    simp only [Matrix.smul_apply]
    exact (Complex.measurable_ofReal.comp
      (measurable_fst.comp (measurable_fst.comp measurable_fst))).smul measurable_const
  unfold blockFrameM
  exact FixedOmega.measurable_matrix_sub (FixedOmega.measurable_matrix_add
    (CoareaNative.BlockBand.measurable_matrix_mul_rect
      (CoareaNative.BlockBand.measurable_matrix_mul_rect
        (CoareaNative.BlockBand.Measurable.matrix_conjTranspose hU1) hF) hU1) measurable_snd) hE

/-- `(e, ω) ↦ 𝒜⁰_{ℓ,e}[G(e, ω, ·)]` is jointly measurable for a jointly measurable `G`. -/
theorem measurable_blockSectorFiberReal_joint'
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (ℓ : ℕ) (G : ℝ → BlockState p k → (BlockSite p k → ℂ) → ℝ)
    (hG : Measurable fun x : (ℝ × BlockState p k) × (BlockSite p k → ℂ) => G x.1.1 x.1.2 x.2) :
    Measurable fun x : ℝ × BlockState p k =>
      blockSectorFiberReal p k U x.2 x.1 ℓ (G x.1 x.2) := by
  have hgue : IsProbabilityMeasure (gueMeasure (BlockFrameIndex p) (blockTime p)) := by
    unfold gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
    infer_instance
  have hM := measurable_blockFrameM_sector p k U hU
  have hg : Measurable fun q : SectorVar p k => (q.1.1.1, q.1.2, blockF p k q.1.1.2 q.1.1.1) :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_blockF_sector p k))
  have hR := (measurable_regressionFactor_joint (ι := BlockSite p k) (blockTime p : ℝ)).comp hg
  have hdet := Complex.continuous_normSq.measurable.comp
    ((continuous_id.matrix_det).measurable.comp hM)
  have hind : Measurable fun q : SectorVar p k =>
      (if negativeCount (blockFrameM p k U q.1.1.2 q.1.1.1 q.1.2 q.2) = ℓ then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_eq_fun ((FixedOmega.measurable_negativeCount _).comp hM)
      measurable_const) measurable_const measurable_const
  have hf : Measurable fun q : SectorVar p k =>
      coareaConstant p.W (blockTime p) *
          regressionFactor (blockTime p) q.1.1.1 q.1.2 (blockF p k q.1.1.2 q.1.1.1) *
          Complex.normSq (blockFrameM p k U q.1.1.2 q.1.1.1 q.1.2 q.2).det *
        (if negativeCount (blockFrameM p k U q.1.1.2 q.1.1.1 q.1.2 q.2) = ℓ then 1 else 0) *
          G q.1.1.1 q.1.1.2 q.1.2 :=
    (((measurable_const.mul hR).mul hdet).mul hind).mul (hG.comp measurable_fst)
  have h2 := hf.stronglyMeasurable.integral_prod_right'
    (ν := gueMeasure (BlockFrameIndex p) (blockTime p))
  have h3 := h2.integral_prod_right' (ν := projectiveHaar (BlockSite p k))
  exact h3.measurable

/-- The normalized one-block sector average of a mass-vector observable is jointly measurable. -/
theorem measurable_blockSectorAverage
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (G : (ZMod p.n → ℝ) → ℝ) (hG : Measurable G) :
    Measurable fun x : ℝ × BlockState p k =>
      (∑ ℓ ∈ Finset.range p.W, blockSectorFiberReal p k U x.2 x.1 ℓ
          (fun v => G (blockReconMass p k x.2 x.1 v))) /
        (blockNormalizer p k U x.2 x.1).toReal := by
  have hS : Measurable fun x : ℝ × BlockState p k => ∑ ℓ ∈ Finset.range p.W,
      blockSectorFiberReal p k U x.2 x.1 ℓ (fun v => G (blockReconMass p k x.2 x.1 v)) :=
    Finset.measurable_sum _ fun ℓ _ => measurable_blockSectorFiberReal_joint' p k U hU ℓ
      (fun e ω v => G (blockReconMass p k ω e v))
      (hG.comp (measurable_blockReconMass_joint' p k))
  exact hS.div (ENNReal.measurable_toReal.comp (measurable_blockNormalizer_joint p k U hU))

end Measurable

/-!
### The representation `Σ_ℓ 𝒜⁰_ℓ[G] = Z₀ · (Σ_ℓ 𝒜⁰_ℓ[G] / Z₀)`
-/

section Representation

variable (p : Parameters) (k : ZMod p.n)

/-- At a Hermitian exterior, the sector sum of a bounded measurable mass-vector observable
vanishes where `Z₀(e) = 0`. Consumes `FreshEigenpairDensityContract`. -/
theorem sum_blockSectorFiberReal_eq_mul (hD : FreshEigenpairDensityContract)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (hω : ω.1.IsHermitian) (e : ℝ)
    (G : (ZMod p.n → ℝ) → ℝ) (hG : Measurable G) (MG : ℝ) (hMG : ∀ q, |G q| ≤ MG) :
    ∑ ℓ ∈ Finset.range p.W, blockSectorFiberReal p k U ω e ℓ
        (fun v => G (blockReconMass p k ω e v)) =
      (blockNormalizer p k U ω e).toReal *
        ((∑ ℓ ∈ Finset.range p.W, blockSectorFiberReal p k U ω e ℓ
          (fun v => G (blockReconMass p k ω e v))) / (blockNormalizer p k U ω e).toReal) := by
  by_cases hZ : (blockNormalizer p k U ω e).toReal = 0
  · rw [hZ, zero_mul]
    set σ := blockEquiv p k
    set F := Matrix.reindex σ σ (blockF p k ω e)
    have hZ' : palmMass F p.c e = 0 := by
      rw [blockNormalizer_eq_palmMass p k hD σ U hU ω hω e,
        ENNReal.toReal_ofReal (palmMass_nonneg _ _ _)] at hZ
      exact hZ
    have hobs : (fun v => G (blockReconMass p k ω e v)) =
        fun v => reconMatrixObs p k ω e G (vecMulVec v (star v)) := by
      funext v; rw [reconMatrixObs_vecMulVec]
    have hterm : ∀ ℓ : Fin p.W, ∫ A0, palmWeight F p.c e ℓ A0 ∂freshTracelessLaw p.W p.c = 0 := by
      intro ℓ
      have h0 := Finset.sum_eq_zero_iff_of_nonneg (fun ℓ _ =>
        integral_nonneg fun A0 => palmWeight_nonneg' F p.c e ℓ A0) |>.mp hZ'
      exact h0 ℓ (Finset.mem_univ _)
    rw [Finset.sum_range]
    refine Finset.sum_eq_zero fun ℓ _ => ?_
    rw [hobs, blockSectorFiberReal_eq_palm p k hD σ U hU ω hω e ℓ ℓ.2 _
      (measurable_reconMatrixObs p k ω e G hG) MG (fun X => hMG _)]
    have hint := integrable_palmWeight_mul F p.c e ℓ (fun _ => 1) measurable_const 1
      (fun _ => by simp)
    simp only [mul_one] at hint
    have hae : (fun A0 => palmWeight F p.c e ℓ A0) =ᵐ[freshTracelessLaw p.W p.c] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun A0 => palmWeight_nonneg' F p.c e ℓ A0) hint).mp
        (hterm ℓ)
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with A0 hA0
    simp only [Pi.zero_apply] at hA0
    show _ * _ = (0 : ℝ)
    exact mul_eq_zero_of_left hA0 _
  · rw [mul_div_cancel₀ _ hZ]

end Representation

end LeadGaussian

end BlockBand.Endpoints.Normalization
