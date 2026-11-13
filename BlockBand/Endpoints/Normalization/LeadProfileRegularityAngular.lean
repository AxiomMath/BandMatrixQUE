module

public import BlockBand.Endpoints.Normalization.LeadProfileAssemblyFinal
public import BlockBand.Endpoints.Normalization.OneBlockPalmMass

/-!
# The physical lead-profile theorem: the regularity statement `LeadAngularRegularity`

We prove the measurability, boundedness and representation properties of the normalized one-block
angular average required by `LeadAngularRegularity`.

**Objects.** For a parameter set `p`, a block `k`, a measurable block frame `U`, an exterior
`ω = (H_R, C)` and a real energy `e`: the nonnegative one-block weight
`w(v, G') = c_{W,t} 𝓡_t(e, v, F(e)) |det M(v, G')|²` (`t = c/W`, `F(e) = blockF`), on
`projectiveHaar ⊗ GUE_{W-1}(t)`; `𝒜⁰_{ℓ,e}[g] = ∫∫ w 1{N_-(M) = ℓ} g`
(`blockSectorFiberReal`), `Z₀(e) = ∫∫ w` (`blockNormalizer`, in `ℝ≥0∞`).

**Main results.**
* `abs_sum_blockSectorFiberReal_le` (unconditional, every `ω, e` with `Z₀(e) < ∞`): for
  measurable `g` with `|g| ≤ M`, `|Σ_{ℓ<W} 𝒜⁰_{ℓ,e}[g]| ≤ M · Z₀(e)`. Proof: `Z₀ < ∞` makes
  `w`, hence every `w 1_ℓ g`, integrable on the product (Tonelli); the iterated Bochner integrals
  are product integrals (Fubini), the sector indicators sum to one (`N_-(M) ≤ W - 1`), and
  `|∫ w g| ≤ M ∫ w`. No Palm bridge is used.
* `measurable_leadAngularAverage_joint` (unconditional): `(e, ω) ↦ leadAngularAverage` is
  jointly measurable (joint measurability of the integrand in `((e, ω), v, G')` and
  `StronglyMeasurable.integral_prod_right'` twice; `measurable_blockNormalizer_joint`).
* `abs_leadAngularAverage_le` (unconditional, every `e, ω`): `|leadAngularAverage| ≤ ‖Φ‖`
  (`A = S/Z₀.toReal` is `0` when `Z₀.toReal = 0`, i.e. `Z₀ ∈ {0, ∞}`).
* `leadAngularRegularity_of_finite`: `LeadAngularRegularity` follows from the a.s. finiteness
  `∀ᵐ ω ∂Pω, ∀ e, Z₀(e) ≠ ∞` under every one-block splitting law (`Σ_ℓ 𝒜⁰_ℓ[Ψ] = 0` when
  `Z₀ = 0` by the first bullet).
* `leadAngularRegularity_of (hD : FreshEigenpairDensityContract) : LeadAngularRegularity`
  (`Z₀ = ofReal(palmMass) < ∞` on Hermitian `H_R`, `blockNormalizer_eq_palmMass`).
* `leadAngularRegularity_of_oneBlockPalm (hPalm : OneBlockPalmContract) : LeadAngularRegularity`
  (`Z₀ ≤ C W` on Hermitian `H_R`, field `upper`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix BoundedContinuousFunction

namespace LeadProfileRegularity

variable (p : Parameters) (k : ZMod p.n)

/-- The nonnegative one-block weight `c_{W,t} 𝓡_t(e, v, F(e)) |det M(v, G')|²`. -/
def blockWeight (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (e : ℝ) (v : BlockSite p k → ℂ)
    (G' : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ) : ℝ :=
  coareaConstant p.W (blockTime p) * regressionFactor (blockTime p) e v (blockF p k ω e) *
    Complex.normSq (blockFrameM p k U ω e v G').det

theorem blockWeight_nonneg
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (e : ℝ) (v : BlockSite p k → ℂ)
    (G' : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ) :
    0 ≤ blockWeight p k U ω e v G' := by
  unfold blockWeight coareaConstant regressionFactor
  have ht : (0 : ℝ) ≤ (blockTime p : ℝ) := (blockTime p).2
  refine mul_nonneg (mul_nonneg ?_ (Real.exp_pos _).le) (Complex.normSq_nonneg _)
  exact div_nonneg zero_le_one (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg ht _))
    (Real.sqrt_nonneg _))

theorem blockSectorFiberReal_eq_weight
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (e : ℝ) (ℓ : ℕ) (g : (BlockSite p k → ℂ) → ℝ) :
    blockSectorFiberReal p k U ω e ℓ g = ∫ v, ∫ G', blockWeight p k U ω e v G' *
        (if negativeCount (blockFrameM p k U ω e v G') = ℓ then 1 else 0) * g v
      ∂(gueMeasure (BlockFrameIndex p) (blockTime p)) ∂(projectiveHaar (BlockSite p k)) :=
  rfl

theorem blockNormalizer_eq_weight
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (e : ℝ) :
    blockNormalizer p k U ω e = ∫⁻ v, ∫⁻ G', ENNReal.ofReal (blockWeight p k U ω e v G')
      ∂(gueMeasure (BlockFrameIndex p) (blockTime p)) ∂(projectiveHaar (BlockSite p k)) :=
  rfl

theorem isProbabilityMeasure_gue (ι : Type*) [Fintype ι] (t : ℝ≥0) :
    IsProbabilityMeasure (gueMeasure ι t) := by
  unfold gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
  infer_instance

/-!
## Joint measurability in `((e, ω), v, G')`
-/

/-- The integration variables `((e, ω), v), G'`. -/
abbrev JointVar := ((ℝ × BlockState p k) × (BlockSite p k → ℂ)) ×
  Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ

theorem measurable_shift_joint {X : Type*} [MeasurableSpace X] {α : Type*} [Fintype α]
    [DecidableEq α] {H : X → Matrix α α ℂ} {e : X → ℝ} (hH : Measurable H) (he : Measurable e) :
    Measurable fun x => H x - ((e x : ℝ) : ℂ) • (1 : Matrix α α ℂ) := by
  refine FixedOmega.measurable_matrix_sub hH ?_
  refine Measurable.of_eval_matrix _ fun a b => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (Complex.measurable_ofReal.comp he).mul measurable_const

theorem measurable_coareaT_joint {X : Type*} [MeasurableSpace X] {α β : Type*} [Fintype α]
    [DecidableEq α] {H : X → Matrix α α ℂ} {C : X → Matrix α β ℂ} {e : X → ℝ}
    (hH : Measurable H) (hC : Measurable C) (he : Measurable e) :
    Measurable fun x => physicalCoareaT (H x) (C x) (e x) := by
  unfold physicalCoareaT physicalCoareaResolvent
  exact CoareaNative.BlockBand.measurable_matrix_mul_rect
    (CoareaNative.BlockBand.Measurable.matrixNonsingInv (measurable_shift_joint hH he)) hC

theorem measurable_coareaD_joint {X : Type*} [MeasurableSpace X] {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] {H : X → Matrix α α ℂ} {C : X → Matrix α β ℂ}
    {e : X → ℝ} (hH : Measurable H) (hC : Measurable C) (he : Measurable e) :
    Measurable fun x => physicalCoareaD (H x) (C x) (e x) := by
  unfold physicalCoareaD schurClock
  have hT := measurable_coareaT_joint hH hC he
  exact FixedOmega.measurable_matrix_add measurable_const
    (CoareaNative.BlockBand.measurable_matrix_mul_rect
      (CoareaNative.BlockBand.Measurable.matrix_conjTranspose hT) hT)

/-- `((e, ω), v) ↦ p(v, e)` (`blockReconMass`) is jointly measurable. -/
theorem measurable_blockReconMass_joint :
    Measurable fun x : (ℝ × BlockState p k) × (BlockSite p k → ℂ) =>
      blockReconMass p k x.1.2 x.1.1 x.2 := by
  have hH : Measurable fun x : (ℝ × BlockState p k) × (BlockSite p k → ℂ) => x.1.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hC : Measurable fun x : (ℝ × BlockState p k) × (BlockSite p k → ℂ) => x.1.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have he : Measurable fun x : (ℝ × BlockState p k) × (BlockSite p k → ℂ) => x.1.1 :=
    measurable_fst.comp measurable_fst
  have hT := measurable_coareaT_joint hH hC he
  have hD := measurable_coareaD_joint hH hC he
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

theorem measurable_blockF_joint :
    Measurable fun q : JointVar p k => blockF p k q.1.1.2 q.1.1.1 := by
  have h := measurable_physicalCoareaF_joint
    (H := fun q : JointVar p k => q.1.1.2.1) (C := fun q : JointVar p k => q.1.1.2.2)
    (V := fun _ : JointVar p k => (0 : Matrix (BlockSite p k) (BlockSite p k) ℂ))
    (e := fun q : JointVar p k => q.1.1.1)
    (measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))
    (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))
    measurable_const (measurable_fst.comp (measurable_fst.comp measurable_fst))
  exact h

theorem measurable_blockFrameM_joint
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) :
    Measurable fun q : JointVar p k => blockFrameM p k U q.1.1.2 q.1.1.1 q.1.2 q.2 := by
  have hU1 : Measurable fun q : JointVar p k => U q.1.2 :=
    hU.comp (measurable_snd.comp measurable_fst)
  have hF := measurable_blockF_joint p k
  have hE : Measurable fun q : JointVar p k =>
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

theorem measurable_blockWeight_joint
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) :
    Measurable fun q : JointVar p k => blockWeight p k U q.1.1.2 q.1.1.1 q.1.2 q.2 := by
  have hM := measurable_blockFrameM_joint p k U hU
  have hg : Measurable fun q : JointVar p k => (q.1.1.1, q.1.2, blockF p k q.1.1.2 q.1.1.1) :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_blockF_joint p k))
  have hR := (measurable_regressionFactor_joint (ι := BlockSite p k) (blockTime p : ℝ)).comp hg
  have hdet := Complex.continuous_normSq.measurable.comp
    ((continuous_id.matrix_det).measurable.comp hM)
  have h := ((measurable_const (a := coareaConstant p.W (blockTime p))).mul hR).mul hdet
  exact h

theorem measurable_blockSectorIndicator_joint
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (ℓ : ℕ) :
    Measurable fun q : JointVar p k =>
      (if negativeCount (blockFrameM p k U q.1.1.2 q.1.1.1 q.1.2 q.2) = ℓ then (1 : ℝ) else 0) :=
  Measurable.ite (measurableSet_eq_fun ((FixedOmega.measurable_negativeCount _).comp
    (measurable_blockFrameM_joint p k U hU)) measurable_const) measurable_const measurable_const

/-- `((e, ω), v) ↦ Ψ(p(v, e))` (`leadReconObservable`) is jointly measurable. -/
theorem measurable_leadReconObservable_joint (Φ : MassProfile →ᵇ ℝ) :
    Measurable fun x : (ℝ × BlockState p k) × (BlockSite p k → ℂ) =>
      leadReconObservable p Φ k x.1.2 x.1.1 x.2 := by
  have h := (measurable_leadProfileRotationAverage p Φ).comp
    ((measurable_massVectorProfile p).comp (measurable_blockReconMass_joint p k))
  exact h

/-- `(e, ω) ↦ 𝒜⁰_{ℓ,e}[g(e, ω, ·)]` is jointly measurable for a jointly measurable `g`. -/
theorem measurable_blockSectorFiberReal_joint
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (ℓ : ℕ) (g : ℝ → BlockState p k → (BlockSite p k → ℂ) → ℝ)
    (hg : Measurable fun x : (ℝ × BlockState p k) × (BlockSite p k → ℂ) => g x.1.1 x.1.2 x.2) :
    Measurable fun x : ℝ × BlockState p k =>
      blockSectorFiberReal p k U x.2 x.1 ℓ (g x.1 x.2) := by
  have := isProbabilityMeasure_gue (BlockFrameIndex p) (blockTime p)
  have hf : Measurable fun q : JointVar p k =>
      blockWeight p k U q.1.1.2 q.1.1.1 q.1.2 q.2 *
        (if negativeCount (blockFrameM p k U q.1.1.2 q.1.1.1 q.1.2 q.2) = ℓ then (1 : ℝ) else 0) *
        g q.1.1.1 q.1.1.2 q.1.2 :=
    ((measurable_blockWeight_joint p k U hU).mul
      (measurable_blockSectorIndicator_joint p k U hU ℓ)).mul (hg.comp measurable_fst)
  have h2 := hf.stronglyMeasurable.integral_prod_right'
    (ν := gueMeasure (BlockFrameIndex p) (blockTime p))
  have h3 := h2.integral_prod_right' (ν := projectiveHaar (BlockSite p k))
  exact h3.measurable

/-!
## The sector sum is dominated by the normalizer
-/

/-- **Domination by `Z₀`.** For `Z₀(e) < ∞` and measurable `g` with `|g| ≤ M`:
`|Σ_{ℓ<W} 𝒜⁰_{ℓ,e}[g]| ≤ M · Z₀(e)`. Unconditional. -/
theorem abs_sum_blockSectorFiberReal_le
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (ω : BlockState p k) (e : ℝ) (g : (BlockSite p k → ℂ) → ℝ)
    (hg : Measurable g) (M : ℝ) (hM : ∀ v, |g v| ≤ M)
    (hZ : blockNormalizer p k U ω e ≠ ∞) :
    |∑ ℓ ∈ Finset.range p.W, blockSectorFiberReal p k U ω e ℓ g| ≤
      M * (blockNormalizer p k U ω e).toReal := by
  have := isProbabilityMeasure_gue (BlockFrameIndex p) (blockTime p)
  set μ := (projectiveHaar (BlockSite p k)).prod (gueMeasure (BlockFrameIndex p) (blockTime p))
    with hμ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hemb : Measurable fun z : (BlockSite p k → ℂ) ×
      Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ => (((e, ω), z.1), z.2) :=
    ((measurable_const.prodMk measurable_fst)).prodMk measurable_snd
  have hw : Measurable fun z : (BlockSite p k → ℂ) ×
      Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ => blockWeight p k U ω e z.1 z.2 := by
    have h := (measurable_blockWeight_joint p k U hU).comp hemb
    exact h
  have hs : ∀ ℓ : ℕ, Measurable fun z : (BlockSite p k → ℂ) ×
      Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ =>
      (if negativeCount (blockFrameM p k U ω e z.1 z.2) = ℓ then (1 : ℝ) else 0) := by
    intro ℓ
    have h := (measurable_blockSectorIndicator_joint p k U hU ℓ).comp hemb
    exact h
  have hw0 : ∀ z : (BlockSite p k → ℂ) × Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ,
      0 ≤ blockWeight p k U ω e z.1 z.2 := fun z => blockWeight_nonneg p k U ω e z.1 z.2
  have hZprod : ∫⁻ z, ENNReal.ofReal (blockWeight p k U ω e z.1 z.2) ∂μ =
      blockNormalizer p k U ω e := by
    have hm : AEMeasurable (fun z : (BlockSite p k → ℂ) ×
        Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ =>
        ENNReal.ofReal (blockWeight p k U ω e z.1 z.2)) μ :=
      (ENNReal.measurable_ofReal.comp hw).aemeasurable
    rw [lintegral_prod _ hm]
    rfl
  have hwint : Integrable (fun z : (BlockSite p k → ℂ) ×
      Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ => blockWeight p k U ω e z.1 z.2) μ := by
    refine ⟨hw.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hw0), hZprod]
    exact lt_top_iff_ne_top.mpr hZ
  have hint : ∀ ℓ : ℕ, Integrable (fun z : (BlockSite p k → ℂ) ×
      Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ => blockWeight p k U ω e z.1 z.2 *
        (if negativeCount (blockFrameM p k U ω e z.1 z.2) = ℓ then (1 : ℝ) else 0) * g z.1) μ := by
    intro ℓ
    refine (hwint.const_mul M).mono' ((hw.mul (hs ℓ)).mul (hg.comp measurable_fst)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hw0 z)]
    have hind : |(if negativeCount (blockFrameM p k U ω e z.1 z.2) = ℓ then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> simp
    have h1 := hM z.1
    have h2 := hw0 z
    calc blockWeight p k U ω e z.1 z.2 *
          |(if negativeCount (blockFrameM p k U ω e z.1 z.2) = ℓ then (1 : ℝ) else 0)| * |g z.1|
        ≤ blockWeight p k U ω e z.1 z.2 * 1 * M := by gcongr
      _ = M * blockWeight p k U ω e z.1 z.2 := by ring
  have hrep : ∀ ℓ : ℕ, blockSectorFiberReal p k U ω e ℓ g = ∫ z, blockWeight p k U ω e z.1 z.2 *
      (if negativeCount (blockFrameM p k U ω e z.1 z.2) = ℓ then (1 : ℝ) else 0) * g z.1 ∂μ := by
    intro ℓ
    rw [hμ, integral_prod _ (hint ℓ)]
    rfl
  have hsum : ∑ ℓ ∈ Finset.range p.W, blockSectorFiberReal p k U ω e ℓ g =
      ∫ z, blockWeight p k U ω e z.1 z.2 * g z.1 ∂μ := by
    simp_rw [hrep]
    rw [← integral_finsetSum _ fun ℓ _ => hint ℓ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have hlt : negativeCount (blockFrameM p k U ω e z.1 z.2) < p.W := by
      have h := negativeCount_le_card (blockFrameM p k U ω e z.1 z.2)
      rw [Fintype.card_fin] at h
      have := p.W_pos
      omega
    simp only
    rw [Finset.sum_eq_single (negativeCount (blockFrameM p k U ω e z.1 z.2))]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_range.2 hlt) h
  rw [hsum]
  have hle : ‖∫ z, blockWeight p k U ω e z.1 z.2 * g z.1 ∂μ‖ ≤
      ∫ z, M * blockWeight p k U ω e z.1 z.2 ∂μ := by
    refine norm_integral_le_of_norm_le (hwint.const_mul M)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 z), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM z.1) (hw0 z)
  rw [integral_const_mul, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hw0) hw.aestronglyMeasurable, hZprod] at hle
  rwa [Real.norm_eq_abs] at hle

end LeadProfileRegularity

open LeadProfileRegularity

/-!
## The three clauses
-/

section Clauses

variable (p : Parameters)

/-- Joint measurability of `(e, ω) ↦ leadAngularAverage` (clause 1 of `LeadAngularRegularity`).
Interface of the proof of.
-/
theorem measurable_leadAngularAverage_joint
    (U : (BlockSite p 0 → ℂ) → Matrix (BlockSite p 0) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (Φ : MassProfile →ᵇ ℝ) :
    Measurable (Function.uncurry fun e ω => leadAngularAverage p U Φ ω e) := by
  have hS : Measurable fun x : ℝ × BlockState p 0 => ∑ ℓ ∈ Finset.range p.W,
      blockSectorFiberReal p 0 U x.2 x.1 ℓ (leadReconObservable p Φ 0 x.2 x.1) :=
    Finset.measurable_sum _ fun ℓ _ => measurable_blockSectorFiberReal_joint p 0 U hU ℓ
      (fun e ω v => leadReconObservable p Φ 0 ω e v)
      (measurable_leadReconObservable_joint p 0 Φ)
  have hZ := ENNReal.measurable_toReal.comp (measurable_blockNormalizer_joint p 0 U hU)
  have h := hS.div hZ
  exact h

/-- `|leadAngularAverage| ≤ ‖Φ‖` for every `e, ω` (clause 2 of `LeadAngularRegularity`).
Interface of the proof of.
-/
theorem abs_leadAngularAverage_le
    (U : (BlockSite p 0 → ℂ) → Matrix (BlockSite p 0) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (Φ : MassProfile →ᵇ ℝ) (ω : BlockState p 0) (e : ℝ) :
    |leadAngularAverage p U Φ ω e| ≤ ‖Φ‖ := by
  unfold leadAngularAverage
  by_cases h0 : (blockNormalizer p 0 U ω e).toReal = 0
  · rw [h0, div_zero, abs_zero]
    exact norm_nonneg _
  have hZ : blockNormalizer p 0 U ω e ≠ ∞ := fun h => h0 (by rw [h]; rfl)
  have hpos : 0 < (blockNormalizer p 0 U ω e).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h0)
  have hgm : Measurable (leadReconObservable p Φ 0 ω e) := by
    have h := (measurable_leadReconObservable_joint p 0 Φ).comp
      ((measurable_const (a := (e, ω))).prodMk measurable_id)
    exact h
  have hb := abs_sum_blockSectorFiberReal_le p 0 U hU ω e (leadReconObservable p Φ 0 ω e) hgm
    ‖Φ‖ (fun v => abs_leadProfileRotationAverage_le p Φ _) hZ
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  exact hb

/-- **`LeadAngularRegularity` from the almost-sure finiteness of `Z₀`.** -/
theorem leadAngularRegularity_of_finite
    (hfin : ∀ (p : Parameters) (model : p.GaussianRingModel) (Pω : Measure (BlockState p 0)),
      IsBlockSplitting p 0 model Pω →
      ∀ (U : (BlockSite p 0 → ℂ) → Matrix (BlockSite p 0) (BlockFrameIndex p) ℂ),
      IsBlockFrame p 0 U → ∀ᵐ ω ∂Pω, ∀ e, blockNormalizer p 0 U ω e ≠ ∞) :
    LeadAngularRegularity := by
  intro p U hU Φ
  refine ⟨measurable_leadAngularAverage_joint p U hU.1 Φ,
    fun e ω => abs_leadAngularAverage_le p U hU.1 Φ ω e, ?_⟩
  intro model Pω hsplit
  filter_upwards [hfin p model Pω hsplit U hU] with ω hω e
  unfold leadAngularAverage
  by_cases h0 : (blockNormalizer p 0 U ω e).toReal = 0
  · rw [h0, zero_mul]
    have hgm : Measurable (leadReconObservable p Φ 0 ω e) := by
      have h := (measurable_leadReconObservable_joint p 0 Φ).comp
        ((measurable_const (a := (e, ω))).prodMk measurable_id)
      exact h
    have hb := abs_sum_blockSectorFiberReal_le p 0 U hU.1 ω e (leadReconObservable p Φ 0 ω e)
      hgm ‖Φ‖ (fun v => abs_leadProfileRotationAverage_le p Φ _) (hω e)
    rw [h0, mul_zero] at hb
    exact abs_nonpos_iff.mp hb
  · rw [mul_div_cancel₀ _ h0]

end Clauses

/-- **`LeadAngularRegularity`** from `FreshEigenpairDensityContract`: on Hermitian `H_R` (almost
surely under every one-block splitting law), `Z₀(e) = ofReal(palmMass) < ∞`
(`blockNormalizer_eq_palmMass`). -/
theorem leadAngularRegularity_of (hD : FreshEigenpairDensityContract) :
    LeadAngularRegularity := by
  refine leadAngularRegularity_of_finite fun p model Pω hsplit U hU => ?_
  filter_upwards [ae_blockSplit_isHermitian p model 0 hsplit] with ω hω e
  rw [blockNormalizer_eq_palmMass p 0 hD (blockEquiv p 0) U hU ω hω e]
  exact ENNReal.ofReal_ne_top

/-- **`LeadAngularRegularity`** from the `OneBlockPalmContract` (field `upper`:
`Z₀(e) ≤ C W` on Hermitian `H_R`), the contract already consumed by
`physicalLeadProfile_of_steps`.
-/
theorem leadAngularRegularity_of_oneBlockPalm (hPalm : OneBlockPalmContract) :
    LeadAngularRegularity := by
  refine leadAngularRegularity_of_finite fun p model Pω hsplit U hU => ?_
  obtain ⟨C, hC⟩ := hPalm.upper p.b p.b_pos p.b_lt_half
  filter_upwards [ae_blockSplit_isHermitian p model 0 hsplit] with ω hω e
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC p rfl 0 U hU ω hω e)

end BlockBand.Endpoints.Normalization
