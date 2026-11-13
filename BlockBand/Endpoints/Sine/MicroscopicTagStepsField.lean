module

public import BlockBand.Endpoints.Sine.MicroscopicTagStepsCommonPort
public import BlockBand.Endpoints.Sine.MicroscopicTagStepsPalm
public import BlockBand.Internal.Contracts.ClocksLeadProfile
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# The Gaussian-field identification from the lead field identification

This file proves `MicroscopicTagFieldIdentity` from `LeadFieldIdentificationContract`
(`microscopicTagFieldIdentity_of_contract`). The ingredients are:

* circular-Gaussian invariance: under every unitary (`mts_circularVectorLaw_map_unitary`,
  hence `M₀g =ᵈ Mg` whenever `M₀M₀* = MM*`, `mts_map_mulVec_eq_of_gram`), and under the
  reindexing `Fin 1 × Fin W ≃ BlockSite p k` underlying `blockPortVector`
  (`mts_circularVectorLaw_map_comp`);
* linearity of `blockLift` (`mts_blockLift_smul`);
* the matching of ring blocks with lead positions (`mts_clock_match`: relative block `1`, `n-1`,
  `2 + i` ↔ near port, far port, path position `i`, i.e. `leadRingBlock`);
* the product reassociation `(path ⊗ layer) ⊗ g = path ⊗ (layer ⊗ g)` (`mts_portLaw`).

The laws are `Pω` (the one-block exterior of block `k`), `circularVectorLaw` and `mts_portLaw`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix WithLp
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.ClocksCommonPort BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.ClocksLeadProfile
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

/-!
## Unitary invariance of the circular Gaussian vector
-/

section Unitary

variable {ι : Type}

/-- Complexification `r ↦ (r_{a,0} + i r_{a,1})_a`. -/
def mts_cplx (r : ι × Fin 2 → ℝ) : ι → ℂ :=
  fun a => (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I

/-- Realification `w ↦ (Re w_a, Im w_a)`. -/
def mts_real (w : ι → ℂ) : ι × Fin 2 → ℝ := fun p => if p.2 = 0 then (w p.1).re else (w p.1).im

theorem mts_cplx_real (w : ι → ℂ) : mts_cplx (mts_real w) = w := by
  funext a
  simp [mts_cplx, mts_real]

theorem mts_real_cplx (r : ι × Fin 2 → ℝ) : mts_real (mts_cplx r) = r := by
  funext p
  obtain ⟨a, j⟩ := p
  fin_cases j <;> simp [mts_cplx, mts_real]

theorem mts_continuous_cplx : Continuous (mts_cplx (ι := ι)) := by
  unfold mts_cplx
  fun_prop

theorem mts_sum_sq_real [Fintype ι] (w : ι → ℂ) :
    ∑ p, mts_real w p ^ 2 = ∑ a, Complex.normSq (w a) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [mts_real, Fin.sum_univ_two, Complex.normSq_apply, pow_two]

theorem mts_sum_normSq_unitary [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    ∑ a, Complex.normSq ((U *ᵥ v) a) = ∑ a, Complex.normSq (v a) := by
  have key (w : ι → ℂ) : ((∑ a, Complex.normSq (w a) : ℝ) : ℂ) = star w ⬝ᵥ w := by
    simp [dotProduct, Complex.normSq_eq_conj_mul_self]
  apply Complex.ofReal_injective
  rw [key, key, star_mulVec, dotProduct_mulVec, vecMul_vecMul,
    show Uᴴ * U = 1 from (Matrix.mem_unitaryGroup_iff').1 hU, vecMul_one]

/-- The real rotation induced by `U`. -/
def mts_rot [Fintype ι] (U : Matrix ι ι ℂ) : (ι × Fin 2 → ℝ) →ₗ[ℝ] (ι × Fin 2 → ℝ) where
  toFun r := mts_real (U *ᵥ mts_cplx r)
  map_add' r s := by
    have : mts_cplx (r + s) = mts_cplx r + mts_cplx s := by
      funext a; simp [mts_cplx]; ring
    rw [this, mulVec_add]
    funext p; simp only [mts_real, Pi.add_apply]; split_ifs <;> simp
  map_smul' t r := by
    have : mts_cplx (t • r) = (t : ℂ) • mts_cplx r := by
      funext a; simp [mts_cplx]; ring
    rw [this, mulVec_smul]
    funext p; simp only [mts_real, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp

theorem mts_rot_apply [Fintype ι] (U : Matrix ι ι ℂ) (r : ι × Fin 2 → ℝ) :
    mts_rot U r = mts_real (U *ᵥ mts_cplx r) := rfl

theorem mts_sum_sq_rot [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (r : ι × Fin 2 → ℝ) :
    ∑ p, mts_rot U r p ^ 2 = ∑ p, r p ^ 2 := by
  rw [mts_rot_apply, mts_sum_sq_real, mts_sum_normSq_unitary U hU, ← mts_sum_sq_real,
    mts_real_cplx]

/-- The rotation as a linear isometry equivalence of `EuclideanSpace ℝ (ι × Fin 2)`. -/
def mts_rotIso [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    EuclideanSpace ℝ (ι × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ι × Fin 2) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := (WithLp.linearEquiv 2 ℝ (ι × Fin 2 → ℝ)).symm.toLinearMap ∘ₗ mts_rot U ∘ₗ
        (WithLp.linearEquiv 2 ℝ (ι × Fin 2 → ℝ)).toLinearMap
      norm_map' := fun x => by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        congr 1
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          Real.norm_eq_abs, sq_abs]
        exact mts_sum_sq_rot U hU _ }
    rfl

theorem mts_pi_std_map_rot [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 1).map (mts_rot U) =
      Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 1 := by
  set P := Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 1
  have hP : P = (stdGaussian (EuclideanSpace ℝ (ι × Fin 2))).map ofLp := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop),
      show (ofLp ∘ toLp 2 : (ι × Fin 2 → ℝ) → _) = id from rfl, Measure.map_id]
  have hfun : (mts_rot U : (ι × Fin 2 → ℝ) → (ι × Fin 2 → ℝ)) ∘ ofLp =
      ofLp ∘ mts_rotIso U hU := by
    funext x; rfl
  have hrot_m : Measurable (mts_rot U : (ι × Fin 2 → ℝ) → (ι × Fin 2 → ℝ)) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  conv_lhs => rw [hP, Measure.map_map hrot_m (by fun_prop), hfun,
    ← Measure.map_map (by fun_prop) (mts_rotIso U hU).continuous.measurable,
    stdGaussian_map]
  exact hP.symm

theorem mts_gaussianReal_half :
    (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (1 / 2) * x) =
      gaussianReal 0 (1 / 2 : ℝ≥0) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt]

theorem mts_pi_half_eq_map [Fintype ι] :
    (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)) =
      (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 1).map
        (fun r p => Real.sqrt (1 / 2) * r p) := by
  rw [Measure.pi_map_pi (fun _ => by fun_prop)]
  simp_rw [mts_gaussianReal_half]

/-- **Unitary invariance of `circularVectorLaw`.** -/
theorem mts_circularVectorLaw_map_unitary [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (circularVectorLaw ι).map (fun h => U *ᵥ h) = circularVectorLaw ι := by
  have hlaw : circularVectorLaw ι =
      (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)).map mts_cplx := rfl
  have hrot_m : Measurable (mts_rot U : (ι × Fin 2 → ℝ) → (ι × Fin 2 → ℝ)) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hsc_m : Measurable
      (fun (r : ι × Fin 2 → ℝ) (p : ι × Fin 2) => Real.sqrt (1 / 2) * r p) := by fun_prop
  have hU_m : Measurable (fun h : ι → ℂ => U *ᵥ h) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hcomm : (fun h : ι → ℂ => U *ᵥ h) ∘ mts_cplx ∘
      (fun (r : ι × Fin 2 → ℝ) (p : ι × Fin 2) => Real.sqrt (1 / 2) * r p) =
      (mts_cplx ∘ (fun (r : ι × Fin 2 → ℝ) (p : ι × Fin 2) => Real.sqrt (1 / 2) * r p)) ∘
        mts_rot U := by
    funext r
    simp only [Function.comp_apply]
    have hs (s : ι × Fin 2 → ℝ) : mts_cplx (fun p => Real.sqrt (1 / 2) * s p) =
        ((Real.sqrt (1 / 2) : ℝ) : ℂ) • mts_cplx s := by
      funext a; simp [mts_cplx]; ring
    rw [hs, hs, mts_rot_apply, mts_cplx_real, mulVec_smul]
  rw [hlaw, mts_pi_half_eq_map, Measure.map_map mts_continuous_cplx.measurable hsc_m,
    Measure.map_map hU_m (mts_continuous_cplx.measurable.comp hsc_m), hcomm,
    ← Measure.map_map (mts_continuous_cplx.measurable.comp hsc_m) hrot_m,
    mts_pi_std_map_rot U hU]

/-- **The law of `Mg` depends only on `MM*`** (`g ~ CN(0, I)`, `M` invertible). -/
theorem mts_map_mulVec_eq_of_gram [Fintype ι] [DecidableEq ι] (M M₀ : Matrix ι ι ℂ)
    (hM : IsUnit M.det) (h : M₀ * M₀ᴴ = M * Mᴴ) :
    (circularVectorLaw ι).map (fun g => M₀ *ᵥ g) = (circularVectorLaw ι).map (fun g => M *ᵥ g) := by
  set V := M⁻¹ * M₀
  have hMH : IsUnit Mᴴ.det := by rw [det_conjTranspose]; exact hM.star
  have hV : V ∈ Matrix.unitaryGroup ι ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    calc V * Vᴴ = M⁻¹ * (M₀ * M₀ᴴ) * M⁻¹ᴴ := by
          simp only [V, conjTranspose_mul, Matrix.mul_assoc]
      _ = M⁻¹ * M * (Mᴴ * Mᴴ⁻¹) := by
          rw [h, conjTranspose_nonsing_inv]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul _ hM, mul_nonsing_inv _ hMH, Matrix.one_mul]
  have hM₀ : M₀ = M * V := by
    simp only [V]; rw [← Matrix.mul_assoc, mul_nonsing_inv _ hM, Matrix.one_mul]
  have hmV : Measurable (fun g : ι → ℂ => V *ᵥ g) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hmM : Measurable (fun g : ι → ℂ => M *ᵥ g) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hcomp : (fun g : ι → ℂ => M₀ *ᵥ g) = (fun g => M *ᵥ g) ∘ (fun g => V *ᵥ g) := by
    funext g; simp [hM₀, Matrix.mulVec_mulVec]
  rw [hcomp, ← Measure.map_map hmM hmV, mts_circularVectorLaw_map_unitary V hV]

end Unitary

/-!
## Linearity and measurability of the block lift
-/

section Lift

variable (p : Parameters) (k : ZMod p.n)

theorem mts_blockLift_smul (ω : BlockState p k) (e : ℝ) (s : ℂ) (v : BlockSite p k → ℂ) :
    blockLift p k ω e (s • v) = s • blockLift p k ω e v := by
  funext x
  by_cases hx : x.1 = k
  · simp [blockLift, hx]
  · simp [blockLift, hx, mulVec_smul]

theorem mts_measurable_blockLift_of (e : ℝ) {α : Type*} [MeasurableSpace α]
    {ω : α → BlockState p k} {v : α → BlockSite p k → ℂ} (hω : Measurable ω)
    (hv : Measurable v) : Measurable (fun a => blockLift p k (ω a) e (v a)) := by
  have hT : Measurable (fun a => physicalCoareaT (ω a).1 (ω a).2 e) := by
    unfold physicalCoareaT physicalCoareaResolvent
    exact measurable_mat_mul (measurable_matrix_inv.comp (measurable_mat_sub
      (measurable_fst.comp hω) measurable_const)) (measurable_snd.comp hω)
  have hTv := mts_measurable_mulVec hT hv
  refine Measurable.of_eval fun x => ?_
  by_cases hx : x.1 = k
  · simp only [blockLift, hx, dite_true]
    exact (measurable_pi_apply _).comp hv
  · simp only [blockLift, hx, dite_false]
    exact ((measurable_pi_apply _).comp hTv).neg

theorem mts_measurable_leadExterior :
    Measurable (fun x : GrowthPath p.W × LayerSample p.W .common => leadExterior p k x) := by
  have hpath : Measurable (fun x : GrowthPath p.W × LayerSample p.W .common =>
      pathAt p.W (p.n - 3) x.1) := (measurable_pathAt _ _).comp measurable_fst
  have hM : Measurable (fun x : GrowthPath p.W × LayerSample p.W .common =>
      leadExteriorMatrix p x.1 x.2) := by
    unfold leadExteriorMatrix
    exact measurable_fromBlocks (measurable_pathMatrix.comp hpath)
      (measurable_pathPortCoupling.comp hpath)
      (measurable_conjTranspose''.comp (measurable_pathPortCoupling.comp hpath))
      (mts_measurable_blockDiag (measurable_fst.comp measurable_snd))
  have hB : Measurable (fun x : GrowthPath p.W × LayerSample p.W .common =>
      bondMatrix .common x.2.2) :=
    mts_measurable_bondMatrix .common (measurable_snd.comp measurable_snd)
  have hCpl : Measurable (fun x : GrowthPath p.W × LayerSample p.W .common =>
      leadExteriorCoupling p x.2) := by
    refine Measurable.of_eval fun u => Measurable.of_eval fun v => ?_
    rcases u with u | u
    · exact measurable_const
    · exact (measurable_pi_apply v).comp ((measurable_pi_apply u).comp hB)
  unfold leadExterior
  refine Measurable.prodMk ?_ ?_
  · refine Measurable.of_eval fun a => Measurable.of_eval fun c => ?_
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hM)
  · refine Measurable.of_eval fun a => Measurable.of_eval fun y => ?_
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hCpl)

end Lift

theorem mts_measurable_commonPortH (b e : ℝ) {W : ℕ} {α : Type*} [MeasurableSpace α]
    {X : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ω : α → LayerSample W .common}
    (hX : Measurable X) (hω : Measurable ω) :
    Measurable (fun a => commonPortH b e (X a) (ω a)) := by
  have hdiag : Measurable (fun a =>
      BlockBand.Internal.Contracts.Layers.blockDiag (ω a).1 - (e : ℂ) • 1 - X a) :=
    measurable_mat_sub (measurable_mat_sub (mts_measurable_blockDiag
      (measurable_fst.comp hω)) measurable_const) hX
  have hbond : Measurable (fun a => bondMatrix .common (ω a).2) :=
    mts_measurable_bondMatrix .common (measurable_snd.comp hω)
  have hM : Measurable (fun a => layerMatrix .common e (commonZ b e) (X a) (ω a)) := by
    unfold layerMatrix
    exact measurable_fromBlocks hdiag hbond (measurable_conjTranspose''.comp hbond)
      measurable_const
  have hinv : Measurable (fun a => (layerMatrix .common e (commonZ b e) (X a) (ω a))⁻¹) :=
    measurable_matrix_inv.comp hM
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  exact (measurable_pi_apply (Sum.inr y)).comp ((measurable_pi_apply (Sum.inr x)).comp hinv)

/-- The ported block clocks are measurable in the ported sample. -/
theorem mts_measurable_portBlockClock (b e : ℝ) (n W : ℕ) (j : ZMod n) :
    Measurable (fun y : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      mts_portBlockClock b e n W y j) := by
  have hX : Measurable (fun y : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      leadSchur e W (n - 3) y.1) := (mts_measurable_leadSchur e W (n - 3)).comp measurable_fst
  have hl : Measurable (fun y : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      y.2.1) := measurable_fst.comp measurable_snd
  have hg : Measurable (fun y : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      y.2.2) := measurable_snd.comp measurable_snd
  have hH : Measurable (fun y : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      commonPortH b e (leadSchur e W (n - 3) y.1) y.2.1) := mts_measurable_commonPortH b e hX hl
  have hHg : Measurable (fun y : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      commonPortH b e (leadSchur e W (n - 3) y.1) y.2.1 *ᵥ y.2.2) := mts_measurable_mulVec hH hg
  unfold mts_portBlockClock
  refine Measurable.add ?_ ?_
  · split_ifs
    · exact Finset.measurable_sum _ fun a _ => (continuous_norm.measurable.comp
        ((measurable_pi_apply _).comp hHg)).pow_const 2
    · exact measurable_const
  · refine Finset.measurable_sum _ fun z _ => ?_
    split_ifs
    · exact measurable_leadPositionMass_of b W (n - 3) z (e := fun _ => e)
        (x := fun y : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
          (y.1, commonPortProbe b e (leadSchur e W (n - 3) y.1) y.2)) measurable_const
        (mts_measurable_portProbe b e W (n - 3))
    · exact measurable_const

/-!
## Ring blocks and lead positions
-/

theorem mts_leadRingBlock_pos (r : ℕ) (x : Fin r ⊕ Fin 2) : 1 ≤ leadRingBlock r x := by
  rcases x with i | j
  · simp [leadRingBlock]
  · simp only [leadRingBlock]; split_ifs <;> omega

/-- **Matching of a ring block with a lead position.** For `j ≠ k`, the clock of ring block `j`
read through `leadPos` is the lead mass of the position at `leadRingBlock = (j - k).val`. -/
theorem mts_clock_match (p : Parameters) (k : ZMod p.n) (b e : ℝ) (ω : GrowthPath p.W)
    (h : Fin 2 × Fin p.W → ℂ) (j : ZMod p.n) (hj : j ≠ k) :
    ∑ a : Fin p.W, ‖(leadResponse b e p.W (p.n - 3) ω *ᵥ h)
        (leadPos p k ⟨(j, a), hj⟩)‖ ^ 2 =
      ∑ x : Fin (p.n - 3) ⊕ Fin 2, if leadRingBlock (p.n - 3) x = (j - k).val then
        leadPositionMass b e p.W (p.n - 3) ω h x else 0 := by
  have : NeZero p.n := ⟨by have := p.n_ge_four; omega⟩
  have hn := p.n_ge_four
  set rel := (j - k).val with hrel
  have hrel0 : rel ≠ 0 := by
    rw [hrel, Ne, ZMod.val_eq_zero, sub_eq_zero]; exact hj
  have hrelt : rel < p.n := ZMod.val_lt _
  set ψ := leadResponse b e p.W (p.n - 3) ω *ᵥ h
  have hpos : ∀ a : Fin p.W, leadPos p k ⟨(j, a), hj⟩ =
      if rel = 1 then Sum.inr ((0 : Fin 2), a) else if rel = p.n - 1 then Sum.inr ((1 : Fin 2), a)
      else Sum.inl (⟨min (rel - 2) (p.n - 3 - 1), by omega⟩, a) := fun a => rfl
  have hmass : ∀ y : Fin (p.n - 3) ⊕ Fin 2, leadPositionMass b e p.W (p.n - 3) ω h y =
      match y with
      | Sum.inl i => ∑ a : Fin p.W, ‖ψ (Sum.inl (i, a))‖ ^ 2
      | Sum.inr i => ∑ a : Fin p.W, ‖ψ (Sum.inr (i, a))‖ ^ 2 := by
    intro y; rcases y with i | i <;> rfl
  have hr : leadRingBlock (p.n - 3) (Sum.inr 1) = p.n - 1 := by
    simp only [leadRingBlock]; rw [ite_eq_right (by decide)]; omega
  have hr0 : leadRingBlock (p.n - 3) (Sum.inr 0) = 1 := by simp [leadRingBlock]
  have hri : ∀ i : Fin (p.n - 3), leadRingBlock (p.n - 3) (Sum.inl i) = i.val + 2 :=
    fun i => rfl
  by_cases h1 : rel = 1
  · have hp : ∀ a, leadPos p k ⟨(j, a), hj⟩ = Sum.inr ((0 : Fin 2), a) := fun a => by
      rw [hpos, ite_eq_left h1]
    rw [Finset.sum_eq_single (Sum.inr 0)]
    · rw [ite_eq_left (by rw [hr0, h1]), hmass]
      exact Finset.sum_congr rfl fun a _ => by rw [hp]
    · intro x _ hx
      refine ite_eq_right ?_
      rcases x with i | i
      · rw [hri]; omega
      · fin_cases i
        · exact absurd rfl hx
        · show leadRingBlock (p.n - 3) (Sum.inr 1) ≠ rel
          rw [hr]; omega
    · simp
  by_cases h2 : rel = p.n - 1
  · have hp : ∀ a, leadPos p k ⟨(j, a), hj⟩ = Sum.inr ((1 : Fin 2), a) := fun a => by
      rw [hpos, ite_eq_right h1, ite_eq_left h2]
    rw [Finset.sum_eq_single (Sum.inr 1)]
    · rw [ite_eq_left (by rw [hr, h2]), hmass]
      exact Finset.sum_congr rfl fun a _ => by rw [hp]
    · intro x _ hx
      refine ite_eq_right ?_
      rcases x with i | i
      · rw [hri]; have := i.isLt; omega
      · fin_cases i
        · show leadRingBlock (p.n - 3) (Sum.inr 0) ≠ rel
          rw [hr0]; omega
        · exact absurd rfl hx
    · simp
  · have hr2 : 2 ≤ rel := by omega
    have hrl : rel - 2 < p.n - 3 := by omega
    have hmin : min (rel - 2) (p.n - 3 - 1) = rel - 2 := min_eq_left (by omega)
    have hp : ∀ a, leadPos p k ⟨(j, a), hj⟩ = Sum.inl (⟨rel - 2, hrl⟩, a) := fun a => by
      rw [hpos, ite_eq_right h1, ite_eq_right h2]
      simp only [Sum.inl.injEq, Prod.mk.injEq, and_true]
      exact Fin.ext hmin
    rw [Finset.sum_eq_single (Sum.inl ⟨rel - 2, hrl⟩)]
    · rw [ite_eq_left (by rw [hri]; simp only; omega), hmass]
      exact Finset.sum_congr rfl fun a _ => by rw [hp]
    · intro x _ hx
      refine ite_eq_right ?_
      rcases x with i | i
      · have hi : i.val ≠ rel - 2 := fun h0 => hx (by congr 1; exact Fin.ext h0)
        rw [hri]; omega
      · fin_cases i
        · show leadRingBlock (p.n - 3) (Sum.inr 0) ≠ rel
          rw [hr0]; omega
        · show leadRingBlock (p.n - 3) (Sum.inr 1) ≠ rel
          rw [hr]; omega
    · simp

/-!
## The field identification
-/

/-- The common-port coordinates of a block-`k` vector, as a reindexing. -/
def mts_blockPortEquiv (p : Parameters) (k : ZMod p.n) : Fin 1 × Fin p.W ≃ BlockSite p k where
  toFun i := ⟨(k, i.2), rfl⟩
  invFun x := ((0 : Fin 1), x.1.2)
  left_inv i := by
    obtain ⟨i0, a⟩ := i
    have : i0 = 0 := Subsingleton.elim _ _
    subst this; rfl
  right_inv x := by
    obtain ⟨⟨j, a⟩, h⟩ := x
    simp only at h
    subst h
    rfl

/-- The block clocks `(‖P_j L(e) v‖²)_j` of a lifted field. -/
def mts_fieldClock (p : Parameters) (k : ZMod p.n) (e : ℝ) (ω : BlockState p k)
    (v : BlockSite p k → ℂ) : ZMod p.n → ℝ :=
  fun j => ∑ a : Fin p.W, ‖blockLift p k ω e v (j, a)‖ ^ 2

theorem mts_measurable_fieldClock_of (p : Parameters) (k : ZMod p.n) (e : ℝ) {α : Type*}
    [MeasurableSpace α] {ω : α → BlockState p k} {v : α → BlockSite p k → ℂ}
    (hω : Measurable ω) (hv : Measurable v) :
    Measurable (fun a => mts_fieldClock p k e (ω a) (v a)) := by
  refine Measurable.of_eval fun j => Finset.measurable_sum _ fun a _ => ?_
  exact (continuous_norm.measurable.comp ((measurable_pi_apply _).comp
    (mts_measurable_blockLift_of p k e hω hv))).pow_const 2

/-- The ported test `Ψ((c · clock_{j-k})_j)`. -/
def mts_portField (p : Parameters) (k : ZMod p.n) (e : ℝ) (Ψ : (ZMod p.n → ℝ) → ℝ)
    (y : GrowthPath p.W × (LayerSample p.W .common × (Fin 1 × Fin p.W → ℂ))) : ℝ :=
  Ψ (fun j => p.c * mts_portBlockClock p.b e p.n p.W y (j - k))

theorem mts_measurable_portField (p : Parameters) (k : ZMod p.n) (e : ℝ)
    {Ψ : (ZMod p.n → ℝ) → ℝ} (hΨ : Measurable Ψ) : Measurable (mts_portField p k e Ψ) :=
  hΨ.comp (Measurable.of_eval fun j =>
    measurable_const.mul (mts_measurable_portBlockClock p.b e p.n p.W (j - k)))

/-- **`LeadFieldIdentificationContract` implies `MicroscopicTagFieldIdentity`.** -/
theorem microscopicTagFieldIdentity_of_contract (hL : LeadFieldIdentificationContract) :
    MicroscopicTagFieldIdentity := by
  intro p model k Pω hs e he1 he2 M₀ hM₀ hM₀Γ Ψ hΨ hΨb
  obtain ⟨C, hC⟩ := hΨb
  have : NeZero p.n := ⟨by have := p.n_ge_four; omega⟩
  have hPg := passDeriv_isProbabilityMeasure_growthPathLaw p.W p.b
  have hPl : IsProbabilityMeasure (layerLaw p.W p.b .common) := by
    have i1 : ∀ _ : Fin 2, IsProbabilityMeasure (gueMeasure (Fin p.W)
        (Real.toNNReal ((1 - 2 * p.b) / p.W))) := fun _ => passDeriv_isProbabilityMeasure_gue _ _
    have i2 : ∀ _ : Fin 2, ∀ _ : Fin 1, IsProbabilityMeasure
        (ginibreMeasure (Fin p.W) (Fin p.W) (Real.toNNReal (p.b / p.W))) :=
      fun _ _ => passDeriv_isProbabilityMeasure_ginibre _ _ _
    unfold layerLaw; infer_instance
  have hPcv : IsProbabilityMeasure (circularVectorLaw (Fin 1 × Fin p.W)) := by
    unfold circularVectorLaw; infer_instance
  -- the left integrand
  have hv0 : Measurable (fun q : BlockState p k × (BlockSite p k → ℂ) => M₀ q.1 *ᵥ q.2) :=
    mts_measurable_mulVec (hM₀.comp measurable_fst) measurable_snd
  have hc0 : Measurable (fun q : BlockState p k × (BlockSite p k → ℂ) =>
      mts_fieldClock p k e q.1 (M₀ q.1 *ᵥ q.2)) :=
    mts_measurable_fieldClock_of p k e measurable_fst hv0
  have h0 : Measurable (fun q : BlockState p k × (BlockSite p k → ℂ) =>
      Ψ (mts_fieldClock p k e q.1 (M₀ q.1 *ᵥ q.2))) := hΨ.comp hc0
  have hFm : StronglyMeasurable (fun ω : BlockState p k =>
      ∫ g, Ψ (mts_fieldClock p k e ω (M₀ ω *ᵥ g)) ∂circularVectorLaw (BlockSite p k)) :=
    h0.stronglyMeasurable.integral_prod_right'
  show (∫ ω, ∫ g, Ψ (mts_fieldClock p k e ω (M₀ ω *ᵥ g)) ∂circularVectorLaw (BlockSite p k)
      ∂Pω) = ∫ y, mts_portField p k e Ψ y ∂mts_portLaw p.W p.b
  rw [hL.law p model k Pω hs, integral_map (mts_measurable_leadExterior p k).aemeasurable
    hFm.aestronglyMeasurable]
  have hGm := mts_measurable_portField p k e hΨ
  have hae : ∀ᵐ x ∂((growthPathLaw p.W p.b).prod (layerLaw p.W p.b .common)),
      (∫ g, Ψ (mts_fieldClock p k e (leadExterior p k x) (M₀ (leadExterior p k x) *ᵥ g))
        ∂circularVectorLaw (BlockSite p k)) =
      ∫ g', mts_portField p k e Ψ (x.1, (x.2, g')) ∂circularVectorLaw (Fin 1 × Fin p.W) := by
    filter_upwards [hL.regular_ae p k e he1 he2] with x hx
    have hdetS : (blockShifted p k (leadExterior p k x) e).det ≠ 0 := hx.2.2.2.1
    have hMf : IsUnit (blockFieldFactor p k (leadExterior p k x) e).det := by
      unfold blockFieldFactor
      rw [det_smul]
      refine IsUnit.mul (IsUnit.pow _ ?_) (isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hdetS))
      rw [isUnit_iff_ne_zero, Ne, Complex.ofReal_eq_zero, Real.sqrt_eq_zero p.c_pos.le]
      exact p.c_pos.ne'
    have hgram : M₀ (leadExterior p k x) * (M₀ (leadExterior p k x))ᴴ =
        blockFieldFactor p k (leadExterior p k x) e *
          (blockFieldFactor p k (leadExterior p k x) e)ᴴ := by
      rw [hM₀Γ, hL.covariance p k _ e hdetS]; rfl
    have hmeas : Measurable (fun v => Ψ (mts_fieldClock p k e (leadExterior p k x) v)) :=
      hΨ.comp (mts_measurable_fieldClock_of p k e measurable_const measurable_id)
    have hm0 : Measurable (fun g : BlockSite p k → ℂ => M₀ (leadExterior p k x) *ᵥ g) :=
      (Continuous.matrix_mulVec continuous_const continuous_id).measurable
    have hmf : Measurable (fun g : BlockSite p k → ℂ =>
        blockFieldFactor p k (leadExterior p k x) e *ᵥ g) :=
      (Continuous.matrix_mulVec continuous_const continuous_id).measurable
    rw [← integral_map hm0.aemeasurable hmeas.aestronglyMeasurable,
      mts_map_mulVec_eq_of_gram _ _ hMf hgram,
      integral_map hmf.aemeasurable hmeas.aestronglyMeasurable]
    -- the field is `√c (Hg, ULg)`
    have h2 : ∀ g : BlockSite p k → ℂ,
        Ψ (mts_fieldClock p k e (leadExterior p k x)
          (blockFieldFactor p k (leadExterior p k x) e *ᵥ g)) =
        mts_portField p k e Ψ (x.1, (x.2, g ∘ mts_blockPortEquiv p k)) := by
      intro g
      unfold mts_portField
      congr 1
      funext j
      have hMg : blockFieldFactor p k (leadExterior p k x) e *ᵥ g =
          ((Real.sqrt p.c : ℝ) : ℂ) • ((blockShifted p k (leadExterior p k x) e)⁻¹ *ᵥ g) := by
        unfold blockFieldFactor; rw [Matrix.smul_mulVec]
      have hsq : ∀ z : ℂ, ‖((Real.sqrt p.c : ℝ) : ℂ) * z‖ ^ 2 = p.c * ‖z‖ ^ 2 := by
        intro z
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
          mul_pow, Real.sq_sqrt p.c_pos.le]
      unfold mts_fieldClock
      rw [hMg, mts_blockLift_smul]
      simp only [Pi.smul_apply, smul_eq_mul, hsq, ← Finset.mul_sum]
      congr 1
      have hid : ∀ a : Fin p.W, blockLift p k (leadExterior p k x) e
          ((blockShifted p k (leadExterior p k x) e)⁻¹ *ᵥ g) (j, a) =
          if hy : j = k then (commonPortH p.b e (leadSchur e p.W (p.n - 3) x.1) x.2 *ᵥ
              blockPortVector p k g) ((0 : Fin 1), a)
          else ((leadResponse p.b e p.W (p.n - 3) x.1 *
              commonPortL p.b e (leadSchur e p.W (p.n - 3) x.1) x.2) *ᵥ
              blockPortVector p k g) (leadPos p k ⟨(j, a), hy⟩) :=
        fun a => hL.identity p k e x hx g (j, a)
      simp only [hid]
      unfold mts_portBlockClock
      by_cases hjk : j = k
      · subst hjk
        have h0' : ∀ y : Fin (p.n - 3) ⊕ Fin 2, leadRingBlock (p.n - 3) y ≠ (j - j).val := by
          intro y; rw [sub_self, ZMod.val_zero]
          exact Nat.one_le_iff_ne_zero.1 (mts_leadRingBlock_pos _ y)
        simp only [dite_true, sub_self, ZMod.val_zero, ite_true]
        rw [Finset.sum_eq_zero fun y _ => ite_eq_right (by
          have := h0' y; rwa [sub_self, ZMod.val_zero] at this), add_zero]
        rfl
      · have hv : (j - k).val ≠ 0 := by rw [Ne, ZMod.val_eq_zero, sub_eq_zero]; exact hjk
        simp only [hjk, dite_false, hv, ite_false, zero_add]
        rw [← mts_clock_match p k p.b e x.1 _ j hjk]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Matrix.mulVec_mulVec]
        rfl
    simp_rw [h2]
    have hmb : Measurable (fun g : BlockSite p k → ℂ => g ∘ mts_blockPortEquiv p k) :=
      mts_measurable_comp_equiv _
    have hGx : Measurable (fun g' : Fin 1 × Fin p.W → ℂ => mts_portField p k e Ψ (x.1, (x.2, g'))) :=
      hGm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    rw [← mts_circularVectorLaw_map_comp (mts_blockPortEquiv p k)]
    exact (integral_map hmb.aemeasurable hGx.aestronglyMeasurable).symm
  rw [integral_congr_ae hae]
  -- reassociate the product
  have hGi : Integrable (fun z : (GrowthPath p.W × LayerSample p.W .common) ×
      (Fin 1 × Fin p.W → ℂ) => mts_portField p k e Ψ (z.1.1, (z.1.2, z.2)))
      (((growthPathLaw p.W p.b).prod (layerLaw p.W p.b .common)).prod
        (circularVectorLaw (Fin 1 × Fin p.W))) := by
    refine Integrable.of_bound (hGm.comp MeasurableEquiv.prodAssoc.measurable).aestronglyMeasurable
      C (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]; exact hC _
  rw [← integral_prod _ hGi]
  have hmp := measurePreserving_prodAssoc (growthPathLaw p.W p.b) (layerLaw p.W p.b .common)
    (circularVectorLaw (Fin 1 × Fin p.W))
  exact hmp.integral_comp' (mts_portField p k e Ψ)

end BlockBand.Endpoints
