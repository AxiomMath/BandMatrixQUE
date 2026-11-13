module

public import BlockBand.Internal.Contracts.Clocks
public import BlockBand.Coarea.ContractClauses
public import BlockBand.Endpoints.Normalization.RegularEventTraces

/-!
# One-block Palm identity: the one-block splitting law and the block frame

We prove the fields `splitting_exists` and `frame_exists` of `Clocks.OneBlockPalmContract`; the
block `k` is entirely fresh, `GUE_W(c/W)`.

**Splitting (`oneBlockPalm_splitting_exists`).** The diagonal block `H_kk` of the exact physical
law has entry variance `σ²_xy = c/W` on the block (`entryVariance`, `y.1 = x.1`), which is exactly
the one-block time `t = blockTime p = c/W`. The splitting law is therefore the image of the
physical law under `H ↦ ω = (H_R, C)` (`R` = off-block sites, `C = H_{R,k}`), and no residual
potential remains on the block. The reassembled law `(Pω ⊗ GUE_W(c/W)).map assembleBlock` is
Hermitian-supported and has the physical joint characteristic function (block coordinates carry the
GUE variance `t = c/W`, all other coordinates the physical variance), computed with
`integral_exp_gueTestPairing`; it equals `model.law` by `physicalGaussianRingLaw_unique`. This
follows the pair case `ContractClauses.coarea_splitting_exists` (residual factor `√(1 - t/σ²)`),
here with residual factor `0` on the block.

**Frame (`oneBlockPalm_frame_exists`).** `card(BlockSite) = W = (W-1)+1`,
`ContractClauses.exists_measurable_frame`.

Measure: the exact physical law `model.law`; every admissible `Parameters`, model and block `k`;
exact finite-dimensional identities (no norm, limit or uniformity).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea BlockBand.Coarea.ContractClauses
  BlockBand.Coarea.GUELaw
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
  BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate

section Split

variable (p : Parameters) (k : ZMod p.n)

/-- `H ↦ (H_R, C)`: off-block block and off-block-to-block coupling. -/
def oneBlockPalmSplitMap (H : p.SiteMatrix) : BlockState p k :=
  (fun x y => H x.1 y.1, fun x y => H x.1 y.1)

/-- The one-block splitting law: image of the physical law under `oneBlockPalmSplitMap`. -/
def oneBlockPalmSplitLaw (model : p.GaussianRingModel) : Measure (BlockState p k) :=
  (model.law : Measure p.SiteMatrix).map (oneBlockPalmSplitMap p k)

/-- Residual factor: `0` on the block `k × k`, `1` elsewhere. -/
private def siteFactor (x y : p.Site) : ℝ := if x.1 = k ∧ y.1 = k then 0 else 1

private theorem assembleBlock_splitMap (H : p.SiteMatrix) (hH : H.IsHermitian) :
    assembleBlock p k (oneBlockPalmSplitMap p k H) 0 =
      Matrix.of fun x y => (siteFactor p k x y : ℂ) * H x y := by
  ext x y
  unfold assembleBlock oneBlockPalmSplitMap siteFactor
  by_cases hx : x.1 = k <;> by_cases hy : y.1 = k
  · simp [hx, hy]
  · simp only [hx, hy, dite_true, dite_false, and_false, ite_false, Matrix.of_apply,
      Complex.ofReal_one, one_mul]
    exact hH.apply x y
  · simp [hx, hy]
  · simp [hx, hy]

private theorem assembleBlock_eq_add (ω : BlockState p k)
    (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) :
    assembleBlock p k ω G = assembleBlock p k ω 0 + assembleBlock p k 0 G := by
  ext x y
  rw [Matrix.add_apply]
  unfold assembleBlock
  by_cases hx : x.1 = k <;> by_cases hy : y.1 = k <;> simp [hx, hy]

private theorem coordinatePairing_add' (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ)
    (H K : p.SiteMatrix) :
    p.coordinatePairing d u v (H + K) =
      p.coordinatePairing d u v H + p.coordinatePairing d u v K :=
  coordinatePairing_add p d u v H K

private theorem sum_eq_sum_blockSite (f : p.Site → ℝ) (hf : ∀ x, ¬ x.1 = k → f x = 0) :
    ∑ x, f x = ∑ a : BlockSite p k, f a.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x : p.Site => x.1 = k) f]
  have h0 : ∑ a : {x : p.Site // ¬ x.1 = k}, f a.1 = 0 :=
    Finset.sum_eq_zero fun a _ => hf a.1 a.2
  rw [h0, add_zero]

private theorem assembleBlock_zero_apply (G : Matrix (BlockSite p k) (BlockSite p k) ℂ)
    (x y : p.Site) :
    assembleBlock p k 0 G x y =
      if hx : x.1 = k then if hy : y.1 = k then G ⟨x, hx⟩ ⟨y, hy⟩ else 0 else 0 := by
  unfold assembleBlock
  by_cases hx : x.1 = k <;> by_cases hy : y.1 = k <;> simp [hx, hy]

private theorem coordinatePairing_assembleBlock_zero (d : p.Site → ℝ)
    (u v : p.Site → p.Site → ℝ) (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) :
    p.coordinatePairing d u v (assembleBlock p k 0 G) =
      gueTestPairing (fun a : BlockSite p k => p.siteIndex a.1) (fun a => d a.1)
        (fun a b => u a.1 b.1) (fun a b => v a.1 b.1) G := by
  unfold Parameters.coordinatePairing gueTestPairing
  congr 1
  · rw [sum_eq_sum_blockSite p k]
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp [assembleBlock_zero_apply, a.2]
    · intro x hx
      simp [assembleBlock_zero_apply, hx]
  · simp only [Finset.sum_filter]
    rw [sum_eq_sum_blockSite p k]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [sum_eq_sum_blockSite p k]
      · refine Finset.sum_congr rfl fun b _ => ?_
        simp [assembleBlock_zero_apply, a.2, b.2]
      · intro y hy
        simp [assembleBlock_zero_apply, hy]
    · intro x hx
      refine Finset.sum_eq_zero fun y _ => ?_
      simp [assembleBlock_zero_apply, hx]

/-- The one-block time is `c/W` as a real number. -/
theorem oneBlockPalm_blockTime_coe : (blockTime p : ℝ) = p.c / p.W := by
  unfold blockTime
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  exact Real.coe_toNNReal _ (div_pos p.c_pos hW).le

private theorem siteFactor_sq (x y : p.Site) :
    p.entryVariance x y * siteFactor p k x y ^ 2 +
      (if x.1 = k ∧ y.1 = k then (blockTime p : ℝ) else 0) = p.entryVariance x y := by
  unfold siteFactor
  split_ifs with h
  · rw [oneBlockPalm_blockTime_coe]
    unfold Parameters.entryVariance
    simp only [h.2.trans h.1.symm, ↓reduceIte]
    ring
  · ring

private theorem coordinateVariance_split (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    p.coordinateVariance d u v =
      p.coordinateVariance (fun x => d x * siteFactor p k x x)
          (fun x y => u x y * siteFactor p k x y)
          (fun x y => v x y * siteFactor p k x y) +
        gueTestVariance (fun a : BlockSite p k => p.siteIndex a.1) (blockTime p)
          (fun a => d a.1) (fun a b => u a.1 b.1) (fun a b => v a.1 b.1) := by
  set t : ℝ := (blockTime p : ℝ)
  set m := siteFactor p k
  have hkey := siteFactor_sq p k
  have hg1 : (t * ∑ a : BlockSite p k, d a.1 ^ 2) =
      ∑ x : p.Site, (if x.1 = k ∧ x.1 = k then t else 0) * d x ^ 2 := by
    rw [Finset.mul_sum, sum_eq_sum_blockSite p k]
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp [a.2]
    · intro x hx
      simp [hx]
  have hg2 : (∑ a : BlockSite p k, ∑ b : BlockSite p k,
      if p.siteIndex a.1 < p.siteIndex b.1 then t / 2 * (u a.1 b.1 ^ 2 + v a.1 b.1 ^ 2) else 0) =
      ∑ x : p.Site, ∑ y ∈ Finset.univ.filter (fun y => p.siteIndex x < p.siteIndex y),
        (if x.1 = k ∧ y.1 = k then t else 0) / 2 * (u x y ^ 2 + v x y ^ 2) := by
    simp only [Finset.sum_filter]
    symm
    rw [sum_eq_sum_blockSite p k]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [sum_eq_sum_blockSite p k]
      · refine Finset.sum_congr rfl fun b _ => ?_
        simp [a.2, b.2]
      · intro y hy
        simp [hy]
    · intro x hx
      refine Finset.sum_eq_zero fun y _ => ?_
      simp [hx]
  unfold Parameters.coordinateVariance gueTestVariance
  rw [hg1, hg2]
  have e1 : ∑ x, p.entryVariance x x * d x ^ 2 =
      ∑ x, p.entryVariance x x * (d x * m x x) ^ 2 +
        ∑ x : p.Site, (if x.1 = k ∧ x.1 = k then t else 0) * d x ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have := hkey x x
    calc p.entryVariance x x * d x ^ 2
        = (p.entryVariance x x * m x x ^ 2 + (if x.1 = k ∧ x.1 = k then t else 0)) *
            d x ^ 2 := by rw [this]
      _ = _ := by ring
  have e2 : (∑ x, ∑ y ∈ Finset.univ.filter (fun y => p.siteIndex x < p.siteIndex y),
      p.entryVariance x y / 2 * (u x y ^ 2 + v x y ^ 2)) =
      (∑ x, ∑ y ∈ Finset.univ.filter (fun y => p.siteIndex x < p.siteIndex y),
        p.entryVariance x y / 2 * ((u x y * m x y) ^ 2 + (v x y * m x y) ^ 2)) +
      ∑ x : p.Site, ∑ y ∈ Finset.univ.filter (fun y => p.siteIndex x < p.siteIndex y),
        (if x.1 = k ∧ y.1 = k then t else 0) / 2 * (u x y ^ 2 + v x y ^ 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    have := hkey x y
    calc p.entryVariance x y / 2 * (u x y ^ 2 + v x y ^ 2)
        = (p.entryVariance x y * m x y ^ 2 + (if x.1 = k ∧ y.1 = k then t else 0)) / 2 *
              (u x y ^ 2 + v x y ^ 2) := by rw [this]
      _ = _ := by ring
  rw [e1, e2]
  ring

theorem oneBlockPalm_measurable_splitMap : Measurable (oneBlockPalmSplitMap p k) := by
  refine Measurable.prodMk ?_ ?_
  · exact Measurable.of_eval_matrix _ fun a b => Matrix.measurable_apply
  · exact Measurable.of_eval_matrix _ fun a b => Matrix.measurable_apply

/-- A reassembled matrix with Hermitian `H_R` and `G` is Hermitian (any coupling `C`). -/
theorem oneBlockPalm_assembleBlock_isHermitian (ω : BlockState p k)
    (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) (h1 : ω.1.IsHermitian) (hG : G.IsHermitian) :
    (assembleBlock p k ω G).IsHermitian := by
  ext x y
  rw [Matrix.conjTranspose_apply]
  unfold assembleBlock
  by_cases hx : x.1 = k <;> by_cases hy : y.1 = k
  · simp only [hx, hy, dite_true]
    exact hG.apply _ _
  · simp [hx, hy]
  · simp [hx, hy]
  · simp only [hx, hy, dite_false]
    exact h1.apply _ _

private theorem ae_splitLaw (model : p.GaussianRingModel) :
    ∀ᵐ ω ∂oneBlockPalmSplitLaw p k model, ω.1.IsHermitian := by
  unfold oneBlockPalmSplitLaw
  have hms : MeasurableSet {ω : BlockState p k | ω.1.IsHermitian} :=
    BlockBand.Model.Construction.measurableSet_isHermitian.preimage measurable_fst
  rw [ae_map_iff (oneBlockPalm_measurable_splitMap p k).aemeasurable hms]
  filter_upwards [model.isPhysical.1] with H hH
  ext a b
  simp only [oneBlockPalmSplitMap]
  exact hH.apply _ _

private instance isProbabilityMeasure_splitLaw (model : p.GaussianRingModel) :
    IsProbabilityMeasure (oneBlockPalmSplitLaw p k model) := by
  unfold oneBlockPalmSplitLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (oneBlockPalm_measurable_splitMap p k).aemeasurable).2 inferInstance

private instance isProbabilityMeasure_gue' :
    IsProbabilityMeasure (gueMeasure (BlockSite p k) (blockTime p)) :=
  regularEvent_isProbabilityMeasure_gue (BlockSite p k) (blockTime p)

/-- The candidate reassembled law. -/
private def assembledLaw (model : p.GaussianRingModel) : Measure p.SiteMatrix :=
  ((oneBlockPalmSplitLaw p k model).prod (gueMeasure (BlockSite p k) (blockTime p))).map
    (fun x => assembleBlock p k x.1 x.2)

private instance isProbabilityMeasure_assembledLaw (model : p.GaussianRingModel) :
    IsProbabilityMeasure (assembledLaw p k model) := by
  unfold assembledLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (regularEvent_measurable_assembleBlock p k).aemeasurable).2 inferInstance

private theorem ae_isHermitian_assembledLaw (model : p.GaussianRingModel) :
    ∀ᵐ H ∂assembledLaw p k model, H.IsHermitian := by
  unfold assembledLaw
  rw [ae_map_iff (regularEvent_measurable_assembleBlock p k).aemeasurable
    BlockBand.Model.Construction.measurableSet_isHermitian]
  have hω := (Measure.quasiMeasurePreserving_fst
    (μ := oneBlockPalmSplitLaw p k model)
    (ν := gueMeasure (BlockSite p k) (blockTime p))).ae (ae_splitLaw p k model)
  have hG := (Measure.quasiMeasurePreserving_snd
    (μ := oneBlockPalmSplitLaw p k model)
    (ν := gueMeasure (BlockSite p k) (blockTime p))).ae
      (ae_isHermitian_gueMeasure (ι := BlockSite p k) (blockTime p))
  filter_upwards [hω, hG] with x hx hx'
  exact oneBlockPalm_assembleBlock_isHermitian p k x.1 x.2 hx hx'

private theorem charFun_assembledLaw (model : p.GaussianRingModel) (d : p.Site → ℝ)
    (u v : p.Site → p.Site → ℝ) :
    ∫ H, Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ)) ∂assembledLaw p k model =
      Complex.exp (-(p.coordinateVariance d u v : ℂ) / 2) := by
  set κ : BlockSite p k → ℕ := fun a => p.siteIndex a.1
  have hκ : Function.Injective κ := p.siteIndex_injective.comp Subtype.val_injective
  unfold assembledLaw
  rw [integral_map (regularEvent_measurable_assembleBlock p k).aemeasurable
    (measurable_exp_pairing p d u v).aestronglyMeasurable]
  have hpt : ∀ x : BlockState p k × Matrix (BlockSite p k) (BlockSite p k) ℂ,
      Complex.exp (Complex.I * (p.coordinatePairing d u v (assembleBlock p k x.1 x.2) : ℂ)) =
        Complex.exp (Complex.I * (p.coordinatePairing d u v (assembleBlock p k x.1 0) : ℂ)) *
          Complex.exp (Complex.I * (gueTestPairing κ (fun a => d a.1) (fun a b => u a.1 b.1)
            (fun a b => v a.1 b.1) x.2 : ℂ)) := by
    intro x
    rw [assembleBlock_eq_add, coordinatePairing_add', coordinatePairing_assembleBlock_zero,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_prod_mul (fun ω : BlockState p k =>
      Complex.exp (Complex.I * (p.coordinatePairing d u v (assembleBlock p k ω 0) : ℂ)))
    (fun G : Matrix (BlockSite p k) (BlockSite p k) ℂ => Complex.exp (Complex.I *
      (gueTestPairing κ (fun a => d a.1) (fun a b => u a.1 b.1) (fun a b => v a.1 b.1) G : ℂ)))]
  rw [integral_exp_gueTestPairing κ hκ]
  have hmeas : Measurable (fun ω : BlockState p k =>
      Complex.exp (Complex.I * (p.coordinatePairing d u v (assembleBlock p k ω 0) : ℂ))) := by
    have hA : Measurable (fun ω : BlockState p k => assembleBlock p k ω 0) :=
      (regularEvent_measurable_assembleBlock p k).comp (measurable_id.prodMk measurable_const)
    exact (measurable_exp_pairing p d u v).comp hA
  unfold oneBlockPalmSplitLaw
  rw [integral_map (oneBlockPalm_measurable_splitMap p k).aemeasurable
    hmeas.aestronglyMeasurable]
  have hae : (fun H : p.SiteMatrix =>
      Complex.exp (Complex.I *
        (p.coordinatePairing d u v (assembleBlock p k (oneBlockPalmSplitMap p k H) 0) : ℂ))) =ᵐ[
      (model.law : Measure p.SiteMatrix)]
      fun H => Complex.exp (Complex.I * (p.coordinatePairing
        (fun x => d x * siteFactor p k x x)
        (fun x y => u x y * siteFactor p k x y)
        (fun x y => v x y * siteFactor p k x y) H : ℂ)) := by
    filter_upwards [model.isPhysical.1] with H hH
    rw [assembleBlock_splitMap p k H hH, coordinatePairing_scale p]
  rw [integral_congr_ae hae, model.isPhysical.2, ← Complex.exp_add,
    coordinateVariance_split p k d u v]
  congr 1
  push_cast
  ring

/-- **`OneBlockPalmContract.splitting_exists`** (the block `k` is entirely fresh, `GUE_W(c/W)`). The explicit law `Pω = (H ↦ (H_R, C)).law` is a one-block splitting law.
Measure: the exact physical law; every admissible `p`, model and block. -/
theorem oneBlockPalm_splitting_exists : ∀ (p : Parameters) (model : p.GaussianRingModel)
    (k : ZMod p.n), ∃ Pω : Measure (BlockState p k), IsBlockSplitting p k model Pω := by
  intro p model k
  refine ⟨oneBlockPalmSplitLaw p k model, ?_⟩
  let model' : p.GaussianRingModel :=
    ⟨⟨assembledLaw p k model, inferInstance⟩,
      ⟨ae_isHermitian_assembledLaw p k model, charFun_assembledLaw p k model⟩⟩
  have h := BlockBand.Parameters.physicalGaussianRingLaw_unique model' model
  exact congrArg (fun P : ProbabilityMeasure p.SiteMatrix => (P : Measure p.SiteMatrix)) h

end Split

/-- **`OneBlockPalmContract.frame_exists`**: a measurable orthonormal frame of `v^⊥ ⊂ ℂ^W`
(the Householder construction `ContractClauses.exists_measurable_frame`, `card = (W-1)+1`). -/
theorem oneBlockPalm_frame_exists : ∀ (p : Parameters) (k : ZMod p.n),
    ∃ U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ,
      IsBlockFrame p k U := by
  intro p k
  have h : Fintype.card (BlockSite p k) = (p.W - 1) + 1 := by
    rw [regularEvent_card_blockSite]
    have := p.W_pos
    omega
  exact exists_measurable_frame h

end BlockBand.Endpoints.Normalization
