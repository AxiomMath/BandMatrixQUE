module

public import BlockBand.Endpoints.Clock.OpenInputsProofDefs
public import BlockBand.Endpoints.Clock.ClockMixingMeasure
public import BlockBand.Endpoints.Clock.ZeroEntranceProbPert
public import BlockBand.Layers.GinibreTails
public import BlockBand.Layers.MatchedScalar

/-!
# The open-inputs lemma: the weighted-layer lemma for one block with one port

The fresh identities of the weighted-layer lemma apply to one block with an independent Hermitian
past. `onePortWeighted_of` proves `OnePortWeighted` from `WeightedLayerContract` (fields
`clockMean`, `clockNoise`, `unrestricted`) and `GaussianAbsorptionContract` (almost sure
invertibility only).

## The embedding

For a Hermitian `X` and `Y ⪰ 0` (`W × W`) put `X₂ = diag(X, X)` and `Y₂ = S*YS = diag(Y, 0)` on
`Fin 2 × Fin W` (`S` selects block `0`). The separate-port layer with old input `X₂` decouples:
its augmented matrix is, after the site relabelling `siteEquiv`, the block diagonal of the two
one-port augmented matrices of the blocks `i = 0, 1` (`proj i`: block `i` of the separate-port
sample). Whenever both are invertible (almost surely, `GaussianAbsorptionContract`), the
separate-port `L₂ = K₂ 𝒢₁₂` is `diag(L(proj 0), L(proj 1))` and
`W⁻¹ Re Tr(L₂*Y₂L₂) = clockT b E X Y (proj 0)`. The map `proj 0` pushes the separate-port law
to the one-port law (`measurePreserving_proj`). Moreover `d(X₂) = δ₀(X)` (`matchedDistance`
of the block-diagonal input) and `W⁻¹ Re Tr Y₂ = clockU Y`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal Matrix ComplexOrder

namespace OpenInputsProof

namespace Embed

variable {W : ℕ}

/-!
## Block-diagonal matrices on `Fin 2 × Fin W`
-/

/-- `diag(M 0, M 1)` on `Fin 2 × Fin W`. -/
def bd2 (M : Fin 2 → Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (blockDiagonal M).submatrix (Equiv.prodComm (Fin 2) (Fin W)) (Equiv.prodComm (Fin 2) (Fin W))

theorem bd2_apply (M : Fin 2 → Matrix (Fin W) (Fin W) ℂ) (i k : Fin 2) (a c : Fin W) :
    bd2 M (i, a) (k, c) = if i = k then M i a c else 0 := by
  simp [bd2, blockDiagonal_apply]

theorem bd2_mul (M N : Fin 2 → Matrix (Fin W) (Fin W) ℂ) :
    bd2 M * bd2 N = bd2 fun i => M i * N i := by
  unfold bd2
  rw [submatrix_mul_equiv, ← blockDiagonal_mul]

theorem bd2_conjTranspose (M : Fin 2 → Matrix (Fin W) (Fin W) ℂ) :
    (bd2 M)ᴴ = bd2 fun i => (M i)ᴴ := by
  unfold bd2
  rw [conjTranspose_submatrix, blockDiagonal_conjTranspose]

theorem bd2_one : bd2 (fun _ => (1 : Matrix (Fin W) (Fin W) ℂ)) = 1 := by
  unfold bd2
  have : (blockDiagonal fun _ : Fin 2 => (1 : Matrix (Fin W) (Fin W) ℂ)) = 1 := blockDiagonal_one
  rw [this, submatrix_one_equiv]

theorem bd2_inv (M : Fin 2 → Matrix (Fin W) (Fin W) ℂ) (h : ∀ i, IsUnit (M i).det) :
    (bd2 M)⁻¹ = bd2 fun i => (M i)⁻¹ := by
  refine inv_eq_right_inv ?_
  rw [bd2_mul]
  have : (fun i => M i * (M i)⁻¹) = fun _ => (1 : Matrix (Fin W) (Fin W) ℂ) := by
    funext i; exact mul_nonsing_inv _ (h i)
  rw [this, bd2_one]

theorem trace_bd2 (M : Fin 2 → Matrix (Fin W) (Fin W) ℂ) :
    (bd2 M).trace = (M 0).trace + (M 1).trace := by
  simp only [trace, diag, bd2_apply, ite_true, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The selector of block `0`. -/
def sel (W : ℕ) : Matrix (Fin W) (Fin 2 × Fin W) ℂ :=
  Matrix.of fun a ic => if ic.1 = 0 then (1 : Matrix (Fin W) (Fin W) ℂ) a ic.2 else 0

theorem sel_mul_bd2 (M : Fin 2 → Matrix (Fin W) (Fin W) ℂ) :
    sel W * bd2 M = M 0 * sel W := by
  ext a ⟨k, c⟩
  simp only [mul_apply, sel, of_apply, bd2_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases k <;> simp [one_apply]

theorem sel_mul_conjTranspose : sel W * (sel W)ᴴ = 1 := by
  ext a c
  simp only [mul_apply, sel, of_apply, conjTranspose_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  simp [one_apply]

/-!
## The site relabelling and the decoupled layer
-/

/-- `inl (i, a) ↦ (inl (0, a), i)`, `inr (j, a) ↦ (inr (0, a), j)`. -/
def siteEquiv (W : ℕ) : LayerSite W .separate ≃ LayerSite W .oneBlockOnePort × Fin 2 where
  toFun s := match s with
    | Sum.inl (i, a) => (Sum.inl ((0 : Fin 1), a), i)
    | Sum.inr (j, a) => (Sum.inr ((0 : Fin 1), a), j)
  invFun t := match t with
    | (Sum.inl (_, a), i) => Sum.inl (i, a)
    | (Sum.inr (_, a), j) => Sum.inr (j, a)
  left_inv := by rintro (⟨i, a⟩ | ⟨i, a⟩) <;> rfl
  right_inv := by
    rintro ⟨(⟨k, a⟩ | ⟨k, a⟩), i⟩ <;> simp [Fin.fin_one_eq_zero k]

/-- Block `i` of a separate-port sample, as a one-port sample. -/
def proj (i : Fin 2) (ω : LayerSample W .separate) : LayerSample W .oneBlockOnePort :=
  (fun _ => ω.1 i, fun _ _ => ω.2 i i)

/-- The one-block embedding of the old input. -/
abbrev emb (X : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ :=
  Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2

set_option linter.unusedSimpArgs false in
theorem layerMatrix_separate_eq (E : ℝ) (z : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .separate) :
    layerMatrix .separate E z (bd2 fun _ => X) ω =
      (blockDiagonal fun i => layerMatrix .oneBlockOnePort E z (emb X) (proj i ω)).submatrix
        (siteEquiv W) (siteEquiv W) := by
  ext s t
  rcases s with ⟨i, a⟩ | ⟨i, a⟩ <;> rcases t with ⟨k, c⟩ | ⟨k, c⟩ <;>
    simp only [submatrix_apply, siteEquiv, Equiv.coe_fn_mk, blockDiagonal_apply,
      layerMatrix, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.smul_apply, BlockBand.Internal.Contracts.Layers.blockDiag, bondMatrix, LayerShape.incident,
      conjTranspose_apply, bd2_apply, proj, one_apply, of_apply, Prod.mk.injEq]
  all_goals by_cases hik : i = k
  all_goals first
    | (subst hik; simp [BlockBand.Internal.Contracts.Layers.blockDiag, Fin.val_eq_val])
    | simp [hik, Ne.symm hik, Fin.val_eq_val, BlockBand.Internal.Contracts.Layers.blockDiag]

theorem layerResolvent_separate_eq (E : ℝ) (z : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .separate)
    (h : ∀ i, IsUnit (layerMatrix .oneBlockOnePort E z (emb X) (proj i ω)).det) :
    layerResolvent .separate E z (bd2 fun _ => X) ω =
      (blockDiagonal fun i => layerResolvent .oneBlockOnePort E z (emb X) (proj i ω)).submatrix
        (siteEquiv W) (siteEquiv W) := by
  unfold layerResolvent
  rw [layerMatrix_separate_eq, inv_submatrix_equiv]
  congr 1
  refine inv_eq_right_inv ?_
  rw [← blockDiagonal_mul]
  have : (fun i => layerMatrix .oneBlockOnePort E z (emb X) (proj i ω) *
      (layerMatrix .oneBlockOnePort E z (emb X) (proj i ω))⁻¹) = 1 := by
    funext i; exact mul_nonsing_inv _ (h i)
  rw [this, blockDiagonal_one]

/-!
## The law of one block
-/

theorem measurePreserving_proj (W : ℕ) (b : ℝ) (i : Fin 2) :
    MeasurePreserving (proj (W := W) i) (layerLaw W b .separate) (layerLaw W b .oneBlockOnePort) := by
  have := fun t => BlockBand.Layers.isProbabilityMeasure_gueMeasure W t
  set g := gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
  set n := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  have h1 : MeasurePreserving (fun f : Fin 2 → Matrix (Fin W) (Fin W) ℂ => fun _ : Fin 1 => f i)
      (Measure.pi fun _ : Fin 2 => g) (Measure.pi fun _ : Fin 1 => g) :=
    (MeasurePreserving.symm _ (measurePreserving_funUnique g (Fin 1))).comp
      (measurePreserving_eval (fun _ : Fin 2 => g) i)
  have h2a : MeasurePreserving (fun f : Fin 2 → Fin 2 → Matrix (Fin W) (Fin W) ℂ => f i i)
      (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => n) n :=
    (measurePreserving_eval (fun _ : Fin 2 => n) i).comp
      (measurePreserving_eval (fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => n) i)
  have h2b : MeasurePreserving (fun x : Matrix (Fin W) (Fin W) ℂ => fun _ : Fin 1 => fun _ : Fin 1 => x)
      n (Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 1 => n) :=
    (MeasurePreserving.symm _ (measurePreserving_funUnique (Measure.pi fun _ : Fin 1 => n)
      (Fin 1))).comp (MeasurePreserving.symm _ (measurePreserving_funUnique n (Fin 1)))
  exact h1.prod (h2b.comp h2a)

/-!
## The decoupled clock and the scalar distance
-/

theorem toBlocks12_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .separate)
    (h : ∀ i, IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E) (emb X) (proj i ω)).det) :
    (layerResolvent .separate E (boundaryZ b E) (bd2 fun _ => X) ω).toBlocks₁₂ =
      bd2 fun i => Matrix.of fun x y =>
        freshLayer b E X (proj i ω) (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y)) := by
  ext ⟨i, a⟩ ⟨k, c⟩
  rw [toBlocks₁₂, of_apply, layerResolvent_separate_eq _ _ _ _ h, bd2_apply]
  simp only [submatrix_apply, siteEquiv, Equiv.coe_fn_mk, blockDiagonal_apply, of_apply]
  rfl

theorem shift_eq (z : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - bd2 (fun _ => X) =
      bd2 fun _ => z • (1 : Matrix (Fin W) (Fin W) ℂ) - X := by
  ext ⟨i, a⟩ ⟨k, c⟩
  rw [Matrix.sub_apply, bd2_apply, bd2_apply, Matrix.smul_apply, one_apply]
  by_cases hik : i = k
  · subst hik; simp [one_apply]
  · simp [hik]

theorem bd2_isHermitian {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian) :
    (bd2 fun _ => X).IsHermitian := by
  unfold IsHermitian
  rw [bd2_conjTranspose, hX.eq]

/-- The separate-port clock of the embedded input is the one-port clock of block `0`. -/
theorem clock_eq (b E : ℝ) (X Y : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .separate)
    (h : ∀ i, IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E) (emb X) (proj i ω)).det) :
    (W : ℝ)⁻¹ * (((boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        bd2 (fun _ => X)) * (layerResolvent .separate E (boundaryZ b E) (bd2 fun _ => X)
          ω).toBlocks₁₂)ᴴ * ((sel W)ᴴ * Y * sel W) *
        ((boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
          bd2 (fun _ => X)) * (layerResolvent .separate E (boundaryZ b E) (bd2 fun _ => X)
            ω).toBlocks₁₂)).trace.re =
      clockT b E X Y (proj 0 ω) := by
  have hL : (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      bd2 (fun _ => X)) * (layerResolvent .separate E (boundaryZ b E) (bd2 fun _ => X)
        ω).toBlocks₁₂ = bd2 fun i => freshL b E X (proj i ω) := by
    rw [shift_eq, toBlocks12_eq b E X ω h, bd2_mul]
    rfl
  rw [hL]
  unfold clockT
  congr 2
  set L := bd2 fun i => freshL b E X (proj i ω)
  have h1 : Lᴴ * ((sel W)ᴴ * Y * sel W) * L = (sel W * L)ᴴ * Y * (sel W * L) := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [h1, sel_mul_bd2, conjTranspose_mul]
  have h2 : ((sel W)ᴴ * (freshL b E X (proj 0 ω))ᴴ * Y * (freshL b E X (proj 0 ω) * sel W)) =
      (sel W)ᴴ * ((freshL b E X (proj 0 ω))ᴴ * Y * freshL b E X (proj 0 ω)) * sel W := by
    simp only [Matrix.mul_assoc]
  rw [h2, trace_mul_comm, ← Matrix.mul_assoc, sel_mul_conjTranspose, Matrix.one_mul]

theorem trace_Y2 (Y : Matrix (Fin W) (Fin W) ℂ) : ((sel W)ᴴ * Y * sel W).trace = Y.trace := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, sel_mul_conjTranspose, Matrix.one_mul]

theorem matchedDistance_eq (b E : ℝ) (hb : b < 1) {κ : ℝ} (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian) :
    matchedDistance b E (bd2 fun _ => X) = jetDistance0 b E X := by
  have hz := (BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval hb hκ hE)
  have hzp : 0 < (boundaryZ b E).im := hz.1.trans_le hz.2
  have hR : (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      bd2 (fun _ => X))⁻¹ = bd2 fun _ => (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ := by
    rw [shift_eq, bd2_inv]
    intro _; exact ZeroEntranceProb.isUnit_resolvent hzp hX
  have hbt : ∀ j : Fin 2, blockTrace (bd2 fun _ =>
      (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹) j =
      (W : ℂ)⁻¹ * (passiveResolvent b E X).trace := by
    intro j
    simp only [blockTrace, bd2_apply, ite_true, passiveResolvent, trace, diag]
  unfold matchedDistance
  rw [hR, hbt, hbt, max_self]
  rfl

theorem measurable_clockT (b E : ℝ) (X Y : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (clockT b E X Y) := by
  have hL : Measurable (fun ω : OneEndedLayer W => freshL b E X ω) :=
    (ClockMixingProb.meas_freshL (W := W) b E).comp (f := fun ω : OneEndedLayer W => (X, ω))
      (measurable_const.prodMk measurable_id)
  have h := ClockMixingProb.meas_trace (ClockMixingProb.meas_mul
    (ClockMixingProb.meas_mul (ClockMixingProb.meas_conjTranspose hL)
      (measurable_const (a := Y))) hL)
  exact measurable_const.mul (Complex.measurable_re.comp h)

/-- Almost surely (both one-port layer matrices invertible), the separate-port clock of the
embedded input equals the one-port clock of block `0`. -/
theorem ae_clock_eq (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) {W : ℕ} (hW : 0 < W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) {E : ℝ} (hE : E ∈ bulkInterval κ) (Y : Matrix (Fin W) (Fin W) ℂ) :
    (fun ω => (W : ℝ)⁻¹ * (((boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        bd2 (fun _ => X)) * (layerResolvent .separate E (boundaryZ b E) (bd2 fun _ => X)
          ω).toBlocks₁₂)ᴴ * ((sel W)ᴴ * Y * sel W) *
        ((boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
          bd2 (fun _ => X)) * (layerResolvent .separate E (boundaryZ b E) (bd2 fun _ => X)
            ω).toBlocks₁₂)).trace.re) =ᵐ[layerLaw W b .separate]
      (clockT b E X Y) ∘ proj 0 := by
  have hz := BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (by linarith : b < 1) hκ hE
  have hzp : 0 < (boundaryZ b E).im := hz.1.trans_le hz.2
  obtain ⟨_ε₁, _C, _hε₁, _hC, hGA'⟩ := hGA b hb0 hb1 (boundaryZ b E).im ‖boundaryZ b E‖ hzp
  have hemb : (emb X).IsHermitian := ClockMixingAlg.physEmbed_isHermitian hX
  have hinv := fun i : Fin 2 => (measurePreserving_proj W b i).quasiMeasurePreserving.ae
    (hGA' W hW .oneBlockOnePort (emb X) hemb E (boundaryZ b E) le_rfl le_rfl).1
  filter_upwards [hinv 0, hinv 1] with ω h0 h1
  refine clock_eq b E X Y ω ?_
  intro i; fin_cases i
  · exact h0
  · exact h1

end Embed

open Embed in

/-- **The weighted-layer lemma for one block with one port** (`OnePortWeighted`), from
`WeightedLayerContract` and `GaussianAbsorptionContract`. -/
theorem onePortWeighted_of (hWL : WeightedLayerContract) (hGA : GaussianAbsorptionContract) :
    OnePortWeighted := by
  intro b hb0 hb1 κ hκ
  have hb1' : b < 1 := by linarith
  have hu0 : ∀ {W : ℕ} {Y : Matrix (Fin W) (Fin W) ℂ}, Y.PosSemidef → 0 ≤ clockU Y := by
    intro W Y hY
    unfold clockU
    exact mul_nonneg (by positivity) (ClockMixingAlg.trace_re_nonneg hY)
  have hu2 : ∀ {W : ℕ} (Y : Matrix (Fin W) (Fin W) ℂ),
      (W : ℝ)⁻¹ * ((sel W)ᴴ * Y * sel W).trace.re = clockU Y := by
    intro W Y; rw [trace_Y2]; rfl
  have hint : ∀ {W : ℕ} (E : ℝ) (X Y : Matrix (Fin W) (Fin W) ℂ),
      ∫ ω, clockT b E X Y ω ∂freshLaw W b =
        ∫ ω, clockT b E X Y (proj 0 ω) ∂layerLaw W b .separate := by
    intro W E X Y
    have hmp := measurePreserving_proj W b 0
    rw [show freshLaw W b = layerLaw W b .oneBlockOnePort from rfl, ← hmp.map_eq,
      integral_map hmp.measurable.aemeasurable
      (measurable_clockT b E X Y).aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · obtain ⟨dstar, C, W₀, hd, h⟩ := hWL.clockMean b hb0 hb1 κ hκ
    refine ⟨dstar, C, W₀, hd, ?_⟩
    intro W hW hW₀ X hX E hE hδ Y hY
    have hcm := h W hW hW₀ (bd2 fun _ => X) (bd2_isHermitian hX) E hE
      (by rw [matchedDistance_eq b E hb1' hκ hE hX]; exact hδ) ((sel W)ᴴ * Y * sel W)
      (hY.conjTranspose_mul_mul_same _)
    dsimp only at hcm
    obtain ⟨hI, hle⟩ := hcm
    have hae := ae_clock_eq hGA hb0 hb1 hκ hW hX hE Y
    have hmp := measurePreserving_proj W b 0
    refine ⟨?_, ?_⟩
    · exact (hmp.integrable_comp (measurable_clockT b E X Y).aestronglyMeasurable).mp
        (hI.congr hae)
    · rw [hint, show (fun ω => clockT b E X Y (proj 0 ω)) = clockT b E X Y ∘ proj 0 from rfl,
        ← integral_congr_ae hae]
      rw [matchedDistance_eq b E hb1' hκ hE hX, hu2] at hle
      exact hle
  · intro p hp
    obtain ⟨C₁, W₁, h₁⟩ := hWL.clockNoise b hb0 hb1 κ hκ p hp
    obtain ⟨C₂, W₂, h₂⟩ := hWL.unrestricted b hb0 hb1 κ hκ p hp
    refine ⟨max C₁ C₂, max W₁ W₂, ?_⟩
    intro W hW hWW X hX E hE Y hY
    have hcn := h₁ W hW ((le_max_left _ _).trans hWW) (bd2 fun _ => X) (bd2_isHermitian hX) E hE
      ((sel W)ᴴ * Y * sel W) (hY.conjTranspose_mul_mul_same _)
    have hun := h₂ W hW ((le_max_right _ _).trans hWW) (bd2 fun _ => X) (bd2_isHermitian hX) E
      hE ((sel W)ᴴ * Y * sel W) (hY.conjTranspose_mul_mul_same _)
    dsimp only at hcn hun
    rw [hu2] at hcn hun
    obtain ⟨hn1, hn2⟩ := hcn
    have hae := ae_clock_eq hGA hb0 hb1 hκ hW hX hE Y
    have hmp := measurePreserving_proj W b 0
    have hm := measurable_clockT b E X Y
    have hu := hu0 hY
    refine ⟨?_, ?_⟩
    · have heq : eLpNorm (fun ω => clockT b E X Y ω - ∫ ω', clockT b E X Y ω' ∂freshLaw W b)
          (ENNReal.ofReal p) (freshLaw W b) =
          eLpNorm ((fun ω => clockT b E X Y ω - ∫ ω', clockT b E X Y ω' ∂freshLaw W b) ∘ proj 0)
            (ENNReal.ofReal p) (layerLaw W b .separate) :=
        (eLpNorm_comp_measurePreserving (hm.sub measurable_const).aestronglyMeasurable hmp).symm
      rw [heq, hint]
      have hae' : ((fun ω => clockT b E X Y ω -
          ∫ ω', clockT b E X Y (proj 0 ω') ∂layerLaw W b .separate) ∘ proj 0) =ᵐ[layerLaw W b
            .separate] fun ω => (W : ℝ)⁻¹ * (((boundaryZ b E •
              (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - bd2 (fun _ => X)) *
              (layerResolvent .separate E (boundaryZ b E) (bd2 fun _ => X) ω).toBlocks₁₂)ᴴ *
              ((sel W)ᴴ * Y * sel W) * ((boundaryZ b E •
              (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - bd2 (fun _ => X)) *
              (layerResolvent .separate E (boundaryZ b E) (bd2 fun _ => X) ω).toBlocks₁₂)).trace.re -
            ∫ ω', (W : ℝ)⁻¹ * (((boundaryZ b E •
              (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - bd2 (fun _ => X)) *
              (layerResolvent .separate E (boundaryZ b E) (bd2 fun _ => X) ω').toBlocks₁₂)ᴴ *
              ((sel W)ᴴ * Y * sel W) * ((boundaryZ b E •
              (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - bd2 (fun _ => X)) *
              (layerResolvent .separate E (boundaryZ b E) (bd2 fun _ => X) ω').toBlocks₁₂)).trace.re
              ∂layerLaw W b .separate := by
        rw [integral_congr_ae hae]
        filter_upwards [hae] with ω hω
        simp only [Function.comp_apply] at hω ⊢
        rw [hω]
      rw [eLpNorm_congr_ae hae']
      refine hn1.trans (ENNReal.ofReal_le_ofReal (hn2.trans ?_))
      refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hu
    · rw [← eLpNorm_comp_measurePreserving hm.aestronglyMeasurable hmp,
        eLpNorm_congr_ae hae.symm]
      refine hun.trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hu

end OpenInputsProof

end BlockBand.Endpoints.Clock
