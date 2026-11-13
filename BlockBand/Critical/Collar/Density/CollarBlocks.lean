module

public import BlockBand.Critical.Collar.Density.BlockRankOne
public import BlockBand.Critical.Collar.Density.Statement
public import BlockBand.Layers.GinibreTails
public import BlockBand.Critical.Collar.Kernel.Collar

/-!
# The three-block collar resolvent bound 

*Law.* `collarLaw W b`: `A_0, A_1 ~ GUE_W(c/W)`, `G ~ GUE(c/W)` on `Fin 1 × Fin W`, bonds
`Gin(b/W)`, all independent; `c = 1 - 2b > 0`, `W ≥ 1`.
*Domain.* every Hermitian `X` (no norm bound), every real `e`, every `z` with `Im z > 0`, every
deterministic vector `v` on `LayerSite W .common`.

## Main results

* `embedVia f G`: a block `G` placed on the image of an injective `f : n → ι`;
  `lintegral_im_resolvent_embedVia_le` (block rank-one averaging along `f`).
* `collarMatrix_eq_add_embed_A`, `collarMatrix_eq_add_embed_G`: `ℋ_X` is the same matrix with one
  diagonal block set to zero plus that block embedded (all other entries conditioned on).
* `lintegral_im_resolvent_collar_le`: **three-block bound at positive height**
  `E_collar Im⟨v, (ℋ_X - z)⁻¹ v⟩ ≤ 3 √(π W/(2c)) ‖v‖²` (split `v` into its three block
  components, `im_quad_sum_le` with `k = 3`, then average each component over its own block).
  This is the `C_k √W` matrix spectral-density bound (`k = 3`) in resolvent form; the Cauchy-kernel
  passage to the density is the same as in `WeightedDensity.Global`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal ComplexConjugate

/-!
## Blocks along an injective map
-/

section Via

variable {ι n : Type} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

/-- The labelling `ι ≃ n ⊕ (ι \ range f)` of an injective `f : n → ι`. -/
def blockEquiv (f : n → ι) (hf : Function.Injective f) :
    ι ≃ n ⊕ {i : ι // i ∉ Set.range f} :=
  (Equiv.sumCompl (fun i : ι => i ∈ Set.range f)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective f hf).symm (Equiv.refl _))

omit [Fintype ι] [DecidableEq n] in
theorem blockEquiv_apply_self (f : n → ι) (hf : Function.Injective f) (a : n) :
    blockEquiv f hf (f a) = Sum.inl a := by
  simp only [blockEquiv, Equiv.trans_apply]
  rw [Equiv.sumCompl_symm_apply_of_pos (Set.mem_range_self a)]
  simp only [Equiv.sumCongr_apply, Sum.map_inl]
  congr 1
  exact (Equiv.ofInjective f hf).symm_apply_eq.mpr rfl

omit [Fintype ι] [DecidableEq n] in
theorem blockEquiv_apply_of_not_mem (f : n → ι) (hf : Function.Injective f) {i : ι}
    (hi : i ∉ Set.range f) : blockEquiv f hf i = Sum.inr ⟨i, hi⟩ := by
  simp only [blockEquiv, Equiv.trans_apply]
  rw [Equiv.sumCompl_symm_apply_of_neg hi]
  simp

/-- `G` placed on the image of `f` (zero elsewhere). -/
def embedVia (f : n → ι) (hf : Function.Injective f) (G : Matrix n n ℂ) : Matrix ι ι ℂ :=
  (embedBlock G {i : ι // i ∉ Set.range f}).submatrix (blockEquiv f hf) (blockEquiv f hf)

/-- `y` placed on the image of `f` (zero elsewhere). -/
def blockVec (f : n → ι) (hf : Function.Injective f) (y : n → ℂ) : ι → ℂ :=
  embedVec y {i : ι // i ∉ Set.range f} ∘ blockEquiv f hf

omit [Fintype ι] [DecidableEq n] in
theorem embedVia_apply_of_not_mem_left (f : n → ι) (hf : Function.Injective f)
    (G : Matrix n n ℂ) {i : ι} (hi : i ∉ Set.range f) (j : ι) : embedVia f hf G i j = 0 := by
  simp only [embedVia, submatrix_apply, blockEquiv_apply_of_not_mem f hf hi]
  rcases (blockEquiv f hf j) with b | b <;> rfl

omit [Fintype ι] [DecidableEq n] in
theorem embedVia_apply_of_not_mem_right (f : n → ι) (hf : Function.Injective f)
    (G : Matrix n n ℂ) (i : ι) {j : ι} (hj : j ∉ Set.range f) : embedVia f hf G i j = 0 := by
  simp only [embedVia, submatrix_apply, blockEquiv_apply_of_not_mem f hf hj]
  rcases (blockEquiv f hf i) with b | b <;> rfl

omit [Fintype ι] [DecidableEq n] in
theorem embedVia_apply_self (f : n → ι) (hf : Function.Injective f) (G : Matrix n n ℂ)
    (a b : n) : embedVia f hf G (f a) (f b) = G a b := by
  simp [embedVia, blockEquiv_apply_self]

omit [Fintype ι] [DecidableEq n] in
theorem blockVec_apply_self (f : n → ι) (hf : Function.Injective f) (y : n → ℂ) (a : n) :
    blockVec f hf y (f a) = y a := by
  simp [blockVec, blockEquiv_apply_self]

omit [Fintype ι] [DecidableEq n] in
theorem blockVec_apply_of_not_mem (f : n → ι) (hf : Function.Injective f) (y : n → ℂ) {i : ι}
    (hi : i ∉ Set.range f) : blockVec f hf y i = 0 := by
  simp [blockVec, blockEquiv_apply_of_not_mem f hf hi]

/-- **Block rank-one averaging along `f`.** Law `G ~ gueMeasure n t`, `t > 0`; every Hermitian
`H` on `ι` (all entries outside the block conditioned on), `Im z > 0`, `y : n → ℂ`:
`E_G Im⟨ŷ, (H + G_f - z)⁻¹ ŷ⟩ ≤ √(π/(2t)) ‖y‖²`, `ŷ = blockVec f y`, `G_f = embedVia f G`. -/
theorem lintegral_im_resolvent_embedVia_le (f : n → ι) (hf : Function.Injective f)
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {t : ℝ≥0} (ht : 0 < t) {z : ℂ} (hz : 0 < z.im)
    (y : n → ℂ) :
    ∫⁻ G, ENNReal.ofReal ((star (blockVec f hf y) ⬝ᵥ
        ((H + embedVia f hf G - z • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ blockVec f hf y)).im)
        ∂gueMeasure n t ≤
      ENNReal.ofReal (Real.sqrt (Real.pi / (2 * t)) * ∑ a, ‖y a‖ ^ 2) :=
  lintegral_im_resolvent_embed_le (m := {i : ι // i ∉ Set.range f}) (blockEquiv f hf) hH ht hz y

end Via

/-!
## Iterated integrals with one inner block
-/

section Fubini

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- If the inner integral over the first factor is `≤ K` for `ν`-a.e. second coordinate, so is the
total integral (`ν` a probability measure). -/
theorem lintegral_prod_le_of_ae_left {μ : Measure α} {ν : Measure β} [SFinite μ]
    [IsProbabilityMeasure ν] {f : α × β → ℝ≥0∞} (hf : Measurable f) {K : ℝ≥0∞}
    (h : ∀ᵐ y ∂ν, ∫⁻ x, f (x, y) ∂μ ≤ K) : ∫⁻ p, f p ∂(μ.prod ν) ≤ K := by
  rw [lintegral_prod_symm _ hf.aemeasurable]
  calc ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν ≤ ∫⁻ _, K ∂ν := lintegral_mono_ae h
    _ = K := by simp

/-- Mirror of `lintegral_prod_le_of_ae_left`: the inner integral is over the second factor. -/
theorem lintegral_prod_le_of_ae_right {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ]
    [SFinite ν] {f : α × β → ℝ≥0∞} (hf : Measurable f) {K : ℝ≥0∞}
    (h : ∀ᵐ x ∂μ, ∫⁻ y, f (x, y) ∂ν ≤ K) : ∫⁻ p, f p ∂(μ.prod ν) ≤ K := by
  rw [lintegral_prod _ hf.aemeasurable]
  calc ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ ≤ ∫⁻ _, K ∂μ := lintegral_mono_ae h
    _ = K := by simp

end Fubini

/-!
## The collar blocks
-/

section Collar

variable {W : ℕ}

/-- Position of the end diagonal `A_j` in `LayerSite W .common`. -/
def siteA (j : Fin 2) : Fin W → LayerSite W .common := fun a => Sum.inl (j, a)

theorem siteA_injective (j : Fin 2) : Function.Injective (siteA (W := W) j) := by
  intro a b h
  simpa [siteA] using h

/-- Position of the middle diagonal `G` in `LayerSite W .common`. -/
def siteG : PortSite W .common → LayerSite W .common := Sum.inr

theorem siteG_injective : Function.Injective (siteG (W := W)) := Sum.inr_injective

/-- The collar sample with end diagonal `j` set to zero. -/
def zeroA (j : Fin 2) (ω : CollarSample W) : CollarSample W :=
  ((Function.update ω.1.1 j 0, ω.1.2), ω.2)

/-- The collar sample with the middle diagonal set to zero. -/
def zeroG (ω : CollarSample W) : CollarSample W := (ω.1, 0)

theorem collarMatrix_eq_add_embed_A (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : CollarSample W) (j : Fin 2) :
    collarMatrix e X ω =
      collarMatrix e X (zeroA j ω) + embedVia (siteA j) (siteA_injective j) (ω.1.1 j) := by
  ext (⟨k, a⟩ | p) (⟨k', a'⟩ | p')
  · simp only [Matrix.add_apply, collarMatrix, zeroA, fromBlocks_apply₁₁, Matrix.sub_apply,
      BlockBand.Internal.Contracts.Layers.blockDiag]
    by_cases hk : k = j
    · subst hk
      by_cases hk' : k = k'
      · subst hk'
        rw [show (Sum.inl (k, a) : LayerSite W .common) = siteA k a from rfl,
          show (Sum.inl (k, a') : LayerSite W .common) = siteA k a' from rfl, embedVia_apply_self]
        simp
        ring
      · have hr' : (Sum.inl (k', a') : LayerSite W .common) ∉ Set.range (siteA k) := by
          rintro ⟨c, hc⟩
          simp only [siteA, Sum.inl.injEq, Prod.mk.injEq] at hc
          exact hk' hc.1
        rw [embedVia_apply_of_not_mem_right _ _ _ _ hr']
        simp [hk']
    · have hr : (Sum.inl (k, a) : LayerSite W .common) ∉ Set.range (siteA j) := by
        rintro ⟨c, hc⟩
        simp only [siteA, Sum.inl.injEq, Prod.mk.injEq] at hc
        exact hk hc.1.symm
      rw [embedVia_apply_of_not_mem_left _ _ _ hr]
      by_cases hk' : k = k'
      · subst hk'; simp [Function.update_of_ne hk]
      · simp [hk']
  · rw [Matrix.add_apply, embedVia_apply_of_not_mem_right _ _ _ _
      (by rintro ⟨c, hc⟩; simp [siteA] at hc)]
    simp [collarMatrix, zeroA]
  · rw [Matrix.add_apply, embedVia_apply_of_not_mem_left _ _ _
      (by rintro ⟨c, hc⟩; simp [siteA] at hc)]
    simp [collarMatrix, zeroA]
  · rw [Matrix.add_apply, embedVia_apply_of_not_mem_left _ _ _
      (by rintro ⟨c, hc⟩; simp [siteA] at hc)]
    simp [collarMatrix, zeroA]

theorem collarMatrix_eq_add_embed_G (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : CollarSample W) :
    collarMatrix e X ω = collarMatrix e X (zeroG ω) + embedVia siteG siteG_injective ω.2 := by
  ext (x | p) (x' | p')
  · rw [Matrix.add_apply, embedVia_apply_of_not_mem_left _ _ _
      (by rintro ⟨c, hc⟩; simp [siteG] at hc)]
    simp [collarMatrix, zeroG]
  · rw [Matrix.add_apply, embedVia_apply_of_not_mem_left _ _ _
      (by rintro ⟨c, hc⟩; simp [siteG] at hc)]
    simp [collarMatrix, zeroG]
  · rw [Matrix.add_apply, embedVia_apply_of_not_mem_right _ _ _ _
      (by rintro ⟨c, hc⟩; simp [siteG] at hc)]
    simp [collarMatrix, zeroG]
  · rw [Matrix.add_apply, show (Sum.inr p : LayerSite W .common) = siteG p from rfl,
      show (Sum.inr p' : LayerSite W .common) = siteG p' from rfl, embedVia_apply_self]
    simp [collarMatrix, zeroG, siteG]
    ring

/-- The three block components of a vector on `LayerSite W .common`. -/
theorem vec_eq_sum_blocks (v : LayerSite W .common → ℂ) :
    v = blockVec (siteA 0) (siteA_injective 0) (fun a => v (siteA 0 a)) +
      blockVec (siteA 1) (siteA_injective 1) (fun a => v (siteA 1 a)) +
      blockVec siteG siteG_injective (fun p => v (siteG p)) := by
  funext i
  rcases i with ⟨k, a⟩ | p
  · have hself : blockVec (siteA k) (siteA_injective k) (fun a => v (siteA k a))
        (Sum.inl (k, a)) = v (Sum.inl (k, a)) := blockVec_apply_self (siteA k) _ _ a
    have hother : ∀ j : Fin 2, j ≠ k → blockVec (siteA j) (siteA_injective j)
        (fun a => v (siteA j a)) (Sum.inl (k, a)) = 0 := by
      intro j hjk
      apply blockVec_apply_of_not_mem
      rintro ⟨c, hc⟩
      simp only [siteA, Sum.inl.injEq, Prod.mk.injEq] at hc
      exact hjk hc.1
    have hG : blockVec siteG siteG_injective (fun p => v (siteG p)) (Sum.inl (k, a)) = 0 :=
      blockVec_apply_of_not_mem _ _ _ (by rintro ⟨c, hc⟩; simp [siteG] at hc)
    obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> simp
    · simp only [Pi.add_apply, hself, hother 1 (by decide), hG, add_zero]
    · simp only [Pi.add_apply, hself, hother 0 (by decide), hG, add_zero, zero_add]
  · have hA : ∀ j : Fin 2, blockVec (siteA j) (siteA_injective j) (fun a => v (siteA j a))
        (Sum.inr p) = 0 := fun j =>
      blockVec_apply_of_not_mem _ _ _ (by rintro ⟨c, hc⟩; simp [siteA] at hc)
    have hG : blockVec siteG siteG_injective (fun p => v (siteG p)) (Sum.inr p) = v (Sum.inr p) :=
      blockVec_apply_self siteG siteG_injective _ p
    simp only [Pi.add_apply, hA, hG, zero_add]

/-- The collar sample with end diagonal `j` replaced by `M`. -/
def setA (j : Fin 2) (M : Matrix (Fin W) (Fin W) ℂ) (ω : CollarSample W) : CollarSample W :=
  ((Function.update ω.1.1 j M, ω.1.2), ω.2)

theorem zeroA_setA (j : Fin 2) (M : Matrix (Fin W) (Fin W) ℂ) (ω : CollarSample W) :
    zeroA j (setA j M ω) = zeroA j ω := by
  simp [zeroA, setA]

theorem setA_apply (j : Fin 2) (M : Matrix (Fin W) (Fin W) ℂ) (ω : CollarSample W) :
    (setA j M ω).1.1 j = M := by
  simp [setA]

/-- `ω ↦ ℋ_X(ω)` is measurable. -/
theorem measurable_collarMatrix (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable (collarMatrix e X) := by
  have hA : ∀ (k : Fin 2) (a c : Fin W),
      Measurable fun ω : CollarSample W => ω.1.1 k a c := fun k a c =>
    (Matrix.measurable_apply).comp ((measurable_pi_apply k).comp (measurable_fst.comp measurable_fst))
  have hB : ∀ (k : Fin 2) (l : Fin 1) (a c : Fin W),
      Measurable fun ω : CollarSample W => ω.1.2 k l a c := fun k l a c =>
    (Matrix.measurable_apply).comp ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp
      (measurable_snd.comp measurable_fst)))
  refine Measurable.of_eval_matrix _ fun i j => ?_
  rcases i with x | p <;> rcases j with y | q
  · simp only [collarMatrix, fromBlocks_apply₁₁, Matrix.sub_apply,
      BlockBand.Internal.Contracts.Layers.blockDiag]
    refine (Measurable.sub ?_ measurable_const).sub measurable_const
    split_ifs
    · exact hA _ _ _
    · exact measurable_const
  · simp only [collarMatrix, fromBlocks_apply₁₂, BlockBand.Internal.Contracts.Layers.bondMatrix]
    split_ifs
    · exact hB _ _ _ _
    · exact measurable_const
  · simp only [collarMatrix, fromBlocks_apply₂₁, conjTranspose_apply,
      BlockBand.Internal.Contracts.Layers.bondMatrix]
    split_ifs
    · exact Complex.continuous_conj.measurable.comp (hB _ _ _ _)
    · exact measurable_const
  · simp only [collarMatrix, fromBlocks_apply₂₂, Matrix.sub_apply]
    exact ((Matrix.measurable_apply).comp measurable_snd).sub measurable_const

/-- The block integrand `ω ↦ Im⟨y, (ℋ_X(ω) - z)⁻¹ y⟩` is measurable. -/
theorem measurable_collarForm (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (z : ℂ)
    (y : LayerSite W .common → ℂ) :
    Measurable fun ω : CollarSample W => ENNReal.ofReal ((star y ⬝ᵥ
      ((collarMatrix e X ω - z • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ))⁻¹ *ᵥ
        y)).im) := by
  have hsub : Measurable fun ω : CollarSample W => collarMatrix e X ω -
      z • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ) :=
    Measurable.of_eval_matrix _ fun i j =>
      ((Matrix.measurable_apply).comp (measurable_collarMatrix e X)).sub measurable_const
  have hinv := (BlockBand.Wegner.measurable_matrix_inv (n := LayerSite W .common)).comp hsub
  have hcont : Continuous fun A : Matrix (LayerSite W .common) (LayerSite W .common) ℂ =>
      (star y ⬝ᵥ (A *ᵥ y)).im :=
    Complex.continuous_im.comp (continuous_const.dotProduct
      (continuous_id.matrix_mulVec continuous_const))
  exact (hcont.measurable.comp hinv).ennreal_ofReal

/-- `collarLaw` is a probability measure. -/
instance isProbabilityMeasure_collarLaw (b : ℝ) : IsProbabilityMeasure (collarLaw W b) := by
  unfold collarLaw layerLaw
  infer_instance

/-- Integrating out one end diagonal: if for every sample whose other diagonals are Hermitian the
average of `g ∘ setA j · ω` over `A_j ~ GUE_W(c/W)` is `≤ K`, then `E_collar g ≤ K`. -/
theorem collar_lintegral_le_of_A (b : ℝ) (j : Fin 2) {g : CollarSample W → ℝ≥0∞}
    (hg : Measurable g) {K : ℝ≥0∞}
    (h : ∀ ω : CollarSample W, (∀ k, k ≠ j → (ω.1.1 k).IsHermitian) → ω.2.IsHermitian →
      ∫⁻ M, g (setA j M ω) ∂gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)) ≤ K) :
    ∫⁻ ω, g ω ∂collarLaw W b ≤ K := by
  set t := Real.toNNReal ((1 - 2 * b) / W)
  set μ := gueMeasure (Fin W) t
  set μA : Measure (Fin 2 → Matrix (Fin W) (Fin W) ℂ) := Measure.pi fun _ : Fin 2 => μ
  set μB : Measure (Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ) := Measure.pi fun _ : Fin 2 =>
    Measure.pi fun _ : Fin 1 => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  set μG := gueMeasure (PortSite W .common) t
  have hlaw : collarLaw W b = (μA.prod μB).prod μG := rfl
  rw [hlaw]
  refine lintegral_prod_le_of_ae_left hg ?_
  filter_upwards [ae_isHermitian_gueMeasure (ι := PortSite W .common) t] with G hG
  refine lintegral_prod_le_of_ae_left (hg.comp (measurable_id.prodMk measurable_const))
    (Filter.Eventually.of_forall fun B => ?_)
  have hmp := (measurePreserving_piFinTwo (fun _ : Fin 2 => μ)).symm
  have hF : Measurable fun A : Fin 2 → Matrix (Fin W) (Fin W) ℂ => g ((A, B), G) :=
    hg.comp ((measurable_id.prodMk measurable_const).prodMk measurable_const)
  change ∫⁻ A, (fun A : Fin 2 → Matrix (Fin W) (Fin W) ℂ => g ((A, B), G)) A ∂μA ≤ K
  rw [← hmp.lintegral_comp hF]
  have hpt : ∀ p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ,
      ((MeasurableEquiv.piFinTwo fun _ : Fin 2 => Matrix (Fin W) (Fin W) ℂ).symm p, B) =
        (setA j (if j = 0 then p.1 else p.2)
          (((MeasurableEquiv.piFinTwo fun _ : Fin 2 => Matrix (Fin W) (Fin W) ℂ).symm p, B), G)).1 := by
    intro p
    simp only [setA, Prod.mk.injEq, and_true]
    funext k
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self]
      fin_cases k <;> simp [MeasurableEquiv.piFinTwo, piFinTwoEquiv]
    · rw [Function.update_of_ne hk]
  have hHerm : ∀ p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ,
      p.1.IsHermitian → p.2.IsHermitian → ∀ k, k ≠ j →
      ((((MeasurableEquiv.piFinTwo fun _ : Fin 2 => Matrix (Fin W) (Fin W) ℂ).symm p, B), G).1.1
        k).IsHermitian := by
    intro p h1 h2 k _
    fin_cases k
    · simpa [MeasurableEquiv.piFinTwo, piFinTwoEquiv] using h1
    · simpa [MeasurableEquiv.piFinTwo, piFinTwoEquiv] using h2
  have hgp : Measurable fun p : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ =>
      g (((MeasurableEquiv.piFinTwo fun _ : Fin 2 => Matrix (Fin W) (Fin W) ℂ).symm p, B), G) :=
    hF.comp (MeasurableEquiv.measurable _)
  obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · refine lintegral_prod_le_of_ae_left hgp ?_
    filter_upwards [ae_isHermitian_gueMeasure (ι := Fin W) t] with A1 hA1
    have := h ((((MeasurableEquiv.piFinTwo fun _ : Fin 2 => Matrix (Fin W) (Fin W) ℂ).symm
      (0, A1), B), G)) (fun k hk => hHerm (0, A1) (by simp [IsHermitian]) hA1 k hk) hG
    refine le_of_eq_of_le (lintegral_congr fun A0 => ?_) this
    congr 1
    rw [Prod.ext_iff]
    refine ⟨?_, rfl⟩
    rw [hpt (A0, A1)]
    simp only [setA, Prod.mk.injEq, and_true, ite_true]
    funext k
    by_cases hk : k = 0
    · subst hk; simp
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      fin_cases k
      · exact absurd rfl hk
      · simp [MeasurableEquiv.piFinTwo, piFinTwoEquiv]
  · refine lintegral_prod_le_of_ae_right hgp ?_
    filter_upwards [ae_isHermitian_gueMeasure (ι := Fin W) t] with A0 hA0
    have := h ((((MeasurableEquiv.piFinTwo fun _ : Fin 2 => Matrix (Fin W) (Fin W) ℂ).symm
      (A0, 0), B), G)) (fun k hk => hHerm (A0, 0) hA0 (by simp [IsHermitian]) k hk) hG
    refine le_of_eq_of_le (lintegral_congr fun A1 => ?_) this
    congr 1
    rw [Prod.ext_iff]
    refine ⟨?_, rfl⟩
    rw [hpt (A0, A1)]
    simp only [setA, Prod.mk.injEq, and_true]
    funext k
    by_cases hk : k = 1
    · subst hk; simp
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      fin_cases k
      · simp [MeasurableEquiv.piFinTwo, piFinTwoEquiv]
      · exact absurd rfl hk

/-- Integrating out the middle diagonal: if for every sample with Hermitian end diagonals the
average of `g (ω.1, ·)` over `G ~ GUE(c/W)` is `≤ K`, then `E_collar g ≤ K`. -/
theorem collar_lintegral_le_of_G (b : ℝ) {g : CollarSample W → ℝ≥0∞} (hg : Measurable g)
    {K : ℝ≥0∞}
    (h : ∀ ω : CollarSample W, (∀ k, (ω.1.1 k).IsHermitian) →
      ∫⁻ M, g (ω.1, M) ∂gueMeasure (PortSite W .common) (Real.toNNReal ((1 - 2 * b) / W)) ≤ K) :
    ∫⁻ ω, g ω ∂collarLaw W b ≤ K := by
  have : IsProbabilityMeasure (layerLaw W b .common) := by unfold layerLaw; infer_instance
  refine lintegral_prod_le_of_ae_right hg ?_
  have hA : ∀ᵐ L ∂layerLaw W b .common, ∀ k, (L.1 k).IsHermitian := by
    have h1 : ∀ᵐ A ∂(Measure.pi fun _ : Fin 2 =>
        gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))), ∀ k, (A k).IsHermitian := by
      rw [ae_all_iff]
      intro k
      exact (Measure.quasiMeasurePreserving_eval _ k).ae
        (ae_isHermitian_gueMeasure (ι := Fin W) _)
    exact (Measure.quasiMeasurePreserving_fst).ae h1
  filter_upwards [hA] with L hL
  exact h (L, 0) hL

/-- **Three-block collar resolvent bound** (the `k = 3` case of the global
weighted-density bound) at positive height. Law
`collarLaw W b`, `b < 1/2`, `W ≥ 1` (block variance `t = c/W`, `c = 1 - 2b`). For every real `e`,
every Hermitian `X` (no norm bound), every `z` with `Im z > 0` and every deterministic `v`:
`E_collar Im⟨v, (ℋ_X - z)⁻¹ v⟩ ≤ 3 √(π/(2t)) ‖v‖²` (`= 3√(πW/(2c)) ‖v‖²`). The fresh bonds are
conditioned on; each block component of `v` is averaged over its own diagonal block. -/
theorem lintegral_im_resolvent_collar_le {b : ℝ} (hb : b < 1 / 2) (hW : 0 < W) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) {z : ℂ} (hz : 0 < z.im)
    (v : LayerSite W .common → ℂ) :
    ∫⁻ ω, ENNReal.ofReal ((star v ⬝ᵥ ((collarMatrix e X ω -
        z • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ))⁻¹ *ᵥ v)).im)
        ∂collarLaw W b ≤
      ENNReal.ofReal (3 * (Real.sqrt (Real.pi / (2 * Real.toNNReal ((1 - 2 * b) / W))) *
        ∑ i, ‖v i‖ ^ 2)) := by
  set t := Real.toNNReal ((1 - 2 * b) / W)
  have ht : 0 < t := Real.toNNReal_pos.2 (div_pos (by linarith) (by exact_mod_cast hW))
  set K := Real.sqrt (Real.pi / (2 * t))
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  set y0 : Fin W → ℂ := fun a => v (siteA 0 a)
  set y1 : Fin W → ℂ := fun a => v (siteA 1 a)
  set yG : PortSite W .common → ℂ := fun p => v (siteG p)
  set w : Fin 3 → LayerSite W .common → ℂ :=
    ![blockVec (siteA 0) (siteA_injective 0) y0, blockVec (siteA 1) (siteA_injective 1) y1,
      blockVec siteG siteG_injective yG]
  have hv : v = ∑ j, w j := by
    rw [Fin.sum_univ_three]
    exact vec_eq_sum_blocks v
  set R : CollarSample W → Matrix (LayerSite W .common) (LayerSite W .common) ℂ := fun ω =>
    (collarMatrix e X ω - z • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ))⁻¹
  set q : (LayerSite W .common → ℂ) → CollarSample W → ℝ≥0∞ := fun u ω =>
    ENNReal.ofReal ((star u ⬝ᵥ (R ω *ᵥ u)).im)
  have hq : ∀ u, Measurable (q u) := fun u => measurable_collarForm e X z u
  -- Hermitian almost surely
  have hHerm : ∀ ω : CollarSample W, (∀ k, (ω.1.1 k).IsHermitian) → ω.2.IsHermitian →
      (collarMatrix e X ω).IsHermitian := by
    intro ω hA hG
    have hD : (BlockBand.Internal.Contracts.Layers.blockDiag ω.1.1).IsHermitian :=
      BlockBand.Critical.Collar.Kernel.blockDiag_isHermitian' hA
    have hc : ((e : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian := by
      simp [IsHermitian, conjTranspose_smul]
    have hc' : ((e : ℂ) • (1 : Matrix (PortSite W .common) (PortSite W .common) ℂ)).IsHermitian := by
      simp [IsHermitian, conjTranspose_smul]
    exact IsHermitian.fromBlocks ((hD.sub hc).sub hX) rfl (hG.sub hc')
  have hae : ∀ᵐ ω ∂collarLaw W b, (∀ k, (ω.1.1 k).IsHermitian) ∧ ω.2.IsHermitian := by
    have hA : ∀ᵐ L ∂layerLaw W b .common, ∀ k, (L.1 k).IsHermitian := by
      have h1 : ∀ᵐ A ∂(Measure.pi fun _ : Fin 2 => gueMeasure (Fin W) t),
          ∀ k, (A k).IsHermitian := by
        rw [ae_all_iff]
        intro k
        exact (Measure.quasiMeasurePreserving_eval _ k).ae
          (ae_isHermitian_gueMeasure (ι := Fin W) _)
      exact (Measure.quasiMeasurePreserving_fst).ae h1
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := layerLaw W b .common)
      (ν := gueMeasure (PortSite W .common) t)).ae hA
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := layerLaw W b .common)
      (ν := gueMeasure (PortSite W .common) t)).ae (ae_isHermitian_gueMeasure (ι := PortSite W .common) t)
    filter_upwards [h1, h2] with ω h1 h2 using ⟨h1, h2⟩
  -- pointwise split
  have hsplit : ∀ᵐ ω ∂collarLaw W b, q v ω ≤ 3 * (q (w 0) ω + q (w 1) ω + q (w 2) ω) := by
    filter_upwards [hae] with ω hω
    have hH := hHerm ω hω.1 hω.2
    have h := im_quad_sum_le hH hz Finset.univ w
    rw [← hv, Finset.card_univ, Fintype.card_fin, Fin.sum_univ_three] at h
    have n0 := im_dotProduct_inv_mulVec_nonneg' hH hz (w 0)
    have n1 := im_dotProduct_inv_mulVec_nonneg' hH hz (w 1)
    have n2 := im_dotProduct_inv_mulVec_nonneg' hH hz (w 2)
    simp only [q, R]
    rw [← ENNReal.ofReal_add n0 n1, ← ENNReal.ofReal_add (add_nonneg n0 n1) n2,
      show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by push_cast at h; linarith)
  -- the three block averages
  have hblockA : ∀ (j : Fin 2) (y : Fin W → ℂ),
      ∫⁻ ω, q (blockVec (siteA j) (siteA_injective j) y) ω ∂collarLaw W b ≤
        ENNReal.ofReal (K * ∑ a, ‖y a‖ ^ 2) := by
    intro j y
    refine collar_lintegral_le_of_A b j (hq _) fun ω hA hG => ?_
    have hH0 : (collarMatrix e X (zeroA j ω)).IsHermitian := by
      refine hHerm _ (fun k => ?_) hG
      by_cases hk : k = j
      · subst hk; simp [zeroA, IsHermitian]
      · simpa [zeroA, Function.update_of_ne hk] using hA k hk
    have := lintegral_im_resolvent_embedVia_le (siteA j) (siteA_injective j) hH0 ht hz y
    refine le_of_eq_of_le (lintegral_congr fun M => ?_) this
    simp only [q, R]
    rw [collarMatrix_eq_add_embed_A e X (setA j M ω) j, zeroA_setA, setA_apply]
  have hblockG : ∀ y : PortSite W .common → ℂ,
      ∫⁻ ω, q (blockVec siteG siteG_injective y) ω ∂collarLaw W b ≤
        ENNReal.ofReal (K * ∑ a, ‖y a‖ ^ 2) := by
    intro y
    refine collar_lintegral_le_of_G b (hq _) fun ω hA => ?_
    have hH0 : (collarMatrix e X (zeroG (ω.1, 0))).IsHermitian :=
      hHerm _ hA (by simp [zeroG, IsHermitian])
    have := lintegral_im_resolvent_embedVia_le siteG siteG_injective hH0 ht hz y
    refine le_of_eq_of_le (lintegral_congr fun M => ?_) this
    simp only [q, R]
    rw [collarMatrix_eq_add_embed_G e X (ω.1, M)]
    rfl
  -- norms of the components
  have hnorm : ∑ a, ‖y0 a‖ ^ 2 + ∑ a, ‖y1 a‖ ^ 2 + ∑ p, ‖yG p‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
    conv_rhs => rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two]
    rfl
  calc ∫⁻ ω, q v ω ∂collarLaw W b
      ≤ ∫⁻ ω, 3 * (q (w 0) ω + q (w 1) ω + q (w 2) ω) ∂collarLaw W b := lintegral_mono_ae hsplit
    _ = 3 * (∫⁻ ω, q (w 0) ω ∂collarLaw W b + ∫⁻ ω, q (w 1) ω ∂collarLaw W b +
          ∫⁻ ω, q (w 2) ω ∂collarLaw W b) := by
        rw [lintegral_const_mul 3 (f := fun ω => q (w 0) ω + q (w 1) ω + q (w 2) ω)
            (((hq _).add (hq _)).add (hq _)),
          lintegral_add_left (f := fun ω => q (w 0) ω + q (w 1) ω) ((hq _).add (hq _)),
          lintegral_add_left (f := fun ω => q (w 0) ω) (hq _)]
    _ ≤ 3 * (ENNReal.ofReal (K * ∑ a, ‖y0 a‖ ^ 2) + ENNReal.ofReal (K * ∑ a, ‖y1 a‖ ^ 2) +
          ENNReal.ofReal (K * ∑ p, ‖yG p‖ ^ 2)) := by
        gcongr
        · exact hblockA 0 y0
        · exact hblockA 1 y1
        · exact hblockG yG
    _ = ENNReal.ofReal (3 * (K * ∑ i, ‖v i‖ ^ 2)) := by
        have h0 : 0 ≤ K * ∑ a, ‖y0 a‖ ^ 2 := mul_nonneg hK (Finset.sum_nonneg fun _ _ => by positivity)
        have h1 : 0 ≤ K * ∑ a, ‖y1 a‖ ^ 2 := mul_nonneg hK (Finset.sum_nonneg fun _ _ => by positivity)
        have h2 : 0 ≤ K * ∑ p, ‖yG p‖ ^ 2 := mul_nonneg hK (Finset.sum_nonneg fun _ _ => by positivity)
        rw [← ENNReal.ofReal_add h0 h1, ← ENNReal.ofReal_add (add_nonneg h0 h1) h2,
          show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp, ← ENNReal.ofReal_mul (by norm_num), ← hnorm]
        congr 1
        ring

end Collar

end BlockBand.Critical.Collar.Density
