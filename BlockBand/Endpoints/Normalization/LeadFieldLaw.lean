module

public import BlockBand.Endpoints.Normalization.LeadProfileField
public import BlockBand.Layers.RingDecomposition
public import BlockBand.Layers.ScalarRecursion
public import BlockBand.Layers.ResolventRowSum
public import BlockBand.Layers.MatchedScalar
public import BlockBand.Layers.LayerMeanBounds
public import BlockBand.Endpoints.Clock.LeadPortBlock

/-!
# `LeadFieldIdentificationContract`: the law and the almost-sure regularity

Facts internal to the proof of the physical lead-profile theorem, in its setting: remove block
`0`; its two neighbours form a common-port layer, the remaining `n-3` blocks the matched-lead
path.

**Statements proved here.**
* `leadFieldLaw_isBlockSplitting` (the hypothesis `hsplit` of
  `leadFieldIdentification_of_split_regular`): for every admissible `p`, model and block `k`,
  the lead law `(growthPathLaw W b ⊗ layerLaw W b .common).map (leadExterior p k)` is a one-block
  splitting law of block `k`.
* `leadFieldLaw_regular_ae` (the hypothesis `hreg`, the clause `regular_ae`): for every
  `-2 < e < 2`, the five matrices of `IsLeadRegular` are invertible almost surely under
  `growthPathLaw W b ⊗ layerLaw W b .common`.
* `leadFieldIdentification_holds : LeadFieldIdentificationContract` (all four clauses).

**Proof of the law.** No new characteristic-function computation is needed.
1. The law identification `Layers.rng_law_eq_map`: `model.law = rngLaw.map rngAssemble` (the
   ring as independent `GUE_W(c/W)` blocks and `Gin(b/W)` bonds), and the measure-preserving
   split `Layers.rng_mp_split k : rngLaw → layerLaw .common ⊗ pathLaw (n-3)`.
2. Deterministically, `H ↦ (H_R, C)` applied to `rngAssemble ω` is the lead exterior assembled
   from `(π, ℓ) = swap (rngSplit k ω)` (`LeadFieldLaw.splitMap_rngAssemble`): `leadPos` and
   `rngSiteEquiv` place the same blocks at the same sites (`LeadFieldLaw.leadPos_rngSiteEquiv`),
   and the entries agree by the `rng_entry_*` lemmas.
3. The length-`(n-3)` marginal of the near-end-grown path is `pathLaw`
   (`leadFieldLaw_growth_map_pathAt`, `n - 3 ≥ 1`; finite injective reindexing of an iid product
   and `Gin` invariance under `ᴴ`).
4. Hence the lead law equals `oneBlockPalmSplitLaw p k model = model.law.map splitMap`, which is a
   one-block splitting law (`oneBlockPalm_splitting_exists` with `blockSplitting_unique`).

**Proof of the regularity.** Pull back along the measure-preserving
`x ↦ (x.2, pathAt x.1) : growthPathLaw ⊗ layerLaw → layerLaw ⊗ pathLaw` the almost-sure events
`rng_ae_invertible` (`H_path - e` and `A - e - X` invertible; Hermitian GUE blocks).
Deterministically on that event: `det(H_R - e) = det(H_path - e) det(A - e - X)` (Schur);
`z₀ - Σ` and `z_b - X` are invertible because `Σ = B*(A - e - X)⁻¹B` and `X` are Hermitian and
`Im z₀, Im z_b > 0` for `|e| < 2` (`Layers.resolvent_det_ne_zero`).

Measure: `growthPathLaw p.W p.b ⊗ layerLaw p.W p.b .common` and the exact physical law
`model.law`; every admissible `Parameters`, model, block `k` and `e ∈ (-2, 2)`; exact
finite-dimensional identities (no norm, limit or uniformity). No contract is assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile
open scoped ENNReal NNReal ComplexConjugate Matrix

namespace LeadFieldLaw

/-!
## 1. The length-`r` marginal of the near-end-grown path
-/

/-- A finite injective reindexing of an iid infinite product is the finite iid product. -/
theorem infinitePi_map_reindex {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {κ ι : Type*} [Fintype ι] (e : ι → κ) (he : Function.Injective e) :
    (Measure.infinitePi fun _ : κ => μ).map (fun ω i => ω (e i)) =
      Measure.pi fun _ : ι => μ := by
  classical
  have hm : Measurable fun (ω : κ → X) (i : ι) => ω (e i) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  let t : κ → Set X := Function.extend e s fun _ => Set.univ
  have ht : ∀ i, t (e i) = s i := fun i => he.extend_apply _ _ _
  have htm : ∀ k, MeasurableSet (t k) := by
    intro k
    by_cases hk : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := hk; rw [ht]; exact hs i
    · simp only [t, Function.extend_apply' _ _ _ hk]; exact MeasurableSet.univ
  have hpre : (fun (ω : κ → X) (i : ι) => ω (e i)) ⁻¹' Set.univ.pi s =
      Set.pi ((Finset.univ.map ⟨e, he⟩ : Finset κ) : Set κ) t := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_map,
      Finset.coe_univ, Set.image_univ, Set.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro h _ ⟨i, rfl⟩; rw [ht]; exact h i (Set.mem_univ _)
    · intro h i _; rw [← ht]; exact h _ ⟨i, rfl⟩
  rw [hpre, Measure.infinitePi_pi _ (fun k _ => htm k), Finset.prod_map]
  simp only [Function.Embedding.coeFn_mk, ht]

theorem mp_reindex {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {κ ι : Type*} [Fintype ι] (e : ι → κ) (he : Function.Injective e) :
    MeasurePreserving (fun (ω : κ → X) (i : ι) => ω (e i))
      (Measure.infinitePi fun _ : κ => μ) (Measure.pi fun _ : ι => μ) :=
  ⟨Measurable.of_eval fun _ => measurable_pi_apply _, infinitePi_map_reindex μ e he⟩

/-- Index map of the bonds of the length-`r` path into the growth sequence: internal bond `i`
is `B_{r-1-i}`, near port `B_r`, far port `B_0`. -/
def bondIndex (r : ℕ) : Fin (r - 1) ⊕ Fin 2 → ℕ
  | Sum.inl i => r - 1 - i.val
  | Sum.inr j => if j = 0 then r else 0

theorem bondIndex_injective {r : ℕ} (hr : 1 ≤ r) : Function.Injective (bondIndex r) := by
  rintro (i | i) (j | j) h <;> simp only [bondIndex] at h
  · have := i.isLt; have := j.isLt
    exact congrArg Sum.inl (Fin.ext (by omega))
  · have := i.isLt
    fin_cases j <;> simp at h <;> omega
  · have := j.isLt
    fin_cases i <;> simp at h <;> omega
  · fin_cases i <;> fin_cases j <;> simp_all
    all_goals omega

theorem blockIndex_injective (r : ℕ) : Function.Injective fun i : Fin r => r - 1 - i.val := by
  intro i j h
  have := i.isLt; have := j.isLt
  exact Fin.ext (by simp only at h; omega)

instance isProbabilityMeasure_growthPathLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (growthPathLaw W b) := by
  unfold growthPathLaw; infer_instance

/-- `pathAt W r` is measure preserving from `growthPathLaw W b` to `pathLaw W r b`, `r ≥ 1`. -/
theorem mp_pathAt (W : ℕ) (b : ℝ) {r : ℕ} (hr : 1 ≤ r) :
    MeasurePreserving (pathAt W r) (growthPathLaw W b) (pathLaw W r b) := by
  set μA := gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
  set μB := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  have hA : MeasurePreserving (fun (a : ℕ → Matrix (Fin W) (Fin W) ℂ) (i : Fin r) =>
      a (r - 1 - i.val)) (Measure.infinitePi fun _ : ℕ => μA) (Measure.pi fun _ : Fin r => μA) :=
    mp_reindex μA _ (blockIndex_injective r)
  have hB0 := mp_reindex μB (bondIndex r) (bondIndex_injective hr)
  have hB1 := measurePreserving_sumPiEquivProdPi (fun _ : Fin (r - 1) ⊕ Fin 2 => μB)
  have hct : MeasurePreserving (fun (v : Fin (r - 1) → Matrix (Fin W) (Fin W) ℂ) i => (v i)ᴴ)
      (Measure.pi fun _ : Fin (r - 1) => μB) (Measure.pi fun _ : Fin (r - 1) => μB) :=
    measurePreserving_pi _ _ fun _ => BlockBand.Layers.pg_mp_conjTranspose_ginibre _
  have hB2 := hct.prod (MeasurePreserving.id (Measure.pi fun _ : Fin 2 => μB))
  have hB := (hB2.comp hB1).comp hB0
  have hAll := hA.prod hB
  have hfun : pathAt W r = Prod.map
      (fun (a : ℕ → Matrix (Fin W) (Fin W) ℂ) (i : Fin r) => a (r - 1 - i.val))
      ((Prod.map (fun (v : Fin (r - 1) → Matrix (Fin W) (Fin W) ℂ) i => (v i)ᴴ) id ∘
        MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (r - 1) ⊕ Fin 2 =>
          Matrix (Fin W) (Fin W) ℂ)) ∘
        fun (ω : ℕ → Matrix (Fin W) (Fin W) ℂ) j => ω (bondIndex r j)) := by
    funext ω
    simp only [pathAt, Prod.map, Function.comp, MeasurableEquiv.sumPiEquivProdPi,
      MeasurableEquiv.coe_mk, Equiv.sumPiEquivProdPi_apply, id, bondIndex]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext j
    fin_cases j <;> rfl
  rw [hfun]
  exact hAll

end LeadFieldLaw

/-- **The length-`r` marginal of the near-end-grown path** (`r ≥ 1`):
`(growthPathLaw W b).map (pathAt W r) = pathLaw W r b`. -/
theorem leadFieldLaw_growth_map_pathAt (W : ℕ) (b : ℝ) {r : ℕ} (hr : 1 ≤ r) :
    (growthPathLaw W b).map (pathAt W r) = pathLaw W r b :=
  (LeadFieldLaw.mp_pathAt W b hr).map_eq

namespace LeadFieldLaw

/-!
## 2. The lead exterior as a function of a path sample
-/

variable (p : Parameters) (k : ZMod p.n)

/-- `leadExterior`, with the path given as a `PathSample` of length `n - 3`. -/
def leadExteriorOfPath (x : PathSample p.W (p.n - 3) × LayerSample p.W .common) :
    BlockState p k :=
  (fun a c => Matrix.fromBlocks (pathMatrix x.1) (pathPortCoupling x.1) (pathPortCoupling x.1)ᴴ
      (blockDiag x.2.1) (leadPos p k a) (leadPos p k c),
   fun a y => leadExteriorCoupling p x.2 (leadPos p k a) ((0 : Fin 1), y.1.2))

theorem leadExterior_eq_ofPath :
    leadExterior p k = leadExteriorOfPath p k ∘ Prod.map (pathAt p.W (p.n - 3)) id := rfl

theorem measurable_leadExteriorOfPath : Measurable (leadExteriorOfPath p k) := by
  have hP : Measurable (fun x : PathSample p.W (p.n - 3) × LayerSample p.W .common =>
      pathMatrix x.1) := (BlockBand.Layers.measurable_pathMatrix _ _).comp measurable_fst
  have hQ : Measurable (fun x : PathSample p.W (p.n - 3) × LayerSample p.W .common =>
      pathPortCoupling x.1) := (BlockBand.Layers.measurable_pathPortCoupling _ _).comp measurable_fst
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun c => ?_
    generalize leadPos p k a = u
    generalize leadPos p k c = v
    rcases u with i | i <;> rcases v with j | j
    · simp only [fromBlocks_apply₁₁]
      exact BlockBand.Layers.pg_entry hP i j
    · simp only [fromBlocks_apply₁₂]
      exact BlockBand.Layers.pg_entry hQ i j
    · simp only [fromBlocks_apply₂₁, conjTranspose_apply]
      exact continuous_star.measurable.comp (BlockBand.Layers.pg_entry hQ j i)
    · simp only [fromBlocks_apply₂₂, Internal.Contracts.Layers.blockDiag]
      split_ifs
      · fun_prop
      · exact measurable_const
  · refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun y => ?_
    generalize leadPos p k a = u
    rcases u with i | i
    · simp only [leadExteriorCoupling]
      exact measurable_const
    · simp only [leadExteriorCoupling, bondMatrix, LayerShape.incident, ite_true]
      fun_prop

/-!
## 3. The ring split and the lead positions agree
-/

open BlockBand.Layers (rngLaw rngAssemble rngSplit rngSiteEquiv rngBlk rngLayerOff) in
theorem leadPos_rngSiteEquiv (u : (Fin 2 × Fin p.W) ⊕ (Fin (p.n - 3) × Fin p.W)) :
    leadPos p k (rngSiteEquiv k u) = Equiv.sumComm _ _ u := by
  have h4 := p.n_ge_four
  rcases u with ⟨a, i⟩ | ⟨j, i⟩
  · have hs : (rngSiteEquiv k (.inl (a, i))).1 = (rngBlk k (rngLayerOff p a), i) :=
      BlockBand.Layers.rngSiteEquiv_inl k a i
    have hv : ((rngSiteEquiv k (.inl (a, i))).1.1 - k).val = rngLayerOff p a := by
      rw [hs]
      simp only [rngBlk, add_sub_cancel_left]
      exact ZMod.val_cast_of_lt (BlockBand.Layers.rngOff_lt (p := p) (.inl a))
    have hi : (rngSiteEquiv k (.inl (a, i))).1.2 = i := by rw [hs]
    unfold leadPos
    simp only [hv, hi, Equiv.sumComm_apply, Sum.swap_inl]
    rcases BlockBand.Layers.rng_fin2_cases a with rfl | rfl
    · simp [BlockBand.Layers.rngLayerOff_zero]
    · simp only [BlockBand.Layers.rngLayerOff_one]
      have : ¬ (p.n - 1 = 1) := by omega
      simp [this]
  · have hs : (rngSiteEquiv k (.inr (j, i))).1 = (rngBlk k (j.val + 2), i) :=
      BlockBand.Layers.rngSiteEquiv_inr k j i
    have hj := j.isLt
    have hv : ((rngSiteEquiv k (.inr (j, i))).1.1 - k).val = j.val + 2 := by
      rw [hs]
      simp only [rngBlk, add_sub_cancel_left]
      exact ZMod.val_cast_of_lt (by omega)
    have hi : (rngSiteEquiv k (.inr (j, i))).1.2 = i := by rw [hs]
    unfold leadPos
    simp only [hv, hi, Equiv.sumComm_apply, Sum.swap_inr]
    have e1 : ¬ (j.val + 2 = 1) := by omega
    have e2 : ¬ (j.val + 2 = p.n - 1) := by omega
    simp only [e1, e2, ite_false, Sum.inl.injEq, Prod.mk.injEq, and_true]
    exact Fin.ext (by simp only; omega)

open BlockBand.Layers (rngLaw rngAssemble rngSplit rngSiteEquiv rngBlk rngLayerOff) in
/-- **Deterministic identification**: `H ↦ (H_R, C)` of the assembled ring is the lead exterior of
`swap (rngSplit k ω)`. -/
theorem splitMap_rngAssemble (ω : BlockBand.Layers.RngSample p) :
    oneBlockPalmSplitMap p k (rngAssemble p ω) =
      leadExteriorOfPath p k ((rngSplit k ω).2, (rngSplit k ω).1) := by
  refine Prod.ext ?_ ?_
  · funext a c
    obtain ⟨u, rfl⟩ := (rngSiteEquiv k).surjective a
    obtain ⟨v, rfl⟩ := (rngSiteEquiv k).surjective c
    simp only [oneBlockPalmSplitMap, leadExteriorOfPath, leadPos_rngSiteEquiv]
    rcases u with ⟨a, i⟩ | ⟨j, i⟩ <;> rcases v with ⟨a', i'⟩ | ⟨j', i'⟩
    · rw [BlockBand.Layers.rngSiteEquiv_inl, BlockBand.Layers.rngSiteEquiv_inl]
      simp only [Equiv.sumComm_apply, Sum.swap_inl, fromBlocks_apply₂₂]
      exact BlockBand.Layers.rng_entry_layer_layer ω k a a' i i'
    · rw [BlockBand.Layers.rngSiteEquiv_inl, BlockBand.Layers.rngSiteEquiv_inr]
      simp only [Equiv.sumComm_apply, Sum.swap_inl, Sum.swap_inr, fromBlocks_apply₂₁]
      exact BlockBand.Layers.rng_entry_layer_path ω k a j' i i'
    · rw [BlockBand.Layers.rngSiteEquiv_inr, BlockBand.Layers.rngSiteEquiv_inl]
      simp only [Equiv.sumComm_apply, Sum.swap_inl, Sum.swap_inr, fromBlocks_apply₁₂]
      exact BlockBand.Layers.rng_entry_path_layer ω k j a' i i'
    · rw [BlockBand.Layers.rngSiteEquiv_inr, BlockBand.Layers.rngSiteEquiv_inr]
      simp only [Equiv.sumComm_apply, Sum.swap_inr, fromBlocks_apply₁₁]
      exact BlockBand.Layers.rng_entry_path_path ω k j j' i i'
  · funext a y
    obtain ⟨u, rfl⟩ := (rngSiteEquiv k).surjective a
    have hy : y.1 = (rngBlk k 0, y.1.2) := by
      rw [BlockBand.Layers.rngBlk_zero]; exact Prod.ext y.2 rfl
    simp only [oneBlockPalmSplitMap, leadExteriorOfPath, leadPos_rngSiteEquiv]
    rw [hy]
    rcases u with ⟨a, i⟩ | ⟨j, i⟩
    · rw [BlockBand.Layers.rngSiteEquiv_inl]
      exact BlockBand.Layers.rng_entry_layer_port ω k a ((0 : Fin 1), y.1.2) i
    · rw [BlockBand.Layers.rngSiteEquiv_inr]
      exact BlockBand.Layers.rng_entry_path_port ω k j ((0 : Fin 1), y.1.2) i

end LeadFieldLaw

/-!
## 4. The lead law is a one-block splitting law
-/

section Split

variable (p : Parameters) (k : ZMod p.n)

/-- **The lead law is the one-block splitting law** `model.law.map (H ↦ (H_R, C))`. -/
theorem leadFieldLaw_eq_oneBlockPalmSplitLaw (model : p.GaussianRingModel) :
    ((growthPathLaw p.W p.b).prod (layerLaw p.W p.b .common)).map (leadExterior p k) =
      oneBlockPalmSplitLaw p k model := by
  have hr : 1 ≤ p.n - 3 := by have := p.n_ge_four; omega
  have hLE := LeadFieldLaw.measurable_leadExteriorOfPath p k
  have hpa := (LeadFieldLaw.mp_pathAt p.W p.b hr)
  have h1 : ((growthPathLaw p.W p.b).prod (layerLaw p.W p.b .common)).map (leadExterior p k) =
      ((pathLaw p.W (p.n - 3) p.b).prod (layerLaw p.W p.b .common)).map
        (LeadFieldLaw.leadExteriorOfPath p k) := by
    rw [LeadFieldLaw.leadExterior_eq_ofPath,
      ← Measure.map_map hLE (hpa.measurable.prodMap measurable_id),
      ← Measure.map_prod_map _ _ hpa.measurable measurable_id, hpa.map_eq, Measure.map_id]
  have hsp := BlockBand.Layers.rng_mp_split (p := p) k
  have hg : oneBlockPalmSplitMap p k ∘ BlockBand.Layers.rngAssemble p =
      LeadFieldLaw.leadExteriorOfPath p k ∘ Prod.swap ∘ BlockBand.Layers.rngSplit k := by
    funext ω; exact LeadFieldLaw.splitMap_rngAssemble p k ω
  unfold oneBlockPalmSplitLaw
  rw [BlockBand.Layers.rng_law_eq_map model, Measure.map_map (oneBlockPalm_measurable_splitMap p k)
    BlockBand.Layers.rng_measurable_assemble, hg,
    ← Measure.map_map hLE (measurable_swap.comp hsp.measurable),
    ← Measure.map_map measurable_swap hsp.measurable, hsp.map_eq, Measure.prod_swap, h1]

end Split

/-- **`hsplit`** of `leadFieldIdentification_of_split_regular`: the lead law
`(growthPathLaw W b ⊗ layerLaw W b .common).map (leadExterior p k)` is a one-block splitting law
of block `k`, for every admissible `p`, model and `k`. -/
theorem leadFieldLaw_isBlockSplitting : ∀ (p : Parameters) (model : p.GaussianRingModel)
    (k : ZMod p.n), IsBlockSplitting p k model
      (((growthPathLaw p.W p.b).prod (layerLaw p.W p.b .common)).map (leadExterior p k)) := by
  intro p model k
  rw [leadFieldLaw_eq_oneBlockPalmSplitLaw p k model]
  obtain ⟨Pω, h⟩ := oneBlockPalm_splitting_exists p model k
  rwa [blockSplitting_unique p k model Pω h] at h

/-!
## 5. Almost-sure regularity
-/

namespace LeadFieldLaw

variable (p : Parameters) (k : ZMod p.n)

/-- `Im a < 0` for `|e| < 2`; hence `Im z₀ > 0` and `Im z_b > 0` (`b < 1/2`). -/
theorem im_matchedA_neg {e : ℝ} (he : |e| < 2) : (matchedA e).im < 0 := by
  have h4 : 0 < 4 - e ^ 2 := by
    have : e ^ 2 < 2 ^ 2 := by
      rw [← sq_abs]; exact pow_lt_pow_left₀ he (abs_nonneg e) two_ne_zero
    linarith
  have : 0 < Real.sqrt (4 - e ^ 2) := Real.sqrt_pos.mpr h4
  simp only [matchedA]
  linarith

theorem commonZ_im_pos {e : ℝ} (he : |e| < 2) : 0 < (commonZ p.b e).im := by
  rw [BlockBand.Layers.commonZ_im he.le]
  have := im_matchedA_neg he
  have := p.b_lt_half
  nlinarith

theorem boundaryZ_im_pos {e : ℝ} (he : |e| < 2) : 0 < (boundaryZ p.b e).im := by
  rw [BlockBand.Layers.boundaryZ_im he.le]
  have := im_matchedA_neg he
  have := p.b_lt_half
  nlinarith

theorem smul_one_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ℝ) :
    ((e : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

/-- **Deterministic regularity**: if `H_path - e` and `A - e - X` are invertible, the path
matrix and the fresh blocks are Hermitian and `|e| < 2`, then the five matrices of
`IsLeadRegular` are invertible. -/
theorem isLeadRegular_of (e : ℝ) (he : |e| < 2) (x : GrowthPath p.W × LayerSample p.W .common)
    (h1 : (leadP p e x).det ≠ 0) (h2 : (leadS2 p e x).det ≠ 0)
    (hH : (pathMatrix (pathAt p.W (p.n - 3) x.1)).IsHermitian)
    (hA : ∀ j, (x.2.1 j).IsHermitian) : IsLeadRegular p k e x := by
  have hX : (leadSchur e p.W (p.n - 3) x.1).IsHermitian :=
    BlockBand.Endpoints.Clock.leadSchur_isHermitian e p.W (p.n - 3) x.1 hH
  have hS2 : (leadS2 p e x).IsHermitian :=
    ((BlockBand.Layers.blockDiag_isHermitian hA).sub (smul_one_isHermitian e)).sub hX
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · rw [leadExterior_fst_sub, det_submatrix_equiv_self, leadExteriorMatrix_sub]
    let _i := invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr h1)
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
    exact mul_ne_zero h1 h2
  · rw [blockShifted_leadExterior p k e x h1 h2, det_submatrix_equiv_self]
    exact BlockBand.Layers.resolvent_det_ne_zero (leadSigma p e x)
      (isHermitian_conjTranspose_mul_mul _ hS2.inv) _ (commonZ_im_pos p he)
  · exact BlockBand.Layers.resolvent_det_ne_zero _ hX _ (boundaryZ_im_pos p he)

/-- `x ↦ (x.2, pathAt x.1)` is measure preserving onto `layerLaw ⊗ pathLaw (n-3)`. -/
theorem mp_layerPath :
    MeasurePreserving (fun x : GrowthPath p.W × LayerSample p.W .common =>
        (x.2, pathAt p.W (p.n - 3) x.1))
      ((growthPathLaw p.W p.b).prod (layerLaw p.W p.b .common))
      ((layerLaw p.W p.b .common).prod (pathLaw p.W (p.n - 3) p.b)) := by
  have hr : 1 ≤ p.n - 3 := by have := p.n_ge_four; omega
  exact (Measure.measurePreserving_swap).comp
    ((mp_pathAt p.W p.b hr).prod (MeasurePreserving.id (layerLaw p.W p.b .common)))

/-- The almost-sure event on `layerLaw ⊗ pathLaw`. -/
theorem ae_layerPath (e : ℝ) :
    ∀ᵐ y : LayerSample p.W .common × PathSample p.W (p.n - 3)
        ∂((layerLaw p.W p.b .common).prod (pathLaw p.W (p.n - 3) p.b)),
      IsUnit (pathMatrix y.2 - (e : ℂ) • 1).det ∧
        IsUnit (Internal.Contracts.Layers.blockDiag y.1.1 - (e : ℂ) • 1 - pathSchur e y.2).det ∧
        (pathMatrix y.2).IsHermitian ∧ ∀ j, (y.1.1 j).IsHermitian := by
  have hP1 := BlockBand.Layers.pg_isProbabilityMeasure_pathLaw p.W (p.n - 3) p.b
  have hL1 := BlockBand.Layers.rng_isProbabilityMeasure_layerLaw_common p.W p.b
  have hP2 : SFinite (pathLaw p.W (p.n - 3) p.b) := by
    exact inferInstance
  have hL2 : SFinite (layerLaw p.W p.b .common) := by
    exact inferInstance
  have h1 := BlockBand.Layers.rng_ae_invertible (W := p.W) (r := p.n - 3) p.b_lt_half e
  have hpath : ∀ᵐ π ∂pathLaw p.W (p.n - 3) p.b, (pathMatrix π).IsHermitian := by
    have hb := BlockBand.Layers.ae_blocks_isHermitian (p.n - 3) p.W
      (Real.toNNReal ((1 - 2 * p.b) / p.W))
    unfold pathLaw
    filter_upwards [(Measure.quasiMeasurePreserving_fst).ae hb] with π hπ
    exact BlockBand.Layers.srec_pathMatrix_isHermitian π hπ
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := layerLaw p.W p.b .common)
    (ν := pathLaw p.W (p.n - 3) p.b)).ae hpath
  have h3 := (Measure.quasiMeasurePreserving_fst (μ := layerLaw p.W p.b .common)
    (ν := pathLaw p.W (p.n - 3) p.b)).ae
      (BlockBand.Layers.lct_ae_blocks_isHermitian p.W p.b .common)
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  exact ⟨hy1.1, hy1.2, hy2, hy3⟩

end LeadFieldLaw

/-- **`hreg`** of `leadFieldIdentification_of_split_regular`, i.e. the clause `regular_ae` of
`LeadFieldIdentificationContract`: for every admissible `p`, block `k` and bulk energy
`-2 < e < 2`, the five matrices `H_path - e`, `A - e - X`, `H_R - e`, `z₀ - Σ`, `z_b - X` are
invertible for almost every sample of `growthPathLaw W b ⊗ layerLaw W b .common`. -/
theorem leadFieldLaw_regular_ae : ∀ (p : Parameters) (k : ZMod p.n) (e : ℝ), -2 < e → e < 2 →
    ∀ᵐ x ∂((growthPathLaw p.W p.b).prod (layerLaw p.W p.b .common)), IsLeadRegular p k e x := by
  intro p k e he1 he2
  have he : |e| < 2 := abs_lt.mpr ⟨he1, he2⟩
  filter_upwards [(LeadFieldLaw.mp_layerPath p).quasiMeasurePreserving.ae
    (LeadFieldLaw.ae_layerPath p e)] with x hx
  obtain ⟨h1, h2, hH, hA⟩ := hx
  exact LeadFieldLaw.isLeadRegular_of p k e he x (isUnit_iff_ne_zero.mp h1)
    (isUnit_iff_ne_zero.mp h2) hH hA

/-- **`LeadFieldIdentificationContract`**, all four clauses `law`, `regular_ae`, `identity`,
`covariance`. Assembled from `leadFieldIdentification_of_split_regular` with
`leadFieldLaw_isBlockSplitting` and `leadFieldLaw_regular_ae`. No extra hypothesis. -/
theorem leadFieldIdentification_holds : LeadFieldIdentificationContract :=
  leadFieldIdentification_of_split_regular leadFieldLaw_isBlockSplitting leadFieldLaw_regular_ae

end BlockBand.Endpoints.Normalization
