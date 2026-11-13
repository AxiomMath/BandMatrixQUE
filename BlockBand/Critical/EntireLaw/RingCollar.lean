module

public import BlockBand.Critical.EntireLaw.ClosedLimit
public import BlockBand.Critical.EntireLaw.Woodbury
public import BlockBand.Critical.Collar.Density.CollarBlocks

/-!
# The entire law: the physical ring as old path ⊕ collar (finite width)

* Law: `measurePreserving_update_pi` (resampling one coordinate of an i.i.d. product),
  `rng_mp_split_middle` (`rngLaw ↦ ((layer at 0, path), A_0)` has law
  `(layerLaw .common ⊗ pathLaw) ⊗ GUE`), `ringCollarSample` (the three-block collar as a
  `CollarSample`, `GlobalSource` orientation), **`measurePreserving_ringPath_collar`**: under
  the exact physical law, `(ringPathSample H, ringCollarSample H)` has law
  `pathLaw W (n-3) b ⊗ collarLaw W b`.
* Sites: `ringSiteEquiv` (path ⊕ (collar ends ⊕ middle) ≃ ring sites), `IsRingBanded`,
  **`submatrix_ringSiteMap`** (a Hermitian banded `H` is the block matrix `closedRingBlocks` of its
  old path and collar), `inv_submatrix_ringSiteEquiv`.
* Sources: `pathProbes`, `probeColumns`, `omittedRingSourceMatrix_eq` (`ζ_o^*Rζ_o = Z*R_{PP}Z`),
  `ringProbeMatrix_eq` (`𝒦_W = Z*G_lead Z`), `leadColumns` (`V`), and
  **`omittedRingSourceMatrix_eq_closedSourceMatrix`**: the collar-omitted closed source matrix is
  `closedSourceMatrix b E 𝒦_W (closingMatrix b E 0 X F ω_c)` for every orthonormal frame `F` with
  `V = F (V*V)^{1/2}`, under four invertibility conditions (which hold a.s., `ae_ringGood`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.CriticalEntire
open scoped ENNReal NNReal

/-!
## Resampling one coordinate of an i.i.d. product
-/

/-- Replacing coordinate `k` of an i.i.d. product sample by an independent copy preserves the law. -/
theorem measurePreserving_update_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*}
    [MeasurableSpace β] (μ : Measure β) [IsProbabilityMeasure μ] (k : ι) :
    MeasurePreserving (fun q : (ι → β) × β => Function.update q.1 k q.2)
      ((Measure.pi fun _ : ι => μ).prod μ) (Measure.pi fun _ : ι => μ) := by
  have hm : Measurable (fun q : (ι → β) × β => Function.update q.1 k q.2) := by
    refine measurable_pi_iff.mpr fun i => ?_
    by_cases hi : i = k
    · subst hi; simpa using measurable_snd
    · simp only [Function.update_of_ne hi]
      exact (measurable_pi_apply i).comp measurable_fst
  refine ⟨hm, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun q : (ι → β) × β => Function.update q.1 k q.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi (Function.update s k Set.univ) ×ˢ s k := by
    ext q
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, by simpa using h k⟩
      by_cases hi : i = k
      · subst hi; simp
      · simpa [Function.update_of_ne hi] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = k
      · subst hi; simpa using h2
      · simpa [Function.update_of_ne hi] using h1 i
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have : ∀ i, μ (Function.update s k Set.univ i) = Function.update (fun i => μ (s i)) k 1 i := by
    intro i
    by_cases hi : i = k
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  simp only [this]
  rw [Finset.prod_update_of_mem (Finset.mem_univ k), one_mul,
    ← Finset.mul_prod_erase Finset.univ (fun i => μ (s i)) (Finset.mem_univ k), mul_comm,
    Finset.sdiff_singleton_eq_erase]

theorem measurePreserving_prodAssoc' {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (τ : Measure γ) [SFinite μ] [SFinite ν]
    [SFinite τ] :
    MeasurePreserving (fun x : (α × β) × γ => (x.1.1, (x.1.2, x.2))) ((μ.prod ν).prod τ)
      (μ.prod (ν.prod τ)) :=
  ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩

/-!
## The ring sample without block `0`, and block `0`
-/

section Split

variable {p : Parameters}

theorem rngSplit_update_zero (ω : BlockBand.Layers.RngSample p) (G : Matrix (Fin p.W) (Fin p.W) ℂ) :
    BlockBand.Layers.rngSplit 0 (Function.update ω.1 0 G, ω.2) = BlockBand.Layers.rngSplit 0 ω := by
  have hn := p.n_ge_four
  have h1 : ∀ a : Fin 2,
      BlockBand.Layers.rngBlk (0 : ZMod p.n) (BlockBand.Layers.rngLayerOff p a) ≠ 0 := by
    intro a
    simp only [BlockBand.Layers.rngBlk, zero_add, BlockBand.Layers.rngLayerOff]
    split_ifs
    · exact BlockBand.Layers.rng_natCast_ne_zero p (by norm_num) (by omega)
    · exact BlockBand.Layers.rng_natCast_ne_zero p (by omega) (by omega)
  have h2 : ∀ i : Fin (p.n - 3), BlockBand.Layers.rngBlk (0 : ZMod p.n) (i.val + 2) ≠ 0 := by
    intro i
    have := i.isLt
    simp only [BlockBand.Layers.rngBlk, zero_add]
    exact BlockBand.Layers.rng_natCast_ne_zero p (by omega) (by omega)
  simp only [BlockBand.Layers.rngSplit, Function.update_of_ne (h1 _), Function.update_of_ne (h2 _)]

/-- **The ring sample splits into the common-port layer at block `0`, the path, and block `0`**,
independently: `rngLaw p ∘ (ω ↦ (rngSplit 0 ω, A_0))⁻¹ = (layerLaw ⊗ pathLaw) ⊗ GUE_W(c/W)`. -/
theorem rng_mp_split_middle :
    MeasurePreserving (fun ω : BlockBand.Layers.RngSample p => (BlockBand.Layers.rngSplit 0 ω, ω.1 0))
      (BlockBand.Layers.rngLaw p)
      (((layerLaw p.W p.b .common).prod (pathLaw p.W (p.n - 3) p.b)).prod
        (gueMeasure (Fin p.W) (Real.toNNReal ((1 - 2 * p.b) / p.W)))) := by
  have := fun t => BlockBand.Layers.isProbabilityMeasure_gueMeasure p.W t
  set μA := gueMeasure (Fin p.W) (Real.toNNReal ((1 - 2 * p.b) / p.W)) with hμA
  set μB := ginibreMeasure (Fin p.W) (Fin p.W) (Real.toNNReal (p.b / p.W)) with hμB
  have : IsProbabilityMeasure μB := by rw [hμB]; infer_instance
  have hpl : IsProbabilityMeasure (pathLaw p.W (p.n - 3) p.b) := inferInstance
  -- resampling block 0
  have hupd := measurePreserving_update_pi μA (0 : ZMod p.n)
  have hR1 : MeasurePreserving
      (fun q : ((ZMod p.n → Matrix (Fin p.W) (Fin p.W) ℂ) × (ZMod p.n → Matrix (Fin p.W) (Fin p.W) ℂ)) ×
          Matrix (Fin p.W) (Fin p.W) ℂ => ((q.1.1, q.2), q.1.2))
      (((Measure.pi fun _ : ZMod p.n => μA).prod (Measure.pi fun _ : ZMod p.n => μB)).prod μA)
      (((Measure.pi fun _ : ZMod p.n => μA).prod μA).prod (Measure.pi fun _ : ZMod p.n => μB)) := by
    have h1 := measurePreserving_prodAssoc' (Measure.pi fun _ : ZMod p.n => μA)
      (Measure.pi fun _ : ZMod p.n => μB) μA
    have h2 := (MeasurePreserving.id (Measure.pi fun _ : ZMod p.n => μA)).prod
      (Measure.measurePreserving_swap (μ := Measure.pi fun _ : ZMod p.n => μB) (ν := μA))
    have h3 : MeasurePreserving
        (fun x : (ZMod p.n → Matrix (Fin p.W) (Fin p.W) ℂ) × (Matrix (Fin p.W) (Fin p.W) ℂ ×
          (ZMod p.n → Matrix (Fin p.W) (Fin p.W) ℂ)) => ((x.1, x.2.1), x.2.2))
        ((Measure.pi fun _ : ZMod p.n => μA).prod (μA.prod (Measure.pi fun _ : ZMod p.n => μB)))
        (((Measure.pi fun _ : ZMod p.n => μA).prod μA).prod (Measure.pi fun _ : ZMod p.n => μB)) :=
      ⟨(MeasurableEquiv.prodAssoc : ((ZMod p.n → Matrix (Fin p.W) (Fin p.W) ℂ) ×
          Matrix (Fin p.W) (Fin p.W) ℂ) × (ZMod p.n → Matrix (Fin p.W) (Fin p.W) ℂ) ≃ᵐ _).symm.measurable, by
        rw [← Measure.prodAssoc_prod (μ := Measure.pi fun _ : ZMod p.n => μA) (ν := μA)
          (τ := Measure.pi fun _ : ZMod p.n => μB)]
        exact MeasurableEquiv.map_symm_map MeasurableEquiv.prodAssoc⟩
    exact h3.comp (h2.comp h1)
  have hU : MeasurePreserving
      (fun q : BlockBand.Layers.RngSample p × Matrix (Fin p.W) (Fin p.W) ℂ =>
        ((Function.update q.1.1 0 q.2, q.1.2) : BlockBand.Layers.RngSample p))
      ((BlockBand.Layers.rngLaw p).prod μA) (BlockBand.Layers.rngLaw p) := by
    have := (hupd.prod (MeasurePreserving.id (Measure.pi fun _ : ZMod p.n => μB))).comp hR1
    unfold BlockBand.Layers.rngLaw
    exact this
  have hF : Measurable (fun ω : BlockBand.Layers.RngSample p => (BlockBand.Layers.rngSplit 0 ω, ω.1 0)) :=
    (BlockBand.Layers.rng_mp_split (p := p) 0).measurable.prodMk
      ((measurable_pi_apply 0).comp measurable_fst)
  have hcomp : (fun ω : BlockBand.Layers.RngSample p => (BlockBand.Layers.rngSplit 0 ω, ω.1 0)) ∘
      (fun q : BlockBand.Layers.RngSample p × Matrix (Fin p.W) (Fin p.W) ℂ =>
        ((Function.update q.1.1 0 q.2, q.1.2) : BlockBand.Layers.RngSample p)) =
      fun q => (BlockBand.Layers.rngSplit 0 q.1, q.2) := by
    funext q
    simp only [Function.comp_apply, rngSplit_update_zero, Function.update_self]
  have hP := (BlockBand.Layers.rng_mp_split (p := p) 0).prod (MeasurePreserving.id μA)
  refine ⟨hF, ?_⟩
  rw [← hU.map_eq, Measure.map_map hF hU.measurable, hcomp]
  exact hP.map_eq

end Split

/-!
## The physical collar of the ring
-/

section Collar

variable {p : Parameters}

/-- Collar end blocks in the GlobalSource orientation: end `0` = ring block `n-1` (next to path
position `0` = block `n-2`), end `1` = ring block `1` (next to block `2`). -/
def collarEndBlock (p : Parameters) (a : Fin 2) : ZMod p.n :=
  if a = 0 then ((p.n - 1 : ℕ) : ZMod p.n) else 1

/-- **The three-block collar of the ring** as a `CollarSample`: end diagonals `A_a = H_{e_a e_a}`
(`e_0 = n-1`, `e_1 = 1`), bonds `B_a = H_{e_a, 0}` to the middle block, middle diagonal `G = H_{00}`
on the port index `Fin 1 × Fin W`. -/
def ringCollarSample (p : Parameters) (H : p.SiteMatrix) : CollarSample p.W :=
  ((fun a x y => H (collarEndBlock p a, x) (collarEndBlock p a, y),
      fun a _ x y => H (collarEndBlock p a, x) (0, y)),
    fun x y => H (0, x.2) (0, y.2))

theorem measurable_ringCollarSample (p : Parameters) : Measurable (ringCollarSample p) := by
  have hent : ∀ x y : p.Site, Measurable fun H : p.SiteMatrix => H x y := fun x y =>
    (measurable_pi_apply y).comp (measurable_pi_apply x)
  refine Measurable.prodMk (Measurable.prodMk ?_ ?_) ?_
  · exact Measurable.of_eval fun a => Measurable.of_eval fun x => Measurable.of_eval fun y =>
      hent _ _
  · exact Measurable.of_eval fun a => Measurable.of_eval fun _ => Measurable.of_eval fun x =>
      Measurable.of_eval fun y => hent _ _
  · exact Measurable.of_eval fun x => Measurable.of_eval fun y => hent _ _

/-- `Fin W ≃ Fin 1 × Fin W`. -/
def portEquiv (W : ℕ) : Fin W ≃ Fin 1 × Fin W := (Equiv.uniqueProd (Fin W) (Fin 1)).symm

theorem neg_collarEndBlock_zero (p : Parameters) :
    -collarEndBlock p 0 = BlockBand.Layers.rngBlk (0 : ZMod p.n) (BlockBand.Layers.rngLayerOff p 0) := by
  have hn := p.n_ge_four
  simp only [collarEndBlock, ↓reduceIte, BlockBand.Layers.rngBlk, BlockBand.Layers.rngLayerOff,
    zero_add]
  refine neg_eq_of_add_eq_zero_left ?_
  rw [← Nat.cast_add, show 1 + (p.n - 1) = p.n by omega, ZMod.natCast_self]

theorem neg_collarEndBlock_one (p : Parameters) :
    -collarEndBlock p 1 = BlockBand.Layers.rngBlk (0 : ZMod p.n) (BlockBand.Layers.rngLayerOff p 1) := by
  have hn := p.n_ge_four
  simp only [collarEndBlock, one_ne_zero, ↓reduceIte, BlockBand.Layers.rngBlk,
    BlockBand.Layers.rngLayerOff, zero_add]
  refine neg_eq_of_add_eq_zero_left ?_
  rw [show (1 : ZMod p.n) = ((1 : ℕ) : ZMod p.n) by simp, ← Nat.cast_add,
    show p.n - 1 + 1 = p.n by omega, ZMod.natCast_self]

/-- Reflection maps the collar in the orientation of `GlobalSource` to the layer of the ring split
at block `0` (`rngSplit 0`) and the block `A_0`. -/
theorem ringCollarSample_reflect (p : Parameters) (ω : BlockBand.Layers.RngSample p) :
    ringCollarSample p (p.siteReindexMatrix (ringReflection p) (BlockBand.Layers.rngAssemble p ω)) =
      ((BlockBand.Layers.rngSplit 0 ω).1, Matrix.reindex (portEquiv p.W) (portEquiv p.W) (ω.1 0)) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext a x y
    rcases BlockBand.Layers.rng_fin2_cases a with rfl | rfl
    · simp only [ringCollarSample, Parameters.siteReindexMatrix, ringReflection, Equiv.coe_fn_mk,
        BlockBand.Layers.rngAssemble_same, BlockBand.Layers.rngSplit, neg_collarEndBlock_zero]
    · simp only [ringCollarSample, Parameters.siteReindexMatrix, ringReflection, Equiv.coe_fn_mk,
        BlockBand.Layers.rngAssemble_same, BlockBand.Layers.rngSplit, neg_collarEndBlock_one]
  · funext a j x y
    rcases BlockBand.Layers.rng_fin2_cases a with rfl | rfl
    · have h1 : -collarEndBlock p 0 = (0 : ZMod p.n) + 1 := by
        rw [neg_collarEndBlock_zero]
        simp [BlockBand.Layers.rngBlk, BlockBand.Layers.rngLayerOff]
      simp only [ringCollarSample, Parameters.siteReindexMatrix, ringReflection, Equiv.coe_fn_mk,
        h1, neg_zero, BlockBand.Layers.rngAssemble_pred, BlockBand.Layers.rngSplit, ↓reduceIte,
        BlockBand.Layers.rngBlk_zero, Matrix.conjTranspose_apply]
    · have key : ∀ j0 : ZMod p.n, j0 + 1 = 0 →
          BlockBand.Layers.rngAssemble p ω (j0, x) (0, y) = ω.2 j0 x y := by
        intro j0 hj
        rw [← hj]
        exact BlockBand.Layers.rngAssemble_succ ω j0 x y
      have h2 : -collarEndBlock p 1 = BlockBand.Layers.rngBlk (0 : ZMod p.n) (p.n - 1) := by
        rw [neg_collarEndBlock_one]; rfl
      simp only [ringCollarSample, Parameters.siteReindexMatrix, ringReflection, Equiv.coe_fn_mk,
        neg_zero]
      rw [key _ (by simp [collarEndBlock]), h2]
      simp [BlockBand.Layers.rngSplit]
  · funext x y
    simp [ringCollarSample, Parameters.siteReindexMatrix, ringReflection,
      BlockBand.Layers.rngAssemble_same, portEquiv]

/-- The ring law is invariant under the reflection `j ↦ -j`. -/
theorem map_ringReflection (model : p.GaussianRingModel) :
    Measure.map (p.siteReindexMatrix (ringReflection p)) (model.law : Measure p.SiteMatrix) =
      (model.law : Measure p.SiteMatrix) := by
  refine model.map_siteReindexMatrix _ (fun x y => ?_) p.entryVariance_symm
  have h1 : -y.1 = -x.1 ↔ y.1 = x.1 := neg_inj
  have h2 : (-y.1 = -x.1 + 1 ∨ -y.1 = -x.1 - 1) ↔ (y.1 = x.1 + 1 ∨ y.1 = x.1 - 1) := by
    constructor
    · rintro (h | h)
      · right; linear_combination -h
      · left; linear_combination -h
    · rintro (h | h)
      · right; linear_combination -h
      · left; linear_combination -h
  simp only [Parameters.entryVariance, ringReflection, Equiv.coe_fn_mk, h1, h2]

/-- **The old path and the collar of the physical ring are independent**: under the physical law
`model.law`, `(ringPathSample H, ringCollarSample H)` has law `pathLaw W (n-3) b ⊗ collarLaw W b`
(every admissible `p`, both parities). Proof: reflection invariance,
`rng_law_eq_map`, `rng_mp_split_middle`, GUE reindexing. -/
theorem measurePreserving_ringPath_collar (model : p.GaussianRingModel) :
    MeasurePreserving (fun H : p.SiteMatrix => (ringPathSample p H, ringCollarSample p H))
      (model.law : Measure p.SiteMatrix)
      ((pathLaw p.W (BlockBand.Critical.GlobalSource.probePathLength p.n) p.b).prod
        (collarLaw p.W p.b)) := by
  have := fun t => BlockBand.Layers.isProbabilityMeasure_gueMeasure p.W t
  set t := Real.toNNReal ((1 - 2 * p.b) / p.W)
  have hpl : IsProbabilityMeasure (pathLaw p.W (p.n - 3) p.b) := inferInstance
  have hfin : IsFiniteMeasure (pathLaw p.W (p.n - 3) p.b) := inferInstance
  have : SFinite (pathLaw p.W (p.n - 3) p.b) := @instSFiniteOfSigmaFinite _ _ _
    (@IsFiniteMeasure.toSigmaFinite _ _ _ hfin)
  have hlay : IsProbabilityMeasure (layerLaw p.W p.b .common) := inferInstance
  have hm : Measurable (fun H : p.SiteMatrix => (ringPathSample p H, ringCollarSample p H)) :=
    (measurable_ringPathSample p).prodMk (measurable_ringCollarSample p)
  have hreidx : MeasurePreserving (Matrix.reindex (portEquiv p.W) (portEquiv p.W))
      (gueMeasure (Fin p.W) t) (gueMeasure (PortSite p.W .common) t) :=
    ⟨Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply,
      BlockBand.Coarea.GUELaw.gueMeasure_map_reindex _ t⟩
  have hgp : IsProbabilityMeasure (gueMeasure (PortSite p.W .common) t) := by
    rw [← hreidx.map_eq]; infer_instance
  -- ((L, π), A₀) ↦ (π, (L, reindex A₀))
  have hG : MeasurePreserving
      (fun q : (LayerSample p.W .common × PathSample p.W (p.n - 3)) × Matrix (Fin p.W) (Fin p.W) ℂ =>
        (q.1.2, (q.1.1, Matrix.reindex (portEquiv p.W) (portEquiv p.W) q.2)))
      (((layerLaw p.W p.b .common).prod (pathLaw p.W (p.n - 3) p.b)).prod (gueMeasure (Fin p.W) t))
      ((pathLaw p.W (p.n - 3) p.b).prod (collarLaw p.W p.b)) := by
    have h1 := (Measure.measurePreserving_swap (μ := layerLaw p.W p.b .common)
      (ν := pathLaw p.W (p.n - 3) p.b)).prod (MeasurePreserving.id (gueMeasure (Fin p.W) t))
    have h2 := measurePreserving_prodAssoc' (pathLaw p.W (p.n - 3) p.b) (layerLaw p.W p.b .common)
      (gueMeasure (Fin p.W) t)
    have h3 := (MeasurePreserving.id (pathLaw p.W (p.n - 3) p.b)).prod
      ((MeasurePreserving.id (layerLaw p.W p.b .common)).prod hreidx)
    unfold collarLaw
    exact h3.comp (h2.comp h1)
  have hall := hG.comp rng_mp_split_middle
  have hfun : (fun H : p.SiteMatrix => (ringPathSample p H, ringCollarSample p H)) ∘
      (p.siteReindexMatrix (ringReflection p) ∘ BlockBand.Layers.rngAssemble p) =
      (fun q : (LayerSample p.W .common × PathSample p.W (p.n - 3)) × Matrix (Fin p.W) (Fin p.W) ℂ =>
        (q.1.2, (q.1.1, Matrix.reindex (portEquiv p.W) (portEquiv p.W) q.2))) ∘
        (fun ω : BlockBand.Layers.RngSample p => (BlockBand.Layers.rngSplit 0 ω, ω.1 0)) := by
    funext ω
    simp only [Function.comp_apply]
    rw [ringPathSample_reflect, ringCollarSample_reflect]
    rfl
  refine ⟨hm, ?_⟩
  rw [← map_ringReflection model, BlockBand.Layers.rng_law_eq_map model,
    Measure.map_map (p.measurable_siteReindexMatrix _) (BlockBand.Layers.rng_measurable_assemble (p := p)),
    Measure.map_map hm ((p.measurable_siteReindexMatrix _).comp
      (BlockBand.Layers.rng_measurable_assemble (p := p))), hfun]
  exact hall.map_eq

end Collar

section Sites

variable {p : Parameters}

/-!
## Block arithmetic on the ring
-/

theorem zmod_natCast_eq_iff {n a b : ℕ} (ha : a < n) (hb : b < n) :
    (a : ZMod n) = (b : ZMod n) ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem zmod_natCast_eq_add_one_iff {n a b : ℕ} (ha : a < n) (hb : b < n) :
    (a : ZMod n) = (b : ZMod n) + 1 ↔ (a = b + 1 ∨ (a = 0 ∧ b + 1 = n)) := by
  rw [show (b : ZMod n) + 1 = ((b + 1 : ℕ) : ZMod n) by push_cast; ring]
  by_cases hb1 : b + 1 < n
  · rw [zmod_natCast_eq_iff ha hb1]; omega
  · have : b + 1 = n := by omega
    rw [this, ZMod.natCast_self, show (0 : ZMod n) = ((0 : ℕ) : ZMod n) by simp,
      zmod_natCast_eq_iff ha (by omega)]
    omega

/-- The block index of each site class, as a natural `< n`. -/
def siteBlockNat (p : Parameters) :
    BlockBand.Critical.GlobalSource.PathSite p.W p.n ⊕ ((Fin 2 × Fin p.W) ⊕ (Fin 1 × Fin p.W)) → ℕ
  | .inl x => p.n - 2 - x.1.val
  | .inr (.inl x) => if x.1 = 0 then p.n - 1 else 1
  | .inr (.inr _) => 0

/-- Sites of the ring as path ⊕ (collar ends ⊕ middle), GlobalSource orientation. -/
def ringSiteMap (p : Parameters) :
    BlockBand.Critical.GlobalSource.PathSite p.W p.n ⊕ ((Fin 2 × Fin p.W) ⊕ (Fin 1 × Fin p.W)) →
      p.Site
  | .inl x => (ringBlockAt p x.1.val, x.2)
  | .inr (.inl x) => (collarEndBlock p x.1, x.2)
  | .inr (.inr x) => (0, x.2)

theorem siteBlockNat_lt (p : Parameters) (u) : siteBlockNat p u < p.n := by
  have hn := p.n_ge_four
  rcases u with x | x | x
  · simp only [siteBlockNat]; omega
  · simp only [siteBlockNat]; split_ifs <;> omega
  · simp only [siteBlockNat]; omega

theorem ringSiteMap_fst (p : Parameters) (u) :
    (ringSiteMap p u).1 = ((siteBlockNat p u : ℕ) : ZMod p.n) := by
  rcases u with x | x | x
  · rfl
  · simp only [ringSiteMap, siteBlockNat, collarEndBlock]
    split_ifs <;> simp
  · simp [ringSiteMap, siteBlockNat]

theorem ringSiteMap_snd (p : Parameters) (u) :
    (ringSiteMap p u).2 = (match u with
      | .inl x => x.2 | .inr (.inl x) => x.2 | .inr (.inr x) => x.2) := by
  rcases u with x | x | x <;> rfl

theorem ringSiteMap_injective (p : Parameters) : Function.Injective (ringSiteMap p) := by
  have hn := p.n_ge_four
  intro u v h
  have hb : siteBlockNat p u = siteBlockNat p v := by
    have := congrArg Prod.fst h
    rw [ringSiteMap_fst, ringSiteMap_fst] at this
    exact (zmod_natCast_eq_iff (siteBlockNat_lt p u) (siteBlockNat_lt p v)).mp this
  have hs := congrArg Prod.snd h
  rcases u with ⟨i, a⟩ | ⟨c, a⟩ | ⟨c, a⟩ <;> rcases v with ⟨i', a'⟩ | ⟨c', a'⟩ | ⟨c', a'⟩ <;>
    simp only [siteBlockNat] at hb <;> simp only [ringSiteMap] at hs <;> subst hs
  · have := i.isLt; have := i'.isLt
    unfold BlockBand.Critical.GlobalSource.probePathLength at *
    congr 2; ext; omega
  · have := i.isLt
    unfold BlockBand.Critical.GlobalSource.probePathLength at *
    split_ifs at hb <;> omega
  · have := i.isLt
    unfold BlockBand.Critical.GlobalSource.probePathLength at *
    omega
  · have := i'.isLt
    unfold BlockBand.Critical.GlobalSource.probePathLength at *
    split_ifs at hb <;> omega
  · congr 2
    rcases BlockBand.Layers.rng_fin2_cases c with rfl | rfl <;>
      rcases BlockBand.Layers.rng_fin2_cases c' with rfl | rfl <;> simp_all
    omega
  · split_ifs at hb; omega
  · have := i'.isLt
    unfold BlockBand.Critical.GlobalSource.probePathLength at *
    omega
  · split_ifs at hb; omega
  · rw [Subsingleton.elim c c']

/-- The site equivalence path ⊕ (collar ends ⊕ middle) ≃ ring sites. -/
def ringSiteEquiv (p : Parameters) :
    BlockBand.Critical.GlobalSource.PathSite p.W p.n ⊕ ((Fin 2 × Fin p.W) ⊕ (Fin 1 × Fin p.W)) ≃
      p.Site :=
  Equiv.ofBijective (ringSiteMap p) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨ringSiteMap_injective p, by
      have hn := p.n_ge_four
      rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_prod, Fintype.card_prod,
        Fintype.card_prod]
      simp only [Fintype.card_fin, Parameters.Site, Fintype.card_prod, ZMod.card]
      unfold BlockBand.Critical.GlobalSource.probePathLength
      zify [show 3 ≤ p.n by omega]
      ring⟩)

/-- `H` is banded: entries between non-adjacent blocks vanish (as for `rngAssemble`). -/
def IsRingBanded (p : Parameters) (H : p.SiteMatrix) : Prop :=
  ∀ x y : p.Site, x.1 ≠ y.1 → y.1 ≠ x.1 + 1 → x.1 ≠ y.1 + 1 → H x y = 0

theorem ringSite_far {H : p.SiteMatrix} (hband : IsRingBanded p H) (u v)
    (h1 : siteBlockNat p u ≠ siteBlockNat p v)
    (h2 : ¬ (siteBlockNat p v = siteBlockNat p u + 1 ∨ (siteBlockNat p v = 0 ∧ siteBlockNat p u + 1 = p.n)))
    (h3 : ¬ (siteBlockNat p u = siteBlockNat p v + 1 ∨ (siteBlockNat p u = 0 ∧ siteBlockNat p v + 1 = p.n))) :
    H (ringSiteMap p u) (ringSiteMap p v) = 0 := by
  have hu := siteBlockNat_lt p u
  have hv := siteBlockNat_lt p v
  refine hband _ _ ?_ ?_ ?_
  · rw [ringSiteMap_fst, ringSiteMap_fst, Ne, zmod_natCast_eq_iff hu hv]; exact h1
  · rw [ringSiteMap_fst, ringSiteMap_fst, Ne, zmod_natCast_eq_add_one_iff hv hu]; exact h2
  · rw [ringSiteMap_fst, ringSiteMap_fst, Ne, zmod_natCast_eq_add_one_iff hu hv]; exact h3

/-- The closed ring as a block matrix over path ⊕ (collar ends ⊕ middle). -/
def closedRingBlocks {W r : ℕ} (π : PathSample W r) (ωc : CollarSample W) :
    Matrix (Fin r × Fin W ⊕ ((Fin 2 × Fin W) ⊕ (Fin 1 × Fin W)))
      (Fin r × Fin W ⊕ ((Fin 2 × Fin W) ⊕ (Fin 1 × Fin W))) ℂ :=
  fromBlocks (pathMatrix π) (fromCols (pathPortCoupling π) 0) (fromRows (pathPortCoupling π)ᴴ 0)
    (fromBlocks (blockDiag ωc.1.1) (bondMatrix .common ωc.1.2) (bondMatrix .common ωc.1.2)ᴴ ωc.2)

theorem entry_path_end {H : p.SiteMatrix} (hband : IsRingBanded p H)
    (i : Fin (BlockBand.Critical.GlobalSource.probePathLength p.n)) (a : Fin p.W) (c : Fin 2)
    (a' : Fin p.W) :
    H (ringBlockAt p i.val, a) (collarEndBlock p c, a') =
      pathPortCoupling (ringPathSample p H) (i, a) (c, a') := by
  have hn := p.n_ge_four
  have hi := i.isLt
  unfold BlockBand.Critical.GlobalSource.probePathLength at hi
  unfold pathPortCoupling
  rcases BlockBand.Layers.rng_fin2_cases c with rfl | rfl
  · by_cases h0 : i.val = 0
    · simp only [h0, true_and, true_or, ↓reduceIte, ringPathSample, collarEndBlock]
    · have hf := ringSite_far hband (.inl (i, a)) (.inr (.inl (0, a')))
        (by simp only [siteBlockNat, ↓reduceIte]; omega)
        (by simp only [siteBlockNat, ↓reduceIte]; omega)
        (by simp only [siteBlockNat, ↓reduceIte]; omega)
      simp only [ringSiteMap] at hf
      rw [hf]
      simp [h0]
  · by_cases h1 : i.val + 1 = BlockBand.Critical.GlobalSource.probePathLength p.n
    · have : i.val = p.n - 4 := by
        unfold BlockBand.Critical.GlobalSource.probePathLength at h1; omega
      simp only [h1, and_true, or_true, ↓reduceIte]
      simp only [ringPathSample, collarEndBlock, one_ne_zero, ↓reduceIte, this]
    · have h1' : i.val + 1 ≠ p.n - 3 := h1
      have hf := ringSite_far hband (.inl (i, a)) (.inr (.inl (1, a')))
        (by simp only [siteBlockNat, one_ne_zero, ↓reduceIte]; omega)
        (by simp only [siteBlockNat, one_ne_zero, ↓reduceIte]; omega)
        (by simp only [siteBlockNat, one_ne_zero, ↓reduceIte]; omega)
      simp only [ringSiteMap] at hf
      rw [hf]
      simp [h1]

/-- **The closed physical ring in path ⊕ collar blocks**: for a Hermitian
banded `H`, reindexing by `ringSiteMap` gives `[[H_path, (Γ 0)], [(Γ* 0)ᵀ, [[A, B], [B*, G]]]]` with
the old path `ringPathSample H` (its port coupling `Γ` reaches the collar ends only) and the
collar `ringCollarSample H`. -/
theorem submatrix_ringSiteMap {H : p.SiteMatrix} (hH : H.IsHermitian) (hband : IsRingBanded p H) :
    H.submatrix (ringSiteMap p) (ringSiteMap p) =
      closedRingBlocks (ringPathSample p H) (ringCollarSample p H) := by
  have hn := p.n_ge_four
  ext u v
  rcases u with ⟨i, a⟩ | ⟨c, a⟩ | ⟨m, a⟩ <;> rcases v with ⟨i', a'⟩ | ⟨c', a'⟩ | ⟨m', a'⟩ <;>
    simp only [closedRingBlocks, submatrix_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, fromCols_apply_inl, fromCols_apply_inr,
      fromRows_apply_inl, fromRows_apply_inr, Matrix.zero_apply, conjTranspose_apply]
  · -- path, path
    have hi := i.isLt; have hi' := i'.isLt
    unfold BlockBand.Critical.GlobalSource.probePathLength at hi hi'
    unfold pathMatrix
    split_ifs with h1 h2 h3
    · subst h1; rfl
    · simp only [ringSiteMap, ringPathSample]
      congr 2
      unfold ringBlockAt; rw [h2]
    · rw [← hH.apply]
      simp only [ringSiteMap, ringPathSample]
      congr 3
      unfold ringBlockAt; rw [h3]
    · have h1' : i.val ≠ i'.val := fun h => h1 (Fin.ext h)
      simp only at h2 h3
      exact ringSite_far hband (.inl (i, a)) (.inl (i', a'))
        (by simp only [siteBlockNat]; omega) (by simp only [siteBlockNat]; omega)
        (by simp only [siteBlockNat]; omega)
  · -- path, end
    exact entry_path_end hband i a c' a'
  · -- path, middle
    have hi := i.isLt
    unfold BlockBand.Critical.GlobalSource.probePathLength at hi
    exact ringSite_far hband (.inl (i, a)) (.inr (.inr (m', a')))
      (by simp only [siteBlockNat]; omega) (by simp only [siteBlockNat]; omega)
      (by simp only [siteBlockNat]; omega)
  · -- end, path
    rw [← hH.apply, ← entry_path_end hband i' a' c a]
    rfl
  · -- end, end
    simp only [ringCollarSample, BlockBand.Internal.Contracts.Layers.blockDiag]
    split_ifs with h
    · subst h; rfl
    · rcases BlockBand.Layers.rng_fin2_cases c with rfl | rfl <;>
        rcases BlockBand.Layers.rng_fin2_cases c' with rfl | rfl
      · exact absurd rfl h
      · exact ringSite_far hband (.inr (.inl (0, a))) (.inr (.inl (1, a')))
          (by simp [siteBlockNat]; omega) (by simp [siteBlockNat]; omega)
          (by simp [siteBlockNat]; omega)
      · exact ringSite_far hband (.inr (.inl (1, a))) (.inr (.inl (0, a')))
          (by simp [siteBlockNat]; omega) (by simp [siteBlockNat]; omega)
          (by simp [siteBlockNat]; omega)
      · exact absurd rfl h
  · -- end, middle
    simp only [ringCollarSample, bondMatrix, LayerShape.incident, ↓reduceIte]
    rfl
  · -- middle, path
    have hi := i'.isLt
    unfold BlockBand.Critical.GlobalSource.probePathLength at hi
    exact ringSite_far hband (.inr (.inr (m, a))) (.inl (i', a'))
      (by simp only [siteBlockNat]; omega) (by simp only [siteBlockNat]; omega)
      (by simp only [siteBlockNat]; omega)
  · -- middle, end
    rw [← hH.apply]
    simp only [ringCollarSample, bondMatrix, LayerShape.incident, ↓reduceIte]
    rfl
  · -- middle, middle
    rfl

end Sites

/-!
## The omitted closed source matrix in path coordinates
-/

section Sources

variable {p : Parameters}

open BlockBand.Critical.GlobalSource

/-- The probe Gaussians read on the remaining path sites (`g ∘ ringSiteMap ∘ inl`). -/
def pathProbes (p : Parameters) {J : ℕ} (g : Fin J → p.Site → ℂ) : Fin J → PathSite p.W p.n → ℂ :=
  fun c x => g c (ringSiteMap p (.inl x))

/-- The source columns `Z = (ζ_c)_c` on the path sites. -/
def probeColumns (W n : ℕ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) (g : Fin J → PathSite W n → ℂ) :
    Matrix (PathSite W n) (Fin J) ℂ :=
  Matrix.of fun x c => globalProbeVector W n (Q c) (g c) x

theorem ringBlockAt_val (p : Parameters) (i : Fin (probePathLength p.n)) :
    (ringBlockAt p i.val).val = p.n - 2 - i.val := by
  unfold ringBlockAt
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := p.n_ge_four; omega)]

theorem ringProbeVector_path (p : Parameters) (Q : C(Torus, ℝ)) (g : p.Site → ℂ)
    (x : PathSite p.W p.n) :
    omitCollar p (ringProbeVector p Q g) (ringSiteMap p (.inl x)) =
      globalProbeVector p.W p.n Q (fun y => g (ringSiteMap p (.inl y))) x := by
  have hn := p.n_ge_four
  have hi := x.1.isLt
  unfold probePathLength at hi
  have hnc : ¬ IsCollarBlock p (ringBlockAt p x.1.val) := by
    have h := siteBlockNat_lt p (.inl x)
    unfold IsCollarBlock
    rw [show ringBlockAt p x.1.val = ((siteBlockNat p (.inl x) : ℕ) : ZMod p.n) from rfl]
    rintro (h0 | h1 | h2)
    · rw [show (0 : ZMod p.n) = ((0 : ℕ) : ZMod p.n) by simp, zmod_natCast_eq_iff h (by omega)] at h0
      simp only [siteBlockNat] at h0; omega
    · rw [show (1 : ZMod p.n) = ((1 : ℕ) : ZMod p.n) by simp, zmod_natCast_eq_iff h (by omega)] at h1
      simp only [siteBlockNat] at h1; omega
    · have : (-1 : ZMod p.n) = ((p.n - 1 : ℕ) : ZMod p.n) := by
        rw [eq_comm, Nat.cast_sub (by omega)]; simp
      rw [this, zmod_natCast_eq_iff h (by omega)] at h2
      simp only [siteBlockNat] at h2; omega
  simp only [omitCollar, ringSiteMap, hnc, ↓reduceIte, ringProbeVector, globalProbeVector,
    pathProfileValue, Parameters.ringProfilePoint, ringBlockAt_val, pathRingBlock]

theorem omitCollar_collar (p : Parameters) (v : p.Site → ℂ) (u : (Fin 2 × Fin p.W) ⊕ (Fin 1 × Fin p.W)) :
    omitCollar p v (ringSiteMap p (.inr u)) = 0 := by
  have hn := p.n_ge_four
  rcases u with ⟨c, a⟩ | ⟨m, a⟩
  · have : IsCollarBlock p (collarEndBlock p c) := by
      unfold IsCollarBlock collarEndBlock
      split_ifs
      · right; right
        rw [Nat.cast_sub (by omega)]; simp
      · right; left; rfl
    simp [omitCollar, ringSiteMap, this]
  · have : IsCollarBlock p 0 := Or.inl rfl
    simp [omitCollar, ringSiteMap, this]

theorem dotProduct_mulVec_eq_mul {ι : Type*} [Fintype ι] {J : ℕ} (u : Fin J → ι → ℂ)
    (G : Matrix ι ι ℂ) (a c : Fin J) :
    star (u a) ⬝ᵥ (G *ᵥ u c) =
      ((Matrix.of fun x c => u c x)ᴴ * G * Matrix.of fun x c => u c x) a c := by
  simp only [dotProduct, mulVec, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **The omitted closed source matrix in path coordinates**: `ζ_o^* R ζ_o = Z*(R_{path,path})Z`,
`R = (H - E)⁻¹` read through `ringSiteEquiv`, `Z = probeColumns` of the path-restricted Gaussians. -/
theorem omittedRingSourceMatrix_eq (E : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) (H : p.SiteMatrix)
    (g : Fin J → p.Site → ℂ) :
    omittedRingSourceMatrix p E Q H g =
      (probeColumns p.W p.n Q (pathProbes p g))ᴴ *
        (((H - (E : ℂ) • 1)⁻¹).submatrix (ringSiteEquiv p) (ringSiteEquiv p)).toBlocks₁₁ *
          probeColumns p.W p.n Q (pathProbes p g) := by
  ext a c
  set R := (H - (E : ℂ) • (1 : p.SiteMatrix))⁻¹
  set v : Fin J → p.Site → ℂ := fun c => omitCollar p (ringProbeVector p (Q c) (g c))
  have hv : ∀ c x, v c (ringSiteMap p (.inl x)) = probeColumns p.W p.n Q (pathProbes p g) x c :=
    fun c x => ringProbeVector_path p (Q c) (g c) x
  have hv0 : ∀ c u, v c (ringSiteMap p (.inr u)) = 0 := fun c u => omitCollar_collar p _ u
  change star (v a) ⬝ᵥ (R *ᵥ v c) = _
  rw [dotProduct_mulVec_eq_mul]
  simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, toBlocks₁₁, submatrix_apply]
  have he : ∀ u, (ringSiteEquiv p) u = ringSiteMap p u := fun _ => rfl
  rw [← (ringSiteEquiv p).sum_comp (fun y => (∑ x, star (v a x) * R x y) * v c y)]
  simp only [Fintype.sum_sum_type, he, hv0, mul_zero, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← (ringSiteEquiv p).sum_comp (fun x => star (v a x) * R x (ringSiteMap p (.inl y)))]
  simp only [Fintype.sum_sum_type, he, hv0, hv, star_zero, zero_mul, Finset.sum_const_zero,
    add_zero]

/-- `𝒦_W = Z* G_lead Z` for the ring's path probes. -/
theorem ringProbeMatrix_eq (b E : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) (H : p.SiteMatrix)
    (g : Fin J → p.Site → ℂ) :
    ringProbeMatrix p b E Q (H, pathProbes p g) =
      (probeColumns p.W p.n Q (pathProbes p g))ᴴ * pathLeadInverse b E (ringPathSample p H) *
        probeColumns p.W p.n Q (pathProbes p g) := by
  ext a c
  exact dotProduct_mulVec_eq_mul (fun c => globalProbeVector p.W p.n (Q c) (pathProbes p g c)) _ a c

theorem submatrix_ringSiteEquiv (H : p.SiteMatrix) :
    H.submatrix (ringSiteEquiv p) (ringSiteEquiv p) = H.submatrix (ringSiteMap p) (ringSiteMap p) :=
  rfl

/-- `(H - E)⁻¹` in path ⊕ collar blocks. -/
theorem inv_submatrix_ringSiteEquiv {H : p.SiteMatrix} (hH : H.IsHermitian)
    (hband : IsRingBanded p H) (E : ℝ) :
    ((H - (E : ℂ) • 1)⁻¹).submatrix (ringSiteEquiv p) (ringSiteEquiv p) =
      (fromBlocks (pathMatrix (ringPathSample p H) - (E : ℂ) • 1)
        (fromCols (pathPortCoupling (ringPathSample p H)) 0)
        (fromRows (pathPortCoupling (ringPathSample p H))ᴴ 0)
        (fromBlocks (blockDiag (ringCollarSample p H).1.1 - (E : ℂ) • 1)
          (bondMatrix .common (ringCollarSample p H).1.2)
          (bondMatrix .common (ringCollarSample p H).1.2)ᴴ
          ((ringCollarSample p H).2 - (E : ℂ) • 1)))⁻¹ := by
  have hs : (H - (E : ℂ) • (1 : p.SiteMatrix)).submatrix (ringSiteEquiv p) (ringSiteEquiv p) =
      H.submatrix (ringSiteEquiv p) (ringSiteEquiv p) - (E : ℂ) • 1 := by
    ext u v
    simp [Matrix.one_apply, (ringSiteEquiv p).injective.eq_iff]
  rw [← inv_submatrix_equiv, hs, submatrix_ringSiteEquiv, submatrix_ringSiteMap hH hband]
  congr 1
  unfold closedRingBlocks
  rw [← fromBlocks_one, ← fromBlocks_one, fromBlocks_smul, fromBlocks_smul, sub_eq_add_neg,
    fromBlocks_neg, fromBlocks_neg, fromBlocks_add, fromBlocks_add]
  simp [sub_eq_add_neg]

/-- The open-lead columns `V = (z_b - X)⁻* Γ* h⁻¹ Z` of the ring's old path (`V*V = B`). -/
def leadColumns (b E : ℝ) {W r J : ℕ} (π : PathSample W r) (Z : Matrix (Fin r × Fin W) (Fin J) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin J) ℂ :=
  ((boundaryZ b E • 1 - pathSchur E π)⁻¹)ᴴ *
    ((pathPortCoupling π)ᴴ * (pathMatrix π - (E : ℂ) • 1)⁻¹ * Z)

theorem pathMatrix_sub_isHermitian {W r : ℕ} {π : PathSample W r} (hA : ∀ j, (π.1 j).IsHermitian)
    (E : ℝ) : (pathMatrix π - (E : ℂ) • (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ)).IsHermitian := by
  refine (BlockBand.Layers.srec_pathMatrix_isHermitian π hA).sub ?_
  unfold IsHermitian
  rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

theorem ringPathSample_blocks_isHermitian {H : p.SiteMatrix} (hH : H.IsHermitian)
    (j : Fin (probePathLength p.n)) : ((ringPathSample p H).1 j).IsHermitian := by
  ext x y
  exact hH.apply _ _

/-- **Finite-width closed-source identity for the physical ring** (the complete closing
determinant and the closed source matrix, by Woodbury and an old orthonormal frame spanning the `V`
columns). For a Hermitian banded `H` (every sample of the physical law,
a.s.), the source matrix of the collar-omitted probes is
`closedSourceMatrix b E 𝒦_W 𝒞_W`, with `𝒦_W = ringProbeMatrix` (old lead source matrix of the
ring's path), `𝒞_W = closingMatrix b E 0 X F ω_c` (`X = pathSchur` of the old path, `ω_c` the
collar, `F` an orthonormal frame with `V = F (V*V)^{1/2}`), provided the old interior, the middle
block, the terminating reaction `K_c + iη` and `D - X` are invertible. -/
theorem omittedRingSourceMatrix_eq_closedSourceMatrix (b E : ℝ) (hη : 0 < (boundaryZ b E).im)
    {J : ℕ} (Q : Fin J → C(Torus, ℝ)) {H : p.SiteMatrix} (hH : H.IsHermitian)
    (hband : IsRingBanded p H) (g : Fin J → p.Site → ℂ)
    (hh : IsUnit (pathMatrix (ringPathSample p H) - (E : ℂ) • 1).det)
    (hG : IsUnit ((ringCollarSample p H).2 - (E : ℂ) • 1).det)
    (hT : IsUnit (BlockBand.Critical.MatrixClosing.middleReaction b E 0 (ringCollarSample p H) +
      (((boundaryZ b E).im : ℂ) * Complex.I) • 1).det)
    (hY : IsUnit (collarEndSchur b E (ringCollarSample p H) - pathSchur E (ringPathSample p H)).det)
    (F : Matrix (Fin 2 × Fin p.W) (Fin J) ℂ)
    (hF : leadColumns b E (ringPathSample p H) (probeColumns p.W p.n Q (pathProbes p g)) =
      F * cfc Real.sqrt ((leadColumns b E (ringPathSample p H)
        (probeColumns p.W p.n Q (pathProbes p g)))ᴴ *
          leadColumns b E (ringPathSample p H) (probeColumns p.W p.n Q (pathProbes p g)))) :
    omittedRingSourceMatrix p E Q H g =
      closedSourceMatrix b E (ringProbeMatrix p b E Q (H, pathProbes p g))
        (BlockBand.Critical.MatrixClosing.closingMatrix b E 0 (pathSchur E (ringPathSample p H)) F
          (ringCollarSample p H)) := by
  set π := ringPathSample p H
  set ωc := ringCollarSample p H
  set Z := probeColumns p.W p.n Q (pathProbes p g)
  set h := pathMatrix π - (E : ℂ) • (1 : Matrix _ _ ℂ)
  set Γ := pathPortCoupling π
  have hhH : h.IsHermitian := pathMatrix_sub_isHermitian (ringPathSample_blocks_isHermitian hH) E
  have hX : (Γᴴ * h⁻¹ * Γ).IsHermitian := by
    have := isHermitian_conjTranspose_mul_mul Γ hhH.inv
    simpa [Matrix.mul_assoc] using this
  have hR := isUnit_det_smul_one_sub_of_isHermitian hX hη
  have hY' : IsUnit (blockDiag ωc.1.1 - (E : ℂ) • 1 - bondMatrix .common ωc.1.2 *
      (ωc.2 - (E : ℂ) • 1)⁻¹ * (bondMatrix .common ωc.1.2)ᴴ - Γᴴ * h⁻¹ * Γ).det := by
    rw [← collarEndSchur_eq]; exact hY
  have hK : ringProbeMatrix p b E Q (H, pathProbes p g) =
      Zᴴ * (h⁻¹ + h⁻¹ * Γ * (boundaryZ b E • 1 - Γᴴ * h⁻¹ * Γ)⁻¹ * Γᴴ * h⁻¹) * Z := by
    rw [ringProbeMatrix_eq]
    unfold pathLeadInverse
    rw [toBlocks11_inv_fromBlocks h Γ Γᴴ _ hh hR]
  rw [omittedRingSourceMatrix_eq, inv_submatrix_ringSiteEquiv hH hband,
    toBlocks11_inv_closedRing _ _ _ _ _ _ hh hG hY', ← collarEndSchur_eq, hK]
  refine closedSource_eq_closedSourceMatrix b E hη hhH Γ Z ωc hT hY F ?_
  rw [probeGram_lead_source b E hη hhH Γ Z]
  exact hF

end Sources

end BlockBand.Critical.EntireLaw
