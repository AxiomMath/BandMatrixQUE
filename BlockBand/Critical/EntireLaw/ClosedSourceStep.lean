module

public import BlockBand.Critical.EntireLaw.RingCollar
public import BlockBand.Critical.EntireLaw.PolarFrame
public import BlockBand.Critical.EntireLaw.Ward
public import BlockBand.Critical.EntireLaw.CollarRemoval

/-!
# The entire law: the closed-source limit step

* `closedSourceLimitStep_holds (hMT : MatchedTracesContract) : ClosedSourceLimitStep`;
* `entireLaw_of_matrixClosing`: `EntireLawContract` from `GlobalGaussianSourceStatement`,
  `MatrixClosingStatement`, `External.PSSS.SourceContract` and `MatchedTracesContract`.

Proof:
1. finite width: a.s. under the physical law,
   `ζ_o^*Rζ_o = closedSourceMatrix b E 𝒦_W (closingMatrix b E 0 X F ω_c)`
   (`omittedRingSourceMatrix_eq_closedSourceMatrix`; invertibility a.s.: `ae_ringGood`,
   `ae_isHermitian_isRingBanded`);
2. frames: measurable polar frames for `J² ≤ 2W` (`exists_measurable_polarFrame`; rank
   deficiency of `B` is padded, no lower bound on `B`); the sequence is shifted by `N₀`;
3. law: `fullRingProbeLaw ↦ (oldProbeLaw ⊗ collarLaw)` (`measurePreserving_ringOldCollar`);
4. `hZ` from `IsRingProbeCriticalLimit` through the `ringProbeLaw` marginal
   (`integral_ringProbeMatrix_eq`);
5. `tendsto_closedPhase_of_oldData`: `MatrixClosingStatement.stable_joint_atZero`
   with the bounded test `closedPhaseRe/Im` (Hermitian parts; `𝒞_W`, `C₀` Hermitian a.s.),
   continuity of `K ↦ cfc √(probeGram K)`, local `PolishSpace`/`BorelSpace` instances, and the
   Fubini step to the iterated integral of `ClosedSourceLimitStep`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.Collar.Kernel (measurable_matrix_mul' measurable_matrix_add'
  measurable_matrix_sub' measurable_matrix_smul' measurable_matrix_conjTranspose'
  measurable_matrix_inv' measurable_blockDiag_collar measurable_bondMatrix_collar)
open scoped ENNReal NNReal BoundedContinuousFunction

/-!
## Almost-sure facts
-/

section AlmostSure

variable {W : ℕ}

theorem measurable_collarEndSchur (b e : ℝ) :
    Measurable fun ω : CollarSample W => collarEndSchur b e ω := by
  have hK : Measurable fun ω : CollarSample W => BlockBand.Critical.MatrixClosing.middleReaction b e 0 ω := by
    unfold BlockBand.Critical.MatrixClosing.middleReaction
    exact measurable_matrix_sub' (measurable_matrix_sub' measurable_blockDiag_collar
      measurable_const) (measurable_matrix_mul' (measurable_matrix_mul' measurable_bondMatrix_collar
        (measurable_matrix_inv' (measurable_matrix_sub' measurable_snd measurable_const)))
        (measurable_matrix_conjTranspose' measurable_bondMatrix_collar))
  unfold collarEndSchur
  exact measurable_matrix_add' hK measurable_const

/-- The collar blocks are Hermitian a.s. -/
theorem ae_collar_isHermitian (b : ℝ) :
    ∀ᵐ ω ∂collarLaw W b, (∀ j, (ω.1.1 j).IsHermitian) ∧ ω.2.IsHermitian := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := layerLaw W b .common)
    (ν := gueMeasure (PortSite W .common) (Real.toNNReal ((1 - 2 * b) / W)))).ae
    (BlockBand.Layers.lct_ae_blocks_isHermitian W b .common)
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := layerLaw W b .common)
    (ν := gueMeasure (PortSite W .common) (Real.toNNReal ((1 - 2 * b) / W)))).ae
    (BlockBand.Coarea.GUELaw.ae_isHermitian_gueMeasure (ι := PortSite W .common) _)
  unfold collarLaw
  filter_upwards [h1, h2] with ω h1 h2
  exact ⟨h1, h2⟩

/-- `K_c + iη` is invertible a.s. (`K_c` Hermitian, `η > 0`). -/
theorem ae_isUnit_middleReaction_add (b e : ℝ) (hη : 0 < (boundaryZ b e).im) :
    ∀ᵐ ω ∂collarLaw W b, IsUnit (BlockBand.Critical.MatrixClosing.middleReaction b e 0 ω +
      (((boundaryZ b e).im : ℂ) * Complex.I) • 1).det := by
  filter_upwards [ae_collar_isHermitian b] with ω h
  exact BlockBand.Critical.Collar.Kernel.isUnit_det_herm_add_I_smul
    (BlockBand.Critical.MatrixClosing.middleReaction_isHermitian b e 0 h.1 h.2) hη

/-- `D - X = A - e - B(G - e)⁻¹B* - X` is invertible a.s. for every fixed `X` (Fubini: a.s. in the
end diagonals `A`, for fixed bonds and middle block). -/
theorem ae_isUnit_collarEndSchur_sub {b : ℝ} (hb : b < 1 / 2) (hW : 0 < W) (e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∀ᵐ ω ∂collarLaw W b, IsUnit (collarEndSchur b e ω - X).det := by
  have := fun t => BlockBand.Layers.isProbabilityMeasure_gueMeasure W t
  set t := Real.toNNReal ((1 - 2 * b) / W)
  have ht : t ≠ 0 :=
    (Real.toNNReal_pos.2 (div_pos (by linarith) (by exact_mod_cast hW))).ne'
  have hm : Measurable fun ω : CollarSample W => (collarEndSchur b e ω - X).det :=
    (continuous_id.matrix_det).measurable.comp (measurable_matrix_sub' (measurable_collarEndSchur b e)
      measurable_const)
  have hset : MeasurableSet {ω : CollarSample W | IsUnit (collarEndSchur b e ω - X).det} := by
    simp_rw [isUnit_iff_ne_zero]
    exact hm (measurableSet_singleton 0).compl
  unfold collarLaw
  rw [Measure.ae_prod_iff_ae_ae hset, Measure.ae_ae_comm hset]
  refine Filter.Eventually.of_forall fun G => ?_
  have hset' : MeasurableSet {L : LayerSample W .common | IsUnit (collarEndSchur b e (L, G) - X).det} :=
    measurable_prodMk_right hset
  unfold layerLaw
  rw [Measure.ae_prod_iff_ae_ae hset', Measure.ae_ae_comm hset']
  refine Filter.Eventually.of_forall fun B => ?_
  rw [ae_iff]
  have hnull := BlockBand.Layers.srec_pi_gue_det_null W 2 ht
    (-(e : ℂ) • 1 - bondMatrix .common B * (G - (e : ℂ) • 1)⁻¹ * (bondMatrix .common B)ᴴ - X)
  refine measure_mono_null (fun A hA => ?_) hnull
  simp only [Set.mem_ofPred_eq, isUnit_iff_ne_zero, not_not] at hA ⊢
  rw [← hA, collarEndSchur_eq]
  congr 1
  simp only [neg_smul]
  abel

variable {p : Parameters}

theorem measurableSet_isRingBanded (p : Parameters) :
    MeasurableSet {H : p.SiteMatrix | IsRingBanded p H} := by
  have : {H : p.SiteMatrix | IsRingBanded p H} =
      ⋂ x : p.Site, ⋂ y : p.Site,
        (if x.1 ≠ y.1 ∧ y.1 ≠ x.1 + 1 ∧ x.1 ≠ y.1 + 1 then {H : p.SiteMatrix | H x y = 0}
          else Set.univ) := by
    ext H
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, IsRingBanded]
    constructor
    · intro h x y
      split_ifs with hc
      · exact h x y hc.1 hc.2.1 hc.2.2
      · trivial
    · intro h x y h1 h2 h3
      simpa [h1, h2, h3] using h x y
  rw [this]
  refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => ?_
  split_ifs
  · exact (measurable_pi_apply y).comp (measurable_pi_apply x) (measurableSet_singleton 0)
  · exact MeasurableSet.univ

/-- The physical law is carried by Hermitian banded matrices. -/
theorem ae_isHermitian_isRingBanded (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), H.IsHermitian ∧ IsRingBanded p H := by
  rw [BlockBand.Layers.rng_law_eq_map model]
  have hset : MeasurableSet {H : p.SiteMatrix | H.IsHermitian ∧ IsRingBanded p H} :=
    (measurableSet_isHermitian_of_measurable measurable_id).inter (measurableSet_isRingBanded p)
  rw [ae_map_iff (BlockBand.Layers.rng_measurable_assemble (p := p)).aemeasurable hset]
  filter_upwards [BlockBand.Layers.rng_ae_blocks_isHermitian (p := p)] with ω hω
  exact ⟨BlockBand.Layers.rngAssemble_isHermitian ω hω,
    fun x y h1 h2 h3 => BlockBand.Layers.rngAssemble_far ω x y h1 h2 h3⟩

end AlmostSure

/-!
## The probes on the path sites
-/

section Probes

variable {p : Parameters}

open BlockBand.Critical.GlobalSource

/-- Restricting a standard circular vector on the ring sites to the path sites. -/
theorem measurePreserving_restrictPath (p : Parameters) :
    MeasurePreserving (fun g : p.Site → ℂ => fun x : PathSite p.W p.n => g (ringSiteMap p (.inl x)))
      (circularVectorLaw p.Site) (circularVectorLaw (PathSite p.W p.n)) := by
  set e := ringSiteEquiv p
  have h1 : MeasurePreserving (fun g : p.Site → ℂ => g ∘ e) (circularVectorLaw p.Site)
      (circularVectorLaw (PathSite p.W p.n ⊕ ((Fin 2 × Fin p.W) ⊕ (Fin 1 × Fin p.W)))) := by
    refine ⟨measurable_pi_iff.mpr fun u => measurable_pi_apply _, ?_⟩
    have := BlockBand.Coarea.ProjectiveHaar.circularVectorLaw_map_comp_equiv e.symm
    simpa using this
  rw [BlockBand.Coarea.ProjectiveHaar.circularVectorLaw_eq_pi,
    BlockBand.Coarea.ProjectiveHaar.circularVectorLaw_eq_pi] at *
  have h2 := BlockBand.Layers.rng_mp_sum_split (ι := PathSite p.W p.n)
    (ι' := (Fin 2 × Fin p.W) ⊕ (Fin 1 × Fin p.W)) BlockBand.Coarea.ProjectiveHaar.circularLawOne
  have h3 := (measurePreserving_fst (μ := Measure.pi fun _ : PathSite p.W p.n =>
      BlockBand.Coarea.ProjectiveHaar.circularLawOne)
    (ν := Measure.pi fun _ : (Fin 2 × Fin p.W) ⊕ (Fin 1 × Fin p.W) =>
      BlockBand.Coarea.ProjectiveHaar.circularLawOne)).comp (h2.comp h1)
  exact h3

/-- The old data (path, path probes) and the collar of a ring sample with probes. -/
def ringOldCollar (p : Parameters) {J : ℕ} (x : p.SiteMatrix × (Fin J → p.Site → ℂ)) :
    (PathSample p.W (probePathLength p.n) × (Fin J → PathSite p.W p.n → ℂ)) × CollarSample p.W :=
  ((ringPathSample p x.1, pathProbes p x.2), ringCollarSample p x.1)

/-- The law of the old data: the path law and `J` independent circular probes on the path sites. -/
def oldProbeLaw (W n J : ℕ) (b : ℝ) :
    Measure (PathSample W (probePathLength n) × (Fin J → PathSite W n → ℂ)) :=
  (pathLaw W (probePathLength n) b).prod (Measure.pi fun _ : Fin J => circularVectorLaw (PathSite W n))

instance isProbabilityMeasure_oldProbeLaw (W n J : ℕ) (b : ℝ) :
    IsProbabilityMeasure (oldProbeLaw W n J b) := by
  unfold oldProbeLaw; infer_instance

/-- **`fullRingProbeLaw = (old data ⊗ probes) ⊗ collarLaw`**: under the physical law with probes on
all ring sites, `(old path, path probes)` and the collar are independent, with laws
`oldProbeLaw ⊗ collarLaw`. -/
theorem measurePreserving_ringOldCollar (model : p.GaussianRingModel) (J : ℕ) :
    MeasurePreserving (ringOldCollar p (J := J)) (fullRingProbeLaw model J)
      ((oldProbeLaw p.W p.n J p.b).prod (collarLaw p.W p.b)) := by
  have hpl : IsProbabilityMeasure (pathLaw p.W (probePathLength p.n) p.b) := by
    unfold probePathLength; infer_instance
  have h1 := (measurePreserving_ringPath_collar model).prod
    (measurePreserving_pi (fun _ : Fin J => circularVectorLaw p.Site)
      (fun _ : Fin J => circularVectorLaw (PathSite p.W p.n))
      (fun _ => measurePreserving_restrictPath p))
  have h2 := measurePreserving_prodAssoc' (pathLaw p.W (probePathLength p.n) p.b)
    (collarLaw p.W p.b) (Measure.pi fun _ : Fin J => circularVectorLaw (PathSite p.W p.n))
  have h3 := (MeasurePreserving.id (pathLaw p.W (probePathLength p.n) p.b)).prod
    (Measure.measurePreserving_swap (μ := collarLaw p.W p.b)
      (ν := Measure.pi fun _ : Fin J => circularVectorLaw (PathSite p.W p.n)))
  have h4 : MeasurePreserving
      (fun x : PathSample p.W (probePathLength p.n) × ((Fin J → PathSite p.W p.n → ℂ) ×
        CollarSample p.W) => ((x.1, x.2.1), x.2.2))
      ((pathLaw p.W (probePathLength p.n) p.b).prod
        ((Measure.pi fun _ : Fin J => circularVectorLaw (PathSite p.W p.n)).prod (collarLaw p.W p.b)))
      ((oldProbeLaw p.W p.n J p.b).prod (collarLaw p.W p.b)) :=
    ⟨(MeasurableEquiv.prodAssoc : (PathSample p.W (probePathLength p.n) ×
        (Fin J → PathSite p.W p.n → ℂ)) × CollarSample p.W ≃ᵐ _).symm.measurable, by
      unfold oldProbeLaw
      rw [← Measure.prodAssoc_prod (μ := pathLaw p.W (probePathLength p.n) p.b)
        (ν := Measure.pi fun _ : Fin J => circularVectorLaw (PathSite p.W p.n))
        (τ := collarLaw p.W p.b)]
      exact MeasurableEquiv.map_symm_map MeasurableEquiv.prodAssoc⟩
  exact h4.comp (h3.comp (h2.comp h1))

theorem measurable_probeColumns (W n : ℕ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) :
    Measurable fun g : Fin J → PathSite W n → ℂ => probeColumns W n Q g := by
  refine Measurable.of_eval_matrix _ fun x c => ?_
  simp only [probeColumns, Matrix.of_apply, globalProbeVector]
  exact measurable_const.mul ((measurable_pi_apply x).comp (measurable_pi_apply c))

theorem measurable_leadColumns (b E : ℝ) (W n J : ℕ) (Q : Fin J → C(Torus, ℝ)) :
    Measurable fun o : PathSample W (probePathLength n) × (Fin J → PathSite W n → ℂ) =>
      leadColumns b E o.1 (probeColumns W n Q o.2) := by
  have hX : Measurable fun o : PathSample W (probePathLength n) × (Fin J → PathSite W n → ℂ) =>
      pathSchur E o.1 := (BlockBand.Layers.measurable_pathSchur W (probePathLength n) E).comp measurable_fst
  have hP : Measurable fun o : PathSample W (probePathLength n) × (Fin J → PathSite W n → ℂ) =>
      pathPortCoupling o.1 :=
    (BlockBand.Layers.measurable_pathPortCoupling W (probePathLength n)).comp measurable_fst
  have hM : Measurable fun o : PathSample W (probePathLength n) × (Fin J → PathSite W n → ℂ) =>
      pathMatrix o.1 := (BlockBand.Layers.measurable_pathMatrix W (probePathLength n)).comp measurable_fst
  have hZ : Measurable fun o : PathSample W (probePathLength n) × (Fin J → PathSite W n → ℂ) =>
      probeColumns W n Q o.2 := (measurable_probeColumns W n Q).comp measurable_snd
  unfold leadColumns
  exact measurable_matrix_mul' (measurable_matrix_conjTranspose' (measurable_matrix_inv'
    (measurable_matrix_sub' measurable_const hX)))
    (measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hP)
      (measurable_matrix_inv' (measurable_matrix_sub' hM measurable_const))) hZ)

end Probes

/-!
## Almost-sure validity of the finite-width identity
-/

section Good

variable {W : ℕ}

/-- The four invertibility conditions of `omittedRingSourceMatrix_eq_closedSourceMatrix` hold
`pathLaw ⊗ collarLaw`-a.s. -/
theorem ae_ringGood {b : ℝ} (hb : b < 1 / 2) (hW : 0 < W) (E : ℝ) (hη : 0 < (boundaryZ b E).im)
    (r : ℕ) :
    ∀ᵐ q ∂(pathLaw W r b).prod (collarLaw W b),
      IsUnit (pathMatrix q.1 - (E : ℂ) • 1).det ∧ IsUnit (q.2.2 - (E : ℂ) • 1).det ∧
      IsUnit (BlockBand.Critical.MatrixClosing.middleReaction b E 0 q.2 +
        (((boundaryZ b E).im : ℂ) * Complex.I) • 1).det ∧
      IsUnit (collarEndSchur b E q.2 - pathSchur E q.1).det := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := pathLaw W r b) (ν := collarLaw W b)).ae
    (BlockBand.Layers.ae_isUnit_det_pathMatrix W r hb E)
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := pathLaw W r b) (ν := collarLaw W b)).ae
    (BlockBand.Critical.Collar.Kernel.ae_isUnit_det_middleBlock (W := W) hb E 0)
  have h3 := (Measure.quasiMeasurePreserving_snd (μ := pathLaw W r b) (ν := collarLaw W b)).ae
    (ae_isUnit_middleReaction_add (W := W) b E hη)
  have hm : Measurable fun q : PathSample W r × CollarSample W =>
      (collarEndSchur b E q.2 - pathSchur E q.1).det :=
    (continuous_id.matrix_det).measurable.comp (measurable_matrix_sub'
      ((measurable_collarEndSchur b E).comp measurable_snd)
      ((BlockBand.Layers.measurable_pathSchur W r E).comp measurable_fst))
  have hset : MeasurableSet {q : PathSample W r × CollarSample W |
      IsUnit (collarEndSchur b E q.2 - pathSchur E q.1).det} := by
    simp_rw [isUnit_iff_ne_zero]
    exact hm (measurableSet_singleton 0).compl
  have h4 : ∀ᵐ q ∂(pathLaw W r b).prod (collarLaw W b),
      IsUnit (collarEndSchur b E q.2 - pathSchur E q.1).det := by
    rw [Measure.ae_prod_iff_ae_ae hset]
    exact Filter.Eventually.of_forall fun π => ae_isUnit_collarEndSchur_sub hb hW E (pathSchur E π)
  filter_upwards [h1, h2, h3, h4] with q h1 h2 h3 h4
  refine ⟨h1, ?_, h3, h4⟩
  simpa [BlockBand.Critical.Collar.Kernel.middleBlock] using h2

end Good

/-!
## Assembly
-/

section Assembly

open BlockBand.Critical.GlobalSource

/-- The old-data probe matrices have the law of the ring's probe matrices. -/
theorem integral_ringProbeMatrix_eq {p : Parameters} (model : p.GaussianRingModel) (b E : ℝ)
    {J : ℕ} (Q : Fin J → C(Torus, ℝ)) (φ : Matrix (Fin J) (Fin J) ℂ → ℝ) (hφ : Measurable φ) :
    ∫ x, φ (ringProbeMatrix p b E Q x) ∂ringProbeLaw model J =
      ∫ o, φ (pathProbeMatrix b E p.W p.n Q o) ∂oldProbeLaw p.W p.n J p.b := by
  have hpl : IsProbabilityMeasure (pathLaw p.W (probePathLength p.n) p.b) := by
    unfold probePathLength; infer_instance
  have hT : Measurable (Prod.map (ringPathSample p) (id : (Fin J → PathSite p.W p.n → ℂ) → _)) :=
    (measurable_ringPathSample p).prodMap measurable_id
  have hmap : Measure.map (Prod.map (ringPathSample p) id) (ringProbeLaw model J) =
      oldProbeLaw p.W p.n J p.b := by
    unfold ringProbeLaw oldProbeLaw
    rw [← Measure.map_prod_map _ _ (measurable_ringPathSample p) measurable_id,
      map_ringPathSample model, Measure.map_id]
  have hm : Measurable fun o => φ (pathProbeMatrix b E p.W p.n Q o) :=
    hφ.comp (measurable_pathProbeMatrix b E p.W p.n Q)
  rw [← hmap, integral_map hT.aemeasurable hm.aestronglyMeasurable]
  rfl

/-- **The finite-width identity under the integral**: the phase expectation with the collar-omitted
probes equals the expectation over `oldProbeLaw ⊗ collarLaw` of the phase of
`closedSourceMatrix b E 𝒦_W (closingMatrix b E 0 X F ω_c)`, for any measurable polar frame map. -/
theorem integral_omittedPhase_eq {p : Parameters} (model : p.GaussianRingModel) (E : ℝ)
    (hη : 0 < (boundaryZ p.b E).im) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) (σ : Fin J → ℤˣ)
    (Fr : Matrix (Fin 2 × Fin p.W) (Fin J) ℂ → Matrix (Fin 2 × Fin p.W) (Fin J) ℂ)
    (hFrm : Measurable Fr) (hFr : ∀ V, V = Fr V * cfc Real.sqrt (Vᴴ * V)) :
    ∫ x, closedSourcePhase σ (omittedRingSourceMatrix p E Q x.1 x.2) ∂fullRingProbeLaw model J =
      ∫ q, closedSourcePhase σ (closedSourceMatrix p.b E (pathProbeMatrix p.b E p.W p.n Q q.1)
        (BlockBand.Critical.MatrixClosing.closingMatrix p.b E 0 (pathSchur E q.1.1)
          (Fr (leadColumns p.b E q.1.1 (probeColumns p.W p.n Q q.1.2))) q.2))
        ∂(oldProbeLaw p.W p.n J p.b).prod (collarLaw p.W p.b) := by
  have hT := measurePreserving_ringOldCollar model J
  have hXm : Measurable fun o : PathSample p.W (probePathLength p.n) ×
      (Fin J → PathSite p.W p.n → ℂ) => pathSchur E o.1 :=
    (BlockBand.Layers.measurable_pathSchur _ _ E).comp measurable_fst
  have hΦm : Measurable fun q : (PathSample p.W (probePathLength p.n) ×
      (Fin J → PathSite p.W p.n → ℂ)) × CollarSample p.W =>
      closedSourcePhase σ (closedSourceMatrix p.b E (pathProbeMatrix p.b E p.W p.n Q q.1)
        (BlockBand.Critical.MatrixClosing.closingMatrix p.b E 0 (pathSchur E q.1.1)
          (Fr (leadColumns p.b E q.1.1 (probeColumns p.W p.n Q q.1.2))) q.2)) :=
    by
    have hK : Measurable fun q : (PathSample p.W (probePathLength p.n) ×
        (Fin J → PathSite p.W p.n → ℂ)) × CollarSample p.W =>
        pathProbeMatrix p.b E p.W p.n Q q.1 :=
      (measurable_pathProbeMatrix p.b E p.W p.n Q).comp measurable_fst
    have hF : Measurable fun o : PathSample p.W (probePathLength p.n) ×
        (Fin J → PathSite p.W p.n → ℂ) => Fr (leadColumns p.b E o.1 (probeColumns p.W p.n Q o.2)) :=
      hFrm.comp (measurable_leadColumns p.b E p.W p.n J Q)
    have hC := measurable_closingMatrix_prod (W := p.W) (Ω := PathSample p.W (probePathLength p.n) ×
      (Fin J → PathSite p.W p.n → ℂ)) p.b E hXm hF
    have h3 := (measurable_closedSourcePhase_closedSourceMatrix (J := J) p.b E σ).comp (hK.prodMk hC)
    exact h3
  have hgood := (measurePreserving_ringPath_collar model).quasiMeasurePreserving.ae
    (ae_ringGood p.b_lt_half p.W_pos E hη (probePathLength p.n))
  have hherm := ae_isHermitian_isRingBanded model
  have hae : ∀ᵐ x ∂fullRingProbeLaw model J,
      closedSourcePhase σ (omittedRingSourceMatrix p E Q x.1 x.2) =
        closedSourcePhase σ (closedSourceMatrix p.b E
          (pathProbeMatrix p.b E p.W p.n Q (ringOldCollar p x).1)
          (BlockBand.Critical.MatrixClosing.closingMatrix p.b E 0
            (pathSchur E (ringOldCollar p x).1.1)
            (Fr (leadColumns p.b E (ringOldCollar p x).1.1
              (probeColumns p.W p.n Q (ringOldCollar p x).1.2))) (ringOldCollar p x).2)) := by
    unfold fullRingProbeLaw
    filter_upwards [(Measure.quasiMeasurePreserving_fst).ae hgood,
      (Measure.quasiMeasurePreserving_fst).ae hherm] with x hx hH
    obtain ⟨h1, h2, h3, h4⟩ := hx
    rw [omittedRingSourceMatrix_eq_closedSourceMatrix p.b E hη Q hH.1 hH.2 x.2 h1 h2 h3 h4 _
      (hFr _)]
    rfl
  rw [integral_congr_ae hae]
  have := integral_map (μ := fullRingProbeLaw model J) hT.measurable.aemeasurable
    hΦm.aestronglyMeasurable
  rw [hT.map_eq] at this
  exact this.symm

/-- `d(X_path) → 0` in probability under the old-data law along a (shifted) critical sequence. -/
theorem tendsto_oldProbeLaw_matchedDistance (hMT : MatchedTracesContract) {b E : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) (hE : -2 < E ∧ E < 2) {τ : ℝ} (s : BlockBand.CriticalSequence τ) (N₀ J : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => oldProbeLaw (s.W (n + N₀)) (s.n (n + N₀)) J b
        {o | δ < matchedDistance b E (pathSchur E o.1)}) atTop (𝓝 0) := by
  have hWt : Tendsto (fun n => s.W (n + N₀)) atTop atTop :=
    s.width_tendsto.comp (tendsto_add_atTop_nat N₀)
  have h := tendsto_pathLaw_matchedDistance hMT hb hb' hE (T := τ + 1)
    (fun n => s.W (n + N₀)) (fun n => probePathLength (s.n (n + N₀))) hWt ?_ hδ
  · refine h.congr fun n => ?_
    have : IsProbabilityMeasure (pathLaw (s.W (n + N₀)) (probePathLength (s.n (n + N₀))) b) := by
      unfold probePathLength; infer_instance
    unfold oldProbeLaw
    rw [show {o : PathSample (s.W (n + N₀)) (probePathLength (s.n (n + N₀))) ×
        (Fin J → PathSite (s.W (n + N₀)) (s.n (n + N₀)) → ℂ) |
        δ < matchedDistance b E (pathSchur E o.1)} =
        {π | δ < matchedDistance b E (pathSchur E π)} ×ˢ Set.univ by ext; simp,
      Measure.prod_prod, measure_univ, mul_one]
  · have hr := ((s.ratio_tendsto.comp (tendsto_add_atTop_nat N₀)).eventually
      (gt_mem_nhds (show τ < τ + 1 by linarith)))
    filter_upwards [hr] with n hn
    have hW : (0 : ℝ) < s.W (n + N₀) := by exact_mod_cast s.W_pos _
    have h4 := s.n_ge_four (n + N₀)
    simp only [Function.comp_apply] at hn
    rw [div_lt_iff₀ hW] at hn
    refine ⟨by unfold probePathLength; omega, ?_⟩
    unfold probePathLength
    have : ((s.n (n + N₀) - 3 : ℕ) : ℝ) ≤ s.n (n + N₀) := by exact_mod_cast Nat.sub_le _ _
    linarith

/-- **The closed-source limit along a shifted critical sequence** (the shift `N₀` only makes the frames exist,
`J² ≤ 2W`). -/
theorem tendsto_omittedPhase_shift (hMC : BlockBand.Critical.MatrixClosing.MatrixClosingStatement)
    (hMT : MatchedTracesContract) {b E : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E ∧ E < 2)
    {τ : ℝ} {J : ℕ} (Q : Fin J → C(Torus, ℝ)) (κ : Measure (Matrix (Fin J) (Fin J) ℂ))
    [IsProbabilityMeasure κ] (hRing : IsRingProbeCriticalLimit b E hb hb' τ Q κ) (σ : Fin J → ℤˣ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Ξ : Ω → VaguePointMeasure (ℝ × (Fin J → ℂ))}
    {C : Ω → Matrix (Fin J) (Fin J) ℂ} (hC : IsCanonicalCauchyAtZero J P Ξ C)
    (s : BlockBand.CriticalSequence τ) (R : ∀ j, BlockBand.FiniteRealization (s.parameters b hb hb' j))
    (N₀ : ℕ) (hN₀ : ∀ n, J * J ≤ Fintype.card (Fin 2 × Fin (s.W (n + N₀)))) :
    Tendsto (fun n => ∫ x, closedSourcePhase σ
        (omittedRingSourceMatrix (s.parameters b hb hb' (n + N₀)) E Q x.1 x.2)
        ∂fullRingProbeLaw (R (n + N₀)).model J)
      atTop (𝓝 (∫ K, ∫ ω, closedSourcePhase σ (closedSourceMatrix b E K (C ω)) ∂P ∂κ)) := by
  have hη : 0 < (boundaryZ b E).im := etaZ_pos (by linarith) hE
  choose Fr hFrm hFr using fun n =>
    exists_measurable_polarFrame (ι := Fin 2 × Fin (s.W (n + N₀))) (J := J) (hN₀ n)
  have hWt : Tendsto (fun n => s.W (n + N₀)) atTop atTop :=
    s.width_tendsto.comp (tendsto_add_atTop_nat N₀)
  have hK : ∀ φ : Matrix (Fin J) (Fin J) ℂ →ᵇ ℝ, Tendsto (fun n =>
      ∫ o, φ (pathProbeMatrix b E (s.W (n + N₀)) (s.n (n + N₀)) Q o)
        ∂oldProbeLaw (s.W (n + N₀)) (s.n (n + N₀)) J b) atTop (𝓝 (∫ k, φ k ∂κ)) := by
    intro φ
    have h := (hRing s R (φ.compContinuous ⟨Prod.fst, continuous_fst⟩)).comp
      (tendsto_add_atTop_nat N₀)
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk]
    exact integral_ringProbeMatrix_eq (R (n + N₀)).model b E Q φ φ.continuous.measurable
  have main := tendsto_closedPhase_of_oldData hMC hb hb' hE σ hC
    (Ωo := fun n => PathSample (s.W (n + N₀)) (probePathLength (s.n (n + N₀))) ×
      (Fin J → PathSite (s.W (n + N₀)) (s.n (n + N₀)) → ℂ))
    (fun n => oldProbeLaw (s.W (n + N₀)) (s.n (n + N₀)) J b)
    (fun n => s.W (n + N₀)) (fun n => s.W_pos _) hWt
    (fun n o => pathSchur E o.1)
    (fun n => (BlockBand.Layers.measurable_pathSchur _ _ E).comp measurable_fst)
    (fun n => (Measure.quasiMeasurePreserving_fst).ae
      (BlockBand.Layers.srec_ae_pathSchur_isHermitian _ _ b E))
    (fun n o => Fr n (leadColumns b E o.1 (probeColumns _ _ Q o.2)))
    (fun n => (hFrm n).comp (measurable_leadColumns b E _ _ J Q))
    (fun n => Filter.Eventually.of_forall fun o => (hFr n _).1)
    (fun δ hδ => tendsto_oldProbeLaw_matchedDistance hMT hb hb' hE s N₀ J hδ)
    (fun n o => pathProbeMatrix b E (s.W (n + N₀)) (s.n (n + N₀)) Q o)
    (fun n => measurable_pathProbeMatrix b E _ _ Q) κ hK
  refine main.congr fun n => ?_
  exact (integral_omittedPhase_eq (p := s.parameters b hb hb' (n + N₀)) (R (n + N₀)).model E hη
    Q σ (Fr n) (hFrm n) (fun V => (hFr n V).2)).symm

/-- `ClosedSourceLimitStep` from `MatchedTracesContract` (its path clause: `d(X_path) → 0` in
probability for the old path). -/
theorem closedSourceLimitStep_holds (hMT : MatchedTracesContract) : ClosedSourceLimitStep := by
  intro hMC b E hb hb' hE τ J Q _hQ κ _hκ hRing σ Ω _ P Ξ C hC s R
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n, J * J ≤ Fintype.card (Fin 2 × Fin (s.W (n + N₀))) := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (s.width_tendsto.eventually_ge_atTop (J * J))
    refine ⟨N, fun n => ?_⟩
    have := hN (n + N) (by omega)
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  rw [← Filter.tendsto_add_atTop_iff_nat N₀]
  exact tendsto_omittedPhase_shift hMC hMT hb hb' hE Q κ hRing σ hC s R N₀ hN₀

/-- **The entire law theorem** (`EntireLawContract`) from `GlobalGaussianSourceStatement`,
`MatrixClosingStatement`, the PSSS source input `SourceContract` and `MatchedTracesContract`; the
step `ClosedSourceLimitStep` is `closedSourceLimitStep_holds`. -/
theorem entireLaw_of_matrixClosing
    (hGS : BlockBand.Critical.GlobalSource.GlobalGaussianSourceStatement)
    (hMC : BlockBand.Critical.MatrixClosing.MatrixClosingStatement)
    (source : BlockBand.External.PSSS.SourceContract.{0}) (hMT : MatchedTracesContract) :
    EntireLawContract :=
  entireLaw_of_closing_source hGS hMC source (closedSourceLimitStep_holds hMT)

end Assembly

end BlockBand.Critical.EntireLaw
