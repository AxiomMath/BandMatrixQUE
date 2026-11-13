module

public import BlockBand.Endpoints.Normalization.ExactPalmReal
public import BlockBand.Coarea.FixedOmegaCoarea

/-!
# Coarea angular measures as fresh-Palm laws

A bridge lemma between the angular sector measures stated in coarea vocabulary
(`pairSectorFiber`, `pairNormalizer`, `blockSectorFiber`, `blockNormalizer`:
`PairSite`/`BlockSite`, `projectiveHaar`, frames), and the fresh-Palm law (`palmWeight`,
`palmMass`, `palmExpect`: `Fin N`, `freshTracelessLaw`). It concerns the angular measure `𝒜_{ℓ,e}`
of the exact Palm proposition, the normalized unranked Palm law `Â` of the Gaussian ratios
theorem, and the remark after the fresh Palm theorem (the scalar Palm weight is the fresh
eigenpair density).

**Hypothesis.** `FreshEigenpairDensityContract`, field `palm` only, taken as the hypothesis `hD`
(proved as `freshEigenpairDensityContract_holds`). Nothing else is assumed.

**Measures, domain, uniformity.** Fixed exterior with Hermitian `H_R` (and Hermitian `V` for the
pair), every real energy `e` (no pole condition is needed), every measurable frame
(`IsPairFrame`/`IsBlockFrame`), every reindexing `σ : PairSite p i ≃ Fin (2W)` (resp.
`BlockSite p k ≃ Fin W`; canonical choices `FixedOmega.pairEquiv`, `blockEquiv`). Pair:
`c₀ = s = pairS p`, `N = 2W`, `t = pairTime p s = s/(2W) = c₀/N`; block: `c₀ = c`, `N = W`,
`t = blockTime p = c/W`. Measures: `projectiveHaar` and `GUE_{N-1}(t)` on the coarea side,
`freshTracelessLaw N c₀` on the Palm side. Exact identities, no error terms.

## Main results

* `sectorFiberOn_eq_freshEigenpairFiber` (unconditional reindexing): the angular sector
  measure of a frame `U` over `ι ≃ Fin N` equals the fresh eigenpair fiber of the reindexed
  deformation with the transported frame `transportFrame σ U`.
* (1) `pairSectorFiber_eq_palm`, `blockSectorFiber_eq_palm`: for measurable `f ≥ 0` of the
  projector, `𝒜_{ℓ,e}[f(vv*)] = E_{A⁰}[ofReal(w_{ℓ,e}) f(σ*(u_ℓu_ℓ*))]` with the deformation
  `reindex σ σ F(e)`.
* (2) `pairNormalizer_eq_palmMass`, `blockNormalizer_eq_palmMass`: `Z(e) = ofReal(palmMass)`
  (in particular `Z(e) < ∞`); `pairSectorFiberReal_eq_palm`, `blockSectorFiberReal_eq_palm`:
  the signed fibers are the signed Palm integrals; `pairSector_ratio_eq_palmExpect`,
  `blockSector_ratio_eq_palmExpect`: `(Σ_{ℓ<N} 𝒜_{ℓ,e}[φ(vv*)])/Z(e) = palmExpect F' c₀ e φ'`
  for bounded measurable real `φ` (both sides use the same totalized division, so no
  positivity of `Z(e)` is needed).
* (3) the block versions, as listed.

The bridge reindexes by `σ : PairSite ≃ Fin (2W)` (`Fin W` for a block). Tests must be
functions of the projector `vv*` and bounded on all matrices (clamp first).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate

/-!
## Generic angular sector measure over a reindexable site type
-/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)

/-- `M = U_v* F U_v + G' - e` for a frame with `n - 1` columns. -/
def frameMOn (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ) (F : Matrix ι ι ℂ) (e : ℝ)
    (v : ι → ℂ) (G' : Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ) :
    Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ :=
  (U v)ᴴ * F * U v + G' - (e : ℂ) • 1

/-- The angular sector measure `𝒜_{ℓ,e}[g]` on a site type `ι` (`|ι| = n`). -/
def sectorFiberOn (t : ℝ≥0) (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ) (F : Matrix ι ι ℂ)
    (e : ℝ) (ℓ : ℕ) (g : (ι → ℂ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ v, ∫⁻ G',
    ENNReal.ofReal (coareaConstant n t * regressionFactor t e v F *
        Complex.normSq (frameMOn n U F e v G').det) *
      (if negativeCount (frameMOn n U F e v G') = ℓ then 1 else 0) * g v
    ∂(gueMeasure (Fin (n - 1)) t) ∂(projectiveHaar ι)

/-- The signed angular sector measure (Bochner integrals). -/
def sectorFiberRealOn (t : ℝ≥0) (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ) (F : Matrix ι ι ℂ)
    (e : ℝ) (ℓ : ℕ) (g : (ι → ℂ) → ℝ) : ℝ :=
  ∫ v, ∫ G',
    coareaConstant n t * regressionFactor t e v F *
        Complex.normSq (frameMOn n U F e v G').det *
      (if negativeCount (frameMOn n U F e v G') = ℓ then 1 else 0) * g v
    ∂(gueMeasure (Fin (n - 1)) t) ∂(projectiveHaar ι)

/-- The unranked mass `Z(e)`. -/
def normalizerOn (t : ℝ≥0) (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ) (F : Matrix ι ι ℂ)
    (e : ℝ) : ℝ≥0∞ :=
  ∫⁻ v, ∫⁻ G',
    ENNReal.ofReal (coareaConstant n t * regressionFactor t e v F *
        Complex.normSq (frameMOn n U F e v G').det)
    ∂(gueMeasure (Fin (n - 1)) t) ∂(projectiveHaar ι)

/-- The frame transported along `σ : ι ≃ Fin n`: `U'_w = σ_* U_{w ∘ σ}`. -/
def transportFrame (σ : ι ≃ Fin n) (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ) :
    (Fin n → ℂ) → Matrix (Fin n) (Fin (n - 1)) ℂ :=
  fun w => Matrix.reindex σ (Equiv.refl _) (U (w ∘ σ))

theorem measurable_transportFrame (σ : ι ≃ Fin n) {U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ}
    (hU : Measurable U) : Measurable (transportFrame n σ U) := by
  have hc : Measurable fun w : Fin n → ℂ => w ∘ σ :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have hr : Measurable (fun M : Matrix ι (Fin (n - 1)) ℂ =>
      Matrix.reindex σ (Equiv.refl (Fin (n - 1))) M) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  exact hr.comp (hU.comp hc)

/-- The transported frame is a fresh frame. -/
theorem isFreshFrame_transportFrame (σ : ι ≃ Fin n) {U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ}
    (hUm : Measurable U)
    (hU : ∀ v : ι → ℂ, l2Norm v = 1 → (U v)ᴴ * U v = 1 ∧ (U v)ᴴ *ᵥ v = 0) :
    IsFreshFrame (transportFrame n σ U) := by
  refine ⟨measurable_transportFrame n σ hUm, fun w hw => ?_⟩
  unfold transportFrame
  have hw' : l2Norm (w ∘ σ) = 1 := by
    have := FixedOmega.l2Norm_comp_symm σ.symm w
    simpa using this.trans hw
  obtain ⟨h1, h2⟩ := hU (w ∘ σ) hw'
  constructor
  · rw [Matrix.conjTranspose_reindex]
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv _ _ _ σ.symm _]
    simp [h1]
  · funext j
    have := congrFun h2 j
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Function.comp_apply,
      Pi.zero_apply] at this ⊢
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply]
    rw [← this, ← σ.sum_comp]
    simp

/-- Reindexing the projector back. -/
theorem reindex_projector (σ : ι ≃ Fin n) (w : ι → ℂ) :
    Matrix.reindex σ.symm σ.symm (vecMulVec (w ∘ σ.symm) (star (w ∘ σ.symm))) =
      vecMulVec w (star w) := by
  ext a b
  simp [Matrix.reindex_apply, vecMulVec_apply]

/-- The fresh `M` of the transported data is the original `M`. -/
theorem freshFrameM_transport (σ : ι ≃ Fin n) (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ)
    (F : Matrix ι ι ℂ) (e : ℝ) (w : ι → ℂ) (G' : Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ) :
    freshFrameM (transportFrame n σ U) (Matrix.reindex σ σ F) e (w ∘ σ.symm) G' =
      frameMOn n U F e w G' := by
  have hU : transportFrame n σ U (w ∘ σ.symm) = Matrix.reindex σ (Equiv.refl _) (U w) := by
    unfold transportFrame
    congr 2
    funext a
    simp
  have hA : (Matrix.reindex σ (Equiv.refl (Fin (n - 1))) (U w))ᴴ * Matrix.reindex σ σ F *
      Matrix.reindex σ (Equiv.refl (Fin (n - 1))) (U w) = (U w)ᴴ * F * U w := by
    rw [Matrix.conjTranspose_reindex]
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv _ _ _ σ.symm _, Matrix.submatrix_mul_equiv _ _ _ σ.symm _]
    simp
  unfold freshFrameM frameMOn
  rw [hU, hA]

/-- **Reindexing identity** (unconditional): the angular sector measure over `ι` is the fresh
eigenpair fiber of `reindex σ σ F` with the transported frame. -/
theorem sectorFiberOn_eq_freshEigenpairFiber (σ : ι ≃ Fin n) (t : ℝ≥0)
    (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ) (F : Matrix ι ι ℂ) (e : ℝ) (ℓ : Fin n)
    (f : Matrix ι ι ℂ → ℝ≥0∞) :
    sectorFiberOn n t U F e ℓ.val (fun v => f (vecMulVec v (star v))) =
      freshEigenpairFiber (Matrix.reindex σ σ F) t ℓ (transportFrame n σ U) e
        (fun w _ => f (Matrix.reindex σ.symm σ.symm (vecMulVec w (star w)))) := by
  have hmap : (projectiveHaar ι).map (MeasurableEquiv.arrowCongr' σ
      (MeasurableEquiv.refl ℂ)) = projectiveHaar (Fin n) := by
    have := ProjectiveHaar.projectiveHaar_map_comp_equiv σ
    convert this using 2
    funext v
    rfl
  unfold freshEigenpairFiber
  rw [← hmap, MeasureTheory.lintegral_map_equiv]
  unfold sectorFiberOn
  refine lintegral_congr fun v => lintegral_congr fun G' => ?_
  have hv : (MeasurableEquiv.arrowCongr' σ (MeasurableEquiv.refl ℂ)) v = v ∘ σ.symm := rfl
  rw [hv, freshFrameM_transport, FixedOmega.regressionFactor_reindex]
  beta_reduce
  rw [reindex_projector]

/-- **Sector identity from `FreshEigenpairDensityContract.palm`.** -/
theorem sectorFiberOn_eq_palm (hD : FreshEigenpairDensityContract) (hn : 0 < n)
    (σ : ι ≃ Fin n) (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ) (hUm : Measurable U)
    (hU : ∀ v : ι → ℂ, l2Norm v = 1 → (U v)ᴴ * U v = 1 ∧ (U v)ᴴ *ᵥ v = 0)
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) (c₀ : ℝ) (hc₀ : 0 < c₀) (e : ℝ) (ℓ : Fin n)
    (f : Matrix ι ι ℂ → ℝ≥0∞) (hf : Measurable f) :
    sectorFiberOn n (Real.toNNReal (c₀ / n)) U F e ℓ.val (fun v => f (vecMulVec v (star v))) =
      ∫⁻ A0, ENNReal.ofReal (palmWeight (Matrix.reindex σ σ F) c₀ e ℓ A0) *
          f (Matrix.reindex σ.symm σ.symm
            (vecMulVec (freshEigenvector (Matrix.reindex σ σ F + A0) ℓ)
              (star (freshEigenvector (Matrix.reindex σ σ F + A0) ℓ))))
        ∂freshTracelessLaw n c₀ := by
  rw [sectorFiberOn_eq_freshEigenpairFiber n σ]
  have hre : Measurable (Matrix.reindex σ.symm σ.symm :
      Matrix (Fin n) (Fin n) ℂ → Matrix ι ι ℂ) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  exact (hD.palm n hn (Matrix.reindex σ σ F) (hF.submatrix σ.symm) c₀ hc₀ ℓ
    (transportFrame n σ U) (isFreshFrame_transportFrame n σ hUm hU)
    (fun X => f (Matrix.reindex σ.symm σ.symm X)) (hf.comp hre) e).symm

/-!
### Measurability
-/

theorem measurable_frameMOn_joint (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ) (hU : Measurable U)
    (F : Matrix ι ι ℂ) (e : ℝ) :
    Measurable fun q : (ι → ℂ) × Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ =>
      frameMOn n U F e q.1 q.2 := by
  have hU1 : Measurable fun q : (ι → ℂ) × Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ => U q.1 :=
    hU.comp measurable_fst
  unfold frameMOn
  exact FixedOmega.measurable_matrix_sub (FixedOmega.measurable_matrix_add
    (CoareaNative.BlockBand.measurable_matrix_mul_rect
      (CoareaNative.BlockBand.measurable_matrix_mul_rect
        (CoareaNative.BlockBand.Measurable.matrix_conjTranspose hU1) measurable_const) hU1)
    measurable_snd) measurable_const

theorem measurable_sectorIntegrandOn (t : ℝ≥0) (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ)
    (hU : Measurable U) (F : Matrix ι ι ℂ) (e : ℝ) (ℓ : ℕ) (g : (ι → ℂ) → ℝ≥0∞)
    (hg : Measurable g) :
    Measurable fun q : (ι → ℂ) × Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ =>
      ENNReal.ofReal (coareaConstant n t * regressionFactor t e q.1 F *
          Complex.normSq (frameMOn n U F e q.1 q.2).det) *
        (if negativeCount (frameMOn n U F e q.1 q.2) = ℓ then 1 else 0) * g q.1 := by
  have hM := measurable_frameMOn_joint n U hU F e
  have hR : Measurable fun q : (ι → ℂ) × Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ =>
      regressionFactor t e q.1 F :=
    (measurable_regressionFactor_joint (ι := ι) (t : ℝ)).comp
      (measurable_const.prodMk (measurable_fst.prodMk measurable_const))
  have hdet : Measurable fun q : (ι → ℂ) × Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ =>
      Complex.normSq (frameMOn n U F e q.1 q.2).det :=
    Complex.continuous_normSq.measurable.comp ((continuous_id.matrix_det).measurable.comp hM)
  have hind : Measurable fun q : (ι → ℂ) × Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ =>
      (if negativeCount (frameMOn n U F e q.1 q.2) = ℓ then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_eq_fun ((FixedOmega.measurable_negativeCount _).comp hM)
      measurable_const) measurable_const measurable_const
  exact ((ENNReal.measurable_ofReal.comp ((measurable_const.mul hR).mul hdet)).mul hind).mul
    (hg.comp measurable_fst)

/-- `Z(e) = Σ_{ℓ < n} 𝒜_{ℓ,e}[1]` (the sector indicators sum to one since `N_-(M) ≤ n - 1`). -/
theorem normalizerOn_eq_sum (hn : 0 < n) (t : ℝ≥0) (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ)
    (hU : Measurable U) (F : Matrix ι ι ℂ) (e : ℝ) :
    normalizerOn n t U F e = ∑ ℓ ∈ Finset.range n, sectorFiberOn n t U F e ℓ (fun _ => 1) := by
  have hmeas := fun ℓ : ℕ => measurable_sectorIntegrandOn n t U hU F e ℓ (fun _ => 1)
    measurable_const
  unfold normalizerOn sectorFiberOn
  rw [← lintegral_finsetSum']
  swap
  · intro ℓ _
    exact (hmeas ℓ).lintegral_prod_right'.aemeasurable
  refine lintegral_congr fun v => ?_
  rw [← lintegral_finsetSum']
  swap
  · intro ℓ _
    exact ((hmeas ℓ).comp measurable_prodMk_left).aemeasurable
  refine lintegral_congr fun G' => ?_
  have hlt : negativeCount (frameMOn n U F e v G') < n := by
    have h := negativeCount_le_card (frameMOn n U F e v G')
    rw [Fintype.card_fin] at h
    omega
  rw [Finset.sum_eq_single (negativeCount (frameMOn n U F e v G'))]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_range.2 hlt) h

/-- The signed sector measure as a difference of two nonnegative ones. -/
theorem sectorFiberRealOn_eq_toReal_sub (t : ℝ≥0) (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ)
    (hU : Measurable U) (F : Matrix ι ι ℂ) (e : ℝ) (ℓ : ℕ) (g hp hm : (ι → ℂ) → ℝ)
    (hpm : Measurable hp) (hmm : Measurable hm) (hp0 : ∀ v, 0 ≤ hp v) (hm0 : ∀ v, 0 ≤ hm v)
    (hg : ∀ v, g v = hp v - hm v)
    (hpf : sectorFiberOn n t U F e ℓ (fun v => ENNReal.ofReal (hp v)) ≠ ∞)
    (hmf : sectorFiberOn n t U F e ℓ (fun v => ENNReal.ofReal (hm v)) ≠ ∞) :
    sectorFiberRealOn n t U F e ℓ g =
      (sectorFiberOn n t U F e ℓ (fun v => ENNReal.ofReal (hp v))).toReal -
        (sectorFiberOn n t U F e ℓ (fun v => ENNReal.ofReal (hm v))).toReal := by
  have hmeas : ∀ h : (ι → ℂ) → ℝ, Measurable h →
      Measurable fun q : (ι → ℂ) × Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ =>
        ENNReal.ofReal (coareaConstant n t * regressionFactor t e q.1 F *
            Complex.normSq (frameMOn n U F e q.1 q.2).det) *
          (if negativeCount (frameMOn n U F e q.1 q.2) = ℓ then 1 else 0) *
          ENNReal.ofReal (h q.1) := fun h hh =>
    measurable_sectorIntegrandOn n t U hU F e ℓ (fun v => ENNReal.ofReal (h v))
      (ENNReal.measurable_ofReal.comp hh)
  unfold sectorFiberOn at hpf hmf
  unfold sectorFiberOn sectorFiberRealOn
  refine integral_integral_eq_toReal_sub _
    (fun v G' => ENNReal.ofReal (coareaConstant n t * regressionFactor t e v F *
            Complex.normSq (frameMOn n U F e v G').det) *
          (if negativeCount (frameMOn n U F e v G') = ℓ then 1 else 0) * ENNReal.ofReal (hp v))
    (fun v G' => ENNReal.ofReal (coareaConstant n t * regressionFactor t e v F *
            Complex.normSq (frameMOn n U F e v G').det) *
          (if negativeCount (frameMOn n U F e v G') = ℓ then 1 else 0) * ENNReal.ofReal (hm v))
    (ae_of_all _ fun v => ((hmeas hp hpm).comp measurable_prodMk_left).aemeasurable)
    (ae_of_all _ fun v => ((hmeas hm hmm).comp measurable_prodMk_left).aemeasurable)
    (hmeas hp hpm).lintegral_prod_right'.aemeasurable
    (hmeas hm hmm).lintegral_prod_right'.aemeasurable hpf hmf
    (ae_of_all _ fun v => ae_of_all _ fun G' => fun _ _ => ?_)
  have hw : 0 ≤ coareaConstant n t * regressionFactor t e v F *
      Complex.normSq (frameMOn n U F e v G').det :=
    mul_nonneg (mul_nonneg (by unfold coareaConstant; positivity) (Real.exp_pos _).le)
      (Complex.normSq_nonneg _)
  rw [hg v]
  split_ifs
  · simp only [mul_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal hw,
      ENNReal.toReal_ofReal (hp0 v), ENNReal.toReal_ofReal (hm0 v)]
    ring
  · simp only [mul_zero, zero_mul, ENNReal.toReal_zero, sub_zero]

end Generic

/-!
## Palm-side integrability
-/

section PalmSide

variable {N : ℕ}

theorem palmWeight_nonneg' (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N)
    (A0 : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ palmWeight F c₀ E ℓ A0 :=
  BlockBand.Palm.scalarWeight_nonneg _ _ _ _

theorem palmWeight_le_prefactor (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N)
    (A0 : Matrix (Fin N) (Fin N) ℂ) :
    palmWeight F c₀ E ℓ A0 ≤
      (Real.sqrt (2 * Real.pi * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N))⁻¹ :=
  BlockBand.Palm.scalarWeight_le_prefactor _ _ _ _

theorem measurable_palmWeight' (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N) :
    Measurable fun A0 => palmWeight F c₀ E ℓ A0 := by
  unfold palmWeight BlockBand.Palm.scalarWeight
  exact (measurable_gaussianPDFReal _ _).comp
    (measurable_const.sub ((measurable_rawIncreasingEigenvalue _).comp
      (FixedOmega.measurable_matrix_add measurable_const measurable_id)))

theorem measurable_freshProjector' (F : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) :
    Measurable fun A0 : Matrix (Fin N) (Fin N) ℂ =>
      vecMulVec (freshEigenvector (F + A0) ℓ) (star (freshEigenvector (F + A0) ℓ)) := by
  have hK : Measurable fun A0 : Matrix (Fin N) (Fin N) ℂ => F + A0 :=
    FixedOmega.measurable_matrix_add measurable_const measurable_id
  apply Measurable.of_eval_matrix
  intro a b
  simp only [freshEigenvector, vecMulVec_apply, Pi.star_apply]
  exact ((measurable_rawOrderedColumnSelection _ a).comp hK).mul
    (Complex.continuous_conj.measurable.comp ((measurable_rawOrderedColumnSelection _ b).comp hK))

instance isProbabilityMeasure_freshTracelessLaw' (c₀ : ℝ) :
    IsProbabilityMeasure (freshTracelessLaw N c₀) := by
  have hT : Continuous (tracelessPart (ι := Fin N)) := by
    unfold tracelessPart
    exact continuous_id.sub ((continuous_const.mul (continuous_id.matrix_trace)).smul
      continuous_const)
  unfold freshTracelessLaw
  exact (Measure.isProbabilityMeasure_map_iff hT.measurable.aemeasurable).2 inferInstance

/-- `w_{ℓ,E} h` is integrable for bounded measurable `h`. -/
theorem integrable_palmWeight_mul (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N)
    (h : Matrix (Fin N) (Fin N) ℂ → ℝ) (hm : Measurable h) (M : ℝ) (hM : ∀ x, |h x| ≤ M) :
    Integrable (fun A0 => palmWeight F c₀ E ℓ A0 * h A0) (freshTracelessLaw N c₀) := by
  refine ⟨((measurable_palmWeight' F c₀ E ℓ).mul hm).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := (Real.sqrt (2 * Real.pi *
      BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N))⁻¹ * M) (ae_of_all _ fun A0 => ?_)⟩
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (palmWeight_nonneg' F c₀ E ℓ A0)]
  exact mul_le_mul (palmWeight_le_prefactor F c₀ E ℓ A0) (hM A0) (abs_nonneg _)
    (by positivity)

/-- `∫⁻ ofReal(w) ofReal(h) = ofReal(∫ w h)` for bounded measurable `h ≥ 0`. -/
theorem lintegral_palm_eq_ofReal (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N)
    (h : Matrix (Fin N) (Fin N) ℂ → ℝ) (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x) (M : ℝ)
    (hM : ∀ x, |h x| ≤ M) :
    (∫⁻ A0, ENNReal.ofReal (palmWeight F c₀ E ℓ A0) * ENNReal.ofReal (h A0)
        ∂freshTracelessLaw N c₀) =
      ENNReal.ofReal (∫ A0, palmWeight F c₀ E ℓ A0 * h A0 ∂freshTracelessLaw N c₀) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_palmWeight_mul F c₀ E ℓ h hm M hM)
    (ae_of_all _ fun A0 => mul_nonneg (palmWeight_nonneg' F c₀ E ℓ A0) (h0 A0))]
  refine lintegral_congr fun A0 => ?_
  rw [ENNReal.ofReal_mul (palmWeight_nonneg' F c₀ E ℓ A0)]

/-- `∫⁻ ofReal(w) = ofReal(∫ w)`. -/
theorem lintegral_palmWeight_eq_ofReal (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ)
    (ℓ : Fin N) :
    (∫⁻ A0, ENNReal.ofReal (palmWeight F c₀ E ℓ A0) * 1 ∂freshTracelessLaw N c₀) =
      ENNReal.ofReal (∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀) := by
  have h := lintegral_palm_eq_ofReal F c₀ E ℓ (fun _ => 1) measurable_const
    (fun _ => zero_le_one) 1 (fun _ => by simp)
  simp only [ENNReal.ofReal_one, mul_one] at h
  simpa using h

theorem palmMass_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) : 0 ≤ palmMass F c₀ E :=
  Finset.sum_nonneg fun ℓ _ => integral_nonneg fun A0 => palmWeight_nonneg' F c₀ E ℓ A0

end PalmSide

/-!
## Generic consequences: normalizer, signed fibers, normalized Palm law
-/

section GenericPalm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)

/-- `Z(e) = ofReal(palmMass)`. -/
theorem normalizerOn_eq_palmMass (hD : FreshEigenpairDensityContract) (hn : 0 < n)
    (σ : ι ≃ Fin n) (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ) (hUm : Measurable U)
    (hU : ∀ v : ι → ℂ, l2Norm v = 1 → (U v)ᴴ * U v = 1 ∧ (U v)ᴴ *ᵥ v = 0)
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) (c₀ : ℝ) (hc₀ : 0 < c₀) (e : ℝ) :
    normalizerOn n (Real.toNNReal (c₀ / n)) U F e =
      ENNReal.ofReal (palmMass (Matrix.reindex σ σ F) c₀ e) := by
  rw [normalizerOn_eq_sum n hn _ U hUm, Finset.sum_range, palmMass,
    ENNReal.ofReal_sum_of_nonneg (fun ℓ _ =>
      integral_nonneg fun A0 => palmWeight_nonneg' _ c₀ e ℓ A0)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have h := sectorFiberOn_eq_palm n hD hn σ U hUm hU F hF c₀ hc₀ e ℓ (fun _ => 1)
    measurable_const
  rw [← lintegral_palmWeight_eq_ofReal]
  exact h

/-- The signed sector measure of `φ(vv*)` is the signed Palm integral, for bounded measurable
real `φ`. -/
theorem sectorFiberRealOn_eq_palm (hD : FreshEigenpairDensityContract) (hn : 0 < n)
    (σ : ι ≃ Fin n) (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ) (hUm : Measurable U)
    (hU : ∀ v : ι → ℂ, l2Norm v = 1 → (U v)ᴴ * U v = 1 ∧ (U v)ᴴ *ᵥ v = 0)
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) (c₀ : ℝ) (hc₀ : 0 < c₀) (e : ℝ) (ℓ : Fin n)
    (φ : Matrix ι ι ℂ → ℝ) (hφ : Measurable φ) (M : ℝ) (hM : ∀ X, |φ X| ≤ M) :
    sectorFiberRealOn n (Real.toNNReal (c₀ / n)) U F e ℓ.val
        (fun v => φ (vecMulVec v (star v))) =
      ∫ A0, palmWeight (Matrix.reindex σ σ F) c₀ e ℓ A0 *
          φ (Matrix.reindex σ.symm σ.symm
            (vecMulVec (freshEigenvector (Matrix.reindex σ σ F + A0) ℓ)
              (star (freshEigenvector (Matrix.reindex σ σ F + A0) ℓ))))
        ∂freshTracelessLaw n c₀ := by
  set F' := Matrix.reindex σ σ F
  have hre : Measurable (Matrix.reindex σ.symm σ.symm :
      Matrix (Fin n) (Fin n) ℂ → Matrix ι ι ℂ) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  set P : Matrix (Fin n) (Fin n) ℂ → Matrix ι ι ℂ := fun A0 =>
    Matrix.reindex σ.symm σ.symm (vecMulVec (freshEigenvector (F' + A0) ℓ)
      (star (freshEigenvector (F' + A0) ℓ))) with hP
  have hPm : Measurable P := hre.comp (measurable_freshProjector' F' ℓ)
  have hproj : Measurable fun v : ι → ℂ => vecMulVec v (star v) := by
    apply Measurable.of_eval_matrix
    intro a b
    simp only [vecMulVec_apply, Pi.star_apply]
    exact (measurable_pi_apply a).mul
      (Complex.continuous_conj.measurable.comp (measurable_pi_apply b))
  set φp : Matrix ι ι ℂ → ℝ := fun X => max (φ X) 0
  set φm : Matrix ι ι ℂ → ℝ := fun X => max (-φ X) 0
  have hφp : Measurable φp := hφ.max measurable_const
  have hφm : Measurable φm := hφ.neg.max measurable_const
  have hBp : ∀ X, |φp X| ≤ M := fun X => by
    rw [abs_of_nonneg (le_max_right _ _)]; exact max_zero_le_of_abs_le (hM X)
  have hBm : ∀ X, |φm X| ≤ M := fun X => by
    rw [abs_of_nonneg (le_max_right _ _)]; exact max_neg_zero_le_of_abs_le (hM X)
  -- the two nonnegative sector identities
  have key : ∀ ψ : Matrix ι ι ℂ → ℝ, Measurable ψ → (∀ X, 0 ≤ ψ X) → (∀ X, |ψ X| ≤ M) →
      sectorFiberOn n (Real.toNNReal (c₀ / n)) U F e ℓ.val
          (fun v => ENNReal.ofReal (ψ (vecMulVec v (star v)))) =
        ENNReal.ofReal (∫ A0, palmWeight F' c₀ e ℓ A0 * ψ (P A0) ∂freshTracelessLaw n c₀) := by
    intro ψ hψ hψ0 hψM
    have h := sectorFiberOn_eq_palm n hD hn σ U hUm hU F hF c₀ hc₀ e ℓ
      (fun X => ENNReal.ofReal (ψ X)) (ENNReal.measurable_ofReal.comp hψ)
    rw [h]
    exact lintegral_palm_eq_ofReal F' c₀ e ℓ (fun A0 => ψ (P A0)) (hψ.comp hPm)
      (fun _ => hψ0 _) M (fun _ => hψM _)
  have hp := key φp hφp (fun _ => le_max_right _ _) hBp
  have hm := key φm hφm (fun _ => le_max_right _ _) hBm
  rw [sectorFiberRealOn_eq_toReal_sub n _ U hUm F e ℓ.val _
    (fun v => φp (vecMulVec v (star v))) (fun v => φm (vecMulVec v (star v)))
    (hφp.comp hproj) (hφm.comp hproj) (fun _ => le_max_right _ _) (fun _ => le_max_right _ _)
    (fun v => (max_zero_sub_max_neg_zero _).symm)
    (by rw [hp]; exact ENNReal.ofReal_ne_top) (by rw [hm]; exact ENNReal.ofReal_ne_top),
    hp, hm,
    ENNReal.toReal_ofReal (integral_nonneg fun A0 =>
      mul_nonneg (palmWeight_nonneg' _ _ _ _ _) (le_max_right _ _)),
    ENNReal.toReal_ofReal (integral_nonneg fun A0 =>
      mul_nonneg (palmWeight_nonneg' _ _ _ _ _) (le_max_right _ _)),
    ← integral_sub (integrable_palmWeight_mul F' c₀ e ℓ (fun A0 => φp (P A0)) (hφp.comp hPm) M
        (fun _ => hBp _))
      (integrable_palmWeight_mul F' c₀ e ℓ (fun A0 => φm (P A0)) (hφm.comp hPm) M
        (fun _ => hBm _))]
  refine integral_congr_ae (ae_of_all _ fun A0 => ?_)
  simp only [φp, φm, ← mul_sub, max_zero_sub_max_neg_zero]
  rfl

/-- **The normalized unranked angular law is the fresh-Palm law**:
`(Σ_{ℓ<n} 𝒜_{ℓ,e}[φ(vv*)]) / Z(e) = palmExpect (reindex σ σ F) c₀ e φ'`. -/
theorem sector_ratio_eq_palmExpect (hD : FreshEigenpairDensityContract) (hn : 0 < n)
    (σ : ι ≃ Fin n) (U : (ι → ℂ) → Matrix ι (Fin (n - 1)) ℂ) (hUm : Measurable U)
    (hU : ∀ v : ι → ℂ, l2Norm v = 1 → (U v)ᴴ * U v = 1 ∧ (U v)ᴴ *ᵥ v = 0)
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) (c₀ : ℝ) (hc₀ : 0 < c₀) (e : ℝ)
    (φ : Matrix ι ι ℂ → ℝ) (hφ : Measurable φ) (M : ℝ) (hM : ∀ X, |φ X| ≤ M) :
    (∑ ℓ ∈ Finset.range n, sectorFiberRealOn n (Real.toNNReal (c₀ / n)) U F e ℓ
        (fun v => φ (vecMulVec v (star v)))) /
        (normalizerOn n (Real.toNNReal (c₀ / n)) U F e).toReal =
      palmExpect (Matrix.reindex σ σ F) c₀ e
        (fun u => φ (Matrix.reindex σ.symm σ.symm (vecMulVec u (star u)))) := by
  rw [normalizerOn_eq_palmMass n hD hn σ U hUm hU F hF c₀ hc₀ e,
    ENNReal.toReal_ofReal (palmMass_nonneg _ _ _), Finset.sum_range]
  unfold palmExpect
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  exact sectorFiberRealOn_eq_palm n hD hn σ U hUm hU F hF c₀ hc₀ e ℓ φ hφ M hM

end GenericPalm

/-!
## Hermitian Schur complements
-/

theorem physicalCoareaF_isHermitian' {α β : Type*} [Fintype α] [DecidableEq α]
    (H : Matrix α α ℂ) (C : Matrix α β ℂ) (V : Matrix β β ℂ) (hH : H.IsHermitian)
    (hV : V.IsHermitian) (e : ℝ) : (physicalCoareaF H C V e).IsHermitian := by
  unfold physicalCoareaF physicalCoareaResolvent
  exact hV.sub (Matrix.isHermitian_conjTranspose_mul_mul _ (ClockRank.shift_isHermitian hH e).inv)

/-!
## (1)–(2): the pair
-/

section Pair

variable (p : Parameters) (i : ZMod p.n)

theorem pairSectorFiber_eq_on
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (e : ℝ) (ℓ : ℕ) (g : (PairSite p i → ℂ) → ℝ≥0∞) :
    pairSectorFiber p i U ω e ℓ g =
      sectorFiberOn (2 * p.W) (pairTime p (pairS p)) U (physicalCoareaF ω.1 ω.2.1 ω.2.2 e)
        e ℓ g := rfl

theorem pairSectorFiberReal_eq_on
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (e : ℝ) (ℓ : ℕ) (g : (PairSite p i → ℂ) → ℝ) :
    pairSectorFiberReal p i U ω e ℓ g =
      sectorFiberRealOn (2 * p.W) (pairTime p (pairS p)) U
        (physicalCoareaF ω.1 ω.2.1 ω.2.2 e) e ℓ g := rfl

theorem pairNormalizer_eq_on
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (e : ℝ) :
    pairNormalizer p i U ω e =
      normalizerOn (2 * p.W) (pairTime p (pairS p)) U (physicalCoareaF ω.1 ω.2.1 ω.2.2 e) e :=
  rfl

/-- `t = s/(2W) = c₀/N` with `c₀ = s`, `N = 2W`. -/
theorem pairTime_pairS : pairTime p (pairS p) = Real.toNNReal (pairS p / ((2 * p.W : ℕ) : ℝ)) := by
  unfold pairTime
  push_cast
  rfl

theorem two_W_pos : 0 < 2 * p.W := by have := p.W_pos; omega

/-- **Pair: the sector identity.** Assumes `FreshEigenpairDensityContract.palm`. At a fixed
Hermitian exterior `ω`, every energy `e`, every measurable pair frame, every reindexing
`σ : PairSite ≃ Fin (2W)`, sector `ℓ < 2W` and measurable `f ≥ 0` of the projector:
`𝒜_{ℓ,e}[f(vv*)] = E_{A⁰ ~ freshTracelessLaw (2W) s}[ofReal(w_{ℓ,e}) f(σ^*(u_ℓu_ℓ*))]` with the
deformation `F' = reindex σ σ F(e)` and `c₀ = s = pairS p`. -/
theorem pairSectorFiber_eq_palm (hD : FreshEigenpairDensityContract)
    (σ : PairSite p i ≃ Fin (2 * p.W))
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (ω : SplitState p i) (hω : IsHermitianExterior p i ω) (e : ℝ) (ℓ : ℕ)
    (hℓ : ℓ < 2 * p.W) (f : PairMatrix p i → ℝ≥0∞) (hf : Measurable f) :
    pairSectorFiber p i U ω e ℓ (fun v => f (vecMulVec v (star v))) =
      ∫⁻ A0, ENNReal.ofReal (palmWeight (Matrix.reindex σ σ (physicalCoareaF ω.1 ω.2.1 ω.2.2 e))
            (pairS p) e ⟨ℓ, hℓ⟩ A0) *
          f (Matrix.reindex σ.symm σ.symm
            (vecMulVec
              (freshEigenvector (Matrix.reindex σ σ (physicalCoareaF ω.1 ω.2.1 ω.2.2 e) + A0)
                ⟨ℓ, hℓ⟩)
              (star (freshEigenvector
                (Matrix.reindex σ σ (physicalCoareaF ω.1 ω.2.1 ω.2.2 e) + A0) ⟨ℓ, hℓ⟩))))
        ∂freshTracelessLaw (2 * p.W) (pairS p) := by
  rw [pairSectorFiber_eq_on, pairTime_pairS]
  exact sectorFiberOn_eq_palm (2 * p.W) hD (two_W_pos p) σ U hU.1 hU.2 _
    (physicalCoareaF_isHermitian' _ _ _ hω.1 hω.2 e) (pairS p) (pairS_pos p) e ⟨ℓ, hℓ⟩ f hf

/-- **I3 (2), pair: the normalizer.** `Z(e) = ofReal(palmMass F' s e)` (in particular finite),
at a fixed Hermitian exterior, every energy, frame and reindexing. Consumes
`FreshEigenpairDensityContract.palm`. -/
theorem pairNormalizer_eq_palmMass (hD : FreshEigenpairDensityContract)
    (σ : PairSite p i ≃ Fin (2 * p.W))
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (ω : SplitState p i) (hω : IsHermitianExterior p i ω) (e : ℝ) :
    pairNormalizer p i U ω e =
      ENNReal.ofReal (palmMass (Matrix.reindex σ σ (physicalCoareaF ω.1 ω.2.1 ω.2.2 e))
        (pairS p) e) := by
  rw [pairNormalizer_eq_on, pairTime_pairS]
  exact normalizerOn_eq_palmMass (2 * p.W) hD (two_W_pos p) σ U hU.1 hU.2 _
    (physicalCoareaF_isHermitian' _ _ _ hω.1 hω.2 e) (pairS p) (pairS_pos p) e

/-- **I3 (2), pair: signed sector fibers.** For bounded measurable real `φ`,
`𝒜_{ℓ,e}[φ(vv*)]` (Bochner) is the signed Palm integral `E[w_{ℓ,e} φ(σ^*(u_ℓu_ℓ*))]`. -/
theorem pairSectorFiberReal_eq_palm (hD : FreshEigenpairDensityContract)
    (σ : PairSite p i ≃ Fin (2 * p.W))
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (ω : SplitState p i) (hω : IsHermitianExterior p i ω) (e : ℝ) (ℓ : ℕ)
    (hℓ : ℓ < 2 * p.W) (φ : PairMatrix p i → ℝ) (hφ : Measurable φ) (M : ℝ)
    (hM : ∀ X, |φ X| ≤ M) :
    pairSectorFiberReal p i U ω e ℓ (fun v => φ (vecMulVec v (star v))) =
      ∫ A0, palmWeight (Matrix.reindex σ σ (physicalCoareaF ω.1 ω.2.1 ω.2.2 e))
            (pairS p) e ⟨ℓ, hℓ⟩ A0 *
          φ (Matrix.reindex σ.symm σ.symm
            (vecMulVec
              (freshEigenvector (Matrix.reindex σ σ (physicalCoareaF ω.1 ω.2.1 ω.2.2 e) + A0)
                ⟨ℓ, hℓ⟩)
              (star (freshEigenvector
                (Matrix.reindex σ σ (physicalCoareaF ω.1 ω.2.1 ω.2.2 e) + A0) ⟨ℓ, hℓ⟩))))
        ∂freshTracelessLaw (2 * p.W) (pairS p) := by
  rw [pairSectorFiberReal_eq_on, pairTime_pairS]
  exact sectorFiberRealOn_eq_palm (2 * p.W) hD (two_W_pos p) σ U hU.1 hU.2 _
    (physicalCoareaF_isHermitian' _ _ _ hω.1 hω.2 e) (pairS p) (pairS_pos p) e ⟨ℓ, hℓ⟩
    φ hφ M hM

/-- **Pair: the normalized unranked angular law is the fresh-Palm law.** At a fixed Hermitian
exterior, every energy `e`, frame and reindexing, for bounded measurable real `φ`:
`(Σ_{ℓ<2W} 𝒜_{ℓ,e}[φ(vv*)]) / Z(e) = palmExpect (reindex σ σ F(e)) s e (φ ∘ σ^* ∘ proj)`.
Real division on both sides (no positivity of `Z(e)` is needed; `Z(e) < ∞` always).
Assumes `FreshEigenpairDensityContract.palm`. -/
theorem pairSector_ratio_eq_palmExpect (hD : FreshEigenpairDensityContract)
    (σ : PairSite p i ≃ Fin (2 * p.W))
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (ω : SplitState p i) (hω : IsHermitianExterior p i ω) (e : ℝ)
    (φ : PairMatrix p i → ℝ) (hφ : Measurable φ) (M : ℝ) (hM : ∀ X, |φ X| ≤ M) :
    (∑ ℓ ∈ Finset.range (2 * p.W),
        pairSectorFiberReal p i U ω e ℓ (fun v => φ (vecMulVec v (star v)))) /
        (pairNormalizer p i U ω e).toReal =
      palmExpect (Matrix.reindex σ σ (physicalCoareaF ω.1 ω.2.1 ω.2.2 e)) (pairS p) e
        (fun u => φ (Matrix.reindex σ.symm σ.symm (vecMulVec u (star u)))) := by
  simp only [pairSectorFiberReal_eq_on, pairNormalizer_eq_on, pairTime_pairS]
  exact sector_ratio_eq_palmExpect (2 * p.W) hD (two_W_pos p) σ U hU.1 hU.2 _
    (physicalCoareaF_isHermitian' _ _ _ hω.1 hω.2 e) (pairS p) (pairS_pos p) e φ hφ M hM

end Pair

/-!
## (3): one block
-/

section Block

variable (p : Parameters) (k : ZMod p.n)

/-- The canonical reindexing `BlockSite p k ≃ Fin W`, `(k, a) ↦ a`. -/
def blockEquiv : BlockSite p k ≃ Fin p.W where
  toFun x := x.1.2
  invFun a := ⟨(k, a), rfl⟩
  left_inv x := Subtype.ext (Prod.ext x.2.symm rfl)
  right_inv _ := rfl

theorem blockSectorFiber_eq_on
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (e : ℝ) (ℓ : ℕ) (g : (BlockSite p k → ℂ) → ℝ≥0∞) :
    blockSectorFiber p k U ω e ℓ g =
      sectorFiberOn p.W (Real.toNNReal (p.c / p.W)) U (blockF p k ω e) e ℓ g := rfl

theorem blockSectorFiberReal_eq_on
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (e : ℝ) (ℓ : ℕ) (g : (BlockSite p k → ℂ) → ℝ) :
    blockSectorFiberReal p k U ω e ℓ g =
      sectorFiberRealOn p.W (Real.toNNReal (p.c / p.W)) U (blockF p k ω e) e ℓ g := rfl

theorem blockNormalizer_eq_on
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (e : ℝ) :
    blockNormalizer p k U ω e =
      normalizerOn p.W (Real.toNNReal (p.c / p.W)) U (blockF p k ω e) e := rfl

theorem blockF_isHermitian (ω : BlockState p k) (hω : ω.1.IsHermitian) (e : ℝ) :
    (blockF p k ω e).IsHermitian :=
  physicalCoareaF_isHermitian' _ _ _ hω Matrix.isHermitian_zero e

/-- **I3 (3), block: the sector identity.** As `pairSectorFiber_eq_palm` for one fresh block
(`N = W`, `c₀ = c`, `t = blockTime p = c/W`, `F(e) = blockF`), at an exterior with Hermitian
`H_R`. Consumes `FreshEigenpairDensityContract.palm`. -/
theorem blockSectorFiber_eq_palm (hD : FreshEigenpairDensityContract)
    (σ : BlockSite p k ≃ Fin p.W)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (hω : ω.1.IsHermitian) (e : ℝ) (ℓ : ℕ)
    (hℓ : ℓ < p.W) (f : Matrix (BlockSite p k) (BlockSite p k) ℂ → ℝ≥0∞) (hf : Measurable f) :
    blockSectorFiber p k U ω e ℓ (fun v => f (vecMulVec v (star v))) =
      ∫⁻ A0, ENNReal.ofReal (palmWeight (Matrix.reindex σ σ (blockF p k ω e)) p.c e ⟨ℓ, hℓ⟩ A0) *
          f (Matrix.reindex σ.symm σ.symm
            (vecMulVec (freshEigenvector (Matrix.reindex σ σ (blockF p k ω e) + A0) ⟨ℓ, hℓ⟩)
              (star (freshEigenvector (Matrix.reindex σ σ (blockF p k ω e) + A0) ⟨ℓ, hℓ⟩))))
        ∂freshTracelessLaw p.W p.c := by
  rw [blockSectorFiber_eq_on]
  exact sectorFiberOn_eq_palm p.W hD p.W_pos σ U hU.1 hU.2 _ (blockF_isHermitian p k ω hω e)
    p.c p.c_pos e ⟨ℓ, hℓ⟩ f hf

/-- **I3 (3), block: the normalizer.** `Z₀(e) = ofReal(palmMass F' c e)`. -/
theorem blockNormalizer_eq_palmMass (hD : FreshEigenpairDensityContract)
    (σ : BlockSite p k ≃ Fin p.W)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (hω : ω.1.IsHermitian) (e : ℝ) :
    blockNormalizer p k U ω e =
      ENNReal.ofReal (palmMass (Matrix.reindex σ σ (blockF p k ω e)) p.c e) := by
  rw [blockNormalizer_eq_on]
  exact normalizerOn_eq_palmMass p.W hD p.W_pos σ U hU.1 hU.2 _
    (blockF_isHermitian p k ω hω e) p.c p.c_pos e

/-- **I3 (3), block: signed sector fibers.** -/
theorem blockSectorFiberReal_eq_palm (hD : FreshEigenpairDensityContract)
    (σ : BlockSite p k ≃ Fin p.W)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (hω : ω.1.IsHermitian) (e : ℝ) (ℓ : ℕ)
    (hℓ : ℓ < p.W) (φ : Matrix (BlockSite p k) (BlockSite p k) ℂ → ℝ) (hφ : Measurable φ)
    (M : ℝ) (hM : ∀ X, |φ X| ≤ M) :
    blockSectorFiberReal p k U ω e ℓ (fun v => φ (vecMulVec v (star v))) =
      ∫ A0, palmWeight (Matrix.reindex σ σ (blockF p k ω e)) p.c e ⟨ℓ, hℓ⟩ A0 *
          φ (Matrix.reindex σ.symm σ.symm
            (vecMulVec (freshEigenvector (Matrix.reindex σ σ (blockF p k ω e) + A0) ⟨ℓ, hℓ⟩)
              (star (freshEigenvector (Matrix.reindex σ σ (blockF p k ω e) + A0) ⟨ℓ, hℓ⟩))))
        ∂freshTracelessLaw p.W p.c := by
  rw [blockSectorFiberReal_eq_on]
  exact sectorFiberRealOn_eq_palm p.W hD p.W_pos σ U hU.1 hU.2 _
    (blockF_isHermitian p k ω hω e) p.c p.c_pos e ⟨ℓ, hℓ⟩ φ hφ M hM

/-- **I3 (3), block: the normalized unranked one-block angular law is the fresh-Palm law**:
`(Σ_{ℓ<W} 𝒜⁰_{ℓ,e}[φ(vv*)]) / Z₀(e) = palmExpect (reindex σ σ F(e)) c e (φ ∘ σ^* ∘ proj)`. -/
theorem blockSector_ratio_eq_palmExpect (hD : FreshEigenpairDensityContract)
    (σ : BlockSite p k ≃ Fin p.W)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (hω : ω.1.IsHermitian) (e : ℝ)
    (φ : Matrix (BlockSite p k) (BlockSite p k) ℂ → ℝ) (hφ : Measurable φ) (M : ℝ)
    (hM : ∀ X, |φ X| ≤ M) :
    (∑ ℓ ∈ Finset.range p.W,
        blockSectorFiberReal p k U ω e ℓ (fun v => φ (vecMulVec v (star v)))) /
        (blockNormalizer p k U ω e).toReal =
      palmExpect (Matrix.reindex σ σ (blockF p k ω e)) p.c e
        (fun u => φ (Matrix.reindex σ.symm σ.symm (vecMulVec u (star u)))) := by
  simp only [blockSectorFiberReal_eq_on, blockNormalizer_eq_on]
  exact sector_ratio_eq_palmExpect p.W hD p.W_pos σ U hU.1 hU.2 _
    (blockF_isHermitian p k ω hω e) p.c p.c_pos e φ hφ M hM

end Block

end BlockBand.Endpoints.Normalization
