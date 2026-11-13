module

public import BlockBand.Endpoints.Sine.MicroscopicTagStepsRegular

/-!
# Steps 1–2 of the microscopic tag comparison: the one-block Palm reduction

In Step 1 of the proof, the observable is taken in its expectation in the Palm law of the mass on
block `0`, so the one-block coarea formula of the physical lead-profile theorem applies to it;
Step 2 uses the Gaussian ratios theorem formulated for the general regular fresh deformation.

The one-block angular measure `blockSectorFiber` (fixed exterior `ω = (H_R, C)`, energy `e`,
sector `ℓ`, on `projectiveHaar (BlockSite p k) ⊗ GUE_{W-1}(c/W)`, frame `U_v`) is identified with
the fresh eigenpair density `freshEigenpairFiber` of the deterministic deformation
`F = blockDeformation σ ω e` (the reindexed `F(e) = -C*(H_R - e)⁻¹C`) at variance `t = c/N`,
`N = |BlockSite p k| = W`, and hence, by `FreshEigenpairDensityContract.palm`
(`F = blockF(e)`, `c₀ = c`, `t = c/W`), with the scalar Palm weight `w_{ℓ,e}` (`palmWeight`,
`palmExpect`).

Ingredients: the reindexing `σ : BlockSite p k ≃ Fin N`; invariance of `projectiveHaar` (and of
`circularVectorLaw`) under reindexing (`mts_projectiveHaar_map_comp`); the transported frame
`mts_freshFrame` (`U'_v = U_{v∘σ}` reindexed, an `IsFreshFrame`); the identities
`U'*F U' = U*F(e)U` and `𝓡(e, v, F) = 𝓡(e, v∘σ, F(e))`; phase invariance of the observable,
expressed as `g(v∘σ) = f(vv*)` (an observable of the eigenprojector).

* `mts_blockSectorFiber_eq_fresh`: `𝒜⁰_{ℓ,e}[g] = freshEigenpairFiber F (c/N) ℓ U' e (g ∘ σ*)`.
* `mts_blockSectorFiber_eq_palm`: for `H_R` Hermitian and `g(v∘σ) = f(vv*)`,
  `𝒜⁰_{ℓ,e}[g] = E_{A⁰}[w_{ℓ,e} f(u_ℓu_ℓ*)]` (fresh traceless `A⁰` of `GUE_N(c/N)`).
* `mts_quadForm_eq_trace`: `v*Av = Re Tr(A vv*)`, the phase-invariant form of the clock
  observables (`v*D_jv`, `v*Dv`), used to produce `f` from quadratic-form observables.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal

/-!
## Reindexing invariance of the circular and projective laws
-/

theorem mts_measurable_comp_equiv {ι κ : Type*} (σ : ι ≃ κ) :
    Measurable (fun v : κ → ℂ => v ∘ σ) :=
  Measurable.of_eval fun a => measurable_pi_apply (σ a)

theorem mts_measurable_circularCombine (α : Type*) :
    Measurable (fun r : α × Fin 2 → ℝ => fun a => (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I) :=
  Measurable.of_eval fun a =>
    (Complex.measurable_ofReal.comp (measurable_pi_apply (a, 0))).add
      ((Complex.measurable_ofReal.comp (measurable_pi_apply (a, 1))).mul_const _)

theorem mts_l2Norm_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : ι ≃ κ) (v : κ → ℂ) :
    l2Norm (v ∘ σ) = l2Norm v := by
  unfold l2Norm
  congr 1
  exact σ.sum_comp (fun j => ‖v j‖ ^ 2)

theorem mts_measurable_l2Norm (ι : Type*) [Fintype ι] : Measurable (fun v : ι → ℂ => l2Norm v) := by
  unfold l2Norm
  exact (Real.continuous_sqrt.measurable).comp
    (Finset.measurable_sum _ fun i _ => (continuous_norm.measurable.comp
      (measurable_pi_apply i)).pow_const 2)

theorem mts_measurable_normalize (ι : Type*) [Fintype ι] :
    Measurable (fun g : ι → ℂ => ((l2Norm g)⁻¹ : ℂ) • g) := by
  refine Measurable.of_eval fun a => ?_
  exact ((Complex.measurable_ofReal.comp (mts_measurable_l2Norm ι)).inv).mul
    (measurable_pi_apply a)

/-- Reindexing preserves the standard circular Gaussian vector law. -/
theorem mts_circularVectorLaw_map_comp {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : ι ≃ κ) :
    (circularVectorLaw κ).map (fun v => v ∘ σ) = circularVectorLaw ι := by
  set e : ι × Fin 2 ≃ κ × Fin 2 := σ.prodCongr (Equiv.refl _)
  set T := MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl ℝ)
  have hT : MeasurePreserving T
      (Measure.pi fun _ : κ × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0))
      (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)) :=
    measurePreserving_arrowCongr' _ _ e.symm (MeasurableEquiv.refl ℝ)
      (fun _ => MeasurePreserving.id _)
  unfold circularVectorLaw
  rw [Measure.map_map (mts_measurable_comp_equiv σ) (mts_measurable_circularCombine κ)]
  have hfun : ((fun v : κ → ℂ => v ∘ σ) ∘
      (fun r : κ × Fin 2 → ℝ => fun a => (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I)) =
      (fun r : ι × Fin 2 → ℝ => fun a => (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I) ∘ T := by
    funext r a
    rfl
  rw [hfun, ← Measure.map_map (mts_measurable_circularCombine ι) T.measurable, hT.map_eq]

/-- Reindexing preserves the normalized projective Haar measure `ν_d`. -/
theorem mts_projectiveHaar_map_comp {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : ι ≃ κ) :
    (projectiveHaar κ).map (fun v => v ∘ σ) = projectiveHaar ι := by
  unfold projectiveHaar
  rw [Measure.map_map (mts_measurable_comp_equiv σ) (mts_measurable_normalize κ)]
  have hfun : ((fun v : κ → ℂ => v ∘ σ) ∘ (fun g : κ → ℂ => ((l2Norm g)⁻¹ : ℂ) • g)) =
      (fun g : ι → ℂ => ((l2Norm g)⁻¹ : ℂ) • g) ∘ (fun v : κ → ℂ => v ∘ σ) := by
    funext g
    simp only [Function.comp_apply, mts_l2Norm_comp_equiv]
    rfl
  rw [hfun, ← Measure.map_map (mts_measurable_normalize ι) (mts_measurable_comp_equiv σ),
    mts_circularVectorLaw_map_comp]

/-!
## Reindexing identities for the regression factor and the frame matrix
-/

theorem mts_reindex_mulVec {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : ι ≃ κ)
    (B : Matrix ι ι ℂ) (v : κ → ℂ) :
    Matrix.reindex σ σ B *ᵥ v = (B *ᵥ (v ∘ σ)) ∘ σ.symm := by
  rw [Matrix.reindex_apply, submatrix_mulVec_equiv]
  rfl

theorem mts_regressionFactor_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : ι ≃ κ)
    (t E : ℝ) (v : κ → ℂ) (B : Matrix ι ι ℂ) :
    regressionFactor t E v (Matrix.reindex σ σ B) = regressionFactor t E (v ∘ σ) B := by
  have ha : star v ⬝ᵥ (Matrix.reindex σ σ B *ᵥ v) = star (v ∘ σ) ⬝ᵥ (B *ᵥ (v ∘ σ)) := by
    rw [mts_reindex_mulVec, dotProduct_comp_equiv_symm]
    rfl
  have hl : ∀ c : ℂ, l2Norm (Matrix.reindex σ σ B *ᵥ v - c • v) =
      l2Norm (B *ᵥ (v ∘ σ) - c • (v ∘ σ)) := by
    intro c
    have : Matrix.reindex σ σ B *ᵥ v - c • v = (B *ᵥ (v ∘ σ) - c • (v ∘ σ)) ∘ σ.symm := by
      rw [mts_reindex_mulVec]
      funext x
      simp
    rw [this, mts_l2Norm_comp_equiv]
  unfold regressionFactor
  dsimp only
  rw [ha, hl]

theorem mts_reindex_conj {ι κ m : Type*} [Fintype ι] [Fintype κ] [Fintype m] (σ : ι ≃ κ)
    (A : Matrix ι m ℂ) (B : Matrix ι ι ℂ) :
    (Matrix.reindex σ (Equiv.refl m) A)ᴴ * Matrix.reindex σ σ B *
        Matrix.reindex σ (Equiv.refl m) A = Aᴴ * B * A := by
  simp only [Matrix.reindex_apply, conjTranspose_submatrix, Equiv.refl_symm, Equiv.coe_refl]
  rw [submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id]

/-!
## The transported frame
-/

variable (p : Parameters) (k : ZMod p.n)

/-- `BlockSite p k ≃ Fin W` (the internal coordinate). -/
def mts_blockSiteEquiv : BlockSite p k ≃ Fin p.W where
  toFun x := x.1.2
  invFun a := ⟨(k, a), rfl⟩
  left_inv x := by
    obtain ⟨⟨j, a⟩, h⟩ := x
    simp only at h
    subst h
    rfl
  right_inv _ := rfl

theorem mts_card_blockSite : Fintype.card (BlockSite p k) = p.W := by
  rw [Fintype.card_congr (mts_blockSiteEquiv p k), Fintype.card_fin]

/-- The fresh frame `U'_v = U_{v∘σ}` reindexed to `Fin N × Fin (N-1)`. -/
def mts_freshFrame {N : ℕ} (hN : N = p.W) (σ : BlockSite p k ≃ Fin N)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ) :
    (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ :=
  fun v => Matrix.reindex σ (finCongr (by rw [hN])) (U (v ∘ σ))

theorem mts_isFreshFrame {N : ℕ} (hN : N = p.W) (σ : BlockSite p k ≃ Fin N)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) : IsFreshFrame (mts_freshFrame p k hN σ U) := by
  subst hN
  refine ⟨?_, fun v hv => ?_⟩
  · have hc := hU.1.comp (mts_measurable_comp_equiv σ)
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    exact (measurable_pi_apply ((finCongr (rfl : p.W - 1 = p.W - 1)).symm y)).comp
      ((measurable_pi_apply (σ.symm x)).comp hc)
  · have hv' : l2Norm (v ∘ σ) = 1 := by rw [mts_l2Norm_comp_equiv]; exact hv
    obtain ⟨h1, h2⟩ := hU.2 (v ∘ σ) hv'
    simp only [mts_freshFrame, finCongr_refl]
    constructor
    · simp only [Matrix.reindex_apply, conjTranspose_submatrix, Equiv.refl_symm, Equiv.coe_refl]
      rw [submatrix_mul_equiv, h1, submatrix_id_id]
    · simp only [Matrix.reindex_apply, conjTranspose_submatrix, Equiv.refl_symm, Equiv.coe_refl]
      rw [submatrix_mulVec_equiv]
      have : v ∘ σ.symm.symm = v ∘ σ := rfl
      rw [this, h2]
      rfl

/-!
## The fiber identity
-/

/-- **The one-block angular sector measure is the fresh eigenpair density of the reindexed
deformation.** For every exterior `ω`, energy `e`, sector `ℓ` and `g ≥ 0`:
`𝒜⁰_{ℓ,e}[g] = freshEigenpairFiber (reindex σ σ F(e)) (c/N) ℓ U' e (g(· ∘ σ))`. -/
theorem mts_blockSectorFiber_eq_fresh {N : ℕ} (hN : N = p.W) (σ : BlockSite p k ≃ Fin N)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (e : ℝ) (ℓ : Fin N) (g : (BlockSite p k → ℂ) → ℝ≥0∞) :
    blockSectorFiber p k U ω e ℓ.val g =
      freshEigenpairFiber (Matrix.reindex σ σ (blockF p k ω e)) (Real.toNNReal (p.c / N)) ℓ
        (mts_freshFrame p k hN σ U) e (fun v _ => g (v ∘ σ)) := by
  subst hN
  classical
  set E := MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl ℂ)
  have hE : (fun v : Fin p.W → ℂ => v ∘ σ) = ⇑E := by funext v; rfl
  have hmap : (projectiveHaar (Fin p.W)).map E = projectiveHaar (BlockSite p k) := by
    rw [← hE]; exact mts_projectiveHaar_map_comp σ
  unfold blockSectorFiber freshEigenpairFiber
  rw [← hmap, lintegral_map_equiv]
  refine lintegral_congr fun v => ?_
  have hEv : E v = v ∘ σ := rfl
  rw [hEv]
  refine lintegral_congr fun G' => ?_
  have hM : freshFrameM (mts_freshFrame p k rfl σ U) (Matrix.reindex σ σ (blockF p k ω e)) e v G' =
      blockFrameM p k U ω e (v ∘ σ) G' := by
    unfold freshFrameM blockFrameM mts_freshFrame
    rw [finCongr_refl, mts_reindex_conj]
  rw [hM, mts_regressionFactor_reindex]
  rfl

/-!
## Hermitian deformation
-/

theorem mts_blockF_isHermitian (ω : BlockState p k) (hω : ω.1.IsHermitian) (e : ℝ) :
    (blockF p k ω e).IsHermitian := by
  unfold blockF physicalCoareaF physicalCoareaResolvent
  refine IsHermitian.sub (isHermitian_zero) ?_
  refine isHermitian_conjTranspose_mul_mul _ ?_
  refine IsHermitian.inv ?_
  refine hω.sub ?_
  simp [IsHermitian, conjTranspose_smul]

theorem mts_blockDeformation_isHermitian {N : ℕ} (σ : BlockSite p k ≃ Fin N)
    (ω : BlockState p k) (hω : ω.1.IsHermitian) (e : ℝ) :
    (Matrix.reindex σ σ (blockF p k ω e)).IsHermitian := by
  rw [Matrix.reindex_apply]
  exact (mts_blockF_isHermitian p k ω hω e).submatrix _

/-!
## The Palm reduction
-/

/-- **The one-block Palm reduction** (with `FreshEigenpairDensityContract.palm`, `F = blockF(e)`,
`c₀ = c`, `t = c/W`). Hypothesis: `FreshEigenpairDensityContract`. For every `p`, block `k`,
reindexing `σ : BlockSite p k ≃ Fin N` (`N = W`), measurable block frame `U`, exterior `ω` with
`H_R` Hermitian, energy `e`, sector `ℓ` and phase-invariant observable `g` (`g(v∘σ) = f(vv*)` for
every `v`, `f ≥ 0` measurable on projectors): `𝒜⁰_{ℓ,e}[g] = E_{A⁰}[w_{ℓ,e} f(u_ℓ u_ℓ*)]`, with
`w_{ℓ,e} = palmWeight` and `u_ℓ = freshEigenvector (F + A⁰) ℓ` for the reindexed deformation
`F = reindex σ σ F(e)` (`= blockDeformation p k σ ω e` when `N = |BlockSite p k|`). -/
theorem mts_blockSectorFiber_eq_palm (hFED : FreshEigenpairDensityContract) {N : ℕ}
    (hN : N = p.W) (σ : BlockSite p k ≃ Fin N)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (hω : ω.1.IsHermitian) (e : ℝ) (ℓ : Fin N)
    (f : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞) (hf : Measurable f)
    (g : (BlockSite p k → ℂ) → ℝ≥0∞) (hg : ∀ v : Fin N → ℂ, g (v ∘ σ) = f (vecMulVec v (star v))) :
    blockSectorFiber p k U ω e ℓ.val g =
      ∫⁻ A0, ENNReal.ofReal (palmWeight (Matrix.reindex σ σ (blockF p k ω e)) p.c e ℓ A0) *
          f (vecMulVec (freshEigenvector (Matrix.reindex σ σ (blockF p k ω e) + A0) ℓ)
            (star (freshEigenvector (Matrix.reindex σ σ (blockF p k ω e) + A0) ℓ)))
        ∂freshTracelessLaw N p.c := by
  have hN0 : 0 < N := by rw [hN]; exact p.W_pos
  rw [hFED.palm N hN0 _ (mts_blockDeformation_isHermitian p k σ ω hω e) p.c p.c_pos ℓ
    (mts_freshFrame p k hN σ U) (mts_isFreshFrame p k hN σ U hU) f hf e,
    mts_blockSectorFiber_eq_fresh p k hN σ U ω e ℓ g]
  congr 1
  funext v _
  exact hg v

/-- The Palm reduction for the reindexing of `BlockRegularEventContract`:
`F = blockDeformation p k σ ω e`, `N = |BlockSite p k|`. -/
theorem mts_blockSectorFiber_eq_palm_blockDeformation (hFED : FreshEigenpairDensityContract)
    (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (hω : ω.1.IsHermitian) (e : ℝ)
    (ℓ : Fin (Fintype.card (BlockSite p k)))
    (f : Matrix (Fin (Fintype.card (BlockSite p k))) (Fin (Fintype.card (BlockSite p k))) ℂ →
      ℝ≥0∞) (hf : Measurable f)
    (g : (BlockSite p k → ℂ) → ℝ≥0∞) (hg : ∀ v, g (v ∘ σ) = f (vecMulVec v (star v))) :
    blockSectorFiber p k U ω e ℓ.val g =
      ∫⁻ A0, ENNReal.ofReal (palmWeight (blockDeformation p k σ ω e) p.c e ℓ A0) *
          f (vecMulVec (freshEigenvector (blockDeformation p k σ ω e + A0) ℓ)
            (star (freshEigenvector (blockDeformation p k σ ω e + A0) ℓ)))
        ∂freshTracelessLaw (Fintype.card (BlockSite p k)) p.c :=
  mts_blockSectorFiber_eq_palm p k hFED (mts_card_blockSite p k) σ U hU ω hω e ℓ f hf g hg

/-!
## Phase invariance of quadratic-form observables
-/

/-- `v*Av = Re Tr(A vv*)`: quadratic forms are functions of the projector `vv*`. -/
theorem mts_quadForm_eq_trace {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    quadForm A v = (A * vecMulVec v (star v)).trace.re := by
  unfold quadForm
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec,
    Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mts_measurable_trace_re {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    Measurable (fun P : Matrix ι ι ℂ => (A * P).trace.re) := by
  have hc : Continuous (fun P : Matrix ι ι ℂ => (A * P).trace.re) :=
    Complex.continuous_re.comp ((continuous_const.matrix_mul continuous_id).matrix_trace)
  exact hc.measurable

/-!
## The normalized Palm expectation
-/

section PalmExpect

variable {N : ℕ}

theorem mts_measurable_add_left (F : Matrix (Fin N) (Fin N) ℂ) :
    Measurable (fun A0 : Matrix (Fin N) (Fin N) ℂ => F + A0) :=
  Measurable.of_eval fun i => Measurable.of_eval fun j =>
    measurable_const.add ((measurable_pi_apply j).comp (measurable_pi_apply i))

theorem mts_measurable_freshEigenvector (F : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) :
    Measurable (fun A0 : Matrix (Fin N) (Fin N) ℂ => freshEigenvector (F + A0) ℓ) :=
  Measurable.of_eval fun x =>
    (measurable_rawOrderedColumnSelection _ x).comp (mts_measurable_add_left F)

theorem mts_measurable_palmWeight (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N) :
    Measurable (fun A0 : Matrix (Fin N) (Fin N) ℂ => palmWeight F c₀ E ℓ A0) := by
  unfold palmWeight BlockBand.Palm.scalarWeight freshEigenvalue
  exact (measurable_gaussianPDFReal _ _).comp
    (measurable_const.sub ((measurable_rawIncreasingEigenvalue _).comp (mts_measurable_add_left F)))

theorem mts_palmWeight_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N)
    (A0 : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ palmWeight F c₀ E ℓ A0 :=
  BlockBand.Palm.scalarWeight_nonneg _ _ _ _

theorem mts_isProbabilityMeasure_freshTracelessLaw (N : ℕ) (c₀ : ℝ) :
    IsProbabilityMeasure (freshTracelessLaw N c₀) := by
  have := passDeriv_isProbabilityMeasure_gue (Fin N) (Real.toNNReal (c₀ / N))
  have hm : Measurable (fun G : Matrix (Fin N) (Fin N) ℂ => tracelessPart G) := by
    have hc : Continuous (fun G : Matrix (Fin N) (Fin N) ℂ => tracelessPart G) := by
      unfold tracelessPart
      exact continuous_id.sub ((continuous_const.mul continuous_id.matrix_trace).smul
        continuous_const)
    exact hc.measurable
  unfold freshTracelessLaw
  exact (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance

/-- For a bounded measurable `φ ≥ 0`, the Palm-weighted lower integral is the real one. -/
theorem mts_palm_lintegral_eq (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N)
    (φ : (Fin N → ℂ) → ℝ) (hφm : Measurable φ) (hφ0 : ∀ v, 0 ≤ φ v) {C : ℝ}
    (hφC : ∀ v, φ v ≤ C) :
    (∫⁻ A0, ENNReal.ofReal (palmWeight F c₀ E ℓ A0) *
        ENNReal.ofReal (φ (freshEigenvector (F + A0) ℓ)) ∂freshTracelessLaw N c₀) =
      ENNReal.ofReal (∫ A0, palmWeight F c₀ E ℓ A0 * φ (freshEigenvector (F + A0) ℓ)
        ∂freshTracelessLaw N c₀) := by
  have := mts_isProbabilityMeasure_freshTracelessLaw N c₀
  have hm : Measurable (fun A0 => palmWeight F c₀ E ℓ A0 * φ (freshEigenvector (F + A0) ℓ)) :=
    (mts_measurable_palmWeight F c₀ E ℓ).mul (hφm.comp (mts_measurable_freshEigenvector F ℓ))
  set K := (Real.sqrt (2 * Real.pi * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N))⁻¹
  have hi : Integrable (fun A0 => palmWeight F c₀ E ℓ A0 * φ (freshEigenvector (F + A0) ℓ))
      (freshTracelessLaw N c₀) := by
    refine Integrable.of_bound hm.aestronglyMeasurable (K * C) (ae_of_all _ fun A0 => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mts_palmWeight_nonneg F c₀ E ℓ A0)
      (hφ0 _))]
    exact mul_le_mul (BlockBand.Palm.scalarWeight_le_prefactor _ _ _ _) (hφC _) (hφ0 _)
      (inv_nonneg.2 (Real.sqrt_nonneg _))
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun A0 =>
    mul_nonneg (mts_palmWeight_nonneg F c₀ E ℓ A0) (hφ0 _))]
  refine lintegral_congr fun A0 => ?_
  rw [ENNReal.ofReal_mul (mts_palmWeight_nonneg F c₀ E ℓ A0)]

/-- `Σ_ℓ E[w_{ℓ,E} φ(u_ℓ)] = Z · Â[φ]` (also when the Palm mass `Z` vanishes). -/
theorem mts_palmMass_mul_palmExpect (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ)
    (φ : (Fin N → ℂ) → ℝ) :
    palmMass F c₀ E * palmExpect F c₀ E φ =
      ∑ ℓ : Fin N, ∫ A0, palmWeight F c₀ E ℓ A0 * φ (freshEigenvector (F + A0) ℓ)
        ∂freshTracelessLaw N c₀ := by
  unfold palmExpect
  by_cases hZ : palmMass F c₀ E = 0
  · rw [hZ, zero_mul]
    have := mts_isProbabilityMeasure_freshTracelessLaw N c₀
    set K := (Real.sqrt (2 * Real.pi * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N))⁻¹
    have hwi : ∀ ℓ, Integrable (fun A0 => palmWeight F c₀ E ℓ A0) (freshTracelessLaw N c₀) :=
      fun ℓ => Integrable.of_bound (mts_measurable_palmWeight F c₀ E ℓ).aestronglyMeasurable K
        (ae_of_all _ fun A0 => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mts_palmWeight_nonneg F c₀ E ℓ A0)]
          exact BlockBand.Palm.scalarWeight_le_prefactor _ _ _ _)
    have hz : ∀ ℓ, (∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀) = 0 := by
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun ℓ _ =>
        integral_nonneg (mts_palmWeight_nonneg F c₀ E ℓ))).1 hZ
      exact fun ℓ => h0 ℓ (Finset.mem_univ _)
    symm
    refine Finset.sum_eq_zero fun ℓ _ => ?_
    have hae := (integral_eq_zero_iff_of_nonneg (mts_palmWeight_nonneg F c₀ E ℓ) (hwi ℓ)).1
      (hz ℓ)
    have h0 : (fun A0 => palmWeight F c₀ E ℓ A0 * φ (freshEigenvector (F + A0) ℓ)) =ᵐ[
        freshTracelessLaw N c₀] 0 := by
      filter_upwards [hae] with A0 hA0
      simp only [Pi.zero_apply] at hA0 ⊢
      rw [hA0, zero_mul]
    rw [integral_congr_ae h0]
    simp
  · rw [mul_div_cancel₀ _ hZ]

/-- **The sector sum of the one-block angular measure is the Palm expectation.** Hypothesis:
`FreshEigenpairDensityContract`. For every `p`, block `k`, reindexing `σ : BlockSite p k ≃ Fin N`
(`N = W`), measurable block frame, exterior with `H_R` Hermitian and energy `e`, and every
bounded measurable `φ ≥ 0` on `ℂ^N` that is a function of the projector (`φ v = f(vv*)`, `f`
measurable): with `F = reindex σ σ F(e)`, `Σ_{ℓ < N} 𝒜⁰_{ℓ,e}[φ(· ∘ σ⁻¹)] = Z_F · Â_F[φ]`
(`palmMass`, `palmExpect`, variance `c₀ = c`). -/
theorem mts_sum_blockSectorFiber_eq_palmExpect (hFED : FreshEigenpairDensityContract)
    (hN : N = p.W) (σ : BlockSite p k ≃ Fin N)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (hω : ω.1.IsHermitian) (e : ℝ)
    (φ : (Fin N → ℂ) → ℝ) (hφ0 : ∀ v, 0 ≤ φ v) {C : ℝ} (hφC : ∀ v, φ v ≤ C)
    (f : Matrix (Fin N) (Fin N) ℂ → ℝ) (hf : Measurable f)
    (hφf : ∀ v, φ v = f (vecMulVec v (star v))) :
    (∑ ℓ : Fin N, blockSectorFiber p k U ω e ℓ.val (fun v => ENNReal.ofReal (φ (v ∘ σ.symm)))) =
      ENNReal.ofReal (palmMass (Matrix.reindex σ σ (blockF p k ω e)) p.c e *
        palmExpect (Matrix.reindex σ σ (blockF p k ω e)) p.c e φ) := by
  have hvv : Measurable (fun v : Fin N → ℂ => vecMulVec v (star v)) :=
    Measurable.of_eval fun i => Measurable.of_eval fun j =>
      (measurable_pi_apply i).mul (continuous_star.measurable.comp (measurable_pi_apply j))
  have hφm : Measurable φ := by
    have : φ = f ∘ fun v => vecMulVec v (star v) := funext hφf
    rw [this]; exact hf.comp hvv
  rw [mts_palmMass_mul_palmExpect _ p.c e φ,
    ENNReal.ofReal_sum_of_nonneg (fun ℓ _ => integral_nonneg fun A0 =>
      mul_nonneg (mts_palmWeight_nonneg _ _ _ _ _) (hφ0 _))]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← mts_palm_lintegral_eq _ p.c e ℓ φ hφm hφ0 hφC]
  simp only [hφf]
  refine mts_blockSectorFiber_eq_palm p k hFED hN σ U hU ω hω e ℓ
    (fun P => ENNReal.ofReal (f P)) (ENNReal.measurable_ofReal.comp hf) _ fun v => ?_
  simp only [Function.comp_def, Equiv.apply_symm_apply]

end PalmExpect

end BlockBand.Endpoints
