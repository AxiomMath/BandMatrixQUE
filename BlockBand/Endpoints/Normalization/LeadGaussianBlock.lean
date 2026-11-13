module

public import BlockBand.Endpoints.Normalization.LeadGaussianEngine
public import BlockBand.Endpoints.Normalization.LeadProfileField
public import BlockBand.Endpoints.Normalization.LeadFieldLaw
public import BlockBand.Endpoints.Normalization.LeadProfileGamma

/-!
# The physical lead-profile theorem at a fixed exterior: Palm law versus the field `Mg`

**Main result** (`block_palm_field_comparison`, for each `(e, ω)`).
Fixed first: `b`, fresh constants `A, r₀, s₀, v₀` with `FreshConstants (1-2b) r₀ s₀ v₀`, `m`, a
continuous `ψ` on `[-1,1]^m` and `ε > 0`. There are `W₀` and `ω₀ ∈ (0,1/2]` such that for every
admissible `p` with `p.b = b`, `W ≥ W₀`, every block `k`, measurable block frame `U`, exterior
`ω` with Hermitian `H_R`, energy `|e| < 2` and reindexing `σ : BlockSite ≃ Fin (card)` with
* `F = blockDeformation σ ω e ∈ FreshClass F A c e r₀ s₀ v₀` (the first half of `IsBlockRegular`),
* `(1-ω₀)Γ₀ ⪯ Γ ⪯ (1+ω₀)Γ₀`, `Γ = freshGamma F c e`, `Γ₀ = reindex σ σ (c|z₀-Σ|^{-2})`,
and for every finite nonempty `S`, Hermitian `B_{s,j}` with `-D ⪯ B_{s,j} ⪯ D` (`D = clockForm`),
measurable defaults `d_s`, and every bounded measurable mass-vector observable `g` with
`|g(p(v,e)) - |S|⁻¹ Σ_s ψ(ratioCube B_s D d_s v)| ≤ δ` for all `v`:

`|Σ_ℓ 𝒜⁰_{ℓ,e}[g(p(v,e))] / Z₀(e) - E_{g'} g(p(Mg', e))| ≤ 2δ + 2ε`,

`g' ~ CN(0, I)` on block `k`, `M = blockFieldFactor ω e = √c(z₀-Σ)⁻¹`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

namespace LeadGaussian

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile
open scoped ComplexConjugate ComplexOrder

theorem continuous_quadForm_left {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℂ) :
    Continuous (quadForm Q) :=
  BlockBand.Endpoints.Clock.continuous_quadForm.comp (continuous_const.prodMk continuous_id)

theorem measurable_ratioCube {ι : Type*} [Fintype ι] {m : ℕ} (B : Fin m → Matrix ι ι ℂ)
    (D : Matrix ι ι ℂ) (d : (ι → ℂ) → Fin m → ℝ) (hd : Measurable d) :
    Measurable (ratioCube B D d) := by
  refine measurable_pi_iff.mpr fun j => ?_
  refine continuous_projIcc.measurable.comp ?_
  exact Measurable.ite (measurableSet_eq_fun (continuous_quadForm_left D).measurable
    measurable_const) ((measurable_pi_apply j).comp hd)
    ((continuous_quadForm_left (B j)).measurable.div (continuous_quadForm_left D).measurable)

theorem integral_circular_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : ι ≃ κ)
    (f : (ι → ℂ) → ℝ) (hf : Measurable f) :
    ∫ g, f (fun x => g (σ x)) ∂circularVectorLaw κ = ∫ g, f g ∂circularVectorLaw ι := by
  have hmap := BlockBand.Coarea.ProjectiveHaar.circularVectorLaw_map_comp_equiv σ.symm
  simp only [Equiv.symm_symm] at hmap
  have hm : Measurable (fun g : κ → ℂ => g ∘ ⇑σ) :=
    measurable_pi_iff.mpr fun x => measurable_pi_apply _
  rw [← hmap, integral_map hm.aemeasurable hf.aestronglyMeasurable]
  rfl

section Block

variable (p : Parameters) (k : ZMod p.n)

theorem measurable_blockReconMass (ω : BlockState p k) (e : ℝ) :
    Measurable (blockReconMass p k ω e) := by
  refine measurable_pi_iff.mpr fun j => ?_
  simp_rw [blockReconMass_eq]
  exact (continuous_quadForm_left _).measurable.div (continuous_quadForm_left _).measurable

theorem blockShifted_det_ne_zero (ω : BlockState p k) (hω : ω.1.IsHermitian) {e : ℝ}
    (he : |e| < 2) : (blockShifted p k ω e).det ≠ 0 := by
  have hF : (-blockF p k ω e).IsHermitian := (blockF_isHermitian p k ω hω e).neg
  have := BlockBand.Layers.resolvent_det_ne_zero (-blockF p k ω e) hF (commonZ p.b e)
    (LeadFieldLaw.commonZ_im_pos p he)
  rwa [sub_neg_eq_add] at this

theorem blockFieldFactor_ne_zero (ω : BlockState p k) (hω : ω.1.IsHermitian) {e : ℝ}
    (he : |e| < 2) : blockFieldFactor p k ω e ≠ 0 := by
  intro h0
  have hdet := blockShifted_det_ne_zero p k ω hω he
  have hc : 0 < p.c := by have := p.b_lt_half; unfold Parameters.c; linarith
  have hsq : ((Real.sqrt p.c : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hc).ne'
  have hinv : (blockShifted p k ω e)⁻¹ = 0 := by
    have := h0
    unfold blockFieldFactor at this
    exact (smul_eq_zero.mp this).resolve_left hsq
  have h1 := Matrix.nonsing_inv_mul (blockShifted p k ω e) (isUnit_iff_ne_zero.mpr hdet)
  rw [hinv, Matrix.zero_mul] at h1
  have hne : Nonempty (BlockSite p k) := ⟨⟨(k, ⟨0, p.W_pos⟩), rfl⟩⟩
  obtain ⟨x⟩ := hne
  have := congrFun (congrFun h1 x) x
  simp at this

/-- `reindex σ σ (LᴴL) = L'ᴴL'` with `L' = L ∘ σ⁻¹` on the columns. -/
theorem reindex_clockForm {N : ℕ} (σ : BlockSite p k ≃ Fin N) (ω : BlockState p k) (e : ℝ) :
    Matrix.reindex σ σ (clockForm p k ω e) =
      ((liftMatrix p k ω e).submatrix id σ.symm)ᴴ * (liftMatrix p k ω e).submatrix id σ.symm := by
  ext i j
  simp [clockForm, liftForm, reindex_apply, mul_apply]

theorem traceAgainst_reindex_clockForm_nonneg {N : ℕ} (σ : BlockSite p k ≃ Fin N)
    (ω : BlockState p k) (e : ℝ) (P : Matrix (Fin N) (Fin N) ℂ) (hP : P.PosSemidef) :
    0 ≤ traceAgainst P (Matrix.reindex σ σ (clockForm p k ω e)) := by
  rw [reindex_clockForm]
  set L' := (liftMatrix p k ω e).submatrix id σ.symm
  unfold traceAgainst
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have h := hP.conjTranspose_mul_mul_same L'ᴴ
  rw [conjTranspose_conjTranspose] at h
  exact (Complex.nonneg_iff.mp h.trace_nonneg).1

theorem traceAgainst_reindex_clockForm_pos {N : ℕ} (σ : BlockSite p k ≃ Fin N)
    (ω : BlockState p k) (hω : ω.1.IsHermitian) {e : ℝ} (he : |e| < 2) :
    0 < traceAgainst (Matrix.reindex σ σ (blockMatchedGamma p k ω e))
      (Matrix.reindex σ σ (clockForm p k ω e)) := by
  set M₀ := Matrix.reindex σ σ (blockFieldFactor p k ω e)
  have hdet := blockShifted_det_ne_zero p k ω hω he
  have hM₀ : M₀ * M₀ᴴ = Matrix.reindex σ σ (blockMatchedGamma p k ω e) := by
    rw [← leadField_covariance p k e ω hdet, LeadProfile.reindex_mul', ← conjTranspose_reindex]
  -- `D ⪰ 1`
  have hD1 : (Matrix.reindex σ σ (clockForm p k ω e) - 1).PosSemidef := by
    have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) = Matrix.reindex σ σ (blockForm p k ω e k) := by
      rw [blockForm_self]; simp
    rw [h1]
    have : Matrix.reindex σ σ (clockForm p k ω e) - Matrix.reindex σ σ (blockForm p k ω e k) =
        Matrix.reindex σ σ (liftForm p k ω e (fun y => 1 - if y.1 = k then 1 else 0)) := by
      rw [← liftForm_sub]; ext i j; simp [reindex_apply, clockForm, blockForm]
    rw [this]
    refine (liftForm_posSemidef p k ω e _ fun y => ?_).submatrix _
    split_ifs <;> norm_num
  have hge := BlockBand.Endpoints.Clock.CovarianceStability.traceAgainst_nonneg_of hM₀ hD1
  rw [BlockBand.Endpoints.Clock.CovarianceStability.traceAgainst_sub] at hge
  have hpos : 0 < traceAgainst (Matrix.reindex σ σ (blockMatchedGamma p k ω e)) 1 := by
    rw [BlockBand.Endpoints.Clock.CovarianceStability.traceAgainst_eq_trace_conj hM₀, Matrix.mul_one]
    have hne : M₀ ≠ 0 := by
      intro h0
      apply blockFieldFactor_ne_zero p k ω hω he
      have := congrArg (Matrix.reindex σ.symm σ.symm) h0
      simpa [M₀] using this
    have h0 := (Complex.nonneg_iff.mp (posSemidef_conjTranspose_mul_self M₀).trace_nonneg)
    rcases h0.1.eq_or_lt with h | h
    · exfalso
      apply hne
      apply (trace_conjTranspose_mul_self_eq_zero_iff).mp
      exact Complex.ext (by simpa using h.symm) (by simpa using h0.2.symm)
    · exact h
  linarith

/-- **Palm law versus the field `Mg` at a fixed exterior**. See the module docstring.
Assumes `FreshEigenpairDensityContract` and `GaussianRatiosContract`. -/
theorem block_palm_field_comparison (hD : FreshEigenpairDensityContract)
    (hGR : GaussianRatiosContract) (b : ℝ) (A r₀ s₀ v₀ : ℝ)
    (hfc : FreshConstants (1 - 2 * b) r₀ s₀ v₀) (m : ℕ) (ψ : C(Fin m → Set.Icc (-1 : ℝ) 1, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ W₀ : ℕ, ∃ ω₀ : ℝ, 0 < ω₀ ∧ ω₀ ≤ 1 / 2 ∧ ∀ (p : Parameters), p.b = b → W₀ ≤ p.W →
    ∀ (k : ZMod p.n) (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ),
      IsBlockFrame p k U → ∀ ω : BlockState p k, ω.1.IsHermitian → ∀ e : ℝ, |e| < 2 →
    ∀ σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)),
      FreshClass (blockDeformation p k σ ω e) A p.c e r₀ s₀ v₀ →
      ((((1 + ω₀ : ℝ) : ℂ) • Matrix.reindex σ σ (blockMatchedGamma p k ω e) -
          freshGamma (blockDeformation p k σ ω e) p.c e).PosSemidef ∧
        (freshGamma (blockDeformation p k σ ω e) p.c e -
          ((1 - ω₀ : ℝ) : ℂ) • Matrix.reindex σ σ (blockMatchedGamma p k ω e)).PosSemidef) →
    ∀ {S : Type} [Fintype S] [Nonempty S]
      (B : S → Fin m → Matrix (BlockSite p k) (BlockSite p k) ℂ),
      (∀ s j, IsSandwichedOn (B s j) (clockForm p k ω e)) →
    ∀ (d : S → (BlockSite p k → ℂ) → Fin m → ℝ), (∀ s, Measurable (d s)) →
    ∀ (g : (ZMod p.n → ℝ) → ℝ), Measurable g → ∀ Mg : ℝ, (∀ q, |g q| ≤ Mg) → ∀ δ : ℝ,
      (∀ v, |g (blockReconMass p k ω e v) - (Fintype.card S : ℝ)⁻¹ *
          ∑ s, ψ (ratioCube (B s) (clockForm p k ω e) (d s) v)| ≤ δ) →
      |(∑ ℓ ∈ Finset.range p.W,
            blockSectorFiberReal p k U ω e ℓ (fun v => g (blockReconMass p k ω e v))) /
          (blockNormalizer p k U ω e).toReal -
        ∫ g', g (blockReconMass p k ω e (blockFieldFactor p k ω e *ᵥ g'))
          ∂circularVectorLaw (BlockSite p k)| ≤ 2 * δ + 2 * ε := by
  obtain ⟨N₀, ω₀, hω₀, hω₀', hEng⟩ := palm_gaussian_cube_comparison hGR A (1 - 2 * b) r₀ s₀ v₀
    hfc m ψ ε hε
  refine ⟨N₀, ω₀, hω₀, hω₀', ?_⟩
  intro p hpb hW k U hU ω hω e he σ hF hclose S _ _ B hB d hd g hg Mg hMg δ hδ
  have hc : p.c = 1 - 2 * b := c_eq_of_b p hpb
  have hcard := card_blockSite_eq p k
  set F := blockDeformation p k σ ω e
  set D := clockForm p k ω e
  set D' := Matrix.reindex σ σ D
  set B' : S → Fin m → Matrix (Fin (Fintype.card (BlockSite p k)))
    (Fin (Fintype.card (BlockSite p k))) ℂ := fun s j => Matrix.reindex σ σ (B s j)
  set d' : S → (Fin (Fintype.card (BlockSite p k)) → ℂ) → Fin m → ℝ := fun s u => d s (fun x => u (σ x))
  set Mb := blockFieldFactor p k ω e
  set M₀ := Matrix.reindex σ σ Mb
  set Γ₀ := Matrix.reindex σ σ (blockMatchedGamma p k ω e)
  have hdet := blockShifted_det_ne_zero p k ω hω he
  have hM₀ : M₀ * M₀ᴴ = Γ₀ := by
    show M₀ * M₀ᴴ = Matrix.reindex σ σ (blockMatchedGamma p k ω e)
    rw [← leadField_covariance p k e ω hdet, LeadProfile.reindex_mul', ← conjTranspose_reindex]
  have hNpos : 0 < Fintype.card (BlockSite p k) := by rw [hcard]; exact p.W_pos
  have hN : N₀ ≤ Fintype.card (BlockSite p k) := by rw [hcard]; exact hW
  have hD' : D'.PosSemidef := (liftForm_posSemidef p k ω e _ fun _ => zero_le_one).submatrix _
  have hB' : ∀ s j, IsSandwiched (B' s j) D' := fun s j => isSandwiched_reindex σ (hB s j)
  have hT₀ : 0 < traceAgainst Γ₀ D' := traceAgainst_reindex_clockForm_pos p k σ ω hω he
  have hDtr : ∀ P : Matrix (Fin (Fintype.card (BlockSite p k)))
      (Fin (Fintype.card (BlockSite p k))) ℂ, P.PosSemidef → 0 ≤ traceAgainst P D' :=
    traceAgainst_reindex_clockForm_nonneg p k σ ω e
  have hd' : ∀ s, Measurable (d' s) := fun s =>
    (hd s).comp (measurable_pi_iff.mpr fun x => measurable_pi_apply _)
  rw [hc] at hF hclose
  have hEs := fun s => hEng _ hN hNpos F e hF Γ₀ M₀ hM₀ ω₀ hω₀.le le_rfl hclose.1 hclose.2 D'
    (B' s) hD' (hB' s) hT₀ hDtr (d' s) (hd' s)
  -- the Palm side
  set σ₁ : BlockSite p k ≃ Fin p.W := σ.trans (finCongr hcard)
  have hobs : (fun v => g (blockReconMass p k ω e v)) =
      fun v => reconMatrixObs p k ω e g (vecMulVec v (star v)) := by
    funext v; rw [reconMatrixObs_vecMulVec]
  have hφM : ∀ X, |reconMatrixObs p k ω e g X| ≤ Mg := fun X => hMg _
  have hbridge := blockSector_ratio_eq_palmExpect p k hD σ₁ U hU ω hω e
    (reconMatrixObs p k ω e g) (measurable_reconMatrixObs p k ω e g hg) Mg hφM
  rw [← hobs] at hbridge
  have hre : Matrix.reindex σ₁ σ₁ (blockF p k ω e) =
      Matrix.reindex (finCongr hcard) (finCongr hcard) F := by
    ext a b; simp [F, σ₁, blockDeformation, Matrix.reindex_apply]
  rw [hre, palmExpect_finCongr, hc] at hbridge
  have hfun : (fun u : Fin (Fintype.card (BlockSite p k)) → ℂ => reconMatrixObs p k ω e g
      (Matrix.reindex σ₁.symm σ₁.symm (vecMulVec (fun i => u ((finCongr hcard).symm i))
        (star fun i => u ((finCongr hcard).symm i))))) =
      fun u => g (blockReconMass p k ω e (fun x => u (σ x))) := by
    funext u
    rw [← reconMatrixObs_vecMulVec p k ω e g]
    congr 1
  rw [hfun] at hbridge
  rw [hbridge]
  -- measurability and bounds
  have hψM : ∀ x, |ψ x| ≤ ‖ψ‖ := fun x => by rw [← Real.norm_eq_abs]; exact ψ.norm_coe_le_norm x
  have hcS : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hrm := measurable_blockReconMass p k ω e
  have hcomp : Measurable (fun u : Fin (Fintype.card (BlockSite p k)) → ℂ => fun x => u (σ x)) :=
    measurable_pi_iff.mpr fun x => measurable_pi_apply _
  have hcube : ∀ s, Measurable (fun v => ψ (ratioCube (B s) D (d s) v)) := fun s =>
    ψ.continuous.measurable.comp (measurable_ratioCube _ _ _ (hd s))
  have hcube' : ∀ s, Measurable (fun u => ψ (ratioCube (B' s) D' (d' s) u)) := fun s =>
    ψ.continuous.measurable.comp (measurable_ratioCube _ _ _ (hd' s))
  have hrc : ∀ s u, ratioCube (B' s) D' (d' s) u = ratioCube (B s) D (d s) (fun x => u (σ x)) :=
    fun s u => ratioCube_reindex σ (B s) D (d s) u
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0)
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  have havgM : ∀ v, |(Fintype.card S : ℝ)⁻¹ * ∑ s, ψ (ratioCube (B s) D (d s) v)| ≤ ‖ψ‖ := by
    intro v
    rw [abs_mul, abs_of_pos (inv_pos.mpr hcS)]
    calc (Fintype.card S : ℝ)⁻¹ * |∑ s, ψ (ratioCube (B s) D (d s) v)|
        ≤ (Fintype.card S : ℝ)⁻¹ * ∑ _s : S, ‖ψ‖ := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => hψM _)
      _ = ‖ψ‖ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
  -- replace `g` by the cube average on the Palm side
  have e1 := abs_palmExpect_sub_le F (1 - 2 * b) e
    (fun u => g (blockReconMass p k ω e (fun x => u (σ x))))
    (fun u => (Fintype.card S : ℝ)⁻¹ * ∑ s, ψ (ratioCube (B' s) D' (d' s) u))
    (hg.comp (hrm.comp hcomp)) (measurable_const.mul (Finset.measurable_sum _ fun s _ => hcube' s))
    (max Mg ‖ψ‖) (fun u => (hMg _).trans (le_max_left _ _))
    (fun u => by simp only [hrc]; exact (havgM _).trans (le_max_right _ _)) δ
    (fun u => by simp only [hrc]; exact hδ _)
  rw [palmExpect_const_mul_sum F (1 - 2 * b) e _ _ hcube' ‖ψ‖ (fun s u => hψM _)] at e1
  -- the comparison for each `s`
  have e2 : |(Fintype.card S : ℝ)⁻¹ * ∑ s, palmExpect F (1 - 2 * b) e
        (fun u => ψ (ratioCube (B' s) D' (d' s) u)) -
      (Fintype.card S : ℝ)⁻¹ * ∑ s, ∫ g', ψ (ratioCube (B s) D (d s) (Mb *ᵥ g'))
        ∂circularVectorLaw (BlockSite p k)| ≤ 2 * ε := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.mpr hcS)]
    have hterm : ∀ s, |palmExpect F (1 - 2 * b) e (fun u => ψ (ratioCube (B' s) D' (d' s) u)) -
        ∫ g', ψ (ratioCube (B s) D (d s) (Mb *ᵥ g')) ∂circularVectorLaw (BlockSite p k)| ≤
          2 * ε := by
      intro s
      have hG : ∫ g, ψ (ratioCube (B' s) D' (d' s) (M₀ *ᵥ g))
          ∂circularVectorLaw (Fin (Fintype.card (BlockSite p k))) =
          ∫ g', ψ (ratioCube (B s) D (d s) (Mb *ᵥ g')) ∂circularVectorLaw (BlockSite p k) := by
        have h1 : ∀ g : Fin (Fintype.card (BlockSite p k)) → ℂ, ψ (ratioCube (B' s) D' (d' s) (M₀ *ᵥ g)) =
            ψ (ratioCube (B s) D (d s) (Mb *ᵥ (fun x => g (σ x)))) := by
          intro g
          rw [hrc]
          congr 2
          funext x
          exact reindex_mulVec_apply σ Mb g x
        simp_rw [h1]
        exact integral_circular_comp_equiv σ (fun g' => ψ (ratioCube (B s) D (d s) (Mb *ᵥ g')))
          ((hcube s).comp (Continuous.matrix_mulVec continuous_const continuous_id).measurable)
      rw [← hG]
      exact hEs s
    calc (Fintype.card S : ℝ)⁻¹ * |∑ s, (palmExpect F (1 - 2 * b) e
          (fun u => ψ (ratioCube (B' s) D' (d' s) u)) -
          ∫ g', ψ (ratioCube (B s) D (d s) (Mb *ᵥ g')) ∂circularVectorLaw (BlockSite p k))|
        ≤ (Fintype.card S : ℝ)⁻¹ * ∑ _s : S, 2 * ε := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => hterm s)
      _ = 2 * ε := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
  -- back to `g` on the Gaussian side
  have hmv : Measurable (fun g' : BlockSite p k → ℂ => Mb *ᵥ g') :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have e3 : |(Fintype.card S : ℝ)⁻¹ * ∑ s, ∫ g', ψ (ratioCube (B s) D (d s) (Mb *ᵥ g'))
        ∂circularVectorLaw (BlockSite p k) -
      ∫ g', g (blockReconMass p k ω e (Mb *ᵥ g')) ∂circularVectorLaw (BlockSite p k)| ≤ δ := by
    have hint : ∀ s, Integrable (fun g' => ψ (ratioCube (B s) D (d s) (Mb *ᵥ g')))
        (circularVectorLaw (BlockSite p k)) := fun s =>
      (integrable_const ‖ψ‖).mono' ((hcube s).comp hmv).aestronglyMeasurable
        (Filter.Eventually.of_forall fun g' => by rw [Real.norm_eq_abs]; exact hψM _)
    have hint2 : Integrable (fun g' => g (blockReconMass p k ω e (Mb *ᵥ g')))
        (circularVectorLaw (BlockSite p k)) :=
      (integrable_const Mg).mono' ((hg.comp hrm).comp hmv).aestronglyMeasurable
        (Filter.Eventually.of_forall fun g' => by rw [Real.norm_eq_abs]; exact hMg _)
    rw [← integral_finsetSum _ fun s _ => hint s, ← integral_const_mul,
      ← integral_sub ((integrable_finsetSum _ fun s _ => hint s).const_mul _) hint2]
    have := norm_integral_le_of_norm_le_const (μ := circularVectorLaw (BlockSite p k))
      (C := δ) (f := fun g' => (Fintype.card S : ℝ)⁻¹ *
        ∑ s, ψ (ratioCube (B s) D (d s) (Mb *ᵥ g')) - g (blockReconMass p k ω e (Mb *ᵥ g')))
      (Filter.Eventually.of_forall fun g' => by
        rw [Real.norm_eq_abs, abs_sub_comm]; exact hδ _)
    simpa [Real.norm_eq_abs] using this
  have := abs_sub_le (palmExpect F (1 - 2 * b) e
      (fun u => g (blockReconMass p k ω e (fun x => u (σ x)))))
    ((Fintype.card S : ℝ)⁻¹ * ∑ s, palmExpect F (1 - 2 * b) e
      (fun u => ψ (ratioCube (B' s) D' (d' s) u)))
    (∫ g', g (blockReconMass p k ω e (Mb *ᵥ g')) ∂circularVectorLaw (BlockSite p k))
  have := abs_sub_le ((Fintype.card S : ℝ)⁻¹ * ∑ s, palmExpect F (1 - 2 * b) e
      (fun u => ψ (ratioCube (B' s) D' (d' s) u)))
    ((Fintype.card S : ℝ)⁻¹ * ∑ s, ∫ g', ψ (ratioCube (B s) D (d s) (Mb *ᵥ g'))
        ∂circularVectorLaw (BlockSite p k))
    (∫ g', g (blockReconMass p k ω e (Mb *ᵥ g')) ∂circularVectorLaw (BlockSite p k))
  linarith

end Block

end LeadGaussian

end BlockBand.Endpoints.Normalization
