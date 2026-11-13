module

public import BlockBand.Angular.FiberAngular

/-!
# Reindexing transport for the angular first moment

* `projectiveHaar_map_piCongrLeft`, `lintegral_projectiveHaar_reindex` — `ν_N` is invariant
  under `v ↦ v ∘ e.symm` (for every `ℝ≥0∞` integrand, measurable or not);
* `reindexFrame`, `isFreshFrame_reindexFrame` — a frame of `v^⊥ ⊂ ℂ^ι` transported to
  `ℂ^{Fin N}` is a fresh frame (`IsFreshFrame`);
* `regressionFactor_reindex`, `quadForm_reindex`, `compress_reindex` — `𝓡`, quadratic forms and
  the frame compression `U_v*FU_v` are invariant;
* `freshGamma_reindex_eq` — with `K₀ = F - E`, `ζ = c₀ m_{c₀}(E)` (`Im ζ ≠ 0`) the fresh
  covariance `freshGamma` of the reindexed `F` is the reindexed angular covariance
  `angularGamma K₀ c₀ ζ = c₀ (K₀ - ζ̄)⁻¹(K₀ - ζ)⁻¹` (`Matrix.mul_inv_rev`, `resolvent_commute`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.FirstMoment

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Angular.ProjectiveStein BlockBand.Angular.Stein BlockBand.Angular.ConeDivergence
open scoped ENNReal NNReal ComplexConjugate

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-!
## Sums, norms and dot products under reindexing
-/

theorem l2Norm_comp_symm (e : ι ≃ κ) (x : ι → ℂ) : l2Norm (x ∘ e.symm) = l2Norm x := by
  unfold l2Norm
  congr 1
  exact Equiv.sum_comp e.symm (fun a => ‖x a‖ ^ 2)

theorem star_comp (e : ι ≃ κ) (x : ι → ℂ) : star (x ∘ e.symm) = star x ∘ e.symm := rfl

theorem dotProduct_comp_symm (e : ι ≃ κ) (x y : ι → ℂ) :
    (x ∘ e.symm) ⬝ᵥ (y ∘ e.symm) = x ⬝ᵥ y := by
  unfold dotProduct
  exact Equiv.sum_comp e.symm (fun a => x a * y a)

theorem mulVec_reindex (e : ι ≃ κ) (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    M.submatrix e.symm e.symm *ᵥ (x ∘ e.symm) = (M *ᵥ x) ∘ e.symm := by
  rw [submatrix_mulVec_equiv]
  congr 2
  funext a; simp

theorem quadForm_reindex (e : ι ≃ κ) (M : Matrix ι ι ℂ) (q : ι → ℂ) :
    quadForm (M.submatrix e.symm e.symm) (q ∘ e.symm) = quadForm M q := by
  unfold quadForm
  rw [mulVec_reindex, star_comp, dotProduct_comp_symm]

/-- `𝓡(E, v ∘ e⁻¹, F ∘ (e⁻¹ × e⁻¹)) = 𝓡(E, v, F)`. -/
theorem regressionFactor_reindex (e : ι ≃ κ) (t E : ℝ) (v : ι → ℂ) (F : Matrix ι ι ℂ) :
    regressionFactor t E (v ∘ e.symm) (F.submatrix e.symm e.symm) = regressionFactor t E v F := by
  unfold regressionFactor
  simp only
  rw [mulVec_reindex, star_comp, dotProduct_comp_symm]
  have : (F *ᵥ v) ∘ e.symm - (star v ⬝ᵥ (F *ᵥ v)) • (v ∘ e.symm) =
      (F *ᵥ v - (star v ⬝ᵥ (F *ᵥ v)) • v) ∘ e.symm := by
    funext b; simp
  rw [this, l2Norm_comp_symm]

/-!
## Projective Haar measure under reindexing
-/

theorem piCongrLeft_apply_const {α : Type*} [MeasurableSpace α] (e : ι ≃ κ) (g : ι → α) (b : κ) :
    (MeasurableEquiv.piCongrLeft (fun _ : κ => α) e) g b = g (e.symm b) := by
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

theorem piCongrLeft_eq_comp {α : Type*} [MeasurableSpace α] (e : ι ≃ κ) (g : ι → α) :
    (MeasurableEquiv.piCongrLeft (fun _ : κ => α) e) g = g ∘ e.symm :=
  funext fun b => piCongrLeft_apply_const e g b

/-- `ν_N` is invariant under reindexing: the law of `v ∘ e⁻¹` for `v ~ ν_ι` is `ν_κ`. -/
theorem projectiveHaar_map_piCongrLeft (e : ι ≃ κ) :
    (projectiveHaar ι).map (MeasurableEquiv.piCongrLeft (fun _ : κ => ℂ) e) =
      projectiveHaar κ := by
  set f := e.prodCongr (Equiv.refl (Fin 2))
  have hpi : (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)).map
      (MeasurableEquiv.piCongrLeft (fun _ : κ × Fin 2 => ℝ) f) =
      Measure.pi fun _ : κ × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0) :=
    (measurePreserving_piCongrLeft (α := fun _ : κ × Fin 2 => ℝ)
      (μ := fun _ => gaussianReal 0 (1 / 2 : ℝ≥0)) f).map_eq
  unfold projectiveHaar
  rw [circularVectorLaw_eq, circularVectorLaw_eq, ← hpi,
    Measure.map_map measurable_normalize measurable_toComplexVec,
    Measure.map_map (MeasurableEquiv.measurable _)
      (measurable_normalize.comp measurable_toComplexVec),
    Measure.map_map measurable_toComplexVec (MeasurableEquiv.measurable _),
    Measure.map_map measurable_normalize
      (measurable_toComplexVec.comp (MeasurableEquiv.measurable _))]
  congr 1
  funext r
  simp only [Function.comp_apply]
  rw [piCongrLeft_eq_comp, piCongrLeft_eq_comp]
  have hc : toComplexVec (r ∘ f.symm) = toComplexVec r ∘ e.symm := by
    funext b; rfl
  rw [hc, l2Norm_comp_symm]
  funext b; rfl

/-- Integration against `ν_κ` is integration of `v ↦ g(v ∘ e⁻¹)` against `ν_ι`, for every
`ℝ≥0∞`-valued `g` (no measurability needed: the map is a measurable equivalence). -/
theorem lintegral_projectiveHaar_reindex (e : ι ≃ κ) (g : (κ → ℂ) → ℝ≥0∞) :
    ∫⁻ v', g v' ∂projectiveHaar κ = ∫⁻ v, g (v ∘ e.symm) ∂projectiveHaar ι := by
  rw [← projectiveHaar_map_piCongrLeft e, lintegral_map_equiv]
  simp only [piCongrLeft_eq_comp]

/-!
## Frames under reindexing
-/

/-- Transport `U'_{v'} = U_{v' ∘ e}` with rows reindexed by `e`. -/
def reindexFrame {m : Type} (e : ι ≃ κ) (U : (ι → ℂ) → Matrix ι m ℂ) :
    (κ → ℂ) → Matrix κ m ℂ :=
  fun v' => (U (v' ∘ e)).submatrix e.symm id

theorem reindexFrame_apply_comp {m : Type} (e : ι ≃ κ) (U : (ι → ℂ) → Matrix ι m ℂ)
    (v : ι → ℂ) : reindexFrame e U (v ∘ e.symm) = (U v).submatrix e.symm id := by
  unfold reindexFrame
  congr 2
  funext a; simp

theorem measurable_reindexFrame {m : Type} [Fintype m] (e : ι ≃ κ)
    {U : (ι → ℂ) → Matrix ι m ℂ} (hU : Measurable U) : Measurable (reindexFrame e U) := by
  have hc : Measurable (fun v' : κ → ℂ => v' ∘ e) :=
    Measurable.of_eval fun a => measurable_pi_apply (e a)
  refine Measurable.of_eval fun b => Measurable.of_eval fun j => ?_
  exact (measurable_pi_apply j).comp ((measurable_pi_apply (e.symm b)).comp (hU.comp hc))

theorem conjTranspose_mul_reindexFrame {m : Type} [Fintype m] (e : ι ≃ κ)
    (U : (ι → ℂ) → Matrix ι m ℂ) (v : ι → ℂ) :
    (reindexFrame e U (v ∘ e.symm))ᴴ * reindexFrame e U (v ∘ e.symm) = (U v)ᴴ * U v := by
  rw [reindexFrame_apply_comp, conjTranspose_submatrix, submatrix_mul_equiv _ _ _ e.symm,
    submatrix_id_id]

theorem conjTranspose_mulVec_reindexFrame {m : Type} [Fintype m] (e : ι ≃ κ)
    (U : (ι → ℂ) → Matrix ι m ℂ) (v : ι → ℂ) :
    (reindexFrame e U (v ∘ e.symm))ᴴ *ᵥ (v ∘ e.symm) = (U v)ᴴ *ᵥ v := by
  rw [reindexFrame_apply_comp, conjTranspose_submatrix, submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm, Function.comp_id]
  rw [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]

/-- The compression `U_v*FU_v` is invariant under the transport. -/
theorem compress_reindex {m : Type} [Fintype m] (e : ι ≃ κ) (U : (ι → ℂ) → Matrix ι m ℂ)
    (F : Matrix ι ι ℂ) (v : ι → ℂ) :
    (reindexFrame e U (v ∘ e.symm))ᴴ * F.submatrix e.symm e.symm *
        reindexFrame e U (v ∘ e.symm) = (U v)ᴴ * F * U v := by
  rw [reindexFrame_apply_comp, conjTranspose_submatrix, submatrix_mul_equiv _ _ _ e.symm,
    submatrix_mul_equiv _ _ _ e.symm, submatrix_id_id]

/-- A frame of `v^⊥ ⊂ ℂ^ι` (orthonormal columns orthogonal to every unit `v`), transported
along `e : ι ≃ Fin N`, is a fresh frame. -/
theorem isFreshFrame_reindexFrame {N : ℕ} (e : ι ≃ Fin N)
    {U : (ι → ℂ) → Matrix ι (Fin (N - 1)) ℂ} (hUm : Measurable U)
    (hU : ∀ v : ι → ℂ, l2Norm v = 1 → (U v)ᴴ * U v = 1 ∧ (U v)ᴴ *ᵥ v = 0) :
    IsFreshFrame (reindexFrame e U) := by
  refine ⟨measurable_reindexFrame e hUm, fun v' hv' => ?_⟩
  have hv : v' = (v' ∘ e) ∘ e.symm := by funext b; simp
  have hn : l2Norm (v' ∘ e) = 1 := by rw [← l2Norm_comp_symm e, ← hv, hv']
  rw [hv, conjTranspose_mul_reindexFrame, conjTranspose_mulVec_reindexFrame]
  exact hU _ hn

/-!
## The two covariances
-/

theorem submatrix_sub_smul_one (e : ι ≃ κ) (F : Matrix ι ι ℂ) (z : ℂ) :
    (F - z • (1 : Matrix ι ι ℂ)).submatrix e.symm e.symm =
      F.submatrix e.symm e.symm - z • (1 : Matrix κ κ ℂ) := by
  ext a b
  simp [one_apply]

/-- **`Γ_§8 = Γ_§11`.** For Hermitian `K₀ = F - E` and `ζ = c₀ m` with `Im ζ ≠ 0`, the
fresh covariance `c₀|F - E - c₀ m|^{-2}` of the reindexed deformation is the reindexed angular
covariance `c₀ (K₀ - ζ̄)⁻¹(K₀ - ζ)⁻¹`. -/
theorem freshGamma_reindex_eq {N : ℕ} (e : ι ≃ Fin N) (F : Matrix ι ι ℂ) (c₀ E : ℝ)
    {K : Matrix ι ι ℂ} (hK : K.IsHermitian) (hFK : K = F - (E : ℂ) • 1) {ζ : ℂ}
    (hζ : ζ = (c₀ : ℂ) * freshDyson (F.submatrix e.symm e.symm) c₀ E) (hz : ζ.im ≠ 0) :
    freshGamma (F.submatrix e.symm e.symm) c₀ E =
      (Reference.angularGamma K c₀ ζ).submatrix e.symm e.symm := by
  unfold freshGamma
  simp only
  rw [← hζ]
  have hX : F.submatrix e.symm e.symm - ((E : ℂ) + ζ) • (1 : Matrix (Fin N) (Fin N) ℂ) =
      (K - ζ • (1 : Matrix ι ι ℂ)).submatrix e.symm e.symm := by
    rw [hFK, sub_sub, ← add_smul, submatrix_sub_smul_one]
  rw [hX, conjTranspose_submatrix, submatrix_mul_equiv _ _ _ e.symm, inv_submatrix_equiv,
    Matrix.mul_inv_rev, ← conjTranspose_nonsing_inv, Reference.angularGamma, submatrix_smul]
  congr 2
  have h1 : (K - ζ • (1 : Matrix ι ι ℂ))⁻¹ = Reference.resolvent K ζ := rfl
  rw [h1, ← Reference.resolvent_conj hK, Reference.resolvent_commute hK hz
    (Reference.im_conj_ne hz)]

end BlockBand.Angular.FirstMoment
