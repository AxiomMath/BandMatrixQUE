module

public import BlockBand.Critical.Collar.Density.GoodEvent
public import BlockBand.Layers.GaussianAbsorption
public import BlockBand.Layers.LayerMeanBounds
public import BlockBand.Wegner.ConditionalCount

/-!
# Two-block deformed Wegner cutoff for `D = A - e - X`

*Law.* `layerLaw W b .common` (`A_j ~ GUE_W(c/W)`, `c = 1 - 2b > 0`), every `W ≥ 1`, real `e`,
every deterministic Hermitian `X` (no norm bound).

* `sum_norm_sq_inv_mulVec_le_of_eigenCount`: a Hermitian matrix with no eigenvalue in `[-t, t]`
  has `‖D⁻¹v‖² ≤ t⁻²‖v‖²` (deterministic, spectral sums).
* `layerLaw_collarTopBlock_inv_bad_le`: from the deformed Wegner estimate,
  `P(∃ v, ‖D⁻¹v‖² > t⁻²‖v‖²) ≤ C/√c · 2W · 2t`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Foundations.Spectral BlockBand.Model.Construction
open scoped ENNReal

variable {W : ℕ}

theorem specSum_congr {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) {g g' : ℝ → ℂ}
    (h : ∀ r, g (increasingEigenvalue hA r) = g' (increasingEigenvalue hA r)) :
    specSum hA g = specSum hA g' := by
  unfold specSum
  exact Finset.sum_congr rfl fun r _ => by rw [h r]

/-- `D⁻¹ = Σ λ_r⁻¹ b_r b_r*` when no eigenvalue vanishes. -/
theorem inv_eq_specSum_of_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (h0 : ∀ r, increasingEigenvalue hA r ≠ 0) :
    A⁻¹ = specSum hA (fun x => ((x : ℂ))⁻¹) := by
  refine inv_eq_right_inv (matrix_eq_of_mulVec_increasingEigenvector_eq ⟨A, hA⟩ _ _ fun r => ?_)
  change (A * specSum hA _) *ᵥ increasingEigenvector hA r = 1 *ᵥ increasingEigenvector hA r
  rw [← mulVec_mulVec, specSum_mulVec_eigenvector, mulVec_smul, mulVec_increasingEigenvector,
    smul_smul, inv_mul_cancel₀ (by exact_mod_cast h0 r), one_smul, one_mulVec]

/-- **Deterministic Wegner step.** If the Hermitian `D` has no eigenvalue in `[-t, t]` (`t > 0`),
then `‖D⁻¹v‖² ≤ t⁻²‖v‖²`. -/
theorem sum_norm_sq_inv_mulVec_le_of_eigenCount {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : BlockBand.External.PSSS.HermitianMatrix ι) {t : ℝ} (ht : 0 < t)
    (h : BlockBand.External.PSSS.eigenCount D (Set.Icc (-t) t) = 0) (v : ι → ℂ) :
    ∑ a, ‖(D.1⁻¹ *ᵥ v) a‖ ^ 2 ≤ (t ^ 2)⁻¹ * ∑ a, ‖v a‖ ^ 2 := by
  have hD := D.2
  have hout : ∀ r, t < |increasingEigenvalue hD r| := by
    intro r
    by_contra hr
    rw [not_lt] at hr
    have hmem : increasingEigenvalue hD r ∈ Set.Icc (-t) t := abs_le.1 hr
    unfold BlockBand.External.PSSS.eigenCount at h
    exact (Finset.eq_empty_iff_forall_notMem.1 (Finset.card_eq_zero.1 h)) r
      (by
        classical
        convert (Finset.mem_filter (p := fun i => increasingEigenvalue hD i ∈ Set.Icc (-t) t)).2
          ⟨Finset.mem_univ r, hmem⟩)
  have h0 : ∀ r, increasingEigenvalue hD r ≠ 0 := fun r h => by
    have := hout r; rw [h, abs_zero] at this; linarith
  rw [inv_eq_specSum_of_ne_zero hD h0, sum_norm_sq_eq_sum_eigen hD, sum_norm_sq_eq_sum_eigen hD v,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [specSum_mulVec]
  simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, star_dotProduct_increasingEigenvector,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, norm_mul]
  rw [mul_pow]
  gcongr
  rw [norm_inv, inv_pow, Complex.norm_real, Real.norm_eq_abs]
  refine inv_anti₀ (by positivity) ?_
  exact pow_le_pow_left₀ ht.le (hout r).le 2

/-- `X` as a `PSSS.HermitianMatrix`, the deformation used in `Layers.absorbedMatrix`. -/
def hermX {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    BlockBand.External.PSSS.HermitianMatrix (Fin 2 × Fin W) := ⟨X, hX⟩

/-- **Two-block deformed Wegner cutoff.** With the absolute PSSS constant `C > 0`: for every
`W ≥ 1`, `b < 1/2`, real `e`, Hermitian `X` (no norm bound) and `t > 0`,
`P_layer(∃ v, ‖D⁻¹v‖² > t⁻²‖v‖²) ≤ C/√c · 2W · 2t`, `c = 1 - 2b`, `D = A - e - X`. -/
theorem layerLaw_collarTopBlock_inv_bad_le (source : BlockBand.External.PSSS.SourceContract.{0}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ), 0 < W → ∀ b : ℝ, b < 1 / 2 → ∀ (e : ℝ)
      (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), X.IsHermitian → ∀ t : ℝ, 0 < t →
        layerLaw W b .common {ω | ¬ ∀ v, ∑ a, ‖((collarTopBlock e X ω)⁻¹ *ᵥ v) a‖ ^ 2 ≤
            (t ^ 2)⁻¹ * ∑ a, ‖v a‖ ^ 2} ≤
          ENNReal.ofReal (C / Real.sqrt (1 - 2 * b) * ((2 : ℝ) * W) * (t - -t)) := by
  obtain ⟨C, hC, h⟩ := BlockBand.Layers.absorbedCount_tail
    (BlockBand.Wegner.conditionalBlockGUECount_holds source)
  refine ⟨C, hC, fun W hW b hb e X hX t ht => ?_⟩
  have hc : 0 < 1 - 2 * b := by linarith
  set S : Set (Fin 2 → Matrix (Fin W) (Fin W) ℂ) :=
    {A | 1 ≤ BlockBand.Layers.absorbedCount e (hermX hX) (Set.Icc (-t) t) A}
  have hsub : {ω : LayerSample W .common | ¬ ∀ v, ∑ a, ‖((collarTopBlock e X ω)⁻¹ *ᵥ v) a‖ ^ 2 ≤
      (t ^ 2)⁻¹ * ∑ a, ‖v a‖ ^ 2} ⊆
        {ω | ¬ ∀ j, (ω.1 j).IsHermitian} ∪ {ω | ω.1 ∈ S} := by
    intro ω hω
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
    obtain ⟨hA, hS⟩ := hn
    apply hω
    have hcount : BlockBand.External.PSSS.eigenCount
        (BlockBand.Layers.absorbedMatrix e (hermX hX) ω.1) (Set.Icc (-t) t) = 0 := by
      simp only [S, Set.mem_ofPred_eq, not_le, Nat.lt_one_iff] at hS
      exact hS
    intro v
    have hv := sum_norm_sq_inv_mulVec_le_of_eigenCount _ ht hcount v
    rwa [BlockBand.Layers.absorbedMatrix_val e (hermX hX) hA] at hv
  have hnull : layerLaw W b .common {ω | ¬ ∀ j, (ω.1 j).IsHermitian} = 0 := by
    have := BlockBand.Layers.lct_ae_blocks_isHermitian W b .common
    rwa [ae_iff] at this
  have hS : layerLaw W b .common {ω | ω.1 ∈ S} = BlockBand.Layers.blockLaw 2 W (1 - 2 * b) S := by
    have hset : {ω : LayerSample W .common | ω.1 ∈ S} = S ×ˢ Set.univ := by ext ω; simp
    rw [hset, BlockBand.Layers.absn_layerLaw_eq, Measure.prod_prod, measure_univ, mul_one]
  have htail := h 2 W hW (1 - 2 * b) hc e (hermX hX) (-t) t (by linarith) 1 le_rfl
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hnull, zero_add, hS]
  refine htail.trans (le_of_eq ?_)
  congr 1
  simp

end BlockBand.Critical.Collar.Density
