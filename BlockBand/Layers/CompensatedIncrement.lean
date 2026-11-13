module

public import BlockBand.Layers.MatchedTraces
public import BlockBand.Layers.SchurInertia
public import BlockBand.Layers.MatchedScalar
public import BlockBand.RankLocation.SemicircleCDF
public import BlockBand.Model.Construction.SpectralEigenvalues

/-!
# Compensated phase increments: spectral vocabulary and the conditional increments

* Spectral vocabulary. For Hermitian `M`, `N_-(M)` and `Θ_z(M) = π⁻¹ Σ_j arg(z - λ_j)` are
  spectral sums of the characteristic roots (`cph_negativeCount_eq_spectralSum`,
  `cph_spectralSum_eq_rawSum`); they are invariant under reindexing
  (`cph_negativeCount_submatrix`, `cph_phaseCount_submatrix`), Borel along the raw increasing
  eigenvalues (`cph_measurable_rawSum`), and bounded: `0 ≤ Θ_z(M) ≤ dim` for `Im z ≥ 0` and every
  square `M` (`cph_phaseCount_nonneg`, `cph_phaseCount_le`), `N_-(M) ≤ dim`.
* The fresh-layer increment variables `N_-(A - E - X) + Θ_{z'}(X₊) - Θ_{z_∂}(X)` for separate
  ports (`cphSepIncrement`, `z' = z_∂`) and the common port (`cphComIncrement`, `z' = z₀`), their
  measurable versions, and their deterministic bound `|Δ| ≤ 6W` for `Im z_∂, Im z₀ ≥ 0`.
* `compensatedIncrement_of_local`: the contract follows from its statement on the scalar
  domain `d(X) ≤ d_*` (any fixed `d_* > 0`), since both sides are `O(W)` off it (the
  parenthetical remark of the contract docstring). The local statement itself (the heat
  interpolation of the paper) is the hypothesis `CphIncrementLocal`, proved from
`ConditionalBlockGUECount` and `ChtMeanSquare` by `cphIncrementLocal_of_meanSquare`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm (negativeCount)
open BlockBand.Model.Construction (rawIncreasingEigenvalue measurable_rawIncreasingEigenvalue
  rawIncreasingEigenvalue_eq)
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
## 1. Spectral sums
-/

section Spectral

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A Borel spectral sum along the raw increasing eigenvalues (zero off the Hermitian locus). -/
def cphRawSum (f : ℝ → ℝ) (M : Matrix ι ι ℂ) : ℝ :=
  ∑ i : Fin (Fintype.card ι), f (rawIncreasingEigenvalue i M)

theorem cph_measurable_rawSum {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (cphRawSum (ι := ι) f) :=
  Finset.measurable_sum _ fun i _ => hf.comp (measurable_rawIncreasingEigenvalue i)

theorem cph_spectralSum_eq_eigenvaluesZero {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (f : ℝ → ℝ) :
    Internal.Contracts.Inputs.spectralSum M f = ∑ j, f (hM.eigenvalues₀ j) := by
  unfold Internal.Contracts.Inputs.spectralSum
  rw [hM.roots_charpoly_eq_eigenvalues₀, Multiset.map_map, Finset.sum_eq_multiset_sum]
  congr 1

theorem cph_spectralSum_eq_eigenvalues {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (f : ℝ → ℝ) :
    Internal.Contracts.Inputs.spectralSum M f = ∑ k, f (hM.eigenvalues k) := by
  unfold Internal.Contracts.Inputs.spectralSum
  rw [hM.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  congr 1

theorem cph_spectralSum_eq_rawSum {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (f : ℝ → ℝ) :
    Internal.Contracts.Inputs.spectralSum M f = cphRawSum f M := by
  rw [cph_spectralSum_eq_eigenvaluesZero hM]
  unfold cphRawSum
  simp only [rawIncreasingEigenvalue_eq _ _ hM, BlockBand.Foundations.Spectral.increasingEigenvalue]
  exact (Equiv.sum_comp Fin.revPerm (fun j => f (hM.eigenvalues₀ j))).symm

theorem cph_spectralSum_submatrix (e : κ ≃ ι) (M : Matrix ι ι ℂ) (f : ℝ → ℝ) :
    Internal.Contracts.Inputs.spectralSum (M.submatrix e e) f =
      Internal.Contracts.Inputs.spectralSum M f := by
  unfold Internal.Contracts.Inputs.spectralSum
  have : M.submatrix e e = reindex e.symm e.symm M := rfl
  rw [this, charpoly_reindex]

/-- The indicator of the negative half-line. -/
def cphNegInd (x : ℝ) : ℝ := if x < 0 then 1 else 0

theorem cph_measurable_negInd : Measurable cphNegInd :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    measurable_const

theorem cph_negativeCount_eq_spectralSum {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    (negativeCount M : ℝ) = Internal.Contracts.Inputs.spectralSum M cphNegInd := by
  rw [cph_spectralSum_eq_eigenvalues hM, negativeCount_of_isHermitian hM]
  unfold cphNegInd
  rw [Finset.sum_boole]

/-- `N_-` as a Borel spectral sum, on all square matrices. -/
theorem cph_negativeCount_eq_rawSum (M : Matrix ι ι ℂ) :
    (negativeCount M : ℝ) = cphRawSum cphNegInd M := by
  by_cases hM : M.IsHermitian
  · rw [cph_negativeCount_eq_spectralSum hM, cph_spectralSum_eq_rawSum hM]
  · have h0 : negativeCount M = 0 := by
      unfold negativeCount
      simp [hM]
    rw [h0]
    unfold cphRawSum rawIncreasingEigenvalue cphNegInd
    simp [hM]

theorem cph_measurable_negativeCount :
    Measurable (fun M : Matrix ι ι ℂ => (negativeCount M : ℝ)) := by
  simp_rw [cph_negativeCount_eq_rawSum]
  exact cph_measurable_rawSum cph_measurable_negInd

theorem cph_negativeCount_submatrix (e : κ ≃ ι) {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    negativeCount (M.submatrix e e) = negativeCount M := by
  have h1 := cph_negativeCount_eq_spectralSum (hM.submatrix e)
  rw [cph_spectralSum_submatrix, ← cph_negativeCount_eq_spectralSum hM] at h1
  exact_mod_cast h1

theorem cph_negativeCount_le (M : Matrix ι ι ℂ) : negativeCount M ≤ Fintype.card ι := by
  unfold negativeCount
  split_ifs
  · exact (Finset.card_filter_le _ _).trans (le_of_eq Finset.card_univ)
  · exact Nat.zero_le _

/-- The phase function `x ↦ arg(z - x)`. -/
def cphArg (z : ℂ) (x : ℝ) : ℝ := Complex.arg (z - x)

theorem cph_measurable_arg (z : ℂ) : Measurable (cphArg z) :=
  Complex.measurable_arg.comp (measurable_const.sub Complex.measurable_ofReal)

theorem cph_arg_nonneg {z : ℂ} (hz : 0 ≤ z.im) (x : ℝ) : 0 ≤ cphArg z x := by
  unfold cphArg
  rw [Complex.arg_nonneg_iff]
  simpa using hz

theorem cph_arg_le_pi (z : ℂ) (x : ℝ) : cphArg z x ≤ Real.pi := Complex.arg_le_pi _

/-- The Borel phase `π⁻¹ Σ_i arg(z - λ_i)` along the raw increasing eigenvalues. -/
def cphPhase (z : ℂ) (M : Matrix ι ι ℂ) : ℝ := cphRawSum (cphArg z) M / Real.pi

theorem cph_measurable_phase (z : ℂ) : Measurable (cphPhase (ι := ι) z) :=
  (cph_measurable_rawSum (cph_measurable_arg z)).div_const _

theorem cph_phase_nonneg {z : ℂ} (hz : 0 ≤ z.im) (M : Matrix ι ι ℂ) : 0 ≤ cphPhase z M :=
  div_nonneg (Finset.sum_nonneg fun _ _ => cph_arg_nonneg hz _) Real.pi_pos.le

theorem cph_phase_le (z : ℂ) (M : Matrix ι ι ℂ) : cphPhase z M ≤ Fintype.card ι := by
  unfold cphPhase cphRawSum
  rw [div_le_iff₀ Real.pi_pos]
  calc ∑ i : Fin (Fintype.card ι), cphArg z (rawIncreasingEigenvalue i M)
      ≤ ∑ _i : Fin (Fintype.card ι), Real.pi := Finset.sum_le_sum fun i _ => cph_arg_le_pi z _
    _ = Fintype.card ι * Real.pi := by simp

theorem cph_abs_phase_le {z : ℂ} (hz : 0 ≤ z.im) (M : Matrix ι ι ℂ) :
    |cphPhase z M| ≤ Fintype.card ι := by
  rw [abs_of_nonneg (cph_phase_nonneg hz M)]; exact cph_phase_le z M

theorem cph_rawNeg_nonneg (M : Matrix ι ι ℂ) : 0 ≤ cphRawSum cphNegInd M := by
  rw [← cph_negativeCount_eq_rawSum]; exact Nat.cast_nonneg _

theorem cph_rawNeg_le (M : Matrix ι ι ℂ) : cphRawSum cphNegInd M ≤ Fintype.card ι := by
  rw [← cph_negativeCount_eq_rawSum]; exact_mod_cast cph_negativeCount_le M

theorem cph_phaseCount_eq {z : ℂ} {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    phaseCount z M = cphPhase z M := by
  unfold phaseCount cphPhase
  rw [← cph_spectralSum_eq_rawSum hM]
  rfl

theorem cph_phaseCount_submatrix (z : ℂ) (e : κ ≃ ι) (M : Matrix ι ι ℂ) :
    phaseCount z (M.submatrix e e) = phaseCount z M := by
  unfold phaseCount
  exact congrArg (· / Real.pi) (cph_spectralSum_submatrix e M _)

theorem cph_phaseCount_nonneg {z : ℂ} (hz : 0 ≤ z.im) (M : Matrix ι ι ℂ) :
    0 ≤ phaseCount z M := by
  unfold phaseCount Internal.Contracts.Inputs.spectralSum
  refine div_nonneg (Multiset.sum_nonneg fun x hx => ?_) Real.pi_pos.le
  obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp hx
  exact cph_arg_nonneg hz y.re

theorem cph_phaseCount_le {z : ℂ} (M : Matrix ι ι ℂ) :
    phaseCount z M ≤ Fintype.card ι := by
  unfold phaseCount Internal.Contracts.Inputs.spectralSum
  rw [div_le_iff₀ Real.pi_pos]
  have h1 := Multiset.sum_le_card_nsmul (M.charpoly.roots.map fun y => Complex.arg (z - y.re))
    Real.pi (fun x hx => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp hx
      exact Complex.arg_le_pi _)
  rw [Multiset.card_map, nsmul_eq_mul] at h1
  have h2 : (M.charpoly.roots.card : ℝ) ≤ Fintype.card ι := by
    have := Polynomial.card_roots' M.charpoly
    rw [charpoly_natDegree_eq_dim] at this
    exact_mod_cast this
  exact h1.trans (mul_le_mul_of_nonneg_right h2 Real.pi_pos.le)

theorem cph_abs_phaseCount_le {z : ℂ} (hz : 0 ≤ z.im) (M : Matrix ι ι ℂ) :
    |phaseCount z M| ≤ Fintype.card ι := by
  rw [abs_of_nonneg (cph_phaseCount_nonneg hz M)]
  exact cph_phaseCount_le M

end Spectral

/-!
## 2. Scalar bounds
-/

section Scalars

open BlockBand.RankLocation

theorem cph_abs_phaseEll_le (E : ℝ) : |phaseEll E| ≤ 1 := by
  unfold phaseEll
  rw [abs_div, abs_of_pos Real.pi_pos, div_le_one Real.pi_pos, Complex.log_im]
  exact Complex.abs_arg_le_pi _

theorem cph_abs_phaseH_le {E : ℝ} (hE : |E| ≤ 2) : |phaseH E| ≤ 1 := by
  unfold phaseH
  rw [abs_div, abs_of_pos Real.pi_pos, div_le_one Real.pi_pos]
  have h1 : |(matchedA E ^ 2).im| ≤ 1 := by
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_pow, norm_matchedA hE, one_pow]
  linarith [Real.pi_gt_three]

theorem cph_abs_semicircleCDF_le (E : ℝ) : |semicircleCDF E| ≤ 1 := by
  rw [abs_of_nonneg (semicircleCDF_nonneg E)]
  exact semicircleCDF_le_one E

theorem cph_boundaryZ_im_nonneg {b κ E : ℝ} (hb : b < 1) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    0 ≤ (boundaryZ b E).im :=
  (boundaryZ_im_pos_of_mem_bulkInterval hb hκ hE).1.le.trans
    (boundaryZ_im_pos_of_mem_bulkInterval hb hκ hE).2

theorem cph_commonZ_im_nonneg {b κ E : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) : 0 ≤ (commonZ b E).im :=
  (commonZ_im_pos_of_mem_bulkInterval hb hκ hE).1.le.trans
    (commonZ_im_pos_of_mem_bulkInterval hb hκ hE).2

/-- Off the scalar domain, an `O(W)` quantity is `O(W d²)`. -/
theorem cph_offDomain {W d dstar L : ℝ} (hW : 0 < W) (hdstar : 0 < dstar) (hd : dstar < d)
    (hL : |L| ≤ 8 * W) : |L| ≤ (8 / dstar ^ 2) * (W * d ^ 2 + W⁻¹) := by
  have hsq : dstar ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hdstar.le hd.le 2
  have h1 : 8 * W ≤ (8 / dstar ^ 2) * (W * d ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have h2 : 0 ≤ (8 / dstar ^ 2) * W⁻¹ := by positivity
  nlinarith

end Scalars

/-!
## 3. The increment variables
-/

section Increment

/-- The separate-port fresh-layer increment `N_-(A - E - X) + Θ_{z_∂}(X₊) - Θ_{z_∂}(X)`. -/
def cphSepIncrement (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ℓ : LayerSample W .separate) : ℝ :=
  (negativeCount (blockDiag ℓ.1 - (E : ℂ) • 1 - X) : ℝ) +
    phaseCount (boundaryZ b E) (layerSchur .separate E X ℓ) - phaseCount (boundaryZ b E) X

/-- The common-port fresh-layer increment `N_-(A - E - X) + Θ_{z₀}(X₊) - Θ_{z_∂}(X)`. -/
def cphComIncrement (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ℓ : LayerSample W .common) : ℝ :=
  (negativeCount (blockDiag ℓ.1 - (E : ℂ) • 1 - X) : ℝ) +
    phaseCount (commonZ b E) (layerSchur .common E X ℓ) - phaseCount (boundaryZ b E) X

/-- Borel version of `cphSepIncrement`. -/
def cphSepIncrementM (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ℓ : LayerSample W .separate) : ℝ :=
  cphRawSum cphNegInd (blockDiag ℓ.1 - (E : ℂ) • 1 - X) +
    cphPhase (boundaryZ b E) (layerSchur .separate E X ℓ) - cphPhase (boundaryZ b E) X

/-- Borel version of `cphComIncrement`. -/
def cphComIncrementM (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ℓ : LayerSample W .common) : ℝ :=
  cphRawSum cphNegInd (blockDiag ℓ.1 - (E : ℂ) • 1 - X) +
    cphPhase (commonZ b E) (layerSchur .common E X ℓ) - cphPhase (boundaryZ b E) X

theorem cph_sepIncrement_eq (b E : ℝ) {W : ℕ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {ℓ : LayerSample W .separate} (hA : ∀ j, (ℓ.1 j).IsHermitian) :
    cphSepIncrement b E X ℓ = cphSepIncrementM b E X ℓ := by
  unfold cphSepIncrement cphSepIncrementM
  rw [cph_negativeCount_eq_rawSum, cph_phaseCount_eq (srec_layerSchur_isHermitian E hX ℓ hA),
    cph_phaseCount_eq hX]

theorem cph_comIncrement_eq (b E : ℝ) {W : ℕ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {ℓ : LayerSample W .common} (hA : ∀ j, (ℓ.1 j).IsHermitian) :
    cphComIncrement b E X ℓ = cphComIncrementM b E X ℓ := by
  unfold cphComIncrement cphComIncrementM
  rw [cph_negativeCount_eq_rawSum, cph_phaseCount_eq (rng_layerSchur_common_isHermitian E hX ℓ hA),
    cph_phaseCount_eq hX]

/-- The common-port layer Schur matrix is jointly measurable in `(X, ℓ)`. -/
theorem cph_measurable_layerSchur_common {Ω : Type*} [MeasurableSpace Ω] {W : ℕ}
    (E : ℝ) {Xf : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ℓf : Ω → LayerSample W .common}
    (hX : Measurable Xf) (hℓ : Measurable ℓf) :
    Measurable (fun t => layerSchur .common E (Xf t) (ℓf t)) := by
  have hB : Measurable (fun t => bondMatrix .common (ℓf t).2) := by
    refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
    unfold bondMatrix
    split_ifs
    · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        ((measurable_pi_apply _).comp (measurable_snd.comp hℓ))))
    · exact measurable_const
  have hD : Measurable (fun t => Internal.Contracts.Layers.blockDiag (ℓf t).1) :=
    (srec_continuous_blockDiag 2 W).measurable.comp (measurable_fst.comp hℓ)
  have hM : Measurable (fun t => (Internal.Contracts.Layers.blockDiag (ℓf t).1 -
      (E : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - Xf t)⁻¹) :=
    measurable_matrix_inv.comp ((hD.sub measurable_const).sub hX)
  exact srec_measurable_mul (srec_measurable_mul (srec_measurable_conjTranspose hB) hM) hB

theorem cph_measurable_top {Ω : Type*} [MeasurableSpace Ω] {W : ℕ}
    (E : ℝ) {Xf : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {Af : Ω → Fin 2 → Matrix (Fin W) (Fin W) ℂ} (hX : Measurable Xf) (hA : Measurable Af) :
    Measurable (fun t => Internal.Contracts.Layers.blockDiag (Af t) -
      (E : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - Xf t) :=
  (((srec_continuous_blockDiag 2 W).measurable.comp hA).sub measurable_const).sub hX

theorem cph_measurable_sepIncrementM {Ω : Type*} [MeasurableSpace Ω] (b E : ℝ) {W : ℕ}
    {Xf : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ℓf : Ω → LayerSample W .separate}
    (hX : Measurable Xf) (hℓ : Measurable ℓf) :
    Measurable (fun t => cphSepIncrementM b E (Xf t) (ℓf t)) := by
  unfold cphSepIncrementM
  exact (((cph_measurable_rawSum cph_measurable_negInd).comp (cph_measurable_top E hX (measurable_fst.comp hℓ))).add
    ((cph_measurable_phase _).comp (srec_measurable_layerSchur E hX hℓ))).sub
    ((cph_measurable_phase _).comp hX)

theorem cph_measurable_comIncrementM {Ω : Type*} [MeasurableSpace Ω] (b E : ℝ) {W : ℕ}
    {Xf : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ℓf : Ω → LayerSample W .common}
    (hX : Measurable Xf) (hℓ : Measurable ℓf) :
    Measurable (fun t => cphComIncrementM b E (Xf t) (ℓf t)) := by
  unfold cphComIncrementM
  exact (((cph_measurable_rawSum cph_measurable_negInd).comp (cph_measurable_top E hX (measurable_fst.comp hℓ))).add
    ((cph_measurable_phase _).comp (cph_measurable_layerSchur_common E hX hℓ))).sub
    ((cph_measurable_phase _).comp hX)

theorem cph_abs_sepIncrement_le {b E : ℝ} (hz : 0 ≤ (boundaryZ b E).im) {W : ℕ}
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ℓ : LayerSample W .separate) :
    |cphSepIncrement b E X ℓ| ≤ 6 * W := by
  unfold cphSepIncrement
  have h1 : (negativeCount (blockDiag ℓ.1 - (E : ℂ) • 1 - X) : ℝ) ≤ 2 * W := by
    have := cph_negativeCount_le (blockDiag ℓ.1 - (E : ℂ) • (1 : Matrix (Fin 2 × Fin W) _ ℂ) - X)
    simp only [Fintype.card_prod, Fintype.card_fin] at this
    exact_mod_cast this
  have h2 := cph_abs_phaseCount_le hz (layerSchur .separate E X ℓ)
  have h3 := cph_abs_phaseCount_le hz X
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at h2 h3
  have h0 : (0 : ℝ) ≤ (negativeCount (blockDiag ℓ.1 - (E : ℂ) • 1 - X) : ℝ) := Nat.cast_nonneg _
  rw [abs_le] at h2 h3 ⊢
  constructor <;> linarith

theorem cph_abs_sepIncrementM_le {b E : ℝ} (hz : 0 ≤ (boundaryZ b E).im) {W : ℕ}
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ℓ : LayerSample W .separate) :
    |cphSepIncrementM b E X ℓ| ≤ 6 * W := by
  unfold cphSepIncrementM
  have h0 := cph_rawNeg_nonneg (blockDiag ℓ.1 - (E : ℂ) • (1 : Matrix (Fin 2 × Fin W) _ ℂ) - X)
  have h1 := cph_rawNeg_le (blockDiag ℓ.1 - (E : ℂ) • (1 : Matrix (Fin 2 × Fin W) _ ℂ) - X)
  have h2 := cph_abs_phase_le hz (layerSchur .separate E X ℓ)
  have h3 := cph_abs_phase_le hz X
  simp only [Fintype.card_prod, Fintype.card_fin] at h1 h2 h3
  push_cast at h1 h2 h3
  rw [abs_le] at h2 h3 ⊢
  constructor <;> linarith

theorem cph_abs_comIncrementM_le {b E : ℝ} (hz : 0 ≤ (boundaryZ b E).im)
    (hz0 : 0 ≤ (commonZ b E).im) {W : ℕ}
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ℓ : LayerSample W .common) :
    |cphComIncrementM b E X ℓ| ≤ 6 * W := by
  unfold cphComIncrementM
  have h0 := cph_rawNeg_nonneg (blockDiag ℓ.1 - (E : ℂ) • (1 : Matrix (Fin 2 × Fin W) _ ℂ) - X)
  have h1 := cph_rawNeg_le (blockDiag ℓ.1 - (E : ℂ) • (1 : Matrix (Fin 2 × Fin W) _ ℂ) - X)
  have h2 := cph_abs_phase_le hz0 (layerSchur .common E X ℓ)
  have h3 := cph_abs_phase_le hz X
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  simp only [Fintype.card_prod, Fintype.card_fin] at h1 h2 h3
  push_cast at h1 h2 h3
  rw [abs_le] at h2 h3 ⊢
  constructor <;> linarith

theorem cph_abs_comIncrement_le {b E : ℝ} (hz : 0 ≤ (boundaryZ b E).im)
    (hz0 : 0 ≤ (commonZ b E).im) {W : ℕ}
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ℓ : LayerSample W .common) :
    |cphComIncrement b E X ℓ| ≤ 6 * W := by
  unfold cphComIncrement
  have h1 : (negativeCount (blockDiag ℓ.1 - (E : ℂ) • 1 - X) : ℝ) ≤ 2 * W := by
    have := cph_negativeCount_le (blockDiag ℓ.1 - (E : ℂ) • (1 : Matrix (Fin 2 × Fin W) _ ℂ) - X)
    simp only [Fintype.card_prod, Fintype.card_fin] at this
    exact_mod_cast this
  have h2 := cph_abs_phaseCount_le hz0 (layerSchur .common E X ℓ)
  have h3 := cph_abs_phaseCount_le hz X
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat,
    one_mul] at h2 h3
  have h0 : (0 : ℝ) ≤ (negativeCount (blockDiag ℓ.1 - (E : ℂ) • 1 - X) : ℝ) := Nat.cast_nonneg _
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  rw [abs_le] at h2 h3 ⊢
  constructor <;> linarith

end Increment

/-!
## 4. Reduction of `CompensatedIncrementContract` to the scalar domain
-/

section Reduction

open BlockBand.RankLocation

theorem cph_abs_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {B : ℝ} (h : ∀ ω, |f ω| ≤ B) : |∫ ω, f ω ∂μ| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := B)
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact h ω)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

theorem cph_negativeCount_le_two {W : ℕ} (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (negativeCount M : ℝ) ≤ 2 * W := by
  have := cph_negativeCount_le M
  simp only [Fintype.card_prod, Fintype.card_fin] at this
  exact_mod_cast this

theorem cph_sep_lhs_le {b κ E : ℝ} (hb1 : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ)
    {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    |(∫ ω, ((negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
          phaseCount (boundaryZ b E) (layerSchur .separate E X ω)) ∂layerLaw W b .separate) -
        phaseCount (boundaryZ b E) X - 2 * W * semicircleCDF E| ≤ 8 * W := by
  have hz := cph_boundaryZ_im_nonneg (b := b) (by linarith) hκ hE
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have hI : |∫ ω, ((negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
      phaseCount (boundaryZ b E) (layerSchur .separate E X ω)) ∂layerLaw W b .separate| ≤ 4 * W := by
    refine cph_abs_integral_le fun ω => ?_
    have h2 := cph_abs_phaseCount_le hz (layerSchur .separate E X ω)
    simp only [Fintype.card_prod, Fintype.card_fin] at h2
    push_cast at h2
    refine abs_le.mpr ⟨?_, ?_⟩
    · have := Nat.cast_nonneg (α := ℝ) (negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X))
      linarith [(abs_le.mp h2).1]
    · have := cph_negativeCount_le_two (blockDiag ω.1 - (E : ℂ) • 1 - X)
      linarith [(abs_le.mp h2).2]
  have h3 := cph_abs_phaseCount_le hz X
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at h3
  have h4 := cph_abs_semicircleCDF_le E
  have h5 : |2 * (W : ℝ) * semicircleCDF E| ≤ 2 * W := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * W)]
    nlinarith
  obtain ⟨a1, a2⟩ := abs_le.mp hI
  obtain ⟨b1, b2⟩ := abs_le.mp h3
  obtain ⟨c1, c2⟩ := abs_le.mp h5
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

theorem cph_com_lhs_le {b κ E : ℝ} (hb1 : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ)
    {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    |(∫ ω, ((negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
          phaseCount (commonZ b E) (layerSchur .common E X ω)) ∂layerLaw W b .common) -
        phaseCount (boundaryZ b E) X - W * (phaseEll E + phaseH E)| ≤ 8 * W := by
  have hz := cph_boundaryZ_im_nonneg (b := b) (by linarith) hκ hE
  have hz0 := cph_commonZ_im_nonneg hb1 hκ hE
  have hE2 : |E| ≤ 2 := (abs_le_of_mem_bulkInterval hE).trans (by linarith)
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have : IsProbabilityMeasure (layerLaw W b .common) := pg_isProbabilityMeasure_layerLaw W b .common
  have hI : |∫ ω, ((negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
      phaseCount (commonZ b E) (layerSchur .common E X ω)) ∂layerLaw W b .common| ≤ 4 * W := by
    refine cph_abs_integral_le fun ω => ?_
    have h2 := cph_abs_phaseCount_le hz0 (layerSchur .common E X ω)
    simp only [Fintype.card_prod, Fintype.card_fin] at h2
    push_cast at h2
    refine abs_le.mpr ⟨?_, ?_⟩
    · have := Nat.cast_nonneg (α := ℝ) (negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X))
      linarith [(abs_le.mp h2).1]
    · have := cph_negativeCount_le_two (blockDiag ω.1 - (E : ℂ) • 1 - X)
      linarith [(abs_le.mp h2).2]
  have h3 := cph_abs_phaseCount_le hz X
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at h3
  have h4 := cph_abs_phaseEll_le E
  have h4' := cph_abs_phaseH_le hE2
  have h5 : |(W : ℝ) * (phaseEll E + phaseH E)| ≤ 2 * W := by
    rw [abs_mul, abs_of_nonneg hW]
    have := abs_add_le (phaseEll E) (phaseH E)
    nlinarith
  obtain ⟨a1, a2⟩ := abs_le.mp hI
  obtain ⟨b1, b2⟩ := abs_le.mp h3
  obtain ⟨c1, c2⟩ := abs_le.mp h5
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

/-- **The local increment input** (the heat interpolation of the paper): the conditional
mean increments on the scalar domain `d(X) ≤ d_*`, for some `d_* > 0` (any choice). This is
`CompensatedIncrementContract` restricted to `d(X) ≤ d_*`; nothing else is assumed. -/
structure CphIncrementLocal : Prop where
  separate : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ dstar C : ℝ, 0 < dstar ∧ ∀ (W : ℕ), 0 < W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar →
      |(∫ ω, ((negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
            phaseCount (boundaryZ b E) (layerSchur .separate E X ω)) ∂layerLaw W b .separate) -
          phaseCount (boundaryZ b E) X - 2 * W * semicircleCDF E| ≤
        C * (W * matchedDistance b E X ^ 2 + (W : ℝ)⁻¹)
  common : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ dstar C : ℝ, 0 < dstar ∧ ∀ (W : ℕ), 0 < W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar →
      |(∫ ω, ((negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
            phaseCount (commonZ b E) (layerSchur .common E X ω)) ∂layerLaw W b .common) -
          phaseCount (boundaryZ b E) X - W * (phaseEll E + phaseH E)| ≤
        C * (W * matchedDistance b E X ^ 2 + (W : ℝ)⁻¹)

theorem cph_local_extend {W : ℕ} (hW : 0 < W) {d dstar C L : ℝ} (hdstar : 0 < dstar)
    (hloc : d ≤ dstar → |L| ≤ C * (W * d ^ 2 + (W : ℝ)⁻¹)) (hL : |L| ≤ 8 * W) :
    |L| ≤ max C (8 / dstar ^ 2) * (W * d ^ 2 + (W : ℝ)⁻¹) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hR : 0 ≤ (W : ℝ) * d ^ 2 + (W : ℝ)⁻¹ := by positivity
  by_cases hd : d ≤ dstar
  · exact (hloc hd).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hR)
  · exact (cph_offDomain hWr hdstar (lt_of_not_ge hd) hL).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hR)

/-- **`CompensatedIncrementContract` from its scalar-domain statement**: off `d(X) ≤ d_*` both
sides are `O(W)` (`cph_sep_lhs_le`, `cph_com_lhs_le`), hence `O(W d²)`. -/
theorem compensatedIncrement_of_local (hloc : CphIncrementLocal) :
    CompensatedIncrementContract where
  separate := by
    intro b hb0 hb1 κ hκ
    obtain ⟨dstar, C, hd, hC⟩ := hloc.separate b hb0 hb1 κ hκ
    exact ⟨max C (8 / dstar ^ 2), fun W hW X hX E hE =>
      cph_local_extend hW hd (hC W hW X hX E hE) (cph_sep_lhs_le hb1 hκ hE X)⟩
  common := by
    intro b hb0 hb1 κ hκ
    obtain ⟨dstar, C, hd, hC⟩ := hloc.common b hb0 hb1 κ hκ
    exact ⟨max C (8 / dstar ^ 2), fun W hW X hX E hE =>
      cph_local_extend hW hd (hC W hW X hX E hE) (cph_com_lhs_le hb1 hκ hE X)⟩

end Reduction

end BlockBand.Layers
