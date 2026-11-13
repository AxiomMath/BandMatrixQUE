module

public import BlockBand.Transmission.PathScalar.PencilAbs
public import BlockBand.Transmission.PathScalar.Dissipative
public import BlockBand.Transmission.PathScalar.CentreSchur

/-!
# The absorbed near-end path: profile of a deterministic absorption, exact one-port recursion

The `absorbedMoment` clause fixes `r` and `ε : Fin r → ℝ` on the positions of `pathAt W r`.
Position `i` holds the block added at step `r - i`, so `ε` is the profile `absProfile W r ε`
read at the birth times (`layerAbsorption_absProfile`); along the near-end growth `1, …, r`
every block keeps its own absorption.

* `nearSchur_absorbed_eq`: the contract object is `pathNearSchur b E (absProfile W r ε) W r`;
* `ae_pathNearSchur_succ_abs`: a.s., for all `j ≥ 1`,
  `X_{j+1} = freshSchur E (X_j - iε'_j) (freshSample W j)` (absorption moved into the input);
* `ae_pathNearSchur_one`: a.s. `X_1 = freshSchur E (z⁻¹B₀B₀ᴴ - iε'_0) (freshSample W 0)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveCovariance
open scoped ENNReal NNReal Matrix ComplexOrder

variable {W : ℕ}

/-! ## The absorption profile of a deterministic position absorption -/

/-- The profile `κ` with `κ((r-i)/W)/W² = ε_i` (zero off the birth times). -/
def absProfile (W r : ℕ) (ε : Fin r → ℝ) : ℝ → ℝ := fun s =>
  if h : ∃ i : Fin r, s = ((r - i.val : ℕ) : ℝ) / W then (W : ℝ) ^ 2 * ε h.choose else 0

theorem birth_injective {r : ℕ} (hW : 0 < W) {i i' : Fin r}
    (h : ((r - i.val : ℕ) : ℝ) / W = ((r - i'.val : ℕ) : ℝ) / W) : i = i' := by
  have hW' : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  rw [div_left_inj' hW'] at h
  have := i.isLt; have := i'.isLt
  exact Fin.ext (by have := Nat.cast_injective h; omega)

theorem layerAbsorption_absProfile {r : ℕ} (hW : 0 < W) (ε : Fin r → ℝ) :
    layerAbsorption W (absProfile W r ε) r = ε := by
  funext i
  have hex : ∃ i' : Fin r, ((r - i.val : ℕ) : ℝ) / W = ((r - i'.val : ℕ) : ℝ) / W := ⟨i, rfl⟩
  have hW' : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  simp only [layerAbsorption, absProfile, hex, dite_true]
  rw [← birth_injective hW hex.choose_spec]
  field_simp

theorem absProfile_nonneg {r : ℕ} {ε : Fin r → ℝ} (hε : ∀ i, 0 ≤ ε i) (s : ℝ) :
    0 ≤ absProfile W r ε s := by
  unfold absProfile; split_ifs
  · exact mul_nonneg (sq_nonneg _) (hε _)
  · exact le_rfl

theorem absProfile_le {r : ℕ} (hW : 0 < W) {ε : Fin r → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hε : ∀ i, ε i ≤ K / (W : ℝ) ^ 2) (s : ℝ) : absProfile W r ε s ≤ K := by
  have hW2 : (0 : ℝ) < (W : ℝ) ^ 2 := by positivity
  unfold absProfile; split_ifs
  · have := hε (Exists.choose ‹_›)
    rw [le_div_iff₀ hW2] at this; linarith
  · exact hK

/-- Every absorption read from the profile lies in `[0, K/W²]`. -/
theorem layerAbsorption_absProfile_mem {r : ℕ} (hW : 0 < W) {ε : Fin r → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hε : ∀ i, 0 ≤ ε i ∧ ε i ≤ K / (W : ℝ) ^ 2) (m : ℕ) (i : Fin m) :
    0 ≤ layerAbsorption W (absProfile W r ε) m i ∧
      layerAbsorption W (absProfile W r ε) m i ≤ K / (W : ℝ) ^ 2 := by
  have hW2 : (0 : ℝ) < (W : ℝ) ^ 2 := by positivity
  refine ⟨div_nonneg (absProfile_nonneg (fun i => (hε i).1) _) hW2.le, ?_⟩
  exact div_le_div_of_nonneg_right (absProfile_le hW hK (fun i => (hε i).2) _) hW2.le

/-- **The contract object** of `absorbedMoment` is the near-end-grown `X_r` with profile
`absProfile W r ε`. -/
theorem nearSchur_absorbed_eq (b E : ℝ) {r : ℕ} (hW : 0 < W) (ε : Fin r → ℝ) (ω : GrowthPath W) :
    nearSchur (boundaryZ b E) (absorbedPathSchur E ε (pathAt W r ω)) =
      pathNearSchur b E (absProfile W r ε) W r ω := by
  rw [pathNearSchur, layerAbsorption_absProfile hW]

/-! ## The exact one-port recursion, almost surely -/

theorem boundaryZ_ne_zero {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) :
    boundaryZ b E ≠ 0 := fun h => by
  have := boundaryZ_im_pos hb hE1 hE2; rw [h] at this; simp at this

/-- **Bridge (i), absorbed, almost surely**: for `j ≥ 1`,
`X_{j+1} = freshSchur E (X_j - iε'_j) (freshSample W j ω)`, `ε'_j = κ((j+1)/W)/W²`. -/
theorem ae_pathNearSchur_succ_abs {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j → pathNearSchur b E κ W (j + 1) ω =
      freshSchur E (pathNearSchur b E κ W j ω -
        (((layerAbsorption W κ (j + 1) 0 : ℝ) : ℂ) * Complex.I) • 1) (freshSample W j ω) := by
  filter_upwards [ae_passiveSample W hκ (by linarith) hE1 hE2,
    ae_isUnit_absorbedPencil_growth hb hW E κ] with ω hP hF j hj
  exact pathNearSchur_succ_eq_freshSchur b E κ hj ω (boundaryZ_ne_zero (by linarith) hE1 hE2)
    (hF j) (isUnit_farPencil hP j) (hF (j + 1)) (isUnit_farPencil hP (j + 1))

/-- The input of the first step: the far matched lead `z⁻¹B₀B₀ᴴ`. -/
def initialInput (b E : ℝ) (ω : GrowthPath W) : Matrix (Fin W) (Fin W) ℂ :=
  (boundaryZ b E)⁻¹ • (ω.2 0 * (ω.2 0)ᴴ)

/-- The far-lead input is passive (`Im z > 0`). -/
theorem passiveY_initialInput {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (ω : GrowthPath W) : (passiveY (initialInput b E ω)).PosSemidef := by
  rw [passiveY, initialInput, matrixImaginaryPart_smul_hermitian _ _
    (Matrix.isHermitian_mul_conjTranspose_self _), Complex.inv_im, ← neg_smul]
  refine (Matrix.posSemidef_self_mul_conjTranspose _).smul ?_
  rw [Complex.nonneg_iff]
  refine ⟨?_, by simp⟩
  simp only [Complex.neg_re, Complex.ofReal_re, neg_div, neg_neg]
  exact div_nonneg (boundaryZ_im_pos hb hE1 hE2).le (Complex.normSq_nonneg _)

/-- **The first step**: a.s. `X_1 = freshSchur E (z⁻¹B₀B₀ᴴ - iε'_0) (freshSample W 0 ω)` (the far
port eliminated by its matched lead). -/
theorem ae_pathNearSchur_one {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) :
    ∀ᵐ ω ∂growthPathLaw W b, pathNearSchur b E κ W 1 ω =
      freshSchur E (initialInput b E ω -
        (((layerAbsorption W κ 1 0 : ℝ) : ℂ) * Complex.I) • 1) (freshSample W 0 ω) := by
  filter_upwards [ae_passiveSample W hκ (by linarith) hE1 hE2,
    ae_isUnit_absorbedPencil_growth hb hW E κ] with ω hP hF
  obtain ⟨hX, -⟩ := pathNearSchur_eq_lead b E κ 1 ω (boundaryZ_ne_zero (by linarith) hE1 hE2)
    (hF 1) (isUnit_farPencil hP 1)
  let e : Fin W ≃ Fin 1 × Fin W := (Equiv.uniqueProd (Fin W) (Fin 1)).symm
  have hC : (nearCol W 1 ω).submatrix e id = ω.2 1 := by
    ext x y; simp [e, nearCol_apply]
  have hL : (leadPencil b E κ W 1 ω).submatrix e e =
      ω.1 0 - (E : ℂ) • 1 - (initialInput b E ω -
        (((layerAbsorption W κ 1 0 : ℝ) : ℂ) * Complex.I) • 1) := by
    ext x y
    simp only [leadPencil, pathPencil, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, pathMatrix_pathAt_apply, absorptionDiag, Matrix.diagonal_apply,
      Matrix.mul_apply, farCol_apply, Matrix.conjTranspose_apply, initialInput, e,
      Matrix.one_apply]
    simp only [Equiv.uniqueProd_symm_apply, Prod.mk.injEq, true_and, Fin.default_eq_zero]
    split_ifs <;> simp <;> ring
  rw [hX, freshSample, freshSchur_eq, congr_submatrix_equiv _ _ e, hC,
    ← Matrix.inv_submatrix_equiv, hL]

end BlockBand.Transmission.PathScalar
