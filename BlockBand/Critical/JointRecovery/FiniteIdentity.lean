module

public import BlockBand.Critical.JointRecovery.ExtractionMeasurable
public import BlockBand.Critical.PhysicalOrderedReadback
public import BlockBand.Model.Construction.PhysicalCanonicalLaw

/-!
# Joint recovery: the finite-width identities

* `D_W = finiteEntireDeterminant p E (fullProfile q) H` is good (`D_W(0) = 1`, its axis zeros
  are exactly `-W²(λ_α - E)`, real and simple);
* for every test `f`, the readout `Σ_α f(u_α, (ν_α(q_a))_a)` of the physical unfolded marked
  configuration (`u = Nρ(E)(λ - E)`) equals the root/derivative extraction
  `Σ_{zeros x} f(rootDerivativePoint E (n/W) D_W x)` (`τ_W = n/W`, not its limit);
* two distinct axis zeros in `(x, y)` give two unfolded eigenvalues in the image interval.
Consequence `readoutLaplace_markedLaw_eq`: `readoutLaplace q (R.markedLaw E) f` is the
extracted Laplace value of the finite law of `D_W`. Exact identities, no limit, no uniformity
needed. Uses `physicalOrdered_profile_readback_ae`, `physicalOrderedMarkedConfig_ae` and
`finiteRealization_markedLaw_eq_canonical`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.JointRecovery

open Filter Topology Set MeasureTheory
open BlockBand.Critical.Entire BlockBand.Critical.Entire.EntireFunction
open BlockBand.Internal.Contracts.CriticalEntire BlockBand.Model.Construction
open scoped Matrix

variable {p : Parameters}

/-- The source matrices `Q_a = profileSourceMatrix (fullProfile q a)` (`Q_0 = I`). -/
def sourceMatrices (p : Parameters) {k : ℕ} (q : Fin k → C(Torus, ℝ)) :
    Fin (k + 1) → p.SiteMatrix :=
  fun a => p.profileSourceMatrix (fullProfile q a)

theorem sourceMatrices_zero {k : ℕ} (q : Fin k → C(Torus, ℝ)) : sourceMatrices p q 0 = 1 := by
  simp only [sourceMatrices, fullProfile, Fin.cons_zero]
  exact p.profileSourceMatrix_one

theorem coe_finiteEntireDeterminant (E : ℝ) {k : ℕ} (q : Fin k → C(Torus, ℝ)) (H : p.SiteMatrix)
    (hA : (H - (E : ℂ) • (1 : p.SiteMatrix)).det ≠ 0) :
    ⇑(finiteEntireDeterminant p E (fullProfile q) H) =
      physicalFiniteDeterminant (H - (E : ℂ) • (1 : p.SiteMatrix)) (sourceMatrices p q) p.W hA := by
  funext z
  simp only [finiteEntireDeterminant, coe_ofDifferentiable, physicalFiniteDeterminant,
    normalizedEntireDeterminant, div_eq_mul_inv]
  rfl

theorem measurable_finiteEntireDeterminant (E : ℝ) {m : ℕ} (Q : Fin m → C(Torus, ℝ)) :
    Measurable (finiteEntireDeterminant p E Q) := by
  apply EntireFunction.measurable_iff_eval.mpr
  intro z
  have h1 : Continuous fun H : p.SiteMatrix =>
      BlockBand.Critical.finiteCharacteristicDeterminant (H - (E : ℂ) • 1)
        (fun a => p.profileSourceMatrix (Q a)) (BlockBand.Critical.widthSourceScale p.W) z := by
    unfold BlockBand.Critical.finiteCharacteristicDeterminant
      BlockBand.Critical.finiteCharacteristicPencil
    exact ((continuous_id.sub continuous_const).add continuous_const).matrix_det
  have h2 : Continuous fun H : p.SiteMatrix => (H - (E : ℂ) • (1 : p.SiteMatrix)).det :=
    (continuous_id.sub continuous_const).matrix_det
  exact h1.measurable.mul h2.measurable.inv

/-- Partial derivatives as derivatives along coordinate lines. -/
theorem partialDerivValue_eq_deriv_line {m : ℕ} (a : Fin m) (F : EntireFunction m)
    (z : Fin m → ℂ) :
    partialDerivValue a F z = deriv (fun t : ℂ => F (z + Pi.single a t)) 0 := by
  rw [← EntireFunction.deriv_coordinateSlice_zero]
  congr 1
  funext t
  congr 1
  funext i
  by_cases hi : i = a
  · subst hi; simp [EntireFunction.coordinateLine, add_comm]
  · simp [EntireFunction.coordinateLine, hi]

theorem partialDerivValue_finiteEntireDeterminant (E : ℝ) {k : ℕ} (q : Fin k → C(Torus, ℝ))
    (H : p.SiteMatrix) (hA : (H - (E : ℂ) • (1 : p.SiteMatrix)).det ≠ 0) (z : ℂ)
    (a : Fin (k + 1)) :
    partialDerivValue a (finiteEntireDeterminant p E (fullProfile q) H)
        (BlockBand.Critical.energySource z) =
      BlockBand.Critical.finiteSourcePartial (H - (E : ℂ) • (1 : p.SiteMatrix))
        (sourceMatrices p q) p.W hA z a := by
  rw [partialDerivValue_eq_deriv_line, coe_finiteEntireDeterminant E q H hA]
  rfl

/-- A Hermitian shift is singular exactly at an eigenvalue. -/
theorem det_sub_smul_eq_zero_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (c : ℂ) :
    (H - c • (1 : Matrix ι ι ℂ)).det = 0 ↔ ∃ i, c = (hH.eigenvalues i : ℂ) := by
  have h : H - c • (1 : Matrix ι ι ℂ) = -(Matrix.scalar ι c - H) := by
    rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [h, Matrix.det_neg, ← Matrix.eval_charpoly, hH.charpoly_eq, Polynomial.eval_prod,
    mul_eq_zero, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

/-- The rank-to-site bijection of the ordered physical spectrum. -/
def rankSite (p : Parameters) : Fin p.N ≃ p.Site :=
  (finCongr (physicalSite_card p).symm).trans BlockBand.Foundations.Spectral.increasingIndex

theorem physicalOrderedEigenvalue_eq (H : p.SiteMatrix) (hH : H.IsHermitian) (α : Fin p.N) :
    physicalOrderedEigenvalue p H α = hH.eigenvalues (rankSite p α) := by
  unfold physicalOrderedEigenvalue
  rw [rawIncreasingEigenvalue_eq _ H hH, ← BlockBand.Foundations.Spectral.eigenvalue_increasingIndex]
  rfl

/-- The finite zero `x_α = -W²(λ_α - E)`. -/
def finiteZero (p : Parameters) (E : ℝ) (H : p.SiteMatrix) (α : Fin p.N) : ℝ :=
  -(p.W : ℝ) ^ 2 * (physicalOrderedEigenvalue p H α - E)

theorem finiteZero_cast (E : ℝ) (H : p.SiteMatrix) (α : Fin p.N) :
    ((finiteZero p E H α : ℝ) : ℂ) = -(p.W : ℂ) ^ 2 * ((physicalOrderedEigenvalue p H α : ℂ) - E) := by
  simp [finiteZero]

theorem widthSourceScale_mul (W : ℕ) (w : ℂ) :
    BlockBand.Critical.widthSourceScale W * w = w / (W : ℂ) ^ 2 := by
  unfold BlockBand.Critical.widthSourceScale
  rw [inv_pow, div_eq_inv_mul]

/-- The axis of the finite determinant vanishes exactly at the finite zeros. -/
theorem axis_finiteEntireDeterminant_eq_zero_iff (E : ℝ) {k : ℕ} (q : Fin k → C(Torus, ℝ))
    (H : p.SiteMatrix) (hH : H.IsHermitian) (hA : (H - (E : ℂ) • (1 : p.SiteMatrix)).det ≠ 0)
    (w : ℂ) :
    axis (finiteEntireDeterminant p E (fullProfile q) H) w = 0 ↔
      ∃ α, w = ((finiteZero p E H α : ℝ) : ℂ) := by
  have hW : (p.W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp p.W_pos)
  rw [axis_apply, coe_finiteEntireDeterminant E q H hA]
  change (BlockBand.Critical.finiteCharacteristicPencil (H - (E : ℂ) • 1) (sourceMatrices p q)
    (BlockBand.Critical.widthSourceScale p.W) (BlockBand.Critical.energySource w)).det /
      (H - (E : ℂ) • (1 : p.SiteMatrix)).det = 0 ↔ _
  rw [BlockBand.Critical.finiteCharacteristicPencil_energySource _ _ _ _ (sourceMatrices_zero q),
    div_eq_zero_iff, or_iff_left hA, smul_smul, widthSourceScale_mul]
  have hshift : H - (E : ℂ) • (1 : p.SiteMatrix) + (w / (p.W : ℂ) ^ 2) • (1 : p.SiteMatrix) =
      H - ((E : ℂ) - w / (p.W : ℂ) ^ 2) • (1 : p.SiteMatrix) := by
    rw [sub_smul]; abel
  rw [hshift, det_sub_smul_eq_zero_iff hH]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨(rankSite p).symm i, ?_⟩
    rw [finiteZero_cast, physicalOrderedEigenvalue_eq H hH, Equiv.apply_symm_apply, ← hi]
    field_simp
    ring
  · rintro ⟨α, rfl⟩
    refine ⟨rankSite p α, ?_⟩
    rw [finiteZero_cast, ← physicalOrderedEigenvalue_eq H hH]
    field_simp
    ring

/-- The physical unfolding of the finite zeros: `-(n/W)ρ x_α = Nρ(λ_α - E)`. -/
theorem unfold_finiteZero (E : ℝ) (H : p.SiteMatrix) (α : Fin p.N) :
    -(((p.n : ℝ) / p.W) * Parameters.semicircleDensity E) * finiteZero p E H α =
      p.N * Parameters.semicircleDensity E * (physicalOrderedEigenvalue p H α - E) := by
  have hW : (p.W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp p.W_pos)
  simp only [finiteZero, Parameters.N, Nat.cast_mul]
  field_simp

end BlockBand.Critical.JointRecovery
