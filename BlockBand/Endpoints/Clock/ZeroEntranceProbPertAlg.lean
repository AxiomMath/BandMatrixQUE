module

public import BlockBand.Endpoints.Clock.ZeroEntranceProbFluct
public import BlockBand.Endpoints.Clock.ZeroEntranceProbNorm
public import BlockBand.Layers.ComparisonStability

/-!
# The zero-entrance lemma (deterministic part): one layer as a bounded factor

For an initial deterministic `D`, the mean changes by at most `C_J‖D‖`. We avoid estimating real
cavity inverses, which may be large: instead of unitary scattering matrices we use the blocks of the (bounded in `L^p`) layer
resolvent `𝒢 = [[A - e - X, B], [B*, ζ']]⁻¹` directly. With `P_X = A - e - X`,
`X₊ = B* P_X⁻¹ B`, `S_X = ζ' - X₊`:
* `layerResolvent_norm_eq`, `freshSchur_eq_plain`: the one-block layer objects are reindexings of
  the plain `2W × 2W` block matrix;
* `norm_blocks_le`: `‖S⁻¹B*P⁻¹‖, ‖P⁻¹BS⁻¹‖, ‖S⁻¹‖ ≤ ‖𝒢‖` (Schur complement formula);
* `resolvent_diff_step`: for Hermitian old inputs `X, Y` and any `ζ` in the upper half-plane,
  `‖S_X⁻¹ - S_Y⁻¹‖ ≤ (‖𝒢_X‖ a) ‖(ζ - X)⁻¹ - (ζ - Y)⁻¹‖ (‖𝒢_Y‖ a)`, `a = |ζ| + |e| + ‖A‖ + ‖B‖`:
  the difference of two resolvents of the old inputs propagates through one layer with a factor
  that never contains a real cavity inverse;
* `resolvent_diff_first`: `‖S_X⁻¹ - S_Y⁻¹‖ ≤ ‖𝒢_X‖ ‖X - Y‖ ‖𝒢_Y‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements (freshSchur)
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace ZeroEntranceProb

variable {W : ℕ}

/-- The reindexing `Fin 1 × Fin W ≃ Fin W`. -/
abbrev fe (W : ℕ) : Fin 1 × Fin W ≃ Fin W := Equiv.uniqueProd (Fin W) (Fin 1)

/-- The plain top block `P = A - e - X`. -/
def topP (e : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y : OneEndedLayer W) : Matrix (Fin W) (Fin W) ℂ :=
  y.1 0 - (e : ℂ) • 1 - X

/-- The plain layer matrix `[[P, B], [B*, ζ']]`. -/
def plainLayer (e : ℝ) (ζ : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (y : OneEndedLayer W) :
    Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ :=
  fromBlocks (topP e X y) (y.2 0 0) (y.2 0 0)ᴴ (ζ • 1)

theorem blockDiag_oneBlock (y : OneEndedLayer W) :
    Internal.Contracts.Layers.blockDiag y.1 = (y.1 0).submatrix (fe W) (fe W) := by
  ext x z
  obtain ⟨a, i⟩ := x
  obtain ⟨c, j⟩ := z
  have ha : a = 0 := Subsingleton.elim _ _
  have hc : c = 0 := Subsingleton.elim _ _
  subst ha hc
  simp [Internal.Contracts.Layers.blockDiag]

theorem top_lift_eq (e : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y : OneEndedLayer W) :
    Internal.Contracts.Layers.blockDiag y.1 - (e : ℂ) • 1 - cavityLift X =
      (topP e X y).submatrix (fe W) (fe W) := by
  rw [blockDiag_oneBlock, CavityMeanProb.cavityLift_eq]
  ext x z
  obtain ⟨a, i⟩ := x
  obtain ⟨c, j⟩ := z
  have ha : a = 0 := Subsingleton.elim _ _
  have hc : c = 0 := Subsingleton.elim _ _
  subst ha hc
  simp [topP, Matrix.one_apply]

theorem isUnit_top_iff (e : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y : OneEndedLayer W) :
    IsUnit (Internal.Contracts.Layers.blockDiag y.1 - (e : ℂ) • 1 - cavityLift X).det ↔ IsUnit (topP e X y).det := by
  rw [top_lift_eq, det_submatrix_equiv_self]

theorem freshSchur_eq_plain (e : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y : OneEndedLayer W) :
    freshSchur e X y = (y.2 0 0)ᴴ * (topP e X y)⁻¹ * y.2 0 0 := by
  have h : layerSchur .oneBlockOnePort e (cavityLift X) y =
      ((y.2 0 0)ᴴ * (topP e X y)⁻¹ * y.2 0 0).submatrix (fe W) (fe W) := by
    unfold layerSchur
    rw [top_lift_eq, ZeroEntranceNorm.bondMatrix_oneBlock_eq, inv_submatrix_equiv,
      conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
  ext x z
  have := congrFun (congrFun h ((0 : Fin 1), x)) ((0 : Fin 1), z)
  simp only [freshSchur, Matrix.of_apply]
  exact this

theorem layerMatrix_eq_plain (e : ℝ) (ζ : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (y : OneEndedLayer W) :
    layerMatrix .oneBlockOnePort e ζ (cavityLift X) y =
      (plainLayer e ζ X y).submatrix (Equiv.sumCongr (fe W) (fe W)) (Equiv.sumCongr (fe W) (fe W)) := by
  unfold layerMatrix plainLayer
  rw [top_lift_eq, ZeroEntranceNorm.bondMatrix_oneBlock_eq]
  ext x z
  rcases x with ⟨a, i⟩ | ⟨a, i⟩ <;> rcases z with ⟨c, j⟩ | ⟨c, j⟩ <;>
  · have ha : a = 0 := Subsingleton.elim _ _
    have hc : c = 0 := Subsingleton.elim _ _
    subst ha hc
    simp [Matrix.one_apply]

theorem layerResolvent_norm_eq (e : ℝ) (ζ : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (y : OneEndedLayer W) :
    ‖layerResolvent .oneBlockOnePort e ζ (cavityLift X) y‖ = ‖(plainLayer e ζ X y)⁻¹‖ := by
  unfold layerResolvent
  rw [layerMatrix_eq_plain, inv_submatrix_equiv]
  exact opNorm_submatrix_equiv _ _

section Blocks

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem inv_sub_inv {M N : Matrix n n ℂ} (hM : IsUnit M.det) (hN : IsUnit N.det) :
    M⁻¹ - N⁻¹ = M⁻¹ * (N - M) * N⁻¹ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv N hN,
    Matrix.mul_one, Matrix.nonsing_inv_mul M hM, Matrix.one_mul]

/-- **Schur blocks of the layer resolvent**: `‖S⁻¹B*P⁻¹‖, ‖P⁻¹BS⁻¹‖, ‖S⁻¹‖ ≤ ‖𝒢‖`. -/
theorem norm_blocks_le (P B : Matrix n n ℂ) (ζ : ℂ) (hP : IsUnit P.det)
    (hS : IsUnit (ζ • (1 : Matrix n n ℂ) - Bᴴ * P⁻¹ * B).det) :
    ‖(ζ • (1 : Matrix n n ℂ) - Bᴴ * P⁻¹ * B)⁻¹ * Bᴴ * P⁻¹‖ ≤ ‖(fromBlocks P B Bᴴ (ζ • 1))⁻¹‖ ∧
      ‖P⁻¹ * B * (ζ • (1 : Matrix n n ℂ) - Bᴴ * P⁻¹ * B)⁻¹‖ ≤ ‖(fromBlocks P B Bᴴ (ζ • 1))⁻¹‖ ∧
      ‖(ζ • (1 : Matrix n n ℂ) - Bᴴ * P⁻¹ * B)⁻¹‖ ≤ ‖(fromBlocks P B Bᴴ (ζ • 1))⁻¹‖ := by
  let := invertibleOfIsUnitDet P hP
  have hS2 : IsUnit (ζ • (1 : Matrix n n ℂ) - Bᴴ * ⅟P * B).det := by rwa [invOf_eq_nonsing_inv]
  let := invertibleOfIsUnitDet _ hS2
  let := fromBlocks₁₁Invertible P B Bᴴ (ζ • (1 : Matrix n n ℂ))
  have h := invOf_fromBlocks₁₁_eq P B Bᴴ (ζ • (1 : Matrix n n ℂ))
  simp only [invOf_eq_nonsing_inv] at h
  refine ⟨?_, ?_, ?_⟩
  · have := opNorm_toBlocks21_le (fromBlocks P B Bᴴ (ζ • (1 : Matrix n n ℂ)))⁻¹
    rw [h, toBlocks_fromBlocks₂₁, norm_neg] at this
    rw [h]; exact this
  · have := opNorm_toBlocks12_le (fromBlocks P B Bᴴ (ζ • (1 : Matrix n n ℂ)))⁻¹
    rw [h, toBlocks_fromBlocks₁₂, norm_neg] at this
    rw [h]; exact this
  · have := opNorm_toBlocks22_le (fromBlocks P B Bᴴ (ζ • (1 : Matrix n n ℂ)))⁻¹
    rw [h, toBlocks_fromBlocks₂₂] at this
    rw [h]; exact this

theorem norm_smul_one_le (c : ℂ) : ‖c • (1 : Matrix n n ℂ)‖ ≤ ‖c‖ :=
  (norm_smul_le _ _).trans (by
    have := BlockBand.Layers.lct_norm_one_le (n := n)
    nlinarith [norm_nonneg c])

/-- One layer propagates a resolvent difference of the old inputs with a bounded factor. -/
theorem resolvent_diff_step (A B X Y : Matrix n n ℂ) (e : ℝ) (ζ ζ' : ℂ)
    (hPX : IsUnit (A - (e : ℂ) • 1 - X).det) (hPY : IsUnit (A - (e : ℂ) • 1 - Y).det)
    (hSX : IsUnit (ζ' • (1 : Matrix n n ℂ) - Bᴴ * (A - (e : ℂ) • 1 - X)⁻¹ * B).det)
    (hSY : IsUnit (ζ' • (1 : Matrix n n ℂ) - Bᴴ * (A - (e : ℂ) • 1 - Y)⁻¹ * B).det)
    (hRX : IsUnit (ζ • (1 : Matrix n n ℂ) - X).det) (hRY : IsUnit (ζ • (1 : Matrix n n ℂ) - Y).det) :
    ‖(ζ' • (1 : Matrix n n ℂ) - Bᴴ * (A - (e : ℂ) • 1 - X)⁻¹ * B)⁻¹ -
        (ζ' • (1 : Matrix n n ℂ) - Bᴴ * (A - (e : ℂ) • 1 - Y)⁻¹ * B)⁻¹‖ ≤
      (‖(fromBlocks (A - (e : ℂ) • 1 - X) B Bᴴ (ζ' • 1))⁻¹‖ * (‖ζ‖ + |e| + ‖A‖ + ‖B‖)) *
        ‖(ζ • (1 : Matrix n n ℂ) - X)⁻¹ - (ζ • (1 : Matrix n n ℂ) - Y)⁻¹‖ *
        (‖(fromBlocks (A - (e : ℂ) • 1 - Y) B Bᴴ (ζ' • 1))⁻¹‖ * (‖ζ‖ + |e| + ‖A‖ + ‖B‖)) := by
  set PX := A - (e : ℂ) • (1 : Matrix n n ℂ) - X with hPXd
  set PY := A - (e : ℂ) • (1 : Matrix n n ℂ) - Y with hPYd
  set SX := ζ' • (1 : Matrix n n ℂ) - Bᴴ * PX⁻¹ * B with hSXd
  set SY := ζ' • (1 : Matrix n n ℂ) - Bᴴ * PY⁻¹ * B with hSYd
  set RX := ζ • (1 : Matrix n n ℂ) - X with hRXd
  set RY := ζ • (1 : Matrix n n ℂ) - Y with hRYd
  set T := RX⁻¹ - RY⁻¹ with hT
  set C := (ζ + (e : ℂ)) • (1 : Matrix n n ℂ) - A with hC
  have hXY : X - Y = RX * T * RY := by
    rw [hT, inv_sub_inv hRX hRY, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hRY,
      Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hRX, Matrix.one_mul, hRXd, hRYd]
    abel
  have hS : SX⁻¹ - SY⁻¹ = (SX⁻¹ * Bᴴ * PX⁻¹) * (X - Y) * (PY⁻¹ * B * SY⁻¹) := by
    have h1 : SY - SX = Bᴴ * (PX⁻¹ * (X - Y) * PY⁻¹) * B := by
      have h2 : PX⁻¹ - PY⁻¹ = PX⁻¹ * (X - Y) * PY⁻¹ := by
        rw [inv_sub_inv hPX hPY]; congr 2; rw [hPXd, hPYd]; abel
      rw [← h2, hSXd, hSYd, Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [inv_sub_inv hSX hSY, h1]
    simp only [Matrix.mul_assoc]
  have hRXe : RX = PX + C := by rw [hRXd, hPXd, hC, add_smul]; abel
  have hRYe : RY = PY + C := by rw [hRYd, hPYd, hC, add_smul]; abel
  have hL : SX⁻¹ * Bᴴ * PX⁻¹ * RX = SX⁻¹ * Bᴴ + SX⁻¹ * Bᴴ * PX⁻¹ * C := by
    rw [hRXe, Matrix.mul_add, Matrix.mul_assoc (SX⁻¹ * Bᴴ), Matrix.nonsing_inv_mul _ hPX,
      Matrix.mul_one]
  have hR : RY * (PY⁻¹ * B * SY⁻¹) = B * SY⁻¹ + C * (PY⁻¹ * B * SY⁻¹) := by
    rw [hRYe, Matrix.add_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hPY, Matrix.one_mul]
  have hfac : SX⁻¹ - SY⁻¹ = (SX⁻¹ * Bᴴ * PX⁻¹ * RX) * T * (RY * (PY⁻¹ * B * SY⁻¹)) := by
    rw [hS, hXY]; simp only [Matrix.mul_assoc]
  obtain ⟨bX1, -, bX3⟩ := norm_blocks_le PX B ζ' hPX hSX
  obtain ⟨-, bY2, bY3⟩ := norm_blocks_le PY B ζ' hPY hSY
  have hCn : ‖C‖ ≤ ‖ζ‖ + |e| + ‖A‖ := by
    refine (norm_sub_le _ _).trans ?_
    have := norm_smul_one_le (n := n) (ζ + (e : ℂ))
    have h2 : ‖ζ + (e : ℂ)‖ ≤ ‖ζ‖ + |e| := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
    linarith
  set GX := ‖(fromBlocks PX B Bᴴ (ζ' • 1))⁻¹‖
  set GY := ‖(fromBlocks PY B Bᴴ (ζ' • 1))⁻¹‖
  set a := ‖ζ‖ + |e| + ‖A‖ + ‖B‖ with ha
  have hB0 : 0 ≤ ‖B‖ := norm_nonneg _
  have hLn : ‖SX⁻¹ * Bᴴ * PX⁻¹ * RX‖ ≤ GX * a := by
    rw [hL]
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖SX⁻¹ * Bᴴ‖ ≤ GX * ‖B‖ := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    have e2 : ‖SX⁻¹ * Bᴴ * PX⁻¹ * C‖ ≤ GX * (‖ζ‖ + |e| + ‖A‖) :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul bX1 hCn (norm_nonneg _) (norm_nonneg _))
    have : GX * ‖B‖ + GX * (‖ζ‖ + |e| + ‖A‖) = GX * a := by rw [ha]; ring
    linarith
  have hRn : ‖RY * (PY⁻¹ * B * SY⁻¹)‖ ≤ GY * a := by
    rw [hR]
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖B * SY⁻¹‖ ≤ ‖B‖ * GY :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left bY3 hB0)
    have e2 : ‖C * (PY⁻¹ * B * SY⁻¹)‖ ≤ (‖ζ‖ + |e| + ‖A‖) * GY :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hCn bY2 (norm_nonneg _) (by positivity))
    have : ‖B‖ * GY + (‖ζ‖ + |e| + ‖A‖) * GY = GY * a := by rw [ha]; ring
    linarith
  rw [hfac]
  refine (Matrix.l2_opNorm_mul _ _).trans ?_
  refine mul_le_mul ((Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul_of_nonneg_right hLn (norm_nonneg _))) hRn (norm_nonneg _) (by positivity)

/-- The first layer: `‖S_X⁻¹ - S_Y⁻¹‖ ≤ ‖𝒢_X‖ ‖X - Y‖ ‖𝒢_Y‖`. -/
theorem resolvent_diff_first (A B X Y : Matrix n n ℂ) (e : ℝ) (ζ' : ℂ)
    (hPX : IsUnit (A - (e : ℂ) • 1 - X).det) (hPY : IsUnit (A - (e : ℂ) • 1 - Y).det)
    (hSX : IsUnit (ζ' • (1 : Matrix n n ℂ) - Bᴴ * (A - (e : ℂ) • 1 - X)⁻¹ * B).det)
    (hSY : IsUnit (ζ' • (1 : Matrix n n ℂ) - Bᴴ * (A - (e : ℂ) • 1 - Y)⁻¹ * B).det) :
    ‖(ζ' • (1 : Matrix n n ℂ) - Bᴴ * (A - (e : ℂ) • 1 - X)⁻¹ * B)⁻¹ -
        (ζ' • (1 : Matrix n n ℂ) - Bᴴ * (A - (e : ℂ) • 1 - Y)⁻¹ * B)⁻¹‖ ≤
      ‖(fromBlocks (A - (e : ℂ) • 1 - X) B Bᴴ (ζ' • 1))⁻¹‖ * ‖X - Y‖ *
        ‖(fromBlocks (A - (e : ℂ) • 1 - Y) B Bᴴ (ζ' • 1))⁻¹‖ := by
  set PX := A - (e : ℂ) • (1 : Matrix n n ℂ) - X with hPXd
  set PY := A - (e : ℂ) • (1 : Matrix n n ℂ) - Y with hPYd
  set SX := ζ' • (1 : Matrix n n ℂ) - Bᴴ * PX⁻¹ * B with hSXd
  set SY := ζ' • (1 : Matrix n n ℂ) - Bᴴ * PY⁻¹ * B with hSYd
  have hS : SX⁻¹ - SY⁻¹ = (SX⁻¹ * Bᴴ * PX⁻¹) * (X - Y) * (PY⁻¹ * B * SY⁻¹) := by
    have h1 : SY - SX = Bᴴ * (PX⁻¹ * (X - Y) * PY⁻¹) * B := by
      have h2 : PX⁻¹ - PY⁻¹ = PX⁻¹ * (X - Y) * PY⁻¹ := by
        rw [inv_sub_inv hPX hPY]; congr 2; rw [hPXd, hPYd]; abel
      rw [← h2, hSXd, hSYd, Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [inv_sub_inv hSX hSY, h1]
    simp only [Matrix.mul_assoc]
  obtain ⟨bX1, -, -⟩ := norm_blocks_le PX B ζ' hPX hSX
  obtain ⟨-, bY2, -⟩ := norm_blocks_le PY B ζ' hPY hSY
  rw [hS]
  refine (Matrix.l2_opNorm_mul _ _).trans ?_
  exact mul_le_mul ((Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul_of_nonneg_right bX1 (norm_nonneg _))) bY2 (norm_nonneg _) (by positivity)

end Blocks

end ZeroEntranceProb

end BlockBand.Endpoints.Clock
