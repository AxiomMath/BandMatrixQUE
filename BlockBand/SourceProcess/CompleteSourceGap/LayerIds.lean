module

public import BlockBand.SourceProcess.CompleteSourceGap.Bridge
public import BlockBand.SourceProcess.CompleteSourceGap.GapAlgebra
public import BlockBand.SourceProcess.FullSource.WardIdentity

/-!
# Block identities of the fresh layer and of the two-port resolvents

* `layer_identities`: the eight `W × W` block identities of `𝕄𝒢 = 1` and `𝒢𝕄 = 1` for the fresh
  layer `𝕄 = [[A - E - X, B], [B*, w]]` (when `𝕄` is invertible);
* `rowOf`, `colBlock_mul_two`, `nearSel_mul_inv_eq`: a `W × 2W` row is the near row of `M⁻¹` as
  soon as it is a left inverse row of `M`;
* `nearRow_twoPortResolvent`: the near row of `ℝ = (z - 𝕏)⁻¹` is `[R, R𝕏₀₁D⁻¹]`, `D = z - 𝕏₁₁`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveLayer BlockBand.SourceProcess.FullSource
open scoped Matrix ComplexOrder

variable {W : ℕ}

/-- **The fresh-layer block identities** (`𝕄𝒢 = 1` and `𝒢𝕄 = 1`), `A = ω.1 0`, `B = ω.2 0 0`. -/
theorem layer_identities (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort)
    (hM : IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω)) :
    (ω.1 0 - (E : ℂ) • 1 - X) * g11 E w X ω + ω.2 0 0 * g21 E w X ω = 1 ∧
      (ω.1 0 - (E : ℂ) • 1 - X) * g12 E w X ω + ω.2 0 0 * g22 E w X ω = 0 ∧
      (ω.2 0 0)ᴴ * g11 E w X ω + w • g21 E w X ω = 0 ∧
      (ω.2 0 0)ᴴ * g12 E w X ω + w • g22 E w X ω = 1 ∧
      g11 E w X ω * (ω.1 0 - (E : ℂ) • 1 - X) + g12 E w X ω * (ω.2 0 0)ᴴ = 1 ∧
      g11 E w X ω * ω.2 0 0 + g12 E w X ω * (w • 1) = 0 ∧
      g21 E w X ω * (ω.1 0 - (E : ℂ) • 1 - X) + g22 E w X ω * (ω.2 0 0)ᴴ = 0 ∧
      g21 E w X ω * ω.2 0 0 + g22 E w X ω * (w • 1) = 1 := by
  set M := layerMatrix .oneBlockOnePort E w (liftX X) ω with hMdef
  have hd := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have hMG : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hd
  have hGM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hd
  let site : Bool → Fin W → LayerSite W .oneBlockOnePort := fun i x =>
    if i then Sum.inl ((0 : Fin 1), x) else Sum.inr ((0 : Fin 1), x)
  let g : Bool → Bool → Matrix (Fin W) (Fin W) ℂ := fun i j => Matrix.of fun x y =>
    M⁻¹ (site i x) (site j y)
  have h11 : g11 E w X ω = g true true := rfl
  have h12 : g12 E w X ω = g true false := rfl
  have h21 : g21 E w X ω = g false true := rfl
  have h22 : g22 E w X ω = g false false := rfl
  have hfin : ∀ i : Fin 1, i = 0 := fun i => Subsingleton.elim _ _
  have keyL : ∀ (i j : Bool) (x y : Fin W),
      ((if i then (ω.1 0 - (E : ℂ) • 1 - X) else (ω.2 0 0)ᴴ) * g true j +
        (if i then ω.2 0 0 else w • (1 : Matrix (Fin W) (Fin W) ℂ)) * g false j) x y =
        (M * M⁻¹) (site i x) (site j y) := by
    intro i j x y
    cases i <;> cases j <;>
      simp [g, site, hMdef, layerMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
        Fintype.sum_prod_type, BlockBand.Internal.Contracts.Layers.blockDiag, bondMatrix,
        LayerShape.incident, Matrix.one_apply, Matrix.conjTranspose_apply, sub_mul,
        Finset.sum_sub_distrib, liftX, hfin]
  have keyR : ∀ (i j : Bool) (x y : Fin W),
      (g i true * (if j then (ω.1 0 - (E : ℂ) • 1 - X) else ω.2 0 0) +
        g i false * (if j then (ω.2 0 0)ᴴ else w • (1 : Matrix (Fin W) (Fin W) ℂ))) x y =
        (M⁻¹ * M) (site i x) (site j y) := by
    intro i j x y
    cases i <;> cases j <;>
      simp [g, site, hMdef, layerMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
        Fintype.sum_prod_type, BlockBand.Internal.Contracts.Layers.blockDiag, bondMatrix,
        LayerShape.incident, Matrix.one_apply, Matrix.conjTranspose_apply, mul_sub,
        Finset.sum_sub_distrib, liftX, hfin] <;> ring
  rw [hMG] at keyL
  rw [hGM] at keyR
  rw [h11, h12, h21, h22]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext x y
  · simpa [site, Matrix.one_apply] using keyL true true x y
  · simpa [site, Matrix.one_apply] using keyL true false x y
  · simpa [site, Matrix.one_apply] using keyL false true x y
  · simpa [site, Matrix.one_apply] using keyL false false x y
  · simpa [site, Matrix.one_apply] using keyR true true x y
  · simpa [site, Matrix.one_apply] using keyR true false x y
  · simpa [site, Matrix.one_apply] using keyR false true x y
  · simpa [site, Matrix.one_apply] using keyR false false x y

/-- A `W × 2W` row from its two column blocks. -/
def rowOf (P Q : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin 2 × Fin W) ℂ :=
  Matrix.of fun x c => if c.1 = 0 then P x c.2 else Q x c.2

theorem colBlock_rowOf (P Q : Matrix (Fin W) (Fin W) ℂ) (i : Fin 2) :
    colBlock (rowOf P Q) i = if i = 0 then P else Q := by
  ext x y; fin_cases i <;> simp [colBlock, rowOf]

theorem colBlock_mul_two (ρ : Matrix (Fin W) (Fin 2 × Fin W) ℂ)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (k : Fin 2) :
    colBlock (ρ * M) k = colBlock ρ 0 * portBlock M 0 k + colBlock ρ 1 * portBlock M 1 k := by
  ext x y
  simp [colBlock, portBlock, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem colBlock_ext {ρ ρ' : Matrix (Fin W) (Fin 2 × Fin W) ℂ}
    (h : ∀ i, colBlock ρ i = colBlock ρ' i) : ρ = ρ' := by
  ext x ⟨i, y⟩; exact congrFun (congrFun (h i) x) y

theorem colBlock_nearSel (i : Fin 2) :
    colBlock (nearSel W) i = if i = 0 then 1 else 0 := by
  ext x y; fin_cases i <;> simp [colBlock, nearSel, Matrix.one_apply, eq_comm]

/-- A left-inverse row is the near row of the inverse. -/
theorem nearSel_mul_inv_eq (ρ : Matrix (Fin W) (Fin 2 × Fin W) ℂ)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hM : IsUnit M) (h : ρ * M = nearSel W) :
    nearSel W * M⁻¹ = ρ := by
  rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM),
    Matrix.mul_one]

theorem portBlock_smul_one_sub (z : ℂ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (i k : Fin 2) :
    portBlock (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - M) i k =
      (if i = k then z • (1 : Matrix (Fin W) (Fin W) ℂ) else 0) - portBlock M i k := by
  ext x y
  by_cases h : i = k
  · subst h; simp [portBlock, Matrix.one_apply]
  · simp [portBlock, h]

/-- **Near row of the old resolvent**: `ι*ℝ = [R, R𝕏₀₁D⁻¹]` (Hermitian `𝕏`, `Im z > 0`). -/
theorem nearRow_twoPortResolvent (b E : ℝ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) :
    nearSel W * twoPortResolvent b E XX =
      rowOf (passiveResolvent b E (nearSchur (boundaryZ b E) XX))
        (passiveResolvent b E (nearSchur (boundaryZ b E) XX) * portBlock XX 0 1 *
          (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1)⁻¹) := by
  set z := boundaryZ b E
  have hz : 0 < z.im := hη
  set X := nearSchur z XX
  set D := z • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1
  have hD : IsUnit D := BlockBand.Transmission.portPencil_isUnit _ (portBlock_isHermitian hXX 1) hz
  have hDD : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  have hY : (passiveY X).PosSemidef := nearSchur_passive hz hXX
  have hK : IsUnit (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X) := by
    apply BlockBand.Transmission.isUnit_of_matrixImaginaryPart_posDef
    rw [BlockBand.Transmission.PassiveCovariance.matrixImaginaryPart_nearPencil]
    exact Matrix.PosDef.posSemidef_add hY (Matrix.PosDef.one.smul hη)
  have hRK : passiveResolvent b E X * (z • 1 - X) = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hK)
  apply nearSel_mul_inv_eq _ _ (BlockBand.Transmission.portPencil_isUnit XX hXX hz)
  apply colBlock_ext
  intro k
  rw [colBlock_mul_two, colBlock_rowOf, colBlock_rowOf, colBlock_nearSel]
  change _ * portBlock (z • 1 - XX) 0 k + _ * portBlock (z • 1 - XX) 1 k = _
  rw [portBlock_smul_one_sub, portBlock_smul_one_sub]
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, ite_true, one_ne_zero, ite_false, zero_sub]
    refine Eq.trans ?_ hRK
    simp only [X, D, nearSchur, Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_add, Matrix.mul_assoc]
    abel
  · simp only [Fin.mk_one, Fin.isValue, zero_ne_one, ite_false, zero_sub, ite_true, one_ne_zero]
    rw [show D = z • 1 - portBlock XX 1 1 from rfl] at hDD
    rw [Matrix.mul_neg, Matrix.mul_assoc _ (z • 1 - portBlock XX 1 1)⁻¹, hDD, Matrix.mul_one]
    abel

end BlockBand.SourceProcess.CompleteSourceGap
