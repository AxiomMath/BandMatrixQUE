module

public import BlockBand.DeterminantScore.PhysicalColumn
public import BlockBand.DeterminantScore.SignedRowSpread
public import BlockBand.DeterminantScore.NegativeSpreadLaw

/-!
# Restoring the deleted row at fixed outer data

At fixed outer data and minor, the selected row sector can occur only if `N_-(B) ∈ {ℓ-1, ℓ}`. On
`{V_B ≤ A}` one drops the selected sign restriction in the nonnegative numerator `det(M)²U` and
applies the signed row spread; restoring `det(B)²q_B²`, the complete row mass, its two possible
Schur signs give full sectors among `ℓ-1, ℓ, ℓ+1`.

`gue_tail`: for Hermitian `K` on `Fin m`, `m = k + 1`, a unit eigenvector `w` of `K`
(`Kw = μw`), an orthonormal frame `V` of `w^⊥` (`V*V = 1`, `V*w = 0`), `G ~ GUE_m(t)`, `t > 0`,
`n, α ∈ ℕ`, `A ∈ ℝ`, with `M = K + G`, `B = V*MV`:
`E[det(M)² 1{N_-(M) + n = α} 1{Tr B⁻² ≤ A} Tr M⁻²]
   ≤ (2A + t⁻¹) Σ_{ℓ ∈ {α-1, α, α+1}} E[det(M)² 1{N_-(M) + n = ℓ}]`.

Proof: rotate `[w | V]` to the standard basis (`frameCompletion`, unitary invariance of
`G_m(t)`), so `K` becomes block diagonal `diag(μ, V*KV)` (`frameCompletion_block`); split the
whitened coordinates into the deleted row and the minor (`lintegral_hermGaussian_row`); the row
coordinates have the law `rowLaw k t` of the signed row spread (`rowLaw_eq_std`) and the minor
coordinates the law `G_k(t)` (`map_restVal`), under which `B` is a.s. invertible; at fixed
invertible minor, `M = [[μ+x, y*], [y, B]]` (`row_block_eq`), `det(M)² = det(B)²a²`
(`det_rowMatrix`), the selected sign is dropped, `E_{x,y} a²U ≤ (2V_B + t⁻¹)q_B²` and
`E_{x,y} a² = q_B²` (`SignedRowSpread.signedRowSpread`), and on an attained sector every row value
lies in a neighbouring sector (`PhysicalColumn.sector_neighbour`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.MinorTail

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.DeterminantScore.GaussianGradient BlockBand.DeterminantScore.PhysicalColumn
open scoped NNReal ENNReal

variable {k : ℕ}

/-- `Fin (k+1) ≃ Unit ⊕ Fin k`, `0 ↦ inl`, `j+1 ↦ inr j`. -/
def finSplit (k : ℕ) : Fin (k + 1) ≃ Unit ⊕ Fin k where
  toFun := Fin.cases (Sum.inl ()) Sum.inr
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv a := by cases a using Fin.cases <;> simp
  right_inv z := by rcases z with _ | j <;> simp

/-- The row coordinates: `(0,0)`, `(0,j+1)` (real part) and `(j+1,0)` (imaginary part). -/
def rowIdxOf : Unit ⊕ (Fin k × Fin 2) → RowIdx (k + 1)
  | Sum.inl _ => ⟨(0, 0), Or.inl rfl⟩
  | Sum.inr (j, b) => if b = 0 then ⟨(0, j.succ), Or.inl rfl⟩ else ⟨(j.succ, 0), Or.inr rfl⟩

def rowIdxInv (c : RowIdx (k + 1)) : Unit ⊕ (Fin k × Fin 2) :=
  if h1 : c.1.1 = 0 then
    (if h2 : c.1.2 = 0 then Sum.inl () else Sum.inr (c.1.2.pred h2, 0))
  else Sum.inr (c.1.1.pred h1, 1)

def rowEquiv (k : ℕ) : Unit ⊕ (Fin k × Fin 2) ≃ RowIdx (k + 1) where
  toFun := rowIdxOf
  invFun := rowIdxInv
  left_inv z := by
    rcases z with _ | ⟨j, b⟩
    · simp [rowIdxOf, rowIdxInv]
    · fin_cases b <;> simp [rowIdxOf, rowIdxInv, Fin.succ_ne_zero]
  right_inv c := by
    obtain ⟨⟨a, b⟩, h⟩ := c
    simp only [IsRow] at h
    by_cases ha : a = 0
    · subst ha
      by_cases hb : b = 0
      · subst hb; simp [rowIdxOf, rowIdxInv]
      · simp [rowIdxOf, rowIdxInv, hb]
    · have hb : b = 0 := h.resolve_left ha
      subst hb; simp [rowIdxOf, rowIdxInv, ha]

/-- Row values `(x, y)` (`x = M₀₀ - μ`, `y_j = M_{j+1,0}`) from the row coordinates. -/
def rowVal (σ : HermCoord (k + 1) → ℝ) (u : RowIdx (k + 1) → ℝ) : ℝ × (Fin k → ℂ) :=
  (σ (0, 0) * u (rowEquiv k (Sum.inl ())),
   fun j => ((σ (0, j.succ) * u (rowEquiv k (Sum.inr (j, 0))) : ℝ) : ℂ) -
     ((σ (j.succ, 0) * u (rowEquiv k (Sum.inr (j, 1))) : ℝ) : ℂ) * Complex.I)

/-- The remaining coordinates are those of the minor. -/
def restOf (c : HermCoord k) : RestIdx (k + 1) :=
  ⟨(c.1.succ, c.2.succ), by simp [IsRow, Fin.succ_ne_zero]⟩

def restEquiv (k : ℕ) : HermCoord k ≃ RestIdx (k + 1) where
  toFun := restOf
  invFun c := (c.1.1.pred (fun h => c.2 (Or.inl h)), c.1.2.pred (fun h => c.2 (Or.inr h)))
  left_inv c := by simp [restOf]
  right_inv c := by
    apply Subtype.ext
    simp [restOf]

/-- The minor coordinates, `G_B(w)`. -/
def restVal (t : ℝ≥0) (w : RestIdx (k + 1) → ℝ) : HermCoord k → ℝ :=
  fun c => hermSd k t c * w (restEquiv k c)

theorem hermSd_succ (t : ℝ≥0) (a b : Fin k) :
    hermSd (k + 1) t (a.succ, b.succ) = hermSd k t (a, b) := by
  simp [hermSd, hermVariance, Fin.succ_inj]

theorem row_block_eq (K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (μ : ℝ) (h00 : K 0 0 = μ)
    (h0j : ∀ j : Fin k, K 0 j.succ = 0) (hj0 : ∀ j : Fin k, K j.succ 0 = 0) (t : ℝ≥0)
    (u : RowIdx (k + 1) → ℝ) (w : RestIdx (k + 1) → ℝ) :
    K + hermOfCoord (rowPoint (hermSd (k + 1) t) u w) =
      (rowMatrix μ (rowVal (hermSd (k + 1) t) u).1 (rowVal (hermSd (k + 1) t) u).2
        (K.submatrix Fin.succ Fin.succ + hermOfCoord (restVal t w))).submatrix
        (finSplit k) (finSplit k) := by
  ext a b
  cases a using Fin.cases <;> cases b using Fin.cases
  · simp [rowMatrix, hermOfCoord, rowPoint, rowVal, finSplit, h00, rowEquiv, rowIdxOf, IsRow]
  · have h0 : ∀ j : Fin k, (0 : Fin (k + 1)) ≠ j.succ := fun j h => Fin.succ_ne_zero j h.symm
    simp [rowMatrix, hermOfCoord, rowPoint, rowVal, finSplit, h0j, rowEquiv, rowIdxOf, IsRow, h0]
  · simp [rowMatrix, hermOfCoord, rowPoint, rowVal, finSplit, hj0, rowEquiv, rowIdxOf, IsRow,
      Fin.succ_ne_zero]
  · simp [rowMatrix, hermOfCoord, rowPoint, rowVal, finSplit, IsRow, restVal, restEquiv, restOf,
      hermSd_succ, Fin.succ_ne_zero]

/-!
## The row law
-/

instance isProbabilityMeasure_std (ι : Type) [Fintype ι] :
    IsProbabilityMeasure (standardGaussianCoordinates (ι := ι)) := by
  unfold standardGaussianCoordinates; infer_instance

theorem measurable_rowVal (σ : HermCoord (k + 1) → ℝ) : Measurable (rowVal σ) := by
  unfold rowVal
  refine Measurable.prodMk ((measurable_pi_apply _).const_mul _) (measurable_pi_iff.mpr fun j => ?_)
  refine (Complex.measurable_ofReal.comp ((measurable_pi_apply _).const_mul _)).sub
    ((Complex.measurable_ofReal.comp ((measurable_pi_apply _).const_mul _)).mul_const _)

theorem std_eq_map_piCongrLeft :
    standardGaussianCoordinates (ι := RowIdx (k + 1)) =
      (standardGaussianCoordinates (ι := Unit ⊕ (Fin k × Fin 2))).map
        (MeasurableEquiv.piCongrLeft (fun _ : RowIdx (k + 1) => ℝ) (rowEquiv k)) :=
  ((measurePreserving_piCongrLeft (fun _ : RowIdx (k + 1) => gaussianReal 0 1)
    (rowEquiv k)).map_eq).symm

theorem std_sum_eq :
    (standardGaussianCoordinates (ι := Unit ⊕ (Fin k × Fin 2))).map
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ (Fin k × Fin 2) => ℝ)) =
      (standardGaussianCoordinates (ι := Unit)).prod
        (standardGaussianCoordinates (ι := Fin k × Fin 2)) :=
  (measurePreserving_sumPiEquivProdPi (fun _ : Unit ⊕ (Fin k × Fin 2) => gaussianReal 0 1)).map_eq

/-- The sign/scale map onto the `N(0,1/2)` coordinates of the circular law. -/
def circScale (r : Fin k × Fin 2 → ℝ) : Fin k × Fin 2 → ℝ :=
  fun c => (if c.2 = 0 then Real.sqrt (1 / 2) else -Real.sqrt (1 / 2)) * r c

theorem map_circScale :
    (standardGaussianCoordinates (ι := Fin k × Fin 2)).map circScale =
      Measure.pi fun _ : Fin k × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0) := by
  unfold standardGaussianCoordinates circScale
  rw [Measure.pi_map_pi (fun c => (measurable_const_mul _).aemeasurable)]
  congr 1
  funext c
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  split_ifs <;> simp [Real.sq_sqrt]

theorem rowLaw_eq_std (t : ℝ≥0) :
    (standardGaussianCoordinates (ι := RowIdx (k + 1))).map (rowVal (hermSd (k + 1) t)) =
      rowLaw k t := by
  set σ := hermSd (k + 1) t
  set pcl := MeasurableEquiv.piCongrLeft (fun _ : RowIdx (k + 1) => ℝ) (rowEquiv k)
  set spe := MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ (Fin k × Fin 2) => ℝ)
  set f₁ : (Unit → ℝ) → ℝ := fun a => σ (0, 0) * a ()
  set ψ₂ : (Fin k × Fin 2 → ℝ) → (Fin k → ℂ) := fun r j =>
    ((σ (0, j.succ) * r (j, 0) : ℝ) : ℂ) - ((σ (j.succ, 0) * r (j, 1) : ℝ) : ℂ) * Complex.I
  have hf₁ : Measurable f₁ := (measurable_pi_apply _).const_mul _
  have hψ₂ : Measurable ψ₂ := by
    refine measurable_pi_iff.mpr fun j => ?_
    exact (Complex.measurable_ofReal.comp ((measurable_pi_apply _).const_mul _)).sub
      ((Complex.measurable_ofReal.comp ((measurable_pi_apply _).const_mul _)).mul_const _)
  have hfun : rowVal σ ∘ pcl = Prod.map f₁ ψ₂ ∘ spe := by
    funext v
    simp only [Function.comp_apply, rowVal, pcl, spe, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_apply, Prod.map, f₁, ψ₂]
    rfl
  rw [std_eq_map_piCongrLeft, Measure.map_map (measurable_rowVal σ) pcl.measurable, hfun,
    ← Measure.map_map (hf₁.prodMap hψ₂) spe.measurable, std_sum_eq,
    ← Measure.map_prod_map _ _ hf₁ hψ₂]
  unfold rowLaw
  congr 1
  · have hu := (measurePreserving_funUnique (gaussianReal 0 1) Unit).map_eq
    have hf : f₁ = (fun x => σ (0, 0) * x) ∘ MeasurableEquiv.funUnique Unit ℝ := by
      funext a; rfl
    unfold standardGaussianCoordinates
    rw [hf, ← Measure.map_map (measurable_const_mul _) (MeasurableEquiv.measurable _), hu,
      gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp [σ, hermSd, hermVariance, Real.sq_sqrt]
  · have hs : Measurable fun g : Fin k → ℂ => (Real.sqrt (t : ℝ) : ℂ) • g :=
      (continuous_const_smul _).measurable
    have hc : Measurable fun (r : Fin k × Fin 2 → ℝ) (a : Fin k) =>
        (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I := by fun_prop
    have hcs : Measurable (circScale (k := k)) :=
      measurable_pi_iff.mpr fun c => (measurable_pi_apply c).const_mul _
    unfold circularVectorLaw
    rw [← map_circScale, Measure.map_map hc hcs, Measure.map_map hs (hc.comp hcs)]
    congr 1
    funext r j
    have h2 : Real.sqrt ((t : ℝ) / 2) = Real.sqrt t * Real.sqrt (1 / 2) := by
      rw [← Real.sqrt_mul (NNReal.coe_nonneg t)]; ring_nf
    have hσ1 : σ (0, j.succ) = Real.sqrt ((t : ℝ) / 2) := by
      simp [σ, hermSd, hermVariance, (Fin.succ_ne_zero j).symm]
    have hσ2 : σ (j.succ, 0) = Real.sqrt ((t : ℝ) / 2) := by
      simp [σ, hermSd, hermVariance, Fin.succ_ne_zero j]
    simp only [ψ₂, Function.comp_apply, circScale, Pi.smul_apply, smul_eq_mul, hσ1, hσ2, h2]
    simp
    ring

/-!
## The minor coordinates
-/

theorem measurable_restVal (t : ℝ≥0) : Measurable (restVal (k := k) t) :=
  measurable_pi_iff.mpr fun _ => (measurable_pi_apply _).const_mul _

theorem map_restVal (t : ℝ≥0) :
    (standardGaussianCoordinates (ι := RestIdx (k + 1))).map (restVal t) = hermGaussian k t := by
  set pcl := MeasurableEquiv.piCongrLeft (fun _ : RestIdx (k + 1) => ℝ) (restEquiv k)
  have hmp := (measurePreserving_piCongrLeft (fun _ : RestIdx (k + 1) => gaussianReal 0 1)
    (restEquiv k)).symm
  have hsymm : ∀ w : RestIdx (k + 1) → ℝ, pcl.symm w = fun c => w (restEquiv k c) := by
    intro w
    rw [MeasurableEquiv.symm_apply_eq]
    funext i
    obtain ⟨_, rfl⟩ := (restEquiv k).surjective i
    simp [pcl, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  have hfun : restVal t = (fun (y : HermCoord k → ℝ) c => hermSd k t c * y c) ∘ pcl.symm := by
    funext w c
    simp only [Function.comp_apply, hsymm, restVal]
  have h2 : (standardGaussianCoordinates (ι := RestIdx (k + 1))).map pcl.symm =
      standardGaussianCoordinates (ι := HermCoord k) := hmp.map_eq
  rw [hfun, ← Measure.map_map (measurable_pi_iff.mpr fun c => (measurable_pi_apply c).const_mul _)
    pcl.symm.measurable, h2, hermGaussian_eq_map]

theorem ae_minor_det_ne_zero {t : ℝ≥0} (ht : 0 < t) (KB : Matrix (Fin k) (Fin k) ℂ) :
    ∀ᵐ w ∂standardGaussianCoordinates (ι := RestIdx (k + 1)),
      (KB + hermOfCoord (restVal t w)).det ≠ 0 :=
  ae_of_ae_map (measurable_restVal t).aemeasurable (by rw [map_restVal]; exact ae_det_ne_zero ht KB)

/-!
## Block algebra of the row matrix
-/

/-- `Tr M⁻²` (real part). -/
def invSq {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : ℝ := (M⁻¹ * M⁻¹).trace.re

theorem invSq_submatrix {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι ι ℂ) (e : κ ≃ ι) : invSq (M.submatrix e e) = invSq M := by
  unfold invSq
  rw [inv_submatrix_equiv, submatrix_mul_equiv]
  congr 1
  simp only [trace, diag, submatrix_apply]
  exact Equiv.sum_comp e (fun i => (M⁻¹ * M⁻¹) i i)

theorem measurable_invSq {ι : Type} [Fintype ι] [DecidableEq ι] :
    Measurable (invSq (ι := ι)) := by
  unfold invSq
  have h := measurable_inv_matrix (κ := ι)
  exact Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp
    (measurable_matMul h h))

theorem invSq_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) : 0 ≤ invSq M := by
  have := Row.hermitian_square_trace_re_nonneg M⁻¹ hM.inv
  simpa [invSq, sq] using this

theorem rowMatrix_isHermitian (μ x : ℝ) (y : Fin k → ℂ) {B : Matrix (Fin k) (Fin k) ℂ}
    (hB : B.IsHermitian) : (rowMatrix μ x y B).IsHermitian := by
  unfold rowMatrix
  refine IsHermitian.fromBlocks ?_ ?_ hB
  · ext a b; simp
  · ext a b; simp

theorem det_rowMatrix (μ x : ℝ) (y : Fin k → ℂ) {B : Matrix (Fin k) (Fin k) ℂ}
    (hB : B.IsHermitian) (hdet : B.det ≠ 0) :
    Complex.normSq (rowMatrix μ x y B).det = Complex.normSq B.det * rowSchur μ B (x, y) ^ 2 := by
  have : Invertible B := B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hdet)
  unfold rowMatrix
  rw [det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv, Complex.normSq_mul]
  congr 1
  rw [Matrix.det_unique]
  have hq := SignedRowSpread.quad_im_eq_zero B⁻¹ hB.inv y
  have he : (Matrix.of (fun (_ : Unit) (_ : Unit) => ((μ + x : ℝ) : ℂ)) -
      Matrix.of (fun (_ : Unit) j => star (y j)) * B⁻¹ * Matrix.of (fun j (_ : Unit) => y j))
        default default = ((μ + x : ℝ) : ℂ) - star y ⬝ᵥ (B⁻¹ *ᵥ y) := by
    simp [Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [he]
  have hr : ((μ + x : ℝ) : ℂ) - star y ⬝ᵥ (B⁻¹ *ᵥ y) = ((rowSchur μ B (x, y) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [rowSchur]
    · simp [rowSchur, hq]
  rw [hr, Complex.normSq_ofReal, sq]

/-!
## The row restoration at a fixed minor
-/

/-- `Tr B⁻²` of the minor on the indices `1, …, k`. -/
def minorInvSq (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℝ :=
  invSq (M.submatrix Fin.succ Fin.succ)

/-- The tail integrand `det(M)² 1{sector} 1{V_B ≤ A} Tr M⁻²`. -/
def tailInt (n α : ℕ) (A : ℝ) (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (secW n α M) * (if minorInvSq M ≤ A then ENNReal.ofReal (invSq M) else 0)

theorem continuous_rowMatrix (μ : ℝ) (B : Matrix (Fin k) (Fin k) ℂ) :
    Continuous fun z : ℝ × (Fin k → ℂ) => rowMatrix μ z.1 z.2 B := by
  unfold rowMatrix
  refine continuous_pi fun a => continuous_pi fun b => ?_
  rcases a with _ | a <;> rcases b with _ | b <;> simp only [fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply] <;> fun_prop

/-- **Row restoration at a fixed invertible minor.** -/
theorem row_restore_fixed {K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hK : K.IsHermitian)
    {t : ℝ≥0} (ht : 0 < t) (μ : ℝ) (h00 : K 0 0 = μ) (h0j : ∀ j : Fin k, K 0 j.succ = 0)
    (hj0 : ∀ j : Fin k, K j.succ 0 = 0) (n α : ℕ) {A : ℝ} (w : RestIdx (k + 1) → ℝ)
    (hw : (K.submatrix Fin.succ Fin.succ + hermOfCoord (restVal t w)).det ≠ 0) :
    (∫⁻ u, tailInt n α A (K + hermOfCoord (rowPoint (hermSd (k + 1) t) u w))
        ∂standardGaussianCoordinates (ι := RowIdx (k + 1))) ≤
      ENNReal.ofReal (2 * A + (t : ℝ)⁻¹) *
        ∫⁻ u, (ENNReal.ofReal (secW n (α - 1) (K + hermOfCoord (rowPoint (hermSd (k + 1) t) u w))) +
          ENNReal.ofReal (secW n α (K + hermOfCoord (rowPoint (hermSd (k + 1) t) u w))) +
          ENNReal.ofReal (secW n (α + 1) (K + hermOfCoord (rowPoint (hermSd (k + 1) t) u w))))
          ∂standardGaussianCoordinates (ι := RowIdx (k + 1)) := by
  set σ := hermSd (k + 1) t
  set Mu := fun u : RowIdx (k + 1) → ℝ => K + hermOfCoord (rowPoint σ u w) with hMudef
  set B := K.submatrix Fin.succ Fin.succ + hermOfCoord (restVal t w) with hBdef
  set R := fun z : ℝ × (Fin k → ℂ) => rowMatrix μ z.1 z.2 B with hRdef
  have hBH : B.IsHermitian := by
    refine IsHermitian.add ?_ (isHermitian_hermOfCoord _)
    exact hK.submatrix _
  have hMuH : ∀ u, (Mu u).IsHermitian := fun u => hK.add (isHermitian_hermOfCoord _)
  have hMu : ∀ u, Mu u = (R (rowVal σ u)).submatrix (finSplit k) (finSplit k) :=
    fun u => row_block_eq K μ h00 h0j hj0 t u w
  have hminor : ∀ u, minorInvSq (Mu u) = invSq B := by
    intro u
    unfold minorInvSq
    congr 1
    rw [hMu u]
    ext a b
    simp [R, rowMatrix, finSplit]
  change (∫⁻ u, tailInt n α A (Mu u) ∂standardGaussianCoordinates (ι := RowIdx (k + 1))) ≤
    ENNReal.ofReal (2 * A + (t : ℝ)⁻¹) * ∫⁻ u, (ENNReal.ofReal (secW n (α - 1) (Mu u)) +
      ENNReal.ofReal (secW n α (Mu u)) + ENNReal.ofReal (secW n (α + 1) (Mu u)))
      ∂standardGaussianCoordinates (ι := RowIdx (k + 1))
  -- outside the event or an unattained sector, the integrand vanishes
  by_cases hVA : invSq B ≤ A
  swap
  · refine le_trans (le_of_eq ?_) (zero_le)
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun u => ?_)
    simp [tailInt, hminor u, hVA]
  by_cases hatt : ∃ u₀, negativeCount (Mu u₀) + n = α
  swap
  · simp only [not_exists] at hatt
    refine le_trans (le_of_eq ?_) (zero_le)
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun u => ?_)
    simp [tailInt, secW, hatt u]
  obtain ⟨u₀, hu₀⟩ := hatt
  -- the signed row spread at the minor `B`
  have hS := SignedRowSpread.signedRowSpread k t μ B ht hBH hw
  dsimp only at hS
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS
  set V := (B⁻¹ * B⁻¹).trace.re with hV
  set δ := μ - (t : ℝ) * B⁻¹.trace.re
  set q2 := δ ^ 2 + (t : ℝ) + (t : ℝ) ^ 2 * V with hq2
  have hV0 : 0 ≤ V := invSq_nonneg hBH
  have hVA' : V ≤ A := hVA
  have htpos : (0 : ℝ) < t := ht
  have hq2pos : 0 < q2 := by positivity
  have hint1 : Integrable (fun z => rowSchur μ B z ^ 2) (rowLaw k t) := by
    by_contra hni
    rw [integral_undef hni] at h1
    linarith
  have hlin1 : (∫⁻ z, ENNReal.ofReal (rowSchur μ B z ^ 2) ∂rowLaw k t) = ENNReal.ofReal q2 := by
    rw [← h1, ofReal_integral_eq_lintegral_ofReal hint1 (ae_of_all _ fun z => sq_nonneg _)]
  have hF0 : ∀ z : ℝ × (Fin k → ℂ), 0 ≤ rowSchur μ B z ^ 2 * invSq (R z) := fun z =>
    mul_nonneg (sq_nonneg _) (invSq_nonneg (rowMatrix_isHermitian μ z.1 z.2 hBH))
  have hlin2 : (∫⁻ z, ENNReal.ofReal (rowSchur μ B z ^ 2 * invSq (R z)) ∂rowLaw k t) ≤
      ENNReal.ofReal ((2 * V + (t : ℝ)⁻¹) * q2) := by
    have hF : (∫ z, rowSchur μ B z ^ 2 * invSq (R z) ∂rowLaw k t) ≤ (2 * V + (t : ℝ)⁻¹) * q2 :=
      (le_of_eq (h3.trans h4)).trans h5
    rw [← ofReal_integral_eq_lintegral_ofReal (f := fun z => rowSchur μ B z ^ 2 * invSq (R z)) h2
      (ae_of_all _ hF0)]
    exact ENNReal.ofReal_le_ofReal hF
  -- transport between the row coordinates and the row law
  have hRc := continuous_rowMatrix μ B
  have hdetR : ∀ z : ℝ × (Fin k → ℂ), Complex.normSq (R z).det =
      Complex.normSq B.det * rowSchur μ B z ^ 2 := fun z => det_rowMatrix μ z.1 z.2 hBH hw
  have hmG1 : Measurable fun z : ℝ × (Fin k → ℂ) =>
      ENNReal.ofReal (Complex.normSq (R z).det * invSq (R z)) :=
    ENNReal.measurable_ofReal.comp
      (((Complex.continuous_normSq.comp (continuous_id.matrix_det)).comp hRc).measurable.mul
        (measurable_invSq.comp hRc.measurable))
  have hmG2 : Measurable fun z : ℝ × (Fin k → ℂ) => ENNReal.ofReal (Complex.normSq (R z).det) :=
    ENNReal.measurable_ofReal.comp
      ((Complex.continuous_normSq.comp (continuous_id.matrix_det)).comp hRc).measurable
  have htr1 : (∫⁻ u, ENNReal.ofReal (Complex.normSq (Mu u).det * invSq (Mu u))
      ∂standardGaussianCoordinates (ι := RowIdx (k + 1))) =
      ∫⁻ z, ENNReal.ofReal (Complex.normSq (R z).det * invSq (R z)) ∂rowLaw k t := by
    rw [← rowLaw_eq_std, lintegral_map hmG1 (measurable_rowVal σ)]
    refine lintegral_congr fun u => ?_
    rw [hMu u, det_submatrix_equiv_self, invSq_submatrix]
  have htr2 : (∫⁻ u, ENNReal.ofReal (Complex.normSq (Mu u).det)
      ∂standardGaussianCoordinates (ι := RowIdx (k + 1))) =
      ∫⁻ z, ENNReal.ofReal (Complex.normSq (R z).det) ∂rowLaw k t := by
    rw [← rowLaw_eq_std, lintegral_map hmG2 (measurable_rowVal σ)]
    refine lintegral_congr fun u => ?_
    rw [hMu u, det_submatrix_equiv_self]
  have hnB : 0 ≤ Complex.normSq B.det := Complex.normSq_nonneg _
  -- the chain
  have hstep1 : ∀ u, tailInt n α A (Mu u) ≤
      ENNReal.ofReal (Complex.normSq (Mu u).det * invSq (Mu u)) := by
    intro u
    unfold tailInt
    simp only [hminor u, hVA, ↓reduceIte]
    rw [← ENNReal.ofReal_mul (secW_nonneg _ _ _)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (invSq_nonneg (hMuH u)))
    unfold secW
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]; exact Complex.normSq_nonneg _
  have hstep3 : ∀ u, ENNReal.ofReal (Complex.normSq (Mu u).det) ≤
      ENNReal.ofReal (secW n (α - 1) (Mu u)) + ENNReal.ofReal (secW n α (Mu u)) +
        ENNReal.ofReal (secW n (α + 1) (Mu u)) := by
    intro u
    have hagree := hermOfCoord_row_agree K 0 (y := rowPoint σ u₀ w)
      (y' := rowPoint σ u w) (fun c h1 h2 => by
        have hc : ¬ IsRow c := by unfold IsRow; tauto
        simp only [rowPoint, hc, ↓reduceDIte])
    rcases sector_neighbour (hMuH u₀) (hMuH u) 0 hagree hu₀ with h | h | h
    · refine le_trans ?_ (le_add_right (le_add_right le_rfl))
      simp [secW, h]
    · refine le_trans ?_ (le_add_right (le_add_left le_rfl))
      simp [secW, h]
    · refine le_trans ?_ (le_add_left le_rfl)
      simp [secW, h]
  calc (∫⁻ u, tailInt n α A (Mu u) ∂standardGaussianCoordinates (ι := RowIdx (k + 1)))
      ≤ ∫⁻ u, ENNReal.ofReal (Complex.normSq (Mu u).det * invSq (Mu u))
          ∂standardGaussianCoordinates (ι := RowIdx (k + 1)) := lintegral_mono hstep1
    _ = ∫⁻ z, ENNReal.ofReal (Complex.normSq B.det) *
          ENNReal.ofReal (rowSchur μ B z ^ 2 * invSq (R z)) ∂rowLaw k t := by
        rw [htr1]
        refine lintegral_congr fun z => ?_
        rw [← ENNReal.ofReal_mul hnB, hdetR z, mul_assoc]
    _ = ENNReal.ofReal (Complex.normSq B.det) *
          ∫⁻ z, ENNReal.ofReal (rowSchur μ B z ^ 2 * invSq (R z)) ∂rowLaw k t :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Complex.normSq B.det) * ENNReal.ofReal ((2 * V + (t : ℝ)⁻¹) * q2) := by
        gcongr
    _ = ENNReal.ofReal (2 * V + (t : ℝ)⁻¹) *
          (ENNReal.ofReal (Complex.normSq B.det) * ENNReal.ofReal q2) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        ring
    _ = ENNReal.ofReal (2 * V + (t : ℝ)⁻¹) *
          ∫⁻ u, ENNReal.ofReal (Complex.normSq (Mu u).det)
            ∂standardGaussianCoordinates (ι := RowIdx (k + 1)) := by
        rw [htr2, ← hlin1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        refine lintegral_congr fun z => ?_
        rw [← ENNReal.ofReal_mul hnB, hdetR z]
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) (lintegral_mono hstep3)

theorem measurable_tailInt (n α : ℕ) (A : ℝ) :
    Measurable (tailInt (k := k) n α A) := by
  unfold tailInt
  have hm : Measurable (minorInvSq (k := k)) :=
    measurable_invSq.comp (continuous_id.matrix_submatrix _ _).measurable
  exact (ENNReal.measurable_ofReal.comp (measurable_secW n α)).mul
    (Measurable.ite (measurableSet_le hm measurable_const)
      (ENNReal.measurable_ofReal.comp measurable_invSq) measurable_const)

/-- **Row restoration in the coordinates of `G_{k+1}(t)`** (`K` block diagonal in `e₀`). -/
theorem coord_restore {K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hK : K.IsHermitian)
    {t : ℝ≥0} (ht : 0 < t) (μ : ℝ) (h00 : K 0 0 = μ) (h0j : ∀ j : Fin k, K 0 j.succ = 0)
    (hj0 : ∀ j : Fin k, K j.succ 0 = 0) (n α : ℕ) (A : ℝ) :
    (∫⁻ y, tailInt n α A (K + hermOfCoord y) ∂hermGaussian (k + 1) t) ≤
      ENNReal.ofReal (2 * A + (t : ℝ)⁻¹) *
        ((∫⁻ y, ENNReal.ofReal (secW n (α - 1) (K + hermOfCoord y)) ∂hermGaussian (k + 1) t) +
          (∫⁻ y, ENNReal.ofReal (secW n α (K + hermOfCoord y)) ∂hermGaussian (k + 1) t) +
          (∫⁻ y, ENNReal.ofReal (secW n (α + 1) (K + hermOfCoord y)) ∂hermGaussian (k + 1) t)) := by
  have hcont : Continuous fun y : HermCoord (k + 1) → ℝ => K + hermOfCoord y :=
    continuous_const.add continuous_hermOfCoord
  have hmS : ∀ ℓ, Measurable fun y : HermCoord (k + 1) → ℝ =>
      ENNReal.ofReal (secW n ℓ (K + hermOfCoord y)) := fun ℓ =>
    ENNReal.measurable_ofReal.comp ((measurable_secW n ℓ).comp hcont.measurable)
  have hmL : Measurable fun y : HermCoord (k + 1) → ℝ => tailInt n α A (K + hermOfCoord y) :=
    (measurable_tailInt n α A).comp hcont.measurable
  have hm3 : Measurable fun y : HermCoord (k + 1) → ℝ =>
      ENNReal.ofReal (secW n (α - 1) (K + hermOfCoord y)) +
        ENNReal.ofReal (secW n α (K + hermOfCoord y)) +
        ENNReal.ofReal (secW n (α + 1) (K + hermOfCoord y)) :=
    ((hmS _).add (hmS _)).add (hmS _)
  rw [← lintegral_add_right _ (hmS _), ← lintegral_add_right _ (hmS _),
    lintegral_hermGaussian_row t _ hmL, lintegral_hermGaussian_row t _ hm3,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_minor_det_ne_zero ht (K.submatrix Fin.succ Fin.succ)] with w hw
  exact row_restore_fixed hK ht μ h00 h0j hj0 n α w hw

/-!
## Rotation of the eigenvector to `e₀`
-/

theorem invSq_unitary_conj {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) {W : Matrix (Fin m) (Fin m) ℂ}
    (hW : Wᴴ * W = 1) : invSq (Wᴴ * M * W) = invSq M := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  unfold invSq
  rw [inv_unitary_conj _ hW]
  have : Wᴴ * M⁻¹ * W * (Wᴴ * M⁻¹ * W) = Wᴴ * (M⁻¹ * M⁻¹) * W := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W, hW', Matrix.one_mul]
  rw [this, Matrix.trace_mul_cycle, hW', Matrix.one_mul]

/-- The unitary `[w | V]`. -/
def frameCompletion (w : Fin (k + 1) → ℂ) (V : Matrix (Fin (k + 1)) (Fin k) ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.of fun a b => Fin.cases (w a) (fun j => V a j) b

theorem frameCompletion_unitary {w : Fin (k + 1) → ℂ} (hw : l2Norm w = 1)
    {V : Matrix (Fin (k + 1)) (Fin k) ℂ} (hV : Vᴴ * V = 1) (hVw : Vᴴ *ᵥ w = 0) :
    (frameCompletion w V)ᴴ * frameCompletion w V = 1 := by
  have hww : star w ⬝ᵥ w = 1 := by
    rw [← ofReal_sum_norm_sq, ← l2Norm_sq', hw]; simp
  have hVw' : ∀ j, ∑ a, star (V a j) * w a = 0 := by
    intro j
    have := congrFun hVw j
    simpa [mulVec, dotProduct, conjTranspose_apply] using this
  have hVV : ∀ i j, ∑ a, star (V a i) * V a j = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hV i) j
    simpa [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply] using this
  ext a b
  cases a using Fin.cases <;> cases b using Fin.cases
  · simpa [frameCompletion, Matrix.mul_apply, dotProduct] using hww
  · rename_i j
    have h := congrArg star (hVw' j)
    simp only [star_sum, star_mul, star_star, star_zero] at h
    have h0 : (0 : Fin (k + 1)) ≠ j.succ := fun h => Fin.succ_ne_zero j h.symm
    simpa [frameCompletion, Matrix.mul_apply, mul_comm, Matrix.one_apply, h0] using h
  · rename_i i
    simpa [frameCompletion, Matrix.mul_apply, Fin.succ_ne_zero] using hVw' i
  · rename_i i j
    simpa [frameCompletion, Matrix.mul_apply, Matrix.one_apply, Fin.succ_inj] using hVV i j

theorem frameCompletion_succ (w : Fin (k + 1) → ℂ) (V : Matrix (Fin (k + 1)) (Fin k) ℂ)
    (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    ((frameCompletion w V)ᴴ * X * frameCompletion w V).submatrix Fin.succ Fin.succ = Vᴴ * X * V := by
  ext i j
  simp [frameCompletion, Matrix.mul_apply]

/-- The rotated deformation `K' = [w|V]* K [w|V]` is block diagonal with corner `μ`. -/
theorem frameCompletion_block {K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hK : K.IsHermitian)
    {w : Fin (k + 1) → ℂ} (hw : l2Norm w = 1) {μ : ℝ} (hKw : K *ᵥ w = (μ : ℂ) • w)
    {V : Matrix (Fin (k + 1)) (Fin k) ℂ} (hVw : Vᴴ *ᵥ w = 0) :
    let K' := (frameCompletion w V)ᴴ * K * frameCompletion w V
    K' 0 0 = μ ∧ (∀ j : Fin k, K' 0 j.succ = 0) ∧ (∀ j : Fin k, K' j.succ 0 = 0) := by
  intro K'
  have hww : star w ⬝ᵥ w = 1 := by
    rw [← ofReal_sum_norm_sq, ← l2Norm_sq', hw]; simp
  have hwK : star w ᵥ* K = (μ : ℂ) • star w := by
    have h1 : star (K *ᵥ w) = star w ᵥ* Kᴴ := star_mulVec K w
    rw [hK.eq, hKw] at h1
    rw [← h1, star_smul, Complex.star_def, Complex.conj_ofReal]
  have e00 : K' 0 0 = star w ⬝ᵥ (K *ᵥ w) := by
    simp [K', frameCompletion, Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [e00, hKw, dotProduct_smul, hww, smul_eq_mul, mul_one]
  · intro j
    have e : K' 0 j.succ = (star w ᵥ* K) ⬝ᵥ (fun a => V a j) := by
      simp [K', frameCompletion, Matrix.mul_apply, dotProduct, vecMul, Finset.sum_mul]
    rw [e, hwK, smul_dotProduct]
    have := congrArg star (congrFun hVw j)
    simp only [mulVec, dotProduct, conjTranspose_apply, star_sum, star_mul, star_star,
      Pi.zero_apply, star_zero] at this
    simp only [dotProduct, Pi.star_apply, smul_eq_mul]
    rw [show (∑ x, star (w x) * V x j) = 0 by simpa [mul_comm] using this, mul_zero]
  · intro j
    have e : K' j.succ 0 = (fun a => star (V a j)) ⬝ᵥ (K *ᵥ w) := by
      simp [K', frameCompletion, Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
    rw [e, hKw, dotProduct_smul]
    have := congrFun hVw j
    simp only [mulVec, dotProduct, conjTranspose_apply, Pi.zero_apply] at this
    simp only [dotProduct, smul_eq_mul]
    rw [this, mul_zero]

/-!
## The fixed-`θ` tail bound under `GUE`
-/

/-- `det(X)² 1{sector α} 1{Tr (V*XV)⁻² ≤ A} Tr X⁻²`. -/
def tailW {m k : ℕ} (V : Matrix (Fin m) (Fin k) ℂ) (n α : ℕ) (A : ℝ)
    (X : Matrix (Fin m) (Fin m) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (secW n α X) * (if invSq (Vᴴ * X * V) ≤ A then ENNReal.ofReal (invSq X) else 0)

theorem measurable_tailW {m k : ℕ} (V : Matrix (Fin m) (Fin k) ℂ) (n α : ℕ) (A : ℝ) :
    Measurable (tailW V n α A) := by
  unfold tailW
  have hm : Measurable fun X : Matrix (Fin m) (Fin m) ℂ => invSq (Vᴴ * X * V) :=
    measurable_invSq.comp ((continuous_const.matrix_mul continuous_id).matrix_mul
      continuous_const).measurable
  exact (ENNReal.measurable_ofReal.comp (measurable_secW n α)).mul
    (Measurable.ite (measurableSet_le hm measurable_const)
      (ENNReal.measurable_ofReal.comp measurable_invSq) measurable_const)

theorem tailW_conj {w : Fin (k + 1) → ℂ} {V : Matrix (Fin (k + 1)) (Fin k) ℂ}
    (hF : (frameCompletion w V)ᴴ * frameCompletion w V = 1) (n α : ℕ) (A : ℝ)
    {Y : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hY : Y.IsHermitian) :
    tailW V n α A (frameCompletion w V * Y * (frameCompletion w V)ᴴ) = tailInt n α A Y := by
  set F := frameCompletion w V
  have hF' : (Fᴴ)ᴴ * Fᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp hF
  have e1 : F * Y * Fᴴ = (Fᴴ)ᴴ * Y * Fᴴ := by rw [conjTranspose_conjTranspose]
  have e2 : Vᴴ * (F * Y * Fᴴ) * V = Y.submatrix Fin.succ Fin.succ := by
    rw [← frameCompletion_succ w V]
    congr 1
    simp only [F, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (frameCompletion w V)ᴴ, hF, Matrix.one_mul]
    rw [Matrix.mul_one]
  unfold tailW tailInt minorInvSq
  rw [e2, e1, secW_unitary_conj hY hF', invSq_unitary_conj _ hF']

/-- **Fixed-`θ` tail bound.** For Hermitian `K` with a unit eigenvector `w` (eigenvalue `μ`) and
an orthonormal frame `V` of `w^⊥`: the selected numerator of `1{V_B ≤ A} Tr M⁻²`,
`B = V*MV`, is at most `(2A + t⁻¹)` times the three neighbouring sector masses. -/
theorem gue_tail {m k : ℕ} (hmk : m = k + 1) {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    {t : ℝ≥0} (ht : 0 < t) {w : Fin m → ℂ} (hw : l2Norm w = 1) {μ : ℝ}
    (hKw : K *ᵥ w = (μ : ℂ) • w) {V : Matrix (Fin m) (Fin k) ℂ} (hV : Vᴴ * V = 1)
    (hVw : Vᴴ *ᵥ w = 0) (n α : ℕ) (A : ℝ) :
    (∫⁻ G, tailW V n α A (K + G) ∂gueMeasure (Fin m) t) ≤
      ENNReal.ofReal (2 * A + (t : ℝ)⁻¹) *
        ((∫⁻ G, ENNReal.ofReal (secW n (α - 1) (K + G)) ∂gueMeasure (Fin m) t) +
          (∫⁻ G, ENNReal.ofReal (secW n α (K + G)) ∂gueMeasure (Fin m) t) +
          (∫⁻ G, ENNReal.ofReal (secW n (α + 1) (K + G)) ∂gueMeasure (Fin m) t)) := by
  subst hmk
  set F := frameCompletion w V
  have hF : Fᴴ * F = 1 := frameCompletion_unitary hw hV hVw
  have hF' : (Fᴴ)ᴴ * Fᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp hF
  set K' := Fᴴ * K * F
  have hK' : K'.IsHermitian := isHermitian_conjTranspose_mul_mul F hK
  obtain ⟨h00, h0j, hj0⟩ := frameCompletion_block hK hw hKw (V := V) hVw
  have hconj : ∀ G, K + (Fᴴ)ᴴ * G * Fᴴ = F * (K' + G) * Fᴴ := by
    intro G
    rw [conjTranspose_conjTranspose]
    simp only [K', Matrix.mul_add, Matrix.add_mul]
    congr 1
    have hFF : F * Fᴴ = 1 := mul_eq_one_comm.mp hF
    rw [show F * (Fᴴ * K * F) * Fᴴ = (F * Fᴴ) * K * (F * Fᴴ) by simp only [Matrix.mul_assoc],
      hFF, Matrix.one_mul, Matrix.mul_one]
  have hmS : ∀ ℓ, Measurable fun G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ =>
      ENNReal.ofReal (secW n ℓ (K + G)) := fun ℓ =>
    ENNReal.measurable_ofReal.comp ((measurable_secW n ℓ).comp (measurable_const_add K))
  have hmL : Measurable fun G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ => tailW V n α A (K + G) :=
    (measurable_tailW V n α A).comp (measurable_const_add K)
  have hsec : ∀ ℓ, (∫⁻ G, ENNReal.ofReal (secW n ℓ (K + G)) ∂gueMeasure (Fin (k + 1)) t) =
      ∫⁻ y, ENNReal.ofReal (secW n ℓ (K' + hermOfCoord y)) ∂hermGaussian (k + 1) t := by
    intro ℓ
    rw [← map_hermOfCoord_hermGaussian, lintegral_map (hmS ℓ) continuous_hermOfCoord.measurable,
      ← lintegral_hermGaussian_unitary t hF' _ (hmS ℓ)]
    refine lintegral_congr fun y => ?_
    rw [hconj]
    have e : F * (K' + hermOfCoord y) * Fᴴ = (Fᴴ)ᴴ * (K' + hermOfCoord y) * Fᴴ := by
      rw [conjTranspose_conjTranspose]
    rw [e, secW_unitary_conj (hK'.add (isHermitian_hermOfCoord y)) hF']
  have htail : (∫⁻ G, tailW V n α A (K + G) ∂gueMeasure (Fin (k + 1)) t) =
      ∫⁻ y, tailInt n α A (K' + hermOfCoord y) ∂hermGaussian (k + 1) t := by
    rw [← map_hermOfCoord_hermGaussian, lintegral_map hmL continuous_hermOfCoord.measurable,
      ← lintegral_hermGaussian_unitary t hF' _ hmL]
    refine lintegral_congr fun y => ?_
    rw [hconj, tailW_conj hF n α A (hK'.add (isHermitian_hermOfCoord y))]
  rw [htail, hsec, hsec, hsec]
  exact coord_restore hK' ht μ h00 h0j hj0 n α A

end BlockBand.DeterminantScore.MinorTail
