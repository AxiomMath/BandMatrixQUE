module

public import BlockBand.Window.Count.RefinedCountSplit
public import BlockBand.Window.Count.SchurInertia
public import BlockBand.Model.Construction.GaussianActiveCoordinates

/-!
# The fresh-block split of the physical ring, clause by clause

* (i)  `RingSchurInertia`: a.s. `N_H(E) = N_{H_R}(E) + N_-(A_k - E - Σ_k)`, the Schur-inertia
  step of the rank-location argument, proved as `ringSchurInertia` from the deterministic
  Haynsworth additivity (`physicalCount_eq_offBlock_add_schur`) and the a.s. invertibility
  of `H_R - E` (`ae_isUnit_det_offBlock_sub`, a nonzero-polynomial null set of the active
  Gaussian coordinates);
* (ii) `RingBlockTransport`: reindexing along `BlockSite p k ≃ Fin W` preserves `Θ_z`,
  the trace and `N_-`, proved as `ringBlockTransport`;
* (iii) `FreshBlockLawSplit`: `law(Σ̃, Ã) = law(Σ̃) ⊗ GUE_W(c/W)` for the concrete
  `Σ̃ = ringSchurSg`, `Ã = ringFreshBlock`, stated here and proved as `freshBlockLawSplit`.

Law: the physical law `model.law` (raw `H`, row variance one); every
admissible `p`, block `k`, real `E`. Conventions: `N_-` is `CoareaPalm.negativeCount`
(`0` off the Hermitian set), `Θ_z` is `Layers.phaseCount`, `Σ_k = oneBlockComplement p k H E`
uses the nonsingular inverse (`0` on singular `H_R - E`).

The everywhere form `RingFreshBlockSplit` cannot hold: its transport clauses fail at
non-Hermitian `H`. They are required for *every* `H`, including non-Hermitian ones, together with `Σ̃(H)` Hermitian for
every `H`; for a non-Hermitian `H` with `Σ_k(H) = (z₀ + i)·1` the trace clause would force
`Im W⁻¹Tr(z₀ - Σ̃)⁻¹ = 1 > 0`, impossible for Hermitian `Σ̃` and `Im z₀ > 0`. The almost-sure form
`RingFreshBlockSplitAE` (transport clauses almost surely, the other clauses unchanged) follows
from (iii) by `ringFreshBlockSplitAE_of_lawSplit`, and holds as `ringFreshBlockSplitAE`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open Matrix MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal

variable (p : BlockBand.Parameters) (k : ZMod p.n)

/-!
## Block pieces of a site matrix
-/

/-- `H_R`: the ring with block `k` deleted (the `let HR` of `oneBlockComplement`). -/
def offBlockMatrix (H : p.SiteMatrix) : Matrix (OffBlockSite p k) (OffBlockSite p k) ℂ :=
  fun x y => H x.1 y.1

/-- `C = H_{R,k}` (the `let C` of `oneBlockComplement`). -/
def offOnCoupling (H : p.SiteMatrix) : Matrix (OffBlockSite p k) (BlockSite p k) ℂ :=
  fun x y => H x.1 y.1

/-- `A_k = H_{kk}`: the diagonal block `k`. -/
def onBlockMatrix (H : p.SiteMatrix) : Matrix (BlockSite p k) (BlockSite p k) ℂ :=
  fun x y => H x.1 y.1

theorem oneBlockComplement_eq (H : p.SiteMatrix) (E : ℝ) :
    oneBlockComplement p k H E =
      (offOnCoupling p k H)ᴴ * (offBlockMatrix p k H - (E : ℂ) • 1)⁻¹ * offOnCoupling p k H :=
  rfl

theorem ringCompensatedPhase_sub (H : p.SiteMatrix) (E : ℝ) :
    ringCompensatedPhase p k H E - phaseCount (commonZ p.b E) (oneBlockComplement p k H E) =
      (negativeCount (offBlockMatrix p k H - (E : ℂ) • 1) : ℝ) := by
  unfold ringCompensatedPhase
  rw [add_sub_cancel_right]; rfl

/-- `Site ≃ BlockSite ⊕ OffBlockSite`. -/
def blockSplitEquiv : BlockSite p k ⊕ OffBlockSite p k ≃ p.Site :=
  Equiv.sumCompl (fun x : p.Site => x.1 = k)

/-- `H - E` in the block coordinates `(k, R)`, for Hermitian `H`. -/
theorem submatrix_blockSplitEquiv {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) :
    (H - (E : ℂ) • 1).submatrix (blockSplitEquiv p k) (blockSplitEquiv p k) =
      fromBlocks (onBlockMatrix p k H - (E : ℂ) • 1) (offOnCoupling p k H)ᴴ
        (offOnCoupling p k H) (offBlockMatrix p k H - (E : ℂ) • 1) := by
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · simp [blockSplitEquiv, onBlockMatrix, Matrix.one_apply, Subtype.ext_iff]
  · have hab : a.1 ≠ b.1 := fun h => b.2 (h ▸ a.2)
    have h := congrFun (congrFun hH a.1) b.1
    simp only [conjTranspose_apply] at h
    simp [blockSplitEquiv, offOnCoupling, Matrix.one_apply_ne hab, ← h]
  · have hab : a.1 ≠ b.1 := fun h => a.2 (h ▸ b.2)
    simp [blockSplitEquiv, offOnCoupling, Matrix.one_apply_ne hab]
  · simp [blockSplitEquiv, offBlockMatrix, Matrix.one_apply, Subtype.ext_iff]

theorem isHermitian_offBlockMatrix {H : p.SiteMatrix} (hH : H.IsHermitian) :
    (offBlockMatrix p k H).IsHermitian :=
  hH.submatrix (Subtype.val : OffBlockSite p k → p.Site)

theorem isHermitian_onBlockMatrix {H : p.SiteMatrix} (hH : H.IsHermitian) :
    (onBlockMatrix p k H).IsHermitian :=
  hH.submatrix (Subtype.val : BlockSite p k → p.Site)

theorem isHermitian_sub_smul_one {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (E : ℝ) : (M - (E : ℂ) • 1).IsHermitian := by
  refine hM.sub ?_
  rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

theorem isHermitian_oneBlockComplement {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) :
    (oneBlockComplement p k H E).IsHermitian := by
  rw [oneBlockComplement_eq]
  exact isHermitian_conjTranspose_mul_mul _
    (isHermitian_sub_smul_one (isHermitian_offBlockMatrix p k hH) E).inv

/-- Deterministic Schur inertia: for Hermitian `H` with `H_R - E` invertible,
`N_-(H - E) = N_-(H_R - E) + N_-(A_k - E - Σ_k)`. -/
theorem physicalCount_eq_offBlock_add_schur {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ)
    (hdet : IsUnit (offBlockMatrix p k H - (E : ℂ) • 1).det) :
    physicalCount p H E = negativeCount (offBlockMatrix p k H - (E : ℂ) • 1) +
      negativeCount (onBlockMatrix p k H - (E : ℂ) • 1 - oneBlockComplement p k H E) := by
  have hHE : (H - (E : ℂ) • 1).IsHermitian := isHermitian_sub_smul_one hH E
  unfold physicalCount
  rw [← negativeCount_submatrix_equiv hHE (blockSplitEquiv p k),
    submatrix_blockSplitEquiv p k hH E,
    negativeCount_fromBlocks_schur _ (isHermitian_sub_smul_one (isHermitian_onBlockMatrix p k hH) E)
      (isHermitian_sub_smul_one (isHermitian_offBlockMatrix p k hH) E) hdet,
    add_comm, oneBlockComplement_eq]

/-!
## Almost-sure invertibility of `H_R - E`
-/

/-- `det(H_R - E)` as a polynomial in the active Gaussian coordinates. -/
def offBlockDetPoly (E : ℝ) : MvPolynomial p.GaussianActiveCoordinate ℂ :=
  (Matrix.of fun x y : OffBlockSite p k =>
    p.gaussianUniversalMatrix x.1 y.1 - if x = y then MvPolynomial.C (E : ℂ) else 0).det

theorem eval_offBlockDetPoly (E : ℝ) (z : p.GaussianActiveCoordinate → ℝ) :
    MvPolynomial.eval (fun i => (z i : ℂ)) (offBlockDetPoly p k E) =
      (offBlockMatrix p k (p.gaussianActiveReconstruction z) - (E : ℂ) • 1).det := by
  rw [offBlockDetPoly, RingHom.map_det]
  congr 1
  ext x y
  have hU := congrFun (congrFun (p.gaussianUniversalMatrix_map_eval z) x.1) y.1
  simp only [Matrix.map_apply] at hU
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sub, hU,
    offBlockMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

/-- The witness `H₀ = (E + 1)·1` of the active coordinates. -/
def offBlockWitness (E : ℝ) : p.GaussianActiveCoordinate → ℝ :=
  fun i => Sum.elim (fun _ => E + 1) (fun _ => 0) i.1

theorem offBlockMatrix_witness (E : ℝ) :
    offBlockMatrix p k (p.gaussianActiveReconstruction (offBlockWitness p E)) - (E : ℂ) • 1 =
      1 := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp [offBlockMatrix, BlockBand.Parameters.gaussianActiveReconstruction,
      BlockBand.Parameters.gaussianReconstruction, BlockBand.Parameters.gaussianActiveValue,
      offBlockWitness, p.gaussianCoordinateVariance_diagonal_ne_zero]
  · have hxy' : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    simp [offBlockMatrix, BlockBand.Parameters.gaussianActiveReconstruction,
      BlockBand.Parameters.gaussianReconstruction, BlockBand.Parameters.gaussianActiveValue,
      offBlockWitness, hxy', Matrix.one_apply_ne hxy]

/-- Almost-sure invertibility of `H_R - E` under the physical law, for every `p`, `k`, real `E`. -/
theorem ae_isUnit_det_offBlock_sub (model : p.GaussianRingModel) (E : ℝ) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      IsUnit (offBlockMatrix p k H - (E : ℂ) • 1).det := by
  have h₀ : MvPolynomial.eval (fun i => (offBlockWitness p E i : ℂ)) (offBlockDetPoly p k E) ≠
      0 := by
    rw [eval_offBlockDetPoly, offBlockMatrix_witness, det_one]; exact one_ne_zero
  filter_upwards [model.ae_activePolynomial_ne_zero _ _ h₀,
    model.ae_gaussianActiveReconstruction_eq] with H hpoly hrec
  rw [eval_offBlockDetPoly, hrec] at hpoly
  exact isUnit_iff_ne_zero.mpr hpoly

/-!
## Clause (i): Schur inertia almost surely
-/

/-- Clause (i), Schur inertia: a.s. `N_H(E) = N_{H_R}(E) + N_-(A_k - E - Σ_k)`. -/
def RingSchurInertia : Prop :=
  ∀ (p : BlockBand.Parameters) (model : p.GaussianRingModel) (k : ZMod p.n) (E : ℝ),
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      physicalCount p H E = negativeCount (offBlockMatrix p k H - (E : ℂ) • 1) +
        negativeCount (onBlockMatrix p k H - (E : ℂ) • 1 - oneBlockComplement p k H E)

theorem ringSchurInertia : RingSchurInertia := by
  intro p model k E
  filter_upwards [ae_isUnit_det_offBlock_sub p k model E, model.isPhysical.1] with H hdet hH
  exact physicalCount_eq_offBlock_add_schur p k hH E hdet

/-!
## Clause (ii): transport to `Fin W`
-/

/-- `BlockSite p k ≃ Fin W`, `x ↦ x.2`. -/
def blockFinEquiv : BlockSite p k ≃ Fin p.W where
  toFun x := x.1.2
  invFun j := ⟨(k, j), rfl⟩
  left_inv x := by
    rcases x with ⟨⟨a, j⟩, h⟩
    simp only at h
    subst h
    rfl
  right_inv _ := rfl

theorem trace_reindex_self {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (M : Matrix ι ι ℂ) : (Matrix.reindex e e M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.diag_apply, Matrix.submatrix_apply]
  exact e.symm.sum_comp (fun i => M i i)

theorem phaseCount_reindex {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (z : ℂ) (M : Matrix ι ι ℂ) :
    phaseCount z (Matrix.reindex e e M) = phaseCount z M := by
  simp only [phaseCount, BlockBand.Internal.Contracts.Inputs.spectralSum, charpoly_reindex]

theorem reindex_sub_smul_one_sub {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (A S : Matrix ι ι ℂ) (c : ℂ) :
    Matrix.reindex e e (A - c • 1 - S) = Matrix.reindex e e A - c • 1 - Matrix.reindex e e S := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.one_apply]

theorem reindex_smul_one_sub {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (S : Matrix ι ι ℂ) (c : ℂ) :
    Matrix.reindex e e (c • 1 - S) = c • 1 - Matrix.reindex e e S := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.one_apply]

/-- Clause (ii), transport: reindexing along `blockFinEquiv` preserves `Θ_z`, the trace, and
`N_-` (on Hermitian matrices). -/
def RingBlockTransport : Prop :=
  ∀ (p : BlockBand.Parameters) (k : ZMod p.n) (M : Matrix (BlockSite p k) (BlockSite p k) ℂ)
    (z : ℂ),
    phaseCount z (Matrix.reindex (blockFinEquiv p k) (blockFinEquiv p k) M) = phaseCount z M ∧
    (Matrix.reindex (blockFinEquiv p k) (blockFinEquiv p k) M).trace = M.trace ∧
    (M.IsHermitian →
      negativeCount (Matrix.reindex (blockFinEquiv p k) (blockFinEquiv p k) M) = negativeCount M)

theorem ringBlockTransport : RingBlockTransport := fun _ _ M z =>
  ⟨phaseCount_reindex _ z M, trace_reindex_self _ M, fun hM => negativeCount_reindex hM _⟩

/-!
## The concrete `Σ̃`, `Ã` and clause (iii)
-/

/-- Hermitian part `(M + Mᴴ)/2` (equal to `M` on Hermitian `M`). -/
def hermPart {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) : Matrix ι ι ℂ := (1 / 2 : ℂ) • (M + Mᴴ)

theorem isHermitian_hermPart {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) :
    (hermPart M).IsHermitian := by
  unfold hermPart IsHermitian
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

theorem hermPart_of_isHermitian {ι : Type} [Fintype ι] {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    hermPart M = M := by
  unfold hermPart
  rw [hM.eq, ← two_smul ℂ M, smul_smul]
  norm_num

/-- `Σ̃(H)`: the one-block complement `Σ_k(H)` (Hermitian part) in `Fin W` coordinates. -/
def ringSchurSg (E : ℝ) (H : p.SiteMatrix) : Matrix (Fin p.W) (Fin p.W) ℂ :=
  Matrix.reindex (blockFinEquiv p k) (blockFinEquiv p k) (hermPart (oneBlockComplement p k H E))

/-- `Ã(H)`: the fresh diagonal block `A_k = H_{kk}` in `Fin W` coordinates. -/
def ringFreshBlock (H : p.SiteMatrix) : Matrix (Fin p.W) (Fin p.W) ℂ :=
  Matrix.reindex (blockFinEquiv p k) (blockFinEquiv p k) (onBlockMatrix p k H)

theorem isHermitian_ringSchurSg (E : ℝ) (H : p.SiteMatrix) : (ringSchurSg p k E H).IsHermitian :=
  (isHermitian_hermPart _).submatrix _

theorem ringSchurSg_of_isHermitian (E : ℝ) {H : p.SiteMatrix} (hH : H.IsHermitian) :
    ringSchurSg p k E H =
      Matrix.reindex (blockFinEquiv p k) (blockFinEquiv p k) (oneBlockComplement p k H E) := by
  rw [ringSchurSg, hermPart_of_isHermitian (isHermitian_oneBlockComplement p k hH E)]

/-- Clause (iii), fresh-block law split: under the physical law, `(Σ̃, Ã)` has law
`law(Σ̃) ⊗ GUE_W(c/W)` (`Ã` is the independent diagonal block, `E|A_xy|² = c/W`). -/
def FreshBlockLawSplit : Prop :=
  ∀ (p : BlockBand.Parameters) (model : p.GaussianRingModel) (k : ZMod p.n) (E : ℝ),
    (model.law : Measure p.SiteMatrix).map (fun H => (ringSchurSg p k E H, ringFreshBlock p k H)) =
      ((model.law : Measure p.SiteMatrix).map (ringSchurSg p k E)).prod
        (gueMeasure (Fin p.W) (Real.toNNReal (p.c / p.W)))

/-!
## Measurability of `Σ̃`, `Ã`
-/

theorem measurable_matrix_iff {X ι κ : Type*} [MeasurableSpace X] {f : X → Matrix ι κ ℂ} :
    Measurable f ↔ ∀ i j, Measurable fun x => f x i j := by
  constructor
  · intro hf i j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hf)
  · intro h
    exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => h i j

theorem measurable_matrix_mul {X ι κ ν : Type*} [MeasurableSpace X] [Fintype κ]
    {f : X → Matrix ι κ ℂ} {g : X → Matrix κ ν ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x * g x := by
  rw [measurable_matrix_iff] at hf hg ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun l _ => (hf i l).mul (hg l j)

theorem measurable_matrix_inv {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [Fintype ι] [DecidableEq ι] {f : X → Matrix ι ι ℂ}
    (hf : Continuous f) : Measurable fun x => (f x)⁻¹ := by
  rw [measurable_matrix_iff]
  intro i j
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  have had : Continuous fun x => (f x).adjugate i j :=
    (continuous_apply_apply i j).comp hf.matrix_adjugate
  exact hf.matrix_det.measurable.inv.mul had.measurable

theorem continuous_offBlockMatrix : Continuous (offBlockMatrix p k) :=
  continuous_matrix fun x y => continuous_apply_apply x.1 y.1

theorem measurable_offOnCoupling : Measurable (offOnCoupling p k) :=
  measurable_matrix_iff.mpr fun x y => (measurable_pi_apply y.1).comp (measurable_pi_apply x.1)

theorem measurable_onBlockMatrix : Measurable (onBlockMatrix p k) :=
  measurable_matrix_iff.mpr fun x y => (measurable_pi_apply y.1).comp (measurable_pi_apply x.1)

theorem measurable_oneBlockComplement (E : ℝ) :
    Measurable fun H => oneBlockComplement p k H E := by
  simp only [oneBlockComplement_eq]
  refine measurable_matrix_mul (measurable_matrix_mul ?_ ?_) (measurable_offOnCoupling p k)
  · rw [measurable_matrix_iff]
    intro i j
    simp only [conjTranspose_apply]
    exact continuous_star.measurable.comp (measurable_matrix_iff.mp (measurable_offOnCoupling p k) j i)
  · exact measurable_matrix_inv ((continuous_offBlockMatrix p k).sub continuous_const)

theorem measurable_reindex {X ι κ : Type*} [MeasurableSpace X] (e : ι ≃ κ)
    {f : X → Matrix ι ι ℂ} (hf : Measurable f) :
    Measurable fun x => Matrix.reindex e e (f x) :=
  measurable_matrix_iff.mpr fun i j => measurable_matrix_iff.mp hf (e.symm i) (e.symm j)

theorem measurable_ringSchurSg (E : ℝ) : Measurable (ringSchurSg p k E) := by
  refine measurable_reindex _ ?_
  rw [measurable_matrix_iff]
  intro i j
  have h := measurable_matrix_iff.mp (measurable_oneBlockComplement p k E)
  simp only [hermPart, Matrix.smul_apply, Matrix.add_apply, conjTranspose_apply, smul_eq_mul]
  exact measurable_const.mul ((h i j).add (continuous_star.measurable.comp (h j i)))

theorem measurable_ringFreshBlock : Measurable (ringFreshBlock p k) :=
  measurable_reindex _ (measurable_onBlockMatrix p k)

/-!
## The almost-sure split and its assembly
-/

/-- The fresh-block split, almost-sure form: `RingFreshBlockSplit` except that the two
transport clauses (phase and normalized trace) are required `model.law`-a.s. instead of for
every `H` (the `∀ H` form cannot hold: the transport clauses fail at non-Hermitian `H`). `refinedCount_count_of` only
uses these clauses inside `eLpNorm`s under `model.law`. -/
def RingFreshBlockSplitAE : Prop :=
  ∀ (p : BlockBand.Parameters) (model : p.GaussianRingModel) (k : ZMod p.n) (E : ℝ),
    ∃ (Sg Af : p.SiteMatrix → Matrix (Fin p.W) (Fin p.W) ℂ),
      Measurable Sg ∧ Measurable Af ∧ (∀ H, (Sg H).IsHermitian) ∧
      (∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
        (physicalCount p H E : ℝ) =
          ringCompensatedPhase p k H E -
            phaseCount (commonZ p.b E) (oneBlockComplement p k H E) +
            negativeCount (Af H - (E : ℂ) • 1 - Sg H)) ∧
      (∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
        phaseCount (commonZ p.b E) (oneBlockComplement p k H E) =
          phaseCount (commonZ p.b E) (Sg H)) ∧
      (∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
        oneBlockTrace p k ((commonZ p.b E • 1 - oneBlockComplement p k H E)⁻¹) =
          (p.W : ℂ)⁻¹ * ((commonZ p.b E • 1 - Sg H)⁻¹).trace) ∧
      (model.law : Measure p.SiteMatrix).map (fun H => (Sg H, Af H)) =
        ((model.law : Measure p.SiteMatrix).map Sg).prod
          (gueMeasure (Fin p.W) (Real.toNNReal (p.c / p.W)))

/-- Assembly: (i) + (ii) + (iii) give the almost-sure fresh-block split, with the concrete
`Σ̃ = ringSchurSg`, `Ã = ringFreshBlock`. -/
theorem ringFreshBlockSplitAE_of (hi : RingSchurInertia) (hii : RingBlockTransport)
    (hiii : FreshBlockLawSplit) : RingFreshBlockSplitAE := by
  intro p model k E
  refine ⟨ringSchurSg p k E, ringFreshBlock p k, measurable_ringSchurSg p k E,
    measurable_ringFreshBlock p k, isHermitian_ringSchurSg p k E, ?_, ?_, ?_, hiii p model k E⟩
  · filter_upwards [hi p model k E, model.isPhysical.1] with H h hH
    have hS : (onBlockMatrix p k H - (E : ℂ) • 1 - oneBlockComplement p k H E).IsHermitian :=
      (isHermitian_sub_smul_one (isHermitian_onBlockMatrix p k hH) E).sub
        (isHermitian_oneBlockComplement p k hH E)
    rw [h, ringSchurSg_of_isHermitian p k E hH, ringFreshBlock, ← reindex_sub_smul_one_sub,
      (hii p k _ 0).2.2 hS, ringCompensatedPhase_sub]
    push_cast; ring
  · filter_upwards [model.isPhysical.1] with H hH
    rw [ringSchurSg_of_isHermitian p k E hH, (hii p k _ _).1]
  · filter_upwards [model.isPhysical.1] with H hH
    rw [ringSchurSg_of_isHermitian p k E hH, ← reindex_smul_one_sub, inv_reindex,
      (hii p k _ 0).2.1, oneBlockTrace]

/-- With (i) and (ii) proved, the almost-sure split reduces to the law clause (iii). -/
theorem ringFreshBlockSplitAE_of_lawSplit (hiii : FreshBlockLawSplit) : RingFreshBlockSplitAE :=
  ringFreshBlockSplitAE_of ringSchurInertia ringBlockTransport hiii

end BlockBand.Window.Count
