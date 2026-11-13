module

public import BlockBand.Transmission.LawFinite.GinibreTail
public import BlockBand.Transmission.LawFinite.Interface
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Column Gram–Schmidt: `det(BᴴB) = ∏‖gs_j‖²` and the frame/Bessel bound

Columns `c : Fin W → (Fin W → ℂ)`, matrix `colsMat c = (c j x)_{x,j}`, Gram–Schmidt
`gsC c j = gramSchmidt ℂ (toLp ∘ c) j`.
* `det_gram_eq`: `det((colsMat c)ᴴ colsMat c) = ∏_j ‖gsC c j‖²` (`B = GR`, `R` unipotent upper
  triangular, `GᴴG` diagonal);
* `chiSum_le_gs`: Bessel, `Σ_{l<k} |⟪u_l, c_j⟫|² ≤ ‖gsC c j‖²` when `u_l ⊥ c_m` (`l < k`, `m < j`);
* `exists_frame`: such an orthonormal basis exists with `k = W - j`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open Matrix InnerProductSpace
open scoped InnerProductSpace ComplexConjugate

variable {W : ℕ}

/-- The matrix with columns `c j`. -/
def colsMat (c : Fin W → Fin W → ℂ) : Matrix (Fin W) (Fin W) ℂ := Matrix.of fun x j => c j x

/-- Columns as Euclidean vectors. -/
def colsE (c : Fin W → Fin W → ℂ) : Fin W → EuclideanSpace ℂ (Fin W) :=
  fun j => WithLp.toLp 2 (c j)

/-- Column Gram–Schmidt vectors. -/
def gsC (c : Fin W → Fin W → ℂ) (j : Fin W) : EuclideanSpace ℂ (Fin W) :=
  gramSchmidt ℂ (colsE c) j

/-- `G`: the matrix of Gram–Schmidt columns. -/
def gsMat (c : Fin W → Fin W → ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x j => (gsC c j).ofLp x

/-- `R = 1 + N`: unipotent upper triangular, `c = G R`. -/
def gsCoef (c : Fin W → Fin W → ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  1 + Matrix.of fun i n => if i < n then
    ⟪gsC c i, colsE c n⟫_ℂ / ((‖gsC c i‖ : ℂ) ^ 2) else 0

theorem colsMat_eq_mul (c : Fin W → Fin W → ℂ) : colsMat c = gsMat c * gsCoef c := by
  rw [gsCoef, Matrix.mul_add, Matrix.mul_one]
  ext x n
  have h := congrArg (fun v : EuclideanSpace ℂ (Fin W) => v.ofLp x)
    (gramSchmidt_def'' ℂ (colsE c) n)
  simp only [colsE, WithLp.ofLp_toLp, WithLp.ofLp_add, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_gt_eq_Iio]
  simp only [colsMat, gsMat, gsC, colsE, Matrix.of_apply]
  rw [h]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem gsCoef_upper (c : Fin W → Fin W → ℂ) : (gsCoef c).IsUpperTriangular := by
  intro i n hni
  have h1 : ¬ i < n := not_lt.2 (le_of_lt hni)
  have h2 : i ≠ n := ne_of_gt hni
  simp [gsCoef, h1, h2]

theorem det_gsCoef (c : Fin W → Fin W → ℂ) : (gsCoef c).det = 1 := by
  rw [det_of_isUpperTriangular (gsCoef_upper c)]
  exact Finset.prod_eq_one fun i _ => by simp [gsCoef]

theorem gsMat_gram (c : Fin W → Fin W → ℂ) :
    (gsMat c)ᴴ * gsMat c = Matrix.diagonal fun j => ((‖gsC c j‖ : ℂ) ^ 2) := by
  ext i j
  have hinner : ((gsMat c)ᴴ * gsMat c) i j = ⟪gsC c i, gsC c j⟫_ℂ := by
    rw [Matrix.mul_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [gsMat, Matrix.conjTranspose_apply, mul_comm]
  rw [hinner, Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij; simp [inner_self_eq_norm_sq_to_K]
  · exact gramSchmidt_orthogonal ℂ (colsE c) hij

/-- **`det(BᴴB) = ∏_j ‖gs_j‖²`** for the column matrix `B = colsMat c`. -/
theorem det_gram_eq (c : Fin W → Fin W → ℂ) :
    ((colsMat c)ᴴ * colsMat c).det = ∏ j, ((‖gsC c j‖ ^ 2 : ℝ) : ℂ) := by
  rw [colsMat_eq_mul, conjTranspose_mul, show (gsCoef c)ᴴ * (gsMat c)ᴴ * (gsMat c * gsCoef c) =
    (gsCoef c)ᴴ * ((gsMat c)ᴴ * gsMat c) * gsCoef c by simp only [Matrix.mul_assoc],
    det_mul, det_mul, det_conjTranspose, det_gsCoef, gsMat_gram, det_diagonal]
  simp

/-- Columns before `j` are orthogonal to `u` ⇒ `⟪u, c_j⟫ = ⟪u, gs_j⟫`. -/
theorem inner_col_eq_inner_gs (c : Fin W → Fin W → ℂ) (j : Fin W) (u : EuclideanSpace ℂ (Fin W))
    (hu : ∀ m < j, ⟪u, colsE c m⟫_ℂ = 0) : ⟪u, colsE c j⟫_ℂ = ⟪u, gsC c j⟫_ℂ := by
  have hspan : ∀ m < j, ∀ v ∈ Submodule.span ℂ (colsE c '' Set.Iic m), ⟪u, v⟫_ℂ = 0 := by
    intro m hm v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m', hm', rfl⟩ := hx
      exact hu m' (lt_of_le_of_lt hm' hm)
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]
  have hgs : ∀ m < j, ⟪u, gsC c m⟫_ℂ = 0 := fun m hm =>
    hspan m hm _ (gramSchmidt_mem_span ℂ (colsE c) le_rfl)
  rw [gramSchmidt_def'' ℂ (colsE c) j, inner_add_right, inner_sum]
  rw [Finset.sum_eq_zero fun m hm => by
    rw [inner_smul_right, show ⟪u, gramSchmidt ℂ (colsE c) m⟫_ℂ = 0 from
      hgs m (Finset.mem_Iio.1 hm), mul_zero]]
  rw [add_zero]; rfl

/-- **Bessel**: for an orthonormal basis `u` whose first `k` vectors are orthogonal to the
columns before `j`, `Σ_{l<k} |⟪u_l, c_j⟫|² ≤ ‖gs_j‖²`. -/
theorem chiSum_le_gs (c : Fin W → Fin W → ℂ) (j : Fin W)
    (u : OrthonormalBasis (Fin W) ℂ (EuclideanSpace ℂ (Fin W))) (k : ℕ)
    (hu : ∀ l : Fin W, l.val < k → ∀ m < j, ⟪u l, colsE c m⟫_ℂ = 0) :
    chiSum k (reprMap u (c j)) ≤ ‖gsC c j‖ ^ 2 := by
  have hs : chiSum k (reprMap u (c j)) =
      ∑ l ∈ Finset.univ.filter (fun l : Fin W => l.val < k), ‖⟪u l, gsC c j⟫_ℂ‖ ^ 2 := by
    rw [chiSum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs with hl
    · rw [reprMap_apply, show WithLp.toLp 2 (c j) = colsE c j from rfl,
        inner_col_eq_inner_gs c j (u l) (hu l hl)]
    · rfl
  rw [hs]
  exact Orthonormal.sum_inner_products_le (gsC c j) u.orthonormal

/-- **A frame for column `j`**: an orthonormal basis whose first `W - j` vectors are orthogonal to
the columns before `j`. -/
theorem exists_frame (c : Fin W → Fin W → ℂ) (j : Fin W) :
    ∃ u : OrthonormalBasis (Fin W) ℂ (EuclideanSpace ℂ (Fin W)),
      ∀ l : Fin W, l.val < W - j.val → ∀ m < j, ⟪u l, colsE c m⟫_ℂ = 0 := by
  classical
  set K : Submodule ℂ (EuclideanSpace ℂ (Fin W)) :=
    Submodule.span ℂ (Set.range fun m : Fin j.val => colsE c (Fin.castLT m (by omega)))
  have hK : Module.finrank ℂ K ≤ j.val := by
    have := finrank_range_le_card (R := ℂ) fun m : Fin j.val => colsE c (Fin.castLT m (by omega))
    rw [Fintype.card_fin] at this
    exact this
  have hKo : W - j.val ≤ Module.finrank ℂ Kᗮ := by
    have h := Submodule.finrank_add_finrank_orthogonal K
    rw [finrank_euclideanSpace, Fintype.card_fin] at h
    omega
  set e := stdOrthonormalBasis ℂ Kᗮ
  set v : Fin W → EuclideanSpace ℂ (Fin W) := fun l =>
    if h : l.val < W - j.val then (e ⟨l.val, lt_of_lt_of_le h hKo⟩ : EuclideanSpace ℂ (Fin W))
    else 0
  set s : Set (Fin W) := {l | l.val < W - j.val}
  have hv : Orthonormal ℂ (s.domRestrict v) := by
    have he : Orthonormal ℂ fun l : Fin (Module.finrank ℂ Kᗮ) => (e l : EuclideanSpace ℂ (Fin W)) :=
      e.orthonormal.comp_linearIsometry Kᗮ.subtypeₗᵢ
    have hinj : Function.Injective fun l : s =>
        (⟨l.1.val, lt_of_lt_of_le l.2 hKo⟩ : Fin (Module.finrank ℂ Kᗮ)) := by
      intro a b hab
      exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val hab))
    convert he.comp _ hinj using 1
    funext l
    have hl : l.1.val < W - j.val := l.2
    simp only [Set.domRestrict, Function.comp, v, hl, ↓reduceDIte]
  obtain ⟨u, hu⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace]) hv
  refine ⟨u, fun l hl m hm => ?_⟩
  rw [hu l hl]
  simp only [v, show l.val < W - j.val from hl, ↓reduceDIte]
  have hmem : colsE c m ∈ K :=
    Submodule.subset_span ⟨⟨m.val, hm⟩, by simp [Fin.castLT]⟩
  exact Submodule.inner_left_of_mem_orthogonal hmem (e _).2

end BlockBand.Transmission.LawFinite
