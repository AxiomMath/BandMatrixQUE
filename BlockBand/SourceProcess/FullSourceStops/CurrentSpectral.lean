module

public import BlockBand.SourceProcess.FullSourceStops.CurrentCarrier
public import BlockBand.Transmission.Bridge.Scattering

/-!
# The spectral identity `Tr|J| = 2 Tr T^{1/2}`

For a unitary two-port `𝕊` (`𝕊ᴴ𝕊 = 𝕊𝕊ᴴ = 1`), `P = nearProjection`, `J = 𝕊ᴴP𝕊 - P`:
* `nuclearNorm_eq_fracTrace_mul_self`: `Tr|J| = Tr (J²)^{1/2}` for Hermitian `J`;
* `current_sq_blocks`: `J² = diag(1 - aᴴa, bᴴb)` with `a = 𝕊₀₀`, `b = 𝕊₀₁`;
* `charpoly_one_sub_congr`: equal characteristic polynomials stay equal under `M ↦ 1 - M`, so
  `bᴴb ∼ bbᴴ = 1 - aaᴴ ∼ 1 - aᴴa`;
* `nuclearNorm_current_eq`: `Tr|J| = 2 fracTrace (1/2) (1 - aᴴa)`;
* `nuclearNorm_twoPortCurrent_eq`: at a Hermitian two-port `𝕏` and `Im z > 0`,
  `Tr|J| = 2 fracTrace (1/2) T(X)`, `X = nearSchur z 𝕏`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open Matrix Polynomial
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open scoped ComplexOrder

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem fracTrace_congr {m : Type*} [Fintype m] [DecidableEq m] {p : ℝ} {A : Matrix n n ℂ}
    {B : Matrix m m ℂ} (h : A.charpoly = B.charpoly) :
    fracTrace p A = fracTrace p B := by
  rw [fracTrace, fracTrace, h]

/-- `charpoly M ∘ (1 - X) = (-1)^n charpoly (1 - M)`. -/
theorem charpoly_comp_one_sub (M : Matrix n n ℂ) :
    M.charpoly.comp (1 - X) = (-1) ^ Fintype.card n * (1 - M).charpoly := by
  have h := (Polynomial.compRingHom (1 - X : ℂ[X])).map_det (charmatrix M)
  have e : (Polynomial.compRingHom (1 - X : ℂ[X])).mapMatrix (charmatrix M) =
      -charmatrix (1 - M) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [charmatrix_apply_eq, Matrix.one_apply_eq]
      ring
    · simp [charmatrix_apply_ne _ _ _ hij, Matrix.one_apply_ne hij]
  rw [Polynomial.coe_compRingHom_apply, e, Matrix.det_neg] at h
  rw [Matrix.charpoly, h, Matrix.charpoly]

theorem charpoly_one_sub_congr {M M' : Matrix n n ℂ} (h : M.charpoly = M'.charpoly) :
    (1 - M).charpoly = (1 - M').charpoly := by
  have h1 := charpoly_comp_one_sub M
  have h2 := charpoly_comp_one_sub M'
  rw [h, h2] at h1
  have hu : ((-1 : ℂ[X]) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  exact (mul_left_cancel₀ hu h1).symm

theorem charpoly_one_sub_mul_comm (a : Matrix n n ℂ) :
    (1 - a * aᴴ).charpoly = (1 - aᴴ * a).charpoly :=
  charpoly_one_sub_congr (Matrix.charpoly_mul_comm a aᴴ)

theorem fracTrace_fromBlocks {m : Type*} [Fintype m] [DecidableEq m] (p : ℝ)
    (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    fracTrace p (Matrix.fromBlocks A 0 0 B) = fracTrace p A + fracTrace p B := by
  rw [fracTrace, Matrix.charpoly_fromBlocks_zero₁₂, Polynomial.roots_mul
    ((Matrix.charpoly_monic A).mul (Matrix.charpoly_monic B)).ne_zero, Multiset.map_add,
    Multiset.sum_add, fracTrace, fracTrace]

theorem fracTrace_submatrix_equiv {m : Type*} [Fintype m] [DecidableEq m] (p : ℝ) (e : m ≃ n)
    (M : Matrix n n ℂ) : fracTrace p (M.submatrix e e) = fracTrace p M := by
  have := Matrix.charpoly_reindex e.symm M
  rw [Matrix.reindex_apply, Equiv.symm_symm] at this
  exact fracTrace_congr this

/-- `Tr|J| = Tr(J²)^{1/2}` for Hermitian `J`. -/
theorem nuclearNorm_eq_fracTrace_mul_self {J : Matrix n n ℂ} (hJ : J.IsHermitian) :
    nuclearNorm J = fracTrace (1 / 2) (J * J) := by
  set U : Matrix n n ℂ := (hJ.eigenvectorUnitary : Matrix n n ℂ)
  set D : Matrix n n ℂ := diagonal (fun i => ((hJ.eigenvalues i : ℝ) : ℂ))
  have hJ' : J = U * D * Uᴴ := conj_eigen hJ
  have hsq : J * J = U * (D * D * Uᴴ) := by
    rw [hJ']
    have : Uᴴ * U = 1 := unitary_star_mul hJ.eigenvectorUnitary
    calc U * D * Uᴴ * (U * D * Uᴴ) = U * D * (Uᴴ * U) * D * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * (D * D * Uᴴ) := by rw [this, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hcp : (J * J).charpoly = ∏ i, (X - C (((hJ.eigenvalues i ^ 2 : ℝ)) : ℂ)) := by
    rw [hsq, Matrix.charpoly_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc,
      unitary_star_mul hJ.eigenvectorUnitary, Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      Matrix.charpoly_diagonal]
    refine Finset.prod_congr rfl fun i _ => ?_
    push_cast; rw [sq]
  have hroots : (J * J).charpoly.roots =
      Finset.univ.val.map fun i => (((hJ.eigenvalues i ^ 2 : ℝ)) : ℂ) := by
    have e : Finset.univ.val.map (fun i => X - C (((hJ.eigenvalues i ^ 2 : ℝ)) : ℂ)) =
        (Finset.univ.val.map fun i => (((hJ.eigenvalues i ^ 2 : ℝ)) : ℂ)).map
          (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [hcp, Finset.prod_eq_multiset_prod, e, Polynomial.roots_multiset_prod_X_sub_C]
  rw [nuclearNorm_eq_sum_abs hJ, fracTrace, hroots, Multiset.map_map]
  simp only [Function.comp_apply, Complex.ofReal_re, Finset.sum_map_val]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [max_eq_left (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]

end General

section Current

variable {W : ℕ}

theorem portBlock_mul (M N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    portBlock (M * N) i j = portBlock M i 0 * portBlock N 0 j + portBlock M i 1 * portBlock N 1 j := by
  ext x y
  simp [portBlock, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem portBlock_conjTranspose (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    portBlock Mᴴ i j = (portBlock M j i)ᴴ := by
  ext x y; simp [portBlock, Matrix.conjTranspose_apply]

theorem portBlock_one (i j : Fin 2) :
    portBlock (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) i j = if i = j then 1 else 0 := by
  ext x y
  by_cases h : i = j
  · subst h; simp [portBlock, Matrix.one_apply]
  · simp [portBlock, h]

theorem portBlock_sandwich_far (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    portBlock (Mᴴ * nearProjection W * M) 1 1 = (portBlock M 0 1)ᴴ * portBlock M 0 1 := by
  ext x y
  simp [portBlock, Matrix.mul_apply, nearProjection, Matrix.diagonal_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.conjTranspose_apply]

/-- **`J² = diag(1 - aᴴa, bᴴb)`** for a co-isometric `𝕊` (`𝕊𝕊ᴴ = 1`). -/
theorem current_sq_blocks (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hS : S * Sᴴ = 1) :
    ((Sᴴ * nearProjection W * S - nearProjection W) *
        (Sᴴ * nearProjection W * S - nearProjection W)).submatrix (portEquiv W) (portEquiv W) =
      Matrix.fromBlocks (1 - (portBlock S 0 0)ᴴ * portBlock S 0 0) 0 0
        ((portBlock S 0 1)ᴴ * portBlock S 0 1) := by
  have h00 := portBlock_sandwich_nearProjection (W := W) S
  have h11 := portBlock_sandwich_far (W := W) S
  set P := nearProjection W
  set Q := Sᴴ * P * S
  have hQ : Q * Q = Q := by
    calc Q * Q = Sᴴ * P * (S * Sᴴ) * P * S := by simp only [Q, Matrix.mul_assoc]
      _ = Q := by rw [hS, Matrix.mul_one, Matrix.mul_assoc Sᴴ P P, nearProjection_mul_self]
  have hsq : (Q - P) * (Q - P) = Q - Q * P - P * Q + P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hQ, nearProjection_mul_self]; abel
  rw [hsq, submatrix_portEquiv]
  have hP : ∀ (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) (x y : Fin W),
      portBlock (M - M * P - P * M + P) i j x y =
        M (i, x) (j, y) - M (i, x) (j, y) * (if j = 0 then 1 else 0) -
          (if i = 0 then 1 else 0) * M (i, x) (j, y) +
            (if i = 0 then (1 : Matrix (Fin W) (Fin W) ℂ) x y else 0) * (if i = j then 1 else 0) := by
    intro M i j x y
    simp only [portBlock, Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply, P, nearProjection,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply, Prod.mk.injEq,
      Matrix.one_apply]
    by_cases hi : i = j <;> by_cases hx : x = y <;> fin_cases i <;> fin_cases j <;> simp_all
  congr 1
  · ext x y
    have := congrFun (congrFun h00 x) y
    rw [hP]; simp only [portBlock, Matrix.of_apply] at this
    simp [Matrix.sub_apply, ← this, portBlock]; ring
  · ext x y; rw [hP]; simp
  · ext x y; rw [hP]; simp
  · ext x y
    have := congrFun (congrFun h11 x) y
    rw [hP]; simp only [portBlock, Matrix.of_apply] at this
    simp [← this, portBlock]

theorem nearProjection_isHermitian' : (nearProjection W).IsHermitian := by
  simp only [nearProjection]
  exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by
    ext x; simp only [Pi.star_apply]; split_ifs <;> simp)

/-- `J = 𝕊ᴴP𝕊 - P` is Hermitian for every `𝕊`. -/
theorem twoPortCurrent_isHermitian (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (Sᴴ * nearProjection W * S - nearProjection W).IsHermitian :=
  (Matrix.isHermitian_conjTranspose_mul_mul S nearProjection_isHermitian').sub
    nearProjection_isHermitian'

/-- **`Tr|J| = 2 Tr(1 - aᴴa)^{1/2}`** for a co-isometric two-port `𝕊` (`𝕊𝕊ᴴ = 1`). -/
theorem nuclearNorm_current_eq (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hS2 : S * Sᴴ = 1) :
    nuclearNorm (Sᴴ * nearProjection W * S - nearProjection W) =
      2 * fracTrace (1 / 2) (1 - (portBlock S 0 0)ᴴ * portBlock S 0 0) := by
  rw [nuclearNorm_eq_fracTrace_mul_self (twoPortCurrent_isHermitian S), ← fracTrace_submatrix_equiv _ (portEquiv W),
    current_sq_blocks S hS2, fracTrace_fromBlocks]
  have hb : ((portBlock S 0 1)ᴴ * portBlock S 0 1).charpoly =
      (1 - (portBlock S 0 0)ᴴ * portBlock S 0 0).charpoly := by
    rw [Matrix.charpoly_mul_comm, ← charpoly_one_sub_mul_comm]
    congr 1
    have h := congrArg (fun M => portBlock M 0 0) hS2
    simp only [portBlock_mul, portBlock_conjTranspose, portBlock_one, ite_true] at h
    rw [← h]; abel
  rw [fracTrace_congr hb]; ring

/-- **`Tr|J| = 2 Tr T^{1/2}`** at a Hermitian two-port `𝕏` (`Im z > 0`), `T = T(nearSchur z 𝕏)`. -/
theorem nuclearNorm_twoPortCurrent_eq (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hX : XX.IsHermitian) (hη : 0 < (boundaryZ b E).im) :
    nuclearNorm ((twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX -
        nearProjection W) =
      2 * fracTrace (1 / 2) (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) := by
  obtain ⟨-, h2⟩ := twoPortScattering_unitary b E XX hX hη
  have hD : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1) :=
    BlockBand.Transmission.portPencil_isUnit _ (by
      ext x y; simpa [portBlock, Matrix.conjTranspose_apply] using
        congrFun (congrFun hX (1, x)) (1, y)) hη
  have hS00 : portBlock (twoPortScattering b E XX) 0 0 =
      passiveS b E (nearSchur (boundaryZ b E) XX) := by
    rw [passiveS, ← portBlock_twoPortResolvent_zero_zero b E XX hD]
    ext x y; simp [twoPortScattering, portBlock, Matrix.one_apply]; left; ring
  rw [nuclearNorm_current_eq _ h2, hS00, passiveTransmission_eq_one_sub]

end Current

end BlockBand.SourceProcess.FullSourceStops
