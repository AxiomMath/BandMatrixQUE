module

public import BlockBand.Palm.MomentFlow.BridgeLaw
public import BlockBand.Internal.Contracts.Transmission
public import BlockBand.Counting.SpectralScaling
public import BlockBand.Model.Construction.SpectralSelection

/-!
# Relabelling between the Dyson Brownian motion conventions and the increasing labels

The Dyson Brownian motion statements use nonincreasing eigenvalue labels and the Lagrange
projector; this file translates eigenvalues, overlaps and couplings to the increasing labels of
`freshEigenvalue` and the selected eigenvector `freshEigenvector`.

* `dysonEigenvalue_rev`: `dysonEigenvalue N K ℓ.rev = freshEigenvalue K ℓ` (relabel `ℓ ↦ N-1-ℓ`).
* `dysonProjection_mulVec_eigenvectorBasis`: on simple spectrum the Lagrange product acts on the
  eigenbasis by `δ`.
* `dysonOverlap_rev`: `dysonOverlap N q K ℓ.rev = N ‖q* freshEigenvector K ℓ‖²` on simple
  spectrum (the selected eigenvector differs from the canonical one by a unit phase).
* `hasSimpleSpectrum_iff_strictMono`: `HasSimpleSpectrum` is strict increase of
  `freshEigenvalue`.
* `dysonCoupling_rev`: the coupling at reversed labels is the formula of `flowRate`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Foundations.Spectral BlockBand.Model.Construction
open scoped ComplexConjugate

variable {N : ℕ}

theorem eigenvalues₀_congr {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (h : A = B) : hA.eigenvalues₀ = hB.eigenvalues₀ := by
  subst h; rfl

/-- For Hermitian `K`, `dysonEigenvalue` is Mathlib's decreasing eigenvalue `eigenvalues₀` of `K`. -/
theorem dysonEigenvalue_eq_eigenvalues₀ {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (i : Fin N) :
    dysonEigenvalue N K i = hK.eigenvalues₀ (Fin.cast (Fintype.card_fin N).symm i) := by
  have h2 : K + Kᴴ = ((2 : ℝ) : ℂ) • K := by rw [hK.eq]; push_cast; rw [two_smul]
  have hS : (((2 : ℝ) : ℂ) • K).IsHermitian := h2 ▸ Matrix.isHermitian_add_transpose_self K
  unfold dysonEigenvalue
  rw [eigenvalues₀_congr _ hS h2,
    BlockBand.Counting.eigenvaluesOrdered_positiveScale hK 2 two_pos hS]
  ring

theorem freshEigenvalue_eq {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian) (ℓ : Fin N) :
    freshEigenvalue K ℓ = hK.eigenvalues₀ (Fin.cast (Fintype.card_fin N).symm ℓ).rev := by
  simp [freshEigenvalue, rawIncreasingEigenvalue_eq _ K hK, increasingEigenvalue]

theorem cast_rev (ℓ : Fin N) :
    Fin.cast (Fintype.card_fin N).symm ℓ.rev = (Fin.cast (Fintype.card_fin N).symm ℓ).rev := by
  ext; simp [Fin.val_rev]

/-- **Relabelling of eigenvalues**: the nonincreasing label `ℓ.rev` is the increasing rank `ℓ`. -/
theorem dysonEigenvalue_rev {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian) (ℓ : Fin N) :
    dysonEigenvalue N K ℓ.rev = freshEigenvalue K ℓ := by
  rw [dysonEigenvalue_eq_eigenvalues₀ hK, freshEigenvalue_eq hK, cast_rev]

theorem freshEigenvalue_eq_dyson {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (ℓ : Fin N) : freshEigenvalue K ℓ = dysonEigenvalue N K ℓ.rev :=
  (dysonEigenvalue_rev hK ℓ).symm

/-- `HasSimpleSpectrum` is strict monotonicity of the increasing eigenvalues. -/
theorem hasSimpleSpectrum_iff_strictMono {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian) :
    HasSimpleSpectrum N K ↔ StrictMono (freshEigenvalue K) := by
  unfold HasSimpleSpectrum
  constructor
  · intro h i j hij
    rw [freshEigenvalue_eq_dyson hK, freshEigenvalue_eq_dyson hK]
    exact h (Fin.rev_lt_rev.2 hij)
  · intro h i j hij
    rw [← Fin.rev_rev i, ← Fin.rev_rev j, dysonEigenvalue_rev hK, dysonEigenvalue_rev hK]
    exact h (Fin.rev_lt_rev.2 (by simpa using hij))

/-- Simple spectrum makes the increasing eigenvalue map injective (the hypothesis of the
measurable selection lemmas). -/
theorem injective_orderedEigenvalue {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (hs : HasSimpleSpectrum N K) :
    Function.Injective (orderedEigenvalue (⟨K, hK⟩ : HermitianMatrix (Fin N))) := by
  have hm := (hasSimpleSpectrum_iff_strictMono hK).1 hs
  intro i j hij
  have h' : freshEigenvalue K (Fin.cast (Fintype.card_fin N) i) =
      freshEigenvalue K (Fin.cast (Fintype.card_fin N) j) := by
    simp only [freshEigenvalue, rawIncreasingEigenvalue_eq _ K hK, Fin.cast_cast, Fin.cast_eq_self]
    exact hij
  have := hm.injective h'
  exact Fin.cast_injective _ this

/-!
## The Lagrange product on simple spectrum
-/

theorem list_prod_mulVec_eigen (L : List (Fin N)) (M : Fin N → Matrix (Fin N) (Fin N) ℂ)
    (c : Fin N → ℂ) (v : Fin N → ℂ) (hv : ∀ j ∈ L, M j *ᵥ v = c j • v) :
    (L.map M).prod *ᵥ v = (L.map c).prod • v := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← Matrix.mulVec_mulVec, ih (fun j hj => hv j (List.mem_cons_of_mem a hj)),
      Matrix.mulVec_smul, hv a (List.mem_cons_self), smul_smul, mul_comm]

/-- The Mathlib eigenbasis label `k` carries the nonincreasing label `dysonLabel k`. -/
def dysonLabel (N : ℕ) (k : Fin N) : Fin N :=
  Fin.cast (Fintype.card_fin N) ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N)))).symm k)

theorem eigenvalues_eq_dyson {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian) (k : Fin N) :
    hK.eigenvalues k = dysonEigenvalue N K (dysonLabel N k) := by
  rw [dysonEigenvalue_eq_eigenvalues₀ hK]
  simp [Matrix.IsHermitian.eigenvalues, dysonLabel]

/-- On simple spectrum the Lagrange product `P_i` acts on Mathlib's eigenbasis by `δ`. -/
theorem dysonProjection_mulVec_eigenvectorBasis {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : K.IsHermitian) (hs : HasSimpleSpectrum N K) (i k : Fin N) :
    dysonProjection N K i *ᵥ ⇑(hK.eigenvectorBasis k) =
      (if dysonLabel N k = i then (1 : ℂ) else 0) • ⇑(hK.eigenvectorBasis k) := by
  unfold dysonProjection
  have hev : ∀ j, ((((dysonEigenvalue N K i - dysonEigenvalue N K j)⁻¹ : ℂ) •
      (K - (dysonEigenvalue N K j : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))) *ᵥ
        ⇑(hK.eigenvectorBasis k)) =
      (((dysonEigenvalue N K i - dysonEigenvalue N K j)⁻¹ : ℂ) *
        ((dysonEigenvalue N K (dysonLabel N k) : ℂ) - dysonEigenvalue N K j)) •
          ⇑(hK.eigenvectorBasis k) := by
    intro j
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, hK.mulVec_eigenvectorBasis, Matrix.smul_mulVec,
      Matrix.one_mulVec, eigenvalues_eq_dyson hK]
    funext x
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.real_smul]
    ring
  rw [list_prod_mulVec_eigen _ _ _ _ (fun j _ => hev j)]
  congr 1
  split_ifs with hk
  · refine List.prod_eq_one fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hji : j ≠ i := by simpa using (List.mem_filter.mp hj).2
    rw [hk]
    have : (dysonEigenvalue N K i : ℂ) - dysonEigenvalue N K j ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast fun e => hji (hs.injective e).symm
    exact inv_mul_cancel₀ this
  · refine List.prod_eq_zero (List.mem_map.mpr ⟨dysonLabel N k, ?_, by simp⟩)
    exact List.mem_filter.mpr ⟨List.mem_finRange _, by simpa using hk⟩

/-- On simple spectrum: `P_i = U diag(δ_{label k = i}) U*`. -/
theorem dysonProjection_eq_unitary {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (hs : HasSimpleSpectrum N K) (i : Fin N) :
    dysonProjection N K i =
      (↑(hK.eigenvectorUnitary) : Matrix (Fin N) (Fin N) ℂ) *
        diagonal (fun k => if dysonLabel N k = i then (1 : ℂ) else 0) *
          star (↑(hK.eigenvectorUnitary) : Matrix (Fin N) (Fin N) ℂ) := by
  set U : Matrix (Fin N) (Fin N) ℂ := ↑(hK.eigenvectorUnitary)
  have hPU : dysonProjection N K i * U =
      U * diagonal (fun k => if dysonLabel N k = i then (1 : ℂ) else 0) := by
    ext x k
    have h := congrFun (dysonProjection_mulVec_eigenvectorBasis hK hs i k) x
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, U, Matrix.IsHermitian.eigenvectorUnitary_apply]
    rw [h, mul_comm]
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hK.eigenvectorUnitary.2
  calc dysonProjection N K i = dysonProjection N K i * (U * star U) := by rw [hUU, Matrix.mul_one]
    _ = U * diagonal (fun k => if dysonLabel N k = i then (1 : ℂ) else 0) * star U := by
      rw [← Matrix.mul_assoc, hPU]

/-- The quadratic form of `P_i` on simple spectrum: `q* P_i q = |(U* q)_k|²` at the label `k`
with `dysonLabel N k = i`. -/
theorem dysonProjection_quad {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (hs : HasSimpleSpectrum N K) (q : Fin N → ℂ) (k : Fin N) :
    star q ⬝ᵥ (dysonProjection N K (dysonLabel N k) *ᵥ q) =
      ((‖star q ⬝ᵥ ⇑(hK.eigenvectorBasis k)‖ ^ 2 : ℝ) : ℂ) := by
  rw [dysonProjection_eq_unitary hK hs]
  set U : Matrix (Fin N) (Fin N) ℂ := ↑(hK.eigenvectorUnitary)
  set c : Fin N → ℂ := star U *ᵥ q
  have hlab : ∀ k' : Fin N, dysonLabel N k' = dysonLabel N k ↔ k' = k := by
    intro k'
    constructor
    · intro h
      unfold dysonLabel at h
      exact (Equiv.injective _) (Fin.cast_injective _ h)
    · rintro rfl; rfl
  set d : Fin N → ℂ := fun k' => if dysonLabel N k' = dysonLabel N k then (1 : ℂ) else 0
  have h1 : (U * diagonal d * star U) *ᵥ q = U *ᵥ (diagonal d *ᵥ c) := by
    simp only [c, ← Matrix.mulVec_mulVec]
  have hstar : star q ᵥ* U = star c := by
    simp only [c, Matrix.star_mulVec, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  have h2 : star q ⬝ᵥ (U *ᵥ (diagonal d *ᵥ c)) = star (c k) * c k := by
    rw [Matrix.dotProduct_mulVec, hstar]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
    rw [Finset.sum_eq_single k]
    · simp [d]
    · intro k' _ hk'
      have : d k' = 0 := by simp only [d]; rw [ite_eq_right_iff]; exact fun h => absurd ((hlab k').1 h) hk'
      rw [this, zero_mul, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hc : c k = conj (star q ⬝ᵥ ⇑(hK.eigenvectorBasis k)) := by
    simp only [c, U, Matrix.mulVec, dotProduct, Matrix.star_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply, map_sum, map_mul, Pi.star_apply,
      RCLike.star_def, Complex.conj_conj]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [h1, h2, hc, RCLike.star_def, Complex.conj_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The increasing rank `ℓ` sits at Mathlib eigenbasis label `increasingIndex (cast ℓ)`, whose
nonincreasing label is `ℓ.rev`.
-/
theorem dysonLabel_increasingIndex (ℓ : Fin N) :
    dysonLabel N (increasingIndex (Fin.cast (Fintype.card_fin N).symm ℓ)) = ℓ.rev := by
  ext
  simp [dysonLabel, increasingIndex, Fin.val_rev]

/-- **Relabelling of overlaps**: on simple spectrum, `dysonOverlap` at the reversed label is
`N ‖q* u_ℓ‖²` for the selected eigenvector `freshEigenvector K ℓ`. -/
theorem dysonOverlap_rev {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (hs : HasSimpleSpectrum N K) (q : Fin N → ℂ) (ℓ : Fin N) :
    dysonOverlap N q K ℓ.rev = (N : ℝ) * ‖star q ⬝ᵥ freshEigenvector K ℓ‖ ^ 2 := by
  set k := increasingIndex (Fin.cast (Fintype.card_fin N).symm ℓ)
  unfold dysonOverlap
  rw [← dysonLabel_increasingIndex ℓ, dysonProjection_quad hK hs q k, Complex.ofReal_re]
  congr 2
  obtain ⟨z, hz, he⟩ := orderedColumnSelection_eq_phase (Fin.cast (Fintype.card_fin N).symm ℓ)
    ⟨K, hK⟩ (injective_orderedEigenvalue hK hs)
  have hfe : freshEigenvector K ℓ = z • increasingEigenvector hK
      (Fin.cast (Fintype.card_fin N).symm ℓ) := by
    funext x
    simp only [freshEigenvector]
    rw [rawOrderedColumnSelection_eq _ K hK, he]
  rw [hfe, dotProduct_smul, norm_smul, hz, one_mul]
  unfold increasingEigenvector
  rw [increasingEigenbasis_apply]

/-- The coupling at reversed labels is `(N (λ_k - λ_l)²)⁻¹`, as in `flowRate`. -/
theorem dysonCoupling_rev {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian) (k l : Fin N) :
    dysonCoupling N (dysonEigenvalue N K) k.rev l.rev =
      ((N : ℝ) * (freshEigenvalue K k - freshEigenvalue K l) ^ 2)⁻¹ := by
  rw [dysonCoupling, dysonEigenvalue_rev hK, dysonEigenvalue_rev hK, one_div]

end BlockBand.Palm.MomentFlow
