module

public import BlockBand.SourceProcess.Stochastic.Dyson.Spectrum

/-!
# Dyson Brownian motion: the Lagrange spectral projections on simple spectrum

The overlap `X_i = N |q* u_i|²` of `DysonBrownianMotion` is defined through the Lagrange product
`dysonProjection`. For a Hermitian matrix `H` with simple spectrum this module proves, through
the spectral theorem `H = U diag(λ ∘ π) U*` (`spectral_eq`), that
`dysonProjection N H i = U diag([π k = i]) U*` and hence the spectral-projection algebra:
* `proj_mul_proj`: `P_i P_j = δ_ij P_i`; `sum_proj`: `∑ P_i = 1`;
* `mul_proj`, `proj_mul`: `H P_i = P_i H = λ_i P_i`; `trace_proj`: `tr P_i = 1`;
* `proj_isHermitian`.

Here `π = specPerm` is the bijection between Mathlib's eigenbasis labels and the decreasing order.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open Matrix
open scoped Matrix ComplexConjugate
open BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

/-- The Hermitian part `H + Hᴴ` used by `dysonEigenvalue`, as a Hermitian matrix. -/
theorem hB (H : Matrix (Fin N) (Fin N) ℂ) : (H + Hᴴ).IsHermitian :=
  Matrix.isHermitian_add_transpose_self H

/-- Eigenvector unitary of `H + Hᴴ`. -/
def specU (H : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ((hB H).eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)

/-- Relabelling between Mathlib's eigenbasis labels and the decreasing order. -/
def specPerm (N : ℕ) : Fin N ≃ Fin N :=
  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N)))).symm.trans
    (finCongr (Fintype.card_fin N))

theorem specU_star_mul (H : Matrix (Fin N) (Fin N) ℂ) : star (specU H) * specU H = 1 :=
  Unitary.star_mul_self_of_mem (hB H).eigenvectorUnitary.2

theorem specU_mul_star (H : Matrix (Fin N) (Fin N) ℂ) : specU H * star (specU H) = 1 :=
  Unitary.mul_star_self_of_mem (hB H).eigenvectorUnitary.2

theorem eigenvalues_hB_eq (H : Matrix (Fin N) (Fin N) ℂ) (k : Fin N) :
    (hB H).eigenvalues k = 2 * dysonEigenvalue N H (specPerm N k) := by
  simp only [Matrix.IsHermitian.eigenvalues, dysonEigenvalue, specPerm, Equiv.trans_apply,
    finCongr_apply, Fin.cast_cast]
  rw [mul_div_cancel₀ _ (two_ne_zero)]
  rfl

/-- **Spectral theorem in the decreasing labels**: `H = U diag(λ_{π k}) U*` for Hermitian `H`. -/
theorem spectral_eq {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    H = specU H * diagonal (fun k => (dysonEigenvalue N H (specPerm N k) : ℂ)) *
      star (specU H) := by
  have hs := (hB H).spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have h2 : H + Hᴴ = (2 : ℂ) • H := by rw [hH.eq, two_smul]
  have : H = (1 / 2 : ℂ) • (H + Hᴴ) := by
    rw [h2, smul_smul]; norm_num
  conv_lhs => rw [this, hs]
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
  rw [show (1 / 2 : ℂ) • (RCLike.ofReal ∘ (hB H).eigenvalues) =
      fun k => (dysonEigenvalue N H (specPerm N k) : ℂ) from ?_]
  · rfl
  funext k
  simp only [Pi.smul_apply, Function.comp_apply, eigenvalues_hB_eq, smul_eq_mul,
    RCLike.ofReal_eq_complex_ofReal]
  push_cast; ring

theorem conj_list_prod {ι : Type*} {U : Matrix (Fin N) (Fin N) ℂ} (hU : star U * U = 1)
    (hU' : U * star U = 1) (L : List ι) (M : ι → Matrix (Fin N) (Fin N) ℂ) :
    (L.map fun j => U * M j * star U).prod = U * (L.map M).prod * star U := by
  induction L with
  | nil => simp [hU']
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    calc U * M a * star U * (U * (L.map M).prod * star U)
        = U * M a * (star U * U) * (L.map M).prod * star U := by simp only [Matrix.mul_assoc]
      _ = U * (M a * (L.map M).prod) * star U := by rw [hU]; simp only [Matrix.mul_one,
          Matrix.mul_assoc]

theorem diagonal_list_prod {ι : Type*} (L : List ι) (d : ι → Fin N → ℂ) :
    (L.map fun j => diagonal (d j)).prod = diagonal fun k => (L.map fun j => d j k).prod := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, diagonal_mul_diagonal]

theorem projFactor_eq {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (i j : Fin N) :
    projFactor N i j H = specU H * diagonal (fun k =>
      ((dysonEigenvalue N H i - dysonEigenvalue N H j)⁻¹ : ℂ) *
        ((dysonEigenvalue N H (specPerm N k) : ℂ) - dysonEigenvalue N H j)) * star (specU H) := by
  have hone : (dysonEigenvalue N H j : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) =
      specU H * diagonal (fun _ => (dysonEigenvalue N H j : ℂ)) * star (specU H) := by
    rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      specU_mul_star]
  have key : H - (dysonEigenvalue N H j : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) =
      specU H * diagonal (fun k => (dysonEigenvalue N H (specPerm N k) : ℂ) -
        dysonEigenvalue N H j) * star (specU H) := by
    rw [hone]
    nth_rewrite 1 [spectral_eq hH]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  unfold projFactor
  rw [key, ← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
  rfl

/-- **Lagrange product = spectral projection**: on simple spectrum,
`dysonProjection N H i = U diag([π k = i]) U*`. -/
theorem dysonProjection_eq_conj {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hs : HasSimpleSpectrum N H) (i : Fin N) :
    dysonProjection N H i = specU H * diagonal (fun k => if specPerm N k = i then 1 else 0) *
      star (specU H) := by
  rw [dysonProjection_eq]
  simp_rw [projFactor_eq hH i]
  rw [conj_list_prod (specU_star_mul H) (specU_mul_star H), diagonal_list_prod]
  congr 3
  funext k
  split_ifs with hk
  · refine List.prod_eq_one fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hji : j ≠ i := by simpa using (List.mem_filter.mp hj).2
    rw [hk]
    have : (dysonEigenvalue N H i : ℂ) - dysonEigenvalue N H j ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast HasSimpleSpectrum.ne hs hji.symm
    exact inv_mul_cancel₀ this
  · refine List.prod_eq_zero (List.mem_map.mpr ⟨specPerm N k, ?_, by simp⟩)
    exact List.mem_filter.mpr ⟨List.mem_finRange _, by simpa using hk⟩

/-- The diagonal pattern of `P_i`. -/
def projDiag (N : ℕ) (i : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  diagonal fun k => if specPerm N k = i then 1 else 0

theorem projDiag_mul (i j : Fin N) :
    projDiag N i * projDiag N j = if i = j then projDiag N i else 0 := by
  unfold projDiag
  rw [diagonal_mul_diagonal]
  split_ifs with h
  · subst h; congr 1; funext k; split_ifs <;> simp
  · rw [← diagonal_zero]; congr 1; funext k
    split_ifs with h1 h2 <;> simp_all

theorem sum_projDiag : ∑ i, projDiag N i = 1 := by
  unfold projDiag
  rw [← diagonal_one]
  ext a b
  simp [Matrix.sum_apply, diagonal_apply]

theorem conj_mul_conj (H A B : Matrix (Fin N) (Fin N) ℂ) :
    (specU H * A * star (specU H)) * (specU H * B * star (specU H)) =
      specU H * (A * B) * star (specU H) := by
  calc (specU H * A * star (specU H)) * (specU H * B * star (specU H))
      = specU H * A * (star (specU H) * specU H) * B * star (specU H) := by
        simp only [Matrix.mul_assoc]
    _ = specU H * (A * B) * star (specU H) := by
        rw [specU_star_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]

section Simple

variable {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hs : HasSimpleSpectrum N H)
include hH hs

theorem proj_eq (i : Fin N) :
    dysonProjection N H i = specU H * projDiag N i * star (specU H) :=
  dysonProjection_eq_conj hH hs i

/-- `P_i P_j = δ_ij P_i`. -/
theorem proj_mul_proj (i j : Fin N) :
    dysonProjection N H i * dysonProjection N H j =
      if i = j then dysonProjection N H i else 0 := by
  rw [proj_eq hH hs, proj_eq hH hs, conj_mul_conj, projDiag_mul]
  split_ifs <;> simp

/-- `∑_i P_i = 1`. -/
theorem sum_proj : ∑ i, dysonProjection N H i = 1 := by
  simp_rw [proj_eq hH hs]
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_projDiag, Matrix.mul_one, specU_mul_star]

omit hH hs in
theorem diag_mul_projDiag (i : Fin N) :
    diagonal (fun k => (dysonEigenvalue N H (specPerm N k) : ℂ)) * projDiag N i =
      (dysonEigenvalue N H i : ℂ) • projDiag N i := by
  unfold projDiag
  rw [diagonal_mul_diagonal, ← diagonal_smul]
  congr 1; funext k
  simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [h]
  · rfl

omit hH hs in
theorem projDiag_mul_diag (i : Fin N) :
    projDiag N i * diagonal (fun k => (dysonEigenvalue N H (specPerm N k) : ℂ)) =
      (dysonEigenvalue N H i : ℂ) • projDiag N i := by
  unfold projDiag
  rw [diagonal_mul_diagonal, ← diagonal_smul]
  congr 1; funext k
  simp only [Pi.smul_apply, smul_eq_mul, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [h]
  · rfl

/-- `H P_i = λ_i P_i`. -/
theorem mul_proj (i : Fin N) :
    H * dysonProjection N H i = (dysonEigenvalue N H i : ℂ) • dysonProjection N H i := by
  rw [proj_eq hH hs]
  nth_rewrite 1 [spectral_eq hH]
  rw [conj_mul_conj, diag_mul_projDiag, Matrix.mul_smul, Matrix.smul_mul]

/-- `P_i H = λ_i P_i`. -/
theorem proj_mul (i : Fin N) :
    dysonProjection N H i * H = (dysonEigenvalue N H i : ℂ) • dysonProjection N H i := by
  have e : dysonProjection N H i * H = (specU H * projDiag N i * star (specU H)) *
      (specU H * diagonal (fun k => (dysonEigenvalue N H (specPerm N k) : ℂ)) *
        star (specU H)) := by
    rw [← spectral_eq hH, proj_eq hH hs]
  rw [e, conj_mul_conj, projDiag_mul_diag, Matrix.mul_smul, Matrix.smul_mul, proj_eq hH hs]

/-- `tr P_i = 1`. -/
theorem trace_proj (i : Fin N) : trace (dysonProjection N H i) = 1 := by
  rw [proj_eq hH hs, trace_mul_comm, ← Matrix.mul_assoc, specU_star_mul, Matrix.one_mul]
  unfold projDiag
  rw [trace_diagonal]
  rw [Fintype.sum_equiv (specPerm N) _ (fun m => if m = i then (1 : ℂ) else 0) (fun k => rfl)]
  simp

/-- `P_i` is Hermitian. -/
theorem proj_isHermitian (i : Fin N) : (dysonProjection N H i).IsHermitian := by
  rw [proj_eq hH hs]
  unfold IsHermitian projDiag
  simp only [conjTranspose_mul, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose,
    diagonal_conjTranspose, Matrix.mul_assoc]
  congr 3
  funext k
  split_ifs <;> simp_all

end Simple

end BlockBand.SourceProcess.Stochastic.Dyson
