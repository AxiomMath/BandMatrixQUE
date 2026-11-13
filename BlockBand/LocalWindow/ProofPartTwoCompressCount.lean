module

public import BlockBand.LocalWindow.ProofPartTwoLargeRhoSection
public import BlockBand.LocalWindow.ProofPartTwoCount

/-!
# Cauchy interlacing for the compressed window count

Deterministic finite-dimensional linear algebra (no measure), for part (ii) of the physical
local-window lemma. The large-`ρ` transfer
`largeRho_actual_transfer` needs the number of eigenvalues of the compressed matrix
`U*(K + G)U` (index `Fin (2W - 1)`) in `[μ - h_c, μ + h_c]`, `h_c = (2W-1)^{-1+β}`. This
file bounds it by full-matrix counts in two windows of the radius `h_f = (2W)^{-1+β}` of
`gue_windowCount_le`.

## Main results

* `inner_compress_toEuclideanLin`, `norm_isometry_toEuclideanLin`,
  `injective_isometry_toEuclideanLin`, `finrank_map_isometry`: an isometry `U` (`U*U = 1`)
  transports Rayleigh forms of `U*AU` to those of `A`.
* **`card_le_le_of_compress`**, **`card_ge_le_of_compress`** (min–max, one direction):
  `#{λ(U*AU) ≤ c} ≤ #{λ(A) ≤ c}` and `#{λ(U*AU) ≥ c} ≤ #{λ(A) ≥ c}`.
* **`card_Icc_add_le_of_compress`** (Cauchy interlacing in counting form):
  `N_{U*AU}([a,b]) + |κ| ≤ N_A([a,b]) + |ι|`; in codimension one, `N_{U*AU} ≤ N_A + 1`.
* `card_filter_eq_of_eigenfamilies`: counts do not depend on the orthonormal eigenbasis.
* **`natCount_le_pairCount_add_one`**: for selections `sel, sel'`, an isometry
  `U : ℂ^{2W-1} → ℂ^{pair}` and a Hermitian `Y` with `Y = U*XU`,
  `#{k : μ_k(Y) ∈ [a,b]} ≤ #{j : λ_j(X) ∈ [a,b]} + 1`.
* `card_Icc_le_card_add_card`, **`compressRadius_le_two_mul_windowRadius`**
  (`h_c ≤ 2 h_f` for `0 ≤ β ≤ 1`), **`natCount_le_two_windows_add_one`**: the compressed count in
  `[μ - h_c, μ + h_c]` is at most the full counts in `[μ - h_f ± h_f]` and `[μ + h_f ± h_f]`
  plus one.
* `pairRootRectangle_shift_half`: a root rectangle of radius `r` at `E₀` contains one of radius
  `r/2` at every `E₁` with `|E₁ - E₀| ≤ r/2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix Module WithLp Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.ProofCount
open scoped InnerProductSpace ComplexOrder ENNReal Matrix.Norms.L2Operator

/-!
## Cauchy interlacing in counting form
-/

section Interlace

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

/-- `⟪Ux, A(Uy)⟫ = ⟪x, (U*AU)y⟫`. -/
theorem inner_compress_toEuclideanLin (U : Matrix ι κ ℂ) (A : Matrix ι ι ℂ)
    (x y : EuclideanSpace ℂ κ) :
    ⟪T U x, T A (T U y)⟫_ℂ = ⟪x, T (Uᴴ * A * U) y⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  change (A *ᵥ (U *ᵥ ofLp y)) ⬝ᵥ star (U *ᵥ ofLp x) =
    ((Uᴴ * A * U) *ᵥ ofLp y) ⬝ᵥ star (ofLp x)
  rw [dotProduct_comm, dotProduct_comm _ (star _), star_mulVec, ← dotProduct_mulVec,
    mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/-- An isometry `U*U = 1` preserves inner products. -/
theorem inner_isometry_toEuclideanLin {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1)
    (x y : EuclideanSpace ℂ κ) : ⟪T U x, T U y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  change (U *ᵥ ofLp y) ⬝ᵥ star (U *ᵥ ofLp x) = ofLp y ⬝ᵥ star (ofLp x)
  rw [dotProduct_comm, dotProduct_comm _ (star _), star_mulVec, ← dotProduct_mulVec,
    mulVec_mulVec, hU, one_mulVec]

/-- An isometry `U*U = 1` preserves norms. -/
theorem norm_isometry_toEuclideanLin {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1)
    (x : EuclideanSpace ℂ κ) : ‖T U x‖ = ‖x‖ := by
  have h := inner_isometry_toEuclideanLin hU x x
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), @norm_sq_eq_re_inner ℂ,
    @norm_sq_eq_re_inner ℂ, h]

/-- An isometry is injective. -/
theorem injective_isometry_toEuclideanLin {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1) :
    Function.Injective (T U) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  have h := norm_isometry_toEuclideanLin hU x
  rw [hx, norm_zero] at h
  exact norm_eq_zero.mp h.symm

/-- The image of a subspace under an isometry has the same dimension. -/
theorem finrank_map_isometry {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1)
    (S : Submodule ℂ (EuclideanSpace ℂ κ)) : finrank ℂ (S.map (T U)) = finrank ℂ S :=
  (Submodule.equivMapOfInjective _ (injective_isometry_toEuclideanLin hU) S).finrank_eq.symm

variable {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} {U : Matrix ι κ ℂ}

/-- **Lower counts under compression** (min–max): for `B = U*AU` with `U*U = 1`,
`#{λ(B) ≤ c} ≤ #{λ(A) ≤ c}`. -/
theorem card_le_le_of_compress (hA : A.IsHermitian) (hU : Uᴴ * U = 1) (hB : B.IsHermitian)
    (hBA : B = Uᴴ * A * U) (c : ℝ) :
    (Finset.univ.filter fun k => hB.eigenvalues k ≤ c).card ≤
      (Finset.univ.filter fun j => hA.eigenvalues j ≤ c).card := by
  have h := finrank_le_card_le hA ((lowSpan hB c).map (T U)) (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    rw [inner_compress_toEuclideanLin, ← hBA, norm_isometry_toEuclideanLin hU]
    exact rayleigh_le_of_mem_lowSpan hB hx)
  rwa [finrank_map_isometry hU, finrank_lowSpan] at h

/-- **Upper counts under compression** (min–max): for `B = U*AU` with `U*U = 1`,
`#{λ(B) ≥ c} ≤ #{λ(A) ≥ c}`. -/
theorem card_ge_le_of_compress (hA : A.IsHermitian) (hU : Uᴴ * U = 1) (hB : B.IsHermitian)
    (hBA : B = Uᴴ * A * U) (c : ℝ) :
    (Finset.univ.filter fun k => c ≤ hB.eigenvalues k).card ≤
      (Finset.univ.filter fun j => c ≤ hA.eigenvalues j).card := by
  have h := finrank_le_card_ge hA ((highSpan hB c).map (T U)) (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    rw [inner_compress_toEuclideanLin, ← hBA, norm_isometry_toEuclideanLin hU]
    exact le_rayleigh_of_mem_highSpan hB hx)
  rwa [finrank_map_isometry hU, finrank_highSpan] at h

/-- `|κ| ≤ |ι|` for an isometry `U : ℂ^κ → ℂ^ι`. -/
theorem card_le_card_of_isometry (hU : Uᴴ * U = 1) : Fintype.card κ ≤ Fintype.card ι := by
  have h := LinearMap.finrank_le_finrank_of_injective (injective_isometry_toEuclideanLin hU)
  rwa [finrank_euclideanSpace, finrank_euclideanSpace] at h

/-- `#{a ≤ λ ≤ b} + |ι| = #{λ ≤ b} + #{λ ≥ a}` for `a ≤ b`. -/
theorem card_Icc_add_card_eq {lam : ι → ℝ} {a b : ℝ} (hab : a ≤ b) :
    (Finset.univ.filter fun j => a ≤ lam j ∧ lam j ≤ b).card + Fintype.card ι =
      (Finset.univ.filter fun j => lam j ≤ b).card +
        (Finset.univ.filter fun j => a ≤ lam j).card := by
  have hu : (Finset.univ.filter fun j => lam j ≤ b) ∪
      (Finset.univ.filter fun j => a ≤ lam j) = Finset.univ := by
    ext j; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    by_contra hc; push Not at hc; linarith [hc.1, hc.2]
  have hi : (Finset.univ.filter fun j => lam j ≤ b) ∩
      (Finset.univ.filter fun j => a ≤ lam j) =
      (Finset.univ.filter fun j => a ≤ lam j ∧ lam j ≤ b) := by
    ext j; simp [and_comm]
  have e := Finset.card_union_add_card_inter (Finset.univ.filter fun j => lam j ≤ b)
    (Finset.univ.filter fun j => a ≤ lam j)
  rw [hu, hi, Finset.card_univ] at e
  omega

/-- **Cauchy interlacing in counting form**: for `B = U*AU` with `U*U = 1` and every `[a, b]`,
`N_B([a,b]) + |κ| ≤ N_A([a,b]) + |ι|`. -/
theorem card_Icc_add_le_of_compress (hA : A.IsHermitian) (hU : Uᴴ * U = 1)
    (hB : B.IsHermitian) (hBA : B = Uᴴ * A * U) (a b : ℝ) :
    (Finset.univ.filter fun k => a ≤ hB.eigenvalues k ∧ hB.eigenvalues k ≤ b).card +
        Fintype.card κ ≤
      (Finset.univ.filter fun j => a ≤ hA.eigenvalues j ∧ hA.eigenvalues j ≤ b).card +
        Fintype.card ι := by
  by_cases hab : a ≤ b
  · rw [card_Icc_add_card_eq hab, card_Icc_add_card_eq hab]
    exact add_le_add (card_le_le_of_compress hA hU hB hBA b)
      (card_ge_le_of_compress hA hU hB hBA a)
  · have : (Finset.univ.filter fun k => a ≤ hB.eigenvalues k ∧ hB.eigenvalues k ≤ b) = ∅ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hk; exact hab (hk.1.trans hk.2)
    rw [this, Finset.card_empty, zero_add]
    exact (card_le_card_of_isometry hU).trans (Nat.le_add_left _ _)

/-- **Counts do not depend on the orthonormal eigenbasis**: for Hermitian `X` with two
orthonormal eigenfamilies `(e, μ)` and `(v, λ)`, `#{k : P(μ_k)} = #{j : P(λ_j)}`. -/
theorem card_filter_eq_of_eigenfamilies {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    {e v : ι → ι → ℂ} (he : IsOrthonormalFamily e) (hv : IsOrthonormalFamily v) {μ lam : ι → ℝ}
    (heig : ∀ k, X *ᵥ e k = (μ k : ℂ) • e k) (hveig : ∀ j, X *ᵥ v j = (lam j : ℂ) • v j)
    (P : ℝ → Prop) [DecidablePred P] :
    (Finset.univ.filter fun k => P (μ k)).card = (Finset.univ.filter fun j => P (lam j)).card := by
  have h := sum_eq_sum_of_eigenfamilies hX he hv heig hveig (fun x => if P x then (1 : ℝ) else 0)
  have h' : ((Finset.univ.filter fun k => P (μ k)).card : ℝ) =
      ((Finset.univ.filter fun j => P (lam j)).card : ℝ) := by
    rw [Finset.card_filter, Finset.card_filter]
    push_cast
    exact h
  exact_mod_cast h'

/-- **An interval count is covered by two windows**: if `h_c ≤ 2 h_f`, the number of `μ_k` in
`[c - h_c, c + h_c]` is at most the numbers in `[c - h_f ± h_f]` and `[c + h_f ± h_f]`. -/
theorem card_Icc_le_card_add_card (μ : ι → ℝ) {c hc hf : ℝ} (hcf : hc ≤ 2 * hf) :
    (Finset.univ.filter fun k => μ k ∈ Icc (c - hc) (c + hc)).card ≤
      (Finset.univ.filter fun k => μ k ∈ Icc ((c - hf) - hf) ((c - hf) + hf)).card +
        (Finset.univ.filter fun k => μ k ∈ Icc ((c + hf) - hf) ((c + hf) + hf)).card := by
  refine (Finset.card_le_card fun k hk => ?_).trans (Finset.card_union_le _ _)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_Icc, Finset.mem_union] at hk ⊢
  by_cases hkc : μ k ≤ c
  · left; constructor <;> linarith
  · right; constructor <;> linarith

end Interlace

/-!
## The compressed pair count
-/

section Pair

variable {p : Parameters} {i : ZMod p.n}

/-- **The compressed count is at most the full count plus one** (Cauchy interlacing): for
eigenpair selections `sel` (dimension `2W`) and `sel'` (dimension `2W - 1`), an isometry
`U : ℂ^{2W-1} → ℂ^{pair}` (`U*U = 1`), a Hermitian pair matrix `X` and a Hermitian `Y`
with `Y = U*XU`, for every `[a, b]`:
`#{k : μ_k(Y) ∈ [a,b]} ≤ #{j : λ_j(X) ∈ [a,b]} + 1`. -/
theorem natCount_le_pairCount_add_one (sel : CEH.EigenpairSelection (2 * p.W))
    (sel' : CEH.EigenpairSelection (2 * p.W - 1))
    {U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ} (hU : Uᴴ * U = 1) {X : PairMatrix p i}
    (hX : X.IsHermitian) (Y : CEH.SourceHermitian (2 * p.W - 1)) (hY : Y.1 = Uᴴ * X * U)
    (a b : ℝ) :
    (Finset.univ.filter fun k => sel'.eigenvalue Y k ∈ Icc a b).card ≤
      (Finset.univ.filter fun j => pairEigval sel X hX j ∈ Icc a b).card + 1 := by
  have e1 := card_filter_eq_of_eigenfamilies Y.2 (fun k l => sel'.orthonormal Y k l)
    (isOrthonormalFamily_eigenvectorBasis Y.2) (fun k => sel'.eigen_equation Y k)
    (mulVec_eigenvectorBasis_complex Y.2) (· ∈ Icc a b)
  have e2 := card_filter_eq_of_eigenfamilies hX (isOrthonormalFamily_pairEigvec sel X hX)
    (isOrthonormalFamily_eigenvectorBasis hX) (mulVec_pairEigvec sel X hX)
    (mulVec_eigenvectorBasis_complex hX) (· ∈ Icc a b)
  simp only [mem_Icc] at e1 e2 ⊢
  rw [e1, e2]
  have h := card_Icc_add_le_of_compress hX hU Y.2 hY a b
  rw [Fintype.card_fin, BlockBand.Angular.FiberAngular.card_pairSite] at h
  have := p.W_pos
  omega

/-- **The compressed radius is at most twice the full radius**: for `0 ≤ β ≤ 1`,
`(2W - 1)^{-1+β} ≤ 2 (2W)^{-1+β}`. -/
theorem compressRadius_le_two_mul_windowRadius {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    compressRadius p β ≤ 2 * windowRadius p β := by
  unfold compressRadius windowRadius
  set n : ℝ := ((2 * p.W - 1 : ℕ) : ℝ) with hn
  have hW := p.W_pos
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast (by omega : 1 ≤ 2 * p.W - 1)
  have hd : ((2 * p.W : ℕ) : ℝ) = n + 1 := by
    rw [hn]; exact_mod_cast (by omega : 2 * p.W = 2 * p.W - 1 + 1)
  rw [hd]
  have hz : -1 + β ≤ 0 := by linarith
  have h1 : (2 * n) ^ (-1 + β) ≤ (n + 1) ^ (-1 + β) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) hz
  have h2 : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ (-1 + β) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [Real.mul_rpow (by norm_num) (by linarith)] at h1
  have h3 : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hn0 : 0 ≤ n ^ (-1 + β) := Real.rpow_nonneg (by linarith) _
  have h4 : 1 / 2 * n ^ (-1 + β) ≤ (2 : ℝ) ^ (-1 + β) * n ^ (-1 + β) :=
    mul_le_mul_of_nonneg_right (h3 ▸ h2) hn0
  linarith

/-- **The compressed window count by two full windows**: with
`h_c = (2W - 1)^{-1+β}` (`compressRadius`), `h_f = (2W)^{-1+β}` (`windowRadius`), `0 ≤ β ≤ 1`,
an isometry `U` and `Y = U*XU`, the number of selected eigenvalues of `Y` in `[μ - h_c, μ + h_c]`
is at most the numbers of selected eigenvalues of `X` in `[(μ - h_f) ± h_f]` and in
`[(μ + h_f) ± h_f]`, plus one. -/
theorem natCount_le_two_windows_add_one (sel : CEH.EigenpairSelection (2 * p.W))
    (sel' : CEH.EigenpairSelection (2 * p.W - 1))
    {U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ} (hU : Uᴴ * U = 1) {X : PairMatrix p i}
    (hX : X.IsHermitian) (Y : CEH.SourceHermitian (2 * p.W - 1)) (hY : Y.1 = Uᴴ * X * U)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (μ : ℝ) :
    (Finset.univ.filter fun k => sel'.eigenvalue Y k ∈
        Icc (μ - compressRadius p β) (μ + compressRadius p β)).card ≤
      (Finset.univ.filter fun j => pairEigval sel X hX j ∈
          Icc ((μ - windowRadius p β) - windowRadius p β)
            ((μ - windowRadius p β) + windowRadius p β)).card +
        (Finset.univ.filter fun j => pairEigval sel X hX j ∈
          Icc ((μ + windowRadius p β) - windowRadius p β)
            ((μ + windowRadius p β) + windowRadius p β)).card + 1 := by
  refine (natCount_le_pairCount_add_one sel sel' hU hX Y hY _ _).trans ?_
  exact Nat.add_le_add_right (card_Icc_le_card_add_card _
    (compressRadius_le_two_mul_windowRadius hβ hβ1)) 1

/-- **Shifting a root rectangle**: `PairRootRectangle K s E₀ r v₀` and `|E₁ - E₀| ≤ r/2` give
`PairRootRectangle K s E₁ (r/2) v₀`. -/
theorem pairRootRectangle_shift_half {K : PairMatrix p i} {s E₀ r v₀ : ℝ}
    (hR : PairRootRectangle K s E₀ r v₀) {E₁ : ℝ} (hE : |E₁ - E₀| ≤ r / 2) :
    PairRootRectangle K s E₁ (r / 2) v₀ := by
  intro x hx η hη hη1
  refine hR x ?_ η hη hη1
  calc |x - E₀| = |(x - E₁) + (E₁ - E₀)| := by ring_nf
    _ ≤ |x - E₁| + |E₁ - E₀| := abs_add_le _ _
    _ ≤ r / 2 + r / 2 := add_le_add hx hE
    _ = r := by ring

end Pair

end BlockBand.LocalWindow.ProofPartTwo
