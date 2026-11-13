module

public import BlockBand.Internal.Contracts.Inputs
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Deterministic eigenvalue counting under perturbation

Min–max counting for Hermitian matrices under finite-rank, small-norm perturbations, used in
part (i) of the physical local-window lemma. Deterministic finite-dimensional linear algebra. Counts are with
multiplicity, through `Inputs.spectralSum` of indicators.

## Main results

* `finrank_le_card_le` (min–max, one direction, no ordering of eigenvalues): a subspace on
  which the Rayleigh form of a Hermitian `A` is `≤ c` has dimension at most `#{λ_j(A) ≤ c}`;
  `finrank_le_card_ge` is the symmetric statement.
* `card_le_le` / `card_ge_le`: if the Rayleigh forms of `A'` and `A`
  differ by at most `r‖y‖²` on a subspace `Y` of codimension `≤ k`, then
  `#{λ(A) ≤ c} ≤ #{λ(A') ≤ c + r} + k` and `#{λ(A) ≥ c} ≤ #{λ(A') ≥ c - r} + k`.
* `window_count_le` (the interval form, Weyl + rank-`k` interlacing in one statement):
  `N_A([a,b]) ≤ N_{A'}([a-r, b+r]) + 2k`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofCount

open Matrix Module WithLp Finset
open scoped InnerProductSpace ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

/-!
## Rayleigh expansion in an orthonormal eigenbasis
-/

section Core

variable {A : Matrix ι ι ℂ}

/-- `Re⟪x, A x⟫ = Σ_j μ_j |⟪b_j, x⟫|²` in any orthonormal eigenbasis `(b_j, μ_j)` of a
Hermitian `A`. -/
theorem re_inner_eq_sum (hA : A.IsHermitian) (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι))
    (μ : ι → ℝ) (hb : ∀ j, T A (b j) = ((μ j : ℝ) : ℂ) • b j) (x : EuclideanSpace ℂ ι) :
    RCLike.re ⟪x, T A x⟫_ℂ = ∑ j, μ j * ‖⟪b j, x⟫_ℂ‖ ^ 2 := by
  have hsym : (T A).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  rw [← b.sum_inner_mul_inner x (T A x), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hsym (b j) x, hb j, inner_smul_left, Complex.conj_ofReal, ← inner_conj_symm x (b j)]
  rw [mul_left_comm, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  exact Complex.ofReal_re _

/-- `‖x‖² = Σ_j |⟪b_j, x⟫|²`. -/
theorem norm_sq_eq_sum (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (x : EuclideanSpace ℂ ι) :
    ‖x‖ ^ 2 = ∑ j, ‖⟪b j, x⟫_ℂ‖ ^ 2 :=
  (b.sum_sq_norm_inner_right x).symm

/-- A vector in the span of `{b_k : k ∈ s}` is orthogonal to `b_j` for `j ∉ s`. -/
theorem inner_eq_zero_of_mem_span (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι))
    (s : ι → Prop) {x : EuclideanSpace ℂ ι}
    (hx : x ∈ Submodule.span ℂ (Set.range fun k : {k // s k} => b k.1)) {j : ι} (hj : ¬ s j) :
    ⟪b j, x⟫_ℂ = 0 := by
  have hle : Submodule.span ℂ (Set.range fun k : {k // s k} => b k.1) ≤ (ℂ ∙ b j)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    have hkj : j ≠ k.1 := fun h => hj (h ▸ k.2)
    exact b.orthonormal.2 hkj
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mp (hle hx)

/-- The span of `{b_k : k ∈ s}` has dimension `#s`. -/
theorem finrank_span_sub (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (s : ι → Prop)
    [DecidablePred s] :
    finrank ℂ (Submodule.span ℂ (Set.range fun k : {k // s k} => b k.1)) =
      (univ.filter s).card := by
  have hli : LinearIndependent ℂ (fun k : {k // s k} => b k.1) :=
    b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  rw [finrank_span_eq_card hli, Fintype.card_subtype]

/-- **Min–max, one direction.** If `Re⟪x, A x⟫ ≤ c‖x‖²` on a subspace `S`, then
`dim S ≤ #{j : μ_j ≤ c}` for any orthonormal eigenbasis `(b_j, μ_j)` of the Hermitian `A`. -/
theorem finrank_le_card_le_of_basis (hA : A.IsHermitian)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (μ : ι → ℝ)
    (hb : ∀ j, T A (b j) = ((μ j : ℝ) : ℂ) • b j) {c : ℝ}
    (S : Submodule ℂ (EuclideanSpace ℂ ι))
    (hS : ∀ x ∈ S, RCLike.re ⟪x, T A x⟫_ℂ ≤ c * ‖x‖ ^ 2) :
    finrank ℂ S ≤ (univ.filter fun j => μ j ≤ c).card := by
  classical
  set Z := Submodule.span ℂ (Set.range fun k : {k // c < μ k} => b k.1)
  have hdisj : S ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxZ⟩ := Submodule.mem_inf.mp hx
    have hzero : ∀ j, μ j ≤ c → ⟪b j, x⟫_ℂ = 0 := fun j hj =>
      inner_eq_zero_of_mem_span b (fun k => c < μ k) hxZ (not_lt.mpr hj)
    have hR := hS x hxS
    rw [re_inner_eq_sum hA b μ hb x, norm_sq_eq_sum b x, Finset.mul_sum] at hR
    have hterm : ∀ j, 0 ≤ (μ j - c) * ‖⟪b j, x⟫_ℂ‖ ^ 2 := by
      intro j
      by_cases hj : μ j ≤ c
      · rw [hzero j hj]; simp
      · exact mul_nonneg (by linarith [not_le.mp hj]) (sq_nonneg _)
    have hsum : ∑ j, (μ j - c) * ‖⟪b j, x⟫_ℂ‖ ^ 2 = 0 := by
      apply le_antisymm
      · have : ∑ j, (μ j - c) * ‖⟪b j, x⟫_ℂ‖ ^ 2 =
            ∑ j, μ j * ‖⟪b j, x⟫_ℂ‖ ^ 2 - ∑ j, c * ‖⟪b j, x⟫_ℂ‖ ^ 2 := by
          rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
        linarith
      · exact Finset.sum_nonneg fun j _ => hterm j
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).mp hsum
    have hcoef : ∀ j, ⟪b j, x⟫_ℂ = 0 := by
      intro j
      by_cases hj : μ j ≤ c
      · exact hzero j hj
      · have h := hall j (Finset.mem_univ j)
        have hpos : 0 < μ j - c := by linarith [not_le.mp hj]
        have : ‖⟪b j, x⟫_ℂ‖ ^ 2 = 0 := by
          rcases mul_eq_zero.mp h with h' | h'
          · linarith
          · exact h'
        exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp this)
    have hx0 : ‖x‖ ^ 2 = 0 := by rw [norm_sq_eq_sum b x]; simp [hcoef]
    rw [Submodule.mem_bot]
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hx0)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq S Z
  have h2 := Submodule.finrank_le (S ⊔ Z)
  rw [hdisj, finrank_bot, finrank_euclideanSpace] at *
  have h3 : finrank ℂ Z = (univ.filter fun j => c < μ j).card := finrank_span_sub b _
  have h4 : (univ.filter fun j => μ j ≤ c).card + (univ.filter fun j => c < μ j).card =
      Fintype.card ι := by
    have := Finset.card_filter_add_card_filter_not (s := univ) (fun j => μ j ≤ c)
    simp only [not_le] at this
    rw [this, Finset.card_univ]
  omega

end Core

/-!
## Mathlib's eigenbasis
-/

section Hermitian

variable {A : Matrix ι ι ℂ}

/-- The eigenvectors of a Hermitian matrix, as Euclidean vectors. -/
theorem toE_eigenvectorBasis (hA : A.IsHermitian) (j : ι) :
    T A (hA.eigenvectorBasis j) = ((hA.eigenvalues j : ℝ) : ℂ) • hA.eigenvectorBasis j := by
  have h := hA.mulVec_eigenvectorBasis j
  apply ofLp_injective (p := 2)
  rw [show T A (hA.eigenvectorBasis j) = toLp 2 (A *ᵥ ofLp (hA.eigenvectorBasis j)) from rfl,
    ofLp_toLp, ofLp_smul, h]
  ext k
  simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]

/-- Min–max: Rayleigh form `≤ c` on `S` gives `dim S ≤ #{λ_j ≤ c}`. -/
theorem finrank_le_card_le (hA : A.IsHermitian) {c : ℝ} (S : Submodule ℂ (EuclideanSpace ℂ ι))
    (hS : ∀ x ∈ S, RCLike.re ⟪x, T A x⟫_ℂ ≤ c * ‖x‖ ^ 2) :
    finrank ℂ S ≤ (univ.filter fun j => hA.eigenvalues j ≤ c).card :=
  finrank_le_card_le_of_basis hA hA.eigenvectorBasis hA.eigenvalues (toE_eigenvectorBasis hA) S hS

/-- Min–max, symmetric form: Rayleigh form `≥ c` on `S` gives `dim S ≤ #{λ_j ≥ c}`. -/
theorem finrank_le_card_ge (hA : A.IsHermitian) {c : ℝ} (S : Submodule ℂ (EuclideanSpace ℂ ι))
    (hS : ∀ x ∈ S, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, T A x⟫_ℂ) :
    finrank ℂ S ≤ (univ.filter fun j => c ≤ hA.eigenvalues j).card := by
  have hb : ∀ j, T (-A) (hA.eigenvectorBasis j) =
      ((-hA.eigenvalues j : ℝ) : ℂ) • hA.eigenvectorBasis j := by
    intro j
    rw [map_neg, LinearMap.neg_apply, toE_eigenvectorBasis hA j, Complex.ofReal_neg, neg_smul]
  have h := finrank_le_card_le_of_basis hA.neg hA.eigenvectorBasis (fun j => -hA.eigenvalues j)
    hb (c := -c) S (fun x hx => by
      rw [map_neg, LinearMap.neg_apply, inner_neg_right, map_neg]
      linarith [hS x hx])
  have he : (univ.filter fun j => -hA.eigenvalues j ≤ -c) =
      (univ.filter fun j => c ≤ hA.eigenvalues j) := by
    ext j; simp
  rwa [he] at h

/-- The span of the eigenvectors with `λ_j ≤ c`. -/
def lowSpan (hA : A.IsHermitian) (c : ℝ) : Submodule ℂ (EuclideanSpace ℂ ι) :=
  Submodule.span ℂ (Set.range fun k : {k // hA.eigenvalues k ≤ c} => hA.eigenvectorBasis k.1)

/-- The span of the eigenvectors with `λ_j ≥ c`. -/
def highSpan (hA : A.IsHermitian) (c : ℝ) : Submodule ℂ (EuclideanSpace ℂ ι) :=
  Submodule.span ℂ (Set.range fun k : {k // c ≤ hA.eigenvalues k} => hA.eigenvectorBasis k.1)

theorem finrank_lowSpan (hA : A.IsHermitian) (c : ℝ) :
    finrank ℂ (lowSpan hA c) = (univ.filter fun j => hA.eigenvalues j ≤ c).card :=
  finrank_span_sub hA.eigenvectorBasis _

theorem finrank_highSpan (hA : A.IsHermitian) (c : ℝ) :
    finrank ℂ (highSpan hA c) = (univ.filter fun j => c ≤ hA.eigenvalues j).card :=
  finrank_span_sub hA.eigenvectorBasis _

theorem rayleigh_le_of_mem_lowSpan (hA : A.IsHermitian) {c : ℝ} {x : EuclideanSpace ℂ ι}
    (hx : x ∈ lowSpan hA c) : RCLike.re ⟪x, T A x⟫_ℂ ≤ c * ‖x‖ ^ 2 := by
  rw [re_inner_eq_sum hA hA.eigenvectorBasis hA.eigenvalues (toE_eigenvectorBasis hA),
    norm_sq_eq_sum hA.eigenvectorBasis, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : hA.eigenvalues j ≤ c
  · exact mul_le_mul_of_nonneg_right hj (sq_nonneg _)
  · rw [inner_eq_zero_of_mem_span hA.eigenvectorBasis (fun k => hA.eigenvalues k ≤ c) hx hj]
    simp

theorem le_rayleigh_of_mem_highSpan (hA : A.IsHermitian) {c : ℝ} {x : EuclideanSpace ℂ ι}
    (hx : x ∈ highSpan hA c) : c * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, T A x⟫_ℂ := by
  rw [re_inner_eq_sum hA hA.eigenvectorBasis hA.eigenvalues (toE_eigenvectorBasis hA),
    norm_sq_eq_sum hA.eigenvectorBasis, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : c ≤ hA.eigenvalues j
  · exact mul_le_mul_of_nonneg_right hj (sq_nonneg _)
  · rw [inner_eq_zero_of_mem_span hA.eigenvectorBasis (fun k => c ≤ hA.eigenvalues k) hx hj]
    simp

/-- `dim (X ⊓ Y) + n ≥ dim X + dim Y`. -/
theorem finrank_inf_add (X Y : Submodule ℂ (EuclideanSpace ℂ ι)) :
    finrank ℂ X + finrank ℂ Y ≤ finrank ℂ ↥(X ⊓ Y) + Fintype.card ι := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq X Y
  have h2 := Submodule.finrank_le (X ⊔ Y)
  rw [finrank_euclideanSpace] at h2
  omega

end Hermitian

/-!
## Perturbation of one-sided and interval counts
-/

/-- `A'` is a perturbation of `A` of rank `≤ k` and quadratic-form size `≤ r`: on some
subspace `Y` of codimension at most `k` the Rayleigh forms differ by at most `r‖y‖²`. -/
def IsPerturbation (A A' : Matrix ι ι ℂ) (k : ℕ) (r : ℝ) : Prop :=
  ∃ Y : Submodule ℂ (EuclideanSpace ℂ ι), Fintype.card ι ≤ finrank ℂ Y + k ∧
    ∀ y ∈ Y, |RCLike.re ⟪y, T A' y⟫_ℂ - RCLike.re ⟪y, T A y⟫_ℂ| ≤ r * ‖y‖ ^ 2

section Perturbation

variable {A A' : Matrix ι ι ℂ}

/-- `#{λ(A) ≤ c} ≤ #{λ(A') ≤ c + r} + k`. -/
theorem card_le_le (hA : A.IsHermitian) (hA' : A'.IsHermitian) {k : ℕ} {r : ℝ}
    (h : IsPerturbation A A' k r) (c : ℝ) :
    (univ.filter fun j => hA.eigenvalues j ≤ c).card ≤
      (univ.filter fun j => hA'.eigenvalues j ≤ c + r).card + k := by
  obtain ⟨Y, hY, hr⟩ := h
  have hS := finrank_le_card_le hA' (c := c + r) (lowSpan hA c ⊓ Y) (fun y hy => by
    obtain ⟨hyX, hyY⟩ := Submodule.mem_inf.mp hy
    have h1 := rayleigh_le_of_mem_lowSpan hA hyX
    have h2 := (abs_le.mp (hr y hyY)).2
    nlinarith)
  have hd := finrank_inf_add (lowSpan hA c) Y
  rw [finrank_lowSpan] at hd
  omega

/-- `#{λ(A) ≥ c} ≤ #{λ(A') ≥ c - r} + k`. -/
theorem card_ge_le (hA : A.IsHermitian) (hA' : A'.IsHermitian) {k : ℕ} {r : ℝ}
    (h : IsPerturbation A A' k r) (c : ℝ) :
    (univ.filter fun j => c ≤ hA.eigenvalues j).card ≤
      (univ.filter fun j => c - r ≤ hA'.eigenvalues j).card + k := by
  obtain ⟨Y, hY, hr⟩ := h
  have hS := finrank_le_card_ge hA' (c := c - r) (highSpan hA c ⊓ Y) (fun y hy => by
    obtain ⟨hyX, hyY⟩ := Submodule.mem_inf.mp hy
    have h1 := le_rayleigh_of_mem_highSpan hA hyX
    have h2 := (abs_le.mp (hr y hyY)).1
    nlinarith)
  have hd := finrank_inf_add (highSpan hA c) Y
  rw [finrank_highSpan] at hd
  omega

/-- **Interval counts under perturbation** (Weyl and rank-`k` interlacing together):
`N_A([a,b]) ≤ N_{A'}([a-r, b+r]) + 2k`. -/
theorem card_Icc_le (hA : A.IsHermitian) (hA' : A'.IsHermitian) {k : ℕ} {r : ℝ}
    (h : IsPerturbation A A' k r) (a b : ℝ) :
    (univ.filter fun j => a ≤ hA.eigenvalues j ∧ hA.eigenvalues j ≤ b).card ≤
      (univ.filter fun j => a - r ≤ hA'.eigenvalues j ∧ hA'.eigenvalues j ≤ b + r).card +
        2 * k := by
  by_cases hab : a ≤ b
  · have h1 := card_le_le hA hA' h b
    have h2 := card_ge_le hA hA' h a
    have hu : (univ.filter fun j => hA.eigenvalues j ≤ b) ∪
        (univ.filter fun j => a ≤ hA.eigenvalues j) = univ := by
      ext j; simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
      by_contra hc; push Not at hc; linarith [hc.1, hc.2]
    have hi : (univ.filter fun j => hA.eigenvalues j ≤ b) ∩
        (univ.filter fun j => a ≤ hA.eigenvalues j) =
        (univ.filter fun j => a ≤ hA.eigenvalues j ∧ hA.eigenvalues j ≤ b) := by
      ext j; simp [and_comm]
    have hi' : (univ.filter fun j => hA'.eigenvalues j ≤ b + r) ∩
        (univ.filter fun j => a - r ≤ hA'.eigenvalues j) =
        (univ.filter fun j => a - r ≤ hA'.eigenvalues j ∧ hA'.eigenvalues j ≤ b + r) := by
      ext j; simp [and_comm]
    have e1 := Finset.card_union_add_card_inter (univ.filter fun j => hA.eigenvalues j ≤ b)
      (univ.filter fun j => a ≤ hA.eigenvalues j)
    have e2 := Finset.card_union_add_card_inter (univ.filter fun j => hA'.eigenvalues j ≤ b + r)
      (univ.filter fun j => a - r ≤ hA'.eigenvalues j)
    have e3 := Finset.card_le_univ ((univ.filter fun j => hA'.eigenvalues j ≤ b + r) ∪
      (univ.filter fun j => a - r ≤ hA'.eigenvalues j))
    rw [hu, hi, Finset.card_univ] at e1
    rw [hi'] at e2
    omega
  · have : (univ.filter fun j => a ≤ hA.eigenvalues j ∧ hA.eigenvalues j ≤ b) = ∅ := by
      ext j; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hj; exact hab (hj.1.trans hj.2)
    rw [this, Finset.card_empty]
    exact Nat.zero_le _

/-- Composition of perturbations: ranks and sizes add. -/
theorem IsPerturbation.trans {A'' : Matrix ι ι ℂ} {k k' : ℕ} {r r' : ℝ}
    (h : IsPerturbation A A' k r) (h' : IsPerturbation A' A'' k' r') :
    IsPerturbation A A'' (k + k') (r + r') := by
  obtain ⟨Y, hY, hr⟩ := h
  obtain ⟨Y', hY', hr'⟩ := h'
  refine ⟨Y ⊓ Y', ?_, fun y hy => ?_⟩
  · have := finrank_inf_add Y Y'
    omega
  · obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.mp hy
    have h1 := hr y hy1
    have h2 := hr' y hy2
    calc |RCLike.re ⟪y, T A'' y⟫_ℂ - RCLike.re ⟪y, T A y⟫_ℂ|
        = |(RCLike.re ⟪y, T A'' y⟫_ℂ - RCLike.re ⟪y, T A' y⟫_ℂ) +
            (RCLike.re ⟪y, T A' y⟫_ℂ - RCLike.re ⟪y, T A y⟫_ℂ)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ r' * ‖y‖ ^ 2 + r * ‖y‖ ^ 2 := add_le_add h2 h1
      _ = (r + r') * ‖y‖ ^ 2 := by ring

/-- Symmetry of the perturbation relation. -/
theorem IsPerturbation.symm {k : ℕ} {r : ℝ} (h : IsPerturbation A A' k r) :
    IsPerturbation A' A k r := by
  obtain ⟨Y, hY, hr⟩ := h
  exact ⟨Y, hY, fun y hy => by rw [abs_sub_comm]; exact hr y hy⟩

/-- An operator-norm perturbation `‖(A' - A)x‖ ≤ r‖x‖` has rank zero and size `r`. -/
theorem isPerturbation_of_norm {r : ℝ}
    (h : ∀ x : EuclideanSpace ℂ ι, ‖T (A' - A) x‖ ≤ r * ‖x‖) : IsPerturbation A A' 0 r := by
  refine ⟨⊤, by rw [finrank_top, finrank_euclideanSpace]; omega, fun y _ => ?_⟩
  have e : RCLike.re ⟪y, T A' y⟫_ℂ - RCLike.re ⟪y, T A y⟫_ℂ = RCLike.re ⟪y, T (A' - A) y⟫_ℂ := by
    rw [map_sub, LinearMap.sub_apply, inner_sub_right, map_sub]
  rw [e]
  calc |RCLike.re ⟪y, T (A' - A) y⟫_ℂ| ≤ ‖⟪y, T (A' - A) y⟫_ℂ‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖y‖ * ‖T (A' - A) y‖ := norm_inner_le_norm _ _
    _ ≤ ‖y‖ * (r * ‖y‖) := mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)
    _ = r * ‖y‖ ^ 2 := by ring

/-- Exact agreement on a subspace of codimension `≤ k` is a perturbation of rank `k`, size `0`. -/
theorem isPerturbation_of_agree {k : ℕ} (Y : Submodule ℂ (EuclideanSpace ℂ ι))
    (hY : Fintype.card ι ≤ finrank ℂ Y + k) (h : ∀ y ∈ Y, T A' y = T A y) :
    IsPerturbation A A' k 0 :=
  ⟨Y, hY, fun y hy => by rw [h y hy]; simp⟩

end Perturbation

/-!
## Counts as spectral sums
-/

/-- `spectralSum` of an interval indicator counts the eigenvalues in the interval. -/
theorem spectralSum_Icc {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (a b : ℝ) :
    BlockBand.Internal.Contracts.Inputs.spectralSum A
        (fun l => if a ≤ l ∧ l ≤ b then 1 else 0) =
      ((univ.filter fun j => a ≤ hA.eigenvalues j ∧ hA.eigenvalues j ≤ b).card : ℝ) := by
  unfold BlockBand.Internal.Contracts.Inputs.spectralSum
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_map_val]
  simp [Finset.sum_boole]

/-- `spectralSum` of a general function, through Mathlib's eigenvalues. -/
theorem spectralSum_eq_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    BlockBand.Internal.Contracts.Inputs.spectralSum A f = ∑ j, f (hA.eigenvalues j) := by
  unfold BlockBand.Internal.Contracts.Inputs.spectralSum
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_map_val]
  simp

/-- **Window counts under perturbation**, spectral-sum form: for a perturbation of rank `k` and
size `r`, `N_A([-h, h]) ≤ N_{A'}([-(h+r), h+r]) + 2k`. -/
theorem window_count_le {A A' : Matrix ι ι ℂ} (hA : A.IsHermitian) (hA' : A'.IsHermitian)
    {k : ℕ} {r : ℝ} (h : IsPerturbation A A' k r) (w : ℝ) :
    BlockBand.Internal.Contracts.Inputs.spectralSum A (fun l => if |l| ≤ w then 1 else 0) ≤
      BlockBand.Internal.Contracts.Inputs.spectralSum A'
          (fun l => if |l| ≤ w + r then 1 else 0) + 2 * k := by
  have e : ∀ (u : ℝ) (B : Matrix ι ι ℂ),
      BlockBand.Internal.Contracts.Inputs.spectralSum B (fun l => if |l| ≤ u then 1 else 0) =
        BlockBand.Internal.Contracts.Inputs.spectralSum B
          (fun l => if -u ≤ l ∧ l ≤ u then 1 else 0) := by
    intro u B
    unfold BlockBand.Internal.Contracts.Inputs.spectralSum
    congr 2
    funext z
    simp only [abs_le]
  rw [e, e, spectralSum_Icc hA, spectralSum_Icc hA']
  have := card_Icc_le hA hA' h (-w) w
  rw [show -w - r = -(w + r) by ring] at this
  exact_mod_cast this

end BlockBand.LocalWindow.ProofCount
