module

public import BlockBand.Model.Construction.OrderedCourantFischer
public import BlockBand.Model.Construction.SpectralPhysical

/-!
# Deterministic spectral inputs of the pair pole exclusion lemma

* Courant–Fischer with dimension inequalities (`exists_ne_zero_re_inner_le`,
  `exists_ne_zero_le_re_inner`), built from the ordered Courant–Fischer library.
* Monotonicity: `eigenvalues₀` of `A + ζ P` is monotone in `ζ` for `P ⪰ 0`.
* Hellmann–Feynman lower bound (`eigenvalues_sub_smul_le`): if `ψ` is a unit
  eigenvector of `T` for its `k`-th (decreasing) eigenvalue and all lower eigenvalues lie at
  least `g > 0` below it, then for `0 < δ < g`,
  `λ_k(T - δ P) ≤ λ_k(T) - δ ⟨Pψ,ψ⟩ + δ²/g` for every `0 ⪯ P ⪯ I` satisfying the
  elementary weighted-parallelogram inequality (proved for real diagonal weights in `[0,1]`).
* Cauchy interlacing for a principal submatrix (`interlace_le`, `le_interlace`).
* A real root of `det(A - μ)` for Hermitian `A` is an eigenvalue (`exists_eigenvalue_of_det`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.PoleExclusion

open Matrix Module
open scoped InnerProductSpace ComplexConjugate

section CF

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T : E →ₗ[𝕜] E}

/-- Courant–Fischer, upper direction with a dimension inequality. -/
theorem exists_ne_zero_re_inner_le (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n)
    (V : Submodule 𝕜 E) (hV : (k : ℕ) + 1 ≤ finrank 𝕜 V) :
    ∃ x ∈ V, x ≠ 0 ∧ RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k * ‖x‖ ^ 2 := by
  set b := hT.eigenvectorBasis hn
  set W := b.spanIndices ↑(Finset.Ici k) with hW
  have hWdim : finrank 𝕜 W = n - (k : ℕ) := by
    rw [hW, b.finrank_spanIndices, Fin.card_Ici]
  have hk : (k : ℕ) < n := k.2
  have hinf : V ⊓ W ≠ ⊥ := Submodule.inf_ne_bot_of_finrank_lt (by rw [hn, hWdim]; omega)
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨hzV, hzW⟩ := Submodule.mem_inf.mp hz
  exact ⟨z, hzV, hz0, hT.re_inner_apply_self_le_of_mem_spanIndices hn
    (fun _ hik => hT.eigenvalues_antitone hn (by simpa using hik)) hzW⟩

/-- Courant–Fischer, lower direction with a dimension inequality. -/
theorem exists_ne_zero_le_re_inner (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n)
    (V : Submodule 𝕜 E) (hV : n ≤ finrank 𝕜 V + (k : ℕ)) :
    ∃ x ∈ V, x ≠ 0 ∧ hT.eigenvalues hn k * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  set b := hT.eigenvectorBasis hn
  set W := b.spanIndices ↑(Finset.Iic k) with hW
  have hWdim : finrank 𝕜 W = (k : ℕ) + 1 := by
    rw [hW, b.finrank_spanIndices, Fin.card_Iic]
  have hinf : V ⊓ W ≠ ⊥ := Submodule.inf_ne_bot_of_finrank_lt (by rw [hn, hWdim]; omega)
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨hzV, hzW⟩ := Submodule.mem_inf.mp hz
  exact ⟨z, hzV, hz0, hT.le_re_inner_apply_self_of_mem_spanIndices hn
    (fun _ hik => hT.eigenvalues_antitone hn (by simpa using hik)) hzW⟩

end CF

section HF

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {n : ℕ}

theorem re_ofReal_mul' (r : ℝ) (z : ℂ) : RCLike.re ((r : ℂ) * z) = r * RCLike.re z :=
  Complex.re_ofReal_mul r z

omit [FiniteDimensional ℂ E] in
/-- Quadratic forms are quadratic under scalars. -/
theorem re_inner_smul_smul (P : E →ₗ[ℂ] E) (c : ℂ) (x : E) :
    RCLike.re ⟪P (c • x), c • x⟫_ℂ = ‖c‖ ^ 2 * RCLike.re ⟪P x, x⟫_ℂ := by
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc]
  have : (starRingEnd ℂ) c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [this, re_ofReal_mul']

/-- **Hellmann–Feynman lower bound** (one-sided quantitative form). Let `ψ` be a unit eigenvector of the
symmetric `T` for its `k`-th decreasing eigenvalue `λ`, with every lower eigenvalue
`λ_j` (`j > k`) at most `λ - g`, `g > 0`. Let `P` satisfy `0 ≤ ⟨Px,x⟩ ≤ ‖x‖²` and the weighted
parallelogram inequality `hPpar`. Then for `0 < δ < g`,
`λ_k(T - δ P) ≤ λ - δ ⟨Pψ,ψ⟩ + δ²/g`. -/
theorem eigenvalues_sub_smul_le {T P : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {δ : ℝ}
    (hS : (T - (δ : ℂ) • P).IsSymmetric) (hn : finrank ℂ E = n) (k : Fin n)
    (ψ : E) (hψ : ‖ψ‖ = 1) (hTψ : T ψ = (hT.eigenvalues hn k : ℂ) • ψ)
    {g : ℝ} (hg : 0 < g) (hgap : ∀ j, k < j → hT.eigenvalues hn j ≤ hT.eigenvalues hn k - g)
    (hP0 : ∀ x, 0 ≤ RCLike.re ⟪P x, x⟫_ℂ) (hP1 : ∀ x, RCLike.re ⟪P x, x⟫_ℂ ≤ ‖x‖ ^ 2)
    (hPpar : ∀ x y, δ * (g - δ) * RCLike.re ⟪P x, x⟫_ℂ - g * (g - δ) * RCLike.re ⟪P y, y⟫_ℂ ≤
      g * δ * RCLike.re ⟪P (x + y), x + y⟫_ℂ)
    (hδ : 0 < δ) (hδg : δ < g) :
    hS.eigenvalues hn k ≤ hT.eigenvalues hn k - δ * RCLike.re ⟪P ψ, ψ⟫_ℂ + δ ^ 2 / g := by
  set lam := hT.eigenvalues hn k with hlam
  set b := hT.eigenvectorBasis hn with hb
  set Wl := b.spanIndices ↑(Finset.Ioi k) with hWl
  have hψ0 : ψ ≠ 0 := by
    intro h; rw [h, norm_zero] at hψ; exact zero_ne_one hψ
  -- `ψ` is orthogonal to the lower eigenvectors.
  have hbj : ∀ j ∈ (↑(Finset.Ioi k) : Set (Fin n)), ⟪ψ, b j⟫_ℂ = 0 := by
    intro j hj
    have hkj : k < j := by simpa using hj
    have h1 : ⟪T ψ, b j⟫_ℂ = ⟪ψ, T (b j)⟫_ℂ := hT ψ (b j)
    have hbj' : T (b j) = (hT.eigenvalues hn j : ℂ) • b j := hT.apply_eigenvectorBasis hn j
    rw [hTψ, hbj', inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
    have h2 : ((lam - hT.eigenvalues hn j : ℝ) : ℂ) * ⟪ψ, b j⟫_ℂ = 0 := by
      push_cast; rw [sub_mul, h1, sub_self]
    have h3 : ((lam - hT.eigenvalues hn j : ℝ) : ℂ) ≠ 0 := by
      have := hgap j hkj
      exact_mod_cast (show lam - hT.eigenvalues hn j ≠ 0 by linarith)
    exact (mul_eq_zero.mp h2).resolve_left h3
  have horth : ∀ w ∈ Wl, ⟪ψ, w⟫_ℂ = 0 := by
    intro w hw
    rw [hWl, b.spanIndices_eq_span] at hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro y ⟨j, hj, rfl⟩; exact hbj j hj
    · exact inner_zero_right _
    · intro y z _ _ hy hz; rw [inner_add_right, hy, hz, add_zero]
    · intro a y _ hy; rw [inner_smul_right, hy, mul_zero]
  -- Dimension of `V = ℂψ ⊔ Wl`.
  set V := (ℂ ∙ ψ) ⊔ Wl with hV
  have hinf : (ℂ ∙ ψ) ⊓ Wl = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz1
    have h := horth _ hz2
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hψ] at h
    simp at h
    simp [h]
  have hWldim : finrank ℂ Wl = n - 1 - (k : ℕ) := by
    rw [hWl, b.finrank_spanIndices, Fin.card_Ioi]
  have hVdim : n ≤ finrank ℂ V + (k : ℕ) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (ℂ ∙ ψ) Wl
    rw [hinf, finrank_bot, finrank_span_singleton hψ0, hWldim] at h
    have hk : (k : ℕ) < n := k.2
    rw [hV]; omega
  obtain ⟨x, hxV, hx0, hlow⟩ := exists_ne_zero_le_re_inner hS hn k V hVdim
  obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.mp hxV
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
  -- Orthogonality and the eigen-relation on the `ψ` component.
  have haw : ⟪c • ψ, w⟫_ℂ = 0 := by rw [inner_smul_left, horth w hw, mul_zero]
  have hwa : ⟪w, c • ψ⟫_ℂ = 0 := by rw [← inner_conj_symm, haw, map_zero]
  have hTa : T (c • ψ) = (lam : ℂ) • (c • ψ) := by
    rw [map_smul, hTψ, smul_comm]
  have hnorm : ‖c • ψ + w‖ ^ 2 = ‖c‖ ^ 2 + ‖w‖ ^ 2 := by
    rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ haw, norm_smul, hψ, mul_one,
      sq, sq]
  have hTx : RCLike.re ⟪T (c • ψ + w), c • ψ + w⟫_ℂ ≤ lam * ‖c‖ ^ 2 + (lam - g) * ‖w‖ ^ 2 := by
    have hTw : RCLike.re ⟪T w, w⟫_ℂ ≤ (lam - g) * ‖w‖ ^ 2 :=
      hT.re_inner_apply_self_le_of_mem_spanIndices hn
        (fun j hj => hgap j (by simpa using hj)) hw
    have hcross : ⟪T w, c • ψ⟫_ℂ = 0 := by
      rw [hT w (c • ψ), hTa, inner_smul_right, hwa, mul_zero]
    have haa : RCLike.re ⟪T (c • ψ), c • ψ⟫_ℂ = lam * ‖c‖ ^ 2 := by
      rw [hTa, inner_smul_left, Complex.conj_ofReal, re_ofReal_mul',
        inner_self_eq_norm_sq_to_K, norm_smul, hψ, mul_one]
      norm_cast
    have hexp : ⟪T (c • ψ + w), c • ψ + w⟫_ℂ = ⟪T (c • ψ), c • ψ⟫_ℂ + ⟪T (c • ψ), w⟫_ℂ +
        ⟪T w, c • ψ⟫_ℂ + ⟪T w, w⟫_ℂ := by
      rw [map_add, inner_add_left, inner_add_right, inner_add_right]; ring
    have hTaw : ⟪T (c • ψ), w⟫_ℂ = 0 := by rw [hTa, inner_smul_left, haw, mul_zero]
    rw [hexp, hTaw, hcross, add_zero, add_zero, map_add, haa]
    linarith
  have hSx : RCLike.re ⟪(T - (δ : ℂ) • P) (c • ψ + w), c • ψ + w⟫_ℂ =
      RCLike.re ⟪T (c • ψ + w), c • ψ + w⟫_ℂ - δ * RCLike.re ⟪P (c • ψ + w), c • ψ + w⟫_ℂ := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, inner_sub_left, inner_smul_left,
      Complex.conj_ofReal, map_sub, re_ofReal_mul']
  set m := RCLike.re ⟪P ψ, ψ⟫_ℂ with hm
  have hm0 : 0 ≤ m := hP0 ψ
  have hm1 : m ≤ 1 := by have := hP1 ψ; rw [hψ, one_pow] at this; exact this
  have hPa : RCLike.re ⟪P (c • ψ), c • ψ⟫_ℂ = ‖c‖ ^ 2 * m := re_inner_smul_smul P c ψ
  have hpar := hPpar (c • ψ) w
  have hw1 := hP1 w
  have hw0 := hP0 w
  rw [hPa] at hpar
  set A2 := ‖c‖ ^ 2 with hA2
  set W2 := ‖w‖ ^ 2 with hW2
  set lS := hS.eigenvalues hn k with hlS
  set qx := RCLike.re ⟪P (c • ψ + w), c • ψ + w⟫_ℂ with hqx
  have hpos : 0 < A2 + W2 := by
    rw [← hnorm]; exact pow_pos (norm_pos_iff.mpr hx0) 2
  rw [hnorm, hSx] at hlow
  have hA0 : 0 ≤ A2 := sq_nonneg _
  have hW0 : 0 ≤ W2 := sq_nonneg _
  -- Clear the denominator `g`.
  have key : g * (lS * (A2 + W2)) ≤ (g * lam - g * δ * m + δ ^ 2) * (A2 + W2) := by
    have h1 : g * (lS * (A2 + W2)) ≤ g * (lam * A2 + (lam - g) * W2) - g * δ * qx := by
      nlinarith
    have h2 : g * δ * qx ≥ δ * (g - δ) * (A2 * m) - g * (g - δ) * W2 := by
      nlinarith [mul_le_mul_of_nonneg_left hw1 (mul_nonneg hg.le (sub_nonneg.mpr hδg.le))]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hm1)) hA0,
      mul_nonneg (mul_nonneg (mul_nonneg hg.le hδ.le) (sub_nonneg.mpr hm1)) hW0,
      mul_nonneg (sq_nonneg δ) hW0]
  have key2 : lS * (g * (A2 + W2)) ≤ (lam - δ * m + δ ^ 2 / g) * (g * (A2 + W2)) := by
    have : (lam - δ * m + δ ^ 2 / g) * (g * (A2 + W2)) =
        (g * lam - g * δ * m + δ ^ 2) * (A2 + W2) := by
      field_simp
    rw [this]; linarith
  exact le_of_mul_le_mul_right key2 (mul_pos hg hpos)

end HF

section MatrixForms

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The symmetric operator of a Hermitian matrix. -/
theorem isSymm (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : (toEuclideanLin A).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.mpr hA

theorem eigenvalues₀_eq (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (k : Fin (Fintype.card ι)) :
    hA.eigenvalues₀ k = (isSymm A hA).eigenvalues finrank_euclideanSpace k := rfl

theorem inner_toEuclideanLin (A : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    ⟪toEuclideanLin A x, x⟫_ℂ = ∑ y, x.ofLp y * star ((A *ᵥ x.ofLp) y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct]

/-- Quadratic form of a real diagonal matrix. -/
theorem re_inner_diagonal (w : ι → ℝ) (x : EuclideanSpace ℂ ι) :
    RCLike.re ⟪toEuclideanLin (diagonal fun y => (w y : ℂ)) x, x⟫_ℂ =
      ∑ y, w y * ‖x.ofLp y‖ ^ 2 := by
  rw [inner_toEuclideanLin]
  simp only [mulVec_diagonal, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [star_mul', Complex.star_def, Complex.conj_ofReal, mul_left_comm, ← Complex.star_def,
    Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  rfl

theorem re_inner_add_smul (A P : Matrix ι ι ℂ) (ζ : ℝ) (x : EuclideanSpace ℂ ι) :
    RCLike.re ⟪toEuclideanLin (A + (ζ : ℂ) • P) x, x⟫_ℂ =
      RCLike.re ⟪toEuclideanLin A x, x⟫_ℂ + ζ * RCLike.re ⟪toEuclideanLin P x, x⟫_ℂ := by
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left,
    inner_smul_left, Complex.conj_ofReal, map_add, re_ofReal_mul']

/-- The scalar weighted-parallelogram inequality
`δ(g-δ)|a|² - g(g-δ)|b|² ≤ gδ|a+b|²` (it equals `|δ a + g b|² ≥ 0`). -/
theorem scalar_par (δ g : ℝ) (a b : ℂ) :
    δ * (g - δ) * ‖a‖ ^ 2 - g * (g - δ) * ‖b‖ ^ 2 ≤ g * δ * ‖a + b‖ ^ 2 := by
  have h := Complex.normSq_nonneg ((δ : ℂ) * a + (g : ℂ) * b)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  rw [Complex.normSq_apply] at h ⊢
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero] at h ⊢
  nlinarith [h]

theorem diag_nonneg (w : ι → ℝ) (hw0 : ∀ y, 0 ≤ w y) (x : EuclideanSpace ℂ ι) :
    0 ≤ RCLike.re ⟪toEuclideanLin (diagonal fun y => (w y : ℂ)) x, x⟫_ℂ := by
  rw [re_inner_diagonal]
  exact Finset.sum_nonneg fun y _ => mul_nonneg (hw0 y) (sq_nonneg _)

theorem diag_le (w : ι → ℝ) (hw1 : ∀ y, w y ≤ 1) (x : EuclideanSpace ℂ ι) :
    RCLike.re ⟪toEuclideanLin (diagonal fun y => (w y : ℂ)) x, x⟫_ℂ ≤ ‖x‖ ^ 2 := by
  rw [re_inner_diagonal, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg
    fun y _ => sq_nonneg _)]
  exact Finset.sum_le_sum fun y _ => mul_le_of_le_one_left (sq_nonneg _) (hw1 y)

theorem diag_par (w : ι → ℝ) (hw0 : ∀ y, 0 ≤ w y) (δ g : ℝ) (x y : EuclideanSpace ℂ ι) :
    δ * (g - δ) * RCLike.re ⟪toEuclideanLin (diagonal fun y => (w y : ℂ)) x, x⟫_ℂ -
        g * (g - δ) * RCLike.re ⟪toEuclideanLin (diagonal fun y => (w y : ℂ)) y, y⟫_ℂ ≤
      g * δ * RCLike.re ⟪toEuclideanLin (diagonal fun y => (w y : ℂ)) (x + y), x + y⟫_ℂ := by
  rw [re_inner_diagonal, re_inner_diagonal, re_inner_diagonal, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun z _ => ?_
  have h := scalar_par δ g (x.ofLp z) (y.ofLp z)
  have hz := hw0 z
  simp only [WithLp.ofLp_add, Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left h hz]

end MatrixForms

section MatrixSpectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open BlockBand.Model.Construction BlockBand.Foundations.Spectral

theorem rawInc_eq (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (r : Fin (Fintype.card ι)) :
    rawIncreasingEigenvalue r A = hA.eigenvalues₀ r.rev := by
  rw [rawIncreasingEigenvalue_eq _ A hA]; rfl

omit [Fintype ι] in
theorem diag_isHermitian (w : ι → ℝ) : (diagonal fun y => (w y : ℂ)).IsHermitian := by
  rw [Matrix.IsHermitian, diagonal_conjTranspose]
  congr 1; funext y; simp

omit [Fintype ι] [DecidableEq ι] in
theorem herm_add_smul {A P : Matrix ι ι ℂ} (hA : A.IsHermitian) (hP : P.IsHermitian) (ζ : ℝ) :
    (A + (ζ : ℂ) • P).IsHermitian :=
  hA.add (hP.smul (Complex.conj_ofReal ζ))

omit [Fintype ι] [DecidableEq ι] in
theorem herm_sub_smul {A P : Matrix ι ι ℂ} (hA : A.IsHermitian) (hP : P.IsHermitian) (ζ : ℝ) :
    (A - (ζ : ℂ) • P).IsHermitian :=
  hA.sub (hP.smul (Complex.conj_ofReal ζ))

/-- Monotonicity: ordered eigenvalues of `A + ζ diag(w)`, `w ≥ 0`, are nondecreasing
in `ζ`. -/
theorem rawInc_mono {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (w : ι → ℝ) (hw0 : ∀ y, 0 ≤ w y)
    (r : Fin (Fintype.card ι)) :
    Monotone (fun ζ : ℝ => rawIncreasingEigenvalue r (A + (ζ : ℂ) • diagonal fun y => (w y : ℂ))) := by
  intro ζ ζ' h
  have h1 := herm_add_smul hA (diag_isHermitian w) ζ
  have h2 := herm_add_smul hA (diag_isHermitian w) ζ'
  simp only
  rw [rawInc_eq _ h1, rawInc_eq _ h2, eigenvalues₀_eq, eigenvalues₀_eq]
  apply LinearMap.IsSymmetric.eigenvalue_mono
  intro x
  rw [re_inner_add_smul, re_inner_add_smul]
  have := diag_nonneg w hw0 x
  have hζ : 0 ≤ ζ' - ζ := sub_nonneg.mpr h
  nlinarith

/-- Separable characteristic polynomial gives injective sorted eigenvalues. -/
theorem eigenvalues₀_injective {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hsep : A.charpoly.Separable) : Function.Injective hA.eigenvalues₀ := by
  have heigC : Function.Injective (fun x => (hA.eigenvalues x : ℂ)) := by
    rw [hA.charpoly_eq, Polynomial.separable_prod_X_sub_C_iff] at hsep
    exact hsep
  intro a b hab
  have : hA.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin _) a) =
      hA.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin _) b) := by
    simp [Matrix.IsHermitian.eigenvalues, hab]
  exact (Fintype.equivOfCardEq (Fintype.card_fin _)).injective
    (heigC (congrArg (fun t : ℝ => (t : ℂ)) this))

/-- Hellmann–Feynman, quantitative left-difference bound at a matrix with separable
characteristic polynomial: for a unit eigenvector `ψ` of rank `r` and real weights in `[0,1]`,
there is a gap `g > 0` with
`λ_r(A - δ diag(w)) ≤ λ_r(A) - δ Σ_y w_y |ψ_y|² + δ²/g` for `0 < δ < g`. -/
theorem rawInc_hf {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (hsep : A.charpoly.Separable)
    (w : ι → ℝ) (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∀ y, w y ≤ 1) (r : Fin (Fintype.card ι))
    (ψ : ι → ℂ) (hψ : A *ᵥ ψ = (rawIncreasingEigenvalue r A : ℂ) • ψ)
    (hnorm : ∑ y, ‖ψ y‖ ^ 2 = 1) :
    ∃ g > 0, ∀ δ : ℝ, 0 < δ → δ < g →
      rawIncreasingEigenvalue r (A - (δ : ℂ) • diagonal fun y => (w y : ℂ)) ≤
        rawIncreasingEigenvalue r A - δ * ∑ y, w y * ‖ψ y‖ ^ 2 + δ ^ 2 / g := by
  set k : Fin (Fintype.card ι) := r.rev with hk
  set lam := hA.eigenvalues₀ with hlam
  have hinj := eigenvalues₀_injective hA hsep
  have hanti : Antitone lam := hA.eigenvalues₀_antitone
  set g : ℝ := if h : (k : ℕ) + 1 < Fintype.card ι then lam k - lam ⟨(k : ℕ) + 1, h⟩ else 1 with hg
  have hgpos : 0 < g := by
    rw [hg]
    split_ifs with h
    · have hle : lam ⟨(k : ℕ) + 1, h⟩ ≤ lam k := hanti (by rw [Fin.le_def]; exact Nat.le_succ _)
      have hne : lam ⟨(k : ℕ) + 1, h⟩ ≠ lam k := by
        intro he; have := hinj he; rw [Fin.ext_iff] at this; simp at this
      exact sub_pos.mpr (lt_of_le_of_ne hle hne)
    · exact one_pos
  have hgap : ∀ j : Fin (Fintype.card ι), k < j → lam j ≤ lam k - g := by
    intro j hj
    have h : (k : ℕ) + 1 < Fintype.card ι := by have := j.2; rw [Fin.lt_def] at hj; omega
    have hg' : g = lam k - lam ⟨(k : ℕ) + 1, h⟩ := by simp only [hg, h, dite_true]
    have : lam j ≤ lam ⟨(k : ℕ) + 1, h⟩ := hanti (by
      rw [Fin.le_def]; rw [Fin.lt_def] at hj; exact hj)
    linarith
  refine ⟨g, hgpos, fun δ hδ hδg => ?_⟩
  set D : Matrix ι ι ℂ := diagonal fun y => (w y : ℂ) with hD
  have hDh : D.IsHermitian := diag_isHermitian w
  have hsub := herm_sub_smul hA hDh δ
  have hEq : toEuclideanLin (A - (δ : ℂ) • D) = toEuclideanLin A - (δ : ℂ) • toEuclideanLin D := by
    rw [map_sub, map_smul]
  have hS : (toEuclideanLin A - (δ : ℂ) • toEuclideanLin D).IsSymmetric := hEq ▸ isSymm _ hsub
  set ψ' : EuclideanSpace ℂ ι := WithLp.toLp 2 ψ with hψ'
  have hnorm' : ‖ψ'‖ = 1 := by
    rw [EuclideanSpace.norm_eq]; simp [hψ', hnorm]
  have hTψ : toEuclideanLin A ψ' =
      ((isSymm A hA).eigenvalues finrank_euclideanSpace k : ℂ) • ψ' := by
    have h1 : rawIncreasingEigenvalue r A = (isSymm A hA).eigenvalues finrank_euclideanSpace k := by
      rw [rawInc_eq _ hA]; rfl
    rw [← h1]
    ext y
    simp [hψ', hψ]
  have key := eigenvalues_sub_smul_le (isSymm A hA) hS finrank_euclideanSpace k ψ' hnorm' hTψ
    hgpos (fun j hj => hgap j hj) (diag_nonneg w hw0) (diag_le w hw1)
    (fun x y => diag_par w hw0 δ g x y) hδ hδg
  have hcongr := LinearMap.IsSymmetric.eigenvalues_congr hEq (isSymm _ hsub) hS
    (finrank_euclideanSpace (𝕜 := ℂ) (ι := ι))
  rw [rawInc_eq _ hsub, rawInc_eq _ hA, eigenvalues₀_eq, eigenvalues₀_eq, hcongr]
  have hm : RCLike.re ⟪toEuclideanLin D ψ', ψ'⟫_ℂ = ∑ y, w y * ‖ψ y‖ ^ 2 := by
    rw [hD, re_inner_diagonal]
  rw [← hm]
  exact key

end MatrixSpectral

section Interlace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → Prop) [DecidablePred r]

/-- Extension by zero `ℂ^R → ℂ^ι` for `R = {x // r x}`. -/
def extendZero : EuclideanSpace ℂ {x // r x} →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun u := WithLp.toLp 2 (fun y => if h : r y then u.ofLp ⟨y, h⟩ else 0)
  map_add' u v := by
    ext y; by_cases h : r y <;> simp [h]
  map_smul' c u := by
    ext y; by_cases h : r y <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
theorem extendZero_apply (u : EuclideanSpace ℂ {x // r x}) (y : ι) :
    (extendZero r u).ofLp y = if h : r y then u.ofLp ⟨y, h⟩ else 0 := rfl

omit [DecidableEq ι] in
theorem sum_extend {M : Type*} [AddCommMonoid M] (f : ι → M) (hf : ∀ y, ¬ r y → f y = 0) :
    ∑ y, f y = ∑ y : {x // r x}, f y.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype r f]
  rw [Finset.sum_eq_zero (s := (Finset.univ : Finset {x // ¬ r x})) (fun y _ => hf y.1 y.2),
    add_zero]

omit [DecidableEq ι] in
theorem norm_extendZero (u : EuclideanSpace ℂ {x // r x}) : ‖extendZero r u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  rw [sum_extend r (fun y => ‖(extendZero r u).ofLp y‖ ^ 2) (fun y hy => by
    simp [extendZero_apply, hy])]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [extendZero_apply, y.2]

omit [DecidableEq ι] in
theorem extendZero_injective : Function.Injective (extendZero r) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro u hu
  rw [LinearMap.mem_ker] at hu
  have h := norm_extendZero r u
  rw [hu, norm_zero] at h
  exact norm_eq_zero.mp h.symm

theorem inner_extendZero (H : Matrix ι ι ℂ) (u : EuclideanSpace ℂ {x // r x}) :
    ⟪toEuclideanLin H (extendZero r u), extendZero r u⟫_ℂ =
      ⟪toEuclideanLin (H.submatrix Subtype.val Subtype.val) u, u⟫_ℂ := by
  rw [inner_toEuclideanLin, inner_toEuclideanLin]
  rw [sum_extend r _ (fun y hy => by simp [extendZero_apply, hy])]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 2
  · simp [extendZero_apply, y.2]
  · simp only [mulVec, dotProduct, submatrix_apply]
    rw [sum_extend r _ (fun z hz => by simp [extendZero_apply, hz])]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp [extendZero_apply, z.2]

variable {r}

/-- **Cauchy interlacing, first half** (decreasing enumeration): the `k`-th eigenvalue of the
principal submatrix is at most the `k`-th eigenvalue of the matrix. -/
theorem interlace_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hB : (H.submatrix (Subtype.val : {x // r x} → ι) Subtype.val).IsHermitian)
    (k : Fin (Fintype.card {x // r x})) (k' : Fin (Fintype.card ι)) (hkk : (k : ℕ) = k') :
    hB.eigenvalues₀ k ≤ hH.eigenvalues₀ k' := by
  set B := H.submatrix (Subtype.val : {x // r x} → ι) Subtype.val
  set hTB := isSymm B hB
  set bB := hTB.eigenvectorBasis finrank_euclideanSpace
  set WR := bB.spanIndices ↑(Finset.Iic k) with hWR
  have hWRdim : finrank ℂ WR = (k : ℕ) + 1 := by rw [hWR, bB.finrank_spanIndices, Fin.card_Iic]
  set V := WR.map (extendZero r) with hV
  have hVdim : finrank ℂ V = (k : ℕ) + 1 := by
    rw [hV, ← hWRdim]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (extendZero_injective r) WR)).symm
  obtain ⟨x, hxV, hx0, hle⟩ := exists_ne_zero_re_inner_le (isSymm H hH) finrank_euclideanSpace k' V
    (by rw [hVdim, hkk])
  obtain ⟨u, huW, rfl⟩ := Submodule.mem_map.mp hxV
  have hu0 : u ≠ 0 := by rintro rfl; exact hx0 (map_zero _)
  have hlow : hB.eigenvalues₀ k * ‖u‖ ^ 2 ≤ RCLike.re ⟪toEuclideanLin B u, u⟫_ℂ :=
    hTB.le_re_inner_apply_self_of_mem_spanIndices finrank_euclideanSpace
      (fun _ hik => hTB.eigenvalues_antitone finrank_euclideanSpace (by simpa using hik)) huW
  rw [inner_extendZero, norm_extendZero] at hle
  have hpos : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu0) 2
  exact le_of_mul_le_mul_right (hlow.trans hle) hpos

/-- **Cauchy interlacing, second half** (decreasing enumeration): the `(k + d)`-th eigenvalue of
the matrix is at most the `k`-th eigenvalue of the principal submatrix, `d` the codimension. -/
theorem le_interlace {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hB : (H.submatrix (Subtype.val : {x // r x} → ι) Subtype.val).IsHermitian)
    (k : Fin (Fintype.card {x // r x})) (k' : Fin (Fintype.card ι))
    (hkk : (k' : ℕ) = k + (Fintype.card ι - Fintype.card {x // r x})) :
    hH.eigenvalues₀ k' ≤ hB.eigenvalues₀ k := by
  set B := H.submatrix (Subtype.val : {x // r x} → ι) Subtype.val
  set hTB := isSymm B hB
  set bB := hTB.eigenvectorBasis finrank_euclideanSpace
  set WR := bB.spanIndices ↑(Finset.Ici k) with hWR
  have hWRdim : finrank ℂ WR = Fintype.card {x // r x} - (k : ℕ) := by
    rw [hWR, bB.finrank_spanIndices, Fin.card_Ici]
  set V := WR.map (extendZero r) with hV
  have hVdim : finrank ℂ V = Fintype.card {x // r x} - (k : ℕ) := by
    rw [hV, ← hWRdim]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (extendZero_injective r) WR)).symm
  have hcard : Fintype.card {x // r x} ≤ Fintype.card ι := Fintype.card_subtype_le r
  have hk := k.2
  obtain ⟨x, hxV, hx0, hle⟩ := exists_ne_zero_le_re_inner (isSymm H hH) finrank_euclideanSpace k' V
    (by rw [hVdim, hkk]; omega)
  obtain ⟨u, huW, rfl⟩ := Submodule.mem_map.mp hxV
  have hu0 : u ≠ 0 := by rintro rfl; exact hx0 (map_zero _)
  have hup : RCLike.re ⟪toEuclideanLin B u, u⟫_ℂ ≤ hB.eigenvalues₀ k * ‖u‖ ^ 2 :=
    hTB.re_inner_apply_self_le_of_mem_spanIndices finrank_euclideanSpace
      (fun _ hik => hTB.eigenvalues_antitone finrank_euclideanSpace (by simpa using hik)) huW
  rw [inner_extendZero, norm_extendZero] at hle
  have hpos : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu0) 2
  exact le_of_mul_le_mul_right (hle.trans hup) hpos

end Interlace

section Root

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open BlockBand.Model.Construction

/-- A real root of `det(A - μ)` for Hermitian `A` is a sorted eigenvalue. -/
theorem exists_eigenvalue_of_det {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (μ : ℝ)
    (hdet : (A - (μ : ℂ) • 1).det = 0) :
    ∃ k : Fin (Fintype.card ι), rawIncreasingEigenvalue k A = μ := by
  have h1 : Polynomial.eval (μ : ℂ) A.charpoly = 0 := by
    rw [eval_charpoly]
    have : (scalar ι (μ : ℂ)) - A = -(A - (μ : ℂ) • 1) := by
      rw [neg_sub, scalar_apply, smul_one_eq_diagonal]
    rw [this, det_neg, hdet, mul_zero]
  rw [hA.charpoly_eq, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h1
  obtain ⟨j, _, hj⟩ := h1
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hj
  have hj' : μ = hA.eigenvalues j := RCLike.ofReal_injective (K := ℂ) hj
  refine ⟨((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j).rev, ?_⟩
  rw [rawInc_eq _ hA, Fin.rev_rev, hj']
  rfl

end Root

end BlockBand.Coarea.PoleExclusion
