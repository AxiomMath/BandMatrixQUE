module

public import BlockBand.Model.Construction.SpectralPhysical
public import BlockBand.Model.Construction.OrderedEigenvalues

/-!
# Hellmann–Feynman along a positive line

* §1 (abstract, a symmetric family `T + x S` on a finite-dimensional complex inner product
  space with `‖S x‖ ≤ ‖x‖`): the spectral gap estimate `cib_gap`; every eigenvector of a simple
  eigenvalue is a multiple of the basis vector (`cib_eq_smul_of_eigen`); Weyl's bound
  `|λ_k(x) - λ_k(y)| ≤ |x - y|` (`cib_eig_lipschitz`); monotonicity for `S ≥ 0`
  (`cib_eig_monotone`); and **Hellmann–Feynman** `cib_hasDerivAt_eig`: at a parameter where the
  `k`-th eigenvalue is simple, `x ↦ λ_k(T + x S)` is differentiable with derivative
  `⟪S v, v⟫` for every unit eigenvector `v` (no simplicity is needed elsewhere on the line).
* §2 (matrices): the same for `x ↦ λ_α(A + x D)` with `A` Hermitian and `D` a real diagonal
  matrix with entries in `[0, 1]`, at a parameter where `A + x D` has separable characteristic
  polynomial; the derivative is the `D`-weighted mass of the selected eigenvector
  (`cib_matrix_hasDerivAt`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open Module (finrank)
open scoped InnerProductSpace Topology ComplexConjugate

/-!
## 1. Abstract symmetric families
-/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {n : ℕ}

/-- A finite family of reals all different from `μ k` stays a positive distance away. -/
theorem cib_exists_gap (μ : Fin n → ℝ) (k : Fin n) (h : ∀ j, j ≠ k → μ j ≠ μ k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j, j ≠ k → δ ≤ |μ j - μ k| := by
  classical
  set s := Finset.univ.filter (fun j : Fin n => j ≠ k) with hs
  by_cases hne : s.Nonempty
  · obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_min_image s (fun j => |μ j - μ k|) hne
    have hj₀' : j₀ ≠ k := (Finset.mem_filter.mp hj₀).2
    refine ⟨|μ j₀ - μ k|, abs_pos.mpr (sub_ne_zero.mpr (h j₀ hj₀')), fun j hj => ?_⟩
    exact hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  · refine ⟨1, one_pos, fun j hj => ?_⟩
    exact absurd ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩ hne

/-- **Spectral gap estimate**: if every other eigenvalue is at distance `≥ δ` from `μ_k`, then
`δ ‖w‖ ≤ ‖(T - μ_k) w‖` for every `w` orthogonal to the `k`-th basis eigenvector. -/
theorem cib_gap {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (k : Fin n) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : ∀ j, j ≠ k → δ ≤ |hT.eigenvalues hn j - hT.eigenvalues hn k|) (w : E)
    (hw : ⟪hT.eigenvectorBasis hn k, w⟫_ℂ = 0) :
    δ * ‖w‖ ≤ ‖T w - ((hT.eigenvalues hn k : ℝ) : ℂ) • w‖ := by
  set b := hT.eigenvectorBasis hn with hb
  set μ := hT.eigenvalues hn with hμ
  have happ : ∀ j, T (b j) = ((μ j : ℝ) : ℂ) • b j := fun j => hT.apply_eigenvectorBasis hn j
  have hcoef : ∀ j, ⟪b j, T w - ((μ k : ℝ) : ℂ) • w⟫_ℂ = ((μ j - μ k : ℝ) : ℂ) * ⟪b j, w⟫_ℂ := by
    intro j
    rw [inner_sub_right, inner_smul_right, ← hT (b j) w, happ, inner_smul_left, Complex.conj_ofReal]
    push_cast
    ring
  have h1 := b.sum_sq_norm_inner_right (T w - ((μ k : ℝ) : ℂ) • w)
  have h2 := b.sum_sq_norm_inner_right w
  have hsq : (δ * ‖w‖) ^ 2 ≤ ‖T w - ((μ k : ℝ) : ℂ) • w‖ ^ 2 := by
    rw [← h1, mul_pow, ← h2, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hcoef j, norm_mul, mul_pow]
    by_cases hj : j = k
    · subst hj
      rw [hw]
      simp
    · gcongr
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hδ j hj
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hsq

/-- At a simple eigenvalue every eigenvector is a multiple of the basis eigenvector. -/
theorem cib_eq_smul_of_eigen {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : finrank ℂ E = n)
    (k : Fin n) (hsimple : ∀ j, j ≠ k → hT.eigenvalues hn j ≠ hT.eigenvalues hn k) (v : E)
    (hv : T v = ((hT.eigenvalues hn k : ℝ) : ℂ) • v) :
    v = ⟪hT.eigenvectorBasis hn k, v⟫_ℂ • hT.eigenvectorBasis hn k := by
  set b := hT.eigenvectorBasis hn with hb
  set μ := hT.eigenvalues hn with hμ
  have happ : ∀ j, T (b j) = ((μ j : ℝ) : ℂ) • b j := fun j => hT.apply_eigenvectorBasis hn j
  obtain ⟨δ, hδ, hgap⟩ := cib_exists_gap μ k hsimple
  set w := v - ⟪b k, v⟫_ℂ • b k with hw
  have hbk : ⟪b k, b k⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
    simp
  have hperp : ⟪b k, w⟫_ℂ = 0 := by
    rw [hw, inner_sub_right, inner_smul_right, hbk, mul_one, sub_self]
  have hTw : T w - ((μ k : ℝ) : ℂ) • w = 0 := by
    rw [hw, map_sub, map_smul, hv, happ, smul_sub, smul_comm]
    abel
  have h := cib_gap hT hn k hδ.le hgap w hperp
  rw [hTw, norm_zero] at h
  have hw0 : ‖w‖ = 0 := le_antisymm (by nlinarith [norm_nonneg w]) (norm_nonneg w)
  rw [norm_eq_zero, hw, sub_eq_zero] at hw0
  exact hw0

variable {T S : E →ₗ[ℂ] E}

/-- **Weyl's bound along the line**: `|λ_k(T + xS) - λ_k(T + yS)| ≤ |x - y|` when
`‖S v‖ ≤ ‖v‖`. -/
theorem cib_eig_lipschitz (hL : ∀ x : ℝ, (T + (x : ℂ) • S).IsSymmetric) (hn : finrank ℂ E = n)
    (hSn : ∀ v, ‖S v‖ ≤ ‖v‖) (k : Fin n) (x y : ℝ) :
    |(hL x).eigenvalues hn k - (hL y).eigenvalues hn k| ≤ |x - y| := by
  refine LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le (hL x) (hL y) hn (fun v => ?_) k
  have : ((T + (x : ℂ) • S) - (T + (y : ℂ) • S)) v = ((x - y : ℝ) : ℂ) • S v := by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply]
    push_cast
    rw [sub_smul]
    abel
  rw [this, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hSn v) (abs_nonneg _)

/-- **Monotonicity along a positive direction**. -/
theorem cib_eig_monotone (hL : ∀ x : ℝ, (T + (x : ℂ) • S).IsSymmetric) (hn : finrank ℂ E = n)
    (hSpos : ∀ v, 0 ≤ RCLike.re ⟪S v, v⟫_ℂ) (k : Fin n) :
    Monotone (fun x : ℝ => (hL x).eigenvalues hn k) := by
  intro x y hxy
  refine LinearMap.IsSymmetric.eigenvalue_mono (hL x) (hL y) hn (fun v => ?_) k
  simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_smul_left,
    Complex.conj_ofReal, map_add]
  have h1 : RCLike.re ((x : ℂ) * ⟪S v, v⟫_ℂ) = x * RCLike.re ⟪S v, v⟫_ℂ := by
    simp
  have h2 : RCLike.re ((y : ℂ) * ⟪S v, v⟫_ℂ) = y * RCLike.re ⟪S v, v⟫_ℂ := by
    simp
  rw [h1, h2]
  have := hSpos v
  nlinarith

/-- **Hellmann–Feynman at a simple eigenvalue**: if the `k`-th eigenvalue of `T + x₀ S` is
simple, then `x ↦ λ_k(T + x S)` has derivative `Re ⟪S v, v⟫` at `x₀` for every unit eigenvector
`v` of `T + x₀ S` with eigenvalue `λ_k(x₀)`. -/
theorem cib_hasDerivAt_eig (hL : ∀ x : ℝ, (T + (x : ℂ) • S).IsSymmetric)
    (hS : S.IsSymmetric) (hn : finrank ℂ E = n) (hSn : ∀ v, ‖S v‖ ≤ ‖v‖) (k : Fin n) (x₀ : ℝ)
    (hsimple : ∀ j, j ≠ k → (hL x₀).eigenvalues hn j ≠ (hL x₀).eigenvalues hn k)
    (v : E) (hv1 : ‖v‖ = 1)
    (hv : (T + (x₀ : ℂ) • S) v = (((hL x₀).eigenvalues hn k : ℝ) : ℂ) • v) :
    HasDerivAt (fun x : ℝ => (hL x).eigenvalues hn k) (RCLike.re ⟪S v, v⟫_ℂ) x₀ := by
  set b := (hL x₀).eigenvectorBasis hn with hb
  set L : ℝ → ℝ := fun x => (hL x).eigenvalues hn k with hLdef
  -- reduce to the basis eigenvector
  have hvb := cib_eq_smul_of_eigen (hL x₀) hn k hsimple v hv
  set c := ⟪b k, v⟫_ℂ with hc
  have hbk1 : ‖b k‖ = 1 := b.orthonormal.norm_eq_one k
  have hc1 : ‖c‖ = 1 := by
    have h := congrArg norm hvb
    rw [norm_smul, hbk1, mul_one, hv1] at h
    exact h.symm
  have hq : RCLike.re ⟪S v, v⟫_ℂ = RCLike.re ⟪S (b k), b k⟫_ℂ := by
    rw [hvb, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, RCLike.conj_mul, hc1]
    simp only [one_pow, RCLike.ofReal_one, one_mul]
    rfl
  rw [hq]
  set e := b k with he
  set q := RCLike.re ⟪S e, e⟫_ℂ with hqdef
  have hqC : ⟪e, S e⟫_ℂ = (q : ℂ) := by
    rw [← hS e e, hqdef]
    exact (hS.coe_re_inner_apply_self e).symm
  obtain ⟨δ, hδ, hgap⟩ := cib_exists_gap ((hL x₀).eigenvalues hn) k hsimple
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_pow_id (n := 2) one_lt_two)
  refine Asymptotics.IsBigO.of_bound (4 / δ) ?_
  have hnear : ∀ᶠ h in 𝓝 (0 : ℝ), |h| < δ / 4 := by
    have : Metric.ball (0 : ℝ) (δ / 4) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 (by positivity)
    filter_upwards [this] with h hh
    simpa [Metric.mem_ball, Real.dist_eq] using hh
  filter_upwards [hnear] with h hh
  -- the eigenvector at `x₀ + h`
  set u := (hL (x₀ + h)).eigenvectorBasis hn k with hu
  have hu1 : ‖u‖ = 1 := ((hL (x₀ + h)).eigenvectorBasis hn).orthonormal.norm_eq_one k
  set lh := L (x₀ + h) with hlh
  set l0 := L x₀ with hl0
  have hThu : (T + ((x₀ + h : ℝ) : ℂ) • S) u = ((lh : ℝ) : ℂ) • u :=
    (hL (x₀ + h)).apply_eigenvectorBasis hn k
  have hsplit : (T + ((x₀ + h : ℝ) : ℂ) • S) u = (T + (x₀ : ℂ) • S) u + (h : ℂ) • S u := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    push_cast
    rw [add_smul]
    abel
  have hTe : (T + (x₀ : ℂ) • S) e = ((l0 : ℝ) : ℂ) • e := (hL x₀).apply_eigenvectorBasis hn k
  -- `h ⟪e, S u⟫ = (lh - l0) ⟪e, u⟫`
  set a := ⟪e, u⟫_ℂ with ha
  have hkey : (h : ℂ) * ⟪e, S u⟫_ℂ = ((lh - l0 : ℝ) : ℂ) * a := by
    have h1 : ⟪e, (T + ((x₀ + h : ℝ) : ℂ) • S) u⟫_ℂ = ((lh : ℝ) : ℂ) * a := by
      rw [hThu, inner_smul_right]
    have h2 : ⟪e, (T + (x₀ : ℂ) • S) u⟫_ℂ = ((l0 : ℝ) : ℂ) * a := by
      rw [← (hL x₀) e u, hTe, inner_smul_left, Complex.conj_ofReal]
    rw [hsplit, inner_add_right, inner_smul_right, h2] at h1
    push_cast
    linear_combination h1
  -- the orthogonal remainder
  set w := u - a • e with hw
  have hee : ⟪e, e⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hbk1]
    simp
  have hperp : ⟪e, w⟫_ℂ = 0 := by
    rw [hw, inner_sub_right, inner_smul_right, hee, mul_one, ha, sub_self]
  have hSu : ⟪e, S u⟫_ℂ = a * (q : ℂ) + ⟪e, S w⟫_ℂ := by
    have : u = a • e + w := by rw [hw]; abel
    rw [this, map_add, map_smul, inner_add_right, inner_smul_right, hqC]
  have hkey2 : ((lh - l0 - h * q : ℝ) : ℂ) * a = (h : ℂ) * ⟪e, S w⟫_ℂ := by
    rw [hSu] at hkey
    push_cast at hkey ⊢
    linear_combination -hkey
  -- the norm of the remainder
  have hpy : ‖a‖ ^ 2 + ‖w‖ ^ 2 = 1 := by
    have hdec : u = a • e + w := by rw [hw]; abel
    have hpi : ⟪a • e, w⟫_ℂ = 0 := by rw [inner_smul_left, hperp, mul_zero]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a • e) w hpi
    rw [← hdec, hu1, norm_smul, hbk1, mul_one] at this
    nlinarith
  have hlip : |lh - l0| ≤ |h| := by
    have := cib_eig_lipschitz hL hn hSn k (x₀ + h) x₀
    rwa [add_sub_cancel_left] at this
  have hTw : (T + (x₀ : ℂ) • S) w - ((l0 : ℝ) : ℂ) • w = ((lh - l0 : ℝ) : ℂ) • u - (h : ℂ) • S u := by
    have h1 : (T + (x₀ : ℂ) • S) u = ((lh : ℝ) : ℂ) • u - (h : ℂ) • S u := by
      rw [← hThu, hsplit]; abel
    rw [hw, map_sub, map_smul, hTe, h1]
    push_cast
    rw [sub_smul, smul_sub, smul_comm a]
    abel
  have hwle : δ * ‖w‖ ≤ 2 * |h| := by
    have hg := cib_gap (hL x₀) hn k hδ.le hgap w hperp
    rw [hTw] at hg
    refine hg.trans ?_
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, hu1, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
      Real.norm_eq_abs, mul_one]
    have := hSn u
    rw [hu1] at this
    nlinarith [abs_nonneg h]
  have hw_small : ‖w‖ ≤ 1 / 2 := by
    have : δ * ‖w‖ ≤ δ * (1 / 2) := by nlinarith [abs_nonneg h]
    exact le_of_mul_le_mul_left this hδ
  have ha_big : 1 / 2 ≤ ‖a‖ := by
    nlinarith [norm_nonneg a, norm_nonneg w]
  -- conclusion
  have hfin : |lh - l0 - h * q| * ‖a‖ ≤ |h| * ‖w‖ := by
    have := congrArg norm hkey2
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
      Real.norm_eq_abs] at this
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg h)
    refine (norm_inner_le_norm e (S w)).trans ?_
    rw [hbk1, one_mul]
    exact hSn w
  have hres : |lh - l0 - h * q| ≤ 4 / δ * h ^ 2 := by
    have h1 : |lh - l0 - h * q| ≤ 2 * (|h| * ‖w‖) := by
      nlinarith [abs_nonneg (lh - l0 - h * q)]
    have h2 : |h| * ‖w‖ ≤ |h| * (2 * |h| / δ) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg h)
      rw [le_div_iff₀ hδ]
      linarith
    have h3 : 2 * (|h| * (2 * |h| / δ)) = 4 / δ * h ^ 2 := by
      rw [← sq_abs h]
      ring
    linarith
  rw [smul_eq_mul, Real.norm_eq_abs, norm_pow, Real.norm_eq_abs, sq_abs]
  exact hres

end Abstract

/-!
## 2. Matrices: a Hermitian matrix moved along a diagonal `[0, 1]` direction
-/

section Matrices

open Matrix BlockBand.Model.Construction BlockBand.Foundations.Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real diagonal direction `D = diag(d)`. -/
def cibDiag (d : ι → ℝ) : Matrix ι ι ℂ := Matrix.diagonal fun a => ((d a : ℝ) : ℂ)

omit [Fintype ι] in
theorem cib_diag_conjTranspose (d : ι → ℝ) : (cibDiag d)ᴴ = cibDiag d := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [cibDiag, conjTranspose_apply]
  · simp [cibDiag, conjTranspose_apply, diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]

omit [Fintype ι] in
theorem cib_line_isHermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (d : ι → ℝ) (x : ℝ) :
    (A + (x : ℂ) • cibDiag d).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_add, conjTranspose_smul, hA, cib_diag_conjTranspose, Complex.star_def,
    Complex.conj_ofReal]

theorem cib_toEuclideanLin_line (A : Matrix ι ι ℂ) (d : ι → ℝ) (x : ℝ) :
    toEuclideanLin (A + (x : ℂ) • cibDiag d) =
      toEuclideanLin A + (x : ℂ) • toEuclideanLin (cibDiag d) := by
  rw [map_add, map_smul]

theorem cib_line_isSymmetric {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (d : ι → ℝ) (x : ℝ) :
    (toEuclideanLin A + (x : ℂ) • toEuclideanLin (cibDiag d)).IsSymmetric := by
  rw [← cib_toEuclideanLin_line]
  exact isSymmetric_toEuclideanLin_iff.mpr (cib_line_isHermitian hA d x)

/-- The raw increasing eigenvalue on the line is the `i.rev`-th decreasing eigenvalue of the
symmetric operator `T + x S`. -/
theorem cib_raw_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (d : ι → ℝ) (i : Fin (Fintype.card ι))
    (x : ℝ) :
    rawIncreasingEigenvalue i (A + (x : ℂ) • cibDiag d) =
      (cib_line_isSymmetric hA d x).eigenvalues finrank_euclideanSpace i.rev := by
  rw [rawIncreasingEigenvalue_eq i _ (cib_line_isHermitian hA d x)]
  unfold increasingEigenvalue Matrix.IsHermitian.eigenvalues₀
  rw [LinearMap.IsSymmetric.eigenvalues_congr (cib_toEuclideanLin_line A d x)]

theorem cib_diag_apply (d : ι → ℝ) (v : EuclideanSpace ℂ ι) (a : ι) :
    (toEuclideanLin (cibDiag d) v).ofLp a = ((d a : ℝ) : ℂ) * v.ofLp a := by
  simp [toLpLin_apply, cibDiag, mulVec_diagonal]

theorem cib_diag_norm_le {d : ι → ℝ} (hd0 : ∀ a, 0 ≤ d a) (hd1 : ∀ a, d a ≤ 1)
    (v : EuclideanSpace ℂ ι) : ‖toEuclideanLin (cibDiag d) v‖ ≤ ‖v‖ := by
  have h : ‖toEuclideanLin (cibDiag d) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [cib_diag_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd0 a),
      mul_pow]
    have h1 : d a ^ 2 ≤ 1 := by nlinarith [hd0 a, hd1 a]
    nlinarith [sq_nonneg ‖v.ofLp a‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

theorem cib_diag_isSymmetric (d : ι → ℝ) : (toEuclideanLin (cibDiag d)).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.mpr (cib_diag_conjTranspose d)

theorem cib_diag_inner (d : ι → ℝ) (v : EuclideanSpace ℂ ι) :
    RCLike.re ⟪toEuclideanLin (cibDiag d) v, v⟫_ℂ = ∑ a, d a * ‖v.ofLp a‖ ^ 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Pi.star_apply, cib_diag_apply, star_mul', Complex.star_def, Complex.conj_ofReal,
    mul_left_comm, Complex.mul_conj, RCLike.re_to_complex, Complex.re_ofReal_mul]
  rw [Complex.normSq_eq_norm_sq, Complex.ofReal_re]

/-- **Lipschitz bound** `|λ_i(A + xD) - λ_i(A + yD)| ≤ |x - y|`. -/
theorem cib_matrix_lipschitz {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {d : ι → ℝ}
    (hd0 : ∀ a, 0 ≤ d a) (hd1 : ∀ a, d a ≤ 1) (i : Fin (Fintype.card ι)) (x y : ℝ) :
    |rawIncreasingEigenvalue i (A + (x : ℂ) • cibDiag d) -
        rawIncreasingEigenvalue i (A + (y : ℂ) • cibDiag d)| ≤ |x - y| := by
  rw [cib_raw_eq hA d i x, cib_raw_eq hA d i y]
  exact cib_eig_lipschitz (cib_line_isSymmetric hA d) finrank_euclideanSpace
    (cib_diag_norm_le hd0 hd1) i.rev x y

/-- **Monotonicity** of `x ↦ λ_i(A + xD)`. -/
theorem cib_matrix_monotone {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {d : ι → ℝ}
    (hd0 : ∀ a, 0 ≤ d a) (i : Fin (Fintype.card ι)) :
    Monotone (fun x : ℝ => rawIncreasingEigenvalue i (A + (x : ℂ) • cibDiag d)) := by
  intro x y hxy
  simp only [cib_raw_eq hA d i]
  refine cib_eig_monotone (cib_line_isSymmetric hA d) finrank_euclideanSpace (fun v => ?_) i.rev hxy
  rw [cib_diag_inner]
  exact Finset.sum_nonneg fun a _ => mul_nonneg (hd0 a) (sq_nonneg _)

/-- **Hellmann–Feynman for matrices**: at a parameter `x₀` where `A + x₀ D` has separable
characteristic polynomial, `x ↦ λ_i(A + xD)` has derivative `Σ_a d_a |ψ_a|²`, `ψ` the selected
eigenvector `rawOrderedColumnSelection i (A + x₀ D)`. -/
theorem cib_matrix_hasDerivAt {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {d : ι → ℝ}
    (hd0 : ∀ a, 0 ≤ d a) (hd1 : ∀ a, d a ≤ 1) (i : Fin (Fintype.card ι)) (x₀ : ℝ)
    (hsep : (A + (x₀ : ℂ) • cibDiag d).charpoly.Separable) :
    HasDerivAt (fun x : ℝ => rawIncreasingEigenvalue i (A + (x : ℂ) • cibDiag d))
      (∑ a, d a * ‖rawOrderedColumnSelection i (A + (x₀ : ℂ) • cibDiag d) a‖ ^ 2) x₀ := by
  set hB := cib_line_isHermitian hA d x₀ with hhB
  set B : HermitianMatrix ι := ⟨A + (x₀ : ℂ) • cibDiag d, hB⟩ with hBdef
  have hinj : Function.Injective (orderedEigenvalue B) :=
    orderedEigenvalue_injective_of_separable B hsep
  have hL := cib_line_isSymmetric hA d
  have hfun : (fun x : ℝ => rawIncreasingEigenvalue i (A + (x : ℂ) • cibDiag d)) =
      fun x => (hL x).eigenvalues finrank_euclideanSpace i.rev := funext (cib_raw_eq hA d i)
  have hval : ∀ j : Fin (Fintype.card ι),
      (hL x₀).eigenvalues finrank_euclideanSpace j = orderedEigenvalue B j.rev := by
    intro j
    have := cib_raw_eq hA d j.rev x₀
    rw [Fin.rev_rev, rawIncreasingEigenvalue_eq _ _ hB] at this
    exact this.symm
  have hsimple : ∀ j, j ≠ i.rev → (hL x₀).eigenvalues finrank_euclideanSpace j ≠
      (hL x₀).eigenvalues finrank_euclideanSpace i.rev := by
    intro j hj heq
    rw [hval, hval, Fin.rev_rev] at heq
    exact hj (by rw [← hinj heq, Fin.rev_rev])
  set ψ := orderedColumnSelection i B with hψ
  set v : EuclideanSpace ℂ ι := WithLp.toLp 2 ψ with hv
  have hv1 : ‖v‖ = 1 := by
    have h := sum_norm_sq_orderedColumnSelection i B hinj
    have h2 : ‖v‖ ^ 2 = 1 := by rw [EuclideanSpace.norm_sq_eq]; exact h
    nlinarith [norm_nonneg v]
  have hev : (toEuclideanLin A + (x₀ : ℂ) • toEuclideanLin (cibDiag d)) v =
      (((hL x₀).eigenvalues finrank_euclideanSpace i.rev : ℝ) : ℂ) • v := by
    have hT : (toEuclideanLin A + (x₀ : ℂ) • toEuclideanLin (cibDiag d)) v =
        toEuclideanLin (A + (x₀ : ℂ) • cibDiag d) v := by rw [cib_toEuclideanLin_line]
    refine hT.trans ?_
    rw [toLpLin_apply, hval, Fin.rev_rev]
    have h := mulVec_orderedColumnSelection i B hinj
    rw [hv, WithLp.ofLp_toLp]
    change WithLp.toLp 2 (B.val *ᵥ ψ) = _
    rw [h]
    rfl
  have hd := cib_hasDerivAt_eig hL (cib_diag_isSymmetric d) finrank_euclideanSpace
    (cib_diag_norm_le hd0 hd1) i.rev x₀ hsimple v hv1 hev
  rw [hfun]
  convert hd using 1
  rw [cib_diag_inner]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rawOrderedColumnSelection_eq i _ hB a]

end Matrices

end BlockBand.Center
