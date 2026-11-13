module

public import BlockBand.DeterminantScore.BorderLawCharpoly

/-!
# Diagonal border law: interlacing and the spectrum of the arrowhead matrix

* `arrowWeight_pos`: on the strictly interlacing set the weights `r_i(λ)` are positive (sign count
  of `∏_j(μ_i - λ_j)` and `∏_{k≠i}(μ_i - μ_k)`);
* `mem_interlaceSet_of_arrowPoly_eq`: conversely, monotone roots of the arrowhead polynomial with
  positive weights strictly interlace `μ` (a parity count of the roots above each `μ_i`,
  `count_eq_of_odd`);
* `borderEig μ r a`, the increasing eigenvalues of `[[diag μ, √r],[√r*, a]]`, satisfies
  `borderEig μ (r(λ)) (a(λ)) = λ` on the interlacing set (`borderEig_arrowCoord`) and, for `r > 0`,
  lies in the interlacing set with coordinates `(r, a)` (`borderEig_spec`);
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeylIntegration

open Matrix Polynomial BlockBand.Internal.Contracts.CoareaPalm

variable {n : ℕ}

/-- A real product is `(-1)^{#negative factors}` times the product of absolute values. -/
theorem prod_eq_neg_one_pow_mul_abs {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∏ j ∈ s, f j = (-1) ^ (s.filter fun j => f j < 0).card * ∏ j ∈ s, |f j| := by
  have h : ∀ j, f j = (if f j < 0 then -1 else 1) * |f j| := fun j => by
    split_ifs with hj
    · rw [abs_of_neg hj]; ring
    · rw [abs_of_nonneg (not_lt.1 hj)]; ring
  conv_lhs => rw [Finset.prod_congr rfl fun j _ => h j]
  rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-- Counting: an antitone `N : Fin n → ℕ` bounded by `n + 1` with `N_i + (n - 1 - i)` odd is
`N_i = n - i`. -/
theorem count_eq_of_odd {N : Fin n → ℕ} (hanti : ∀ i j, i ≤ j → N j ≤ N i)
    (hle : ∀ i, N i ≤ n + 1) (hodd : ∀ i, Odd (N i + (n - 1 - i))) (i : Fin n) :
    N i = n - i := by
  have lower : ∀ m : ℕ, ∀ i : Fin n, (i : ℕ) + m + 1 = n → m + 1 ≤ N i := by
    intro m
    induction m with
    | zero =>
      intro i hi
      have := Nat.odd_iff.1 (hodd i)
      omega
    | succ m ih =>
      intro i hi
      have hi' : (i : ℕ) + 1 < n := by omega
      have h1 := ih ⟨i + 1, hi'⟩ (by simp; omega)
      have h2 := hanti i ⟨i + 1, hi'⟩ (by rw [Fin.le_def]; simp only; omega)
      have h3 := Nat.odd_iff.1 (hodd i)
      have h4 := Nat.odd_iff.1 (hodd ⟨i + 1, hi'⟩)
      simp only at h4
      omega
  have upper : ∀ m : ℕ, ∀ i : Fin n, (i : ℕ) = m → N i + i ≤ n := by
    intro m
    induction m with
    | zero =>
      intro i hi
      have := Nat.odd_iff.1 (hodd i)
      have := hle i
      omega
    | succ m ih =>
      intro i hi
      have hm : m < n := by omega
      have h1 := ih ⟨m, hm⟩ rfl
      have h2 := hanti ⟨m, hm⟩ i (by rw [Fin.le_def]; simp only; omega)
      have h3 := Nat.odd_iff.1 (hodd i)
      have h4 := Nat.odd_iff.1 (hodd ⟨m, hm⟩)
      simp only at h4 h1
      omega
  have h1 := lower (n - 1 - i) i (by omega)
  have h2 := upper i i rfl
  omega

/-- Sign of `c_i = ∏_{k≠i}(μ_i - μ_k)` for increasing `μ`: `(-1)^{n-1-i}`. -/
theorem arrowDenom_eq {μ : Fin n → ℝ} (hμ : StrictMono μ) (i : Fin n) :
    arrowDenom μ i = (-1) ^ (n - 1 - i) * ∏ k ∈ Finset.univ.erase i, |μ i - μ k| := by
  rw [arrowDenom, prod_eq_neg_one_pow_mul_abs]
  congr 2
  have : ((Finset.univ.erase i).filter fun k => μ i - μ k < 0) = Finset.Ioi i := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, Finset.mem_Ioi, sub_neg,
      hμ.lt_iff_lt, and_true]
    exact ⟨fun h => h.2, fun h => ⟨h.ne', h⟩⟩
  rw [this, Fin.card_Ioi]

/-- `∏_{k≠i}|μ_i - μ_k| > 0`. -/
theorem prod_abs_arrowDenom_pos {μ : Fin n → ℝ} (hμ : StrictMono μ) (i : Fin n) :
    0 < ∏ k ∈ Finset.univ.erase i, |μ i - μ k| :=
  Finset.prod_pos fun _ hk =>
    abs_pos.2 (sub_ne_zero.2 fun h => (Finset.mem_erase.1 hk).1 (hμ.injective h).symm)

/-- Interlacing points are strictly increasing. -/
theorem strictMono_of_mem_interlaceSet {μ : Fin n → ℝ} {lam : Fin (n + 1) → ℝ}
    (hlam : lam ∈ interlaceSet μ) : StrictMono lam :=
  Fin.strictMono_iff_lt_succ.2 fun i => (hlam i).1.trans (hlam i).2

/-- Sign of `∏_j (μ_i - λ_j)` on the interlacing set: `(-1)^{n-i}`. -/
theorem prod_sub_eq_of_mem_interlaceSet {μ : Fin n → ℝ} {lam : Fin (n + 1) → ℝ}
    (hlam : lam ∈ interlaceSet μ) (i : Fin n) :
    ∏ j, (μ i - lam j) = (-1) ^ (n - i) * ∏ j, |μ i - lam j| := by
  have hmono := (strictMono_of_mem_interlaceSet hlam).monotone
  rw [prod_eq_neg_one_pow_mul_abs]
  congr 2
  have : (Finset.univ.filter fun j => μ i - lam j < 0) = Finset.Ioi i.castSucc := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi, sub_neg]
    constructor
    · intro h
      by_contra hj
      exact absurd ((hmono (not_lt.1 hj)).trans (hlam i).1.le) (not_le.2 h)
    · intro hj
      exact (hlam i).2.trans_le (hmono (Fin.castSucc_lt_iff_succ_le.1 hj))
  rw [this, Fin.card_Ioi, Fin.val_castSucc]
  omega

/-- On the interlacing set no `λ_j` equals `μ_i`. -/
theorem prod_abs_sub_pos_of_mem_interlaceSet {μ : Fin n → ℝ} {lam : Fin (n + 1) → ℝ}
    (hlam : lam ∈ interlaceSet μ) (i : Fin n) : 0 < ∏ j, |μ i - lam j| := by
  have hmono := (strictMono_of_mem_interlaceSet hlam).monotone
  refine Finset.prod_pos fun j _ => abs_pos.2 (sub_ne_zero.2 fun h => ?_)
  rcases le_or_gt j i.castSucc with hj | hj
  · exact absurd ((hmono hj).trans_lt (hlam i).1) (by rw [h]; exact lt_irrefl _)
  · exact absurd ((hlam i).2.trans_le (hmono (Fin.castSucc_lt_iff_succ_le.1 hj)))
      (by rw [h]; exact lt_irrefl _)

/-- The weights `r_i(λ)` are positive on the interlacing set. -/
theorem arrowWeight_pos {μ : Fin n → ℝ} (hμ : StrictMono μ) {lam : Fin (n + 1) → ℝ}
    (hlam : lam ∈ interlaceSet μ) (i : Fin n) : 0 < arrowWeight μ lam i := by
  have hA := prod_abs_sub_pos_of_mem_interlaceSet hlam i
  have hC := prod_abs_arrowDenom_pos hμ i
  rw [arrowWeight, prod_sub_eq_of_mem_interlaceSet hlam, arrowDenom_eq hμ,
    show n - (i : ℕ) = (n - 1 - i) + 1 by omega, pow_succ]
  have hs : ((-1 : ℝ) ^ (n - 1 - (i : ℕ))) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hne : ((-1 : ℝ) ^ (n - 1 - (i : ℕ))) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [show -((-1 : ℝ) ^ (n - 1 - (i : ℕ)) * -1 * ∏ j, |μ i - lam j|) /
      ((-1) ^ (n - 1 - (i : ℕ)) * ∏ k ∈ Finset.univ.erase i, |μ i - μ k|) =
      (∏ j, |μ i - lam j|) / ∏ k ∈ Finset.univ.erase i, |μ i - μ k| by
    field_simp]
  exact div_pos hA hC

/-- Parity from a sign identity `(-1)^p A = -r (-1)^q C`, `A ≥ 0 < r, C`. -/
theorem odd_of_sign_eq {p q : ℕ} {A r C : ℝ} (hA : 0 ≤ A) (hr : 0 < r) (hC : 0 < C)
    (h : (-1) ^ p * A = -(r * ((-1) ^ q * C))) : Odd (p + q) ∧ A ≠ 0 := by
  have hrC := mul_pos hr hC
  rcases Nat.even_or_odd p with hp | hp <;> rcases Nat.even_or_odd q with hq | hq
  · rw [hp.neg_one_pow, hq.neg_one_pow] at h; exact absurd h (by nlinarith)
  · rw [hp.neg_one_pow, hq.neg_one_pow] at h
    exact ⟨hp.add_odd hq, by intro h0; rw [h0] at h; nlinarith⟩
  · rw [hp.neg_one_pow, hq.neg_one_pow] at h
    exact ⟨hp.add_even hq, by intro h0; rw [h0] at h; nlinarith⟩
  · rw [hp.neg_one_pow, hq.neg_one_pow] at h; exact absurd h (by nlinarith)

/-- **Interlacing**: if the arrowhead polynomial with positive weights `r` has the monotone roots
`λ`, then `λ` strictly interlaces `μ`. -/
theorem mem_interlaceSet_of_arrowPoly_eq {μ r : Fin n → ℝ} {a : ℝ} (hμ : StrictMono μ)
    (hr : ∀ i, 0 < r i) {lam : Fin (n + 1) → ℝ} (hlam : Monotone lam)
    (h : arrowPoly μ r a = rootPoly lam) : lam ∈ interlaceSet μ := by
  set N : Fin n → ℕ := fun i => (Finset.univ.filter fun j => μ i - lam j < 0).card with hN
  have hsign : ∀ i, Odd (N i + (n - 1 - i)) ∧ ∏ j, |μ i - lam j| ≠ 0 := by
    intro i
    have he := congrArg (fun p => p.eval (μ i)) h
    simp only [eval_arrowPoly, eval_rootPoly] at he
    rw [prod_eq_neg_one_pow_mul_abs, arrowDenom_eq hμ] at he
    exact odd_of_sign_eq (Finset.prod_nonneg fun _ _ => abs_nonneg _) (hr i)
      (prod_abs_arrowDenom_pos hμ i) he.symm
  have hcount : ∀ i, N i = n - i := by
    refine count_eq_of_odd (fun i i' hii' => ?_) (fun i => ?_) (fun i => (hsign i).1)
    · refine Finset.card_le_card fun j => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_neg]
      exact fun hj => (hμ.monotone hii').trans_lt hj
    · exact (Finset.card_filter_le _ _).trans (by simp)
  have hne : ∀ i j, μ i ≠ lam j := fun i j h0 =>
    (hsign i).2 (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [h0, sub_self, abs_zero]))
  intro i
  constructor
  · by_contra hc
    have hlt : μ i < lam i.castSucc := lt_of_le_of_ne (not_lt.1 hc) (hne i _)
    have hsub : Finset.Ici i.castSucc ⊆ Finset.univ.filter fun j => μ i - lam j < 0 := by
      intro j hj
      simp only [Finset.mem_Ici] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_neg]
      exact hlt.trans_le (hlam hj)
    have := Finset.card_le_card hsub
    rw [Fin.card_Ici, Fin.val_castSucc] at this
    have h2 := hcount i
    simp only [hN] at h2
    omega
  · by_contra hc
    have hle : lam i.succ ≤ μ i := not_lt.1 hc
    have hsub : (Finset.univ.filter fun j => μ i - lam j < 0) ⊆ Finset.Ioi i.succ := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_neg] at hj
      simp only [Finset.mem_Ioi]
      by_contra hj'
      exact absurd ((hlam (not_lt.1 hj')).trans hle) (not_le.2 hj)
    have := Finset.card_le_card hsub
    rw [Fin.card_Ioi, Fin.val_succ] at this
    have h2 := hcount i
    simp only [hN] at h2
    have := i.isLt
    omega

/-!
## The increasing eigenvalues of the arrowhead matrix
-/

/-- Increasing eigenvalues of `[[diag μ, √r],[√r*, a]]`. -/
def borderEig (μ r : Fin n → ℝ) (a : ℝ) : Fin (n + 1) → ℝ := fun k =>
  freshEigenvalue
    (borderHerm (diagonal fun i => (μ i : ℂ)) (fun i => ((Real.sqrt (r i) : ℝ) : ℂ)) a) k

/-- A real diagonal matrix is Hermitian. -/
theorem isHermitian_diagonal_ofReal (μ : Fin n → ℝ) :
    (diagonal fun i => (μ i : ℂ)).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]

/-- Characteristic polynomial of `[[diag μ, √r],[√r*, a]]`, `r ≥ 0`. -/
theorem charpoly_borderHerm_sqrt (μ : Fin n → ℝ) {r : Fin n → ℝ} (hr : ∀ i, 0 ≤ r i) (a : ℝ) :
    (borderHerm (diagonal fun i => (μ i : ℂ)) (fun i => ((Real.sqrt (r i) : ℝ) : ℂ)) a).charpoly =
      (arrowPoly μ r a).map (algebraMap ℝ ℂ) := by
  rw [charpoly_borderHerm_diagonal]
  congr 3
  funext i
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hr i)]

/-- The spectrum of `[[diag μ, v],[v*, a]]` depends on `v` only through `|v_i|²`. -/
theorem freshEigenvalue_borderHerm_diagonal (μ : Fin n → ℝ) (v : Fin n → ℂ) (a : ℝ) :
    (fun k => freshEigenvalue (borderHerm (diagonal fun i => (μ i : ℂ)) v a) k) =
      borderEig μ (fun i => ‖v i‖ ^ 2) a := by
  refine freshEigenvalue_eq_of_charpoly_eq
    (isHermitian_borderHerm (isHermitian_diagonal_ofReal μ) v a)
    (isHermitian_borderHerm (isHermitian_diagonal_ofReal μ) _ a) ?_
  rw [charpoly_borderHerm_diagonal, charpoly_borderHerm_sqrt μ (fun i => sq_nonneg _)]

/-- Complexified root polynomial. -/
theorem map_rootPoly {m : ℕ} (lam : Fin m → ℝ) :
    (rootPoly lam).map (algebraMap ℝ ℂ) = ∏ j, (X - C ((lam j : ℝ) : ℂ)) := by
  simp [rootPoly, Polynomial.map_prod]

/-- A Hermitian matrix's characteristic polynomial has roots its increasing eigenvalues. -/
theorem charpoly_eq_rootPoly_freshEigenvalue {m : ℕ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hB : B.IsHermitian) :
    B.charpoly = (rootPoly fun k => freshEigenvalue B k).map (algebraMap ℝ ℂ) := by
  rw [map_rootPoly, hB.charpoly_eq]
  obtain ⟨e, he⟩ := SpectralConvexity.exists_equiv_freshEigenvalue hB
  rw [← Equiv.prod_comp e]
  simp_rw [he]
  rfl

/-- On the interlacing set, `λ` is the spectrum of the arrowhead matrix with
`(r, a) = (r(λ), a(λ))`. -/
theorem borderEig_arrowCoord {μ : Fin n → ℝ} (hμ : StrictMono μ) {lam : Fin (n + 1) → ℝ}
    (hlam : lam ∈ interlaceSet μ) :
    borderEig μ (arrowWeight μ lam) (arrowCorner μ lam) = lam := by
  refine EigenDensity.freshEigenvalue_eq_of_charpoly
    (isHermitian_borderHerm (isHermitian_diagonal_ofReal μ) _ _)
    (strictMono_of_mem_interlaceSet hlam).monotone ?_
  rw [charpoly_borderHerm_sqrt μ (fun i => (arrowWeight_pos hμ hlam i).le),
    arrowPoly_arrowCoord hμ.injective, map_rootPoly]

/-- For positive weights the spectrum strictly interlaces `μ` and returns `(r, a)`. -/
theorem borderEig_spec {μ r : Fin n → ℝ} (hμ : StrictMono μ) (hr : ∀ i, 0 < r i) (a : ℝ) :
    borderEig μ r a ∈ interlaceSet μ ∧ arrowWeight μ (borderEig μ r a) = r ∧
      arrowCorner μ (borderEig μ r a) = a := by
  have hB := isHermitian_borderHerm (isHermitian_diagonal_ofReal μ)
    (fun i => ((Real.sqrt (r i) : ℝ) : ℂ)) a
  have hpoly : arrowPoly μ r a = rootPoly (borderEig μ r a) := by
    refine Polynomial.map_injective (algebraMap ℝ ℂ) (RCLike.ofReal_injective) ?_
    rw [← charpoly_borderHerm_sqrt μ (fun i => (hr i).le), charpoly_eq_rootPoly_freshEigenvalue hB]
    rfl
  exact ⟨mem_interlaceSet_of_arrowPoly_eq hμ hr (EigenDensity.monotone_freshEigenvalue hB) hpoly,
    arrowCoord_of_arrowPoly_eq hμ.injective hpoly⟩

end BlockBand.DeterminantScore.WeylIntegration
