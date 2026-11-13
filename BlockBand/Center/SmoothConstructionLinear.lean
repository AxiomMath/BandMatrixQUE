module

public import BlockBand.Center.SmoothCenter
public import BlockBand.Layers.TaggedTrace

/-!
# Deterministic linear algebra for the smooth center

Invertibility of the full matrix `H - E - ζ P_S` on the shift lines, operator-norm and
Hilbert–Schmidt bounds for the compressed resolvent, the Ward identity and stability of the Dyson
equation at a root, and a comparison of the tagged derivative at two spectral parameters.

* §1 `scn_ctrFull_det_ne`: for Hermitian, ring-banded `H` with invertible exterior bonds, the
  full matrix `H - E - ζ P_S` is invertible for every real `E` and `Im ζ ≠ 0`.
* §5 `scn_D_diff_le`: the tagged derivative at two spectral parameters differs by
  `O(|ζ₁ - ζ₀|) λ(ζ₀)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexConjugate Matrix.Norms.L2Operator

/-!
## 1. Invertibility of the full matrix on the shift lines
-/

section Invertible

variable {p : Parameters} {e : ZMod p.n}

/-- The quadratic form of a Hermitian matrix is real. -/
theorem scn_im_quad_hermitian {H : p.SiteMatrix} (hH : H.IsHermitian) (v : p.Site → ℂ) :
    (∑ x, conj (v x) * (H *ᵥ v) x).im = 0 := by
  have h : conj (∑ x, conj (v x) * (H *ᵥ v) x) = ∑ x, conj (v x) * (H *ᵥ v) x := by
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
    rw [Finset.sum_comm]
    have key : ∀ a b, conj (H a b) = H b a := fun a b => hH.apply b a
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [key]
    ring
  exact Complex.conj_eq_iff_im.mp h

theorem scn_ctrFull_mulVec_apply (H : p.SiteMatrix) (E : ℝ) (ζ : ℂ) (v : p.Site → ℂ)
    (x : p.Site) :
    (ctrFull p e H E ζ *ᵥ v) x =
      (H *ᵥ v) x - (E : ℂ) * v x - ζ * (if x.1 = e ∨ x.1 = e + 1 then v x else 0) := by
  unfold ctrFull pairProjector
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul]
  split_ifs <;> ring

/-- A kernel vector of `H - E - ζ P_S` (`H` Hermitian, `Im ζ ≠ 0`) vanishes on the pair. -/
theorem scn_kernel_pair_zero {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) {ζ : ℂ}
    (hζ : ζ.im ≠ 0) {v : p.Site → ℂ} (hv : ctrFull p e H E ζ *ᵥ v = 0) (x : p.Site)
    (hx : x.1 = e ∨ x.1 = e + 1) : v x = 0 := by
  have hsum : ∑ x, conj (v x) * (ctrFull p e H E ζ *ᵥ v) x = 0 :=
    Finset.sum_eq_zero fun x _ => by rw [hv, Pi.zero_apply, mul_zero]
  have hexp : ∑ x, conj (v x) * (ctrFull p e H E ζ *ᵥ v) x =
      (∑ x, conj (v x) * (H *ᵥ v) x) - (E : ℂ) * ((∑ x, Complex.normSq (v x) : ℝ) : ℂ) -
        ζ * ((∑ x, (if x.1 = e ∨ x.1 = e + 1 then Complex.normSq (v x) else 0) : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [scn_ctrFull_mulVec_apply, Complex.normSq_eq_conj_mul_self]
    split_ifs
    · rw [Complex.normSq_eq_conj_mul_self]; ring
    · push_cast; ring
  rw [hexp] at hsum
  have him := congrArg Complex.im hsum
  rw [Complex.sub_im, Complex.sub_im, scn_im_quad_hermitian hH, Complex.mul_im, Complex.mul_im]
    at him
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_sub,
    Complex.zero_im] at him
  set S : ℝ := ∑ x, (if x.1 = e ∨ x.1 = e + 1 then Complex.normSq (v x) else 0) with hS
  have hS0 : S = 0 := by
    have : ζ.im * S = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hζ
    · exact h
  have hnn : ∀ y ∈ Finset.univ, 0 ≤ (if y.1 = e ∨ y.1 = e + 1 then Complex.normSq (v y) else 0) :=
    fun y _ => by split_ifs <;> simp [Complex.normSq_nonneg]
  have hx0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hS0 x (Finset.mem_univ _)
  rw [ite_eq_left_of_eq_true _ _ (eq_true hx)] at hx0
  exact Complex.normSq_eq_zero.mp hx0

theorem scn_natCast_ne_zero {m : ℕ} (h0 : 0 < m) (hm : m < p.n) : ((m : ℕ) : ZMod p.n) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd h0 h) (not_le.mpr hm)

/-- One step of the propagation along the ring: if `(H - E)v = 0`, `v` vanishes on the blocks
`j, j+1`, `H` is ring-banded and the bond `H_{j-1,j}` is invertible, then `v` vanishes on the
block `j - 1`. -/
theorem scn_propagate_step {H : p.SiteMatrix} (hH : H.IsHermitian) (hband : IsRingBanded p H)
    {E : ℝ} {v : p.Site → ℂ} (hker : ∀ x, (H *ᵥ v) x = (E : ℂ) * v x) {j : ZMod p.n}
    (h0 : ∀ a, v (j, a) = 0) (h1 : ∀ a, v (j + 1, a) = 0)
    (hbond : (Matrix.of fun a b : Fin p.W => H (j - 1, a) (j - 1 + 1, b)).det ≠ 0) :
    ∀ a, v (j - 1, a) = 0 := by
  have hn4 := p.n_ge_four
  have hj1 : j - 1 ≠ j := by
    intro h
    have : ((1 : ℕ) : ZMod p.n) = 0 := by
      have h' : (1 : ZMod p.n) = j - (j - 1) := by ring
      rw [Nat.cast_one, h', h, sub_self]
    exact scn_natCast_ne_zero (by norm_num) (by omega) this
  have hj2 : j - 1 ≠ j + 1 := by
    intro h
    have : ((2 : ℕ) : ZMod p.n) = 0 := by
      have h' : ((2 : ℕ) : ZMod p.n) = (j + 1) - (j - 1) := by push_cast; ring
      rw [h', h, sub_self]
    exact scn_natCast_ne_zero (by norm_num) (by omega) this
  set B := Matrix.of fun a b : Fin p.W => H (j - 1, a) (j - 1 + 1, b) with hB
  set w : Fin p.W → ℂ := fun c => v (j - 1, c) with hw
  have hrow : ∀ a, (Bᴴ *ᵥ w) a = 0 := by
    intro a
    have hx := hker (j, a)
    rw [h0 a, mul_zero] at hx
    rw [← hx]
    simp only [Matrix.mulVec, dotProduct]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (j - 1)]
    · refine Finset.sum_congr rfl fun c _ => ?_
      simp only [hB, hw, Matrix.conjTranspose_apply, Matrix.of_apply]
      rw [show j - 1 + 1 = j by ring]
      rw [hH.apply (j, a) (j - 1, c)]
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hbj : b = j ∨ b = j + 1
      · rcases hbj with hbj | hbj
        · rw [hbj, h0 c, mul_zero]
        · rw [hbj, h1 c, mul_zero]
      · rw [hband (j, a) (b, c) (by
          simp only
          push Not at hbj ⊢
          exact ⟨hbj.1, hbj.2, hb⟩), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hdet : Bᴴ.det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact (star_ne_zero).mpr hbond
  have := Matrix.eq_zero_of_mulVec_eq_zero hdet (funext hrow)
  intro a
  exact congrFun this a

/-- **Invertibility on the shift lines**: for Hermitian, ring-banded `H` with
invertible exterior bonds, `H - E - ζ P_S` is invertible for every real `E` and `Im ζ ≠ 0`
(a kernel vector vanishes on the pair by the Ward identity, then on every block by
propagation through the invertible exterior bonds). -/
theorem scn_ctrFull_det_ne {H : p.SiteMatrix} (hH : H.IsHermitian) (hband : IsRingBanded p H)
    (hbond : ExteriorBondsInvertible p e H) (E : ℝ) {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    (ctrFull p e H E ζ).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  have hpair := scn_kernel_pair_zero hH E hζ hv
  have hker : ∀ x, (H *ᵥ v) x = (E : ℂ) * v x := by
    intro x
    have h := congrFun hv x
    rw [scn_ctrFull_mulVec_apply, Pi.zero_apply] at h
    have h2 : (if x.1 = e ∨ x.1 = e + 1 then v x else 0) = 0 := by
      split_ifs with hx
      · exact hpair x hx
      · rfl
    rw [h2, mul_zero, sub_zero] at h
    linear_combination h
  have hn4 := p.n_ge_four
  have claim : ∀ m : ℕ, m + 2 ≤ p.n →
      (∀ a, v (e - (m : ZMod p.n), a) = 0) ∧ (∀ a, v (e - (m : ZMod p.n) + 1, a) = 0) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [Nat.cast_zero, sub_zero]
      exact ⟨fun a => hpair _ (Or.inl rfl), fun a => hpair _ (Or.inr rfl)⟩
    | succ m ih =>
      intro hm
      obtain ⟨h0, h1⟩ := ih (by omega)
      have hne : e - (m : ZMod p.n) - 1 ≠ e := by
        intro h
        have : (((m + 1 : ℕ)) : ZMod p.n) = 0 := by
          have h' : (((m + 1 : ℕ)) : ZMod p.n) = e - (e - (m : ZMod p.n) - 1) := by
            push_cast; ring
          rw [h', h, sub_self]
        exact scn_natCast_ne_zero (by omega) (by omega) this
      have hstep := scn_propagate_step hH hband hker h0 h1 (hbond _ hne)
      refine ⟨fun a => ?_, fun a => ?_⟩
      · have := hstep a
        rwa [show e - ((m + 1 : ℕ) : ZMod p.n) = e - (m : ZMod p.n) - 1 by push_cast; ring]
      · have := h0 a
        rwa [show e - ((m + 1 : ℕ) : ZMod p.n) + 1 = e - (m : ZMod p.n) by push_cast; ring]
  funext x
  obtain ⟨j, a⟩ := x
  set m := (e - j).val with hm
  have hmlt : m < p.n := ZMod.val_lt _
  have hjm : j = e - (m : ZMod p.n) := by
    rw [hm, ZMod.natCast_zmod_val]; ring
  by_cases hm2 : m + 2 ≤ p.n
  · rw [hjm]; exact (claim m hm2).1 a
  · have hmn : m = (p.n - 2) + 1 := by omega
    have h := (claim (p.n - 2) (by omega)).1 a
    have hj' : j = e - ((p.n - 2 : ℕ) : ZMod p.n) - 1 := by
      rw [hjm, hmn]; push_cast; ring
    have hcl := (claim (p.n - 2) (by omega)).2
    -- `e - (n-2) - 1 = e - (n - 1) = e + 1`
    have he1 : e - ((p.n - 2 : ℕ) : ZMod p.n) - 1 = e + 1 := by
      have hcast : ((p.n - 2 : ℕ) : ZMod p.n) = -2 := by
        have : ((p.n - 2 : ℕ) : ZMod p.n) + 2 = (p.n : ZMod p.n) := by
          rw [show (2 : ZMod p.n) = ((2 : ℕ) : ZMod p.n) by norm_num, ← Nat.cast_add,
            Nat.sub_add_cancel (by omega)]
        rw [ZMod.natCast_self] at this
        linear_combination this
      rw [hcast]; ring
    rw [hj', he1]
    exact hpair _ (Or.inr rfl)

end Invertible

/-!
## 2. Norm tools: operator norm and Hilbert–Schmidt mass
-/

section Norms

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] [DecidableEq m] [DecidableEq n]
  [DecidableEq l]

/-- The Hilbert–Schmidt mass `Σ_{x,y} |X_xy|²` of a rectangular matrix. -/
def scnHS (X : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (X i j)

theorem scnHS_nonneg (X : Matrix m n ℂ) : 0 ≤ scnHS X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem scn_mulVec_normSq_le (A : Matrix m n ℂ) (v : n → ℂ) :
    ∑ i, Complex.normSq ((A *ᵥ v) i) ≤ ‖A‖ ^ 2 * ∑ j, Complex.normSq (v j) := by
  have h := Matrix.l2_opNorm_mulVec A ((EuclideanSpace.equiv n ℂ).symm v)
  have h2 : ‖(EuclideanSpace.equiv m ℂ).symm (A *ᵥ v)‖ ^ 2 ≤
      (‖A‖ * ‖(EuclideanSpace.equiv n ℂ).symm v‖) ^ 2 := by
    have h0 := norm_nonneg ((EuclideanSpace.equiv m ℂ).symm (A *ᵥ v))
    exact pow_le_pow_left₀ h0 (by simpa using h) 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa [Complex.normSq_eq_norm_sq] using h2

theorem scn_norm_entry_le (X : Matrix m n ℂ) (i : m) (j : n) : ‖X i j‖ ≤ ‖X‖ := by
  have h := scn_mulVec_normSq_le X (Pi.single j 1)
  have hv : ∑ k, Complex.normSq ((Pi.single j (1 : ℂ) : n → ℂ) k) = 1 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk; simp [hk]
    · simp
  rw [hv, mul_one] at h
  have hi : Complex.normSq ((X *ᵥ Pi.single j 1) i) ≤
      ∑ k, Complex.normSq ((X *ᵥ Pi.single j 1) k) :=
    Finset.single_le_sum (f := fun k => Complex.normSq ((X *ᵥ Pi.single j 1) k))
      (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  rw [Matrix.mulVec_single_one] at hi h
  have : ‖X i j‖ ^ 2 ≤ ‖X‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hi.trans (by simpa [Matrix.col_apply] using h)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp this

theorem scnHS_conjTranspose (X : Matrix m n ℂ) : scnHS Xᴴ = scnHS X := by
  unfold scnHS
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

theorem scnHS_mul_left (B : Matrix m n ℂ) (X : Matrix n l ℂ) :
    scnHS (B * X) ≤ ‖B‖ ^ 2 * scnHS X := by
  unfold scnHS
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => Complex.normSq (X i j)), Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := scn_mulVec_normSq_le B (fun k => X k j)
  convert h using 3 with i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem scnHS_mul_right (X : Matrix m n ℂ) (B : Matrix n l ℂ) :
    scnHS (X * B) ≤ scnHS X * ‖B‖ ^ 2 := by
  rw [← scnHS_conjTranspose, Matrix.conjTranspose_mul, ← scnHS_conjTranspose X, mul_comm,
    ← Matrix.l2_opNorm_conjTranspose B]
  exact scnHS_mul_left _ _

theorem scn_norm_trace_mul_sq_le (U : Matrix m n ℂ) (V : Matrix n m ℂ) :
    ‖(U * V).trace‖ ^ 2 ≤ scnHS U * scnHS V := by
  have h1 : ‖(U * V).trace‖ ≤ ∑ i, ∑ k, ‖U i k‖ * ‖V k i‖ := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul]
  have h2 : (∑ i, ∑ k, ‖U i k‖ * ‖V k i‖) ^ 2 ≤
      (∑ i, ∑ k, ‖U i k‖ ^ 2) * (∑ i, ∑ k, ‖V k i‖ ^ 2) := by
    simp only [← Finset.sum_product']
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hU : ∑ i, ∑ k, ‖U i k‖ ^ 2 = scnHS U := by
    unfold scnHS; simp [Complex.normSq_eq_norm_sq]
  have hV : ∑ i, ∑ k, ‖V k i‖ ^ 2 = scnHS V := by
    unfold scnHS; rw [Finset.sum_comm]; simp [Complex.normSq_eq_norm_sq]
  rw [hU, hV] at h2
  calc ‖(U * V).trace‖ ^ 2 ≤ (∑ i, ∑ k, ‖U i k‖ * ‖V k i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem scn_norm_trace_mul_le (U : Matrix m n ℂ) (V : Matrix n m ℂ) :
    ‖(U * V).trace‖ ≤ Real.sqrt (scnHS U) * Real.sqrt (scnHS V) := by
  rw [← Real.sqrt_mul (scnHS_nonneg U)]
  exact Real.le_sqrt_of_sq_le (scn_norm_trace_mul_sq_le U V)

theorem scn_norm_diagonal_indicator_le (P : m → Prop) [DecidablePred P] :
    ‖(Matrix.diagonal fun x => if P x then (1 : ℂ) else 0 : Matrix m m ℂ)‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_diagonal]
  refine pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun x => ?_
  split_ifs <;> simp

end Norms

/-!
## 3. The compressed resolvent: blocks, adjoint, norm, Ward, stability
-/

section Resolvent

variable {p : Parameters} {e : ZMod p.n}

/-- The `(S_i, S_j)` block of a site matrix (`S_i = {i, i+1}`). -/
def scnBlk (A : p.SiteMatrix) (i j : ZMod p.n) : Matrix (PairSite p i) (PairSite p j) ℂ :=
  fun x y => A x.1 y.1

theorem scn_compressed_eq_blk (H : p.SiteMatrix) (E : ℝ) (ζ : ℂ) :
    compressedResolvent p e H E ζ = scnBlk (ctrFull p e H E ζ)⁻¹ e e := rfl

theorem scn_full_inv_conjTranspose {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) (ζ : ℂ) :
    ((ctrFull p e H E ζ)⁻¹)ᴴ = (ctrFull p e H E (conj ζ))⁻¹ := by
  rw [Matrix.conjTranspose_nonsing_inv, ctr_ctrFull_conjTranspose hH]

theorem scn_blk_conjTranspose (A : p.SiteMatrix) (i j : ZMod p.n) :
    (scnBlk A i j)ᴴ = scnBlk Aᴴ j i := by
  ext x y
  simp [scnBlk, Matrix.conjTranspose_apply]

/-- Block form of the resolvent identity: `A₁ - A₂ = (ζ₁ - ζ₂) A₁ P_S A₂`. -/
theorem scn_blk_sub (H : p.SiteMatrix) (E : ℝ) {ζ₁ ζ₂ : ℂ}
    (h₁ : (ctrFull p e H E ζ₁).det ≠ 0) (h₂ : (ctrFull p e H E ζ₂).det ≠ 0) (i j : ZMod p.n) :
    scnBlk (ctrFull p e H E ζ₁)⁻¹ i j - scnBlk (ctrFull p e H E ζ₂)⁻¹ i j =
      (ζ₁ - ζ₂) • (scnBlk (ctrFull p e H E ζ₁)⁻¹ i e * scnBlk (ctrFull p e H E ζ₂)⁻¹ e j) := by
  ext x y
  have h := congrFun (congrFun (ctr_full_inv_sub H E h₁ h₂) x.1) y.1
  rw [Matrix.sub_apply, Matrix.smul_apply, ctr_mul_projector_mul_apply] at h
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply]
  exact h

theorem scn_conj_sub (ζ : ℂ) : conj ζ - ζ = -(2 * ζ.im : ℝ) * Complex.I := by
  apply Complex.ext <;> simp; ring

/-- **Operator norm of the compressed resolvent**: `‖ℛ(ζ)‖ ≤ 1/|Im ζ|` (Hermitian `H`, invertible
full matrices at `ζ` and `ζ̄`). -/
theorem scn_norm_compressed_le {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) {ζ : ℂ}
    (hζ : ζ.im ≠ 0) (h₁ : (ctrFull p e H E ζ).det ≠ 0) :
    ‖compressedResolvent p e H E ζ‖ ≤ 1 / |ζ.im| := by
  have h₂ : (ctrFull p e H E (conj ζ)).det ≠ 0 := ctr_full_det_conj hH E h₁
  set R := compressedResolvent p e H E ζ
  have hs := ctr_compressed_sub (i := e) H E h₂ h₁
  rw [ctr_compressed_conj hH] at hs
  have hn := congrArg norm hs
  rw [norm_smul, Matrix.l2_opNorm_conjTranspose_mul_self, scn_conj_sub] at hn
  have hle : ‖Rᴴ - R‖ ≤ 2 * ‖R‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose]; linarith
  have hc : ‖(-(2 * ζ.im : ℝ) * Complex.I : ℂ)‖ = 2 * |ζ.im| := by
    rw [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_two]
  rw [hc] at hn
  have hy : 0 < |ζ.im| := abs_pos.mpr hζ
  have hR := norm_nonneg R
  rw [le_div_iff₀ hy]
  by_cases h0 : ‖R‖ = 0
  · rw [h0]; norm_num
  · have hpos : 0 < ‖R‖ := lt_of_le_of_ne hR (Ne.symm h0)
    have : 2 * |ζ.im| * (‖R‖ * ‖R‖) ≤ 2 * ‖R‖ := hn ▸ hle
    nlinarith

theorem scn_card_block_le (k : ZMod p.n) :
    ((Finset.univ.filter fun x : PairSite p e => x.1.1 = k).card : ℝ) ≤ p.W := by
  have : (Finset.univ.filter fun x : PairSite p e => x.1.1 = k).card ≤ p.W := by
    calc (Finset.univ.filter fun x : PairSite p e => x.1.1 = k).card
        ≤ (Finset.univ : Finset (Fin p.W)).card := by
          refine Finset.card_le_card_of_injOn (fun x => x.1.2) (fun _ _ => Finset.mem_univ _) ?_
          intro x hx y hy hxy
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
          exact Subtype.ext (Prod.ext (hx.trans hy.symm) hxy)
      _ = p.W := by simp
  exact_mod_cast this

/-- `|W⁻¹ Tr P_k M| ≤ ‖M‖`. -/
theorem scn_norm_pairBlockTrace_le (M : PairMatrix p e) (k : ZMod p.n) :
    ‖pairBlockTrace p e M k‖ ≤ ‖M‖ := by
  unfold pairBlockTrace
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rw [inv_mul_le_iff₀ hW]
  calc ‖∑ x : PairSite p e, if x.1.1 = k then M x x else 0‖
      ≤ ∑ x : PairSite p e, if x.1.1 = k then ‖M‖ else 0 := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        split_ifs
        · exact scn_norm_entry_le M x x
        · simp
    _ = ((Finset.univ.filter fun x : PairSite p e => x.1.1 = k).card : ℝ) * ‖M‖ := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ p.W * ‖M‖ := mul_le_mul_of_nonneg_right (scn_card_block_le k) (norm_nonneg _)

/-- `pairBlockTrace` as a trace against a diagonal indicator. -/
theorem scn_pairBlockTrace_eq_trace (M : PairMatrix p e) (k : ZMod p.n) :
    pairBlockTrace p e M k = (p.W : ℂ)⁻¹ *
      ((Matrix.diagonal fun x : PairSite p e => if x.1.1 = k then (1 : ℂ) else 0) * M).trace := by
  unfold pairBlockTrace Matrix.trace
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, Matrix.diagonal_mul]
  split_ifs <;> simp

/-- `Tr J_e M = W (W⁻¹ Tr P_e M - W⁻¹ Tr P_{e+1} M)`. -/
theorem scn_trace_contrast (M : PairMatrix p e) :
    (pairContrast p e * M).trace =
      (p.W : ℂ) * (pairBlockTrace p e M e - pairBlockTrace p e M (e + 1)) := by
  have hW : (p.W : ℂ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  unfold pairBlockTrace
  rw [← mul_sub, ← mul_assoc, mul_inv_cancel₀ hW, one_mul, ← Finset.sum_sub_distrib]
  unfold Matrix.trace pairContrast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, Matrix.diagonal_mul]
  rcases x.2 with h | h
  · have h' : x.1.1 ≠ e + 1 := by
      rw [h]; exact (BlockBand.Layers.rng_add_one_ne p e).symm
    rw [ite_eq_left h, ite_eq_left h, ite_eq_right h']; ring
  · have h' : x.1.1 ≠ e := by
      rw [h]; exact BlockBand.Layers.rng_add_one_ne p e
    rw [ite_eq_right h', ite_eq_right h', ite_eq_left h]; ring

/-- The unclipped center value `(s/N_aux) Tr J_e ℛ*ℛ`. -/
def scnU (p : Parameters) (e : ZMod p.n) (M : PairMatrix p e) : ℝ :=
  ((splitS p : ℂ) * (2 * (p.W : ℂ))⁻¹ * (pairContrast p e * Mᴴ * M).trace).re

/-- **The center as a residual difference**: `(s/N_aux) Tr J_e ℛ*ℛ =
(s/2) Im(W⁻¹Tr P_eℛ - W⁻¹Tr P_{e+1}ℛ)/Im ζ` (Ward identity `ℛ*ℛ = (ℛ - ℛ*)/(ζ - ζ̄)`). -/
theorem scn_scnU_eq {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) {ζ : ℂ} (hζ : ζ.im ≠ 0)
    (h₁ : (ctrFull p e H E ζ).det ≠ 0) :
    scnU p e (compressedResolvent p e H E ζ) =
      splitS p / 2 * (pairBlockTrace p e (compressedResolvent p e H E ζ) e -
        pairBlockTrace p e (compressedResolvent p e H E ζ) (e + 1)).im / ζ.im := by
  have h₂ : (ctrFull p e H E (conj ζ)).det ≠ 0 := ctr_full_det_conj hH E h₁
  set R := compressedResolvent p e H E ζ
  have hs := ctr_compressed_sub (i := e) H E h₂ h₁
  rw [ctr_compressed_conj hH] at hs
  -- `Rᴴ R = (Rᴴ - R) / (ζ̄ - ζ)`
  have hne : conj ζ - ζ ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    exact hζ (by linarith)
  have hRR : Rᴴ * R = (conj ζ - ζ)⁻¹ • (Rᴴ - R) := by
    rw [hs, smul_smul, inv_mul_cancel₀ hne, one_smul]
  set T := (pairContrast p e * R).trace
  have hJ : (pairContrast p e)ᴴ = pairContrast p e := by
    unfold pairContrast
    rw [Matrix.diagonal_conjTranspose]
    congr 1; funext x; simp only [Pi.star_apply]; split_ifs <;> simp
  have hTs : (pairContrast p e * Rᴴ).trace = conj T := by
    rw [show pairContrast p e * Rᴴ = (R * pairContrast p e)ᴴ by
      rw [Matrix.conjTranspose_mul, hJ], Matrix.trace_conjTranspose, Matrix.trace_mul_comm]
    rfl
  have htr : (pairContrast p e * Rᴴ * R).trace = (conj ζ - ζ)⁻¹ * (conj T - T) := by
    rw [Matrix.mul_assoc, hRR, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub,
      Matrix.trace_sub, hTs, smul_eq_mul]
  have hW : (p.W : ℂ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  have hT : T = (p.W : ℂ) * (pairBlockTrace p e R e - pairBlockTrace p e R (e + 1)) :=
    scn_trace_contrast R
  unfold scnU
  rw [htr, scn_conj_sub]
  set d := pairBlockTrace p e R e - pairBlockTrace p e R (e + 1)
  have hTd : conj T - T = -(2 * T.im : ℝ) * Complex.I := by
    apply Complex.ext <;> simp; ring
  rw [hTd]
  have hTim : T.im = p.W * d.im := by
    rw [hT]; simp [Complex.mul_im]
  rw [hTim]
  have hWr : (p.W : ℝ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  have hk : ((-(2 * ζ.im : ℝ) * Complex.I)⁻¹ * (-(2 * (p.W * d.im) : ℝ) * Complex.I) : ℂ) =
      ((p.W * d.im / ζ.im : ℝ) : ℂ) := by
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hζc : ((ζ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hζ
    push_cast
    field_simp
  rw [hk]
  rw [show ((splitS p : ℂ) * (2 * (p.W : ℂ))⁻¹ * ((p.W * d.im / ζ.im : ℝ) : ℂ)) =
    ((splitS p * (2 * (p.W : ℝ))⁻¹ * (p.W * d.im / ζ.im) : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]
  field_simp

/-- `|ζ| ≤ √s ≤ 1` at a Dyson root (Ward identity and Cauchy–Schwarz). -/
theorem scn_root_norm_le {H : p.SiteMatrix} (hH : H.IsHermitian) {E : ℝ} {ζ : ℂ}
    (h : IsDysonRoot p e H E ζ) : ‖ζ‖ ≤ 1 := by
  have hw := ctr_root_ward hH h
  set R := compressedResolvent p e H E ζ
  have hz := h.2
  rw [← ctrK_coe] at hz
  have htr : R.trace = (1 * R).trace := by rw [Matrix.one_mul]
  have hcs := scn_norm_trace_mul_sq_le (1 : PairMatrix p e) R
  rw [← htr] at hcs
  have h1 : scnHS (1 : PairMatrix p e) = 2 * p.W := by
    unfold scnHS
    have hrow : ∀ x : PairSite p e, ∑ y, Complex.normSq ((1 : PairMatrix p e) x y) = 1 := by
      intro x
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hy; simp [Ne.symm hy]
      · simp
    simp only [hrow, Finset.sum_const, Finset.card_univ, ctr_card_pairSite, nsmul_eq_mul, mul_one]
    push_cast; ring
  have hHS : scnHS R = ctrHS R := rfl
  rw [h1, hHS] at hcs
  have hk := ctrK_pos (p := p)
  have hs := ctr_splitS_pos (p := p)
  have hs1 := ctr_splitS_le_one (p := p)
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hkW : ctrK p * (2 * p.W) = splitS p := by
    unfold ctrK; field_simp
  have hnorm : ‖ζ‖ ^ 2 ≤ 1 := by
    rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, mul_pow]
    have hHSv : ctrHS R = 1 / ctrK p := by field_simp; linarith
    rw [hHSv] at hcs
    calc ctrK p ^ 2 * ‖R.trace‖ ^ 2 ≤ ctrK p ^ 2 * (2 * p.W * (1 / ctrK p)) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = splitS p := by rw [← hkW]; field_simp
      _ ≤ 1 := hs1
  nlinarith [norm_nonneg ζ]

/-- `|(s/N_aux) Tr J_e ℛ*ℛ| ≤ 1` at a Dyson root. -/
theorem scn_abs_scnU_root_le {H : p.SiteMatrix} (hH : H.IsHermitian) {E : ℝ} {ζ : ℂ}
    (h : IsDysonRoot p e H E ζ) : |scnU p e (compressedResolvent p e H E ζ)| ≤ 1 := by
  have hw := ctr_root_ward hH h
  set M := compressedResolvent p e H E ζ
  unfold scnU
  rw [ctr_contrast_re, abs_mul, abs_of_pos ctrK_pos, ← hw]
  exact mul_le_mul_of_nonneg_left (ctr_abs_contrast_le M) ctrK_pos.le

end Resolvent

/-!
## 4. Stability of the Dyson equation at a root
-/

section Stability

variable {p : Parameters} {e : ZMod p.n}

theorem scn_norm_one_le {m : Type*} [Fintype m] [DecidableEq m] : ‖(1 : Matrix m m ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  refine pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun _ => ?_
  simp

/-- `ℛ*ℛ = ℛℛ*` and `ℛ* - ℛ = (ζ̄ - ζ)ℛ*ℛ` for the compressed resolvent (Hermitian `H`). -/
theorem scn_compressed_normal {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) {ζ : ℂ}
    (hζ : ζ.im ≠ 0) (h₁ : (ctrFull p e H E ζ).det ≠ 0) :
    (compressedResolvent p e H E ζ)ᴴ - compressedResolvent p e H E ζ =
        (conj ζ - ζ) • ((compressedResolvent p e H E ζ)ᴴ * compressedResolvent p e H E ζ) ∧
      compressedResolvent p e H E ζ * (compressedResolvent p e H E ζ)ᴴ =
        (compressedResolvent p e H E ζ)ᴴ * compressedResolvent p e H E ζ := by
  have h₂ : (ctrFull p e H E (conj ζ)).det ≠ 0 := ctr_full_det_conj hH E h₁
  have hs1 := ctr_compressed_sub (i := e) H E h₂ h₁
  have hs2 := ctr_compressed_sub (i := e) H E h₁ h₂
  rw [ctr_compressed_conj hH] at hs1 hs2
  refine ⟨hs1, ?_⟩
  have hne : ζ - conj ζ ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    exact hζ (by linarith)
  have key : (ζ - conj ζ) • (compressedResolvent p e H E ζ * (compressedResolvent p e H E ζ)ᴴ) =
      (ζ - conj ζ) • ((compressedResolvent p e H E ζ)ᴴ * compressedResolvent p e H E ζ) := by
    rw [← hs2, show ζ - conj ζ = -(conj ζ - ζ) by ring, neg_smul, ← hs1]
    abel
  have := congrArg (fun M => (ζ - conj ζ)⁻¹ • M) key
  simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using this

/-- **Stability of the Dyson equation at its root**: for Hermitian `H^{(e)}` and a Dyson root `ζ`,
`Re(1 - (s/N_aux) Tr ℛ(ζ)²) ≥ 2 (Im ζ)²/s` (Ward identity `(s/N_aux) Tr ℛ*ℛ = 1`, normality, and
`Tr (ℛ*ℛ)² ≥ (Tr ℛ*ℛ)²/N_aux`). In particular the Jacobian of `ζ ↦ ζ - (s/N_aux) Tr ℛ(ζ)` does not
vanish at the root. -/
theorem scn_stability {H : p.SiteMatrix} (hH : H.IsHermitian) {E : ℝ} {ζ : ℂ}
    (h : IsDysonRoot p e H E ζ) :
    2 * ζ.im ^ 2 / splitS p ≤
      (1 - (ctrK p : ℂ) * (compressedResolvent p e H E ζ * compressedResolvent p e H E ζ).trace).re := by
  have hy := h.1
  have h₁ := ctr_root_det_ne_zero h
  obtain ⟨hs1, hnorm⟩ := scn_compressed_normal hH E hy.ne' h₁
  set R := compressedResolvent p e H E ζ
  set X := Rᴴ * R with hX
  set k := ctrK p
  have hw := ctr_root_ward hH h
  -- `k Tr X = 1`
  have htrX : X.trace = ((ctrHS R : ℝ) : ℂ) := by
    rw [← hnorm]; exact ctr_trace_mul_conjTranspose R
  have hXh : Xᴴ = X := by rw [hX, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  -- `1 - k Tr R² = k (ζ̄ - ζ) Tr (X R)`
  have h1 : 1 - (k : ℂ) * (R * R).trace = (k : ℂ) * ((conj ζ - ζ) * (X * R).trace) := by
    have e1 : (1 : ℂ) = (k : ℂ) * X.trace := by
      rw [htrX, ← Complex.ofReal_mul, hw, Complex.ofReal_one]
    rw [e1, ← mul_sub, ← Matrix.trace_sub]
    congr 1
    rw [show X - R * R = (Rᴴ - R) * R by rw [hX, Matrix.sub_mul], hs1, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul]
  -- `Im Tr (X R) = Im ζ · Tr X²`
  have h2 : (X * R).trace - conj (X * R).trace = (ζ - conj ζ) * (X * X).trace := by
    have hc : conj (X * R).trace = (X * Rᴴ).trace := by
      rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hXh,
        Matrix.trace_mul_comm]
    have hRR : R - Rᴴ = (ζ - conj ζ) • X := by
      rw [show ζ - conj ζ = -(conj ζ - ζ) by ring, neg_smul, ← hs1]; abel
    rw [hc, ← Matrix.trace_sub, ← Matrix.mul_sub, hRR, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul]
  have hXX : (X * X).trace = ((ctrHS X : ℝ) : ℂ) := by
    rw [show X * X = X * Xᴴ by rw [hXh]]
    exact ctr_trace_mul_conjTranspose X
  have him : (X * R).trace.im = ζ.im * ctrHS X := by
    have := congrArg Complex.im h2
    rw [hXX] at this
    simp only [Complex.sub_im, Complex.conj_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero] at this
    linarith
  have hre : (1 - (k : ℂ) * (R * R).trace).re = 2 * ζ.im * k * (ζ.im * ctrHS X) := by
    rw [h1, ← him]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.sub_im, Complex.conj_re, Complex.conj_im, zero_mul, sub_zero, Complex.mul_im]
    ring
  rw [hre]
  -- `ctrHS X ≥ (Tr X)² / (2W) = 1/(k² 2W)`
  have hN : (Fintype.card (PairSite p e) : ℝ) = 2 * p.W := by
    rw [ctr_card_pairSite]; push_cast; ring
  have hdiag : (∑ x, (X x x).re) ^ 2 ≤ (Fintype.card (PairSite p e) : ℝ) * ctrHS X := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun x : PairSite p e => (X x x).re)
    refine hcs.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    unfold ctrHS
    refine Finset.sum_le_sum fun x _ => ?_
    calc (X x x).re ^ 2 ≤ Complex.normSq (X x x) := by
          rw [Complex.normSq_apply]; nlinarith [sq_nonneg (X x x).im]
      _ ≤ ∑ z, Complex.normSq (X x z) :=
          Finset.single_le_sum (f := fun z => Complex.normSq (X x z))
            (fun z _ => Complex.normSq_nonneg _) (Finset.mem_univ x)
  have hsumre : ∑ x, (X x x).re = 1 / k := by
    have := congrArg Complex.re htrX
    rw [Matrix.trace, Complex.re_sum] at this
    simp only [Matrix.diag_apply, Complex.ofReal_re] at this
    rw [this]
    have hk : 0 < k := ctrK_pos
    field_simp
    linarith
  rw [hsumre, hN] at hdiag
  have hk : 0 < k := ctrK_pos
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hs : 0 < splitS p := ctr_splitS_pos
  have hkW : k * (2 * p.W) = splitS p := by
    simp only [k]; unfold ctrK; field_simp
  have hHS : 1 / (k * splitS p) ≤ ctrHS X := by
    rw [← hkW]
    rw [div_pow, one_pow] at hdiag
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ k ^ 2 * (2 * p.W * ctrHS X) := by
      have h3 := mul_le_mul_of_nonneg_left hdiag (sq_nonneg k)
      rwa [mul_one_div_cancel (by positivity)] at h3
    nlinarith
  have hy2 : 0 ≤ ζ.im ^ 2 := sq_nonneg _
  calc 2 * ζ.im ^ 2 / splitS p = 2 * ζ.im * k * (ζ.im * (1 / (k * splitS p))) := by
        field_simp
    _ ≤ 2 * ζ.im * k * (ζ.im * ctrHS X) := by
        have : 0 ≤ 2 * ζ.im * k * ζ.im := by positivity
        nlinarith

end Stability

/-!
## 5. Comparison of the tagged derivative at two spectral parameters
-/

section Compare

variable {p : Parameters} {e : ZMod p.n}

theorem scn_norm_one_add_smul_le {m : Type*} [Fintype m] [DecidableEq m] (c : ℂ)
    (R : Matrix m m ℂ) : ‖1 + c • R‖ ≤ 1 + ‖c‖ * ‖R‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul]
  linarith [scn_norm_one_le (m := m)]

theorem scn_sqrt_HS_mul_left_le {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
    [DecidableEq m] [DecidableEq n] [DecidableEq l] (B : Matrix m n ℂ) (X : Matrix n l ℂ)
    {c : ℝ} (hc : 0 ≤ c) (hB : ‖B‖ ≤ c) : Real.sqrt (scnHS (B * X)) ≤ c * Real.sqrt (scnHS X) := by
  rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg c)]
  refine Real.sqrt_le_sqrt ((scnHS_mul_left B X).trans ?_)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hB 2) (scnHS_nonneg X)

theorem scn_sqrt_HS_mul_right_le {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
    [DecidableEq m] [DecidableEq n] [DecidableEq l] (X : Matrix m n ℂ) (B : Matrix n l ℂ)
    {c : ℝ} (hc : 0 ≤ c) (hB : ‖B‖ ≤ c) : Real.sqrt (scnHS (X * B)) ≤ Real.sqrt (scnHS X) * c := by
  rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (scnHS_nonneg X)]
  refine Real.sqrt_le_sqrt ((scnHS_mul_right X B).trans ?_)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hB 2) (scnHS_nonneg X)

/-- The diagonal indicator of the block `k` inside the pair `S_e`. -/
def scnQ (e k : ZMod p.n) : PairMatrix p e :=
  Matrix.diagonal fun x : PairSite p e => if x.1.1 = k then (1 : ℂ) else 0

theorem scn_norm_scnQ_le (k : ZMod p.n) : ‖scnQ (p := p) e k‖ ≤ 1 :=
  scn_norm_diagonal_indicator_le _

/-- `|W⁻¹ Tr P_k (U V)| ≤ W⁻¹ ‖P_k‖ … ` in Hilbert–Schmidt form. -/
theorem scn_norm_pairBlockTrace_mul_le {g : ZMod p.n} (U : Matrix (PairSite p e) (PairSite p g) ℂ)
    (V : Matrix (PairSite p g) (PairSite p e) ℂ) (k : ZMod p.n) :
    ‖pairBlockTrace p e (U * V) k‖ ≤
      (p.W : ℝ)⁻¹ * (Real.sqrt (scnHS U) * Real.sqrt (scnHS V)) := by
  rw [scn_pairBlockTrace_eq_trace, norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  change ‖(scnQ e k * (U * V)).trace‖ ≤ _
  rw [← Matrix.mul_assoc]
  refine (scn_norm_trace_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  have := scn_sqrt_HS_mul_left_le (scnQ (p := p) e k) U zero_le_one (scn_norm_scnQ_le k)
  linarith

/-- **Comparison of `∂_{ξ_g} ε` at two spectral parameters**: with
`A_j = (H - E - ζ_j P_S)⁻¹`, `D_k(ζ) = W⁻¹ Tr P_k [A P_g A]_{SS}` and
`λ(ζ₀) = W⁻¹ Σ_{y ∈ S_g, z ∈ S_e} |A₀_yz|²`,
`|D_k(ζ₁) - D_k(ζ₀)| ≤ |ζ₁ - ζ₀| (6 + 3|ζ₁ - ζ₀|/Im ζ₁)/Im ζ₁ · λ(ζ₀)`. -/
theorem scn_D_diff_le {H : p.SiteMatrix} (hH : H.IsHermitian) (E : ℝ) {ζ₁ ζ₀ : ℂ}
    (hy₁ : 0 < ζ₁.im) (hy₀ : 0 < ζ₀.im) (h₁ : (ctrFull p e H E ζ₁).det ≠ 0)
    (h₀ : (ctrFull p e H E ζ₀).det ≠ 0) (g k : ZMod p.n) :
    ‖pairBlockTrace p e (scnBlk (ctrFull p e H E ζ₁)⁻¹ e g * scnBlk (ctrFull p e H E ζ₁)⁻¹ g e) k -
        pairBlockTrace p e (scnBlk (ctrFull p e H E ζ₀)⁻¹ e g *
          scnBlk (ctrFull p e H E ζ₀)⁻¹ g e) k‖ ≤
      ‖ζ₁ - ζ₀‖ * ((6 + 3 * ‖ζ₁ - ζ₀‖ / ζ₁.im) / ζ₁.im) *
        ((p.W : ℝ)⁻¹ * scnHS (scnBlk (ctrFull p e H E ζ₀)⁻¹ g e)) := by
  have hc₀ : (ctrFull p e H E (conj ζ₀)).det ≠ 0 := ctr_full_det_conj hH E h₀
  set A₁ := (ctrFull p e H E ζ₁)⁻¹
  set A₀ := (ctrFull p e H E ζ₀)⁻¹
  set Ab := (ctrFull p e H E (conj ζ₀))⁻¹
  set δ := ζ₁ - ζ₀ with hδ
  set R₁ := scnBlk A₁ e e
  set Rb := scnBlk Ab e e
  set Y₀ := scnBlk A₀ g e
  set Y₁ := scnBlk A₁ g e
  set Z₀ := scnBlk A₀ e g
  set Z₁ := scnBlk A₁ e g
  have hR₁ : ‖R₁‖ ≤ 1 / ζ₁.im := by
    have := scn_norm_compressed_le hH E hy₁.ne' h₁
    rwa [abs_of_pos hy₁] at this
  have hRb : ‖Rb‖ ≤ 1 / ζ₀.im := by
    have := scn_norm_compressed_le hH E (by simpa using hy₀.ne') hc₀
    rwa [Complex.conj_im, abs_neg, abs_of_pos hy₀] at this
  -- `Y₁ = Y₀ (1 + δ R₁)`, `Z₁ = (1 + δ R₁) Z₀`, `Ȳ = Y₀ (1 + (ζ̄₀ - ζ₀) R̄)`
  have hY : Y₁ = Y₀ * (1 + δ • R₁) := by
    have h := scn_blk_sub H E h₀ h₁ g e
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    have : Y₁ = Y₀ - (ζ₀ - ζ₁) • (Y₀ * R₁) := by rw [← h]; abel
    rw [this, hδ, show ζ₀ - ζ₁ = -(ζ₁ - ζ₀) by ring, neg_smul, sub_neg_eq_add]
  have hZ : Z₁ = (1 + δ • R₁) * Z₀ := by
    have h := scn_blk_sub H E h₁ h₀ e g
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [← h]; abel
  have hYb : scnBlk Ab g e = Y₀ * (1 + (conj ζ₀ - ζ₀) • Rb) := by
    have h := scn_blk_sub H E h₀ hc₀ g e
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    have : scnBlk Ab g e = Y₀ - (ζ₀ - conj ζ₀) • (Y₀ * Rb) := by rw [← h]; abel
    rw [this, show ζ₀ - conj ζ₀ = -(conj ζ₀ - ζ₀) by ring, neg_smul, sub_neg_eq_add]
  have hZ₀ : Z₀ = (scnBlk Ab g e)ᴴ := by
    rw [scn_blk_conjTranspose]
    simp only [Z₀, Ab, A₀]
    rw [scn_full_inv_conjTranspose hH, Complex.conj_conj]
  -- Hilbert–Schmidt bounds
  set a := Real.sqrt (scnHS Y₀)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hn1 : ‖1 + δ • R₁‖ ≤ 1 + ‖δ‖ / ζ₁.im := by
    refine (scn_norm_one_add_smul_le δ R₁).trans ?_
    have := mul_le_mul_of_nonneg_left hR₁ (norm_nonneg δ)
    rw [mul_one_div] at this
    linarith
  have hnb : ‖1 + (conj ζ₀ - ζ₀) • Rb‖ ≤ 3 := by
    refine (scn_norm_one_add_smul_le _ Rb).trans ?_
    have hc : ‖conj ζ₀ - ζ₀‖ = 2 * ζ₀.im := by
      rw [scn_conj_sub, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hc]
    have := mul_le_mul_of_nonneg_left hRb (by positivity : (0 : ℝ) ≤ 2 * ζ₀.im)
    rw [show 2 * ζ₀.im * (1 / ζ₀.im) = 2 by field_simp] at this
    linarith
  have hZa : Real.sqrt (scnHS Z₀) ≤ 3 * a := by
    rw [hZ₀, scnHS_conjTranspose, hYb]
    have := scn_sqrt_HS_mul_right_le Y₀ (1 + (conj ζ₀ - ζ₀) • Rb) (by norm_num) hnb
    linarith
  have hY₁a : Real.sqrt (scnHS Y₁) ≤ a * (1 + ‖δ‖ / ζ₁.im) := by
    rw [hY]; exact scn_sqrt_HS_mul_right_le Y₀ _ (by positivity) hn1
  -- the difference
  have hdiff : Z₁ * Y₁ - Z₀ * Y₀ = δ • ((R₁ * Z₀) * Y₁) + δ • (Z₀ * (Y₀ * R₁)) := by
    have e1 : Z₁ * Y₁ - Z₀ * Y₀ = (Z₁ - Z₀) * Y₁ + Z₀ * (Y₁ - Y₀) := by
      rw [Matrix.sub_mul, Matrix.mul_sub]; abel
    have e2 : Z₁ - Z₀ = δ • (R₁ * Z₀) := by
      rw [hZ, Matrix.add_mul, Matrix.one_mul, add_sub_cancel_left, Matrix.smul_mul]
    have e3 : Y₁ - Y₀ = δ • (Y₀ * R₁) := by
      rw [hY, Matrix.mul_add, Matrix.mul_one, add_sub_cancel_left, Matrix.mul_smul]
    rw [e1, e2, e3, Matrix.smul_mul, Matrix.mul_smul]
  have hlin : pairBlockTrace p e (Z₁ * Y₁) k - pairBlockTrace p e (Z₀ * Y₀) k =
      δ * pairBlockTrace p e ((R₁ * Z₀) * Y₁) k + δ * pairBlockTrace p e (Z₀ * (Y₀ * R₁)) k := by
    simp only [pairBlockTrace]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    have hd := hdiff
    have : ∀ x : PairSite p e, ((if x.1.1 = k then (Z₁ * Y₁) x x else 0) -
        if x.1.1 = k then (Z₀ * Y₀) x x else 0) =
        δ * (if x.1.1 = k then ((R₁ * Z₀) * Y₁) x x else 0) +
          δ * (if x.1.1 = k then (Z₀ * (Y₀ * R₁)) x x else 0) := by
      intro x
      have := congrFun (congrFun hd x) x
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this
      split_ifs
      · rw [this]
      · ring
    rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    ring
  rw [hlin]
  have t1 : ‖pairBlockTrace p e ((R₁ * Z₀) * Y₁) k‖ ≤
      (p.W : ℝ)⁻¹ * ((1 / ζ₁.im * (3 * a)) * (a * (1 + ‖δ‖ / ζ₁.im))) := by
    refine (scn_norm_pairBlockTrace_mul_le _ _ k).trans
      (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hRZ := scn_sqrt_HS_mul_left_le R₁ Z₀ (by positivity) hR₁
    refine mul_le_mul (hRZ.trans (mul_le_mul_of_nonneg_left hZa (by positivity))) hY₁a
      (Real.sqrt_nonneg _) (by positivity)
  have t2 : ‖pairBlockTrace p e (Z₀ * (Y₀ * R₁)) k‖ ≤
      (p.W : ℝ)⁻¹ * ((3 * a) * (a * (1 / ζ₁.im))) := by
    refine (scn_norm_pairBlockTrace_mul_le _ _ k).trans
      (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact mul_le_mul hZa (scn_sqrt_HS_mul_right_le Y₀ R₁ (by positivity) hR₁)
      (Real.sqrt_nonneg _) (by positivity)
  have hasq : a * a = scnHS Y₀ := Real.mul_self_sqrt (scnHS_nonneg _)
  calc ‖δ * pairBlockTrace p e ((R₁ * Z₀) * Y₁) k + δ * pairBlockTrace p e (Z₀ * (Y₀ * R₁)) k‖
      ≤ ‖δ‖ * ‖pairBlockTrace p e ((R₁ * Z₀) * Y₁) k‖ +
          ‖δ‖ * ‖pairBlockTrace p e (Z₀ * (Y₀ * R₁)) k‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_); rw [norm_mul, norm_mul]
    _ ≤ ‖δ‖ * ((p.W : ℝ)⁻¹ * ((1 / ζ₁.im * (3 * a)) * (a * (1 + ‖δ‖ / ζ₁.im)))) +
          ‖δ‖ * ((p.W : ℝ)⁻¹ * ((3 * a) * (a * (1 / ζ₁.im)))) := by
        gcongr
    _ = ‖δ‖ * ((6 + 3 * ‖δ‖ / ζ₁.im) / ζ₁.im) * ((p.W : ℝ)⁻¹ * (a * a)) := by
        field_simp
        ring
    _ = _ := by rw [hasq]

end Compare

/-!
## 6. The tagged quantities in full-inverse form
-/

section Tagged

variable {p : Parameters} {e : ZMod p.n}

open BlockBand.Layers

theorem scn_trace_conj_diag_mul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (V : Matrix α β ℂ) (d : α → ℝ) :
    (Vᴴ * Matrix.diagonal (fun x => (d x : ℂ)) * V).trace =
      ((∑ x, d x * ∑ z, Complex.normSq (V x z) : ℝ) : ℂ) := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring

/-- The indicator of the pair `S_g` at a site. -/
def scnInd (g : ZMod p.n) (x : p.Site) : ℝ := if x.1 = g ∨ x.1 = g + 1 then 1 else 0

theorem scn_pairBlock_projector (g : ZMod p.n) :
    pairBlock p e (pairProjector p g) = Matrix.diagonal fun x => ((scnInd g x.1 : ℝ) : ℂ) := by
  ext x y
  unfold pairBlock pairProjector scnInd
  by_cases h : x = y
  · subst h; simp only [Matrix.diagonal_apply_eq]; split_ifs <;> simp
  · have h' : x.1 ≠ y.1 := fun h'' => h (Subtype.ext h'')
    simp [h, h']

theorem scn_exteriorBlock_projector (g : ZMod p.n) :
    exteriorBlock p e (pairProjector p g) = Matrix.diagonal fun x => ((scnInd g x.1 : ℝ) : ℂ) := by
  ext x y
  unfold exteriorBlock pairProjector scnInd
  by_cases h : x = y
  · subst h; simp only [Matrix.diagonal_apply_eq]; split_ifs <;> simp
  · have h' : x.1 ≠ y.1 := fun h'' => h (Subtype.ext h'')
    simp [h, h']

theorem scn_scnHS_blk_eq (A : p.SiteMatrix) (g : ZMod p.n) :
    scnHS (scnBlk A g e) = ∑ y : p.Site, scnInd g y * ∑ z : PairSite p e,
      Complex.normSq (A y z.1) := by
  unfold scnHS scnBlk
  rw [← Fintype.sum_subtype_add_sum_subtype (fun y : p.Site => y.1 = g ∨ y.1 = g + 1)]
  have h2 : ∑ y : {y : p.Site // ¬ (y.1 = g ∨ y.1 = g + 1)}, scnInd g y.1 *
      ∑ z : PairSite p e, Complex.normSq (A y.1 z.1) = 0 :=
    Finset.sum_eq_zero fun y _ => by simp [scnInd, y.2]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [scnInd, y.2]

/-- **`λ_{eg}` in full-inverse form** (off the exterior poles, Hermitian `H^{(e)}`):
`λ_{eg} = W⁻¹ Σ_{y ∈ S_g, z ∈ S_e} |(H - E - sμ P_S)⁻¹_{yz}|²` (Schur column formula
`A_{RS} = -(H_R - E)⁻¹ C A_{SS}`). -/
theorem scn_tgtLambda_eq {H : p.SiteMatrix} (hH : H.IsHermitian) {E : ℝ}
    (hdet : (exteriorBlock p e H - (E : ℂ) • 1).det ≠ 0)
    (hM : (ctrFull p e H E ((splitS p : ℂ) * tgtMu E)).det ≠ 0) (g : ZMod p.n) :
    tgtLambda p e g H E = (((p.W : ℝ)⁻¹ *
      scnHS (scnBlk (ctrFull p e H E ((splitS p : ℂ) * tgtMu E))⁻¹ g e) : ℝ) : ℂ) := by
  set ζ := (splitS p : ℂ) * tgtMu E
  set A := (ctrFull p e H E ζ)⁻¹ with hA
  set R := scnBlk A e e with hR
  set N := exteriorBlock p e H - (E : ℂ) • 1 with hN
  set C := couplingBlock p e H with hC
  have hR0 : tgtR0 p e H E = R := rfl
  have hU : IsUnit (ctrFull p e H E ζ).det := isUnit_iff_ne_zero.mpr hM
  -- the Schur column formula
  have hcol : ∀ (w : ExteriorSite p e) (z : PairSite p e), A w.1 z.1 = -((N⁻¹ * C * R) w z) := by
    intro w z
    set u : p.Site → ℂ := fun y => A y z.1
    have hext : ∀ x : ExteriorSite p e, (ctrFull p e H E ζ *ᵥ u) x.1 = 0 := by
      intro x
      have : (ctrFull p e H E ζ *ᵥ u) x.1 = (ctrFull p e H E ζ * A) x.1 z.1 := by
        rw [Matrix.mul_apply]; rfl
      rw [this, hA, Matrix.mul_nonsing_inv _ hU, Matrix.one_apply_ne (ctr_ne_of_pair_ext z x).symm]
    obtain ⟨hue, -⟩ := ctr_schur_elim hH hdet ζ u hext
    have := congrFun hue w
    change u w.1 = _
    rw [this]
    simp only [Pi.neg_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rfl
  -- Hermitian exterior inverse
  have hNh : (N⁻¹)ᴴ = N⁻¹ := by
    have hext : (exteriorBlock p e H).IsHermitian := by
      ext x y
      simp only [Matrix.conjTranspose_apply, exteriorBlock]
      exact hH.apply x.1 y.1
    have hE1 : ((E : ℂ) • (1 : Matrix (ExteriorSite p e) (ExteriorSite p e) ℂ)).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
        Complex.conj_ofReal]
    exact (hext.sub hE1).inv.eq
  -- the trace
  set Dp : PairMatrix p e := Matrix.diagonal (fun x : PairSite p e => ((scnInd g x.1 : ℝ) : ℂ))
  set De : Matrix (ExteriorSite p e) (ExteriorSite p e) ℂ :=
    Matrix.diagonal (fun x : ExteriorSite p e => ((scnInd g x.1 : ℝ) : ℂ))
  have hB : tgtB p e g H E = Dp + Cᴴ * N⁻¹ * De * N⁻¹ * C := by
    unfold tgtB
    rw [scn_pairBlock_projector, scn_exteriorBlock_projector]
  have htr : (Rᴴ * tgtB p e g H E * R).trace =
      (Rᴴ * Dp * R).trace + ((N⁻¹ * C * R)ᴴ * De * (N⁻¹ * C * R)).trace := by
    rw [hB, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
    congr 1
    simp only [Matrix.conjTranspose_mul, hNh, Matrix.mul_assoc]
  unfold tgtLambda
  rw [hR0, htr, scn_trace_conj_diag_mul, scn_trace_conj_diag_mul, scn_scnHS_blk_eq]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun y : p.Site => y.1 = e ∨ y.1 = e + 1)]
  push_cast
  congr 2
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [hcol w z, Complex.normSq_neg]

/-- `tgtTraceCLM` of a product through `P_g` is a block trace of block products. -/
theorem scn_traceCLM_projector (A B : p.SiteMatrix) (g k : ZMod p.n) :
    tgtTraceCLM e k (A * pairProjector p g * B) =
      pairBlockTrace p e (scnBlk A e g * scnBlk B g e) k := by
  change (p.W : ℂ)⁻¹ * ∑ x : PairSite p e, (if x.1.1 = k then (A * pairProjector p g * B) x.1 x.1
    else 0) = _
  unfold pairBlockTrace
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ctr_mul_projector_mul_apply]
  rfl

/-- `tgtTraceCLM` of a site matrix is the block trace of its pair block. -/
theorem scn_traceCLM_eq (A : p.SiteMatrix) (k : ZMod p.n) :
    tgtTraceCLM e k A = pairBlockTrace p e (scnBlk A e e) k := rfl

end Tagged

end BlockBand.Center
