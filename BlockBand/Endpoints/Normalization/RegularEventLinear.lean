module

public import BlockBand.Internal.Contracts.CoareaPalm

/-!
# Regular prior event: entrywise norms and the real-gap resolvent

We collect the deterministic finite linear algebra used for the norm event of the regular prior
event:
* `regularEventEnt M = Σ_{a,b} |M_ab|` (entrywise `ℓ¹`), with `l2Norm (M *ᵥ x) ≤ ent M · l2Norm x`
  (`regularEvent_l2Norm_mulVec_le`), submultiplicativity, adjoint and reindex invariance.
* `regularEvent_spectral_lower`: Hermitian `A` whose eigenvalues all satisfy `ε ≤ |λ_j - e|`
  has `ε ‖y‖ ≤ ‖(A - e) y‖` for every `y` (orthonormal eigenbasis, Parseval).
* `regularEvent_norm_inv_entry_le`: if `ε ‖y‖ ≤ ‖M y‖` for all `y` with `ε > 0`, then every entry
  of `M⁻¹` is at most `ε⁻¹`, hence `ent M⁻¹ ≤ d² ε⁻¹` (`d` the dimension;
  `regularEventEnt_le_card_sq_mul`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexConjugate InnerProductSpace

section Ent

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

/-- The entrywise `ℓ¹` norm `Σ_{a,b} |M_ab|`. -/
def regularEventEnt (M : Matrix ι κ ℂ) : ℝ := ∑ a, ∑ b, ‖M a b‖

theorem regularEventEnt_nonneg (M : Matrix ι κ ℂ) : 0 ≤ regularEventEnt M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem regularEvent_norm_entry_le_ent (M : Matrix ι κ ℂ) (a : ι) (b : κ) :
    ‖M a b‖ ≤ regularEventEnt M := by
  unfold regularEventEnt
  refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ b, ‖M a b‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))
  exact Finset.single_le_sum (f := fun b => ‖M a b‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ b)

theorem regularEventEnt_sub_le (M N : Matrix ι κ ℂ) :
    regularEventEnt (M - N) ≤ regularEventEnt M + regularEventEnt N := by
  unfold regularEventEnt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun b _ => norm_sub_le _ _

theorem regularEventEnt_add_le (M N : Matrix ι κ ℂ) :
    regularEventEnt (M + N) ≤ regularEventEnt M + regularEventEnt N := by
  unfold regularEventEnt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun b _ => norm_add_le _ _

theorem regularEventEnt_neg (M : Matrix ι κ ℂ) : regularEventEnt (-M) = regularEventEnt M := by
  simp [regularEventEnt]

theorem regularEventEnt_conjTranspose (M : Matrix ι κ ℂ) :
    regularEventEnt Mᴴ = regularEventEnt M := by
  unfold regularEventEnt
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

theorem regularEventEnt_mul_le (M : Matrix ι κ ℂ) (N : Matrix κ μ ℂ) :
    regularEventEnt (M * N) ≤ regularEventEnt M * regularEventEnt N := by
  unfold regularEventEnt
  calc ∑ a, ∑ b, ‖(M * N) a b‖ ≤ ∑ a, ∑ b, ∑ c, ‖M a c‖ * ‖N c b‖ := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ ∑ a, ∑ b, ∑ c, ‖M a c‖ * ∑ c', ‖N c' b‖ := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          Finset.sum_le_sum fun c _ => ?_
        exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun c' => ‖N c' b‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ c)) (norm_nonneg _)
    _ = (∑ a, ∑ c, ‖M a c‖) * ∑ c', ∑ b, ‖N c' b‖ := by
        rw [Finset.sum_comm (f := fun c' b => ‖N c' b‖), Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm

theorem regularEventEnt_submatrix_equiv {ι' κ' : Type*} [Fintype ι'] [Fintype κ']
    (M : Matrix ι κ ℂ) (f : ι' ≃ ι) (g : κ' ≃ κ) :
    regularEventEnt (M.submatrix f g) = regularEventEnt M := by
  unfold regularEventEnt
  simp only [Matrix.submatrix_apply]
  rw [Equiv.sum_comp f (fun a => ∑ b, ‖M a (g b)‖)]
  exact Finset.sum_congr rfl fun a _ => Equiv.sum_comp g (fun b => ‖M a b‖)

theorem regularEvent_norm_le_l2Norm (x : ι → ℂ) (a : ι) : ‖x a‖ ≤ l2Norm x := by
  unfold l2Norm
  rw [← Real.sqrt_sq (norm_nonneg (x a))]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun k => ‖x k‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ a))

theorem regularEvent_l2Norm_le_sum (x : ι → ℂ) : l2Norm x ≤ ∑ a, ‖x a‖ := by
  unfold l2Norm
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  have h : ∀ a ∈ (Finset.univ : Finset ι), 0 ≤ ‖x a‖ := fun _ _ => norm_nonneg _
  calc ∑ k, ‖x k‖ ^ 2 ≤ (∑ k, ‖x k‖) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg h
    _ = _ := rfl

/-- `‖M x‖ ≤ (Σ |M_ab|) ‖x‖`. -/
theorem regularEvent_l2Norm_mulVec_le (M : Matrix ι κ ℂ) (x : κ → ℂ) :
    l2Norm (M *ᵥ x) ≤ regularEventEnt M * l2Norm x := by
  refine (regularEvent_l2Norm_le_sum _).trans ?_
  unfold regularEventEnt
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_mul]
  unfold Matrix.mulVec dotProduct
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (regularEvent_norm_le_l2Norm x b) (norm_nonneg _)

theorem regularEvent_l2Norm_comp_equiv {ι' : Type*} [Fintype ι'] (f : ι' ≃ ι) (x : ι → ℂ) :
    l2Norm (x ∘ f) = l2Norm x := by
  unfold l2Norm
  congr 1
  exact Equiv.sum_comp f (fun k => ‖x k‖ ^ 2)

theorem regularEventEnt_le_card_sq_mul {M : Matrix ι ι ℂ} {K : ℝ} (hK : ∀ a b, ‖M a b‖ ≤ K) :
    regularEventEnt M ≤ (Fintype.card ι : ℝ) ^ 2 * K := by
  unfold regularEventEnt
  calc ∑ a, ∑ b, ‖M a b‖ ≤ ∑ _a : ι, ∑ _b : ι, K :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hK a b
    _ = _ := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Ent

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem regularEvent_l2Norm_eq (y : ι → ℂ) :
    l2Norm y = ‖(WithLp.toLp 2 y : EuclideanSpace ℂ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  rfl

/-- **Real-gap lower bound.** If every eigenvalue of the Hermitian `A` is at distance at least
`ε ≥ 0` from `e`, then `ε ‖y‖ ≤ ‖(A - e) y‖`. -/
theorem regularEvent_spectral_lower {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {e ε : ℝ}
    (hε : 0 ≤ ε) (hgap : ∀ j, ε ≤ |hA.eigenvalues j - e|) (y : ι → ℂ) :
    ε * l2Norm y ≤ l2Norm ((A - (e : ℂ) • 1) *ᵥ y) := by
  set w := hA.eigenvectorBasis
  set M : Matrix ι ι ℂ := A - (e : ℂ) • 1
  have hM : M.IsHermitian := by
    refine hA.sub ?_
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  have hT : (toEuclideanLin M).IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hM
  set x : EuclideanSpace ℂ ι := WithLp.toLp 2 y
  have hTx : toEuclideanLin M x = WithLp.toLp 2 (M *ᵥ y) := rfl
  have hTw : ∀ j, toEuclideanLin M (w j) = ((hA.eigenvalues j - e : ℝ) : ℂ) • w j := by
    intro j
    have h := hA.mulVec_eigenvectorBasis j
    change WithLp.toLp 2 (M *ᵥ WithLp.ofLp (w j)) = _
    have : M *ᵥ WithLp.ofLp (w j) = ((hA.eigenvalues j - e : ℝ) : ℂ) • WithLp.ofLp (w j) := by
      simp only [M, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [show A *ᵥ WithLp.ofLp (w j) = (hA.eigenvalues j) • WithLp.ofLp (w j) from h]
      ext k
      simp [Pi.smul_apply, sub_mul, Complex.real_smul]
    rw [this]
    rfl
  have hrepr : ∀ j, w.repr (toEuclideanLin M x) j =
      ((hA.eigenvalues j - e : ℝ) : ℂ) * w.repr x j := by
    intro j
    rw [w.repr_apply_apply, w.repr_apply_apply, ← hT (w j) x, hTw j, inner_smul_left,
      Complex.conj_ofReal]
  have hpars : ∀ v : EuclideanSpace ℂ ι, ‖v‖ ^ 2 = ∑ j, ‖w.repr v j‖ ^ 2 := by
    intro v
    rw [← w.repr.norm_map v, EuclideanSpace.norm_sq_eq]
  have hsq : (ε * ‖x‖) ^ 2 ≤ ‖toEuclideanLin M x‖ ^ 2 := by
    rw [mul_pow, hpars x, hpars (toEuclideanLin M x), Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hrepr j, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h1 : ε ^ 2 ≤ (hA.eigenvalues j - e) ^ 2 := by
      have := hgap j
      nlinarith [abs_nonneg (hA.eigenvalues j - e), sq_abs (hA.eigenvalues j - e)]
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  rw [regularEvent_l2Norm_eq, regularEvent_l2Norm_eq, ← hTx]
  have h2 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (mul_nonneg hε (norm_nonneg x)), Real.sqrt_sq (norm_nonneg _)] at h2

omit [DecidableEq ι] in
/-- Lower bounds transfer along a reindexing. -/
theorem regularEvent_lower_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ] (f : κ ≃ ι)
    {M : Matrix ι ι ℂ} {ε : ℝ} (h : ∀ y, ε * l2Norm y ≤ l2Norm (M *ᵥ y)) (y : κ → ℂ) :
    ε * l2Norm y ≤ l2Norm (M.submatrix f f *ᵥ y) := by
  rw [Matrix.submatrix_mulVec_equiv, regularEvent_l2Norm_comp_equiv]
  have := h (y ∘ f.symm)
  rwa [regularEvent_l2Norm_comp_equiv] at this

/-- **Inverse entries from a lower bound.** If `ε ‖y‖ ≤ ‖M y‖` for all `y`, `ε > 0`, then `M`
is invertible and every entry of `M⁻¹` is at most `ε⁻¹`. -/
theorem regularEvent_norm_inv_entry_le {M : Matrix ι ι ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ y, ε * l2Norm y ≤ l2Norm (M *ᵥ y)) (a b : ι) : ‖M⁻¹ a b‖ ≤ ε⁻¹ := by
  have hdet : M.det ≠ 0 := by
    intro hd
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    have h1 := h v
    rw [hMv] at h1
    have h0 : l2Norm (0 : ι → ℂ) = 0 := by simp [l2Norm]
    rw [h0] at h1
    have hpos : 0 < l2Norm v := by
      obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
      have := regularEvent_norm_le_l2Norm v k
      have : 0 < ‖v k‖ := norm_pos_iff.mpr hk
      linarith
    nlinarith
  set y : ι → ℂ := M⁻¹ *ᵥ Pi.single b 1
  have hMy : M *ᵥ y = Pi.single b 1 := by
    simp only [y, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have h1 := h y
  rw [hMy] at h1
  have hs : l2Norm (Pi.single b (1 : ℂ) : ι → ℂ) = 1 := by
    unfold l2Norm
    rw [Finset.sum_eq_single b (fun k _ hk => by simp [hk]) (by simp)]
    simp
  rw [hs] at h1
  have hya : M⁻¹ a b = y a := by
    simp [y]
  rw [hya]
  calc ‖y a‖ ≤ l2Norm y := regularEvent_norm_le_l2Norm y a
    _ = ε⁻¹ * (ε * l2Norm y) := by field_simp
    _ ≤ ε⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hε.le)
    _ = ε⁻¹ := mul_one _

end Spectral

end BlockBand.Endpoints.Normalization
