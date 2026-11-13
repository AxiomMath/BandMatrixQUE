module

public import BlockBand.Endpoints.Response.TaggedConvexOrderWickMoment
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The second-order Wick coefficient along a Hermitian line

**Objects.** For square matrices `Q, H` over `ℂ`:
* `wg_pertTrace Q H r = Tr((Q + sH)^r) ∈ ℂ[s]` (`wg_eval_pertTrace`);
* its coefficients (`wg_pertTrace_coeff_zero/one/two`): `Tr Q^r`, `Tr A_r`, `Tr B_r`, where
  `A_r = Σ_{i<r} Q^i H Q^{r-1-i}` and `B_r = Σ_{i<r} Σ_{i<j<r} Q^i H Q^{j-i-1} H Q^{r-1-j}`
  (`wg_A_eq`, `wg_B_eq`).

**Results.**
* `wg_integrable_quadForm_pow_mul_pow`: `(h*Q h)^a (h*H h)^b` is integrable.
* `wg_coeff_two_wick`: for Hermitian `Q, H`, the `s²`-coefficient of
  `Σ_{π∈S_m} Π_c Tr (Q + sH)^{|c|}` is `C(m,2) E[(h*Qh)^{m-2} (h*Hh)²]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.CoareaPalm

variable {ι : Type} [Fintype ι]

/-!
## The Hermitian Wick formula
-/

/-- **Wick for Hermitian matrices**: `E_h (h*Mh)^m = Σ_{π∈S_m} Π_{c} Tr M^{|c|}`. -/
theorem wg_wickMoment_hermitian [DecidableEq ι] (m : ℕ) {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    ((∫ h, quadForm M h ^ m ∂circularVectorLaw ι : ℝ) : ℂ) =
      ∑ π : Equiv.Perm (Fin m), (π.partition.parts.map fun r => (M ^ r).trace).prod := by
  set lam := hM.eigenvalues
  rw [wk_integral_quadForm_pow_eq m hM]
  have hexp : ∀ g : ι → ℂ, (∑ i, lam i * Complex.normSq (g i)) ^ m =
      ∑ f : Fin m → ι, (∏ a, lam (f a)) * ∏ i, Complex.normSq (g i) ^ wk_fib f i :=
    fun g => wk_sum_pow_eq m lam _
  have hint : ∀ f : Fin m → ι, Integrable
      (fun g : ι → ℂ => (∏ a, lam (f a)) * ∏ i, Complex.normSq (g i) ^ wk_fib f i)
      (circularVectorLaw ι) := by
    intro f
    refine Integrable.const_mul (Integrable.of_integral_ne_zero ?_) _
    rw [wk_integral_prod_normSq_pow]
    exact Finset.prod_ne_zero_iff.2 fun a _ => by positivity
  rw [integral_congr_ae (ae_of_all _ hexp), integral_finsetSum _ fun f _ => hint f]
  rw [Finset.sum_congr rfl fun f _ => by rw [integral_const_mul, wk_integral_prod_normSq_pow]]
  have htr : ∀ r, (M ^ r).trace = ∑ i, ((lam i : ℝ) : ℂ) ^ r := fun r => ns_trace_pow M hM r
  rw [show (fun r => (M ^ r).trace) = (fun r => ∑ i, ((lam i : ℝ) : ℂ) ^ r) from funext htr,
    wk_sum_perm_parts_eq (fun i => ((lam i : ℝ) : ℂ))]
  push_cast
  rfl

/-!
## Integrability of quadratic-form monomials
-/

/-- `N(h) = Σ_a |h_a|²`. -/
def wg_normSq (h : ι → ℂ) : ℝ := ∑ a, Complex.normSq (h a)

theorem wg_integrable_normSq_pow [DecidableEq ι] (n : ℕ) :
    Integrable (fun h : ι → ℂ => wg_normSq h ^ n) (circularVectorLaw ι) := by
  have hexp : ∀ h : ι → ℂ, wg_normSq h ^ n =
      ∑ f : Fin n → ι, (∏ a, (fun _ => (1 : ℝ)) (f a)) * ∏ i, Complex.normSq (h i) ^ wk_fib f i := by
    intro h
    rw [← wk_sum_pow_eq n (fun _ => (1 : ℝ))]
    simp [wg_normSq]
  simp_rw [hexp]
  refine integrable_finsetSum _ fun f _ => ?_
  refine Integrable.const_mul (Integrable.of_integral_ne_zero ?_) _
  rw [wk_integral_prod_normSq_pow]
  exact Finset.prod_ne_zero_iff.2 fun a _ => by positivity

theorem wg_norm_mul_norm_le (h : ι → ℂ) (a b : ι) : ‖h a‖ * ‖h b‖ ≤ wg_normSq h := by
  have ha : ‖h a‖ ^ 2 ≤ wg_normSq h := by
    rw [Complex.sq_norm]
    exact Finset.single_le_sum (f := fun c => Complex.normSq (h c))
      (fun c _ => Complex.normSq_nonneg _) (Finset.mem_univ a)
  have hb : ‖h b‖ ^ 2 ≤ wg_normSq h := by
    rw [Complex.sq_norm]
    exact Finset.single_le_sum (f := fun c => Complex.normSq (h c))
      (fun c _ => Complex.normSq_nonneg _) (Finset.mem_univ b)
  nlinarith [two_mul_le_add_sq ‖h a‖ ‖h b‖]

theorem wg_dotProduct_mulVec_eq (M : Matrix ι ι ℂ) (h : ι → ℂ) :
    star h ⬝ᵥ (M *ᵥ h) = ∑ a, ∑ b, star (h a) * (M a b * h b) := by
  simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]

theorem wg_abs_quadForm_le (M : Matrix ι ι ℂ) (h : ι → ℂ) :
    |quadForm M h| ≤ (∑ a, ∑ b, ‖M a b‖) * wg_normSq h := by
  unfold quadForm
  rw [wg_dotProduct_mulVec_eq]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [norm_mul, norm_mul, norm_star]
  calc ‖h a‖ * (‖M a b‖ * ‖h b‖) = ‖M a b‖ * (‖h a‖ * ‖h b‖) := by ring
    _ ≤ ‖M a b‖ * wg_normSq h :=
        mul_le_mul_of_nonneg_left (wg_norm_mul_norm_le h a b) (norm_nonneg _)

theorem wg_continuous_quadForm (M : Matrix ι ι ℂ) :
    Continuous (fun h : ι → ℂ => quadForm M h) :=
  tco_continuous_quadForm.comp (continuous_const.prodMk continuous_id)

/-- `(h*Q h)^a (h*H h)^b` is integrable under the circular law. -/
theorem wg_integrable_quadForm_pow_mul_pow [DecidableEq ι] (Q H : Matrix ι ι ℂ) (a b : ℕ) :
    Integrable (fun h => quadForm Q h ^ a * quadForm H h ^ b) (circularVectorLaw ι) := by
  set c₁ := ∑ x, ∑ y, ‖Q x y‖
  set c₂ := ∑ x, ∑ y, ‖H x y‖
  refine Integrable.mono' ((wg_integrable_normSq_pow (a + b)).const_mul (c₁ ^ a * c₂ ^ b))
    (((wg_continuous_quadForm Q).pow a).mul ((wg_continuous_quadForm H).pow b)).aestronglyMeasurable
    (ae_of_all _ fun h => ?_)
  have hN : 0 ≤ wg_normSq h := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow, pow_add]
  calc |quadForm Q h| ^ a * |quadForm H h| ^ b
      ≤ (c₁ * wg_normSq h) ^ a * (c₂ * wg_normSq h) ^ b := by
        gcongr
        · exact wg_abs_quadForm_le Q h
        · exact wg_abs_quadForm_le H h
    _ = c₁ ^ a * c₂ ^ b * (wg_normSq h ^ a * wg_normSq h ^ b) := by ring

/-!
## The perturbed trace `Tr (Q + sH)^r` as a polynomial in `s`
-/

/-- `A_{r+1} = A_r Q + Q^r H`, `A_0 = 0` (the coefficient of `s` in `(Q + sH)^r`). -/
def wg_A [DecidableEq ι] (Q H : Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => 0
  | r + 1 => wg_A Q H r * Q + Q ^ r * H

/-- `B_{r+1} = B_r Q + A_r H`, `B_0 = 0` (the coefficient of `s²` in `(Q + sH)^r`). -/
def wg_B [DecidableEq ι] (Q H : Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => 0
  | r + 1 => wg_B Q H r * Q + wg_A Q H r * H

/-- `Q + sH` over `ℂ[s]`. -/
def wg_pertMat [DecidableEq ι] (Q H : Matrix ι ι ℂ) : Matrix ι ι (Polynomial ℂ) :=
  Q.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • H.map Polynomial.C

/-- `Tr (Q + sH)^r ∈ ℂ[s]`. -/
def wg_pertTrace [DecidableEq ι] (Q H : Matrix ι ι ℂ) (r : ℕ) : Polynomial ℂ := ((wg_pertMat Q H) ^ r).trace

theorem wg_pertMat_pow [DecidableEq ι] (Q H : Matrix ι ι ℂ) (r : ℕ) :
    ∃ R : Matrix ι ι (Polynomial ℂ), wg_pertMat Q H ^ r =
      (Q ^ r).map Polynomial.C + (Polynomial.X : Polynomial ℂ) • (wg_A Q H r).map Polynomial.C +
        (Polynomial.X : Polynomial ℂ) ^ 2 • (wg_B Q H r).map Polynomial.C +
          (Polynomial.X : Polynomial ℂ) ^ 3 • R := by
  induction r with
  | zero =>
    refine ⟨0, ?_⟩
    have e : (1 : Matrix ι ι ℂ).map Polynomial.C =
        RingHom.mapMatrix (m := ι) (Polynomial.C : ℂ →+* Polynomial ℂ) 1 := rfl
    simp [wg_A, wg_B, e, map_one]
  | succ r ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨(wg_B Q H r * H).map Polynomial.C + R * wg_pertMat Q H, ?_⟩
    set φ := RingHom.mapMatrix (m := ι) (Polynomial.C : ℂ →+* Polynomial ℂ)
    have e : ∀ A : Matrix ι ι ℂ, A.map Polynomial.C = φ A := fun _ => rfl
    rw [pow_succ (wg_pertMat Q H), hR, wg_A, wg_B, pow_succ Q r]
    unfold wg_pertMat
    simp only [e, map_add, map_mul]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    module

theorem wg_coeff_trace (N : Matrix ι ι (Polynomial ℂ)) (n : ℕ) :
    N.trace.coeff n = (N.map fun p => p.coeff n).trace := by
  unfold Matrix.trace
  rw [Polynomial.finsetSum_coeff]
  rfl

theorem wg_pertTrace_coeff [DecidableEq ι] (Q H : Matrix ι ι ℂ) (r n : ℕ) (hn : n < 3) :
    (wg_pertTrace Q H r).coeff n =
      if n = 0 then (Q ^ r).trace else if n = 1 then (wg_A Q H r).trace else (wg_B Q H r).trace := by
  obtain ⟨R, hR⟩ := wg_pertMat_pow Q H r
  unfold wg_pertTrace
  rw [hR, wg_coeff_trace]
  interval_cases n <;> simp [Matrix.trace, Polynomial.coeff_C, Polynomial.coeff_X_pow_mul']

theorem wg_pertTrace_coeff_zero [DecidableEq ι] (Q H : Matrix ι ι ℂ) (r : ℕ) :
    (wg_pertTrace Q H r).coeff 0 = (Q ^ r).trace := by
  rw [wg_pertTrace_coeff Q H r 0 (by norm_num)]; simp

theorem wg_pertTrace_coeff_one [DecidableEq ι] (Q H : Matrix ι ι ℂ) (r : ℕ) :
    (wg_pertTrace Q H r).coeff 1 = (wg_A Q H r).trace := by
  rw [wg_pertTrace_coeff Q H r 1 (by norm_num)]; simp

theorem wg_pertTrace_coeff_two [DecidableEq ι] (Q H : Matrix ι ι ℂ) (r : ℕ) :
    (wg_pertTrace Q H r).coeff 2 = (wg_B Q H r).trace := by
  rw [wg_pertTrace_coeff Q H r 2 (by norm_num)]; simp

theorem wg_eval_pertTrace [DecidableEq ι] (Q H : Matrix ι ι ℂ) (r : ℕ) (z : ℂ) :
    (wg_pertTrace Q H r).eval z = ((Q + z • H) ^ r).trace := by
  unfold wg_pertTrace
  have h1 := AddMonoidHom.map_trace (Polynomial.evalRingHom z) (wg_pertMat Q H ^ r)
  have h2 := Matrix.map_pow (wg_pertMat Q H) (Polynomial.evalRingHom z) r
  rw [Polynomial.coe_evalRingHom] at h1 h2
  rw [h1, h2]
  congr 2
  ext i j
  simp only [wg_pertMat, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-!
## Closed forms of `A_r`, `B_r`
-/

theorem wg_A_eq [DecidableEq ι] (Q H : Matrix ι ι ℂ) (r : ℕ) :
    wg_A Q H r = ∑ i ∈ range r, Q ^ i * H * Q ^ (r - 1 - i) := by
  induction r with
  | zero => simp [wg_A]
  | succ r ih =>
    rw [wg_A, ih, Finset.sum_mul, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < r := Finset.mem_range.1 hi
    rw [mul_assoc, ← pow_succ, show r - 1 - i + 1 = r - i by omega]

theorem wg_B_eq [DecidableEq ι] (Q H : Matrix ι ι ℂ) (r : ℕ) :
    wg_B Q H r = ∑ i ∈ range r, ∑ j ∈ Ioo i r,
      Q ^ i * H * Q ^ (j - i - 1) * H * Q ^ (r - 1 - j) := by
  induction r with
  | zero => simp [wg_B]
  | succ r ih =>
    have he : Ioo r (r + 1) = ∅ := by ext x; simp
    rw [wg_B, ih, wg_A_eq, Finset.sum_mul, Finset.sum_mul, Finset.sum_range_succ,
      he, Finset.sum_empty, add_zero, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < r := Finset.mem_range.1 hi
    rw [← Finset.Ico_add_one_left_eq_Ioo, ← Finset.Ico_add_one_left_eq_Ioo, Finset.sum_Ico_succ_top (by omega),
      Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < r := (Finset.mem_Ico.1 hj).2
      rw [mul_assoc _ (Q ^ (r - 1 - j)), ← pow_succ, show r - 1 - j + 1 = r + 1 - 1 - j by omega]
    · rw [show r + 1 - 1 - r = 0 by omega, pow_zero, mul_one, show r - i - 1 = r - 1 - i by omega]

/-!
## The `s²`-coefficient
-/

theorem wg_quadForm_add_smul (Q H : Matrix ι ι ℂ) (s : ℝ) (h : ι → ℂ) :
    quadForm (Q + (s : ℂ) • H) h = s * quadForm H h + quadForm Q h := by
  unfold quadForm
  rw [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, Complex.add_re, smul_eq_mul,
    Complex.re_ofReal_mul]
  ring

omit [Fintype ι] in
theorem wg_isHermitian_add_smul {Q H : Matrix ι ι ℂ} (hQ : Q.IsHermitian) (hH : H.IsHermitian)
    (s : ℝ) : (Q + (s : ℂ) • H).IsHermitian := by
  refine hQ.add ?_
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hH, Complex.star_def, Complex.conj_ofReal]

/-- **The `s²`-coefficient of the Wick polynomial along a Hermitian line**: for Hermitian `Q, H`,
`[s²] Σ_{π∈S_m} Π_c Tr (Q + sH)^{|c|} = C(m,2) E[(h*Qh)^{m-2}(h*Hh)²]`. -/
theorem wg_coeff_two_wick [DecidableEq ι] (m : ℕ) {Q H : Matrix ι ι ℂ} (hQ : Q.IsHermitian) (hH : H.IsHermitian) :
    (∑ π : Equiv.Perm (Fin m), (π.partition.parts.map fun r => wg_pertTrace Q H r).prod).coeff 2 =
      (((m.choose 2 : ℝ) * ∫ h, quadForm Q h ^ (m - 2) * quadForm H h ^ 2
        ∂circularVectorLaw ι : ℝ) : ℂ) := by
  set c : ℕ → ℂ := fun j => (((m.choose j : ℝ) * ∫ h, quadForm Q h ^ (m - j) * quadForm H h ^ j
    ∂circularVectorLaw ι : ℝ) : ℂ)
  set q : Polynomial ℂ := ∑ j ∈ range (m + 1), Polynomial.C (c j) * Polynomial.X ^ j
  have hpq : (∑ π : Equiv.Perm (Fin m),
      (π.partition.parts.map fun r => wg_pertTrace Q H r).prod) = q := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective Complex.ofReal_injective)
    rintro _ ⟨s, rfl⟩
    simp only [Set.mem_ofPred_eq, Polynomial.eval_finsetSum, Polynomial.eval_multiset_prod,
      Multiset.map_map, Function.comp_def, wg_eval_pertTrace, q, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← wg_wickMoment_hermitian m (wg_isHermitian_add_smul hQ hH s)]
    simp_rw [wg_quadForm_add_smul, add_pow]
    rw [integral_finsetSum _ fun j _ => ?_]
    · push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [c, mul_pow]
      rw [show (fun h => s ^ j * quadForm H h ^ j * quadForm Q h ^ (m - j) * (m.choose j : ℝ)) =
        fun h => (s ^ j * (m.choose j : ℝ)) * (quadForm Q h ^ (m - j) * quadForm H h ^ j) from
          funext fun h => by ring, integral_const_mul]
      push_cast
      ring
    · simp only [mul_pow]
      exact ((wg_integrable_quadForm_pow_mul_pow Q H (m - j) j).const_mul
        (s ^ j * (m.choose j : ℝ))).congr (ae_of_all _ fun h => by simp only; ring)
  rw [hpq]
  simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h2
  · rfl
  · have hm : m < 2 := by simp at h2; omega
    simp [Nat.choose_eq_zero_of_lt hm]

end BlockBand.Endpoints
