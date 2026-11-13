module

public import BlockBand.Critical.RelativeVectors.Statement

/-!
# The bounded-`C²` norm of `exp(-Σ φ(x_m, L z_m))`

Marks `z ∈ MarkArray n r = (ℂ^r)^n` carry real derivatives and the sup product norm (the norm of
`IsC2Bounded`); `L ∈ ℂ^{r×r}` acts on each mark, `matCLM L : ℂ^r →L[ℝ] ℂ^r`.

* `norm_mulVec_le`: `‖Az‖ ≤ r β ‖z‖` (sup norms) if `|A_{ij}| ≤ β`; `norm_matCLM_le`.
* `isC2Bounded_expSum`: if every `g_m ≥ 0` is bounded `C²` with bound `K` on `ℂ^r` and
  `‖matCLM L‖ ≤ B`, then `z ↦ (expSumConst n K B)⁻¹ exp(-Σ_m g_m(L z_m))` is bounded `C²` with
  bound `1`, where `expSumConst n K B = 2((nK + 1)(B + 1))²` (Faà di Bruno bound
  `norm_iteratedFDeriv_comp_le`, `‖D^i(g_m ∘ L ∘ π_m)‖ ≤ K B^i`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Matrix

variable {r : ℕ}

/-- `z ↦ L z` on `ℂ^r`, as a real continuous linear map. -/
def matCLM (L : Matrix (Fin r) (Fin r) ℂ) : (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) :=
  LinearMap.toContinuousLinearMap ((Matrix.mulVecLin L).restrictScalars ℝ)

@[simp] theorem matCLM_apply (L : Matrix (Fin r) (Fin r) ℂ) (z : Fin r → ℂ) :
    matCLM L z = L *ᵥ z := rfl

/-- `‖Az‖ ≤ rβ‖z‖` in the sup norm when every entry of `A` has modulus `≤ β`. -/
theorem norm_mulVec_le (A : Matrix (Fin r) (Fin r) ℂ) {β : ℝ} (hβ : 0 ≤ β)
    (hA : ∀ i j, ‖A i j‖ ≤ β) (z : Fin r → ℂ) : ‖A *ᵥ z‖ ≤ r * β * ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Matrix.mulVec, dotProduct]
  calc ‖∑ j, A i j * z j‖ ≤ ∑ _j : Fin r, β * ‖z‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          exact mul_le_mul (hA i j) (norm_le_pi_norm z j) (norm_nonneg _) hβ)
    _ = r * β * ‖z‖ := by simp; ring

theorem norm_matCLM_le (A : Matrix (Fin r) (Fin r) ℂ) {β : ℝ} (hβ : 0 ≤ β)
    (hA : ∀ i j, ‖A i j‖ ≤ β) : ‖matCLM A‖ ≤ r * β :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_mulVec_le A hβ hA)

/-- `z ↦ L z_m` on `(ℂ^r)^n`. -/
def markProj {n : ℕ} (L : Matrix (Fin r) (Fin r) ℂ) (m : Fin n) :
    MarkArray n r →L[ℝ] (Fin r → ℂ) :=
  (matCLM L).comp (ContinuousLinearMap.proj m)

@[simp] theorem markProj_apply {n : ℕ} (L : Matrix (Fin r) (Fin r) ℂ) (m : Fin n)
    (z : MarkArray n r) : markProj L m z = L *ᵥ z m := rfl

theorem norm_markProj_le {n : ℕ} (L : Matrix (Fin r) (Fin r) ℂ) (m : Fin n) :
    ‖markProj L m‖ ≤ ‖matCLM L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z =>
    ((matCLM L).le_opNorm (z m)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm z m) (norm_nonneg _))

/-- The chain-rule constant `M(n, K, B) = 2((nK + 1)(B + 1))²`. -/
def expSumConst (n : ℕ) (K B : ℝ) : ℝ := 2 * (((n : ℝ) * K + 1) * (B + 1)) ^ 2

theorem IsC2Bounded.nonneg {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {K : ℝ}
    {f : X → ℝ} (hf : IsC2Bounded K f) : 0 ≤ K :=
  (abs_nonneg _).trans (hf.bound 0)

theorem norm_iteratedFDeriv_le_of_isC2Bounded {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {K : ℝ} {f : X → ℝ} (hf : IsC2Bounded K f) (z : X) {i : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i ≤ 2) : ‖iteratedFDeriv ℝ i f z‖ ≤ K := by
  interval_cases i
  · rw [norm_iteratedFDeriv_one]; exact hf.deriv_bound z
  · exact hf.hessian_bound z

/-- **Chain-rule `C²` bound.** If every `g_m ≥ 0` (`m < n`) is bounded `C²` with bound `K` on
`ℂ^r` and `‖matCLM L‖ ≤ B`, then `z ↦ M⁻¹ exp(-Σ_m g_m(L z_m))` on `(ℂ^r)^n`, with
`M = expSumConst n K B`, is bounded `C²` with bound `1`. -/
theorem isC2Bounded_expSum {n : ℕ} (g : Fin n → (Fin r → ℂ) → ℝ) {K B : ℝ}
    (hg : ∀ m, IsC2Bounded K (g m)) (hg0 : ∀ m w, 0 ≤ g m w) (L : Matrix (Fin r) (Fin r) ℂ)
    (hB : ‖matCLM L‖ ≤ B) :
    IsC2Bounded 1 (fun z : MarkArray n r =>
      (expSumConst n K B)⁻¹ * Real.exp (-∑ m, g m (L *ᵥ z m))) := by
  have hnK : 0 ≤ (n : ℝ) * K := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exact mul_nonneg (Nat.cast_nonneg _) (hg ⟨0, hn⟩).nonneg
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  set D : ℝ := ((n : ℝ) * K + 1) * (B + 1) with hD
  have hD1 : 1 ≤ D := by rw [hD]; nlinarith
  set M := expSumConst n K B with hM
  have hMD : M = 2 * D ^ 2 := rfl
  have hMpos : 0 < M := by rw [hMD]; positivity
  set h : MarkArray n r → ℝ := fun z => ∑ m, g m (markProj L m z) with hh
  set e : ℝ → ℝ := fun t => M⁻¹ * Real.exp (-1 * t) with he
  have hfun : (fun z : MarkArray n r => M⁻¹ * Real.exp (-∑ m, g m (L *ᵥ z m))) = e ∘ h := by
    funext z; simp [he, hh]
  have hgc : ∀ m, ContDiff ℝ 2 (fun z : MarkArray n r => g m (markProj L m z)) := fun m =>
    (hg m).contDiff.comp (markProj L m).contDiff
  have hhc : ContDiff ℝ 2 h := ContDiff.sum fun m _ => hgc m
  have hec : ContDiff ℝ 2 e := contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  have hh0 : ∀ z, 0 ≤ h z := fun z => Finset.sum_nonneg fun m _ => hg0 m _
  have hiter_e : ∀ i t, iteratedDeriv i e t = M⁻¹ * ((-1) ^ i * Real.exp (-1 * t)) := by
    intro i t
    rw [he, iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul]
  have hCe : ∀ z, ∀ i, i ≤ 2 → ‖iteratedFDeriv ℝ i e (h z)‖ ≤ M⁻¹ := by
    intro z i _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hiter_e, norm_mul, norm_mul, norm_pow,
      norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hMpos),
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (-1 * h z) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hh0 z])
    have hMi : 0 < M⁻¹ := inv_pos.2 hMpos
    nlinarith
  have hDh : ∀ z, ∀ i, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i h z‖ ≤ D ^ i := by
    intro z i hi1 hi2
    have hsum : iteratedFDeriv ℝ i h z =
        ∑ m, iteratedFDeriv ℝ i (fun z : MarkArray n r => g m (markProj L m z)) z := by
      rw [hh, iteratedFDeriv_sum (fun m _ => (hgc m).of_le (by exact_mod_cast hi2))]
      simp
    have hterm : ∀ m, ‖iteratedFDeriv ℝ i (fun z : MarkArray n r => g m (markProj L m z)) z‖ ≤
        K * B ^ i := by
      intro m
      have hcomp := (markProj L m).iteratedFDeriv_comp_right (hg m).contDiff z
        (i := i) (by exact_mod_cast hi2)
      change ‖iteratedFDeriv ℝ i (g m ∘ markProj L m) z‖ ≤ _
      rw [hcomp]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hP : ‖markProj L m‖ ≤ B := (norm_markProj_le L m).trans hB
      exact mul_le_mul (norm_iteratedFDeriv_le_of_isC2Bounded (hg m) _ hi1 hi2)
        (pow_le_pow_left₀ (norm_nonneg _) hP i) (by positivity) (hg m).nonneg
    rw [hsum]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun m _ => hterm m).trans ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    interval_cases i
    · rw [hD]; nlinarith
    · rw [hD]
      have hB1 : B ^ 2 ≤ (B + 1) ^ 2 := by nlinarith
      have h1 : (n : ℝ) * K ≤ ((n : ℝ) * K + 1) ^ 2 := by nlinarith
      calc (n : ℝ) * (K * B ^ 2) = ((n : ℝ) * K) * B ^ 2 := by ring
        _ ≤ ((n : ℝ) * K + 1) ^ 2 * (B + 1) ^ 2 :=
          mul_le_mul h1 hB1 (by positivity) (by positivity)
        _ = (((n : ℝ) * K + 1) * (B + 1)) ^ 2 := by ring
  have hcomp : ∀ z, ∀ i, i ≤ 2 → ‖iteratedFDeriv ℝ i (e ∘ h) z‖ ≤ i.factorial * M⁻¹ * D ^ i :=
    fun z i hi => norm_iteratedFDeriv_comp_le hec hhc (by exact_mod_cast hi) z
      (fun j hj => hCe z j (hj.trans hi)) (fun j hj1 hj2 => hDh z j hj1 (hj2.trans hi))
  have hMi : M⁻¹ = (2 * D ^ 2)⁻¹ := by rw [hMD]
  rw [hfun]
  refine ⟨hec.comp hhc, fun z => ?_, fun z => ?_, fun z => ?_⟩
  · have h0 := hcomp z 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
    refine h0.trans ?_
    rw [hMi]
    simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, mul_one]
    exact inv_le_one_of_one_le₀ (by nlinarith)
  · have h1 := hcomp z 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at h1
    refine h1.trans ?_
    rw [hMi]
    simp only [Nat.factorial_one, Nat.cast_one, pow_one, one_mul]
    rw [inv_mul_le_iff₀ (by positivity)]
    nlinarith
  · have h2 := hcomp z 2 le_rfl
    refine h2.trans ?_
    rw [hMi]
    simp only [Nat.factorial_two, Nat.cast_ofNat]
    have : (2 : ℝ) * D ^ 2 ≠ 0 := by positivity
    rw [mul_comm (2 : ℝ), mul_assoc, inv_mul_cancel₀ this]

end BlockBand.Critical.RelativeVectors
