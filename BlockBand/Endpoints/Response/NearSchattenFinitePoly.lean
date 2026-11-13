module

public import BlockBand.Endpoints.Response.NearSchattenFiniteAlgebra

/-!
# `C²` polynomial approximation of `f_ε` and the generator comparison

Part of the proof of the near-Schatten decay theorem: polynomial approximation through the
derivatives on a trace stop. Deterministic.

* `nsf_hasDerivAt_polyFun`, `nsf_hasDerivAt_polyD1`: `π' = nsfPolyD1`, `π'' = nsfPolyD2`.
* `nsf_exists_poly_approx` (**C² Weierstrass with `π(0) = 0`**): for `L ≥ 0`, `δ > 0` there is
  `π(x) = Σ_r a_r x^{r+1}` with, on `[0, L]`, `|π - f_ε| ≤ δx`, `|π' - f_ε'| ≤ δ` and
  `|DD π' - DD f_ε'| ≤ δ` (both points in `[0, L]`). The paper asks three derivatives; two suffice
  for the spectral generator, whose divided differences only involve `f'` and `f''`.
* `nsf_specGen_sub_le` (**generator comparison**): with `λ_i ∈ [0, L]`, `s_j ∈ [0, 1]`,
  `g, D ≥ 0`: `|𝒢_π - 𝒢_f| ≤ (D/2) δ (g Σλ + (Σλ)²)`.
* `nsf_sum_regFun_sub_le`: `|Σ_i π(λ_i) - Σ_i f_ε(λ_i)| ≤ δ Σ_i λ_i` (no rank factor).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Finset Set

theorem nsf_hasDerivAt_polyFun (a : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    HasDerivAt (nsfPolyFun a N) (nsfPolyD1 a N x) x := by
  unfold nsfPolyFun nsfPolyD1
  have h := HasDerivAt.fun_sum (u := range N) (A := fun r y => a r * y ^ (r + 1))
    (A' := fun r => a r * (r + 1) * x ^ r) (x := x) fun r _ => by
      have := (hasDerivAt_pow (r + 1) x).const_mul (a r)
      convert this using 1
      push_cast; ring
  exact h

theorem nsf_hasDerivAt_polyD1 (a : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    HasDerivAt (nsfPolyD1 a N) (nsfPolyD2 a N x) x := by
  unfold nsfPolyD1 nsfPolyD2
  have h := HasDerivAt.fun_sum (u := range N) (A := fun r y => a r * (r + 1) * y ^ r)
    (A' := fun r => a r * (r + 1) * r * x ^ (r - 1)) (x := x) fun r _ => by
      have := (hasDerivAt_pow r x).const_mul (a r * (r + 1))
      convert this using 1
      ring
  exact h

/-- Lipschitz bound on `[0, L]` from a derivative bound. -/
theorem nsf_abs_sub_le_of_deriv {g g' : ℝ → ℝ} {L C : ℝ}
    (hg : ∀ x ∈ Icc 0 L, HasDerivAt g (g' x) x) (hC : ∀ x ∈ Icc 0 L, |g' x| ≤ C)
    {x y : ℝ} (hx : x ∈ Icc 0 L) (hy : y ∈ Icc 0 L) : |g x - g y| ≤ C * |x - y| := by
  wlog hxy : y ≤ x generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x]
    exact this hy hx (le_of_not_ge hxy)
  have hsub : Icc y x ⊆ Icc 0 L := Icc_subset_Icc hy.1 hx.2
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (f' := g') (C := C) (a := y)
    (b := x) (fun z hz => (hg z (hsub hz)).hasDerivWithinAt)
    (fun z hz => by rw [Real.norm_eq_abs]; exact hC z (hsub (Ico_subset_Icc_self hz))) x
    ⟨hxy, le_rfl⟩
  rw [Real.norm_eq_abs] at h
  rwa [abs_of_nonneg (sub_nonneg.2 hxy)]

/-- **`C²` polynomial approximation of `f_ε` with `π(0) = 0`** on `[0, L]`. -/
theorem nsf_exists_poly_approx {p ε : ℝ} (hε : 0 < ε) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) :
    ∃ (a : ℕ → ℝ) (N : ℕ), (∀ x ∈ Icc 0 L,
        |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x ∧
        |nsfPolyD1 a N x - nsgDeriv p ε x| ≤ δ) ∧
      ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L,
        |nsfDivDiff (nsfPolyD1 a N) (nsfPolyD2 a N) x y - nsgDivDiff p ε x y| ≤ δ := by
  set δ₀ := δ / (L + 1) with hδ₀
  have hδ₀pos : 0 < δ₀ := div_pos hδ (by linarith)
  have hδ₀le : δ₀ ≤ δ := div_le_self hδ.le (by linarith)
  have hδ₀L : δ₀ * L ≤ δ := by
    rw [hδ₀, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  have hcont : ContinuousOn (nsgDeriv2 p ε) (Icc 0 L) := fun x hx =>
    (((continuous_id.add continuous_const).continuousAt.rpow_const
      (Or.inl (ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x + ε)))).const_mul
        (p * (p - 1))).continuousWithinAt
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn 0 L _ hcont δ₀ hδ₀pos
  set M := P.natDegree + 1
  set a : ℕ → ℝ := fun r => if r = 0 then nsgDeriv p ε 0 else
    P.coeff (r - 1) / (((r : ℝ) + 1) * r) with ha
  have hD2 : ∀ x, nsfPolyD2 a (M + 1) x = P.eval x := by
    intro x
    unfold nsfPolyD2
    rw [Finset.sum_range_succ', P.eval_eq_sum_range]
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ha]
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    have h1 : ((n + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    have h2 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have hD10 : nsfPolyD1 a (M + 1) 0 = nsgDeriv p ε 0 := by
    unfold nsfPolyD1
    rw [Finset.sum_range_succ']
    simp [ha]
  have hF0 : nsfPolyFun a (M + 1) 0 = 0 := by simp [nsfPolyFun]
  have hR0 : nsfRegFun p ε 0 = 0 := by simp [nsfRegFun]
  -- derivative bounds
  have hderf : ∀ x ∈ Icc 0 L, HasDerivAt (fun y => nsfPolyD1 a (M + 1) y - nsgDeriv p ε y)
      (nsfPolyD2 a (M + 1) x - nsgDeriv2 p ε x) x := fun x hx =>
    (nsf_hasDerivAt_polyD1 a (M + 1) x).sub (nsg_hasDerivAt_deriv (by linarith [hx.1]))
  have hbd2 : ∀ x ∈ Icc 0 L, |nsfPolyD2 a (M + 1) x - nsgDeriv2 p ε x| ≤ δ₀ := fun x hx => by
    rw [hD2]; exact (hP x hx).le
  have hbd1 : ∀ x ∈ Icc 0 L, |nsfPolyD1 a (M + 1) x - nsgDeriv p ε x| ≤ δ₀ * x := by
    intro x hx
    have h := nsf_abs_sub_le_of_deriv hderf hbd2 hx ⟨le_rfl, hL⟩
    rw [hD10, sub_self, sub_zero, sub_zero, abs_of_nonneg hx.1] at h
    exact h
  have hder0 : ∀ x ∈ Icc 0 L, HasDerivAt (fun y => nsfPolyFun a (M + 1) y - nsfRegFun p ε y)
      (nsfPolyD1 a (M + 1) x - nsgDeriv p ε x) x := fun x hx =>
    (nsf_hasDerivAt_polyFun a (M + 1) x).sub (nsg_hasDerivAt_regFun (by linarith [hx.1]))
  have hbd1' : ∀ x ∈ Icc 0 L, |nsfPolyD1 a (M + 1) x - nsgDeriv p ε x| ≤ δ := fun x hx =>
    (hbd1 x hx).trans ((mul_le_mul_of_nonneg_left hx.2 hδ₀pos.le).trans hδ₀L)
  refine ⟨a, M + 1, fun x hx => ⟨?_, hbd1' x hx⟩, fun x hx y hy => ?_⟩
  · have h := nsf_abs_sub_le_of_deriv hder0 hbd1' hx ⟨le_rfl, hL⟩
    rw [hF0, hR0, sub_zero, sub_zero, sub_zero, abs_of_nonneg hx.1] at h
    exact h
  · rw [nsf_nsgDivDiff_eq]
    unfold nsfDivDiff
    split_ifs with hxy
    · exact (hbd2 x hx).trans hδ₀le
    · have hne : x - y ≠ 0 := sub_ne_zero.2 hxy
      rw [div_sub_div_same, show nsfPolyD1 a (M + 1) x - nsfPolyD1 a (M + 1) y -
          (nsgDeriv p ε x - nsgDeriv p ε y) =
          (nsfPolyD1 a (M + 1) x - nsgDeriv p ε x) - (nsfPolyD1 a (M + 1) y - nsgDeriv p ε y)
          by ring, abs_div, div_le_iff₀ (abs_pos.2 hne)]
      exact (nsf_abs_sub_le_of_deriv hderf hbd2 hx hy).trans
        (mul_le_mul_of_nonneg_right hδ₀le (abs_nonneg _))

/-- **Generator comparison.** -/
theorem nsf_specGen_sub_le {ι : Type*} [Fintype ι] {D g δ L : ℝ} (hD : 0 ≤ D) (hg : 0 ≤ g)
    {d₁ d₂ e₁ e₂ : ℝ → ℝ} {lam s : ι → ℝ} (hlam : ∀ i, lam i ∈ Icc 0 L)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1)
    (h1 : ∀ x ∈ Icc 0 L, |d₁ x - e₁ x| ≤ δ)
    (h2 : ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L, |nsfDivDiff d₁ d₂ x y - nsfDivDiff e₁ e₂ x y| ≤ δ) :
    |nsfSpecGen D g d₁ d₂ lam s - nsfSpecGen D g e₁ e₂ lam s| ≤
      D / 2 * δ * (g * ∑ i, lam i + (∑ i, lam i) ^ 2) := by
  have hl0 : ∀ i, 0 ≤ lam i := fun i => (hlam i).1
  have e : nsfSpecGen D g d₁ d₂ lam s - nsfSpecGen D g e₁ e₂ lam s =
      -(D / 2) * g * ∑ i, lam i * (d₁ (lam i) - e₁ (lam i)) +
        D / 2 * ∑ i, ∑ j, lam i * lam j * s j *
          (nsfDivDiff d₁ d₂ (lam i) (lam j) - nsfDivDiff e₁ e₂ (lam i) (lam j)) := by
    unfold nsfSpecGen
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [e]
  have hA : |-(D / 2) * g * ∑ i, lam i * (d₁ (lam i) - e₁ (lam i))| ≤ D / 2 * δ * (g * ∑ i, lam i) := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ D / 2), abs_of_nonneg hg]
    have : |∑ i, lam i * (d₁ (lam i) - e₁ (lam i))| ≤ δ * ∑ i, lam i := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul, abs_of_nonneg (hl0 i), mul_comm]
      exact mul_le_mul_of_nonneg_right (h1 _ (hlam i)) (hl0 i)
    calc D / 2 * g * |∑ i, lam i * (d₁ (lam i) - e₁ (lam i))| ≤ D / 2 * g * (δ * ∑ i, lam i) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hB : |D / 2 * ∑ i, ∑ j, lam i * lam j * s j *
      (nsfDivDiff d₁ d₂ (lam i) (lam j) - nsfDivDiff e₁ e₂ (lam i) (lam j))| ≤
      D / 2 * δ * (∑ i, lam i) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ D / 2), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (mul_nonneg (mul_nonneg (hl0 i) (hl0 j)) (hs0 j))]
    have hh := h2 _ (hlam i) _ (hlam j)
    have hlj : lam i * lam j * s j ≤ lam i * lam j :=
      mul_le_of_le_one_right (mul_nonneg (hl0 i) (hl0 j)) (hs1 j)
    have hδ : 0 ≤ δ := (abs_nonneg _).trans hh
    calc lam i * lam j * s j * |nsfDivDiff d₁ d₂ (lam i) (lam j) - nsfDivDiff e₁ e₂ (lam i) (lam j)|
        ≤ lam i * lam j * δ := mul_le_mul hlj hh (abs_nonneg _) (mul_nonneg (hl0 i) (hl0 j))
      _ = δ * (lam i * lam j) := by ring
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hA hB
    _ = _ := by ring

/-- `|Σ_i π(λ_i) - Σ_i f_ε(λ_i)| ≤ δ Σ_i λ_i` from `|π - f_ε| ≤ δx` on `[0, L]`. -/
theorem nsf_sum_regFun_sub_le {ι : Type*} [Fintype ι] {p ε δ L : ℝ} {a : ℕ → ℝ} {N : ℕ}
    (h : ∀ x ∈ Icc 0 L, |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x) {lam : ι → ℝ}
    (hlam : ∀ i, lam i ∈ Icc 0 L) :
    |∑ i, nsfPolyFun a N (lam i) - ∑ i, nsfRegFun p ε (lam i)| ≤ δ * ∑ i, lam i := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => h _ (hlam i))

end BlockBand.Endpoints
