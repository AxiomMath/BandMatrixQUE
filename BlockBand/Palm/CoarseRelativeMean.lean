module

public import BlockBand.Palm.CoarseRelativeIBP

/-!
# Coarse relative local law: the exact integration-by-parts mean equation

Gaussian integration by parts gives the exact mean equation `(F - z) E[R] - s E[⟨R⟩ R] = I`
for the resolvent `R = (F + √s G - z)⁻¹` with `G ~ GUE_N(1/N)`, entrywise.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate NNReal ENNReal

section Sandwich

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem pair_sandwich (κ : ℂ) (A : Matrix ι ι ℂ) (a b : ι) :
    (κ • (single a b 1 + single b a 1)) * A * (κ • (single a b 1 + single b a 1)) +
      (κ • (Complex.I • single a b 1 - Complex.I • single b a 1)) * A *
        (κ • (Complex.I • single a b 1 - Complex.I • single b a 1)) =
    (2 * κ ^ 2) • (single a a (A b b) + single b b (A a a)) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, single_mul_mul_single, one_mul, mul_one, smul_smul]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

omit [Fintype ι] in
theorem single_eq_smul (a : ι) (c : ℂ) : single a a c = c • single a a (1 : ℂ) := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

theorem sandwich_sum (κ : ℂ) (A : Matrix ι ι ℂ) :
    ∑ u : ι × ι, (2 * κ ^ 2) • (single u.1 u.1 (A u.2 u.2) + single u.2 u.2 (A u.1 u.1)) =
      (4 * κ ^ 2 * A.trace) • (1 : Matrix ι ι ℂ) := by
  rw [← Finset.smul_sum, Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hs : ∀ a b : ι, single a a (A b b) = A b b • single a a (1 : ℂ) :=
    fun a b => single_eq_smul a _
  simp_rw [hs]
  have h1 : ∑ a : ι, ∑ b : ι, A b b • single a a (1 : ℂ) = A.trace • (1 : Matrix ι ι ℂ) := by
    simp_rw [← Finset.sum_smul]
    rw [← Finset.smul_sum, Matrix.sum_single_one]
    rfl
  have h2 : ∑ a : ι, ∑ b : ι, A a a • single b b (1 : ℂ) = A.trace • (1 : Matrix ι ι ℂ) := by
    simp_rw [← Finset.smul_sum, Matrix.sum_single_one]
    rw [← Finset.sum_smul]
    rfl
  rw [h1, h2, ← add_smul, smul_smul]
  congr 1
  ring

/-- **GUE sandwich identity.** `Σ_j D_j A D_j = t tr(A) I` for `D_j = ∂_j G`. -/
theorem gue_sandwich (t : ℝ≥0) (A : Matrix ι ι ℂ) :
    ∑ j : (ι × ι) × Fin 2, gueCoord t (Pi.single j (1 : ℝ)) * A * gueCoord t (Pi.single j 1) =
      ((t : ℂ) * A.trace) • (1 : Matrix ι ι ℂ) := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, gueCoord_single0, gueCoord_single1]
  simp_rw [pair_sandwich]
  rw [sandwich_sum]
  congr 1
  have hκ2 : (Real.sqrt (t / 2) / Real.sqrt 2) ^ 2 = (t : ℝ) / 4 := by
    rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
    ring
  have : (4 : ℂ) * ((Real.sqrt (t / 2) / Real.sqrt 2 : ℝ) : ℂ) ^ 2 = (t : ℂ) := by
    rw [← Complex.ofReal_pow, hκ2]
    push_cast
    ring
  rw [this]

end Sandwich

section Entries

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem entry_le_of_nsq {A : Matrix ι ι ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ y : ι → ℂ, nsq (A *ᵥ y) ≤ C ^ 2 * nsq y) (m l : ι) : ‖A m l‖ ≤ C := by
  have h1 : ‖A m l‖ ^ 2 ≤ nsq (A *ᵥ Pi.single l 1) := by
    have : A m l = (A *ᵥ Pi.single l 1) m := by simp
    rw [this]
    exact Finset.single_le_sum (f := fun k => ‖(A *ᵥ Pi.single l 1) k‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ m)
  have h2 := hA (Pi.single l 1)
  rw [nsq_single_one, mul_one] at h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hC two_ne_zero).mp (h1.trans h2)

theorem hermitian_resolvent_entry_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (m l : ι) : ‖(H - z • (1 : Matrix ι ι ℂ))⁻¹ m l‖ ≤ z.im⁻¹ := by
  apply entry_le_of_nsq (by positivity)
  intro y
  have := hermitian_resolvent_nsq_le hH hz.ne' y
  rwa [inv_pow]

omit [DecidableEq ι] in
theorem mul_entry_le (B A : Matrix ι ι ℂ) {a : ℝ} (hA : ∀ m l, ‖A m l‖ ≤ a) (k l : ι) :
    ‖(B * A) k l‖ ≤ (∑ m, ‖B k m‖) * a := by
  rw [mul_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ => ?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hA m l) (norm_nonneg _)

omit [DecidableEq ι] in
theorem triple_entry_le (A X C : Matrix ι ι ℂ) {a c : ℝ} (ha : 0 ≤ a)
    (hA : ∀ m l, ‖A m l‖ ≤ a) (hC : ∀ m l, ‖C m l‖ ≤ c) (m l : ι) :
    ‖(A * X * C) m l‖ ≤ a * c * ∑ q, ∑ p, ‖X p q‖ := by
  rw [mul_apply]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun q _ => ?_)
  rw [norm_mul, mul_apply]
  have h1 : ‖∑ p, A m p * X p q‖ ≤ a * ∑ p, ‖X p q‖ := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hA m p) (norm_nonneg _)
  calc ‖∑ p, A m p * X p q‖ * ‖C q l‖ ≤ (a * ∑ p, ‖X p q‖) * c :=
        mul_le_mul h1 (hC q l) (norm_nonneg _) (by positivity)
    _ = a * c * ∑ p, ‖X p q‖ := by ring

/-- The real-linear entry functional `A ↦ (B A)_{kl}`. -/
def entryLin (B : Matrix ι ι ℂ) (k l : ι) : Matrix ι ι ℂ →ₗ[ℝ] ℂ where
  toFun A := (B * A) k l
  map_add' A A' := by simp [Matrix.mul_add]
  map_smul' r A := by simp

end Entries

/-!
## Resolvent entries in Gaussian coordinates
-/

variable {N : ℕ}

/-- `R(y) = (F + √s G(y) - z)⁻¹`. -/
abbrev coordRes (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) (t : ℝ≥0)
    (y : ((Fin N × Fin N) × Fin 2) → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  coarseResolvent F (gueCoord t y) s z

theorem coordRes_eq (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) (t : ℝ≥0)
    (y : ((Fin N × Fin N) × Fin 2) → ℝ) :
    coordRes F s z t y =
      ((F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) + (Real.sqrt s • gueCoordLin t) y)⁻¹ := by
  unfold coordRes coarseResolvent
  rw [coarse_shift_eq F _ s z t y rfl]

theorem coordRes_entry_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ) {z : ℂ}
    (hz : 0 < z.im) (t : ℝ≥0) (y : ((Fin N × Fin N) × Fin 2) → ℝ) (m l : Fin N) :
    ‖coordRes F s z t y m l‖ ≤ z.im⁻¹ :=
  hermitian_resolvent_entry_le (coarse_hermitian hF (gueCoord_isHermitian t y) s) hz m l

theorem entryFn_contDiff {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (t : ℝ≥0) (B : Matrix (Fin N) (Fin N) ℂ) (k l : Fin N) :
    ContDiff ℝ 1 (fun y => (B * coordRes F s z t y) k l) := by
  have h := linInv_contDiff (F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) (Real.sqrt s • gueCoordLin t)
    (entryLin B k l) (coarse_shift_det_isUnit hF s hz t)
  convert h using 2 with y
  rw [coordRes_eq]
  rfl

theorem entryFn_fderiv {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (t : ℝ≥0) (B : Matrix (Fin N) (Fin N) ℂ) (k l : Fin N)
    (y v : ((Fin N × Fin N) × Fin 2) → ℝ) :
    fderiv ℝ (fun y => (B * coordRes F s z t y) k l) y v =
      -((Real.sqrt s : ℂ) * (B * (coordRes F s z t y * gueCoord t v * coordRes F s z t y)) k l) := by
  obtain ⟨D, hD, hDv⟩ := linInv_hasFDerivAt (F - z • (1 : Matrix (Fin N) (Fin N) ℂ))
    (Real.sqrt s • gueCoordLin t) (entryLin B k l) (coarse_shift_det_isUnit hF s hz t) y
  have hfun : (fun y => (B * coordRes F s z t y) k l) = fun y => entryLin B k l
      (((F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) + (Real.sqrt s • gueCoordLin t) y)⁻¹) := by
    funext w
    rw [coordRes_eq]
    rfl
  rw [hfun, hD.fderiv, hDv, ← coordRes_eq, LinearMap.smul_apply]
  change -((B * (coordRes F s z t y * (Real.sqrt s • gueCoord t v) * coordRes F s z t y)) k l) = _
  rw [← Complex.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply,
    smul_eq_mul]

/-- **Entry IBP.** `E[y_j (B R)_{kl}] = -√s E[(B R D_j R)_{kl}]`. -/
theorem entry_ibp (hIBP : MultivariateGaussianIBP) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) (s : ℝ) {z : ℂ} (hz : 0 < z.im) (t : ℝ≥0)
    (B : Matrix (Fin N) (Fin N) ℂ) (k l : Fin N) (j : (Fin N × Fin N) × Fin 2) :
    ∫ y, (y j : ℂ) * (B * coordRes F s z t y) k l ∂gaussianProduct (fun _ => (1 : ℝ≥0)) =
      -((Real.sqrt s : ℂ) * ∫ y, (B * (coordRes F s z t y * gueCoord t (Pi.single j 1) *
        coordRes F s z t y)) k l ∂gaussianProduct (fun _ => (1 : ℝ≥0))) := by
  have hb := fun y => mul_entry_le B (coordRes F s z t y) (coordRes_entry_le hF s hz t y) k l
  have hb' : ∀ y, ‖fderiv ℝ (fun y => (B * coordRes F s z t y) k l) y (Pi.single j 1)‖ ≤
      Real.sqrt s * ((∑ m, ‖B k m‖) * (z.im⁻¹ * z.im⁻¹ *
        ∑ q, ∑ p, ‖gueCoord t (Pi.single j (1 : ℝ)) p q‖)) := by
    intro y
    rw [entryFn_fderiv hF s hz.ne' t B k l y, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply mul_entry_le
    intro m l'
    exact triple_entry_le _ _ _ (by positivity)
      (coordRes_entry_le hF s hz t y) (coordRes_entry_le hF s hz t y) m l'
  rw [gaussian_ibp_of_bounded hIBP (entryFn_contDiff hF s hz.ne' t B k l) j hb hb']
  simp_rw [entryFn_fderiv hF s hz.ne' t B k l]
  rw [integral_neg, integral_const_mul]

theorem gueCoord_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι] (t : ℝ≥0)
    (y : ((ι × ι) × Fin 2) → ℝ) :
    gueCoord t y = ∑ j, (y j : ℂ) • gueCoord t (Pi.single j (1 : ℝ)) := by
  have h := congrArg (gueCoordLin (ι := ι) t) (Finset.univ_sum_single y)
  rw [map_sum] at h
  rw [← show gueCoordLin t y = gueCoord t y from rfl, ← h]
  apply Finset.sum_congr rfl
  intro j _
  have : Pi.single j (y j) = y j • Pi.single j (1 : ℝ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, Complex.coe_smul]
  rfl

theorem coordRes_continuous {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (t : ℝ≥0) : Continuous (fun y => coordRes F s z t y) := by
  apply continuous_pi
  intro m
  apply continuous_pi
  intro l
  have h := (entryFn_contDiff hF s hz t 1 m l).continuous
  simpa using h

/-- **Exact mean equation.** `(F - z) E[R] - s E[⟨R⟩ R] = I`, entrywise, from
`MultivariateGaussianIBP`. -/
theorem coarse_mean_equation (hIBP : MultivariateGaussianIBP) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : 0 < z.im)
    (k l : Fin N) :
    ∑ m, (F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) k m *
        (∫ y, coordRes F s z (Real.toNNReal (1 / N)) y m l ∂gaussianProduct (fun _ => (1 : ℝ≥0))) -
      (s : ℂ) * ∫ y, ((N : ℂ)⁻¹ * (coordRes F s z (Real.toNNReal (1 / N)) y).trace) *
          coordRes F s z (Real.toNNReal (1 / N)) y k l ∂gaussianProduct (fun _ => (1 : ℝ≥0)) =
      (1 : Matrix (Fin N) (Fin N) ℂ) k l := by
  set t := Real.toNNReal (1 / N) with htdef
  set μ := gaussianProduct (fun _ : (Fin N × Fin N) × Fin 2 => (1 : ℝ≥0)) with hμ
  have hprob : IsProbabilityMeasure μ := coordLaw_isProb N
  set R := fun y => coordRes F s z t y with hRdef
  set D := fun j : (Fin N × Fin N) × Fin 2 => gueCoord t (Pi.single j (1 : ℝ)) with hDdef
  have hRc : Continuous R := coordRes_continuous hF s hz.ne' t
  have hent : ∀ y m l, ‖R y m l‖ ≤ z.im⁻¹ := fun y => coordRes_entry_le hF s hz t y
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : ((t : ℝ) : ℂ) = (N : ℂ)⁻¹ := by
    rw [htdef, Real.coe_toNNReal _ (by positivity)]
    push_cast
    ring
  -- pointwise identity
  have hpt : ∀ y, ∑ m, (F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) k m * R y m l +
      (Real.sqrt s : ℂ) * ∑ j, (y j : ℂ) * (D j * R y) k l = (1 : Matrix (Fin N) (Fin N) ℂ) k l := by
    intro y
    have hH := coarse_hermitian hF (gueCoord_isHermitian t y) s
    have h1 := hermitian_shift_mul_inv hH hz.ne'
    have h2 : (F + (Real.sqrt s : ℂ) • gueCoord t y - z • (1 : Matrix (Fin N) (Fin N) ℂ)) * R y =
        (F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) * R y +
          (Real.sqrt s : ℂ) • ∑ j, (y j : ℂ) • (D j * R y) := by
      rw [show F + (Real.sqrt s : ℂ) • gueCoord t y - z • (1 : Matrix (Fin N) (Fin N) ℂ) =
          (F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) + (Real.sqrt s : ℂ) • gueCoord t y by abel,
        Matrix.add_mul, Matrix.smul_mul, gueCoord_eq_sum t y, Finset.sum_mul]
      simp_rw [Matrix.smul_mul]
      rfl
    have h3 := congrArg (fun A => A k l) h1
    beta_reduce at h3
    rw [show (F + (Real.sqrt s : ℂ) • gueCoord t y - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = R y
      from rfl, h2] at h3
    rw [← h3, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, mul_apply, smul_eq_mul]
    simp_rw [Matrix.smul_apply, smul_eq_mul]
  -- integrability
  have hRi : ∀ m l, Integrable (fun y => R y m l) μ := fun m l =>
    Integrable.of_bound ((continuous_apply_apply m l).comp hRc).aestronglyMeasurable _
      (Filter.Eventually.of_forall (fun y => hent y m l))
  have hDRc : ∀ j, Continuous (fun y => (D j * R y) k l) := fun j =>
    (continuous_apply_apply k l).comp (continuous_const.matrix_mul hRc)
  have hDRb : ∀ j y, ‖(D j * R y) k l‖ ≤ (∑ m, ‖D j k m‖) * z.im⁻¹ :=
    fun j y => mul_entry_le _ _ (hent y) k l
  have hxi : ∀ j, Integrable (fun y => (y j : ℂ) * (D j * R y) k l) μ := by
    intro j
    have hc : Integrable (fun y : ((Fin N × Fin N) × Fin 2) → ℝ => ((y j : ℝ) : ℂ)) μ :=
      (coord_integrable j).ofReal
    have := hc.bdd_mul (f := fun y => (D j * R y) k l) (hDRc j).aestronglyMeasurable
      (Filter.Eventually.of_forall (hDRb j))
    exact this.congr (Filter.Eventually.of_forall (fun y => by simp only; ring))
  have hFRi : Integrable (fun y => ∑ m, (F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) k m * R y m l) μ :=
    integrable_finsetSum _ (fun m _ => (hRi m l).const_mul _)
  have hGi : Integrable (fun y => (Real.sqrt s : ℂ) * ∑ j, (y j : ℂ) * (D j * R y) k l) μ :=
    (integrable_finsetSum _ (fun j _ => hxi j)).const_mul _
  have hDDRc : ∀ j, Continuous (fun y => (D j * (R y * D j * R y)) k l) := fun j =>
    (continuous_apply_apply k l).comp
      (continuous_const.matrix_mul ((hRc.matrix_mul continuous_const).matrix_mul hRc))
  have hDDRi : ∀ j, Integrable (fun y => (D j * (R y * D j * R y)) k l) μ := fun j =>
    Integrable.of_bound (hDDRc j).aestronglyMeasurable _ (Filter.Eventually.of_forall (fun y =>
      mul_entry_le _ _ (fun m l' => triple_entry_le (R y) (D j) (R y) (by positivity)
        (hent y) (hent y) m l') k l))
  -- integrate the pointwise identity
  have hint := congrArg (fun g : (((Fin N × Fin N) × Fin 2) → ℝ) → ℂ => ∫ y, g y ∂μ)
    (funext hpt)
  beta_reduce at hint
  rw [integral_add hFRi hGi, integral_const, probReal_univ, one_smul,
    integral_finsetSum _ (fun m _ => (hRi m l).const_mul _), integral_const_mul,
    integral_finsetSum _ (fun j _ => hxi j)] at hint
  simp_rw [integral_const_mul] at hint
  have hibp : ∀ j, ∫ y, (y j : ℂ) * (D j * R y) k l ∂μ =
      -((Real.sqrt s : ℂ) * ∫ y, (D j * (R y * D j * R y)) k l ∂μ) :=
    fun j => entry_ibp hIBP hF s hz t (D j) k l j
  simp_rw [hibp] at hint
  -- the sandwich
  have hsand : ∀ y, ∑ j, (D j * (R y * D j * R y)) k l =
      ((N : ℂ)⁻¹ * (R y).trace) * R y k l := by
    intro y
    have h1 : ∑ j, D j * (R y * D j * R y) = (∑ j, D j * R y * D j) * R y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.mul_assoc]
    have h2 := gue_sandwich t (R y)
    rw [← Matrix.sum_apply, h1]
    simp only [hDdef] at h2 ⊢
    rw [h2, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul, ht]
  have hsum : ∑ j, -((Real.sqrt s : ℂ) * ∫ y, (D j * (R y * D j * R y)) k l ∂μ) =
      -((Real.sqrt s : ℂ) * ∫ y, ((N : ℂ)⁻¹ * (R y).trace) * R y k l ∂μ) := by
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← integral_finsetSum _ (fun j _ => hDDRi j)]
    simp_rw [hsand]
  rw [hsum] at hint
  have hss : (Real.sqrt s : ℂ) * (Real.sqrt s : ℂ) = (s : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs]
  rw [← hint]
  simp only [R]
  linear_combination (∫ y, ((N : ℂ)⁻¹ * (coordRes F s z t y).trace) * coordRes F s z t y k l ∂μ) * hss

end BlockBand.Palm.CoarseRelative
