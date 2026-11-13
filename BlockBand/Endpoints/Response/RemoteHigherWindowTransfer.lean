module

public import BlockBand.Endpoints.Response.RemoteHigherWindowGaussCoord

/-!
# The window transfer on the path law: likelihood of the transform `Tπ`

The energy shift `E → e` is absorbed by a transform `Tπ` of the path sample: each block is
shifted by `h_i = -δ + α D_i` (a function of the port bonds) and the two port bonds are rescaled.
On the good event where the port bonds have total mass at most `M`, Hölder and the Gaussian
likelihood ratio give the transfer inequality (`rhw_transfer_holder`); the bad event has
probability at most `4^{W²} e^{-M/(2s)}` (`rhw_bad_ports_le`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate Matrix

/-!
## Frobenius bounds
-/

section Frobenius

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem rhw_normSq_add_le (X Y : Matrix ι κ ℂ) :
    rhwNormSq (X + Y) ≤ 2 * rhwNormSq X + 2 * rhwNormSq Y := by
  unfold rhwNormSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  simp only [Matrix.add_apply, Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg ((X x y).re - (Y x y).re), sq_nonneg ((X x y).im - (Y x y).im)]

theorem rhw_normSq_smul (c : ℝ) (X : Matrix ι κ ℂ) :
    rhwNormSq ((c : ℂ) • X) = c ^ 2 * rhwNormSq X := by
  unfold rhwNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

theorem rhw_normSq_one [DecidableEq ι] : rhwNormSq (1 : Matrix ι ι ℂ) = Fintype.card ι := by
  unfold rhwNormSq
  have : ∀ x : ι, ∑ y, Complex.normSq ((1 : Matrix ι ι ℂ) x y) = 1 := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [Matrix.one_apply_ne' hy]
    · simp
  simp [this]

theorem rhw_normSq_zero : rhwNormSq (0 : Matrix ι κ ℂ) = 0 := by
  simp [rhwNormSq]

/-- `‖PP*‖²_F ≤ ‖P‖⁴_F` (Cauchy–Schwarz). -/
theorem rhw_normSq_mul_conjTranspose_le (P : Matrix ι κ ℂ) :
    rhwNormSq (P * Pᴴ) ≤ rhwNormSq P ^ 2 := by
  have hcs : ∀ x y : ι, Complex.normSq ((P * Pᴴ) x y) ≤
      (∑ c, Complex.normSq (P x c)) * (∑ c, Complex.normSq (P y c)) := by
    intro x y
    rw [Matrix.mul_apply, Complex.normSq_eq_norm_sq]
    have h1 : ‖∑ c, P x c * Pᴴ c y‖ ≤ ∑ c, ‖P x c‖ * ‖P y c‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
      rw [norm_mul, Matrix.conjTranspose_apply, norm_star]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun c => ‖P x c‖) (fun c => ‖P y c‖)
    simp only [← Complex.normSq_eq_norm_sq] at h2
    calc ‖∑ c, P x c * Pᴴ c y‖ ^ 2 ≤ (∑ c, ‖P x c‖ * ‖P y c‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  unfold rhwNormSq
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  refine Finset.sum_le_sum fun y _ => ?_
  exact hcs x y

end Frobenius

/-!
## The block shift of the transform
-/

variable {W n : ℕ}

/-- The block shifts `h_i = -δ + α D_i` of `rhwT`, as functions of the port bonds. -/
def rhwShift (δ α : ℝ) (P : Fin 2 → Matrix (Fin W) (Fin W) ℂ) (i : Fin n) :
    Matrix (Fin W) (Fin W) ℂ :=
  -((δ : ℂ) • 1) + (α : ℂ) • ((if i.val = 0 then P 0 * (P 0)ᴴ else 0) +
    (if i.val + 1 = n then P 1 * (P 1)ᴴ else 0))

theorem rhw_rhwT_eq (δ α lam : ℝ) (π : PathSample W n) :
    rhwT δ α lam π = ((fun i => π.1 i + rhwShift δ α π.2.2 i), π.2.1,
      fun j => (lam : ℂ) • π.2.2 j) := by
  unfold rhwT rhwShift rhwPortGram
  congr 1
  funext i
  abel

theorem rhw_shift_isHermitian (δ α : ℝ) (P : Fin 2 → Matrix (Fin W) (Fin W) ℂ) (i : Fin n) :
    (rhwShift δ α P i).IsHermitian := by
  unfold rhwShift Matrix.IsHermitian
  split_ifs <;>
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul]

theorem rhw_sum_ite_le (n : ℕ) (p : Fin n → Prop) [DecidablePred p]
    (hp : ∀ i j, p i → p j → i = j) {c : ℝ} (hc : 0 ≤ c) :
    ∑ i : Fin n, (if p i then c else 0) ≤ c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have : (Finset.univ.filter p).card ≤ 1 :=
    Finset.card_le_one.mpr fun i hi j hj => hp i j (Finset.mem_filter.mp hi).2
      (Finset.mem_filter.mp hj).2
  have : ((Finset.univ.filter p).card : ℝ) ≤ 1 := by exact_mod_cast this
  nlinarith

/-- `Σ_i ‖h_i‖²_F ≤ 2nWδ² + 4α²(Σ_j ‖B_j‖²_F)²`. -/
theorem rhw_sum_normSq_shift_le (δ α : ℝ) (P : Fin 2 → Matrix (Fin W) (Fin W) ℂ) :
    ∑ i : Fin n, rhwNormSq (rhwShift δ α P i) ≤
      2 * n * W * δ ^ 2 + 4 * α ^ 2 * (∑ j, rhwNormSq (P j)) ^ 2 := by
  set X := rhwNormSq (P 0 * (P 0)ᴴ)
  set Y := rhwNormSq (P 1 * (P 1)ᴴ)
  have hX : 0 ≤ X := rhw_normSq_nonneg _
  have hY : 0 ≤ Y := rhw_normSq_nonneg _
  have hpt : ∀ i : Fin n, rhwNormSq (rhwShift δ α P i) ≤
      2 * (W * δ ^ 2) + 2 * α ^ 2 * (2 * (if i.val = 0 then X else 0) +
        2 * (if i.val + 1 = n then Y else 0)) := by
    intro i
    unfold rhwShift
    refine (rhw_normSq_add_le _ _).trans ?_
    have h1 : rhwNormSq (-((δ : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ))) = W * δ ^ 2 := by
      rw [← neg_smul, ← Complex.ofReal_neg, rhw_normSq_smul, rhw_normSq_one, Fintype.card_fin]
      ring
    rw [h1, rhw_normSq_smul]
    have h2 := rhw_normSq_add_le (if i.val = 0 then P 0 * (P 0)ᴴ else 0)
      (if i.val + 1 = n then P 1 * (P 1)ᴴ else 0)
    have h3 : rhwNormSq (if i.val = 0 then P 0 * (P 0)ᴴ else 0) = if i.val = 0 then X else 0 := by
      split_ifs <;> simp [X, rhw_normSq_zero]
    have h4 : rhwNormSq (if i.val + 1 = n then P 1 * (P 1)ᴴ else 0) =
        if i.val + 1 = n then Y else 0 := by
      split_ifs <;> simp [Y, rhw_normSq_zero]
    rw [h3, h4] at h2
    nlinarith [sq_nonneg α]
  refine (Finset.sum_le_sum fun i _ => hpt i).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hs0 := rhw_sum_ite_le n (fun i : Fin n => i.val = 0) (fun i j hi hj => Fin.ext (hi.trans hj.symm)) hX
  have hs1 := rhw_sum_ite_le n (fun i : Fin n => i.val + 1 = n)
    (fun i j hi hj => Fin.ext (by omega)) hY
  have hXP : X ≤ rhwNormSq (P 0) ^ 2 := rhw_normSq_mul_conjTranspose_le _
  have hYP : Y ≤ rhwNormSq (P 1) ^ 2 := rhw_normSq_mul_conjTranspose_le _
  have hP0 := rhw_normSq_nonneg (P 0)
  have hP1 := rhw_normSq_nonneg (P 1)
  rw [Fin.sum_univ_two]
  nlinarith [sq_nonneg α, mul_nonneg (sq_nonneg α) hP0, mul_nonneg (sq_nonneg α) hP1,
    mul_nonneg (sq_nonneg α) (mul_nonneg hP0 hP1)]

/-!
## The transfer inequality
-/

/-- The good event of the port bonds: total mass `Σ_j ‖B_j‖²_F ≤ M`. -/
def rhwGood (W n : ℕ) (M : ℝ) : Set (PathSample W n) :=
  {π | ∑ j, rhwNormSq (π.2.2 j) ≤ M}

theorem rhw_measurableSet_good (M : ℝ) : MeasurableSet (rhwGood W n M) := by
  unfold rhwGood rhwNormSq
  exact measurableSet_le (by fun_prop) measurable_const

/-- The Ginibre rescaling constant of two port bonds. -/
def rhwScaleConst (W : ℕ) (lam a' : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (lam ^ (-a') * (1 - a' * (1 - (lam ^ 2)⁻¹)) ^ (-(1 / 2 : ℝ))) ^
    (2 * Fintype.card (Fin W × Fin W × Fin 2))) ^ (1 / a')

theorem rhw_scaleConst_ne_top (W : ℕ) (lam : ℝ) {a' : ℝ} (ha' : 0 < a') :
    rhwScaleConst W lam a' ≠ ⊤ :=
  ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

section MatrixMeasurability

variable {Ω : Type*} [MeasurableSpace Ω] {m o p : Type*}

theorem rhw_measurable_matrix_add {f g : Ω → Matrix m o ℂ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun ω => f ω + g ω) := by
  rw [Matrix.measurable_iff] at *
  intro i j
  simp only [Matrix.add_apply]
  exact (hf i j).add (hg i j)

theorem rhw_measurable_matrix_smul {f : Ω → Matrix m o ℂ} (c : ℂ) (hf : Measurable f) :
    Measurable (fun ω => c • f ω) := by
  rw [Matrix.measurable_iff] at *
  intro i j
  simpa only [Matrix.smul_apply, smul_eq_mul] using (hf i j).const_mul c

theorem rhw_measurable_matrix_mul [Fintype o] {f : Ω → Matrix m o ℂ} {g : Ω → Matrix o p ℂ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun ω => f ω * g ω) := by
  rw [Matrix.measurable_iff] at *
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hf i k).mul (hg k j)

theorem rhw_measurable_matrix_conjTranspose {f : Ω → Matrix m o ℂ} (hf : Measurable f) :
    Measurable (fun ω => (f ω)ᴴ) := by
  rw [Matrix.measurable_iff] at *
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact continuous_star.measurable.comp (hf j i)

end MatrixMeasurability

theorem rhw_measurable_shift (δ α : ℝ) (i : Fin n) :
    Measurable fun P : Fin 2 → Matrix (Fin W) (Fin W) ℂ => rhwShift δ α P i := by
  have h0 : Measurable fun P : Fin 2 → Matrix (Fin W) (Fin W) ℂ => P 0 * (P 0)ᴴ :=
    rhw_measurable_matrix_mul (measurable_pi_apply 0)
      (rhw_measurable_matrix_conjTranspose (measurable_pi_apply 0))
  have h1 : Measurable fun P : Fin 2 → Matrix (Fin W) (Fin W) ℂ => P 1 * (P 1)ᴴ :=
    rhw_measurable_matrix_mul (measurable_pi_apply 1)
      (rhw_measurable_matrix_conjTranspose (measurable_pi_apply 1))
  unfold rhwShift
  refine rhw_measurable_matrix_add measurable_const (rhw_measurable_matrix_smul _
    (rhw_measurable_matrix_add ?_ ?_))
  · split_ifs
    · exact h0
    · exact measurable_const
  · split_ifs
    · exact h1
    · exact measurable_const

theorem rhw_measurable_portScale (lam : ℝ) :
    Measurable fun P : Fin 2 → Matrix (Fin W) (Fin W) ℂ => fun j => (lam : ℂ) • P j :=
  measurable_pi_iff.mpr fun j => rhw_measurable_matrix_smul _ (measurable_pi_apply j)

theorem rhw_measurable_rhwT (δ α lam : ℝ) :
    Measurable fun π : PathSample W n => rhwT δ α lam π := by
  have h : (fun π : PathSample W n => rhwT δ α lam π) = fun π =>
      ((fun i => π.1 i + rhwShift δ α π.2.2 i), π.2.1, fun j => (lam : ℂ) • π.2.2 j) :=
    funext (rhw_rhwT_eq δ α lam)
  rw [h]
  refine Measurable.prodMk ?_ (Measurable.prodMk (measurable_fst.comp measurable_snd)
    ((rhw_measurable_portScale lam).comp (measurable_snd.comp measurable_snd)))
  refine measurable_pi_iff.mpr fun i => ?_
  exact rhw_measurable_matrix_add ((measurable_pi_apply i).comp measurable_fst)
    ((rhw_measurable_shift δ α i).comp (measurable_snd.comp measurable_snd))

/-- The block shift at fixed bonds `y`, on the good event. -/
theorem rhw_transfer_stepA {t : ℝ≥0} (ht0 : t ≠ 0) {δ α lam M : ℝ} {a a' : ℝ}
    (ha : a.HolderConjugate a') {G : PathSample W n → ℝ≥0∞} (hG : Measurable G)
    (y : (Fin (n - 1) → Matrix (Fin W) (Fin W) ℂ) × (Fin 2 → Matrix (Fin W) (Fin W) ℂ)) :
    ∫⁻ A, (rhwGood W n M).indicator (fun π => G (rhwT δ α lam π)) (A, y)
        ∂Measure.pi (fun _ : Fin n => gueMeasure (Fin W) t) ≤
      ENNReal.ofReal (Real.exp ((a' - 1) * (2 * n * W * δ ^ 2 + 4 * α ^ 2 * M ^ 2) / (2 * t))) *
        (∫⁻ A, G (A, y.1, fun j => (lam : ℂ) • y.2 j) ^ a
          ∂Measure.pi (fun _ : Fin n => gueMeasure (Fin W) t)) ^ (1 / a) := by
  have ha' : 1 < a' := ha.symm.lt
  by_cases hy : ∑ j, rhwNormSq (y.2 j) ≤ M
  · have hmem : ∀ A, (A, y) ∈ rhwGood W n M := fun A => hy
    simp_rw [Set.indicator_of_mem (hmem _), rhw_rhwT_eq]
    have hgm : Measurable fun A : Fin n → Matrix (Fin W) (Fin W) ℂ =>
        G (A, y.1, fun j => (lam : ℂ) • y.2 j) := hG.comp (measurable_id.prodMk measurable_const)
    refine (rhw_gue_pi_shift_holder ht0 (rhwShift δ α y.2) (rhw_shift_isHermitian δ α y.2)
      hgm ha).trans ?_
    gcongr
    have hsum := rhw_sum_normSq_shift_le (n := n) δ α y.2
    have hM0 : 0 ≤ ∑ j, rhwNormSq (y.2 j) := Finset.sum_nonneg fun j _ => rhw_normSq_nonneg _
    have hM2 : (∑ j, rhwNormSq (y.2 j)) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hM0 hy 2
    nlinarith [sq_nonneg α, mul_le_mul_of_nonneg_left hM2 (sq_nonneg α)]
  · have hnot : ∀ A, (A, y) ∉ rhwGood W n M := fun A => hy
    simp_rw [Set.indicator_of_notMem (hnot _), lintegral_zero]
    exact bot_le

/-- The window transfer inequality on the good event. -/
theorem rhw_transfer_holder (hW : 1 ≤ W) {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2)
    {δ α lam M : ℝ} (hlam : 0 < lam) {a a' : ℝ} (ha : a.HolderConjugate a')
    (hκ : 0 < 1 - a' * (1 - (lam ^ 2)⁻¹)) {G : PathSample W n → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ π, (rhwGood W n M).indicator (fun π => G (rhwT δ α lam π)) π ∂pathLaw W n b ≤
      ENNReal.ofReal (Real.exp ((a' - 1) * (2 * n * W * δ ^ 2 + 4 * α ^ 2 * M ^ 2) /
          (2 * ((1 - 2 * b) / W)))) * rhwScaleConst W lam a' *
        (∫⁻ π, G π ^ a ∂pathLaw W n b) ^ (1 / a) := by
  have ha0 : 0 < a := ha.pos
  have ha1 : 1 < a := ha.lt
  have ha' : 0 < a' := ha.symm.pos
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h12 : 0 < 1 - 2 * b := by linarith
  have htr : (Real.toNNReal ((1 - 2 * b) / W) : ℝ) = (1 - 2 * b) / W :=
    Real.coe_toNNReal _ (by positivity)
  have ht0 : Real.toNNReal ((1 - 2 * b) / W) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    simp only [htr, NNReal.coe_zero] at this
    linarith [div_pos h12 hW0]
  have hsr : (Real.toNNReal (b / W) : ℝ) = b / W := Real.coe_toNNReal _ (div_pos hb hW0).le
  have hs0 : Real.toNNReal (b / W) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    simp only [hsr, NNReal.coe_zero] at this
    linarith [div_pos hb hW0]
  have : ∀ _ : Fin n, IsProbabilityMeasure (gueMeasure (Fin W)
      (Real.toNNReal ((1 - 2 * b) / W))) := fun _ => isProbabilityMeasure_gueMeasure _ _
  have : ∀ _ : Fin 2, IsProbabilityMeasure (ginibreMeasure (Fin W) (Fin W)
      (Real.toNNReal (b / W))) := fun _ => isProbabilityMeasure_ginibreMeasure _ _ _
  have : ∀ _ : Fin (n - 1), IsProbabilityMeasure (ginibreMeasure (Fin W) (Fin W)
      (Real.toNNReal (b / W))) := fun _ => isProbabilityMeasure_ginibreMeasure _ _ _
  have : IsProbabilityMeasure (Measure.pi fun _ : Fin (n - 1) =>
      ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) := inferInstance
  have : IsProbabilityMeasure (Measure.pi fun _ : Fin 2 =>
      ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) := inferInstance
  have : IsProbabilityMeasure (Measure.pi fun _ : Fin n =>
      gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) := inferInstance
  have hGa : Measurable fun π : PathSample W n => G π ^ a := hG.pow_const a
  have hΦ : Measurable fun y : (Fin (n - 1) → Matrix (Fin W) (Fin W) ℂ) ×
      (Fin 2 → Matrix (Fin W) (Fin W) ℂ) =>
      ∫⁻ A, G (A, y) ^ a ∂Measure.pi (fun _ : Fin n => gueMeasure (Fin W)
        (Real.toNNReal ((1 - 2 * b) / W))) := hGa.lintegral_prod_left'
  have hTm : Measurable fun π : PathSample W n => G (rhwT δ α lam π) :=
    hG.comp (rhw_measurable_rhwT δ α lam)
  unfold pathLaw
  rw [lintegral_prod_symm' _ (hTm.indicator (rhw_measurableSet_good M))]
  refine (lintegral_mono fun y => rhw_transfer_stepA ht0 ha hG y).trans ?_
  rw [htr, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    mul_assoc (ENNReal.ofReal (Real.exp _)) (rhwScaleConst W lam a')]
  refine mul_le_mul' le_rfl ?_
  have hmP : Measurable fun y : (Fin (n - 1) → Matrix (Fin W) (Fin W) ℂ) ×
      (Fin 2 → Matrix (Fin W) (Fin W) ℂ) => (y.1, fun j => (lam : ℂ) • y.2 j) :=
    measurable_fst.prodMk ((rhw_measurable_portScale lam).comp measurable_snd)
  refine (lintegral_prod _ ?_).trans_le ?_
  · exact ((hΦ.comp hmP).pow_const _).aemeasurable
  have hstep : ∀ x : Fin (n - 1) → Matrix (Fin W) (Fin W) ℂ,
      ∫⁻ P, (∫⁻ A, G (A, x, fun j => (lam : ℂ) • P j) ^ a ∂Measure.pi (fun _ : Fin n =>
        gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)))) ^ (1 / a)
          ∂Measure.pi (fun _ : Fin 2 => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) ≤
        rhwScaleConst W lam a' * (∫⁻ P, ∫⁻ A, G (A, x, P) ^ a ∂Measure.pi (fun _ : Fin n =>
          gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)))
          ∂Measure.pi (fun _ : Fin 2 => ginibreMeasure (Fin W) (Fin W)
            (Real.toNNReal (b / W)))) ^ (1 / a) := by
    intro x
    have hf : Measurable fun P : Fin 2 → Matrix (Fin W) (Fin W) ℂ =>
        (∫⁻ A, G (A, x, P) ^ a ∂Measure.pi (fun _ : Fin n => gueMeasure (Fin W)
          (Real.toNNReal ((1 - 2 * b) / W)))) ^ (1 / a) :=
      (hΦ.comp (measurable_const.prodMk measurable_id)).pow_const _
    refine (rhw_gin_pi_scale_holder hs0 hlam hf ha hκ).trans (le_of_eq ?_)
    unfold rhwScaleConst
    simp only [Fintype.card_fin]
    congr 2
    refine lintegral_congr fun P => ?_
    rw [← ENNReal.rpow_mul, one_div_mul_cancel ha0.ne', ENNReal.rpow_one]
  refine (lintegral_mono hstep).trans ?_
  rw [lintegral_const_mul' _ _ (rhw_scaleConst_ne_top W lam ha')]
  gcongr
  refine (rhw_lintegral_rpow_le ((hΦ.lintegral_prod_right').aemeasurable)
    (by positivity) (by rw [one_div]; exact inv_le_one_of_one_le₀ ha1.le)).trans (le_of_eq ?_)
  congr 1
  rw [← lintegral_prod _ hΦ.aemeasurable, ← lintegral_prod_symm' _ hGa]

/-!
## The bad event
-/

/-- The port bonds are rarely heavy: `P(Σ_j ‖B_j‖²_F > M) ≤ 4^{W²} e^{-M/(2s)}`, `s = b/W`. -/
theorem rhw_bad_ports_le (hW : 1 ≤ W) {b : ℝ} (hb : 0 < b) (M : ℝ) :
    pathLaw W n b (rhwGood W n M)ᶜ ≤
      4 ^ (W * W) * ENNReal.ofReal (Real.exp (-(M / (2 * (b / W))))) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set s : ℝ≥0 := Real.toNNReal (b / W) with hs
  have hsr : (s : ℝ) = b / W := Real.coe_toNNReal _ (div_pos hb hW0).le
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    simp only [hsr, NNReal.coe_zero] at this
    linarith [div_pos hb hW0]
  set μP := Measure.pi fun _ : Fin 2 => ginibreMeasure (Fin W) (Fin W) s
  have : ∀ _ : Fin 2, IsProbabilityMeasure (ginibreMeasure (Fin W) (Fin W) s) := fun _ =>
    isProbabilityMeasure_ginibreMeasure _ _ _
  have hset : (rhwGood W n M)ᶜ = Prod.snd ⁻¹' (Prod.snd ⁻¹'
      {P : Fin 2 → Matrix (Fin W) (Fin W) ℂ | M < ∑ j, rhwNormSq (P j)}) := by
    ext π; simp [rhwGood]
  have hmeasS : MeasurableSet {P : Fin 2 → Matrix (Fin W) (Fin W) ℂ |
      M < ∑ j, rhwNormSq (P j)} := by
    unfold rhwNormSq
    exact measurableSet_lt measurable_const (by fun_prop)
  have hmarg : pathLaw W n b (rhwGood W n M)ᶜ = μP {P | M < ∑ j, rhwNormSq (P j)} := by
    have : ∀ _ : Fin n, IsProbabilityMeasure (gueMeasure (Fin W)
        (Real.toNNReal ((1 - 2 * b) / W))) := fun _ => isProbabilityMeasure_gueMeasure _ _
    have : ∀ _ : Fin (n - 1), IsProbabilityMeasure (ginibreMeasure (Fin W) (Fin W) s) :=
      fun _ => isProbabilityMeasure_ginibreMeasure _ _ _
    have : IsProbabilityMeasure (Measure.pi fun _ : Fin (n - 1) =>
        ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) := inferInstance
    have : IsProbabilityMeasure (Measure.pi fun _ : Fin 2 =>
        ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) := inferInstance
    have : IsProbabilityMeasure (Measure.pi fun _ : Fin n =>
        gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) := inferInstance
    rw [hset, ← Set.preimage_comp, ← Measure.map_apply (measurable_snd.comp measurable_snd)
      hmeasS]
    unfold pathLaw
    rw [← Measure.map_map measurable_snd measurable_snd, Measure.map_snd_prod, measure_univ,
      one_smul, Measure.map_snd_prod, measure_univ, one_smul]
  rw [hmarg]
  -- Chernoff
  set f : (Fin 2 → Matrix (Fin W) (Fin W) ℂ) → ℝ≥0∞ := fun P =>
    ENNReal.ofReal (Real.exp ((∑ j, rhwNormSq (P j)) / (2 * s)))
  have hf : Measurable f := by unfold f rhwNormSq; fun_prop
  have hle : ∀ P ∈ {P : Fin 2 → Matrix (Fin W) (Fin W) ℂ | M < ∑ j, rhwNormSq (P j)},
      ENNReal.ofReal (Real.exp (M / (2 * s))) ≤ f P := by
    intro P hP
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have : (0 : ℝ) < 2 * s := by rw [hsr]; positivity
    exact div_le_div_of_nonneg_right hP.le this.le
  have hmark := mul_meas_ge_le_lintegral₀ (μ := μP) hf.aemeasurable (ENNReal.ofReal (Real.exp (M / (2 * s))))
  have hint : ∫⁻ P, f P ∂μP = 2 ^ (2 * (W * W)) := by
    rw [rhw_gin_pi_exp_normSq hs0]
    simp
  have hc0 : ENNReal.ofReal (Real.exp (M / (2 * s))) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
  calc μP {P | M < ∑ j, rhwNormSq (P j)}
      ≤ μP {P | ENNReal.ofReal (Real.exp (M / (2 * s))) ≤ f P} :=
        measure_mono fun P hP => hle P hP
    _ ≤ (∫⁻ P, f P ∂μP) / ENNReal.ofReal (Real.exp (M / (2 * s))) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact hmark
    _ = 4 ^ (W * W) * ENNReal.ofReal (Real.exp (-(M / (2 * (b / W))))) := by
        rw [hint, div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg,
          hsr, pow_mul]
        norm_num

end BlockBand.Endpoints
