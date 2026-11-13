module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.ChartSigma
public import BlockBand.SourceProcess.Stochastic.SourceSDE.MatrixForms
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The chart coefficients are locally Lipschitz

* **`locallyLipschitz_chartSigma`**: `y ↦ chartSigma D0 D δ y` is locally Lipschitz on all of
  `ℝ^{4|c|²}` (Frobenius norm on matrices): `fromGramReal` is linear, `chartFrame`
  is Lipschitz (`lipschitzWith_chartFrame`, from `lipschitzWith_fcM`), the Gram noise is
  polynomial in the frame (`contDiff_gramNoise`), and entries are Lipschitz.
* **`locallyLipschitz_gramRealDrift`**: the real Gram drift is polynomial.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

theorem norm_sq_rect {m n : Type*} [Fintype m] [Fintype n] (Z : Matrix m n ℂ) :
    ‖Z‖ ^ 2 = ∑ i, ∑ j, ‖Z i j‖ ^ 2 := by
  rw [frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => by positivity)]
  simp only [Real.rpow_two]

theorem norm_entry_le {m n : Type*} [Fintype m] [Fintype n] (Z : Matrix m n ℂ) (i : m) (j : n) :
    ‖Z i j‖ ≤ ‖Z‖ := by
  have h : ‖Z i j‖ ^ 2 ≤ ‖Z‖ ^ 2 := by
    rw [norm_sq_rect]
    exact (Finset.single_le_sum (f := fun j => ‖Z i j‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖Z i j‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i))
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem norm_fromRows_le {m₁ m₂ n : Type*} [Fintype m₁] [Fintype m₂] [Fintype n]
    (A : Matrix m₁ n ℂ) (B : Matrix m₂ n ℂ) : ‖fromRows A B‖ ≤ ‖A‖ + ‖B‖ := by
  have h : ‖fromRows A B‖ ^ 2 ≤ (‖A‖ + ‖B‖) ^ 2 := by
    rw [norm_sq_rect, Fintype.sum_sum_type]
    simp only [fromRows_apply_inl, fromRows_apply_inr]
    rw [← norm_sq_rect, ← norm_sq_rect]
    nlinarith [norm_nonneg A, norm_nonneg B]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- **The chart frame is Lipschitz.** -/
theorem lipschitzWith_chartFrame {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith (3 * Real.toNNReal (2 / Real.sqrt δ)) (chartFrame (c := c) δ) := by
  have hf := lipschitzWith_fcM (n := c) (lipschitzWith_cutSqrt hδ)
  set L := Real.toNNReal (2 / Real.sqrt δ)
  refine LipschitzWith.of_dist_le_mul fun G G' => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have e : chartFrame δ G - chartFrame δ G' = fromRows (fcM (cutSqrt δ) G.2 - fcM (cutSqrt δ) G'.2)
      (fcM (cutSqrt δ) (G.1 - G.2) - fcM (cutSqrt δ) (G'.1 - G'.2)) := by
    ext (i | i) j <;> simp [chartFrame]
  rw [e]
  have h1 : ‖fcM (cutSqrt δ) G.2 - fcM (cutSqrt δ) G'.2‖ ≤ L * ‖G - G'‖ := by
    have := hf.dist_le_mul G.2 G'.2
    rw [dist_eq_norm, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_left (norm_snd_le (G - G')) L.2)
  have h2 : ‖fcM (cutSqrt δ) (G.1 - G.2) - fcM (cutSqrt δ) (G'.1 - G'.2)‖ ≤ L * (2 * ‖G - G'‖) := by
    have := hf.dist_le_mul (G.1 - G.2) (G'.1 - G'.2)
    rw [dist_eq_norm, dist_eq_norm] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ L.2)
    have e2 : G.1 - G.2 - (G'.1 - G'.2) = (G - G').1 - (G - G').2 := by simp; abel
    rw [e2]
    refine (norm_sub_le _ _).trans ?_
    linarith [norm_fst_le (G - G'), norm_snd_le (G - G')]
  refine (norm_fromRows_le _ _).trans ?_
  push_cast
  nlinarith [norm_nonneg (G - G'), L.2]

/-- `Xᴴ` as a real-linear map. -/
def ctLin (m n : Type*) [Fintype m] [Fintype n] : Matrix m n ℂ →ₗ[ℝ] Matrix n m ℂ where
  toFun X := Xᴴ
  map_add' X Y := conjTranspose_add X Y
  map_smul' r X := by ext i j; simp

/-- `Xᴴ` as a continuous real-linear map. -/
def ctCLM (m n : Type*) [Fintype m] [Fintype n] : Matrix m n ℂ →L[ℝ] Matrix n m ℂ :=
  toCLM (ctLin m n)

theorem ctCLM_apply {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) :
    ctCLM m n X = Xᴴ := rfl

omit [DecidableEq c] in
theorem contDiff_gramNoise {ι : Type*} [Fintype ι] [DecidableEq ι] (D0 : ℝ) (P : Matrix ι ι ℂ)
    (D : Matrix c c ℂ) (a : SourceNoise ι) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun V : Matrix ι c ℂ => gramNoise D0 P D a V) := by
  have hσ := contDiff_sourceDiffusion (c := c) D0 P D a (k := k)
  have hσH : ContDiff ℝ k (fun V : Matrix ι c ℂ => ctCLM ι c (sourceDiffusion D0 P D a V)) :=
    (ctCLM ι c).contDiff.comp hσ
  have hVH : ContDiff ℝ k (fun V : Matrix ι c ℂ => ctCLM ι c V) := (ctCLM ι c).contDiff
  have h1 : ContDiff ℝ k (fun V : Matrix ι c ℂ => mulBil (ctCLM ι c (sourceDiffusion D0 P D a V)) V +
      mulBil (ctCLM ι c V) (sourceDiffusion D0 P D a V)) :=
    (contDiff_bilin _ hσH contDiff_id).add (contDiff_bilin _ hVH hσ)
  have h2 : ContDiff ℝ k (fun V : Matrix ι c ℂ =>
      mulBil (mulBil (ctCLM ι c (sourceDiffusion D0 P D a V)) P) V +
        mulBil (mulBil (ctCLM ι c V) P) (sourceDiffusion D0 P D a V)) :=
    (contDiff_bilin _ (contDiff_bilin _ hσH contDiff_const) contDiff_id).add
      (contDiff_bilin _ (contDiff_bilin _ hVH contDiff_const) hσ)
  exact h1.prodMk h2

omit [DecidableEq c] in
theorem lipschitzWith_reIm_gramEntry (r : Fin 2) (e : Fin 2 × c × c) :
    LipschitzWith 1 fun x : Matrix c c ℂ × Matrix c c ℂ => reIm r (gramEntry e x) := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
  have hlin : reIm r (gramEntry e x) - reIm r (gramEntry e x') = reIm r (gramEntry e (x - x')) := by
    unfold reIm gramEntry; split_ifs <;> simp
  rw [hlin]
  have hz : ‖gramEntry e (x - x')‖ ≤ ‖x - x'‖ := by
    unfold gramEntry; split_ifs
    · exact (norm_entry_le _ _ _).trans (norm_fst_le _)
    · exact (norm_entry_le _ _ _).trans (norm_snd_le _)
  refine le_trans ?_ hz
  unfold reIm; split_ifs
  · exact Complex.abs_re_le_norm _
  · exact Complex.abs_im_le_norm _

theorem locallyLipschitz_sum {X E ι : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup E]
    (s : Finset ι) {f : ι → X → E} (h : ∀ i, LocallyLipschitz (f i)) :
    LocallyLipschitz fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (LipschitzWith.const (0 : E)).locallyLipschitz (α := X)
  | insert a s ha ih =>
      simp_rw [Finset.sum_insert ha]
      exact (h a).add ih

theorem locallyLipschitz_matrix {X m n : Type*} [PseudoMetricSpace X] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {F : X → Matrix m n ℝ}
    (h : ∀ i j, LocallyLipschitz fun x => F x i j) : LocallyLipschitz F := by
  have e : F = fun x => ∑ i, ∑ j, F x i j • Matrix.single i j (1 : ℝ) := by
    funext x
    conv_lhs => rw [matrix_eq_sum_single (F x)]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]
  refine locallyLipschitz_sum _ fun i => locallyLipschitz_sum _ fun j => ?_
  have he : (fun t : ℝ => t • Matrix.single i j (1 : ℝ)) =
      ⇑(ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Matrix.single i j (1 : ℝ))) := by
    funext t; simp
  have hs : LocallyLipschitz fun t : ℝ => t • Matrix.single i j (1 : ℝ) := by
    rw [he]; exact (ContinuousLinearMap.lipschitzWith _).locallyLipschitz
  exact hs.comp (h i j)

/-- **The chart diffusion is locally Lipschitz.** -/
theorem locallyLipschitz_chartSigma (D0 : ℝ) (D : Matrix c c ℂ) {δ : ℝ} (hδ : 0 < δ) :
    LocallyLipschitz (chartSigma D0 D δ) := by
  refine locallyLipschitz_matrix fun i k => ?_
  have h1 : LipschitzWith _ fun y : Fin (gramDim c) → ℝ => chartFrame δ (fromGramReal y) :=
    (lipschitzWith_chartFrame hδ).comp (fromGramReal (c := c)).lipschitzWith
  exact (lipschitzWith_reIm_gramEntry _ _).locallyLipschitz.comp
    ((contDiff_gramNoise (k := 1) D0 P0 D _).locallyLipschitz.comp h1.locallyLipschitz)

omit [DecidableEq c] in
theorem contDiff_gramScalar (D : Matrix c c ℂ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun M : Matrix c c ℂ => gramScalar D M) := by
  have h : ContDiff ℝ k (fun M : Matrix c c ℂ =>
      (1 / 2 : ℂ) * traceCLM (mulBil (mulBil (mulBil D M) D) M)) :=
    contDiff_const.mul (traceCLM.contDiff.comp (contDiff_bilin _ (contDiff_bilin _
      (contDiff_bilin _ contDiff_const contDiff_id) contDiff_const) contDiff_id))
  exact h

omit [DecidableEq c] in
theorem contDiff_gramDriftG (D0 : ℝ) (D : Matrix c c ℂ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (gramDriftG (c := c) D0 D) := by
  have hs : ContDiff ℝ k (fun G : Matrix c c ℂ × Matrix c c ℂ =>
      -(((D0 / 2 : ℝ) : ℂ) * gramScalar D G.1)) :=
    (contDiff_const.mul ((contDiff_gramScalar D).comp contDiff_fst)).neg
  exact contDiff_const.prodMk (hs.smul contDiff_snd)

theorem locallyLipschitz_pi {X n : Type*} [PseudoMetricSpace X] [Fintype n] [DecidableEq n]
    {F : X → n → ℝ} (h : ∀ i, LocallyLipschitz fun x => F x i) : LocallyLipschitz F := by
  have e : F = fun x => ∑ i, Pi.single i (F x i) := by
    funext x; exact (Finset.univ_sum_single (F x)).symm
  rw [e]
  refine locallyLipschitz_sum _ fun i => ?_
  exact (ContinuousLinearMap.single ℝ (fun _ : n => ℝ) i).lipschitzWith.locallyLipschitz.comp (h i)

/-- **The real Gram drift is locally Lipschitz.** -/
theorem locallyLipschitz_gramRealDrift (D0 : ℝ) (D : Matrix c c ℂ) :
    LocallyLipschitz (gramRealDrift (c := c) D0 D) := by
  refine locallyLipschitz_pi fun i => ?_
  have h1 : LocallyLipschitz fun y : Fin (gramDim c) → ℝ => gramDriftG D0 D (fromGramReal y) :=
    (contDiff_gramDriftG (k := 1) D0 D).locallyLipschitz.comp
      (fromGramReal (c := c)).lipschitzWith.locallyLipschitz
  exact (lipschitzWith_reIm_gramEntry _ _).locallyLipschitz.comp h1

end BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
