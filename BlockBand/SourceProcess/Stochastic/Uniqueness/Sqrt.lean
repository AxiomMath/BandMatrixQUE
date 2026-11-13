module
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.EMetricSpace.Lipschitz
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# A locally Lipschitz square root of a positive definite `C²` covariance

Matrices `Matrix (Fin d) (Fin d) ℝ` carry the Frobenius norm (local instance); `Fin d → ℝ` the
sup norm.

* `psdSqrt A = U diag(√λ) Uᵀ` (spectral square root, `0` off symmetric matrices);
  `psdSqrt_mul_self`, `psdSqrt_transpose` for symmetric `A` with nonnegative eigenvalues.
* `QuadGe A c`: `c |v|² ≤ vᵀ A v` for all `v`; `quadGe_psdSqrt`: `A ≥ c I ⇒ √A ≥ √c I`.
* **`norm_sub_le_of_quadGe`** (Sylvester bound): if `S, T ≥ γ I` with `γ > 0`, then
  `‖S - T‖ ≤ ‖S² - T²‖ / (2γ)` (from `S² - T² = S(S-T) + (S-T)T`; no differentiability).
* **`exists_sqrt_of_posDef`**: if `a` is `C²` (indeed `C¹` suffices) on the open `U` with
  `a(y)` positive definite on `U`, then `σ = psdSqrt ∘ a` is locally Lipschitz on `U`,
  `σ σᵀ = a` and `det σ ≠ 0` on `U`.
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open Matrix Filter Topology Set
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {d : ℕ}

/-- The quadratic-form lower bound `A ≥ c I`. -/
def QuadGe (A : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) : Prop :=
  ∀ v : Fin d → ℝ, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)

/-- The spectral square root `U diag(√λ) Uᵀ` of a symmetric matrix (`0` otherwise). -/
def psdSqrt (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  if h : A.IsHermitian then
    (h.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) * diagonal (fun i => √(h.eigenvalues i)) *
      (h.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᵀ
  else 0

theorem unitary_transpose_mul (U : Matrix.unitaryGroup (Fin d) ℝ) :
    (U : Matrix (Fin d) (Fin d) ℝ)ᵀ * U = 1 := by
  have h := Unitary.coe_star_mul_self U
  rwa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

theorem unitary_mul_transpose (U : Matrix.unitaryGroup (Fin d) ℝ) :
    (U : Matrix (Fin d) (Fin d) ℝ) * (U : Matrix (Fin d) (Fin d) ℝ)ᵀ = 1 := by
  exact mul_eq_one_comm.1 (unitary_transpose_mul U)

theorem spectral_real {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) * diagonal hA.eigenvalues *
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᵀ := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]

/-- Quadratic form of `U diag(f) Uᵀ`. -/
theorem dotProduct_conj_diagonal (U : Matrix (Fin d) (Fin d) ℝ) (f v : Fin d → ℝ) :
    v ⬝ᵥ ((U * diagonal f * Uᵀ) *ᵥ v) = ∑ i, f i * (Uᵀ *ᵥ v) i ^ 2 := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dotProduct_transpose_mulVec {U : Matrix (Fin d) (Fin d) ℝ} (hU : U * Uᵀ = 1)
    (v : Fin d → ℝ) : (Uᵀ *ᵥ v) ⬝ᵥ (Uᵀ *ᵥ v) = v ⬝ᵥ v := by
  rw [mulVec_transpose, ← dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hU, one_mulVec]

theorem sum_sq_transpose_mulVec {U : Matrix (Fin d) (Fin d) ℝ} (hU : U * Uᵀ = 1)
    (v : Fin d → ℝ) : ∑ i, (Uᵀ *ᵥ v) i ^ 2 = v ⬝ᵥ v := by
  rw [← dotProduct_transpose_mulVec hU v]
  simp only [dotProduct, sq]

/-- `U diag(f) Uᵀ ≥ c I` when every `f i ≥ c`. -/
theorem quadGe_conj_diagonal (U : Matrix.unitaryGroup (Fin d) ℝ) {f : Fin d → ℝ} {c : ℝ}
    (hf : ∀ i, c ≤ f i) : QuadGe ((U : Matrix (Fin d) (Fin d) ℝ) * diagonal f *
      (U : Matrix (Fin d) (Fin d) ℝ)ᵀ) c := fun v => by
  rw [dotProduct_conj_diagonal, ← sum_sq_transpose_mulVec (unitary_mul_transpose U) v,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hf i) (sq_nonneg _)

/-- `A ≥ c I` bounds every eigenvalue below by `c`. -/
theorem le_eigenvalues_of_quadGe {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) {c : ℝ}
    (hc : QuadGe A c) (i : Fin d) : c ≤ hA.eigenvalues i := by
  set U := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  have h := hc (U *ᵥ Pi.single i 1)
  have hw : Uᵀ *ᵥ (U *ᵥ Pi.single i 1) = Pi.single i 1 := by
    rw [mulVec_mulVec, unitary_transpose_mul, one_mulVec]
  have hA' := spectral_real hA
  rw [← hA'] at hA'
  rw [← dotProduct_transpose_mulVec (unitary_mul_transpose hA.eigenvectorUnitary), hw,
    spectral_real hA, dotProduct_conj_diagonal, hw] at h
  simpa [Pi.single_apply] using h

theorem eigenvalues_nonneg_of_quadGe {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : QuadGe A c) (i : Fin d) : 0 ≤ hA.eigenvalues i :=
  hc0.trans (le_eigenvalues_of_quadGe hA hc i)

theorem psdSqrt_eq {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    psdSqrt A = (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *
      diagonal (fun i => √(hA.eigenvalues i)) *
        (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᵀ := by
  simp only [psdSqrt, hA, ↓reduceDIte]

/-- `√A · √A = A` for symmetric `A` with nonnegative eigenvalues. -/
theorem psdSqrt_mul_self {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (h0 : ∀ i, 0 ≤ hA.eigenvalues i) : psdSqrt A * psdSqrt A = A := by
  set U := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  have hU := unitary_transpose_mul hA.eigenvectorUnitary
  rw [psdSqrt_eq hA]
  conv_rhs => rw [spectral_real hA]
  calc U * diagonal (fun i => √(hA.eigenvalues i)) * Uᵀ *
        (U * diagonal (fun i => √(hA.eigenvalues i)) * Uᵀ)
      = U * diagonal (fun i => √(hA.eigenvalues i)) * (Uᵀ * U) *
        diagonal (fun i => √(hA.eigenvalues i)) * Uᵀ := by simp only [Matrix.mul_assoc]
    _ = U * diagonal hA.eigenvalues * Uᵀ := by
        rw [hU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]
        congr 3
        funext i
        exact Real.mul_self_sqrt (h0 i)

theorem psdSqrt_transpose {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    (psdSqrt A)ᵀ = psdSqrt A := by
  rw [psdSqrt_eq hA, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose,
    Matrix.mul_assoc]

/-- `A ≥ c I` with `c ≥ 0` gives `√A ≥ √c I`. -/
theorem quadGe_psdSqrt {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) {c : ℝ}
    (hc : QuadGe A c) : QuadGe (psdSqrt A) √c := by
  rw [psdSqrt_eq hA]
  exact quadGe_conj_diagonal _ fun i => Real.sqrt_le_sqrt (le_eigenvalues_of_quadGe hA hc i)

/-- Sum of squared entries. -/
def sumSq (M : Matrix (Fin d) (Fin d) ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

theorem sumSq_nonneg (M : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ sumSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm_eq_sqrt_sumSq (M : Matrix (Fin d) (Fin d) ℝ) : ‖M‖ = √(sumSq M) := by
  rw [frobenius_norm_def, Real.sqrt_eq_rpow, sumSq]
  simp only [Real.norm_eq_abs]
  norm_num

theorem abs_entry_le_norm (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) : |M i j| ≤ ‖M‖ := by
  rw [norm_eq_sqrt_sumSq, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  calc M i j ^ 2 ≤ ∑ j', M i j' ^ 2 :=
        Finset.single_le_sum (f := fun j' => M i j' ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ sumSq M := Finset.single_le_sum (f := fun i' => ∑ j', M i' j' ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)

/-- `|vᵀ M v| ≤ d ‖M‖ |v|²`. -/
theorem abs_dotProduct_mulVec_le (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    |v ⬝ᵥ (M *ᵥ v)| ≤ d * ‖M‖ * (v ⬝ᵥ v) := by
  have hterm : ∀ i j, |v i * (M i j * v j)| ≤ ‖M‖ * ((v i ^ 2 + v j ^ 2) / 2) := by
    intro i j
    rw [abs_mul, abs_mul, ← mul_assoc, mul_comm |v i|, mul_assoc]
    refine mul_le_mul (abs_entry_le_norm M i j) ?_ (by positivity) (norm_nonneg _)
    nlinarith [sq_nonneg (|v i| - |v j|), sq_abs (v i), sq_abs (v j)]
  calc |v ⬝ᵥ (M *ᵥ v)| = |∑ i, ∑ j, v i * (M i j * v j)| := by
        simp only [dotProduct, mulVec, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, ‖M‖ * ((v i ^ 2 + v j ^ 2) / 2) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hterm i j))
    _ = d * ‖M‖ * (v ⬝ᵥ v) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, dotProduct, ← Finset.sum_div]
        simp only [sq]
        ring

theorem sum_mul_mul_left (S X : Matrix (Fin d) (Fin d) ℝ) :
    ∑ i, ∑ j, X i j * (S * X) i j = ∑ j, (fun i => X i j) ⬝ᵥ (S *ᵥ fun i => X i j) := by
  rw [Finset.sum_comm]
  simp only [dotProduct, mulVec, mul_apply]

theorem sum_mul_mul_right (T X : Matrix (Fin d) (Fin d) ℝ) :
    ∑ i, ∑ j, X i j * (X * T) i j = ∑ i, X i ⬝ᵥ (T *ᵥ X i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [dotProduct, mulVec, mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Sylvester bound.** If `S, T ≥ γ I` with `γ > 0` then `Σ (S-T)²_{ij} ≤ Σ (S²-T²)²_{ij}/(4γ²)`. -/
theorem sumSq_sub_le_of_quadGe {S T : Matrix (Fin d) (Fin d) ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hS : QuadGe S γ) (hT : QuadGe T γ) :
    sumSq (S - T) ≤ sumSq (S * S - T * T) / (4 * γ ^ 2) := by
  set X := S - T
  set D := S * S - T * T
  have hD : D = S * X + X * T := by
    simp only [D, X, Matrix.mul_sub, Matrix.sub_mul]; abel
  have hlow : 2 * γ * sumSq X ≤ ∑ i, ∑ j, X i j * D i j := by
    have e : ∑ i, ∑ j, X i j * D i j =
        ∑ i, ∑ j, X i j * (S * X) i j + ∑ i, ∑ j, X i j * (X * T) i j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hD, Matrix.add_apply, mul_add]
    rw [e, sum_mul_mul_left, sum_mul_mul_right]
    have h1 : γ * sumSq X ≤ ∑ j, (fun i => X i j) ⬝ᵥ (S *ᵥ fun i => X i j) := by
      rw [sumSq, Finset.sum_comm, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => by
        have := hS fun i => X i j
        simpa [dotProduct, sq] using this
    have h2 : γ * sumSq X ≤ ∑ i, X i ⬝ᵥ (T *ᵥ X i) := by
      rw [sumSq, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => by
        have := hT (X i)
        simpa [dotProduct, sq] using this
    linarith
  have hup : ∑ i, ∑ j, X i j * D i j ≤ γ * sumSq X + sumSq D / (4 * γ) := by
    rw [sumSq, sumSq, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have key : γ * X i j ^ 2 + D i j ^ 2 / (4 * γ) - X i j * D i j =
        (2 * γ * X i j - D i j) ^ 2 / (4 * γ) := by field_simp; ring
    have : 0 ≤ (2 * γ * X i j - D i j) ^ 2 / (4 * γ) := by positivity
    linarith
  have hX := sumSq_nonneg X
  rw [le_div_iff₀ (by positivity)]
  have : γ * sumSq X ≤ sumSq D / (4 * γ) := by linarith
  rw [le_div_iff₀ (by positivity)] at this
  nlinarith

/-- **Sylvester bound, norm form**: `‖S - T‖ ≤ ‖S² - T²‖ / (2γ)` for `S, T ≥ γ I`, `γ > 0`. -/
theorem norm_sub_le_of_quadGe {S T : Matrix (Fin d) (Fin d) ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hS : QuadGe S γ) (hT : QuadGe T γ) : ‖S - T‖ ≤ ‖S * S - T * T‖ / (2 * γ) := by
  rw [norm_eq_sqrt_sumSq, norm_eq_sqrt_sumSq]
  calc √(sumSq (S - T)) ≤ √(sumSq (S * S - T * T) / (4 * γ ^ 2)) :=
        Real.sqrt_le_sqrt (sumSq_sub_le_of_quadGe hγ hS hT)
    _ = √(sumSq (S * S - T * T)) / (2 * γ) := by
        rw [Real.sqrt_div' _ (by positivity), show (4 * γ ^ 2) = (2 * γ) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]

/-- A positive definite matrix is `≥ c I` for some `c > 0`. -/
theorem exists_quadGe_of_posDef {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef) :
    ∃ c > 0, QuadGe A c := by
  classical
  set f := hA.isHermitian.eigenvalues
  set m := (Finset.univ.image f ∪ {1}).min' (by simp)
  have hm : ∀ i, m ≤ f i := fun i => Finset.min'_le _ _ (by simp)
  have hm0 : 0 < m := by
    have hx := Finset.min'_mem (Finset.univ.image f ∪ {1}) (by simp)
    rcases Finset.mem_union.1 hx with h | h
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
      change 0 < (Finset.univ.image f ∪ {1}).min' _
      rw [← hi]; exact hA.eigenvalues_pos i
    · change 0 < (Finset.univ.image f ∪ {1}).min' _
      rw [Finset.mem_singleton.1 h]; exact one_pos
  refine ⟨m, hm0, ?_⟩
  have := quadGe_conj_diagonal hA.isHermitian.eigenvectorUnitary hm
  rwa [← spectral_real hA.isHermitian] at this

theorem quadGe_of_near {A B : Matrix (Fin d) (Fin d) ℝ} {c : ℝ} (hA : QuadGe A (2 * c))
    (hB : d * ‖B - A‖ ≤ c) : QuadGe B c := fun v => by
  have h1 := hA v
  have h2 := abs_dotProduct_mulVec_le (B - A) v
  have hvv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have e : v ⬝ᵥ (B *ᵥ v) = v ⬝ᵥ (A *ᵥ v) + v ⬝ᵥ ((B - A) *ᵥ v) := by
    rw [sub_mulVec, dotProduct_sub]; ring
  rw [e]
  have h3 : -(c * (v ⬝ᵥ v)) ≤ v ⬝ᵥ ((B - A) *ᵥ v) := by
    have := (abs_le.1 (h2.trans (mul_le_mul_of_nonneg_right hB hvv))).1
    linarith
  linarith

/-- **A locally Lipschitz square root of a positive definite `C²` covariance.** -/
theorem exists_sqrt_of_posDef {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) (ha : ContDiffOn ℝ 2 a U)
    (hpos : ∀ y ∈ U, (a y).PosDef) :
    ∃ σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ, LocallyLipschitzOn U σ ∧
      (∀ y ∈ U, σ y * (σ y).transpose = a y) ∧ (∀ y ∈ U, IsUnit (σ y).det) := by
  have hsq : ∀ y ∈ U, psdSqrt (a y) * psdSqrt (a y) = a y := fun y hy => by
    obtain ⟨c, hc, hq⟩ := exists_quadGe_of_posDef (hpos y hy)
    exact psdSqrt_mul_self (hpos y hy).isHermitian
      (eigenvalues_nonneg_of_quadGe _ hc.le hq)
  refine ⟨fun y => psdSqrt (a y), fun x hx => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨c₂, hc₂, hq⟩ := exists_quadGe_of_posDef (hpos x hx)
    set c := c₂ / 2
    have hc : 0 < c := by positivity
    have hq' : QuadGe (a x) (2 * c) := by rwa [show 2 * c = c₂ by ring]
    obtain ⟨K, t, ht, hK⟩ :=
      ((ha.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num) : ContDiffAt ℝ 1 a x)
        |>.exists_lipschitzOnWith
    have hcont : ContinuousAt (fun y => (d : ℝ) * ‖a y - a x‖) x :=
      continuousAt_const.mul ((((ha.continuousOn.continuousAt (hU.mem_nhds hx)).sub
        continuousAt_const)).norm)
    have hnear : {y | (d : ℝ) * ‖a y - a x‖ < c} ∈ 𝓝 x :=
      hcont (Iio_mem_nhds (by simpa using hc))
    set γ := √c
    have hγ : 0 < γ := Real.sqrt_pos.2 hc
    refine ⟨Real.toNNReal (K / (2 * γ)), t ∩ ({y | (d : ℝ) * ‖a y - a x‖ < c} ∩ U),
      mem_nhdsWithin_of_mem_nhds (Filter.inter_mem ht (Filter.inter_mem hnear
        (hU.mem_nhds hx))), LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_⟩
    have hqy : ∀ w ∈ t ∩ ({y | (d : ℝ) * ‖a y - a x‖ < c} ∩ U),
        QuadGe (psdSqrt (a w)) γ := fun w hw =>
      quadGe_psdSqrt (hpos w hw.2.2).isHermitian (quadGe_of_near hq' hw.2.1.le)
    rw [dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    calc ‖psdSqrt (a y) - psdSqrt (a z)‖
        ≤ ‖psdSqrt (a y) * psdSqrt (a y) - psdSqrt (a z) * psdSqrt (a z)‖ / (2 * γ) :=
          norm_sub_le_of_quadGe hγ (hqy y hy) (hqy z hz)
      _ = dist (a y) (a z) / (2 * γ) := by rw [hsq y hy.2.2, hsq z hz.2.2, dist_eq_norm]
      _ ≤ K * dist y z / (2 * γ) := by
          gcongr; exact hK.dist_le_mul y hy.1 z hz.1
      _ = K / (2 * γ) * dist y z := by ring
  · rw [psdSqrt_transpose (hpos y hy).isHermitian]; exact hsq y hy
  · have h := congrArg Matrix.det (hsq y hy)
    rw [det_mul] at h
    have hd : (a y).det ≠ 0 := (hpos y hy).det_pos.ne'
    refine isUnit_iff_ne_zero.2 fun h0 => hd ?_
    rw [← h, h0, zero_mul]

end BlockBand.SourceProcess.Stochastic.Uniqueness
