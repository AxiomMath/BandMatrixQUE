module

public import BlockBand.Endpoints.Sine.FredholmDefs

/-!
# Absolute convergence and continuity of Fredholm expansions

For a σ-finite measure `ν`, a weight `φ ∈ L¹(ν)` and a jointly Borel kernel whose Gram
determinants are bounded by one, the Fredholm terms satisfy the Hadamard-type bound
`|fredholmTerm K ν φ k| ≤ (∫ |φ| dν)^k / k!`, so the series converges absolutely with an explicit
tail bound (`abs_fredholmSeries_sub_sum_le`). The series is continuous under pointwise
convergence of such kernels (`tendsto_fredholmSeries`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter
open scoped Topology

/-- The Leibniz determinant is continuous on real square matrices of any size. -/
theorem continuous_matrix_det_fin (k : ℕ) :
    Continuous (fun M : Matrix (Fin k) (Fin k) ℝ => M.det) :=
  continuous_id.matrix_det

/-- For a jointly Borel kernel `K`, the Gram determinant
`x ↦ det [K (x i) (x j)]` is Borel on `Fin k → ℝ`. -/
theorem measurable_det_kernel {K : ℝ → ℝ → ℝ} (hK : Measurable (Function.uncurry K))
    (k : ℕ) :
    Measurable (fun x : Fin k → ℝ => Matrix.det (fun i j : Fin k => K (x i) (x j))) := by
  have hm : Measurable (fun x : Fin k → ℝ => fun i j : Fin k => K (x i) (x j)) := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    exact hK.comp (f := fun a : Fin k → ℝ => (a i, a j))
      ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  exact (continuous_matrix_det_fin k).measurable.comp hm

/-- Pointwise domination of the Fredholm integrand: if all Gram determinants of
`K` are bounded by one, then for every `k` and `x : Fin k → ℝ`,
`|det [K (x i) (x j)] * ∏ φ (x i)| ≤ ∏ |φ (x i)|`. -/
theorem abs_fredholmIntegrand_le {K : ℝ → ℝ → ℝ}
    (hdet : ∀ (k : ℕ) (x : Fin k → ℝ), |Matrix.det (fun i j : Fin k => K (x i) (x j))| ≤ 1)
    (φ : ℝ → ℝ) (k : ℕ) (x : Fin k → ℝ) :
    |Matrix.det (fun i j : Fin k => K (x i) (x j)) * ∏ i : Fin k, φ (x i)| ≤
      ∏ i : Fin k, |φ (x i)| := by
  rw [abs_mul, Finset.abs_prod]
  calc _ ≤ 1 * ∏ i : Fin k, |φ (x i)| :=
        mul_le_mul_of_nonneg_right (hdet k x) (Finset.prod_nonneg fun i _ => abs_nonneg _)
    _ = _ := one_mul _

/-- Integrability of the Fredholm integrand on `(Fin k → ℝ, ν^k)`, for `ν`
σ-finite, `K` jointly Borel with Gram determinants bounded by one, and
`φ ∈ L¹(ν)`. -/
theorem integrable_fredholmIntegrand {K : ℝ → ℝ → ℝ} (hK : Measurable (Function.uncurry K))
    (hdet : ∀ (k : ℕ) (x : Fin k → ℝ), |Matrix.det (fun i j : Fin k => K (x i) (x j))| ≤ 1)
    {ν : Measure ℝ} [SigmaFinite ν] {φ : ℝ → ℝ} (hφ : Integrable φ ν) (k : ℕ) :
    Integrable (fun x : Fin k → ℝ =>
        Matrix.det (fun i j : Fin k => K (x i) (x j)) * ∏ i : Fin k, φ (x i))
      (Measure.pi fun _ : Fin k => ν) := by
  have hp : Integrable (fun x : Fin k → ℝ => ∏ i : Fin k, φ (x i))
      (Measure.pi fun _ : Fin k => ν) :=
    Integrable.fintype_prod (f := fun _ : Fin k => φ) fun _ => hφ
  refine hp.bdd_mul (c := 1) (measurable_det_kernel hK k).aestronglyMeasurable ?_
  exact Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hdet k x

/-- Hadamard-type bound. For `ν` σ-finite, `φ ∈ L¹(ν)` and a kernel whose Gram determinants are
bounded by one, for every `k : ℕ`, `|fredholmIntegral K ν φ k| ≤ (∫ |φ| dν) ^ k`. -/
theorem abs_fredholmIntegral_le {K : ℝ → ℝ → ℝ}
    (hdet : ∀ (k : ℕ) (x : Fin k → ℝ), |Matrix.det (fun i j : Fin k => K (x i) (x j))| ≤ 1)
    {ν : Measure ℝ} [SigmaFinite ν] {φ : ℝ → ℝ} (hφ : Integrable φ ν) (k : ℕ) :
    |fredholmIntegral K ν φ k| ≤ (∫ x, |φ x| ∂ν) ^ k := by
  unfold fredholmIntegral
  have hp : Integrable (fun x : Fin k → ℝ => ∏ i : Fin k, |φ (x i)|)
      (Measure.pi fun _ : Fin k => ν) :=
    Integrable.fintype_prod (f := fun _ : Fin k => fun y => |φ y|) fun _ => hφ.abs
  calc _ ≤ ∫ x : Fin k → ℝ,
        |Matrix.det (fun i j : Fin k => K (x i) (x j)) * ∏ i : Fin k, φ (x i)|
        ∂Measure.pi (fun _ : Fin k => ν) := abs_integral_le_integral_abs
    _ ≤ ∫ x : Fin k → ℝ, ∏ i : Fin k, |φ (x i)| ∂Measure.pi (fun _ : Fin k => ν) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hp
          (Eventually.of_forall fun x => abs_fredholmIntegrand_le hdet φ k x)
    _ = _ := by
        rw [integral_fintype_prod_eq_pow (fun y => |φ y|), Fintype.card_fin]

/-- Termwise bound `|fredholmTerm K ν φ k| ≤ (∫ |φ| dν) ^ k / k!`, for `ν`
σ-finite, `φ ∈ L¹(ν)` and Gram determinants of `K` bounded by one. -/
theorem abs_fredholmTerm_le {K : ℝ → ℝ → ℝ}
    (hdet : ∀ (k : ℕ) (x : Fin k → ℝ), |Matrix.det (fun i j : Fin k => K (x i) (x j))| ≤ 1)
    {ν : Measure ℝ} [SigmaFinite ν] {φ : ℝ → ℝ} (hφ : Integrable φ ν) (k : ℕ) :
    |fredholmTerm K ν φ k| ≤ (∫ x, |φ x| ∂ν) ^ k / (Nat.factorial k : ℝ) := by
  have hf : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  unfold fredholmTerm
  rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast, one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right (abs_fredholmIntegral_le hdet hφ k) hf.le

/-- Absolute summability of the Fredholm terms (σ-finite `ν`, `φ ∈ L¹(ν)`,
Gram determinants of `K` bounded by one). -/
theorem summable_abs_fredholmTerm {K : ℝ → ℝ → ℝ}
    (hdet : ∀ (k : ℕ) (x : Fin k → ℝ), |Matrix.det (fun i j : Fin k => K (x i) (x j))| ≤ 1)
    {ν : Measure ℝ} [SigmaFinite ν] {φ : ℝ → ℝ} (hφ : Integrable φ ν) :
    Summable (fun k => |fredholmTerm K ν φ k|) :=
  (Real.summable_pow_div_factorial _).of_nonneg_of_le (fun _ => abs_nonneg _)
    (abs_fredholmTerm_le hdet hφ)

/-- Summability of the Fredholm terms (σ-finite `ν`, `φ ∈ L¹(ν)`, Gram
determinants of `K` bounded by one). -/
theorem summable_fredholmTerm {K : ℝ → ℝ → ℝ}
    (hdet : ∀ (k : ℕ) (x : Fin k → ℝ), |Matrix.det (fun i j : Fin k => K (x i) (x j))| ≤ 1)
    {ν : Measure ℝ} [SigmaFinite ν] {φ : ℝ → ℝ} (hφ : Integrable φ ν) :
    Summable (fredholmTerm K ν φ) :=
  (summable_abs_fredholmTerm hdet hφ).of_abs

/-- The Fredholm terms sum to `fredholmSeries K ν φ` (σ-finite `ν`,
`φ ∈ L¹(ν)`, Gram determinants of `K` bounded by one). -/
theorem hasSum_fredholmTerm {K : ℝ → ℝ → ℝ}
    (hdet : ∀ (k : ℕ) (x : Fin k → ℝ), |Matrix.det (fun i j : Fin k => K (x i) (x j))| ≤ 1)
    {ν : Measure ℝ} [SigmaFinite ν] {φ : ℝ → ℝ} (hφ : Integrable φ ν) :
    HasSum (fredholmTerm K ν φ) (fredholmSeries K ν φ) :=
  (summable_fredholmTerm hdet hφ).hasSum

/-- The real exponential series: `∑ k, a ^ k / k! = exp a`. -/
theorem hasSum_pow_div_factorial_exp (a : ℝ) :
    HasSum (fun k : ℕ => a ^ k / (Nat.factorial k : ℝ)) (Real.exp a) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp a

/-- Tail bound. For σ-finite `ν`, `φ ∈ L¹(ν)`, Gram determinants of `K` bounded by one and every
`n : ℕ`, with `A = ∫ |φ| dν`,
`|fredholmSeries K ν φ - ∑_{k < n} fredholmTerm K ν φ k| ≤ A ^ n / n! * exp A`. -/
theorem abs_fredholmSeries_sub_sum_le {K : ℝ → ℝ → ℝ}
    (hdet : ∀ (k : ℕ) (x : Fin k → ℝ), |Matrix.det (fun i j : Fin k => K (x i) (x j))| ≤ 1)
    {ν : Measure ℝ} [SigmaFinite ν] {φ : ℝ → ℝ} (hφ : Integrable φ ν) (n : ℕ) :
    |fredholmSeries K ν φ - ∑ k ∈ Finset.range n, fredholmTerm K ν φ k| ≤
      (∫ x, |φ x| ∂ν) ^ n / (Nat.factorial n : ℝ) * Real.exp (∫ x, |φ x| ∂ν) := by
  set A := ∫ x, |φ x| ∂ν with hA
  have hA0 : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  have hs := summable_fredholmTerm hdet hφ
  have hsa := summable_abs_fredholmTerm hdet hφ
  have htail : fredholmSeries K ν φ - ∑ k ∈ Finset.range n, fredholmTerm K ν φ k =
      ∑' k, fredholmTerm K ν φ (k + n) := by
    unfold fredholmSeries
    rw [← hs.sum_add_tsum_nat_add n]
    ring
  rw [htail]
  have hsn : Summable (fun k => |fredholmTerm K ν φ (k + n)|) :=
    (summable_nat_add_iff n).2 hsa
  have hexp := hasSum_pow_div_factorial_exp A
  have hbound (k : ℕ) : |fredholmTerm K ν φ (k + n)| ≤ A ^ n / (Nat.factorial n : ℝ) * (A ^ k / (Nat.factorial k : ℝ)) := by
    refine (abs_fredholmTerm_le hdet hφ (k + n)).trans ?_
    have hk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hn : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hkn : ((Nat.factorial n * Nat.factorial k : ℕ) : ℝ) ≤ (Nat.factorial (k + n) : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
        (by rw [add_comm]; exact Nat.factorial_mul_factorial_dvd_factorial_add n k)
    push_cast at hkn
    rw [div_mul_div_comm, pow_add, mul_comm (A ^ k)]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hkn
  calc |∑' k, fredholmTerm K ν φ (k + n)| ≤ ∑' k, |fredholmTerm K ν φ (k + n)| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun k =>
          fredholmTerm K ν φ (k + n)) (by simpa only [Real.norm_eq_abs] using hsn)
    _ ≤ ∑' k, A ^ n / (Nat.factorial n : ℝ) * (A ^ k / (Nat.factorial k : ℝ)) :=
        hsn.tsum_le_tsum hbound (hexp.summable.mul_left _)
    _ = _ := by rw [tsum_mul_left, hexp.tsum_eq]

/-- The zeroth Fredholm integral is `1`, for every kernel, weight and measure
`ν` (the empty product measure is the unit Dirac mass). -/
theorem fredholmIntegral_zero (K : ℝ → ℝ → ℝ) (ν : Measure ℝ) (φ : ℝ → ℝ) :
    fredholmIntegral K ν φ 0 = 1 := by
  unfold fredholmIntegral
  have h1 (x : Fin 0 → ℝ) :
      Matrix.det (fun i j : Fin 0 => K (x i) (x j)) * ∏ i : Fin 0, φ (x i) = 1 := by
    have hd : Matrix.det (fun i j : Fin 0 => K (x i) (x j)) = 1 := Matrix.det_isEmpty
    rw [hd, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  simp_rw [h1]
  rw [Measure.pi_of_empty]
  simp

/-- The first Fredholm integral is `∫ K x x * φ x dν`, for every kernel, weight
and measure `ν`. -/
theorem fredholmIntegral_one (K : ℝ → ℝ → ℝ) (ν : Measure ℝ) (φ : ℝ → ℝ) :
    fredholmIntegral K ν φ 1 = ∫ x, K x x * φ x ∂ν := by
  unfold fredholmIntegral
  refine Eq.trans ?_
    ((measurePreserving_funUnique ν (Fin 1)).integral_comp' (fun y => K y y * φ y))
  congr 1
  funext x
  have hd : Matrix.det (fun i j : Fin 1 => K (x i) (x j)) = K (x 0) (x 0) :=
    Matrix.det_unique _
  rw [hd, Fin.prod_univ_one]
  rfl

/-- Fredholm integrals only see `ν` on a set `W` off which the weight vanishes:
for σ-finite `ν`, `W : Set ℝ` (no measurability needed) and `φ = 0` off `W`,
`fredholmIntegral K (ν.restrict W) φ k = fredholmIntegral K ν φ k` for all `k`. -/
theorem fredholmIntegral_restrict (K : ℝ → ℝ → ℝ) {ν : Measure ℝ} [SigmaFinite ν]
    {φ : ℝ → ℝ} {W : Set ℝ} (hφ : ∀ x, x ∉ W → φ x = 0) (k : ℕ) :
    fredholmIntegral K (ν.restrict W) φ k = fredholmIntegral K ν φ k := by
  unfold fredholmIntegral
  rw [← Measure.restrict_pi_pi]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
  obtain ⟨i, hi⟩ := hx
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (hφ _ hi), mul_zero]

/-- Fredholm series only see `ν` on a set `W` off which the weight vanishes:
for σ-finite `ν` and `φ = 0` off `W`,
`fredholmSeries K (ν.restrict W) φ = fredholmSeries K ν φ`. -/
theorem fredholmSeries_restrict (K : ℝ → ℝ → ℝ) {ν : Measure ℝ} [SigmaFinite ν]
    {φ : ℝ → ℝ} {W : Set ℝ} (hφ : ∀ x, x ∉ W → φ x = 0) :
    fredholmSeries K (ν.restrict W) φ = fredholmSeries K ν φ := by
  unfold fredholmSeries fredholmTerm
  simp_rw [fredholmIntegral_restrict K hφ]

/-- Gram determinants converge under pointwise convergence of kernels: if
`Kn n x y → K x y` for all `x y`, then for every `k` and `x : Fin k → ℝ`,
`det [Kn n (x i) (x j)] → det [K (x i) (x j)]` as `n → ∞`. -/
theorem tendsto_det_kernel {Kn : ℕ → ℝ → ℝ → ℝ} {K : ℝ → ℝ → ℝ}
    (hconv : ∀ x y, Tendsto (fun n => Kn n x y) atTop (𝓝 (K x y))) (k : ℕ) (x : Fin k → ℝ) :
    Tendsto (fun n => Matrix.det (fun i j : Fin k => Kn n (x i) (x j))) atTop
      (𝓝 (Matrix.det (fun i j : Fin k => K (x i) (x j)))) := by
  have hm : Tendsto (fun n => (fun i j : Fin k => Kn n (x i) (x j) : Matrix (Fin k) (Fin k) ℝ))
      atTop (𝓝 (fun i j : Fin k => K (x i) (x j))) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hconv _ _
  exact ((continuous_matrix_det_fin k).tendsto _).comp hm

/-- The determinant bound passes to pointwise limits: if every kernel `Kn n`
has all Gram determinants bounded by one in absolute value and `Kn n → K`
pointwise, then so does `K`. -/
theorem abs_det_le_one_of_tendsto {Kn : ℕ → ℝ → ℝ → ℝ} {K : ℝ → ℝ → ℝ}
    (hdetn : ∀ (n k : ℕ) (x : Fin k → ℝ),
      |Matrix.det (fun i j : Fin k => Kn n (x i) (x j))| ≤ 1)
    (hconv : ∀ x y, Tendsto (fun n => Kn n x y) atTop (𝓝 (K x y))) :
    ∀ (k : ℕ) (x : Fin k → ℝ), |Matrix.det (fun i j : Fin k => K (x i) (x j))| ≤ 1 :=
  fun k x => le_of_tendsto' ((continuous_abs.tendsto _).comp (tendsto_det_kernel hconv k x))
    fun n => hdetn n k x

/-- Termwise kernel continuity of Fredholm integrals: kernels `Kn n`, jointly
Borel with Gram determinants bounded by one, converging pointwise to `K`; for
σ-finite `ν` and `φ ∈ L¹(ν)`, for each `k`,
`fredholmIntegral (Kn n) ν φ k → fredholmIntegral K ν φ k`. -/
theorem tendsto_fredholmIntegral {Kn : ℕ → ℝ → ℝ → ℝ} {K : ℝ → ℝ → ℝ}
    (hKn : ∀ n, Measurable (Function.uncurry (Kn n)))
    (hdetn : ∀ (n k : ℕ) (x : Fin k → ℝ),
      |Matrix.det (fun i j : Fin k => Kn n (x i) (x j))| ≤ 1)
    (hconv : ∀ x y, Tendsto (fun n => Kn n x y) atTop (𝓝 (K x y)))
    {ν : Measure ℝ} [SigmaFinite ν] {φ : ℝ → ℝ} (hφ : Integrable φ ν) (k : ℕ) :
    Tendsto (fun n => fredholmIntegral (Kn n) ν φ k) atTop
      (𝓝 (fredholmIntegral K ν φ k)) := by
  unfold fredholmIntegral
  refine tendsto_integral_of_dominated_convergence (fun x : Fin k → ℝ => ∏ i : Fin k, |φ (x i)|)
    (fun n => (integrable_fredholmIntegrand (hKn n) (hdetn n) hφ k).aestronglyMeasurable)
    (Integrable.fintype_prod (f := fun _ : Fin k => fun y => |φ y|) fun _ => hφ.abs)
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_fredholmIntegrand_le (hdetn n) φ k x)
    (Eventually.of_forall fun x => (tendsto_det_kernel hconv k x).mul_const _)

/-- Kernel continuity of the Fredholm expansion. Kernels `Kn n`, each jointly Borel with all
Gram determinants bounded by one, converging pointwise to `K`; for σ-finite `ν` and
`φ ∈ L¹(ν)`, `fredholmSeries (Kn n) ν φ → fredholmSeries K ν φ` as `n → ∞`. (No measurability or
determinant hypothesis on `K` is needed; the latter follows from `abs_det_le_one_of_tendsto`.) -/
theorem tendsto_fredholmSeries {Kn : ℕ → ℝ → ℝ → ℝ} {K : ℝ → ℝ → ℝ}
    (hKn : ∀ n, Measurable (Function.uncurry (Kn n)))
    (hdetn : ∀ (n k : ℕ) (x : Fin k → ℝ),
      |Matrix.det (fun i j : Fin k => Kn n (x i) (x j))| ≤ 1)
    (hconv : ∀ x y, Tendsto (fun n => Kn n x y) atTop (𝓝 (K x y)))
    {ν : Measure ℝ} [SigmaFinite ν] {φ : ℝ → ℝ} (hφ : Integrable φ ν) :
    Tendsto (fun n => fredholmSeries (Kn n) ν φ) atTop (𝓝 (fredholmSeries K ν φ)) := by
  unfold fredholmSeries
  refine tendsto_tsum_of_dominated_convergence (Real.summable_pow_div_factorial
    (∫ x, |φ x| ∂ν)) (fun k => ?_) (Eventually.of_forall fun n k => ?_)
  · unfold fredholmTerm
    exact (tendsto_fredholmIntegral hKn hdetn hconv hφ k).const_mul _
  · rw [Real.norm_eq_abs]
    exact abs_fredholmTerm_le (hdetn n) hφ k

end BlockBand.Endpoints
