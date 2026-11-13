module

public import BlockBand.Palm.ReferenceFlowKernel
public import BlockBand.Palm.ReferenceFlowRoot
public import BlockBand.Palm.ReferenceFlowParamInt
public import BlockBand.Palm.ReferenceFlowHeat
public import BlockBand.Palm.ReferenceFlowStatic
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Assembling `IsReferenceFlow` from the kernel, the root and the backward equation

The factor is the principal root `L_s = (I - K_s K_s^*)^{1/2}` (`refFactor`, via the binomial
series `sqrtOneSub`). Given

* the reflected rotation flow `𝓝`, with kernel `K_s = (𝓝_{c-s})ᴴ`,
* the kernel contraction `KernelContracts`, and
* the backward Kolmogorov equation on `(a,c)` (`BackwardEquationHolds`),

`isReferenceFlow_of` proves every clause of `IsReferenceFlow`: measurability, continuity of `K`
and `L`, `K_c = I`, the reference covariance identity `L Lᴴ = I - K Kᴴ`, contraction, the
principal-root bound, the mass clauses (`mass`, `mass_unique`), and the `backward` clause (`g_c =
f`,
continuity in `s`, `C²` in `z` with the derivative representations, and the backward equation).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow

open MeasureTheory Set Filter Matrix BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionFlow (IsRotationFlow LinearRotationFlowContract
  massGenerator)
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.Stochastic
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {N : ℕ} {S : Type} [MeasurableSpace S]

/-- The Ornstein–Uhlenbeck factor `L_s = (I - K_s K_s^*)^{1/2}`. -/
def refFactor (c : ℝ) (𝓝 : ℝ≥0 → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ)
    (s : ℝ) (y : DriverSample S (RotIdx N)) : Matrix (Fin N) (Fin N) ℂ :=
  sqrtOneSub (refKernel c 𝓝 s y * (refKernel c 𝓝 s y)ᴴ)

/-- The `contraction` clause, as a hypothesis on a kernel. -/
def KernelContracts (μ : Measure S) (κ : ℝ → Fin N → ℝ) (a c : ℝ)
    (K : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ b : ℝ, (∀ x ∈ Icc a c, ∀ k, b ≤ κ x k) →
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ s ∈ Icc a c, ∀ v : Fin N → ℂ,
      ∑ k, ‖(K s y *ᵥ v) k‖ ^ 2 ≤ Real.exp (-(b * (c - s))) * ∑ k, ‖v k‖ ^ 2

/-- The backward-equation clause, as a hypothesis. -/
def BackwardEquationHolds (μ : Measure S) (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ)
    (a c : ℝ) (K L : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ (p : ℕ) (C : ℝ) (f : RefState N p → ℝ), IsC2BoundedBy C f →
    ∀ s ∈ Ioo a c, ∀ z, HasDerivAt (fun x => refSemigroup μ K L f x z)
      (-refGenerator r κ s (refSemigroup μ K L f s) z) s

/-!
## Matrix facts
-/

theorem isHermitian_mul_conjTranspose_self' (K : Matrix (Fin N) (Fin N) ℂ) :
    (K * Kᴴ).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_mul]

theorem norm_entry_le_of_contraction {K : Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ v : Fin N → ℂ, ∑ k, ‖(K *ᵥ v) k‖ ^ 2 ≤ ∑ k, ‖v k‖ ^ 2)
    (i j : Fin N) : ‖K i j‖ ≤ 1 := by
  have hj := h (Pi.single j 1)
  have hv : ∑ k, ‖(Pi.single j (1 : ℂ) : Fin N → ℂ) k‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp
  have hcol : ∀ k, (K *ᵥ Pi.single j (1 : ℂ)) k = K k j := fun k => by
    simp [Matrix.mulVec_single]
  simp_rw [hcol, hv] at hj
  have hi : ‖K i j‖ ^ 2 ≤ 1 :=
    (Finset.single_le_sum (f := fun k => ‖K k j‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ i)).trans hj
  nlinarith [norm_nonneg (K i j)]

variable {μ : Measure S} [IsProbabilityMeasure μ] {r : ℝ → Fin N → Fin N → ℝ}
  {κ : ℝ → Fin N → ℝ} {a c : ℝ}
  {𝓝 : ℝ≥0 → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ}

/-!
## The factor
-/

theorem refFactor_terminal (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝)
    (hN : 0 < N) (y : DriverSample S (RotIdx N)) : refFactor c 𝓝 c y = 0 := by
  simp only [refFactor, refKernel_terminal h𝓝 y, Matrix.conjTranspose_one, mul_one]
  exact sqrtOneSub_of_not_lt (by rw [opNorm_one_of_pos hN]; exact lt_irrefl 1)

omit [IsProbabilityMeasure μ] in
theorem opNorm_kernel_le {K : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ}
    (hcon : KernelContracts μ κ a c K) {b : ℝ} (hb : ∀ x ∈ Icc a c, ∀ k, b ≤ κ x k) :
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ s ∈ Icc a c,
      opNorm (K s y * (K s y)ᴴ) ≤ Real.exp (-(b * (c - s))) := by
  filter_upwards [hcon b hb] with y hy s hs
  exact opNorm_mul_conjTranspose_le _ (Real.exp_pos _).le (hy s hs)

omit [IsProbabilityMeasure μ] in
theorem opNorm_kernel_lt {K : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ}
    (hcon : KernelContracts μ κ a c K) {b : ℝ} (hb0 : 0 < b)
    (hb : ∀ x ∈ Icc a c, ∀ k, b ≤ κ x k) :
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ s ∈ Ico a c, opNorm (K s y * (K s y)ᴴ) < 1 := by
  filter_upwards [opNorm_kernel_le hcon hb] with y hy s hs
  refine (hy s (Ico_subset_Icc_self hs)).trans_lt ?_
  rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
  exact Real.exp_lt_exp.2 (by nlinarith [mul_pos hb0 (sub_pos.2 hs.2)])

theorem matrix_subsingleton_zero (hN : N = 0) (A B : Matrix (Fin N) (Fin N) ℂ) : A = B := by
  subst hN
  ext i
  exact i.elim0

theorem refFactor_covariance
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝)
    (hcon : KernelContracts μ κ a c (refKernel c 𝓝)) {b : ℝ} (hb0 : 0 < b)
    (hfloor : ∀ x ∈ Icc a c, ∀ k, b ≤ κ x k) :
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ s ∈ Icc a c,
      refFactor c 𝓝 s y * (refFactor c 𝓝 s y)ᴴ = 1 - refKernel c 𝓝 s y * (refKernel c 𝓝 s y)ᴴ := by
  filter_upwards [opNorm_kernel_lt hcon hb0 hfloor] with y hy s hs
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact matrix_subsingleton_zero hN _ _
  rcases hs.2.lt_or_eq with h | h
  · have hA := hy s ⟨hs.1, h⟩
    have hH := sqrtOneSub_isHermitian hA (isHermitian_mul_conjTranspose_self' (refKernel c 𝓝 s y))
    rw [refFactor, hH.eq]
    exact sqrtOneSub_mul_self hA
  · rw [h, refFactor_terminal h𝓝 hN, refKernel_terminal h𝓝]
    simp

theorem refFactor_isHermitian
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝)
    (hcon : KernelContracts μ κ a c (refKernel c 𝓝)) {b : ℝ} (hb0 : 0 < b)
    (hfloor : ∀ x ∈ Icc a c, ∀ k, b ≤ κ x k) :
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ s ∈ Icc a c, (refFactor c 𝓝 s y).IsHermitian := by
  filter_upwards [opNorm_kernel_lt hcon hb0 hfloor] with y hy s hs
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact matrix_subsingleton_zero hN _ _
  rcases hs.2.lt_or_eq with h | h
  · exact sqrtOneSub_isHermitian (hy s ⟨hs.1, h⟩)
      (isHermitian_mul_conjTranspose_self' (refKernel c 𝓝 s y))
  · rw [h, refFactor_terminal h𝓝 hN]
    exact Matrix.isHermitian_zero

theorem exp_sq_eq (x : ℝ) : Real.exp (-x) ^ 2 = Real.exp (-(2 * x)) := by
  rw [sq, ← Real.exp_add]
  ring_nf

theorem refFactor_near_one
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝)
    (hcon : KernelContracts μ κ a c (refKernel c 𝓝)) {b : ℝ} (hb0 : 0 < b)
    (hfloor : ∀ x ∈ Icc a c, ∀ k, b ≤ κ x k) (b' : ℝ) (hb' : ∀ x ∈ Icc a c, ∀ k, b' ≤ κ x k) :
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ s ∈ Icc a c, ∀ v : Fin N → ℂ,
      ∑ k, ‖((1 - refFactor c 𝓝 s y) *ᵥ v) k‖ ^ 2 ≤
        Real.exp (-(2 * b' * (c - s))) * ∑ k, ‖v k‖ ^ 2 := by
  filter_upwards [opNorm_kernel_lt hcon hb0 hfloor, opNorm_kernel_le hcon hb'] with y hlt hle s hs v
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  rcases hs.2.lt_or_eq with h | h
  · refine (sqrtOneSub_one_sub_bound_of_lt (hlt s ⟨hs.1, h⟩) v).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => by positivity)
    have h0 : 0 ≤ opNorm (refKernel c 𝓝 s y * (refKernel c 𝓝 s y)ᴴ) := norm_nonneg _
    have h2 := pow_le_pow_left₀ h0 (hle s hs) 2
    rw [exp_sq_eq] at h2
    simpa [mul_assoc] using h2
  · rw [h, refFactor_terminal h𝓝 hN]
    simp

theorem continuous_mul_conjTranspose :
    Continuous fun M : Matrix (Fin N) (Fin N) ℂ => M * Mᴴ :=
  continuous_id.matrix_mul continuous_id.matrix_conjTranspose

theorem measurable_refFactor
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝) (s : ℝ) :
    Measurable (refFactor c 𝓝 s) :=
  measurable_sqrtOneSub.comp (continuous_mul_conjTranspose.measurable.comp
    (measurable_refKernel h𝓝 s))

theorem re_mul_conjTranspose_diag (M : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    ((M * Mᴴ) i i).re = ∑ k, ‖M i k‖ ^ 2 := by
  rw [Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.mul_re]
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem continuousOn_refFactor
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝)
    (hcon : KernelContracts μ κ a c (refKernel c 𝓝)) {b : ℝ} (hb0 : 0 < b)
    (hfloor : ∀ x ∈ Icc a c, ∀ k, b ≤ κ x k) :
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ContinuousOn (fun s => refFactor c 𝓝 s y) (Icc a c) := by
  filter_upwards [continuousOn_refKernel h𝓝, opNorm_kernel_lt hcon hb0 hfloor,
    refFactor_covariance h𝓝 hcon hb0 hfloor] with y hK hlt hcov
  rcases Nat.eq_zero_or_pos N with hN | hN
  · intro s _
    have : (fun s => refFactor c 𝓝 s y) = fun _ => refFactor c 𝓝 c y :=
      funext fun _ => matrix_subsingleton_zero hN _ _
    rw [this]
    exact continuousWithinAt_const
  intro s hs
  have hKK : ContinuousWithinAt (fun s => refKernel c 𝓝 s y * (refKernel c 𝓝 s y)ᴴ) (Icc a c) s :=
    continuous_mul_conjTranspose.continuousAt.comp_continuousWithinAt (hK s hs)
  rcases hs.2.lt_or_eq with h | h
  · show ContinuousWithinAt
        (fun s => sqrtOneSub (refKernel c 𝓝 s y * (refKernel c 𝓝 s y)ᴴ)) (Icc a c) s
    exact ContinuousAt.comp_continuousWithinAt (g := sqrtOneSub)
      (continuousOn_sqrtOneSub.continuousAt (isOpen_opNorm_lt_one.mem_nhds (hlt s ⟨hs.1, h⟩))) hKK
  · rw [h] at hKK ⊢
    have hL0 : refFactor c 𝓝 c y = 0 := refFactor_terminal h𝓝 hN y
    show Tendsto (fun s => refFactor c 𝓝 s y) (nhdsWithin c (Icc a c)) (nhds (refFactor c 𝓝 c y))
    rw [hL0]
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    -- `‖L_ij‖² ≤ Re (1 - K Kᴴ)_ii → 0`
    have he : Tendsto (fun s => ((1 - refKernel c 𝓝 s y * (refKernel c 𝓝 s y)ᴴ) i i).re)
        (nhdsWithin c (Icc a c)) (nhds 0) := by
      have h1 : ContinuousWithinAt (fun s => 1 - refKernel c 𝓝 s y * (refKernel c 𝓝 s y)ᴴ)
          (Icc a c) c := continuousWithinAt_const.sub hKK
      have hent : Continuous fun M : Matrix (Fin N) (Fin N) ℂ => (M i i).re :=
        Complex.continuous_re.comp (continuous_id.matrix_elem i i)
      have hc : ContinuousWithinAt
          (fun s => ((1 - refKernel c 𝓝 s y * (refKernel c 𝓝 s y)ᴴ) i i).re) (Icc a c) c :=
        hent.continuousAt.comp_continuousWithinAt h1
      have hv : ((1 - refKernel c 𝓝 c y * (refKernel c 𝓝 c y)ᴴ) i i).re = 0 := by
        rw [refKernel_terminal h𝓝]; simp
      rw [← hv]
      exact hc
    have hs : Tendsto (fun s => Real.sqrt
        (((1 - refKernel c 𝓝 s y * (refKernel c 𝓝 s y)ᴴ) i i).re)) (nhdsWithin c (Icc a c))
        (nhds 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp he
      simpa [Function.comp_def] using this
    change Tendsto _ _ (nhds (0 : ℂ))
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hs
    filter_upwards [self_mem_nhdsWithin] with s hs'
    rw [← hcov s hs', re_mul_conjTranspose_diag]
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun k => ‖refFactor c 𝓝 s y i k‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ j)

theorem continuousOn_massGenerator (hr : ContinuousOn r (Icc a c)) (hκ : ContinuousOn κ (Icc a c)) :
    ContinuousOn (massGenerator r κ) (Icc a c) := by
  refine continuousOn_pi.2 fun k => continuousOn_pi.2 fun l => ?_
  have hrk : ∀ m, ContinuousOn (fun x => r x k m) (Icc a c) := fun m =>
    continuousOn_pi.1 (continuousOn_pi.1 hr k) m
  by_cases h : k = l
  · simp only [massGenerator, h, ite_true]
    subst h
    exact ((continuousOn_finsetSum _ fun m _ => hrk m).neg).sub (continuousOn_pi.1 hκ k)
  · simp only [massGenerator, h, ite_false]
    exact hrk l

theorem refKernel_mass_unique (hRF : LinearRotationFlowContract N) (hac : a ≤ c)
    (hr : ContinuousOn r (Icc a c)) (hκ : ContinuousOn κ (Icc a c))
    (hrs : ∀ x k l, r x k l = r x l k) (hr0 : ∀ x k l, 0 ≤ r x k l) (hκ0 : ∀ x k, 0 ≤ κ x k)
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝)
    (P : ℝ → Fin N → Fin N → ℝ) (hP : BackwardPropagator (massGenerator r κ) a c P) :
    ∀ s ∈ Icc a c, ∀ k j,
      ∫ y, ‖refKernel c 𝓝 s y k j‖ ^ 2 ∂driverLaw (κ := RotIdx N) μ = P s k j := by
  intro s hs k j
  have h := backwardPropagator_unique (continuousOn_massGenerator hr hκ)
    (refKernel_mass hRF hac hr hκ hrs hr0 hκ0 h𝓝) hP s hs
  exact congrFun (congrFun h k) j

/-!
## The constructor
-/

omit [IsProbabilityMeasure μ] in
theorem kernel_entry_le (hκ0 : ∀ x k, 0 ≤ κ x k)
    (hcon : KernelContracts μ κ a c (refKernel c 𝓝)) (s : ℝ) (hs : s ∈ Icc a c) :
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ i j, ‖refKernel c 𝓝 s y i j‖ ≤ 1 := by
  filter_upwards [hcon 0 (fun x _ k => hκ0 x k)] with y hy i j
  exact norm_entry_le_of_contraction (fun v => by simpa using hy s hs v) i j

theorem refSemigroup_terminal
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝) {p : ℕ}
    (f : RefState N p → ℝ) (z : RefState N p) :
    refSemigroup μ (refKernel c 𝓝) (refFactor c 𝓝) f c z = f z := by
  have hpt : ∀ y (G : RefState N p),
      lmul (refKernel c 𝓝 c y) z + lmul (refFactor c 𝓝 c y) G = z := by
    intro y G
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; exact Subsingleton.elim _ _
    · rw [refKernel_terminal h𝓝, refFactor_terminal h𝓝 hN, lmul_one', lmul_zero', add_zero]
  simp only [refSemigroup, hpt, integral_const, probReal_univ, one_smul]

/-- **`IsReferenceFlow` from the kernel contraction and the backward equation.** -/
theorem isReferenceFlow_of (hRF : LinearRotationFlowContract N) (hac : a ≤ c) {b : ℝ}
    (hb0 : 0 < b) (hr : ContinuousOn r (Icc a c)) (hκ : ContinuousOn κ (Icc a c))
    (hrs : ∀ x k l, r x k l = r x l k) (hr0 : ∀ x k l, 0 ≤ r x k l) (hκ0 : ∀ x k, 0 ≤ κ x k)
    (hfloor : ∀ x ∈ Icc a c, ∀ k, b ≤ κ x k)
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝)
    (hcon : KernelContracts μ κ a c (refKernel c 𝓝))
    (hback : BackwardEquationHolds μ r κ a c (refKernel c 𝓝) (refFactor c 𝓝)) :
    IsReferenceFlow μ r κ a c (refKernel c 𝓝) (refFactor c 𝓝) where
  measurable_kernel := measurable_refKernel h𝓝
  measurable_factor := measurable_refFactor h𝓝
  continuous := continuousOn_refKernel h𝓝
  terminal := refKernel_terminal h𝓝
  covariance := refFactor_covariance h𝓝 hcon hb0 hfloor
  contraction := hcon
  factor_continuous := continuousOn_refFactor h𝓝 hcon hb0 hfloor
  factor_hermitian := refFactor_isHermitian h𝓝 hcon hb0 hfloor
  factor_near_one := fun b' hb' => refFactor_near_one h𝓝 hcon hb0 hfloor b' hb'
  mass := refKernel_mass hRF hac hr hκ hrs hr0 hκ0 h𝓝
  mass_unique := refKernel_mass_unique hRF hac hr hκ hrs hr0 hκ0 h𝓝
  backward := fun p C f hf => by
    refine ⟨refSemigroup_terminal h𝓝 f,
      refSemigroup_continuousOn (measurable_refKernel h𝓝) (measurable_refFactor h𝓝)
        (continuousOn_refKernel h𝓝) (continuousOn_refFactor h𝓝 hcon hb0 hfloor) hf,
      fun s hs => (refSemigroup_static (measurable_refKernel h𝓝 s) (measurable_refFactor h𝓝 s)
        (kernel_entry_le hκ0 hcon s hs) hf).1,
      fun s hs => (refSemigroup_static (measurable_refKernel h𝓝 s) (measurable_refFactor h𝓝 s)
        (kernel_entry_le hκ0 hcon s hs) hf).2.1,
      fun s hs => (refSemigroup_static (measurable_refKernel h𝓝 s) (measurable_refFactor h𝓝 s)
        (kernel_entry_le hκ0 hcon s hs) hf).2.2,
      hback p C f hf⟩

end BlockBand.Palm.ReferenceFlow
