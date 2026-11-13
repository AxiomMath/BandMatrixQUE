module

public import BlockBand.Palm.ReferenceFlowSpec
public import BlockBand.Palm.ReferenceFlowItoMean
public import BlockBand.Palm.RelativeLocalizationODE
public import BlockBand.Internal.Contracts.TransmissionFlow
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Pathwise contraction of rotation flows

Measure: `driverLaw μ` on `DriverSample S (RotIdx N)`, `μ` an arbitrary probability law on `S`.
Hypotheses: the bilinear Itô product rule `ItoProductRuleFor` on `Matrix (Fin N) (Fin N) ℂ`
(Frobenius norm), and a rotation flow `IsRotationFlow μ r κ a c s M` with symmetric nonnegative
rates `r` and damping `κ` continuous on `[a,c]`, `a ≤ c`.

* `rotationFlow_contraction`: if `b ≤ κ` on `[a,c]` then a.s., for all `t ≥ 0` and `v`,
  `‖M_t v‖² ≤ e^{-bt} ‖v‖²`; `rotationFlow_contraction_conjTranspose`: the same for `M_tᴴ`.
* `vec_bound_conjTranspose`: `‖A·‖² ≤ q‖·‖²` implies `‖Aᴴ·‖² ≤ q‖·‖²`.

Proof. The product rule with the real-bilinear map `(X,Y) ↦ Xᴴ Y` (`conjMulCLM`) makes
`G_t = M_tᴴ M_t` an Itô process; its diffusion `Mᴴ(σ_αᴴ + σ_α)M` vanishes since the
rotation coefficients are skew-Hermitian (`rotationNoise_conjTranspose`), so
`G_t = I + ∫_0^t B_u du` a.s. for each `t` (`ae_eq_add_drift_of_zero_diffusion`), hence for all
rational `t` at once. Pairing with `v` (`qfCLM`), the drift is
`Re⟨v, B_u v⟩ = -∑_k κ_k(u) |(M_u v)_k|²` (`qfCLM_drift`: the Itô correction
`∑_α ‖σ_α w‖² = ∑_k (∑_{m≠k} r_km) |w_k|²` cancels the rotation part of the drift). Both sides
are continuous in `t` along a.e. path, so the identity holds for all `t ≥ 0`, and the scalar
Grönwall lemma `le_exp_mul_of_deriv_le` gives the bound since `κ ≥ b` at the clamped times.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow

open MeasureTheory Set Matrix Filter Topology
open BlockBand.Palm.RelativeLocalization (le_exp_mul_of_deriv_le)
open BlockBand.Internal.Contracts.TransmissionFlow (IsRotationFlow rotX rotY rotationNoise
  rotationDrift clampTime)
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.Stochastic
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {N : ℕ}

/-!
## Algebra of the rotation coefficients
-/

theorem rotX_conjTranspose (i j : Fin N) : (rotX i j)ᴴ = -rotX i j := by
  simp [rotX, conjTranspose_sub, conjTranspose_single]

theorem rotY_conjTranspose (i j : Fin N) : (rotY i j)ᴴ = -rotY i j := by
  simp [rotY, conjTranspose_add, conjTranspose_single, add_comm, single_neg]

theorem rotationNoise_conjTranspose (ρ : Fin N → Fin N → ℝ) (α : RotIdx N) :
    (rotationNoise ρ α)ᴴ = -rotationNoise ρ α := by
  unfold rotationNoise
  split_ifs <;> simp [conjTranspose_smul, rotX_conjTranspose, rotY_conjTranspose]

theorem rotX_mulVec_apply (i j k : Fin N) (w : Fin N → ℂ) :
    (rotX i j *ᵥ w) k = (if k = j then w i else 0) - (if k = i then w j else 0) := by
  simp [rotX, sub_mulVec, single_mulVec, Function.update_apply]

theorem rotY_mulVec_apply (i j k : Fin N) (w : Fin N → ℂ) :
    (rotY i j *ᵥ w) k =
      Complex.I * ((if k = j then w i else 0) + (if k = i then w j else 0)) := by
  simp only [rotY, smul_mulVec, add_mulVec, single_mulVec, Function.update_apply, Pi.smul_apply,
    Pi.add_apply, Pi.zero_apply, smul_eq_mul, one_mul]

theorem norm_sq_ite_sub {i j k : Fin N} (hij : i ≠ j) (x y : ℂ) :
    ‖(if k = j then x else 0) - (if k = i then y else 0)‖ ^ 2 =
      (if k = j then ‖x‖ ^ 2 else 0) + (if k = i then ‖y‖ ^ 2 else 0) := by
  by_cases hkj : k = j
  · subst hkj; simp [Ne.symm hij]
  · by_cases hki : k = i
    · subst hki; simp [hkj]
    · simp [hkj, hki]

theorem norm_sq_ite_add {i j k : Fin N} (hij : i ≠ j) (x y : ℂ) :
    ‖Complex.I * ((if k = j then x else 0) + (if k = i then y else 0))‖ ^ 2 =
      (if k = j then ‖x‖ ^ 2 else 0) + (if k = i then ‖y‖ ^ 2 else 0) := by
  rw [norm_mul, Complex.norm_I, one_mul]
  by_cases hkj : k = j
  · subst hkj; simp [Ne.symm hij]
  · by_cases hki : k = i
    · subst hki; simp [hkj]
    · simp [hkj, hki]

theorem sum_norm_sq_rotX {i j : Fin N} (hij : i ≠ j) (w : Fin N → ℂ) :
    ∑ k, ‖(rotX i j *ᵥ w) k‖ ^ 2 = ‖w i‖ ^ 2 + ‖w j‖ ^ 2 := by
  simp only [rotX_mulVec_apply, norm_sq_ite_sub hij, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem sum_norm_sq_rotY {i j : Fin N} (hij : i ≠ j) (w : Fin N → ℂ) :
    ∑ k, ‖(rotY i j *ᵥ w) k‖ ^ 2 = ‖w i‖ ^ 2 + ‖w j‖ ^ 2 := by
  simp only [rotY_mulVec_apply, norm_sq_ite_add hij, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem sum_norm_sq_real_smul_mulVec (c : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) (w : Fin N → ℂ) :
    ∑ k, ‖(((c : ℂ) • A) *ᵥ w) k‖ ^ 2 = c ^ 2 * ∑ k, ‖(A *ᵥ w) k‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mulVec, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- `∑_{i<j} ρ_ij (a_i + a_j) = ∑_k (∑_{m≠k} ρ_km) a_k` for symmetric `ρ`. -/
theorem sum_lt_pair_eq (ρ : Fin N → Fin N → ℝ) (hρs : ∀ k l, ρ k l = ρ l k) (a : Fin N → ℝ) :
    ∑ i, ∑ j, (if i < j then ρ i j * (a i + a j) else 0) =
      ∑ k, (∑ m ∈ Finset.univ.erase k, ρ k m) * a k := by
  have hR : ∀ k, (∑ m ∈ Finset.univ.erase k, ρ k m) * a k =
      ∑ m, (if m ≠ k then ρ k m * a k else 0) := by
    intro k
    rw [Finset.sum_mul, ← Finset.filter_ne', Finset.sum_filter]
  simp_rw [hR]
  calc ∑ i, ∑ j, (if i < j then ρ i j * (a i + a j) else 0)
      = ∑ i, ∑ j, (if i < j then ρ i j * a i else 0) +
          ∑ i, ∑ j, (if i < j then ρ i j * a j else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> ring
    _ = ∑ i, ∑ j, (if i < j then ρ i j * a i else 0) +
          ∑ i, ∑ j, (if j < i then ρ i j * a i else 0) := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hρs]
    _ = ∑ i, ∑ j, (if j ≠ i then ρ i j * a i else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rcases lt_trichotomy i j with h | h | h
        · simp [h, h.ne', not_lt_of_gt h]
        · subst h; simp
        · simp [h, h.ne, not_lt_of_gt h]

/-- The Itô correction of the rotations: `∑_α ‖σ_α w‖² = ∑_k (∑_{m≠k} ρ_km) |w_k|²`. -/
theorem sum_norm_sq_rotationNoise (ρ : Fin N → Fin N → ℝ) (hρs : ∀ k l, ρ k l = ρ l k)
    (hρ0 : ∀ k l, 0 ≤ ρ k l) (w : Fin N → ℂ) :
    ∑ α : RotIdx N, ∑ k, ‖(rotationNoise ρ α *ᵥ w) k‖ ^ 2 =
      ∑ k, (∑ m ∈ Finset.univ.erase k, ρ k m) * ‖w k‖ ^ 2 := by
  rw [← sum_lt_pair_eq ρ hρs, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_two]
  by_cases hij : i < j
  · simp only [rotationNoise, hij, ite_true, Fin.isValue, one_ne_zero, ite_false]
    rw [sum_norm_sq_real_smul_mulVec, sum_norm_sq_real_smul_mulVec, sum_norm_sq_rotX hij.ne,
      sum_norm_sq_rotY hij.ne, Real.sq_sqrt (div_nonneg (hρ0 i j) zero_le_two)]
    ring
  · simp [rotationNoise, hij]

/-!
## The real-bilinear map `(X, Y) ↦ Xᴴ Y` and the quadratic pairing
-/

/-- `(X, Y) ↦ Xᴴ Y` as a real-bilinear map. -/
def conjMulLin : Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ]
    Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.mk₂ ℝ (fun X Y => Xᴴ * Y)
    (fun X X' Y => by simp [conjTranspose_add, Matrix.add_mul])
    (fun c X Y => by simp [conjTranspose_smul])
    (fun X Y Y' => by simp [Matrix.mul_add])
    (fun c X Y => by simp)

/-- `(X, Y) ↦ Xᴴ Y` as a continuous real-bilinear map (finite dimension). -/
def conjMulCLM : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ →L[ℝ]
    Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      conjMulLin)

@[simp] theorem conjMulCLM_apply (X Y : Matrix (Fin N) (Fin N) ℂ) : conjMulCLM X Y = Xᴴ * Y :=
  rfl

/-- The real quadratic pairing `A ↦ Re ⟨v, A v⟩`. -/
def qfLin (v : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] ℝ where
  toFun A := (star v ⬝ᵥ (A *ᵥ v)).re
  map_add' A B := by simp [add_mulVec, dotProduct_add]
  map_smul' c A := by simp [smul_mulVec, dotProduct_smul]

/-- `A ↦ Re ⟨v, A v⟩` as a continuous real-linear functional. -/
def qfCLM (v : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (qfLin v)

@[simp] theorem qfCLM_apply (v : Fin N → ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    qfCLM v A = (star v ⬝ᵥ (A *ᵥ v)).re :=
  rfl

theorem re_star_dotProduct_self (w : Fin N → ℂ) : (star w ⬝ᵥ w).re = ∑ k, ‖w k‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.star_def, Complex.conj_mul']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem qfCLM_conjMul (v : Fin N → ℂ) (X Y : Matrix (Fin N) (Fin N) ℂ) :
    qfCLM v (conjMulCLM X Y) = (star (X *ᵥ v) ⬝ᵥ (Y *ᵥ v)).re := by
  rw [qfCLM_apply, conjMulCLM_apply, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

theorem qfCLM_conjMul_self (v : Fin N → ℂ) (X : Matrix (Fin N) (Fin N) ℂ) :
    qfCLM v (conjMulCLM X X) = ∑ k, ‖(X *ᵥ v) k‖ ^ 2 := by
  rw [qfCLM_conjMul, re_star_dotProduct_self]

theorem re_star_diagonal_dotProduct (d : Fin N → ℝ) (w : Fin N → ℂ) :
    (star (diagonal (fun k => (d k : ℂ)) *ᵥ w) ⬝ᵥ w).re = ∑ k, d k * ‖w k‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, mulVec_diagonal, Complex.re_sum, star_mul',
    Complex.star_def, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re]

theorem re_star_dotProduct_diagonal (d : Fin N → ℝ) (w : Fin N → ℂ) :
    (star w ⬝ᵥ (diagonal (fun k => (d k : ℂ)) *ᵥ w)).re = ∑ k, d k * ‖w k‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, mulVec_diagonal, Complex.re_sum, Complex.star_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- **Drift pairing.** For the drift of `Mᴴ M` given by the product rule,
`Re ⟨v, (Mᴴ Dᴴ M + Mᴴ D M + ∑_α Mᴴ σ_αᴴ σ_α M) v⟩ = -∑_k κ_k |(M v)_k|²`. -/
theorem qfCLM_drift (ρ : Fin N → Fin N → ℝ) (κ' : Fin N → ℝ) (hρs : ∀ k l, ρ k l = ρ l k)
    (hρ0 : ∀ k l, 0 ≤ ρ k l) (A : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    qfCLM v (conjMulCLM (rotationDrift ρ κ' * A) A + conjMulCLM A (rotationDrift ρ κ' * A) +
        ∑ α, conjMulCLM (rotationNoise ρ α * A) (rotationNoise ρ α * A)) =
      -∑ k, κ' k * ‖(A *ᵥ v) k‖ ^ 2 := by
  rw [map_add, map_add, map_sum]
  simp only [qfCLM_conjMul_self, qfCLM_conjMul, ← mulVec_mulVec]
  rw [sum_norm_sq_rotationNoise ρ hρs hρ0, rotationDrift, re_star_diagonal_dotProduct,
    re_star_dotProduct_diagonal, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Zero diffusion of `Mᴴ M`.** -/
theorem conjMul_rotationNoise_add (ρ : Fin N → Fin N → ℝ) (α : RotIdx N)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    conjMulCLM (rotationNoise ρ α * A) A + conjMulCLM A (rotationNoise ρ α * A) = 0 := by
  simp [conjTranspose_mul, rotationNoise_conjTranspose, Matrix.mul_assoc]

/-!
## Pathwise contraction
-/

/-- The Borel structure of `Matrix (Fin N) (Fin N) ℂ` for the Frobenius topology (equal to the
product topology, so this is the product Borel instance of `Mathlib.Analysis.Matrix.MeasurableSpace`
read through the Frobenius norm). `BorelSpace` is a `Prop`, so any other proof is
definitionally equal. -/
theorem frobeniusBorelSpace :
    @BorelSpace (Matrix (Fin N) (Fin N) ℂ)
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ :=
  (inferInstance : BorelSpace (Matrix (Fin N) (Fin N) ℂ))

attribute [local instance] frobeniusBorelSpace

theorem clampTime_mem {a c : ℝ} (hac : a ≤ c) (x : ℝ) : clampTime a c x ∈ Icc a c :=
  ⟨le_max_left _ _, max_le hac (min_le_right _ _)⟩

theorem continuous_clampTime (a c : ℝ) : Continuous (clampTime a c) := by
  unfold clampTime; fun_prop

theorem denseRange_rat_toNNReal : DenseRange fun q : ℚ => (q : ℝ).toNNReal :=
  DenseRange.comp (g := Real.toNNReal) (f := ((↑) : ℚ → ℝ))
    (Function.Surjective.denseRange fun t => ⟨t, Real.toNNReal_coe⟩)
    (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)) continuous_real_toNNReal

/-- **Pathwise contraction of rotation flows.** If the damping is bounded below by `b` on
`[a,c]`, then almost surely, for all times `t ≥ 0` and all vectors `v`,
`‖M_t v‖² ≤ e^{-bt} ‖v‖²`. -/
theorem rotationFlow_contraction {S : Type} [MeasurableSpace S] {μ : Measure S}
    [IsProbabilityMeasure μ]
    (hProd : ItoProductRuleFor (S := S) (κ := RotIdx N) μ (Matrix (Fin N) (Fin N) ℂ)
      (Matrix (Fin N) (Fin N) ℂ) (Matrix (Fin N) (Fin N) ℂ))
    {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c s : ℝ} (hac : a ≤ c)
    (_hr : ContinuousOn r (Icc a c)) (hκ : ContinuousOn κ (Icc a c))
    (hrs : ∀ x k l, r x k l = r x l k) (hr0 : ∀ x k l, 0 ≤ r x k l)
    {M : ℝ≥0 → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ}
    (hM : IsRotationFlow μ r κ a c s M)
    (b : ℝ) (hb : ∀ x ∈ Icc a c, ∀ k, b ≤ κ x k) :
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ t : ℝ≥0, ∀ v : Fin N → ℂ,
      ∑ k, ‖(M t y *ᵥ v) k‖ ^ 2 ≤ Real.exp (-(b * t)) * ∑ k, ‖v k‖ ^ 2 := by
  have hP := hProd _ _ _ _ _ _ hM.1 hM.1 conjMulCLM
  have hG : IsNativeItoProcess μ (fun t x => conjMulCLM (M t x) (M t x))
      (fun t x => conjMulCLM (rotationDrift (r (clampTime a c (s + t)))
          (κ (clampTime a c (s + t))) * M t x) (M t x) +
        conjMulCLM (M t x) (rotationDrift (r (clampTime a c (s + t)))
          (κ (clampTime a c (s + t))) * M t x) +
        ∑ α, conjMulCLM (rotationNoise (r (clampTime a c (s + t))) α * M t x)
          (rotationNoise (r (clampTime a c (s + t))) α * M t x))
      (fun _ _ _ => 0) := by
    convert hP using 1
    funext α t x
    exact (conjMul_rotationNoise_add _ _ _).symm
  have hall : ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ q : ℚ,
      conjMulCLM (M (q : ℝ).toNNReal y) (M (q : ℝ).toNNReal y) =
        conjMulCLM (M 0 y) (M 0 y) + stoppedDrift (fun _ => ⊤) _ (q : ℝ).toNNReal y :=
    ae_all_iff.2 fun q => ae_eq_add_drift_of_zero_diffusion hG _
  filter_upwards [hM.1.continuous, hG.drift_integrable, hall] with y hcont hint hq
  intro t v
  have hent : ∀ i j, Continuous fun u : ℝ≥0 => M u y i j := fun i j =>
    (((continuous_apply j).comp (continuous_apply i) :
      @Continuous (Matrix (Fin N) (Fin N) ℂ) ℂ
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ (fun A => A i j))).comp hcont
  have hw : ∀ k, Continuous fun u : ℝ≥0 => (M u y *ᵥ v) k := fun k => by
    simp only [mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => (hent k j).mul continuous_const
  set φ : ℝ≥0 → ℝ := fun u => ∑ k, ‖(M u y *ᵥ v) k‖ ^ 2 with hφ
  have hφc : Continuous φ :=
    continuous_finsetSum _ fun k _ => ((hw k).norm).pow 2
  set κc : ℝ → Fin N → ℝ := fun u => κ (clampTime a c (s + u)) with hκc_def
  have hκc : Continuous κc :=
    hκ.comp_continuous ((continuous_clampTime a c).comp (continuous_const.add continuous_id))
      (fun u => clampTime_mem hac _)
  set g : ℝ → ℝ := fun u => ∑ k, κc (u.toNNReal : ℝ) k * ‖(M u.toNNReal y *ᵥ v) k‖ ^ 2 with hg
  have hgc : Continuous g := by
    refine continuous_finsetSum _ fun k _ => ?_
    exact ((continuous_apply k).comp (hκc.comp (NNReal.continuous_coe.comp
      continuous_real_toNNReal))).mul (((hw k).comp continuous_real_toNNReal).norm.pow 2)
  set F : ℝ → ℝ := fun x => ∑ k, ‖v k‖ ^ 2 - ∫ u in (0 : ℝ)..x, g u with hF_def
  have hF : ∀ x, HasDerivAt F (-g x) x := fun x =>
    ((hgc.integral_hasStrictDerivAt 0 x).hasDerivAt).const_sub _
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hF x).continuousAt
  have hrat : ∀ q : ℚ, φ (q : ℝ).toNNReal = F ((q : ℝ).toNNReal : ℝ) := by
    intro q
    have h1 := congrArg (qfCLM v) (hq q)
    rw [map_add, qfCLM_conjMul_self, qfCLM_conjMul_self, hM.2 y, one_mulVec] at h1
    change ∑ k, ‖(M (q : ℝ).toNNReal y *ᵥ v) k‖ ^ 2 =
      ∑ k, ‖v k‖ ^ 2 - ∫ u in (0 : ℝ)..(((q : ℝ).toNNReal : ℝ≥0) : ℝ), g u
    rw [h1, sub_eq_add_neg]
    congr 1
    simp only [stoppedDrift, le_top, ite_true]
    refine ((qfCLM v).integral_comp_comm (hint _)).symm.trans ?_
    rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg _), ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    exact qfCLM_drift _ _ (hrs _) (hr0 _) _ _
  have heq : φ = fun u : ℝ≥0 => F u :=
    Continuous.ext_on denseRange_rat_toNNReal hφc (hFc.comp NNReal.continuous_coe)
      (by rintro _ ⟨q, rfl⟩; exact hrat q)
  have hle : ∀ x ∈ Ioo (0 : ℝ) t, -g x ≤ -b * F x := by
    intro x hx
    have hx0 : ((x.toNNReal : ℝ≥0) : ℝ) = x := Real.coe_toNNReal x hx.1.le
    have hFx : F x = φ x.toNNReal := by rw [heq]; exact congrArg F hx0.symm
    rw [hFx, neg_mul, neg_le_neg_iff, hφ, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact hb _ (clampTime_mem hac _) k
  have hgr := le_exp_mul_of_deriv_le (f := F) (f' := fun x => -g x) (s := 0) (u := t) (K := -b)
    hFc.continuousOn (fun x _ => hF x) hle t ⟨t.2, le_rfl⟩
  have hφt : ∑ k, ‖(M t y *ᵥ v) k‖ ^ 2 = F t := congrFun heq t
  simp only [hF_def, intervalIntegral.integral_same, sub_zero] at hgr
  rw [hφt]
  simpa [hF_def, neg_mul] using hgr

/-- **Adjoint bound.** If `‖A v‖² ≤ q ‖v‖²` for all `v`, then `‖Aᴴ v‖² ≤ q ‖v‖²` for all `v`
(Cauchy–Schwarz: `‖Aᴴ v‖² = Re ⟨v, A Aᴴ v⟩ ≤ ‖v‖ ‖A Aᴴ v‖ ≤ √q ‖v‖ ‖Aᴴ v‖`). -/
theorem vec_bound_conjTranspose (A : Matrix (Fin N) (Fin N) ℂ) (q : ℝ) (hq : 0 ≤ q)
    (h : ∀ v : Fin N → ℂ, ∑ k, ‖(A *ᵥ v) k‖ ^ 2 ≤ q * ∑ k, ‖v k‖ ^ 2) :
    ∀ v : Fin N → ℂ, ∑ k, ‖(Aᴴ *ᵥ v) k‖ ^ 2 ≤ q * ∑ k, ‖v k‖ ^ 2 := by
  intro v
  set u := Aᴴ *ᵥ v with hu
  set nu := ∑ k, ‖u k‖ ^ 2
  set nv := ∑ k, ‖v k‖ ^ 2
  have hnu0 : 0 ≤ nu := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hnv0 : 0 ≤ nv := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hs : star u = star v ᵥ* A := by rw [hu, star_mulVec, conjTranspose_conjTranspose]
  have hre : nu = (star v ⬝ᵥ (A *ᵥ u)).re := by
    rw [dotProduct_mulVec, ← hs, re_star_dotProduct_self]
  have hX : nu ≤ ∑ k, ‖v k‖ * ‖(A *ᵥ u) k‖ := by
    rw [hre]
    refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (le_of_eq ?_))
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.star_apply, norm_mul, norm_star]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖v k‖)
    (fun k => ‖(A *ᵥ u) k‖)
  have hsq : nu ^ 2 ≤ nv * (q * nu) := by
    calc nu ^ 2 ≤ (∑ k, ‖v k‖ * ‖(A *ᵥ u) k‖) ^ 2 := pow_le_pow_left₀ hnu0 hX 2
      _ ≤ nv * ∑ k, ‖(A *ᵥ u) k‖ ^ 2 := hCS
      _ ≤ nv * (q * nu) := mul_le_mul_of_nonneg_left (h u) hnv0
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hpos : 0 < nu := lt_of_le_of_lt (mul_nonneg hq hnv0) hlt
  nlinarith

/-- **Pathwise contraction of the adjoint.** Under the hypotheses of
`rotationFlow_contraction`, almost surely `‖M_tᴴ v‖² ≤ e^{-bt} ‖v‖²` for all `t ≥ 0`, `v`. -/
theorem rotationFlow_contraction_conjTranspose {S : Type} [MeasurableSpace S] {μ : Measure S}
    [IsProbabilityMeasure μ]
    (hProd : ItoProductRuleFor (S := S) (κ := RotIdx N) μ (Matrix (Fin N) (Fin N) ℂ)
      (Matrix (Fin N) (Fin N) ℂ) (Matrix (Fin N) (Fin N) ℂ))
    {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c s : ℝ} (hac : a ≤ c)
    (hr : ContinuousOn r (Icc a c)) (hκ : ContinuousOn κ (Icc a c))
    (hrs : ∀ x k l, r x k l = r x l k) (hr0 : ∀ x k l, 0 ≤ r x k l)
    {M : ℝ≥0 → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ}
    (hM : IsRotationFlow μ r κ a c s M)
    (b : ℝ) (hb : ∀ x ∈ Icc a c, ∀ k, b ≤ κ x k) :
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ t : ℝ≥0, ∀ v : Fin N → ℂ,
      ∑ k, ‖((M t y)ᴴ *ᵥ v) k‖ ^ 2 ≤ Real.exp (-(b * t)) * ∑ k, ‖v k‖ ^ 2 := by
  filter_upwards [rotationFlow_contraction hProd hac hr hκ hrs hr0 hM b hb] with y hy
  intro t
  exact vec_bound_conjTranspose _ _ (Real.exp_pos _).le (hy t)

end BlockBand.Palm.ReferenceFlow
