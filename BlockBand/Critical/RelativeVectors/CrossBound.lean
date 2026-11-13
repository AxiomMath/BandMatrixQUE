module

public import BlockBand.Critical.RelativeVectors.CrossPhase

/-!
# The cross-Hessian error bound

`crossError_backward_le`. In the setting of `TestedSetting` (tested test `φ`, `|D²φ| ≤ K₂`,
propagator entries `≤ 1`), let the backward function `g = ∫ φ(π(M · + Ξ)) dP` be of class `C²` and
label-phase invariant (both given by `IsReferenceFlow`: `backward` and `phase_covariant`). For a
window `J` on which `|z_iq|² ≤ B`, and `|z_iq| ≤ Z` everywhere:
`|crossError(D²g(z))(z)| ≤ K₂ Σ_{m',q',m,q} ∫ [B (Σ_{ij} |Θ^{mm'}_{ij}|² + |Θ^{mm'}_{ij}Θ^{mm'}_{ji}|)^{1/2}
  + Z² Σ_{(i,j) ∉ J×J} |Θ^{mm'}_{ij}|] dP`,
`Θ^{mm'}_{ij} = 1_{i≠j, |i-j|≥ℓ} c_ij M_{ιm,i} M_{ιm',j}` (`crossTheta`). The phases are those of
`phaseVectorLaw` (inserted by `crossError_eq_phase_average`), averaged before the auxiliary
randomness (Fubini).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission

variable {N r k : ℕ}

theorem continuous_crossTheta (ι : Fin k → Fin N) (lam : Fin N → ℝ) (ℓ : ℕ) (m m' : Fin k)
    (i j : Fin N) :
    Continuous fun A : Matrix (Fin N) (Fin N) ℂ => crossTheta ι lam ℓ A m m' i j := by
  unfold crossTheta
  split_ifs
  · exact (continuous_const.mul (continuous_id.matrix_elem _ _)).mul
      (continuous_id.matrix_elem _ _)
  · exact continuous_const

theorem norm_crossTheta_le (ι : Fin k → Fin N) (lam : Fin N → ℝ) (ℓ : ℕ)
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : ∀ a b, ‖A a b‖ ≤ 1) (m m' : Fin k) (i j : Fin N) :
    ‖crossTheta ι lam ℓ A m m' i j‖ ≤ |dysonCoupling N lam i j| := by
  unfold crossTheta
  split_ifs
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := hA (ι m) i
    have h2 := hA (ι m') j
    calc |dysonCoupling N lam i j| * ‖A (ι m) i‖ * ‖A (ι m') j‖
        ≤ |dysonCoupling N lam i j| * 1 * 1 := by gcongr
      _ = _ := by ring
  · simp

theorem ae_prod_phase_unit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    ∀ᵐ p ∂(P.prod (phaseVectorLaw N)), ∀ i, ‖p.2 i‖ = 1 := by
  rw [ae_iff]
  have hset : {p : Ω × (Fin N → ℂ) | ¬ ∀ i, ‖p.2 i‖ = 1} =
      (Set.univ : Set Ω) ×ˢ {θ : Fin N → ℂ | ¬ ∀ i, ‖θ i‖ = 1} := by
    ext p; simp
  rw [hset, Measure.prod_prod]
  have h0 : phaseVectorLaw N {θ : Fin N → ℂ | ¬ ∀ i, ‖θ i‖ = 1} = 0 := by
    have := (ae_norm_phase_eq_one (N := N))
    rwa [ae_iff] at this
  rw [h0, mul_zero]

section Backward

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {M : Ω → Matrix (Fin N) (Fin N) ℂ} {Ξ : Ω → Fin N → Fin r → ℂ}
  {φ : (Fin k → Fin r → ℂ) → ℝ}

/-- The cross sum `Σ_{ij} Θ_ij z_{iq'} z_{jq}` of one tested Hessian entry. -/
def crossSum (ι : Fin k → Fin N) (lam : Fin N → ℝ) (ℓ : ℕ) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : Fin N → Fin r → ℂ) (m m' : Fin k) (q' q : Fin r) : ℂ :=
  ∑ i, ∑ j, crossTheta ι lam ℓ A m m' i j * (z i q' * z j q)

theorem continuous_crossSum (ι : Fin k → Fin N) (lam : Fin N → ℝ) (ℓ : ℕ) (m m' : Fin k)
    (q' q : Fin r) :
    Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) =>
      crossSum ι lam ℓ p.1 p.2 m m' q' q := by
  unfold crossSum
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_crossTheta ι lam ℓ m m' i j).comp continuous_fst).mul (by fun_prop)

theorem norm_crossSum_le (ι : Fin k → Fin N) (lam : Fin N → ℝ) (ℓ : ℕ)
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : ∀ a b, ‖A a b‖ ≤ 1) (z : Fin N → Fin r → ℂ)
    (m m' : Fin k) (q' q : Fin r) :
    ‖crossSum ι lam ℓ A z m m' q' q‖ ≤ ∑ i, ∑ j, |dysonCoupling N lam i j| * (‖z‖ * ‖z‖) := by
  unfold crossSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul]
  have z1 : ‖z i q'‖ ≤ ‖z‖ := (norm_le_pi_norm (z i) q').trans (norm_le_pi_norm z i)
  have z2 : ‖z j q‖ ≤ ‖z‖ := (norm_le_pi_norm (z j) q).trans (norm_le_pi_norm z j)
  exact mul_le_mul (norm_crossTheta_le ι lam ℓ hA m m' i j) (mul_le_mul z1 z2 (norm_nonneg _)
    (norm_nonneg _)) (by positivity) (abs_nonneg _)

/-- Pointwise in the array: `|crossError(D²g(z))(z)| ≤ K₂ Σ ∫ |Σ_{ij} Θ_ij z_{iq'} z_{jq}| dP`. -/
theorem abs_crossError_backward_le (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂) (lam : Fin N → ℝ) (ℓ : ℕ) (z : Fin N → Fin r → ℂ) :
    |crossError N r lam ℓ
        (fderiv ℝ (fderiv ℝ (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P)) z) z| ≤
      K₂ * ∑ m', ∑ q' : Fin r, ∑ m, ∑ q : Fin r,
        ∫ ω, ‖crossSum ι lam ℓ (M ω) z m m' q' q‖ ∂P := by
  have hK₂ := hS.nonneg2
  have hint : ∀ m m' (q' q : Fin r), Integrable (fun ω => ‖crossSum ι lam ℓ (M ω) z m m' q' q‖) P := by
    intro m m' q' q
    refine Integrable.of_bound (μ := P) (((continuous_crossSum ι lam ℓ m m' q' q).comp
      (continuous_id.prodMk continuous_const)).measurable.comp hS.measM).norm.aestronglyMeasurable
      (∑ i, ∑ j, |dysonCoupling N lam i j| * (‖z‖ * ‖z‖)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact norm_crossSum_le ι lam ℓ (hS.entry ω) z m m' q' q
  rw [crossError_backward_eq ι hS lam ℓ z, abs_mul, abs_neg,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4), ← Real.norm_eq_abs]
  have hle : ∀ ω, ‖(∑ m', ∑ q', ∑ m, ∑ q,
      gam (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))) m q m' q' *
        ∑ i, ∑ j, crossTheta ι lam ℓ (M ω) m m' i j * (z i q' * z j q)).re‖ ≤
      4 * K₂ * ∑ m', ∑ q' : Fin r, ∑ m, ∑ q : Fin r, ‖crossSum ι lam ℓ (M ω) z m m' q' q‖ := by
    intro ω
    rw [Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m' _ => (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q' _ => (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_gam_le (hS.bound2 _) m q m' q') (norm_nonneg _)
  have hsumi : Integrable (fun ω => ∑ m', ∑ q' : Fin r, ∑ m, ∑ q : Fin r,
      ‖crossSum ι lam ℓ (M ω) z m m' q' q‖) P :=
    integrable_finsetSum _ fun m' _ => integrable_finsetSum _ fun q' _ =>
      integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun q _ => hint m m' q' q
  calc 1 / 4 * ‖∫ ω, (∑ m', ∑ q', ∑ m, ∑ q,
        gam (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))) m q m' q' *
          ∑ i, ∑ j, crossTheta ι lam ℓ (M ω) m m' i j * (z i q' * z j q)).re ∂P‖
      ≤ 1 / 4 * ∫ ω, 4 * K₂ * ∑ m', ∑ q' : Fin r, ∑ m, ∑ q : Fin r,
          ‖crossSum ι lam ℓ (M ω) z m m' q' q‖ ∂P := by
        gcongr
        exact (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hsumi.const_mul _)
          (Filter.Eventually.of_forall hle))
    _ = K₂ * ∑ m', ∑ q' : Fin r, ∑ m, ∑ q : Fin r,
        ∫ ω, ‖crossSum ι lam ℓ (M ω) z m m' q' q‖ ∂P := by
        rw [integral_const_mul, ← mul_assoc,
          show (1 / 4 : ℝ) * (4 * K₂) = K₂ by ring]
        congr 1
        rw [integral_finsetSum _ fun m' _ => integrable_finsetSum _ fun q' _ =>
          integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun q _ => hint m m' q' q]
        refine Finset.sum_congr rfl fun m' _ => ?_
        rw [integral_finsetSum _ fun q' _ => integrable_finsetSum _ fun m _ =>
          integrable_finsetSum _ fun q _ => hint m m' q' q]
        refine Finset.sum_congr rfl fun q' _ => ?_
        rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun q _ => hint m m' q' q]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [integral_finsetSum _ fun q _ => hint m m' q' q]

theorem crossSum_phase (ι : Fin k → Fin N) (lam : Fin N → ℝ) (ℓ : ℕ)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : Fin N → Fin r → ℂ) (θ : Fin N → ℂ) (m m' : Fin k)
    (q' q : Fin r) :
    crossSum ι lam ℓ A (phaseCLM θ z) m m' q' q =
      phaseSum (crossTheta ι lam ℓ A m m') (fun i => z i q') (fun j => z j q) θ := by
  simp [crossSum, phaseSum, smul_eq_mul]

/-- The window bound of one tested entry, as a function of the propagator. -/
def crossBoundFun (ι : Fin k → Fin N) (lam : Fin N → ℝ) (ℓ : ℕ) (J : Finset (Fin N)) (B Z : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) (m m' : Fin k) : ℝ :=
  B * Real.sqrt (∑ i, ∑ j, (‖crossTheta ι lam ℓ A m m' i j‖ ^ 2 +
      ‖crossTheta ι lam ℓ A m m' i j * crossTheta ι lam ℓ A m m' j i‖)) +
    Z * Z * ∑ i, ∑ j, (if i ∈ J ∧ j ∈ J then 0 else ‖crossTheta ι lam ℓ A m m' i j‖)

theorem continuous_crossBoundFun (ι : Fin k → Fin N) (lam : Fin N → ℝ) (ℓ : ℕ)
    (J : Finset (Fin N)) (B Z : ℝ) (m m' : Fin k) :
    Continuous fun A : Matrix (Fin N) (Fin N) ℂ => crossBoundFun ι lam ℓ J B Z A m m' := by
  unfold crossBoundFun
  have hc := continuous_crossTheta ι lam ℓ m m'
  refine (continuous_const.mul (Continuous.sqrt (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ((hc i j).norm.pow 2).add
      ((hc i j).mul (hc j i)).norm))).add (continuous_const.mul (continuous_finsetSum _
        fun i _ => continuous_finsetSum _ fun j _ => ?_))
  split_ifs
  · exact continuous_const
  · exact (hc i j).norm

/-- **The cross-Hessian error bound.** See the module docstring. -/
theorem crossError_backward_le (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂)
    (hg : ContDiff ℝ 2 (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P))
    (hinv : ∀ u : Fin N → ℂ, (∀ i, ‖u i‖ = 1) → ∀ z,
      (∫ ω, φ (testProj ι (arrayMul (M ω) (phaseCLM u z) + Ξ ω)) ∂P) =
        ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P)
    (lam : Fin N → ℝ) (ℓ : ℕ) (z : Fin N → Fin r → ℂ) (J : Finset (Fin N)) {B Z : ℝ}
    (hB : 0 ≤ B) (hZ : 0 ≤ Z) (hzJ : ∀ i ∈ J, ∀ q, ‖z i q‖ ^ 2 ≤ B)
    (hz : ∀ i q, ‖z i q‖ ≤ Z) :
    |crossError N r lam ℓ
        (fderiv ℝ (fderiv ℝ (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P)) z) z| ≤
      K₂ * ∑ m', ∑ _q' : Fin r, ∑ m, ∑ _q : Fin r,
        ∫ ω, crossBoundFun ι lam ℓ J B Z (M ω) m m' ∂P := by
  have hK₂ := hS.nonneg2
  set S : Fin k → Fin k → Fin r → Fin r → Ω × (Fin N → ℂ) → ℝ := fun m m' q' q p =>
    ‖phaseSum (crossTheta ι lam ℓ (M p.1) m m') (fun i => z i q') (fun j => z j q) p.2‖ with hSdef
  have hSm : ∀ m m' q' q, Measurable (S m m' q' q) := by
    intro m m' q' q
    have hc : Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) =>
        phaseSum (crossTheta ι lam ℓ p.1 m m') (fun i => z i q') (fun j => z j q) p.2 := by
      unfold phaseSum
      refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
      exact ((continuous_crossTheta ι lam ℓ m m' i j).comp continuous_fst).mul (by fun_prop)
    exact (hc.measurable.comp ((hS.measM.comp measurable_fst).prodMk measurable_snd)).norm
  have hzq : ∀ q, ∀ i, ‖(fun i => z i q) i‖ ≤ Z := fun q i => hz i q
  have hSb : ∀ m m' q' q, ∀ p : Ω × (Fin N → ℂ), (∀ i, ‖p.2 i‖ = 1) →
      S m m' q' q p ≤ ∑ i, ∑ j, |dysonCoupling N lam i j| * (Z * Z) := by
    intro m m' q' q p hp
    refine (norm_phaseSum_le _ _ _ p.2 hp (hzq q') (hzq q)).trans ?_
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (norm_crossTheta_le ι lam ℓ (hS.entry p.1) m m' i j)
        (by positivity)
  have hSi : ∀ m m' q' q, Integrable (S m m' q' q) (P.prod (phaseVectorLaw N)) :=
    fun m m' q' q => Integrable.of_bound (hSm m m' q' q).aestronglyMeasurable _
      ((ae_prod_phase_unit P).mono fun p hp => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hSb m m' q' q p hp)
  -- integrability in `θ` of the inner integrals
  have hIθ : ∀ m m' q' q, Integrable (fun θ => ∫ ω, S m m' q' q (ω, θ) ∂P) (phaseVectorLaw N) :=
    fun m m' q' q => (hSi m m' q' q).integral_prod_right
  have hsumθ : Integrable (fun θ => K₂ * ∑ m', ∑ q' : Fin r, ∑ m, ∑ q : Fin r,
      ∫ ω, S m m' q' q (ω, θ) ∂P) (phaseVectorLaw N) :=
    (integrable_finsetSum _ fun m' _ => integrable_finsetSum _ fun q' _ =>
      integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun q _ => hIθ m m' q' q).const_mul _
  -- the bound functions
  have hbi : ∀ m m', Integrable (fun ω => crossBoundFun ι lam ℓ J B Z (M ω) m m') P := by
    intro m m'
    refine Integrable.of_bound (μ := P) ((continuous_crossBoundFun ι lam ℓ J B Z m m').measurable.comp
      hS.measM).aestronglyMeasurable
      (B * Real.sqrt (∑ i, ∑ j, (|dysonCoupling N lam i j| ^ 2 +
        |dysonCoupling N lam i j| * |dysonCoupling N lam j i|)) +
        Z * Z * ∑ i, ∑ j, |dysonCoupling N lam i j|) (Filter.Eventually.of_forall fun ω => ?_)
    have h0 : 0 ≤ crossBoundFun ι lam ℓ J B Z (M ω) m m' := by
      unfold crossBoundFun
      have : 0 ≤ ∑ i, ∑ j, (if i ∈ J ∧ j ∈ J then 0 else ‖crossTheta ι lam ℓ (M ω) m m' i j‖) :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    have hθb := norm_crossTheta_le ι lam ℓ (hS.entry ω) m m'
    unfold crossBoundFun
    refine add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hθb i j) 2) ?_))
      hB) (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_)
        (by positivity))
    · rw [norm_mul]
      exact mul_le_mul (hθb i j) (hθb j i) (norm_nonneg _) (abs_nonneg _)
    · split_ifs
      · exact abs_nonneg _
      · exact hθb i j
  -- assemble
  set g := fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P with hgdef
  rw [crossError_eq_phase_average hg (fun u hu z => hinv u hu z) lam ℓ z]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ θ, |crossError N r lam ℓ (fderiv ℝ (fderiv ℝ g) (phaseCLM θ z)) (phaseCLM θ z)|
        ∂phaseVectorLaw N
      ≤ ∫ θ, K₂ * ∑ m', ∑ q' : Fin r, ∑ m, ∑ q : Fin r, ∫ ω, S m m' q' q (ω, θ) ∂P
          ∂phaseVectorLaw N := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) hsumθ
          (Filter.Eventually.of_forall fun θ => ?_)
        refine (abs_crossError_backward_le ι hS lam ℓ (phaseCLM θ z)).trans (le_of_eq ?_)
        simp only [hSdef, crossSum_phase]
    _ = K₂ * ∑ m', ∑ q' : Fin r, ∑ m, ∑ q : Fin r, ∫ θ, ∫ ω, S m m' q' q (ω, θ) ∂P
          ∂phaseVectorLaw N := by
        rw [integral_const_mul]
        congr 1
        rw [integral_finsetSum _ fun m' _ => integrable_finsetSum _ fun q' _ =>
          integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun q _ => hIθ m m' q' q]
        refine Finset.sum_congr rfl fun m' _ => ?_
        rw [integral_finsetSum _ fun q' _ => integrable_finsetSum _ fun m _ =>
          integrable_finsetSum _ fun q _ => hIθ m m' q' q]
        refine Finset.sum_congr rfl fun q' _ => ?_
        rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun q _ => hIθ m m' q' q]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [integral_finsetSum _ fun q _ => hIθ m m' q' q]
    _ ≤ K₂ * ∑ m', ∑ _q' : Fin r, ∑ m, ∑ _q : Fin r,
        ∫ ω, crossBoundFun ι lam ℓ J B Z (M ω) m m' ∂P := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m' _ => Finset.sum_le_sum
          fun q' _ => Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun q _ => ?_) hK₂
        rw [← integral_integral_swap (f := fun ω θ => S m m' q' q (ω, θ)) (hSi m m' q' q)]
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ =>
          integral_nonneg fun _ => norm_nonneg _) (hbi m m') (Filter.Eventually.of_forall fun ω => ?_)
        exact phase_cross_window_le (crossTheta ι lam ℓ (M ω) m m')
          (crossTheta_diag ι lam ℓ (M ω) m m') (fun i => z i q') (fun j => z j q) J hB hZ
          (fun i hi => hzJ i hi q') (fun i hi => hzJ i hi q) (hzq q') (hzq q)

end Backward

end BlockBand.Critical.RelativeVectors
